#!/usr/bin/env python3
"""
NeeDoh stock watcher.

Checks UK shops listed in stores.json and sends a phone alert (via the free
ntfy app) the moment a NeeDoh goes from "sold out" to "in stock".

Uses only the Python standard library, so there is nothing to install.

Environment variables:
  NTFY_TOPIC   required to send alerts (your private ntfy topic name)
  NTFY_SERVER  optional, defaults to https://ntfy.sh
  TEST_ALERT   set to "1" to send a single test notification and exit
  DRY_RUN      set to "1" to print alerts instead of sending them
"""

import json
import os
import re
import sys
import html as html_lib
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
STORES_FILE = HERE / "stores.json"
STATE_FILE = HERE / "state.json"

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/130.0 Safari/537.36")

# After this many failed checks in a row for one shop, send one heads-up.
FAIL_ALERT_AFTER = 12  # ~1 hour at 5-minute checks
FULL_SCAN_EVERY = 30 * 60  # seconds between whole-shop searches for new NeeDoh


# --------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------

def log(msg):
    print(f"[{datetime.now(timezone.utc):%H:%M:%S}] {msg}", flush=True)


def http_get(url, accept="application/json,text/html;q=0.9,*/*;q=0.8", timeout=25):
    req = urllib.request.Request(url, headers={
        "User-Agent": UA,
        "Accept": accept,
        "Accept-Language": "en-GB,en;q=0.9",
    })
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read().decode("utf-8", errors="replace")


def matches(text, keywords):
    t = (text or "").lower()
    return any(k.lower() in t for k in keywords)


def load_json(path, default):
    try:
        return json.loads(path.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return default


# --------------------------------------------------------------------------
# shop checkers - each returns {product_key: {"title", "url", "available", "price"}}
# --------------------------------------------------------------------------

def _shopify_item(store, base, p, from_js=False):
    variants = p.get("variants", [])
    if from_js:  # /products/<handle>.js gives prices in pence
        available = bool(p.get("available"))
        prices = [v["price"] / 100 for v in variants if isinstance(v.get("price"), (int, float))]
    else:
        available = any(v.get("available") for v in variants)
        prices = [float(v["price"]) for v in variants if v.get("price")]
    return {
        "title": p.get("title", p["handle"]),
        "url": f"{base}/products/{p['handle']}",
        "available": available,
        "price": f"£{min(prices):.2f}" if prices else "",
    }


def _is_needoh(p, keywords):
    # title or brand only - shop tags often mention NeeDoh on lookalike squishies
    return matches(f"{p.get('title', '')} {p.get('vendor', '')}", keywords)


def _scan_shopify(src, max_pages):
    for page in range(1, max_pages + 1):
        products = json.loads(http_get(f"{src}?limit=250&page={page}")).get("products", [])
        yield from products
        if len(products) < 250:
            return
        time.sleep(0.5)


def check_shopify(store, keywords, ctx):
    """
    Shopify shops publish their catalogue as JSON.
    - The shop's NeeDoh collection (if it has one) is checked every run.
    - The WHOLE shop is searched for NeeDoh every ~30 minutes, so brand-new
      uploads are found even if the shop never puts them in its NeeDoh section
      (and shops with no NeeDoh yet are still watched).
    - NeeDoh found outside the collection is re-checked every run after that.
    """
    base = store["url"].rstrip("/")
    name = store["name"]
    extras = ctx["state"].setdefault("extras", {})
    found = {}

    in_collection = set()
    for handle in store.get("collections", []):
        for p in _scan_shopify(f"{base}/collections/{handle}/products.json", store.get("max_pages", 4)):
            if _is_needoh(p, keywords):
                found[f"{name}|{p['handle']}"] = _shopify_item(store, base, p)
                in_collection.add(p["handle"])

    full_scan = ctx["full_scan"] or name not in extras
    if full_scan:
        outside = []
        for p in _scan_shopify(f"{base}/products.json", store.get("full_scan_pages", 40)):
            if _is_needoh(p, keywords) and p["handle"] not in in_collection:
                found[f"{name}|{p['handle']}"] = _shopify_item(store, base, p)
                outside.append(p["handle"])
        extras[name] = sorted(outside)
    else:
        for handle in extras.get(name, []):
            try:
                p = json.loads(http_get(f"{base}/products/{handle}.js"))
                found[f"{name}|{handle}"] = _shopify_item(store, base, p, from_js=True)
            except urllib.error.HTTPError as e:
                if e.code != 404:  # 404 = product removed, just drop it
                    raise
            time.sleep(0.5)
    return found


LD_RE = re.compile(r'<script[^>]+application/ld\+json[^>]*>(.*?)</script>', re.S | re.I)


def _walk_ld(node):
    # visit every nested object (shops spell keys differently, e.g. "Offers" vs "offers")
    if isinstance(node, list):
        for n in node:
            yield from _walk_ld(n)
    elif isinstance(node, dict):
        yield node
        for value in node.values():
            if isinstance(value, (dict, list)):
                yield from _walk_ld(value)


META_AVAIL_RE = re.compile(
    r'<meta[^>]+(?:property|name)=["\'](?:og:availability|product:availability)["\'][^>]*'
    r'content=["\']([^"\']+)["\']', re.I)
META_AVAIL_RE2 = re.compile(  # same tag with the attributes the other way round
    r'<meta[^>]+content=["\']([^"\']+)["\'][^>]*'
    r'(?:property|name)=["\'](?:og:availability|product:availability)["\']', re.I)


def _read_product_page(store, url):
    html = http_get(url, accept="text/html,*/*;q=0.8")
    title, available, price = None, None, ""

    # 1) shop-specific markers, when given (most precise)
    oos_pat = store.get("out_of_stock_pattern") or (re.escape(store["out_of_stock_text"])
                                                     if store.get("out_of_stock_text") else None)
    in_pat = store.get("in_stock_pattern")
    if oos_pat or in_pat:
        if oos_pat and re.search(oos_pat, html, re.I):
            available = False
        elif in_pat and re.search(in_pat, html, re.I):
            available = True
        else:
            # neither marker: probably a block page or the shop changed its site
            raise RuntimeError("stock markers not found")

    # 2) schema.org data (what Google reads)
    ld_available = None
    for block in LD_RE.findall(html):
        try:
            data = json.loads(block.strip())
        except json.JSONDecodeError:
            continue
        for node in _walk_ld(data):
            typ = str(node.get("@type", ""))
            if "Product" in typ and node.get("name") and not title:
                title = html_lib.unescape(str(node["name"]))
            if "availability" in node:
                is_in = "instock" in str(node["availability"]).lower().replace("_", "")
                ld_available = bool(ld_available) or is_in
                if node.get("price") and not price:
                    price = f"£{node['price']}"
    if available is None:
        available = ld_available

    # 3) social-media meta tags (e.g. Urban Outfitters)
    if available is None:
        m = META_AVAIL_RE.search(html) or META_AVAIL_RE2.search(html)
        if m:
            v = m.group(1).lower().replace(" ", "").replace("_", "")
            available = v in ("instock", "in", "available")

    if available is None:
        raise RuntimeError("no stock info on page")
    if not title:
        m = re.search(r"<title>(.*?)</title>", html, re.S | re.I)
        title = html_lib.unescape(m.group(1).strip()) if m else url
    return {"title": title, "url": url, "available": available, "price": price}


HREF_RE = re.compile(r'<a\b[^>]*?href=["\']([^"\'#]+)["\'][^>]*>(.{0,400}?)</a>', re.S | re.I)
TAG_RE = re.compile(r"<[^>]+>")


def _discover(store, keywords):
    """Read the shop's own NeeDoh search/brand page and pick out product links."""
    found = []
    for d in store.get("discover", []):
        page = http_get(d["url"], accept="text/html,*/*;q=0.8")
        for href, inner in HREF_RE.findall(page):
            url = urllib.parse.urljoin(d["url"], html_lib.unescape(href)).split("?")[0]
            if not re.search(d["link_pattern"], url, re.I):
                continue
            text = html_lib.unescape(TAG_RE.sub(" ", inner))
            if matches(url.replace("-", " "), keywords) or matches(url, keywords) or matches(text, keywords):
                found.append(url)
        time.sleep(1)
    return found


def check_product_pages(store, keywords, ctx):
    """
    Any shop: read each NeeDoh product page.
    If the shop has a search/brand page ("discover"), it's read every run so
    newly uploaded NeeDoh pages are added automatically.
    One bad page doesn't stop the rest.
    """
    known = ctx["state"].setdefault("discovered", {}).setdefault(store["name"], [])
    discover_error = None
    try:
        for url in _discover(store, keywords):
            if url not in known and url not in store.get("products", []):
                known.append(url)
                log(f"{store['name']}: found new NeeDoh page {url}")
    except Exception as e:  # noqa: BLE001
        discover_error = e
        log(f"{store['name']}: couldn't read search page: {e}")

    found, errors = {}, []
    urls = list(dict.fromkeys(store.get("products", []) + known))
    for url in urls:
        try:
            found[f"{store['name']}|{url}"] = _read_product_page(store, url)
        except Exception as e:  # noqa: BLE001
            errors.append(f"{url.rstrip('/').rsplit('/', 1)[-1]}: {e}")
        time.sleep(1)
    if errors:
        log(f"{store['name']}: skipped {len(errors)} page(s): {'; '.join(errors)[:300]}")
    if urls and not found:
        raise RuntimeError(f"all {len(urls)} pages failed ({errors[0]})")
    if not urls and discover_error:
        raise discover_error
    return found


def check_woocommerce(store, keywords, ctx):
    """WooCommerce (WordPress) shops have a public Store API with stock info."""
    base = store["url"].rstrip("/")
    found = {}
    for term in store.get("search_terms", ["needoh", "nee doh"]):
        q = urllib.parse.quote(term)
        data = json.loads(http_get(f"{base}/wp-json/wc/store/v1/products?search={q}&per_page=100"))
        for p in data:
            name = html_lib.unescape(p.get("name", ""))
            if not matches(name, keywords):
                continue
            prices = p.get("prices") or {}
            price = ""
            if prices.get("price"):
                minor = int(prices.get("currency_minor_unit", 2))
                price = f"£{int(prices['price']) / 10 ** minor:.2f}"
            found[f"{store['name']}|{p['id']}"] = {
                "title": name,
                "url": p.get("permalink", base),
                "available": bool(p.get("is_in_stock")),
                "price": price,
            }
        time.sleep(1)
    return found


CHECKERS = {"shopify": check_shopify, "product_pages": check_product_pages,
            "woocommerce": check_woocommerce}


# --------------------------------------------------------------------------
# alerts
# --------------------------------------------------------------------------

def notify(title, message, click=None, priority="high", tags="tada"):
    topic = os.environ.get("NTFY_TOPIC", "").strip()
    server = os.environ.get("NTFY_SERVER", "https://ntfy.sh").rstrip("/")
    if os.environ.get("DRY_RUN") == "1" or not topic:
        log(f"ALERT (not sent{'' if topic else ', no NTFY_TOPIC set'}): {title} | {message} | {click}")
        return
    headers = {
        # ntfy headers must be latin-1; the body can be full UTF-8
        "Title": title.encode("latin-1", "replace").decode("latin-1"),
        "Priority": priority,
        "Tags": tags,
    }
    if click:
        headers["Click"] = click
        headers["Actions"] = f"view, Open shop, {click}"
    req = urllib.request.Request(f"{server}/{topic}", data=message.encode("utf-8"),
                                 headers=headers, method="POST")
    urllib.request.urlopen(req, timeout=20).read()
    log(f"Alert sent: {title}")


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------

def main():
    if os.environ.get("TEST_ALERT") == "1":
        notify("NeeDoh watcher is working!",
               "This is a test. You'll get an alert like this when something comes back in stock.",
               click="https://www.bigjigstoys.co.uk/collections/nee-doh")
        return 0

    config = load_json(STORES_FILE, None)
    if not config:
        log("stores.json missing or invalid")
        return 1
    keywords = config.get("keywords", ["needoh", "nee doh", "nee-doh"])
    state = load_json(STATE_FILE, {})
    for k in ("products", "failures", "baselined"):
        state.setdefault(k, {} if k != "baselined" else [])
    first_run = not state["baselined"]

    # search every shop's whole catalogue roughly every 30 minutes
    slot = int(time.time() // FULL_SCAN_EVERY)
    ctx = {"state": state, "full_scan": state.get("full_scan_slot") != slot}
    if ctx["full_scan"]:
        log("Full search of every shop this run")
        state["full_scan_slot"] = slot

    in_stock_now, new_shops = [], []

    for store in config["stores"]:
        if store.get("enabled", True) is False:
            continue
        name = store["name"]
        try:
            results = CHECKERS[store["type"]](store, store.get("keywords", keywords), ctx)
        except Exception as e:  # noqa: BLE001 - keep going with the other shops
            n = state["failures"].get(name, 0) + 1
            state["failures"][name] = min(n, FAIL_ALERT_AFTER + 1)  # stop counting = no extra commits
            log(f"{name}: check failed ({n} in a row): {e}")
            if n == FAIL_ALERT_AFTER:
                notify(f"Can't check {name} right now",
                       f"{name} has failed {n} checks in a row ({e}). "
                       "It may be blocking the checker; other shops are still being watched.",
                       priority="low", tags="warning")
            continue

        if state["failures"].get(name, 0) >= FAIL_ALERT_AFTER:
            notify(f"{name} is being checked again", "Back to normal.", priority="min", tags="white_check_mark")
        state["failures"][name] = 0
        avail = sum(1 for r in results.values() if r["available"])
        log(f"{name}: {len(results)} NeeDoh products, {avail} in stock")

        # the first time we see a shop, just remember what it has (no alert storm)
        baseline = name not in state["baselined"]
        if baseline:
            state["baselined"].append(name)
            new_shops.append(name)

        for key, item in results.items():
            before = state["products"].get(key)
            was_available = before["available"] if before else False
            if item["available"]:
                in_stock_now.append(f"{item['title']} ({name})")
            if not baseline:
                price = f" - {item['price']}" if item["price"] else ""
                if item["available"] and not was_available:
                    label = "NEW & IN STOCK" if before is None else "BACK IN STOCK"
                    notify(f"{label}: {item['title']}"[:120],
                           f"{item['title']}{price}\nat {name}\nTap to open the shop.",
                           click=item["url"])
                elif before is None:
                    notify(f"New NeeDoh listed: {item['title']}"[:120],
                           f"{name} has just added {item['title']}{price}. It's not buyable yet, "
                           "but you'll get a loud alert the moment it is.",
                           click=item["url"], priority="default", tags="new")
            state["products"][key] = item  # only changes on real changes, so few commits

    if first_run or new_shops:
        title = "NeeDoh watcher started" if first_run else f"Now also watching {len(new_shops)} more shop(s)"
        stock = ("In stock right now:\n- " + "\n- ".join(in_stock_now)) if in_stock_now \
            else "Everything is sold out at the moment. You'll hear the second that changes."
        notify(title, stock[:3500], priority="default", tags="eyes")

    STATE_FILE.write_text(json.dumps(state, indent=1, sort_keys=True, ensure_ascii=False) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
