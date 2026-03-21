#!/usr/bin/env python3
"""
AliExpress Product Scraper → Amazon Bulk Upload
================================================
Scrapes AliExpress search results, visits each product page to get ALL images
and variations, then generates an Amazon-compatible bulk upload file.

Setup:
    pip3 install -r requirements.txt
    python3 -m playwright install chromium

Usage:
    python3 scraper.py urls.txt
    python3 scraper.py urls.txt -o output.csv
"""
from __future__ import annotations
import argparse
import csv
import json
import logging
import math
import atexit
import os
import random
import re
import signal
import subprocess
import sys
import time
from datetime import datetime
from io import BytesIO
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from urllib.parse import urlparse, parse_qs, urlencode, urlunparse

from playwright.sync_api import sync_playwright
import requests as http_requests

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s  %(levelname)-8s  %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger("scraper")

# ---------------------------------------------------------------------------
# CONFIGURATION
# ---------------------------------------------------------------------------
MARKUP = 3.0
DEFAULT_PRICE_GBP = 12.99
BROWSE_NODE = "364155031"       # Amazon UK: Action & Toy Figures
PRODUCT_TYPE = "toyfigure"
BRAND = "Generic"
HANDLING_DAYS = 7
QUANTITY = 5
MAX_PAGES = 50
MAX_IMAGES = 9                  # Amazon allows main + 8 other images
PARALLEL_TABS = 1               # Sequential detail scraping — more reliable, avoids CAPTCHAs

# Proxy pool disabled — cheap datacenter proxies trigger more CAPTCHAs than
# browsing direct from a residential IP.  Keep the list empty so proxy code
# is safely skipped everywhere.
PROXY_POOL = []
PROXY_LOCAL_BASE_PORT = 19800  # local forwarder listens on 19800, 19801, etc.
_proxy_procs = []  # track pproxy subprocesses for cleanup


def start_proxy_forwarders():
    """Launch local pproxy forwarders for each SOCKS5 proxy in the pool.

    Playwright can't do SOCKS5 auth, so we run local HTTP proxies that
    forward to the authenticated SOCKS5 proxies. Returns list of
    local proxy URLs like http://127.0.0.1:19800.
    """
    local_urls = []
    for idx, (host, port, user, pwd) in enumerate(PROXY_POOL):
        local_port = PROXY_LOCAL_BASE_PORT + idx
        # pproxy: listen as HTTP on local port, forward to SOCKS5 with auth
        remote = f"socks5://{host}:{port}#{user}:{pwd}"
        local = f"http://127.0.0.1:{local_port}"
        cmd = [sys.executable, "-m", "pproxy", "-l", local, "-r", remote]
        try:
            proc = subprocess.Popen(
                cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            )
            _proxy_procs.append(proc)
            local_urls.append(f"http://127.0.0.1:{local_port}")
            log.info("  Proxy forwarder: %s → socks5://%s:%s", local, host, port)
        except Exception as e:
            log.warning("  Failed to start proxy forwarder for %s:%s: %s", host, port, e)
    # Give forwarders a moment to start
    if local_urls:
        time.sleep(1)
    return local_urls


def stop_proxy_forwarders():
    """Kill all pproxy forwarder subprocesses."""
    for proc in _proxy_procs:
        try:
            proc.terminate()
            proc.wait(timeout=3)
        except Exception:
            try:
                proc.kill()
            except Exception:
                pass
    _proxy_procs.clear()


atexit.register(stop_proxy_forwarders)


# ---- SMART PRICING CONFIG ----
TARGET_PROFIT_MARGIN = 0.30
MIN_PROFIT_GBP = 7.50          # Minimum £7.50 profit per item
AMAZON_REFERRAL_FEE = 0.1545
AMAZON_PER_ITEM_FEE = 0.75
USD_TO_GBP = 0.75
MIN_SELL_PRICE = 5.99

# ---- IMAGE HOSTING ----
IMGBB_API_KEY = "dd9a3b6ab5cabf1a45a24736ffe29e42"

# Keywords for resin model filtering — STRICT: only resin figures, busts, dioramas
# The product MUST match at least one INCLUDE term AND not match any EXCLUDE term.
# Additionally, products matching SOFT_INCLUDE still require "resin" somewhere in the title.
RESIN_INCLUDE = [
    # Primary — these are strong enough signals on their own
    "resin model", "resin figure", "resin statue", "resin bust",
    "resin kit", "resin cast", "resin diorama",
    "garage kit", "gk kit", "gk,",
    "unpainted kit", "unassembled kit",
    "miniature figure", "miniature figurine",
]

RESIN_SOFT_INCLUDE = [
    # These only count if "resin" is ALSO in the title
    "model figure", "figure kit", "model kit",
    "bust kit", "statue kit", "diorama",
    "unpainted", "unassembled",
    "1/6", "1/8", "1/9", "1/10", "1/12", "1/16",
    "1/24", "1/32", "1/35", "1/43", "1/64", "1/72",
    "1/87", "1/100", "1/144",
    "scale model", "scale figure",
    "soldier figure", "military figure",
    "fantasy figure", "wargame", "wargaming",
    "tabletop", "miniature",
]

RESIN_EXCLUDE = [
    # Electronics / accessories
    "phone case", "screen protector", "earphone", "headphone",
    "charger", "cable", "adapter", "usb", "bluetooth", "led light",
    # Clothing
    "clothing", "shirt", "dress", "pants", "shoe", "sock", "costume",
    # Food / health
    "food", "snack", "drink", "supplement", "vitamin",
    # Cosmetics
    "cosmetic", "makeup", "skincare", "perfume", "shampoo",
    # Pet
    "pet food", "dog food", "cat food",
    # Non-resin crafts
    "sticker", "decal only", "poster", "wall art", "painting",
    "silicone mold", "silicone mould", "candle mold",
    "jewelry mold", "epoxy mold", "soap mold",
    "resin art supply", "resin pigment", "resin dye", "resin glue",
    "uv resin", "epoxy resin", "resin coaster", "resin tray",
    "resin jewelry", "resin earring", "resin necklace", "resin ring",
    "resin keychain", "resin bookmark",
    # Branded vehicles (IP risk)
    "jeep", "ford", "toyota", "bmw", "mercedes", "audi",
    "ferrari", "lamborghini", "porsche", "tesla", "honda",
    "chevrolet", "volkswagen", "nissan", "subaru",
    # Branded IP (takedown risk)
    "marvel", "disney", "star wars", "pokemon", "transformers",
    "warhammer", "games workshop", "bandai", "kotobukiya", "hasbro",
    "funko", "lego", "nike", "adidas", "supreme",
    "dragon ball", "naruto", "one piece", "demon slayer",
    "gundam", "gunpla",
    # Non-resin model types
    "building block", "brick set", "brick model", "nano block",
    "micro block", "diamond block", "mini block", "moc set",
    "plastic model", "plastic kit", "injection kit",
    "die cast", "diecast", "die-cast", "metal car",
    "rc car", "remote control", "radio control",
    "plush", "stuffed", "soft toy", "puzzle", "jigsaw",
    "board game", "card game", "trading card",
    "3d print file", "stl file", "digital download",
]

# ---------------------------------------------------------------------------
# CSV — writes rows live
# ---------------------------------------------------------------------------
FIELDS = [
    "id", "product_title", "product_price", "product_original_price",
    "product_discount", "product_url", "product_image", "product_images",
    "product_rating", "store_name", "store_url", "store_id",
    "total_sales", "ship_from", "store_member_id", "trade_info",
    "shipping", "launch_time", "company_name", "source_url",
    "variations", "variation_images",
]


class LiveCSV:
    def __init__(self, path, resume=False):
        self.path = path
        self.count = 0
        self._seen = set()
        self._seen_urls = {}  # source_url -> count of products from that URL

        if resume and os.path.exists(path):
            # Load existing data to resume
            try:
                with open(path, "r", newline="", encoding="utf-8") as f:
                    reader = csv.DictReader(f)
                    for row in reader:
                        pid = row.get("id", "")
                        if pid:
                            self._seen.add(pid)
                            self.count += 1
                            src = row.get("source_url", "")
                            if src:
                                self._seen_urls[src] = self._seen_urls.get(src, 0) + 1
                log.info("  Resuming: loaded %d existing products from %s", self.count, path)
                if self._seen_urls:
                    for u, c in self._seen_urls.items():
                        log.info("    %s: %d products", u[:80], c)
            except Exception as e:
                log.warning("  Could not read existing CSV for resume: %s", e)
                self._seen.clear()
                self._seen_urls.clear()
                self.count = 0

            # Open in append mode (no header needed)
            self._f = open(path, "a", newline="", encoding="utf-8")
            self._w = csv.DictWriter(self._f, fieldnames=FIELDS, extrasaction="ignore")
        else:
            self._f = open(path, "w", newline="", encoding="utf-8")
            self._w = csv.DictWriter(self._f, fieldnames=FIELDS, extrasaction="ignore")
            self._w.writeheader()
        self._f.flush()

    def already_scraped(self, product_id):
        """Check if a product has already been scraped."""
        return product_id in self._seen

    def url_product_count(self, url):
        """Get how many products have been scraped from a URL."""
        return self._seen_urls.get(url, 0)

    def add(self, rows, source_url):
        dupes = 0
        new = 0
        for r in rows:
            pid = r.get("id", "")
            if pid in self._seen:
                dupes += 1
                continue
            self._seen.add(pid)
            r["source_url"] = source_url
            self._w.writerow(r)
            self.count += 1
            new += 1
            self._seen_urls[source_url] = self._seen_urls.get(source_url, 0) + 1
        self._f.flush()
        if dupes:
            log.info("  Skipped %d duplicate products (already scraped)", dupes)
        return new

    def close(self):
        self._f.close()


# ---------------------------------------------------------------------------
# URL helpers
# ---------------------------------------------------------------------------
def sort_by_orders(url):
    parsed = urlparse(url)
    qs = parse_qs(parsed.query, keep_blank_values=True)
    qs["SortType"] = ["total_tranpro_desc"]
    qs["sortType"] = ["orders_desc"]
    qs["shop_sortType"] = ["orders_desc"]
    return urlunparse(parsed._replace(query=urlencode(qs, doseq=True)))


CLICK_ORDERS_SORT_JS = """
() => {
    // Find and click the "Orders" sort tab on store pages
    const sortItems = document.querySelectorAll(
        '[class*="sort"] a, [class*="Sort"] a, [class*="sort"] span, [class*="Sort"] span, ' +
        '[class*="tab"] a, [class*="Tab"] a'
    );
    for (const el of sortItems) {
        const text = (el.innerText || el.textContent || '').trim().toLowerCase();
        if (text === 'orders' || text === 'order' || text === 'orders ↓') {
            el.click();
            return true;
        }
    }
    // Broader search: any clickable element with "Orders" text in sort/filter areas
    const allEls = document.querySelectorAll('a, span, div, button');
    for (const el of allEls) {
        const text = (el.innerText || el.textContent || '').trim();
        if (text === 'Orders' || text === 'orders') {
            // Make sure it's a sort button (near other sort options like "Best Match", "New", "Price")
            const parent = el.parentElement;
            if (parent) {
                const parentText = parent.innerText || '';
                if (/best\\s*match|new|price/i.test(parentText)) {
                    el.click();
                    return true;
                }
            }
        }
    }
    return false;
}
"""


def click_orders_sort(tab):
    """Click the 'Orders' sort tab on store pages."""
    try:
        clicked = tab.evaluate(CLICK_ORDERS_SORT_JS)
        if clicked:
            log.info("  Clicked 'Orders' sort tab")
            tab.wait_for_timeout(2000)
            # Wait for page to reload with sorted results
            try:
                tab.wait_for_selector("a[href*='/item/']", timeout=8000)
            except Exception:
                pass
            return True
        else:
            log.info("  'Orders' sort tab not found (URL params may handle it)")
    except Exception as e:
        log.info("  Could not click Orders sort: %s", e)
    return False


# ---------------------------------------------------------------------------
# Extract products from search/category page
# ---------------------------------------------------------------------------
EXTRACT_JS = """
() => {
    const results = [];
    const links = document.querySelectorAll('a[href*="/item/"]');
    const processed = new Set();
    for (const link of links) {
        const href = link.getAttribute('href') || '';
        const match = href.match(/\\/item\\/(\\d+)\\.html/);
        if (!match) continue;
        const pid = match[1];
        if (processed.has(pid)) continue;
        processed.add(pid);

        let card = link;
        for (let i = 0; i < 3; i++) {
            if (!card.parentElement) break;
            const p = card.parentElement;
            if (p.querySelectorAll('a[href*="/item/"]').length > 1) break;
            card = p;
        }

        let image = '';
        const img = link.querySelector('img') || card.querySelector('img');
        if (img) {
            image = img.getAttribute('src') || img.getAttribute('data-src') || '';
            if (image.includes('48x48') || image.includes('placeholder')) image = '';
        }

        let title = '';
        if (img) title = (img.getAttribute('alt') || '').trim();
        if (!title) title = (link.getAttribute('title') || '').trim();
        if (!title) title = (link.getAttribute('aria-label') || '').trim();
        if (!title) {
            const titleEl = card.querySelector('[class*="title"],[class*="Title"],h1,h2,h3');
            if (titleEl) {
                const t = titleEl.innerText.trim();
                if (t.length > 5 && !['New arrivals','Hot deals','Related Searches','More to love'].includes(t)) {
                    title = t;
                }
            }
        }
        if (!title) {
            const text = card.innerText || '';
            const lines = text.split('\\n').map(l => l.trim()).filter(l => l.length > 10);
            if (lines.length) title = lines.reduce((a, b) => a.length > b.length ? a : b);
        }

        let price = 'N/A';
        const cardText = card.innerText || '';
        // Strategy 1: Look for price in dedicated DOM elements first
        const priceSelectors = [
            '[class*="price-current"]', '[class*="price--current"]',
            '[class*="sale-price"]', '[class*="salePrice"]',
            '[class*="Price"] [class*="current"]',
            '[class*="multi--price"]', '[class*="price-sale"]',
            '[class*="snow-price_SnowPrice"]',
            '[class*="price"]'
        ];
        for (const sel of priceSelectors) {
            try {
                const el = card.querySelector(sel);
                if (el) {
                    const pText = el.innerText.trim();
                    const pMatch = pText.match(/(?:US\\s*)?[\\$€£¥₽]\\s*[\\d,]+\\.\\d{1,2}/);
                    if (pMatch) { price = pMatch[0].trim(); break; }
                    // Prices like "9.30" without currency symbol
                    const pMatch2 = pText.match(/\\d+[,.]\\d{2}/);
                    if (pMatch2) { price = '$' + pMatch2[0]; break; }
                }
            } catch(e) {}
        }
        // Strategy 2: Regex on full card text (original approach)
        if (price === 'N/A') {
            const pm = cardText.match(/(?:US\\s*)?[\\$€£¥₽]\\s*[\\d,]+\\.?\\d*/);
            if (pm) {
                price = pm[0].trim();
            } else {
                const pm2 = cardText.match(/\\d+[,.]\\d{2}/);
                if (pm2) price = '$' + pm2[0];
            }
        }

        let sales = '';
        const sm = cardText.match(/(\\d[\\d,\\.]*[KkMm]?\\+?)\\s*[Ss]old(?![a-zA-Z])/);
        if (sm) sales = sm[0].trim();

        if (['New arrivals','Hot deals','Related Searches','More to love',''].includes(title)) continue;

        results.push({ id: pid, title: title.substring(0, 300), price, image, sales, href });
    }
    return results;
}
"""


def extract(page):
    try:
        raw = page.evaluate(EXTRACT_JS)
    except Exception:
        return []
    products = []
    seen = set()
    for r in raw:
        pid = r["id"]
        url = f"https://www.aliexpress.com/item/{pid}.html"
        if url in seen:
            continue
        seen.add(url)
        img = r.get("image", "")
        if img.startswith("//"):
            img = "https:" + img
        products.append({
            "id": pid,
            "product_title": r["title"],
            "product_price": r["price"],
            "product_original_price": "",
            "product_discount": "",
            "product_url": url,
            "product_image": img,
            "product_images": "",
            "product_rating": "",
            "store_name": "", "store_url": "", "store_id": "",
            "total_sales": r.get("sales", ""),
            "ship_from": "", "store_member_id": "",
            "trade_info": r.get("sales", ""),
            "shipping": "", "launch_time": "", "company_name": "",
            "variations": "", "variation_images": "",
        })
    return products


# ---------------------------------------------------------------------------
# Product detail page scraper — gets ALL images + variations
# ---------------------------------------------------------------------------
DETAIL_EXTRACT_JS = """
() => {
    const result = {
        images: [],
        variations: [],
        title: '',
        price: '',
        originalPrice: '',
        shipping: '',
        description: '',
    };

    // Helper: clean an image URL to get full-size version
    function cleanImgUrl(src) {
        if (!src) return '';
        src = src.replace(/_\\d+x\\d+[^.]*\\./g, '.');
        src = src.replace(/\\.(jpg|png|jpeg|webp)_\\d+x\\d+[^.]*/gi, '.$1');
        // Remove .webp suffix to get .jpg (Amazon needs JPEG)
        src = src.replace(/\\.webp$/i, '.jpg');
        if (src.startsWith('//')) src = 'https:' + src;
        return src;
    }

    const imgSet = new Set();
    function addImage(src) {
        src = cleanImgUrl(src);
        if (!src) return;
        if (src.includes('placeholder') || src.includes('48x48') || src.includes('avatar')
            || src.includes('icon') || src.includes('logo') || src.includes('flag-icon')) return;
        if (!src.includes('alicdn.com') && !src.includes('ae01.') && !src.includes('ae04.')) return;
        // Deduplicate by the core filename (ignore size suffixes)
        const key = src.replace(/https?:\\/\\/[^/]+/, '').replace(/_\\d+x\\d+/g, '');
        if (imgSet.has(key)) return;
        imgSet.add(key);
        result.images.push(src);
    }

    // --- Strategy 1 (BEST): Gallery thumbnail images from the DOM ---
    // These are the small thumbnails on the LEFT side of the product page.
    // They represent exactly the images shown in the gallery — nothing more.
    // The main large image is always one of these thumbnails expanded.

    // Always grab the main/large image first
    const mainSelectors = [
        '.image-view-magnifier-wrap img',
        '[class*="image-view"] img',
        '.mag-img img',
        '.product-image-panel img',
    ];
    for (const sel of mainSelectors) {
        try {
            const els = document.querySelectorAll(sel);
            for (const el of els) {
                const src = el.getAttribute('src') || el.getAttribute('data-src') || '';
                addImage(src);
            }
        } catch(e) {}
        if (result.images.length > 0) break;
    }

    // Then get all thumbnails (dedup will handle overlap with main image)
    const thumbSelectors = [
        '.images-view-item img',
        '[class*="slider--item"] img',
        '[class*="slider--img"] img',
        '[class*="thumbnail"] img[src*="alicdn"]',
        '[class*="pic-gallery"] img',
        '[class*="PicGallery"] img',
        '.images-view-wrap img',
        // Modern AliExpress uses CSS module hashed classes
        '[class*="gallery"] img[src*="alicdn"]',
        '[class*="Gallery"] img[src*="alicdn"]',
        '[class*="imageGallery"] img',
        '[class*="slider"] img[src*="alicdn"]',
        '[class*="Slider"] img[src*="alicdn"]',
    ];
    for (const sel of thumbSelectors) {
        try {
            const els = document.querySelectorAll(sel);
            for (const el of els) {
                const src = el.getAttribute('src') || el.getAttribute('data-src') || '';
                addImage(src);
            }
        } catch(e) {}
        if (result.images.length >= 5) break;  // got enough
    }

    // --- Strategy 2 (FALLBACK): imagePathList from JSON if DOM gave few/no images ---
    if (result.images.length <= 2) {
        const html = document.documentElement.innerHTML;
        const imgListPatterns = [
            /"imagePathList"\\s*:\\s*\\[([^\\]]+)\\]/,
            /"productImageList"\\s*:\\s*\\[([^\\]]+)\\]/,
        ];
        for (const pattern of imgListPatterns) {
            const match = html.match(pattern);
            if (match) {
                const urls = match[1].match(/"((?:https?:|\\/)?\\/\\/[^"]+)"/g);
                if (urls) {
                    for (let url of urls) {
                        url = url.replace(/"/g, '').replace(/\\\\/g, '/');
                        addImage(url);
                    }
                }
                break;
            }
        }
    }

    // --- Get variations (SKU properties) ---
    const varContainers = document.querySelectorAll(
        '[class*="sku-property"], [class*="product-sku"], [class*="sku-wrap"], ' +
        '[class*="product-prop"], [class*="variation"]'
    );

    for (const container of varContainers) {
        const nameEl = container.querySelector(
            '[class*="sku-property-text"], [class*="property-title"], ' +
            '[class*="sku-title"], span[class*="name"]'
        );
        const varName = nameEl ? nameEl.innerText.trim().replace(/:$/, '') : '';

        const items = container.querySelectorAll(
            '[class*="sku-property-item"], [class*="sku-item"], ' +
            'a[class*="item"], span[class*="item"], li'
        );

        const options = [];
        for (const item of items) {
            const img = item.querySelector('img');
            const text = item.innerText.trim() ||
                         item.getAttribute('title') ||
                         (img ? img.getAttribute('alt') : '') || '';
            let imgUrl = '';
            if (img) {
                imgUrl = cleanImgUrl(img.getAttribute('src') || img.getAttribute('data-src') || '');
            }
            if (text || imgUrl) {
                options.push({ name: text.substring(0, 100), image: imgUrl });
            }
        }

        if (options.length > 0) {
            result.variations.push({
                property: varName,
                options: options
            });
        }
    }

    // Get title from detail page
    const titleEl = document.querySelector(
        'h1[data-pl="product-title"], h1[class*="title"], ' +
        '[class*="product-title"] h1, [class*="ProductTitle"]'
    );
    if (titleEl) result.title = titleEl.innerText.trim();

    // Get product description / specifications
    // Strategy 1: Product description section (below images, often in an iframe or div)
    const descSels = [
        '[class*="product-description"]', '[class*="ProductDescription"]',
        '[class*="detail-desc"]', '[class*="detailDesc"]',
        '[id*="product-description"]', '[data-pl="product-description"]',
        '[class*="product-detail-info"]',
        '[class*="specification"] [class*="content"]',
    ];
    for (const sel of descSels) {
        try {
            const allEls = document.querySelectorAll(sel);
            for (const el of allEls) {
                const t = el.innerText.trim();
                const stripped = t.toLowerCase().replace(/[^a-z]/g, '');
                if (stripped === 'description' || stripped === 'descriptionreportviewmore'
                    || stripped === 'descriptionviewmore' || stripped === 'viewmore') continue;
                if (t.length > 50) {
                    result.description = t.substring(0, 2000);
                    break;
                }
            }
        } catch(e) {}
        if (result.description) break;
    }
    // Strategy 2: Specifications / attributes table
    if (!result.description || result.description.length < 50) {
        const specSels = [
            '[class*="specification"]', '[class*="Specification"]',
            '[class*="product-specs"]', '[class*="sku-info"]',
            '[class*="product-properties"]', '[class*="ItemSpecTable"]',
            '[class*="detail-attributes"]',
        ];
        let specs = [];
        for (const sel of specSels) {
            try {
                const el = document.querySelector(sel);
                if (el) {
                    // Extract key-value pairs from spec rows
                    const rows = el.querySelectorAll('li, tr, [class*="property-item"], [class*="attr-item"]');
                    for (const row of rows) {
                        const t = row.innerText.trim().replace(/\\s+/g, ' ');
                        if (t.length > 3 && t.length < 200) specs.push(t);
                    }
                    if (specs.length === 0) {
                        const t = el.innerText.trim();
                        if (t.length > 20) specs.push(t);
                    }
                }
            } catch(e) {}
            if (specs.length > 0) break;
        }
        if (specs.length > 0) {
            const specText = specs.join(' | ');
            result.description = result.description
                ? result.description + '\\n' + specText
                : specText.substring(0, 2000);
        }
    }
    // Strategy 3: removed — JSON "description" field is just the SEO meta title, not useful

    // Get price — try multiple strategies
    // Strategy 1: CSS selectors for known price elements
    const priceSels = [
        '[class*="product-price-current"]', '[class*="uniform-banner-box-price"]',
        '[class*="price--current"]', '.product-price-value',
        '[class*="snow-price_SnowPrice"]', '[class*="price-current"]',
        '[class*="sale-price"]', '[class*="salePrice"]',
        '[class*="multi--price"]', '[class*="price-sale"]',
        '[class*="es--wrap"] [class*="price"]',
        '[data-pl="product-price"]',
    ];
    for (const sel of priceSels) {
        try {
            const el = document.querySelector(sel);
            if (el) {
                const pText = el.innerText.trim();
                if (pText && /[\d]/.test(pText)) {
                    result.price = pText;
                    break;
                }
            }
        } catch(e) {}
    }
    // Strategy 2: Find any element that looks like a price near the top of the page
    if (!result.price) {
        try {
            const allEls = document.querySelectorAll('span, div, p, b, strong');
            for (const el of allEls) {
                const t = (el.innerText || '').trim();
                // Match: £9.30, $12.50, US $9.30, US$ 9.30, €15.00, etc
                if (/^(?:US\\s*)?[£$€¥]\\s*\\d+[.,]\\d{2}$/.test(t)) {
                    const rect = el.getBoundingClientRect();
                    // Must be in the top portion of the page (price area)
                    if (rect.top > 0 && rect.top < 800 && el.offsetParent !== null) {
                        result.price = t;
                        break;
                    }
                }
            }
        } catch(e) {}
    }
    // Strategy 3: Look for price in a wider format (e.g. "£ 9 . 30" split across elements)
    if (!result.price) {
        try {
            const priceContainers = document.querySelectorAll('[class*="price"], [class*="Price"]');
            for (const container of priceContainers) {
                const t = container.innerText.replace(/\\s+/g, '').trim();
                const m = t.match(/[£$€¥]\\d+[.,]\\d{2}/);
                if (m) {
                    result.price = m[0];
                    break;
                }
            }
        } catch(e) {}
    }
    // Strategy 4: extract price from page scripts/JSON data
    if (!result.price) {
        try {
            const scripts = document.querySelectorAll('script');
            for (const s of scripts) {
                const t = s.textContent || '';
                const priceMatch = t.match(/"formattedActivityPrice"\\s*:\\s*"([^"]+)"/);
                if (priceMatch) { result.price = priceMatch[1]; break; }
                const priceMatch2 = t.match(/"minAmount"\\s*:\\s*{\\s*"value"\\s*:\\s*([\\d.]+)/);
                if (priceMatch2) { result.price = '$' + priceMatch2[1]; break; }
                const priceMatch3 = t.match(/"discountPrice"\\s*:\\s*{\\s*"minPrice"\\s*:\\s*([\\d.]+)/);
                if (priceMatch3) { result.price = '$' + priceMatch3[1]; break; }
                const priceMatch4 = t.match(/"formattedPrice"\\s*:\\s*"([^"]+)"/);
                if (priceMatch4) { result.price = priceMatch4[1]; break; }
                const priceMatch5 = t.match(/"salePrice"\\s*:\\s*{[^}]*"formattedPrice"\\s*:\\s*"([^"]+)"/);
                if (priceMatch5) { result.price = priceMatch5[1]; break; }
            }
        } catch(e) {}
    }

    // Get shipping cost (AliExpress shows shipping in user's local currency, e.g. £3.52)
    // Strategy 1: DOM elements with shipping info
    const shipSels = [
        '[class*="shipping-value"]', '[class*="shipping-price"]',
        '[class*="dynamic-shipping"] [class*="price"]',
        '[class*="product-shipping"] [class*="price"]',
        '[class*="delivery"] [class*="price"]',
        '[class*="shipping-cost"]', '[data-pl="product-shipping"]',
        '[class*="dynamic-shipping"]',
        '[class*="service-commitment"] [class*="shipping"]',
        '[class*="Shipping"]',
    ];
    for (const sel of shipSels) {
        try {
            const el = document.querySelector(sel);
            if (el) {
                const sText = el.innerText.trim();
                const sLower = sText.toLowerCase();
                if (sLower.includes('free')) {
                    result.shipping = 'Free';
                    break;
                }
                // Match any currency: £3.52, $2.50, €1.80, etc.
                const sMatch = sText.match(/[£$€¥₽]\\s*([\\d,]+\\.?\\d*)/);
                if (sMatch) {
                    // Store as plain number — AliExpress shows in user's local currency (GBP)
                    result.shipping = sMatch[1].replace(',', '');
                    break;
                }
                // Also match "3.52" without currency symbol
                const sMatch2 = sText.match(/(\\d+[,.]\\d{2})/);
                if (sMatch2 && sLower.includes('ship')) {
                    result.shipping = sMatch2[1].replace(',', '');
                    break;
                }
            }
        } catch(e) {}
    }
    // Strategy 2: Script/JSON data
    if (!result.shipping) {
        try {
            const scripts = document.querySelectorAll('script');
            for (const s of scripts) {
                const t = s.textContent || '';
                if (t.includes('freightAmount')) {
                    const fm = t.match(/"freightAmount"\\s*:\\s*{\\s*"value"\\s*:\\s*([\\d.]+)/);
                    if (fm) {
                        result.shipping = parseFloat(fm[1]) === 0 ? 'Free' : fm[1];
                        break;
                    }
                }
                const freeMatch = t.match(/"isFreeship"\\s*:\\s*true/i);
                if (freeMatch) {
                    result.shipping = 'Free';
                    break;
                }
            }
        } catch(e) {}
    }
    // Strategy 3: Look for "Shipping: £X.XX" or "Free shipping" in page text
    if (!result.shipping) {
        const bodyText = document.body.innerText || '';
        const shipMatch = bodyText.match(/[Ss]hipping[:\\s]*[£$€]\\s*([\\d,]+\\.\\d{2})/);
        if (shipMatch) {
            result.shipping = shipMatch[1].replace(',', '');
        } else if (/free\\s+shipping/i.test(bodyText)) {
            result.shipping = 'Free';
        }
    }

    return result;
}
"""


# Cache for store-level moduleanalysis URL (same for all products in a store)
_cached_moduleanalysis_url = ""
# Track which desc strategy works for this store to skip slow ones
_store_desc_strategy = ""  # e.g. "s2", "s4", "s5", "none" — skip slow strategies
_store_desc_failures = 0   # consecutive desc failures — after 3, mark store as "none"

def scrape_product_detail(detail_tab, product_url, product_id, context=None, main_tab=None):
    global _cached_moduleanalysis_url, _store_desc_strategy, _store_desc_failures, _store_desc_failures
    """Visit a product detail page and extract all images + variations.

    Uses detail_tab (a dedicated tab) so the main search results tab is untouched.
    """
    result = {
        "all_images": [],
        "variations": [],
        "detail_title": "",
        "detail_price": "",
        "detail_shipping": "",
        "detail_description": "",
    }

    try:
        detail_tab.goto(product_url, wait_until="commit", timeout=12000)
        # Close any popup tabs that AliExpress opened (keep main + detail)
        if context:
            try:
                for p in context.pages:
                    if p != detail_tab and p != main_tab:
                        p.close()
            except Exception:
                pass

        # Check for CAPTCHA on detail tab — pause until solved
        if is_captcha(detail_tab):
            handle_captcha(detail_tab)
            # Also check main tab
            if main_tab:
                handle_captcha(main_tab)
            # Re-navigate after CAPTCHA is solved
            try:
                detail_tab.goto(product_url, wait_until="domcontentloaded", timeout=15000)
            except Exception:
                pass

        # Wait for product images to render
        try:
            detail_tab.wait_for_selector(
                'img[src*="alicdn"], [class*="gallery"], [class*="slider"]',
                timeout=3000
            )
        except Exception:
            pass

        # Dismiss any popups
        dismiss_popups(detail_tab)
        detail_tab.wait_for_timeout(500)

        # --- STEP 1: Extract images, title, variations from top of page ---
        data = detail_tab.evaluate(DETAIL_EXTRACT_JS)
        if data.get("images"):
            result["all_images"] = data["images"][:MAX_IMAGES]
        if data.get("variations"):
            result["variations"] = data["variations"]
        if data.get("title"):
            result["detail_title"] = data["title"]
        if data.get("shipping"):
            result["detail_shipping"] = data["shipping"]

        # --- STEP 2: Get price from the page ---
        # AliExpress uses fullwidth pound ￡ (U+FFE1) not regular £ (U+00A3)
        # Price is "￡ 10.79" in the sidebar, rendered as split elements.
        try:
            price_text = detail_tab.evaluate("""
            () => {
                // Strategy A: Collapse whitespace in price containers, match ￡ or £
                const priceSels = [
                    '[class*="price--current"]', '[class*="product-price-current"]',
                    '[class*="snow-price"]', '[class*="price-current"]',
                    '[class*="uniform-banner-box-price"]',
                    '[class*="sale-price"]', '[class*="salePrice"]',
                    '[class*="price"]',
                ];
                for (const sel of priceSels) {
                    const els = document.querySelectorAll(sel);
                    for (const el of els) {
                        if (!el.offsetParent) continue;
                        const t = el.innerText.replace(/\\s+/g, '').trim();
                        const m = t.match(/[£￡$€]\\d+[.,]\\d{2}/);
                        if (m) return m[0].replace('￡', '£');
                    }
                }
                // Strategy B: ALL visible elements
                const allEls = document.querySelectorAll('span, div, strong, b');
                for (const el of allEls) {
                    if (!el.offsetParent) continue;
                    const t = el.innerText.replace(/\\s+/g, '').trim();
                    if (t.length > 30) continue;
                    const m = t.match(/[£￡$€]\\d+[.,]\\d{2}/);
                    if (m) {
                        const rect = el.getBoundingClientRect();
                        if (rect.top > 0 && rect.top < 800) return m[0].replace('￡', '£');
                    }
                }
                // Strategy C: JSON data
                const scripts = document.querySelectorAll('script');
                for (const s of scripts) {
                    const t = s.textContent || '';
                    const patterns = [
                        /"formattedActivityPrice"\\s*:\\s*"([^"]+)"/,
                        /"formattedPrice"\\s*:\\s*"([^"]+)"/,
                    ];
                    for (const pat of patterns) {
                        const m = t.match(pat);
                        if (m) return m[1].replace('￡', '£');
                    }
                    const m2 = t.match(/"minAmount"\\s*:\\s*{\\s*"value"\\s*:\\s*([\\d.]+)/);
                    if (m2) return '£' + m2[1];
                }
                return '';
            }
            """)
            if price_text:
                result["detail_price"] = price_text
                log.info("      Price: %s", price_text)
        except Exception:
            pass

        # If few images, scroll a bit and retry
        if len(result["all_images"]) <= 2:
            try:
                detail_tab.evaluate("window.scrollTo(0, 400)")
                detail_tab.wait_for_timeout(400)
                data2 = detail_tab.evaluate(DETAIL_EXTRACT_JS)
                if data2.get("images") and len(data2["images"]) > len(result["all_images"]):
                    result["all_images"] = data2["images"][:MAX_IMAGES]
            except Exception:
                pass

        # --- STEP 3: Get specs + description from page's embedded JSON data ---
        # DO NOT click tabs or View more — they open the reviews popup.
        # AliExpress embeds all product data in <script> tags as JSON.
        try:
            detail_tab.evaluate("void(0)")
            specs_and_desc = detail_tab.evaluate("""
            () => {
                const result = { specs: '', desc: '' };
                const scripts = document.querySelectorAll('script');

                // ---- SPECS: from JSON productPropList / props ----
                let specLines = [];
                for (const s of scripts) {
                    const t = s.textContent || '';
                    // Try productPropList
                    const m1 = t.match(/"productPropList"\\s*:\\s*(\\[[^\\]]{10,}\\])/);
                    if (m1) {
                        try {
                            const attrs = JSON.parse(m1[1]);
                            for (const a of attrs) {
                                const n = a.attrName || a.name || '';
                                const v = a.attrValue || a.value || '';
                                if (!n || !v) continue;
                                const low = n.toLowerCase();
                                if (low.includes('brand') || low.includes('origin') || low.includes('country')
                                    || low.includes('chemical') || low.includes('warning') || low.includes('hazard')
                                    || low.includes('regulatory')) continue;
                                specLines.push(n + ': ' + v);
                            }
                        } catch(e) {}
                    }
                    // Try props array
                    if (specLines.length === 0) {
                        const m2 = t.match(/"props"\\s*:\\s*(\\[[^\\]]{10,}\\])/);
                        if (m2) {
                            try {
                                const props = JSON.parse(m2[1]);
                                for (const p of props) {
                                    const n = p.attrName || p.name || p.key || '';
                                    const v = p.attrValue || p.value || p.val || '';
                                    if (!n || !v) continue;
                                    const low = n.toLowerCase();
                                    if (low.includes('brand') || low.includes('origin') || low.includes('country')
                                        || low.includes('chemical') || low.includes('warning') || low.includes('hazard')
                                        || low.includes('regulatory')) continue;
                                    specLines.push(n + ': ' + v);
                                }
                            } catch(e) {}
                        }
                    }
                    if (specLines.length > 0) break;
                }
                result.specs = specLines.join(' | ');

                return result;
            }
            """)

            specs_text = specs_and_desc.get("specs", "")
            desc_text = ""

            # --- DESCRIPTION EXTRACTION ---
            # Strategy 1: Find descriptionUrl in page source and fetch it
            # Strategy 2: Scroll to description section and extract from DOM
            # Strategy 3: Use AliExpress API to get description HTML

            # If we already know which strategy works for this store, try it first
            # and skip slow strategies (especially Strategy 4's 2s+ wait)
            if _store_desc_strategy == "s5" and not desc_text:
                log.info("      Desc: trying Strategy 5 (cached as working for store)...")
                try:
                    s5_result = detail_tab.evaluate("""
                    () => {
                        function extractDesc(html) {
                            if (!html || html.length < 100) return null;
                            if (!/<[a-z][^>]*>/i.test(html)) return null;
                            const tmp = document.createElement('div');
                            tmp.innerHTML = html;
                            let firstImg = '';
                            tmp.querySelectorAll('img').forEach(img => {
                                if (firstImg) return;
                                const src = img.src || img.getAttribute('src') || img.getAttribute('data-src') || '';
                                if (src && (src.includes('alicdn') || src.includes('ae01') || src.includes('ae04'))
                                    && !src.includes('icon') && !src.includes('logo')) firstImg = src;
                            });
                            tmp.querySelectorAll('img, script, style, video').forEach(e => e.remove());
                            let text = tmp.innerText.trim();
                            if (text.length < 150) return null;
                            if (/^Buy\\s/i.test(text)) return null;
                            if (/^Smarter Shopping/i.test(text)) return null;
                            return {text: text.substring(0, 3000), img: firstImg};
                        }
                        const scripts = document.querySelectorAll('script');
                        for (const s of scripts) {
                            const t = s.textContent || '';
                            if (t.length < 200 || t.length > 500000) continue;
                            const patterns = [
                                /"(?:descriptionContent|descriptionHtml|detailDesc|descContent)"\\s*:\\s*"((?:[^"\\\\]|\\\\.)*)"/i,
                                /"(?:itemDescription|product_description|descriptionModule)"\\s*:\\s*"((?:[^"\\\\]|\\\\.)*)"/i,
                            ];
                            for (const p of patterns) {
                                const m = t.match(p);
                                if (m && m[1] && m[1].length > 100) {
                                    let html = m[1];
                                    try { html = JSON.parse('"' + html + '"'); } catch(e) {}
                                    const r = extractDesc(html);
                                    if (r) return JSON.stringify(r);
                                }
                            }
                        }
                        const globals = [window.runParams, window.__INIT_DATA__,
                            window.runConfig, window.detailData, window.pageData, window.__pageData__];
                        function deepSearch(obj, depth) {
                            if (!obj || depth > 6) return null;
                            if (typeof obj === 'string' && obj.length > 200 && /<[a-z][^>]*>/i.test(obj)) {
                                const r = extractDesc(obj);
                                if (r) return r;
                            }
                            if (typeof obj !== 'object') return null;
                            try {
                                for (const [k, v] of Object.entries(obj)) {
                                    const kl = k.toLowerCase();
                                    if (kl.includes('og') || kl.includes('meta') || kl.includes('seo')
                                        || kl === 'title' || kl === 'name' || kl === 'subject') continue;
                                    if (kl.includes('desc') || kl.includes('description') || kl === 'detail'
                                        || kl === 'descriptionmodule') {
                                        const r = deepSearch(v, depth + 1);
                                        if (r) return r;
                                    }
                                }
                            } catch(e) {}
                            return null;
                        }
                        for (const g of globals) {
                            if (!g) continue;
                            const r = deepSearch(g, 0);
                            if (r) return JSON.stringify(r);
                        }
                        return '';
                    }
                    """) or ""
                    if s5_result:
                        import json as _json7b
                        parsed = _json7b.loads(s5_result)
                        _s5t = (parsed.get("text") or "").strip()
                        # Python-side reject: titles/meta, not real descriptions
                        if _s5t and len(_s5t) >= 300 and not _s5t.startswith("Buy ") and not _s5t.startswith("Smarter Shopping"):
                            desc_text = _s5t
                            log.info("      Desc Strategy 5 (cached): got %d chars", len(desc_text))
                            s5_img = parsed.get("img", "")
                            if s5_img and s5_img not in result["all_images"] and len(result["all_images"]) < MAX_IMAGES:
                                result["all_images"].append(s5_img)
                                log.info("      Desc: added 1st description image (total: %d)", len(result["all_images"]))
                        elif _s5t:
                            log.info("      Desc Strategy 5 (cached): rejected (%d chars, starts='%s')", len(_s5t), _s5t[:30])
                except Exception:
                    pass

            # Strategy 1: Search page source for description URL (skip if cache exists)
            desc_url = ""
            if not _cached_moduleanalysis_url and not desc_text:
                log.info("      Desc: trying Strategy 1 (descriptionUrl in page source)...")
                try:
                    desc_url = detail_tab.evaluate("""
                () => {
                    // First check global JS data objects that AliExpress uses
                    const globals = [
                        window.runParams, window.__INIT_DATA__,
                        window.runConfig, window.detailData,
                        window.pageData, window.__pageData__
                    ];
                    for (const g of globals) {
                        if (!g) continue;
                        const s = JSON.stringify(g);
                        const m = s.match(/"descriptionUrl"\\s*:\\s*"([^"]+)"/);
                        if (m) {
                            let url = m[1];
                            if (url.startsWith('//')) url = 'https:' + url;
                            return '__FOUND_GLOBAL__:' + url;
                        }
                    }

                    const html = document.documentElement.innerHTML;
                    // Try various patterns for the description URL
                    const patterns = [
                        /"descriptionUrl"\\s*:\\s*"(https?:[^"]+)"/,
                        /"descriptionUrl"\\s*:\\s*"(\\/\\/[^"]+)"/,
                        /descriptionUrl['":\\s]+(https?:\\/\\/[^"'\\s,}]+)/,
                        /(https?:\\/\\/[a-z0-9-]+\\.alicdn\\.com\\/[^"'\\s]*desc[^"'\\s]*\\.htm[l]?)/i,
                        /(\\/\\/[a-z0-9-]+\\.alicdn\\.com\\/[^"'\\s]*desc[^"'\\s]*\\.htm[l]?)/i,
                    ];
                    for (const p of patterns) {
                        const m = html.match(p);
                        if (m) {
                            let url = m[1];
                            if (url.startsWith('//')) url = 'https:' + url;
                            return url;
                        }
                    }

                    // Debug: search for ANY mention of "description" near a URL
                    const descContext = html.match(/.{0,50}description.{0,200}/i);
                    if (descContext) return '__DEBUG__:' + descContext[0].substring(0, 200);

                    return '';
                    }
                    """) or ""
                except Exception as e:
                    log.info("      Desc Strategy 1 error: %s", str(e)[:120])
                    desc_url = ""

            if desc_url and desc_url.startswith("__DEBUG__:"):
                log.info("      Desc Strategy 1 debug (no URL, but found context): %s", desc_url[10:200])
                desc_url = ""
            elif desc_url and desc_url.startswith("__FOUND_GLOBAL__:"):
                desc_url = desc_url[17:]
                log.info("      Desc Strategy 1: found URL in global JS: %s", desc_url[:120])

            if desc_url:
                log.info("      Desc URL found: %s", desc_url[:120])
                try:
                    desc_text = detail_tab.evaluate("""
                    async (url) => {
                        try {
                            const resp = await fetch(url);
                            const html = await resp.text();
                            const tmp = document.createElement('div');
                            tmp.innerHTML = html;
                            tmp.querySelectorAll('img, script, style, video').forEach(e => e.remove());
                            let text = tmp.innerText.trim();
                            const lower = text.toLowerCase();
                            for (const cut of ['additional regulatory', 'regulatory information']) {
                                const idx = lower.indexOf(cut);
                                if (idx > 0) { text = text.substring(0, idx).trim(); break; }
                            }
                            return text.substring(0, 3000);
                        } catch(e) { return ''; }
                    }
                    """, desc_url) or ""
                except Exception:
                    pass

            # Strategy 2: Try API endpoints (non-destructive, no page changes)
            if not desc_text and product_id:
                log.info("      Desc: trying Strategy 2 (API endpoints)...")
                # Try to find moduleanalysis params from page source
                try:
                    module_url = detail_tab.evaluate("""
                    () => {
                        const html = document.documentElement.innerHTML;
                        // Look for moduleIds and adminAccountId in page source
                        const moduleMatch = html.match(/moduleIds[=:]["']?(\\d+)/);
                        const adminMatch = html.match(/adminAccountId[=:]["']?(\\d+)/);
                        if (moduleMatch && adminMatch) {
                            return 'https://moduleanalysis.aliexpress.com/item/desc/module/analysis.json?moduleIds='
                                + moduleMatch[1] + '&adminAccountId=' + adminMatch[1];
                        }
                        // Also check script tags for storeModule or descriptionModule
                        const scripts = document.querySelectorAll('script');
                        for (const s of scripts) {
                            const t = s.textContent || '';
                            const m1 = t.match(/"moduleId"\\s*:\\s*(\\d+)/);
                            const m2 = t.match(/"adminAccountId"\\s*:\\s*"?(\\d+)/);
                            if (m1 && m2) {
                                return 'https://moduleanalysis.aliexpress.com/item/desc/module/analysis.json?moduleIds='
                                    + m1[1] + '&adminAccountId=' + m2[1];
                            }
                        }
                        return '';
                    }
                    """) or ""
                except Exception:
                    module_url = ""
                api_urls = []
                # Try cached moduleanalysis URL first (same for all products in a store)
                if _cached_moduleanalysis_url:
                    api_urls.append(_cached_moduleanalysis_url)
                    log.info("      Desc: using cached moduleanalysis URL")
                if module_url and module_url not in api_urls:
                    api_urls.append(module_url)
                    log.info("      Desc: found moduleanalysis URL: %s", module_url[:120])
                api_urls.extend([
                    f"https://www.aliexpress.com/aer-api/module/item/description?productId={product_id}",
                    f"https://www.aliexpress.com/fn/item-description/index.html?productId={product_id}",
                    f"https://aeproductsourcesite.alicdn.com/product/description/pc/{product_id}.html",
                    f"https://www.aliexpress.com/aeglobal/ae/item/description/query?productId={product_id}",
                    f"https://www.aliexpress.com/aer-jsonapi/module/item/description?productId={product_id}",
                ])
                for api_url in api_urls:
                    if desc_text:
                        break
                    try:
                        desc_text = detail_tab.evaluate("""
                        async (url) => {
                            try {
                                const resp = await fetch(url, {credentials: 'include'});
                                if (!resp.ok) return '';
                                const contentType = resp.headers.get('content-type') || '';
                                const body = await resp.text();
                                // If JSON response, extract HTML from it
                                let html = body;
                                if (contentType.includes('json') || body.trim().startsWith('{')) {
                                    try {
                                        const j = JSON.parse(body);
                                        // moduleanalysis format: {data: {moduleId: "html content"}}
                                        if (j.data && typeof j.data === 'object' && !j.data.description) {
                                            const values = Object.values(j.data);
                                            for (const v of values) {
                                                if (typeof v === 'string' && v.length > 50) {
                                                    html = v;
                                                    break;
                                                }
                                            }
                                        }
                                        if (html === body) {
                                            html = j.data?.description || j.data?.content || j.description || j.content || j.result || '';
                                            if (typeof html !== 'string') html = JSON.stringify(html);
                                        }
                                    } catch(e) { html = body; }
                                }
                                const tmp = document.createElement('div');
                                tmp.innerHTML = html;
                                // Get first description image before removing imgs
                                let firstImg = '';
                                tmp.querySelectorAll('img').forEach(img => {
                                    if (firstImg) return;
                                    const src = img.src || img.getAttribute('src') || img.getAttribute('data-src') || '';
                                    if (src && src.includes('alicdn') && !src.includes('icon')
                                        && !src.includes('logo') && !src.includes('thumbnail')) {
                                        firstImg = src;
                                    }
                                });
                                if (!firstImg) {
                                    const imgMatch = html.match(/src=['"]?(https?:\/\/[^'"\\s>]+(?:alicdn|ae01|ae04)[^'"\\s>]*\\.(?:jpg|png|jpeg|webp))/i);
                                    if (imgMatch) firstImg = imgMatch[1];
                                }
                                tmp.querySelectorAll('img, script, style, video').forEach(e => e.remove());
                                let text = tmp.innerText.trim();
                                // Reject 404 pages and garbage
                                if (text.includes('404') || text.includes("can't find") || text.includes('Sorry')) return '';
                                if (/^Buy\\s/i.test(text)) return '';
                                if (text.length >= 50) return JSON.stringify({text: text.substring(0, 3000), img: firstImg});
                                return '';
                            } catch(e) { return ''; }
                        }
                        """, api_url) or ""
                        if desc_text:
                            try:
                                import json as _json2
                                parsed2 = _json2.loads(desc_text)
                                desc_text = parsed2.get("text", desc_text)
                                s2_img = parsed2.get("img", "")
                                # Python-side: if JS returned raw JSON text, parse it
                                if desc_text and desc_text.lstrip().startswith("{"):
                                    try:
                                        j2 = _json2.loads(desc_text)
                                        if isinstance(j2.get("data"), dict):
                                            for v in j2["data"].values():
                                                if isinstance(v, str) and len(v) > 50:
                                                    import re as _re3
                                                    clean = _re3.sub(r'<[^>]+>', ' ', v)
                                                    desc_text = _re3.sub(r'\s+', ' ', clean).strip()[:3000]
                                                    if not s2_img:
                                                        img_m = _re3.search(r'src=["\']?(https?://[^"\'>\s]+(?:alicdn|ae01|ae04)[^"\'>\s]*\.(?:jpg|png|jpeg|webp))', v, _re3.IGNORECASE)
                                                        if img_m:
                                                            s2_img = img_m.group(1)
                                                    break
                                    except Exception:
                                        pass
                                if s2_img and s2_img not in result["all_images"] and len(result["all_images"]) < MAX_IMAGES:
                                    result["all_images"].append(s2_img)
                                    log.info("      Desc: added 1st description image (total: %d)", len(result["all_images"]))
                            except (json.JSONDecodeError, TypeError, ValueError):
                                # desc_text might be raw moduleanalysis JSON
                                if desc_text.lstrip().startswith("{"):
                                    try:
                                        import json as _json2b
                                        import re as _re3b
                                        j2 = _json2b.loads(desc_text)
                                        if isinstance(j2.get("data"), dict):
                                            for v in j2["data"].values():
                                                if isinstance(v, str) and len(v) > 50:
                                                    clean = _re3b.sub(r'<[^>]+>', ' ', v)
                                                    desc_text = _re3b.sub(r'\s+', ' ', clean).strip()[:3000]
                                                    img_m = _re3b.search(r'src=["\']?(https?://[^"\'>\s]+(?:alicdn|ae01|ae04)[^"\'>\s]*\.(?:jpg|png|jpeg|webp))', v, _re3b.IGNORECASE)
                                                    if img_m and img_m.group(1) not in result["all_images"] and len(result["all_images"]) < MAX_IMAGES:
                                                        result["all_images"].append(img_m.group(1))
                                                    break
                                    except Exception:
                                        desc_text = ""
                            # Reject JS code
                            if desc_text and (desc_text.lstrip().startswith("/*") or "function(e){" in desc_text[:100]):
                                desc_text = ""
                            if desc_text:
                                log.info("      Desc Strategy 2: got %d chars from %s", len(desc_text), api_url[:80])
                                if not _store_desc_strategy:
                                    _store_desc_strategy = "s2"
                            # Cache moduleanalysis URL if it worked
                            if "moduleanalysis" in api_url:
                                _cached_moduleanalysis_url = api_url
                    except Exception:
                        pass

            # Strategy 3: Extract description from page's embedded JSON data (skip if cache exists)
            if not desc_text and not _cached_moduleanalysis_url:
                log.info("      Desc: trying Strategy 3 (embedded page JSON)...")
                try:
                    desc_text = detail_tab.evaluate("""
                    () => {
                        const html = document.documentElement.innerHTML;

                        // Look for description in embedded data
                        const dataPatterns = [
                            /"descriptionContent"\\s*:\\s*"([^"]{50,})"/,
                            /"detailDesc"\\s*:\\s*"([^"]{50,})"/,
                            /"detail"\\s*:\\s*\\{[^}]*"description"\\s*:\\s*"([^"]{50,})"/,
                        ];
                        for (const p of dataPatterns) {
                            const m = html.match(p);
                            if (m) {
                                try {
                                    let text = JSON.parse('"' + m[1] + '"');
                                    if (/^Buy\\s/i.test(text.trim())) continue;
                                    if (text.includes('<')) {
                                        const tmp = document.createElement('div');
                                        tmp.innerHTML = text;
                                        tmp.querySelectorAll('img, script, style, video').forEach(e => e.remove());
                                        text = tmp.innerText.trim();
                                    }
                                    if (text.length >= 50) return text.substring(0, 3000);
                                } catch(e) {}
                            }
                        }

                        // Look for descriptionUrl in any format
                        const urlPatterns = [
                            /['"](https?:\/\/[^'"\\s]*desc[^'"\\s]*\.html?)['"]/i,
                            /['"](\/\/[^'"\\s]*desc[^'"\\s]*\.html?)['"]/i,
                            /['"](https?:\/\/[^'"\\s]*alicdn[^'"\\s]*desc[^'"\\s]*)['"]/i,
                        ];
                        for (const p of urlPatterns) {
                            const m = html.match(p);
                            if (m) {
                                return '__URL__:' + m[1];
                            }
                        }

                        // Search script content for HTML description
                        const scripts = document.querySelectorAll('script');
                        for (const s of scripts) {
                            const t = s.textContent || '';
                            if (t.length < 200) continue;
                            const htmlMatch = t.match(/"(?:description|desc|detail)(?:Html|Content|Text)?"\\s*:\\s*"(<[^"]{100,})"/i);
                            if (htmlMatch) {
                                try {
                                    let decoded = JSON.parse('"' + htmlMatch[1] + '"');
                                    const tmp = document.createElement('div');
                                    tmp.innerHTML = decoded;
                                    tmp.querySelectorAll('img, script, style, video').forEach(e => e.remove());
                                    const text = tmp.innerText.trim();
                                    if (text.length >= 50) return text.substring(0, 3000);
                                } catch(e) {}
                            }
                        }

                        return '';
                    }
                    """) or ""

                    if desc_text and desc_text.startswith("__URL__:"):
                        found_url = desc_text[8:]
                        if found_url.startswith("//"):
                            found_url = "https:" + found_url
                        log.info("      Desc Strategy 3: found desc URL: %s", found_url[:120])
                        try:
                            desc_text = detail_tab.evaluate("""
                            async (url) => {
                                try {
                                    const resp = await fetch(url);
                                    if (!resp.ok) return '';
                                    const html = await resp.text();
                                    const tmp = document.createElement('div');
                                    tmp.innerHTML = html;
                                    tmp.querySelectorAll('img, script, style, video').forEach(e => e.remove());
                                    let text = tmp.innerText.trim();
                                    if (text.length >= 50) return text.substring(0, 3000);
                                    return '';
                                } catch(e) { return ''; }
                            }
                            """, found_url) or ""
                        except Exception:
                            desc_text = ""
                    elif desc_text:
                        log.info("      Desc Strategy 3: got %d chars from embedded JSON", len(desc_text))
                except Exception as e:
                    log.info("      Desc Strategy 3 error: %s", str(e)[:120])

            # Strategy 4: Intercept network requests + click View More
            # Skip if Strategy 5 is known to work for this store (saves ~5s per product)
            if not desc_text and _store_desc_strategy != "s5":
                log.info("      Desc: trying Strategy 4 (network intercept + View More)...")
                try:
                    # Set up network request capture BEFORE clicking View More
                    # Capture ALL JSON/HTML responses — some stores use URLs without "desc" keyword
                    captured_urls = []
                    def _on_response(response):
                        try:
                            url = response.url
                            ct = response.headers.get("content-type", "") or ""
                            ul = url.lower()
                            # Capture: desc-related URLs OR any JSON/HTML response (could be description)
                            is_desc_url = any(k in ul for k in ["desc", "description", "detail-desc",
                                    "moduleanalysis", "item/detail", "richtext", "item-description",
                                    "module/analysis", "product/detail"])
                            is_content = ("json" in ct or "html" in ct) and response.status == 200
                            # Skip tracking/analytics/images
                            is_noise = any(k in ul for k in ["goldlog", "beacon", "tracker", "analytics",
                                    ".png", ".jpg", ".gif", ".webp", ".css", ".js", "google", "facebook",
                                    "lazada", "aplus", "retcode", "arms", "wpk."])
                            if is_desc_url or (is_content and not is_noise):
                                captured_urls.append({"url": url, "status": response.status, "ct": ct,
                                                      "is_desc": is_desc_url})
                        except Exception:
                            pass
                    detail_tab.on("response", _on_response)

                    # Scroll to bottom to trigger lazy loading
                    detail_tab.evaluate("window.scrollTo(0, document.body.scrollHeight)")
                    detail_tab.wait_for_timeout(800)
                    detail_tab.evaluate("window.scrollTo(0, document.body.scrollHeight)")
                    detail_tab.wait_for_timeout(500)

                    # Click the description "View more"
                    try:
                        clicked_vm = detail_tab.evaluate("""
                        () => {
                            let regulatoryY = Infinity;
                            const allEls = document.querySelectorAll('h2, h3, h4, div, span, p, strong, b');
                            for (const el of allEls) {
                                const t = (el.innerText || '').trim().toLowerCase();
                                if (t.includes('additional regulatory') || t.includes('regulatory information')) {
                                    regulatoryY = el.getBoundingClientRect().top + window.scrollY;
                                    break;
                                }
                            }
                            const vmButtons = [];
                            const candidates = document.querySelectorAll('button, span, div, a');
                            for (const btn of candidates) {
                                if (btn.children.length > 3) continue;
                                const text = (btn.innerText || '').trim().toLowerCase();
                                if (text !== 'view more' && text !== 'show more' && text !== 'see more') continue;
                                const btnY = btn.getBoundingClientRect().top + window.scrollY;
                                vmButtons.push({btn, y: btnY});
                            }
                            if (vmButtons.length === 0) return false;
                            if (regulatoryY < Infinity) {
                                let bestBtn = null, bestDist = Infinity;
                                for (const {btn, y} of vmButtons) {
                                    const dist = regulatoryY - y;
                                    if (dist > 0 && dist < bestDist) { bestBtn = btn; bestDist = dist; }
                                }
                                if (bestBtn) { bestBtn.scrollIntoView({block: 'center'}); bestBtn.click(); return 'above regulatory'; }
                            }
                            const descEl = document.querySelector('[class*="description--wrap"], [class*="description--store"], .product-description, [class*="product-description"]');
                            if (descEl) {
                                const descY = descEl.getBoundingClientRect().top + window.scrollY;
                                let bestBtn = null, bestDist = Infinity;
                                for (const {btn, y} of vmButtons) {
                                    const dist = y - descY;
                                    if (dist > 0 && dist < 2000 && dist < bestDist) { bestBtn = btn; bestDist = dist; }
                                }
                                if (bestBtn) { bestBtn.scrollIntoView({block: 'center'}); bestBtn.click(); return 'near description'; }
                            }
                            // Last resort: click the first View More
                            vmButtons[0].btn.scrollIntoView({block: 'center'});
                            vmButtons[0].btn.click();
                            return 'first button';
                        }
                        """)
                        if clicked_vm:
                            log.info("      Desc: clicked View More (%s)", str(clicked_vm)[:40])
                    except Exception:
                        pass

                    # Wait for content to appear (network fetch or CSS toggle)
                    detail_tab.wait_for_timeout(2000)

                    # IMMEDIATE DOM scan after View More click — catches CSS-toggled content
                    # that was hidden and is now visible (no network request needed)
                    if not desc_text:
                        try:
                            vm_result = detail_tab.evaluate("""
                            () => {
                                // After View More click, look for any large visible text block
                                // that looks like a product description
                                // Try known description containers first
                                const sels = [
                                    '[class*="product-description"]', '[class*="detail-desc"]',
                                    '[class*="description--"]', '[class*="ItemDescription"]',
                                    '[class*="desc-content"]', '[class*="desc_rich"]',
                                    '[class*="richtext"]', '[class*="detail-content"]',
                                    '.product-description', '.detailmodule_html',
                                    '#product-description', '[data-pl="product-description"]',
                                    'div[data-spm="description"]',
                                    // Newer AliExpress patterns
                                    '[class*="expand"]', '[class*="toggle-content"]',
                                    '[class*="collapse"][class*="show"]',
                                    '[class*="description"][class*="content"]',
                                ];
                                for (const sel of sels) {
                                    try {
                                        const els = document.querySelectorAll(sel);
                                        for (const el of els) {
                                            if (!el) continue;
                                            // Skip invisible elements
                                            const style = window.getComputedStyle(el);
                                            if (style.display === 'none' || style.visibility === 'hidden') continue;
                                            // Check for substantial content
                                            const clone = el.cloneNode(true);
                                            // Get first description image before removing
                                            let firstImg = '';
                                            el.querySelectorAll('img').forEach(img => {
                                                if (firstImg) return;
                                                const src = img.src || img.getAttribute('data-src') || '';
                                                if (src && (src.includes('alicdn') || src.includes('ae01') || src.includes('ae04'))
                                                    && !src.includes('icon') && !src.includes('logo')
                                                    && !src.includes('thumbnail')) firstImg = src;
                                            });
                                            clone.querySelectorAll('img, script, style, video, iframe').forEach(e => e.remove());
                                            let text = clone.innerText.trim();
                                            // Skip placeholder text
                                            const stripped = text.toLowerCase().replace(/[^a-z]/g, '');
                                            if (['description','descriptionreportviewmore','descriptionviewmore',
                                                 'viewmore','descriptionreport','showmore','seemore'].includes(stripped)) continue;
                                            // Cut at regulatory section
                                            for (const cut of ['additional regulatory', 'regulatory information',
                                                               'shipping info', 'return policy']) {
                                                const idx = text.toLowerCase().indexOf(cut);
                                                if (idx > 0) { text = text.substring(0, idx).trim(); break; }
                                            }
                                            if (text.length >= 50 || firstImg)
                                                return JSON.stringify({text: text.substring(0, 3000), img: firstImg});
                                        }
                                    } catch(e) {}
                                }
                                // Broader fallback: find ANY large visible text block near the View More area
                                // Walk the DOM looking for containers with substantial text
                                const allDivs = document.querySelectorAll('div, section, article');
                                for (const div of allDivs) {
                                    try {
                                        const style = window.getComputedStyle(div);
                                        if (style.display === 'none' || style.visibility === 'hidden') continue;
                                        // Only check leaf-ish containers (not too many children)
                                        if (div.children.length > 50) continue;
                                        const html = div.innerHTML;
                                        // Must have substantial HTML with images or formatted text
                                        if (html.length < 200) continue;
                                        // Must contain img tags with alicdn sources — description sections have product images
                                        const hasDescImg = /<img[^>]+(?:alicdn|ae01|ae04)[^>]+>/i.test(html);
                                        if (!hasDescImg) continue;
                                        let firstImg = '';
                                        div.querySelectorAll('img').forEach(img => {
                                            if (firstImg) return;
                                            const src = img.src || img.getAttribute('data-src') || '';
                                            if (src && (src.includes('alicdn') || src.includes('ae01') || src.includes('ae04'))
                                                && !src.includes('icon') && !src.includes('logo')
                                                && !src.includes('thumbnail') && !src.includes('avatar')) firstImg = src;
                                        });
                                        const clone = div.cloneNode(true);
                                        clone.querySelectorAll('img, script, style, video, iframe').forEach(e => e.remove());
                                        let text = clone.innerText.trim();
                                        // Must be a real description, not navigation or headers
                                        if (text.length >= 100 || firstImg) {
                                            for (const cut of ['additional regulatory', 'regulatory information']) {
                                                const idx = text.toLowerCase().indexOf(cut);
                                                if (idx > 0) { text = text.substring(0, idx).trim(); break; }
                                            }
                                            return JSON.stringify({text: text.substring(0, 3000), img: firstImg});
                                        }
                                    } catch(e) {}
                                }
                                return '';
                            }
                            """) or ""
                            if vm_result:
                                import json as _json_vm
                                parsed_vm = _json_vm.loads(vm_result)
                                t = parsed_vm.get("text", "")
                                img = parsed_vm.get("img", "")
                                if t and len(t) >= 50 and not t.startswith("Buy "):
                                    desc_text = t
                                    log.info("      Desc: got %d chars from DOM after View More click", len(desc_text))
                                    if not _store_desc_strategy:
                                        _store_desc_strategy = "s4dom"
                                if img and img not in result["all_images"] and len(result["all_images"]) < MAX_IMAGES:
                                    result["all_images"].append(img)
                                    log.info("      Desc: added 1st description image (total: %d)", len(result["all_images"]))
                        except Exception:
                            pass

                    # Remove listener
                    try:
                        detail_tab.remove_listener("response", _on_response)
                    except Exception:
                        pass

                    # Sort captured URLs: desc-related first, then others
                    if captured_urls:
                        captured_urls.sort(key=lambda x: (0 if x.get("is_desc") else 1))
                        for cu in captured_urls[:8]:
                            log.info("      Desc captured: %s (status=%s, ct=%s, desc=%s)",
                                     cu["url"][:120], cu["status"], cu["ct"][:40], cu.get("is_desc"))
                            # Cache moduleanalysis URL for reuse across products
                            if "moduleanalysis" in cu["url"] and int(cu["status"]) == 200:
                                _cached_moduleanalysis_url = cu["url"]
                                log.info("      Desc: CACHED moduleanalysis URL for store")

                    # Try to fetch each captured URL for description content
                    desc_img = ""
                    for cu in captured_urls:
                        if desc_text:
                            break
                        if cu["status"] != 200:
                            continue
                        try:
                            fetch_result = detail_tab.evaluate("""
                            async (url) => {
                                try {
                                    const resp = await fetch(url);
                                    let body = await resp.text();

                                    // Handle JSON responses (moduleanalysis API returns {data: {id: "html..."}})
                                    let html = body;
                                    if (body.trim().startsWith('{')) {
                                        try {
                                            const j = JSON.parse(body);
                                            // moduleanalysis format: {data: {moduleId: "html content"}}
                                            if (j.data && typeof j.data === 'object') {
                                                const values = Object.values(j.data);
                                                for (const v of values) {
                                                    if (typeof v === 'string' && v.length > 50) {
                                                        html = v;
                                                        break;
                                                    }
                                                }
                                            }
                                            // Other JSON formats
                                            if (html === body) {
                                                html = j.data?.description || j.data?.content ||
                                                       j.description || j.content || j.result || body;
                                                if (typeof html !== 'string') html = body;
                                            }
                                        } catch(e) {}
                                    }

                                    const tmp = document.createElement('div');
                                    tmp.innerHTML = html;
                                    // Get first description image
                                    let firstImg = '';
                                    tmp.querySelectorAll('img').forEach(img => {
                                        if (firstImg) return;
                                        const src = img.src || img.getAttribute('src') || img.getAttribute('data-src') || '';
                                        if (src && src.includes('alicdn') && !src.includes('icon')
                                            && !src.includes('logo') && !src.includes('thumbnail')) {
                                            firstImg = src;
                                        }
                                    });
                                    // Also check for img src in raw HTML
                                    if (!firstImg) {
                                        const imgMatch = html.match(/src=['"]?(https?:\/\/[^'"\\s>]+(?:alicdn|ae01|ae04)[^'"\\s>]*\\.(?:jpg|png|jpeg|webp))/i);
                                        if (imgMatch) firstImg = imgMatch[1];
                                    }
                                    tmp.querySelectorAll('img, script, style, video, iframe').forEach(e => e.remove());
                                    let text = tmp.innerText.trim();
                                    // Reject JavaScript code
                                    if (/^\s*(\/\*|!function|\(function|function\s*\()/.test(text))
                                        return '';
                                    for (const cut of ['additional regulatory', 'regulatory information']) {
                                        const idx = text.toLowerCase().indexOf(cut);
                                        if (idx > 0) { text = text.substring(0, idx).trim(); break; }
                                    }
                                    if (text.length < 50 && !firstImg) return '';
                                    return JSON.stringify({text: text.substring(0, 3000), img: firstImg, htmlLen: html.length});
                                } catch(e) { return ''; }
                            }
                            """, cu["url"]) or ""
                            if fetch_result:
                                import json as _json4
                                parsed = _json4.loads(fetch_result)
                                t = parsed.get("text", "")
                                img = parsed.get("img", "")
                                # Python-side safety: if JS didn't parse the JSON, do it here
                                if t and t.lstrip().startswith("{"):
                                    try:
                                        j = _json4.loads(t)
                                        if isinstance(j.get("data"), dict):
                                            for v in j["data"].values():
                                                if isinstance(v, str) and len(v) > 50:
                                                    # Parse HTML from the extracted value
                                                    import re as _re2
                                                    clean = _re2.sub(r'<[^>]+>', ' ', v)
                                                    clean = _re2.sub(r'\s+', ' ', clean).strip()
                                                    t = clean[:3000]
                                                    # Extract first image from HTML
                                                    if not img:
                                                        img_m = _re2.search(r'src=["\']?(https?://[^"\'>\s]+(?:alicdn|ae01|ae04)[^"\'>\s]*\.(?:jpg|png|jpeg|webp))', v, _re2.IGNORECASE)
                                                        if img_m:
                                                            img = img_m.group(1)
                                                    break
                                    except Exception:
                                        pass
                                # Reject JavaScript code
                                if t and (t.lstrip().startswith("/*") or t.lstrip().startswith("!function")):
                                    t = ""
                                log.info("      Desc fetched: %d chars text, img=%s, htmlLen=%d",
                                         len(t), bool(img), parsed.get("htmlLen", 0))
                                if t and len(t) >= 50:
                                    desc_text = t
                                if img and not desc_img:
                                    desc_img = img
                        except Exception:
                            pass

                    # If no network capture worked, try ALL frames (skip wp.html and JS frames)
                    if not desc_text:
                        for frame in detail_tab.frames:
                            if frame == detail_tab.main_frame:
                                continue
                            frame_url = (frame.url or "").lower()
                            # Skip known non-description frames
                            if any(skip in frame_url for skip in ["wp.html", "store-proxy", "captcha", "recaptcha", "about:blank", "chrome-error"]):
                                continue
                            try:
                                body_len = frame.evaluate("() => (document.body ? document.body.innerHTML.length : 0)")
                                if body_len > 100:
                                    frame_result = frame.evaluate("""
                                    () => {
                                        if (!document.body) return '';
                                        let text = document.body.innerText.trim();
                                        // Reject JavaScript code
                                        if (/^\s*(\/\*|!function|\(function|function\s*\()/.test(text))
                                            return '';
                                        for (const cut of ['additional regulatory', 'regulatory information']) {
                                            const idx = text.toLowerCase().indexOf(cut);
                                            if (idx > 0) { text = text.substring(0, idx).trim(); break; }
                                        }
                                        let firstImg = '';
                                        document.querySelectorAll('img').forEach(img => {
                                            if (firstImg) return;
                                            const src = img.src || img.getAttribute('data-src') || '';
                                            if (src && src.includes('alicdn') && !src.includes('icon')
                                                && !src.includes('logo') && !src.includes('thumbnail')) {
                                                firstImg = src;
                                            }
                                        });
                                        if (text.length < 50 && !firstImg) return '';
                                        return JSON.stringify({text: text.substring(0, 3000), img: firstImg});
                                    }
                                    """) or ""
                                    if frame_result:
                                        import json as _json5
                                        parsed = _json5.loads(frame_result)
                                        t = parsed.get("text", "")
                                        img = parsed.get("img", "")
                                        # Python-side: reject JS code that JS filter missed
                                        if t and (t.lstrip().startswith("/*") or t.lstrip().startswith("!function") or "function(e){" in t[:100]):
                                            t = ""
                                        if t and len(t) >= 50:
                                            desc_text = t
                                            log.info("      Desc: got %d chars from frame %s", len(t), (frame.url or "")[:60])
                                        if img and not desc_img:
                                            desc_img = img
                            except Exception:
                                continue

                    # If still no desc, try main document extraction with broad selectors
                    if not desc_text:
                        try:
                            main_result = detail_tab.evaluate("""
                            () => {
                                const sels = ['.product-description', '.detailmodule_html',
                                    '.detail-desc-decorate-richtext', '#product-description',
                                    '[class*="product-description"]', '[class*="detail-desc"]',
                                    '[data-pl="product-description"]',
                                    '[class*="description--wrap"]', '[class*="description--store"]',
                                    '[class*="ItemDescription"]', '[class*="item-description"]',
                                    '[class*="desc-content"]', '[class*="desc_rich"]',
                                    '[class*="richtext-detail"]', '[class*="detail-content"]',
                                    '[class*="sku-property"]',
                                    'div[data-spm="description"]', 'div[data-aplus-ae]'];
                                for (const sel of sels) {
                                    try {
                                    const els = document.querySelectorAll(sel);
                                    for (const el of els) {
                                        if (!el) continue;
                                        const clone = el.cloneNode(true);
                                        clone.querySelectorAll('img, script, style, video, iframe').forEach(e => e.remove());
                                        let text = clone.innerText.trim();
                                        const stripped = text.toLowerCase().replace(/[^a-z]/g, '');
                                        if (['description','descriptionreportviewmore','descriptionviewmore',
                                             'viewmore','descriptionreport'].includes(stripped)) continue;
                                        for (const cut of ['additional regulatory', 'regulatory information',
                                                           'shipping info', 'return policy']) {
                                            const idx = text.toLowerCase().indexOf(cut);
                                            if (idx > 0) { text = text.substring(0, idx).trim(); break; }
                                        }
                                        // Get 1st description image
                                        let firstImg = '';
                                        el.querySelectorAll('img').forEach(img => {
                                            if (firstImg) return;
                                            const src = img.src || img.getAttribute('data-src') || '';
                                            if (src && src.includes('alicdn') && !src.includes('icon')
                                                && !src.includes('logo') && !src.includes('thumbnail')) {
                                                firstImg = src;
                                            }
                                        });
                                        if (text.length >= 50 || firstImg) {
                                            return JSON.stringify({text: text.substring(0, 3000), img: firstImg});
                                        }
                                    }
                                    } catch(e) {}
                                }
                                // Last resort: find any large text block below the "Description" heading
                                try {
                                    const headings = document.querySelectorAll('h2, h3, h4, div, span');
                                    for (const h of headings) {
                                        const ht = (h.innerText || '').trim().toLowerCase();
                                        if (ht === 'description' || ht === 'product description') {
                                            let sibling = h.nextElementSibling;
                                            for (let i = 0; i < 5 && sibling; i++) {
                                                const clone = sibling.cloneNode(true);
                                                clone.querySelectorAll('script, style').forEach(e => e.remove());
                                                let text = clone.innerText.trim();
                                                let firstImg = '';
                                                sibling.querySelectorAll('img').forEach(img => {
                                                    if (firstImg) return;
                                                    const src = img.src || img.getAttribute('data-src') || '';
                                                    if (src && src.includes('alicdn') && !src.includes('icon')
                                                        && !src.includes('logo')) firstImg = src;
                                                });
                                                if (text.length >= 50 || firstImg)
                                                    return JSON.stringify({text: text.substring(0, 3000), img: firstImg});
                                                sibling = sibling.nextElementSibling;
                                            }
                                            // Also check parent's next sibling
                                            let parent = h.parentElement;
                                            if (parent) {
                                                sibling = parent.nextElementSibling;
                                                for (let i = 0; i < 3 && sibling; i++) {
                                                    const clone = sibling.cloneNode(true);
                                                    clone.querySelectorAll('script, style').forEach(e => e.remove());
                                                    let text = clone.innerText.trim();
                                                    let firstImg = '';
                                                    sibling.querySelectorAll('img').forEach(img => {
                                                        if (firstImg) return;
                                                        const src = img.src || img.getAttribute('data-src') || '';
                                                        if (src && src.includes('alicdn') && !src.includes('icon')
                                                            && !src.includes('logo')) firstImg = src;
                                                    });
                                                    if (text.length >= 50 || firstImg)
                                                        return JSON.stringify({text: text.substring(0, 3000), img: firstImg});
                                                    sibling = sibling.nextElementSibling;
                                                }
                                            }
                                        }
                                    }
                                } catch(e) {}
                                return '';
                            }
                            """) or ""
                            if main_result:
                                import json as _json6
                                parsed = _json6.loads(main_result)
                                if parsed.get("text") and len(parsed["text"]) >= 50:
                                    desc_text = parsed["text"]
                                if parsed.get("img") and not desc_img:
                                    desc_img = parsed["img"]
                        except Exception:
                            pass

                    # Add first description image if found
                    if desc_img and desc_img not in result["all_images"] and len(result["all_images"]) < MAX_IMAGES:
                        result["all_images"].append(desc_img)
                        log.info("      Desc: added 1st description image (total: %d)", len(result["all_images"]))

                    # Close any popups
                    try:
                        detail_tab.evaluate("""() => { document.dispatchEvent(new KeyboardEvent('keydown', {key: 'Escape', keyCode: 27})); }""")
                    except Exception:
                        pass
                except Exception as e:
                    log.info("      Description extraction error: %s", str(e)[:120])

            # Strategy 5: Deep search of page JS globals for REAL description content
            # Must contain HTML markup (real descriptions have <p>, <div>, <img> tags)
            # Must be long enough to not be a title/meta description
            if not desc_text:
                log.info("      Desc: trying Strategy 5 (deep JS global search)...")
                try:
                    s5_result = detail_tab.evaluate("""
                    () => {
                        // Helper: validate that content is a real description, not a title/meta
                        function extractDesc(html) {
                            if (!html || html.length < 100) return null;
                            // Must contain HTML tags — real descriptions have markup
                            if (!/<[a-z][^>]*>/i.test(html)) return null;
                            const tmp = document.createElement('div');
                            tmp.innerHTML = html;
                            let firstImg = '';
                            tmp.querySelectorAll('img').forEach(img => {
                                if (firstImg) return;
                                const src = img.src || img.getAttribute('src') || img.getAttribute('data-src') || '';
                                if (src && (src.includes('alicdn') || src.includes('ae01') || src.includes('ae04'))
                                    && !src.includes('icon') && !src.includes('logo')) firstImg = src;
                            });
                            tmp.querySelectorAll('img, script, style, video').forEach(e => e.remove());
                            let text = tmp.innerText.trim();
                            // Reject titles/meta descriptions (too short, starts with "Buy")
                            if (text.length < 150) return null;
                            if (/^Buy\\s/i.test(text)) return null;
                            if (/^Smarter Shopping/i.test(text)) return null;
                            return {text: text.substring(0, 3000), img: firstImg};
                        }
                        // Deep search through all script tags for description HTML
                        const scripts = document.querySelectorAll('script');
                        for (const s of scripts) {
                            const t = s.textContent || '';
                            if (t.length < 200 || t.length > 500000) continue;
                            // Look for description HTML embedded in JSON — only keys that indicate item description
                            const patterns = [
                                /"(?:descriptionContent|descriptionHtml|detailDesc|descContent)"\\s*:\\s*"((?:[^"\\\\]|\\\\.)*)"/i,
                                /"(?:itemDescription|product_description|descriptionModule)"\\s*:\\s*"((?:[^"\\\\]|\\\\.)*)"/i,
                            ];
                            for (const p of patterns) {
                                const m = t.match(p);
                                if (m && m[1] && m[1].length > 100) {
                                    let html = m[1];
                                    try { html = JSON.parse('"' + html + '"'); } catch(e) {}
                                    const r = extractDesc(html);
                                    if (r) return JSON.stringify(r);
                                }
                            }
                        }
                        // Also try window globals — but only look for actual description content keys
                        const globals = [window.runParams, window.__INIT_DATA__,
                            window.runConfig, window.detailData, window.pageData, window.__pageData__];
                        function deepSearch(obj, depth) {
                            if (!obj || depth > 6) return null;
                            if (typeof obj === 'string' && obj.length > 200 && /<[a-z][^>]*>/i.test(obj)) {
                                const r = extractDesc(obj);
                                if (r) return r;
                            }
                            if (typeof obj !== 'object') return null;
                            try {
                                for (const [k, v] of Object.entries(obj)) {
                                    const kl = k.toLowerCase();
                                    // Skip SEO/meta/og description keys — those are titles not descriptions
                                    if (kl.includes('og') || kl.includes('meta') || kl.includes('seo')
                                        || kl === 'title' || kl === 'name' || kl === 'subject') continue;
                                    if (kl.includes('desc') || kl.includes('description') || kl === 'detail'
                                        || kl === 'descriptionmodule') {
                                        const r = deepSearch(v, depth + 1);
                                        if (r) return r;
                                    }
                                }
                            } catch(e) {}
                            return null;
                        }
                        for (const g of globals) {
                            if (!g) continue;
                            const r = deepSearch(g, 0);
                            if (r) return JSON.stringify(r);
                        }
                        return '';
                    }
                    """) or ""
                    if s5_result:
                        import json as _json7
                        parsed = _json7.loads(s5_result)
                        _s5t = (parsed.get("text") or "").strip()
                        # Python-side reject: must be 300+ chars and NOT a product title
                        if _s5t and len(_s5t) >= 300 and not _s5t.startswith("Buy ") and not _s5t.startswith("Smarter Shopping"):
                            desc_text = _s5t
                            if not _store_desc_strategy:
                                _store_desc_strategy = "s5"
                                log.info("      Desc: CACHED Strategy 5 as working for this store (faster for remaining products)")
                            log.info("      Desc Strategy 5: got %d chars from JS globals", len(desc_text))
                            s5_img = parsed.get("img", "")
                            if s5_img and s5_img not in result["all_images"] and len(result["all_images"]) < MAX_IMAGES:
                                result["all_images"].append(s5_img)
                                log.info("      Desc: added 1st description image (total: %d)", len(result["all_images"]))
                        elif _s5t:
                            log.info("      Desc Strategy 5: rejected (%d chars, starts='%s')", len(_s5t), _s5t[:40])
                except Exception as e:
                    log.info("      Desc Strategy 5 error: %s", str(e)[:120])

            if specs_text:
                log.info("      Specs: %s", specs_text[:120])
            if desc_text:
                log.info("      Desc: %d chars — %s", len(desc_text), desc_text[:100])
                _store_desc_failures = 0  # reset on success
            else:
                _store_desc_failures += 1
                if _store_desc_failures >= 3 and not _store_desc_strategy:
                    _store_desc_strategy = "none"
                    log.info("      Desc: none found (3 consecutive failures — skipping desc for remaining products in this store)")
                else:
                    log.info("      Desc: none found")

            combined = ""
            if specs_text:
                combined += specs_text
            if desc_text:
                if combined:
                    combined += "\n"
                combined += desc_text
            if combined:
                result["detail_description"] = combined
        except Exception as e:
            log.debug("      Specs/description error: %s", str(e)[:80])

    except Exception as e:
        log.debug("  Detail scrape failed for %s: %s", product_id, str(e)[:80])

    # Log what we got
    log.info("      Got: %d images, %s price, %s shipping, %d char desc",
             len(result["all_images"]),
             result["detail_price"][:20] if result["detail_price"] else "none",
             result["detail_shipping"][:20] if result["detail_shipping"] else "none",
             len(result["detail_description"]))

    return result


def scrape_details_parallel(context, products, main_tab):
    """Fetch product details using multiple tabs in parallel batches.

    Opens PARALLEL_TABS extra tabs and processes products in batches,
    significantly faster than sequential single-tab fetching.
    """
    if not products:
        return

    tabs = []
    try:
        for _ in range(min(PARALLEL_TABS, len(products))):
            tabs.append(context.new_page())
    except Exception as e:
        log.warning("  Could not open parallel tabs: %s — falling back to sequential", e)
        # Close any tabs we did open
        for t in tabs:
            try:
                t.close()
            except Exception:
                pass
        return None  # Signal caller to use sequential fallback

    results = [None] * len(products)

    # Process in batches of PARALLEL_TABS
    for batch_start in range(0, len(products), len(tabs)):
        batch = products[batch_start:batch_start + len(tabs)]

        # Check for CAPTCHA on main tab AND all parallel tabs before each batch
        try:
            handle_captcha(main_tab)
            for t in tabs:
                handle_captcha(t)
        except Exception:
            pass

        # Navigate each tab and wait for content
        for i, product in enumerate(batch):
            pid = product["id"]
            product_url = product["product_url"]
            idx = batch_start + i
            log.info("    [%d/%d] Fetching details for %s...", idx + 1, len(products), pid)
            try:
                tabs[i].goto(product_url, wait_until="domcontentloaded", timeout=15000)
            except Exception as e:
                log.debug("  Detail nav failed for %s: %s", pid, str(e)[:80])

        # Wait for content to render
        try:
            tabs[0].wait_for_selector('img[src*="alicdn"], [class*="gallery"], [class*="slider"]', timeout=5000)
        except Exception:
            time.sleep(1.0)

        # Check if any tab landed on CAPTCHA — if so, handle it and retry
        captcha_tabs = []
        for i, product in enumerate(batch):
            try:
                if is_captcha(tabs[i]):
                    captcha_tabs.append(i)
            except Exception:
                pass

        if captcha_tabs:
            log.info("  CAPTCHA detected on %d tab(s), handling...", len(captcha_tabs))
            # Handle CAPTCHA on the first tab that has it (solving one usually clears all)
            handle_captcha(tabs[captcha_tabs[0]])
            # Also check/handle main tab
            handle_captcha(main_tab)
            # Retry the CAPTCHA'd tabs
            for i in captcha_tabs:
                product = batch[i]
                try:
                    tabs[i].goto(product["product_url"], wait_until="commit", timeout=10000)
                except Exception:
                    pass
            time.sleep(random.uniform(1.0, 1.8))

        # Extract data from all tabs
        for i, product in enumerate(batch):
            idx = batch_start + i
            pid = product["id"]
            result = {
                "all_images": [],
                "variations": [],
                "detail_title": "",
                "detail_price": "",
                "detail_shipping": "",
                "detail_description": "",
            }
            try:
                # Skip if still on CAPTCHA
                if is_captcha(tabs[i]):
                    log.debug("  Tab %d still on CAPTCHA, skipping %s", i, pid)
                    results[idx] = result
                    continue
                dismiss_popups(tabs[i])
                data = tabs[i].evaluate(DETAIL_EXTRACT_JS)
                if data.get("images"):
                    result["all_images"] = data["images"][:MAX_IMAGES]
                if data.get("variations"):
                    result["variations"] = data["variations"]
                if data.get("title"):
                    result["detail_title"] = data["title"]
                if data.get("price"):
                    result["detail_price"] = data["price"]
                if data.get("shipping"):
                    result["detail_shipping"] = data["shipping"]
                # If only 1 image, scroll and retry for more
                if len(result["all_images"]) <= 1:
                    tabs[i].evaluate("window.scrollTo(0, document.body.scrollHeight * 0.5)")
                    tabs[i].wait_for_timeout(800)
                    data2 = tabs[i].evaluate(DETAIL_EXTRACT_JS)
                    if data2.get("images") and len(data2["images"]) > len(result["all_images"]):
                        result["all_images"] = data2["images"][:MAX_IMAGES]
            except Exception as e:
                log.debug("  Detail scrape failed for %s: %s", pid, str(e)[:80])
            results[idx] = result

        # Check main tab after each batch — CAPTCHA may have appeared there too
        try:
            handle_captcha(main_tab)
        except Exception:
            pass

    # Close the extra tabs
    for t in tabs:
        try:
            t.close()
        except Exception:
            pass

    return results


# ---------------------------------------------------------------------------
# Pagination
# ---------------------------------------------------------------------------
CLICK_NEXT_JS = """
(targetPage) => {
    function clickEl(el) {
        el.scrollIntoView({block: 'center'});
        el.click();
        return true;
    }
    const paginationEls = document.querySelectorAll(
        '[class*="pagination"], [class*="Pagination"], nav[aria-label*="page"], [class*="comet-pagination"]'
    );
    for (const pg of paginationEls) {
        const nextBtns = pg.querySelectorAll(
            '[class*="next"]:not([class*="disabled"]):not([disabled]), ' +
            'button[aria-label="Next"], a[rel="next"], ' +
            '[aria-label*="Next"], button[aria-label="Next page"]'
        );
        for (const btn of nextBtns) {
            if (btn.offsetParent !== null) return clickEl(btn);
        }
        const allBtns = pg.querySelectorAll('a, button, span[role="button"], li');
        for (const btn of allBtns) {
            const txt = (btn.innerText || '').trim();
            if (txt === String(targetPage) && btn.offsetParent !== null) {
                return clickEl(btn);
            }
        }
    }
    const globalNextSels = [
        '.comet-pagination-next:not(.comet-pagination-disabled)',
        'button[class*="next"]:not([disabled])',
        'a[class*="next"]',
        '[aria-label*="Next"]',
        'a[rel="next"]',
    ];
    for (const sel of globalNextSels) {
        const els = document.querySelectorAll(sel);
        for (const el of els) {
            if (el.offsetParent !== null) return clickEl(el);
        }
    }
    const allEls = document.querySelectorAll('a, button, span[role="button"]');
    for (const el of allEls) {
        const txt = (el.innerText || '').trim();
        const rect = el.getBoundingClientRect();
        if (txt === String(targetPage) && el.offsetParent !== null && rect.top > 200) {
            if (rect.width < 200 && rect.height < 100) {
                return clickEl(el);
            }
        }
    }
    return false;
}
"""


def click_next(tab, current):
    nxt = current + 1
    try:
        tab.evaluate("window.scrollTo(0, document.body.scrollHeight)")
        tab.wait_for_timeout(500)
        result = tab.evaluate(CLICK_NEXT_JS, nxt)
        if result:
            tab.wait_for_timeout(500)
            return True
    except Exception:
        pass
    return False


def is_blocked(tab):
    """Check if AliExpress is showing 'unusual traffic' / IP block page."""
    try:
        body = tab.query_selector("body")
        if body:
            text = (body.inner_text() or "").strip().lower()
            if len(text) < 500 and ("unusual traffic" in text or "try again later" in text):
                return True
    except Exception:
        pass
    return False


# ---------------------------------------------------------------------------
# CAPTCHA / Login detection
# ---------------------------------------------------------------------------
def is_captcha(tab):
    try:
        url = tab.url.lower()
        if "captcha" in url or "punch" in url or "sec.aliexpress" in url:
            return True
        for sel in [
            "#captcha", "[class*='captcha']", "[class*='Captcha']",
            "#nc_1_n1z", ".nc-container", "#baxia-dialog",
            "#nc_1_wrapper", "#nc_1__scale_text", ".nc_wrapper",
            ".nc-outer", "#nocaptcha", "[class*='nocaptcha']",
            ".J_MIDDLEWARE_FRAME_WIDGET",
            "iframe[src*='captcha']", "iframe[src*='punch']",
            "iframe[src*='nocaptcha']", "iframe[src*='sec.aliexpress']",
            "[class*='slider-verify']", "[class*='SliderCaptcha']",
            "[class*='slide-verify']", "[class*='smartCaptcha']",
            # Google reCAPTCHA
            "iframe[src*='recaptcha']", "iframe[src*='google.com/recaptcha']",
            ".g-recaptcha", "#recaptcha", "[class*='recaptcha']",
        ]:
            try:
                el = tab.query_selector(sel)
                if el and el.is_visible():
                    return True
            except Exception:
                pass
        for frame in tab.frames:
            try:
                frame_url = frame.url.lower()
                if any(w in frame_url for w in ["captcha", "punch", "nocaptcha", "sec.aliexpress"]):
                    return True
            except Exception:
                pass
        body = tab.query_selector("body")
        if body:
            text = (body.inner_text() or "").strip()
            if len(text) < 500:
                low = text.lower()
                if any(w in low for w in ["captcha", "verify you are human", "robot",
                                          "slide to verify", "puzzle", "drag the slider",
                                          "not a robot", "check if you are",
                                          "unusual traffic", "try again later"]):
                    return True
    except Exception:
        pass
    return False


def try_solve_captcha(tab):
    """Attempt to auto-solve simple CAPTCHAs (checkbox click, slider drag).
    Returns True if it attempted a solve (caller should re-check is_captcha).
    """
    try:
        # --- 1. Google reCAPTCHA checkbox ("I'm not a robot") ---
        # Only click the checkbox — if an image challenge appears after,
        # we can't solve it, so return False to let the user handle it.
        for frame in tab.frames:
            try:
                if "recaptcha" not in frame.url.lower():
                    continue
                cb = frame.query_selector("#recaptcha-anchor")
                if cb and cb.is_visible():
                    # Check if checkbox is already checked
                    aria = cb.get_attribute("aria-checked")
                    if aria == "true":
                        continue
                    log.info("  Auto-clicking reCAPTCHA checkbox...")
                    box = cb.bounding_box()
                    if box:
                        tab.mouse.click(
                            box["x"] + box["width"] / 2 + random.uniform(-3, 3),
                            box["y"] + box["height"] / 2 + random.uniform(-3, 3),
                        )
                        tab.wait_for_timeout(3000)
                        # Check if an image challenge appeared — if so, we can't solve it
                        for f in tab.frames:
                            try:
                                if "recaptcha" in f.url.lower():
                                    challenge = f.query_selector(".rc-imageselect, .rc-doscaptcha, .rc-imageselect-table-33")
                                    if challenge and challenge.is_visible():
                                        log.info("  Image challenge appeared — need manual solve")
                                        return False
                            except Exception:
                                pass
                        return True
            except Exception:
                pass

        # --- 2. AliExpress slide-to-verify (drag slider to the right) ---
        for sel in ["#nc_1_n1z", ".nc_iconfont.btn_slide", "[class*='slider'] button",
                     "[class*='slide-btn']", ".btn_slide", "#nc_1__scale_text",
                     "[class*='SliderCaptcha'] .slider-btn"]:
            try:
                slider = tab.query_selector(sel)
                if slider and slider.is_visible():
                    log.info("  Auto-dragging slider CAPTCHA...")
                    box = slider.bounding_box()
                    if box:
                        # Find the track/container width
                        track_width = tab.evaluate("""
                        () => {
                            const t = document.querySelector('#nc_1_wrapper, [class*="slider-track"], [class*="nc-container"], [class*="SliderCaptcha"]');
                            return t ? t.getBoundingClientRect().width : 600;
                        }
                        """)
                        start_x = box["x"] + box["width"] / 2
                        start_y = box["y"] + box["height"] / 2
                        end_x = start_x + track_width - box["width"]

                        # Simulate human-like drag
                        tab.mouse.move(start_x, start_y)
                        tab.mouse.down()
                        steps = random.randint(15, 25)
                        for s in range(1, steps + 1):
                            progress = s / steps
                            # Ease-out curve
                            ease = 1 - (1 - progress) ** 2
                            cx = start_x + (end_x - start_x) * ease + random.uniform(-1, 1)
                            cy = start_y + random.uniform(-2, 2)
                            tab.mouse.move(cx, cy)
                            tab.wait_for_timeout(random.randint(10, 30))
                        tab.mouse.move(end_x, start_y)
                        tab.mouse.up()
                        tab.wait_for_timeout(2000)
                        return True
            except Exception:
                pass

        # --- 3. Simple "click to verify" / "press and hold" button ---
        for sel in ["button:has-text('Verify')", "button:has-text('verify')",
                     "button:has-text('Continue')", "[class*='captcha'] button",
                     "button:has-text('I\\'m not a robot')"]:
            try:
                btn = tab.query_selector(sel)
                if btn and btn.is_visible():
                    log.info("  Auto-clicking verify button...")
                    btn.click()
                    tab.wait_for_timeout(2000)
                    return True
            except Exception:
                pass

    except Exception:
        pass
    return False


def handle_captcha(tab):
    """Auto-solve CAPTCHA if possible, otherwise wait for user. Returns when clear."""
    if not is_captcha(tab):
        return

    # Scroll page to top so CAPTCHA is visible
    try:
        tab.evaluate("window.scrollTo(0, 0)")
    except Exception:
        pass

    # Wait for user to solve — no auto-solve attempts, no reloads
    log.warning(">>> CAPTCHA detected! Solve it in the browser window. <<<")
    print("\a", flush=True)
    while is_captcha(tab):
        tab.wait_for_timeout(3000)
    log.info(">>> CAPTCHA solved! <<<")


def is_login(tab):
    try:
        url = tab.url.lower()
        if "login" in url or "passport" in url or "signin" in url:
            return True
        for sel in [
            "input[type='password']",
            "[class*='login-dialog']", "[class*='LoginDialog']",
            "[class*='sign-in']", "[class*='SignIn']",
            "form[action*='login']", "form[action*='signin']",
        ]:
            try:
                el = tab.query_selector(sel)
                if el and el.is_visible():
                    return True
            except Exception:
                pass
    except Exception:
        pass
    return False


def wait_ready(tab, target):
    try:
        tab.wait_for_selector("a[href*='/item/']", timeout=5000)
    except Exception:
        pass
    for _ in range(5):
        if is_login(tab):
            log.warning(">>> Sign in required! Log in in the browser window. <<<")
            print("\a", flush=True)
            while is_login(tab):
                tab.wait_for_timeout(1000)
            log.info(">>> Login complete! Reloading target... <<<")
            try:
                tab.goto(target, wait_until="domcontentloaded", timeout=30000)
                tab.wait_for_selector("a[href*='/item/']", timeout=5000)
            except Exception:
                pass
            continue
        if is_captcha(tab):
            # Wait for user to solve — no auto-solve, no reloads
            log.warning(">>> CAPTCHA detected! Solve it in the browser window. <<<")
            print("\a", flush=True)
            while is_captcha(tab):
                tab.wait_for_timeout(3000)
            log.info(">>> CAPTCHA solved! Reloading target... <<<")
            try:
                tab.goto(target, wait_until="domcontentloaded", timeout=30000)
                tab.wait_for_selector("a[href*='/item/']", timeout=5000)
            except Exception:
                pass
            continue
        break
    return True


def dismiss_popups(tab):
    for sel in ["button:has-text('Accept')", "button:has-text('OK')",
                "button:has-text('Got it')", ".comet-modal-close"]:
        try:
            btn = tab.query_selector(sel)
            if btn and btn.is_visible():
                btn.click()
                tab.wait_for_timeout(100)
        except Exception:
            pass


def close_extra_tabs(context, keep_tab):
    """Close any tabs/popups that aren't the main tab.

    AliExpress product pages often open popup tabs via JavaScript.
    These accumulate and slow down the browser.
    """
    try:
        for page in context.pages:
            if page != keep_tab:
                try:
                    page.close()
                except Exception:
                    pass
    except Exception:
        pass


SCROLL_JS = """
async () => {
    const step = window.innerHeight * 2;
    const delay = ms => new Promise(r => setTimeout(r, ms));
    let h = document.body.scrollHeight;
    let y = 0;
    while (y < h) {
        y += step;
        window.scrollTo(0, y);
        await delay(150);
        h = document.body.scrollHeight;
    }
    window.scrollTo(0, document.body.scrollHeight);
    await delay(300);
}
"""


def scroll_and_extract(tab):
    """Scroll page to trigger infinite-scroll loading, then extract products.

    For store pages, AliExpress loads ~40 products at a time via infinite scroll.
    We keep scrolling until no new products appear for several rounds.
    """
    try:
        tab.evaluate(SCROLL_JS)
    except Exception:
        pass
    products = extract(tab)
    stale = 0
    max_stale = 6
    while stale < max_stale:
        try:
            # Scroll to bottom, wait, then scroll up slightly and back down
            # to trigger lazy-load observers that need scroll direction changes
            tab.evaluate("window.scrollTo(0, document.body.scrollHeight)")
            tab.wait_for_timeout(1200)
            tab.evaluate("window.scrollBy(0, -500)")
            tab.wait_for_timeout(500)
            tab.evaluate("window.scrollTo(0, document.body.scrollHeight)")
            tab.wait_for_timeout(1200)
        except Exception:
            break
        new = extract(tab)
        if len(new) > len(products):
            log.info("    Infinite scroll: %d -> %d products", len(products), len(new))
            products = new
            stale = 0
        else:
            stale += 1
    try:
        tab.evaluate("window.scrollTo(0, 0)")
    except Exception:
        pass
    return products


# ---------------------------------------------------------------------------
# Image rehosting — convert to JPEG, upload to Imgur
# ---------------------------------------------------------------------------
IMGUR_CLIENT_ID = "546c25a59c58ad7"  # Anonymous upload client ID

def _download_and_convert(img_url):
    """Download image from URL, convert to proper JPEG bytes. Returns bytes or None."""
    try:
        from PIL import Image
        has_pillow = True
    except ImportError:
        has_pillow = False

    resp = http_requests.get(img_url, headers={
        "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36",
        "Accept": "image/*",
        "Referer": "https://www.aliexpress.com/",
    }, timeout=15)

    if resp.status_code != 200:
        return None

    if has_pillow:
        try:
            img = Image.open(BytesIO(resp.content))
            w, h = img.size

            # Handle transparency first
            if img.mode in ('RGBA', 'P', 'LA'):
                bg = Image.new('RGB', img.size, (255, 255, 255))
                if img.mode == 'P':
                    img = img.convert('RGBA')
                bg.paste(img, mask=img.split()[-1] if 'A' in img.mode else None)
                img = bg
            elif img.mode != 'RGB':
                img = img.convert('RGB')

            # Ensure BOTH dimensions are at least 1000px for Amazon
            # Scale up so the shortest side reaches 1000px
            w, h = img.size
            if min(w, h) < 1000:
                scale = 1000 / min(w, h)
                new_w, new_h = int(w * scale), int(h * scale)
                # Cap at 2000px max to avoid oversized images
                if max(new_w, new_h) > 2000:
                    scale = 2000 / max(w, h)
                    new_w, new_h = int(w * scale), int(h * scale)
                img = img.resize((max(new_w, 1000), max(new_h, 1000)), Image.LANCZOS)
                w, h = img.size

            # If still not 1000 on both sides (extreme aspect ratio), pad to square
            if min(w, h) < 1000:
                side = max(w, h, 1000)
                bg = Image.new('RGB', (side, side), (255, 255, 255))
                bg.paste(img, ((side - w) // 2, (side - h) // 2))
                img = bg

            jpeg_buffer = BytesIO()
            img.save(jpeg_buffer, format='JPEG', quality=92, dpi=(96, 96))
            return jpeg_buffer.getvalue()
        except Exception:
            return resp.content
    return resp.content


def _save_image_locally(jpeg_bytes, img_url):
    """Save image to local images/ folder. Returns local filename."""
    img_dir = os.path.join(os.getcwd(), "images")
    os.makedirs(img_dir, exist_ok=True)
    # Generate filename from URL
    from hashlib import md5
    name = md5(img_url.encode()).hexdigest()[:12] + ".jpg"
    path = os.path.join(img_dir, name)
    with open(path, "wb") as f:
        f.write(jpeg_bytes)
    return path


def _is_thumbnail_url(url):
    """Check if URL is a tiny AliExpress thumbnail/swatch (e.g. /154x64.png, /60x60.png)."""
    # Match dimension patterns in the URL path like /154x64.png or /60x60.jpg
    m = re.search(r'/(\d+)x(\d+)\.\w+$', url)
    if m:
        w, h = int(m.group(1)), int(m.group(2))
        if max(w, h) < 500:
            return True
    # Also catch _NNxNN suffixes in filename
    m2 = re.search(r'_(\d+)x(\d+)', url)
    if m2:
        w, h = int(m2.group(1)), int(m2.group(2))
        if max(w, h) < 500:
            return True
    return False


def _upload_to_catbox(jpeg_bytes):
    """Upload JPEG bytes to catbox.moe. Returns direct URL or None."""
    try:
        resp = http_requests.post(
            "https://catbox.moe/user/api.php",
            data={"reqtype": "fileupload"},
            files={"fileToUpload": ("image.jpg", jpeg_bytes, "image/jpeg")},
            timeout=15,
        )
        if resp.status_code == 200 and resp.text.startswith("https://"):
            return resp.text.strip()
        log.info(f"          [IMG] catbox response: {resp.status_code}")
    except Exception as e:
        log.info(f"          [IMG] catbox error: {e}")
    return None


def _upload_to_litterbox(jpeg_bytes):
    """Upload JPEG bytes to litterbox.catbox.moe (temp hosting). Returns direct URL or None."""
    try:
        resp = http_requests.post(
            "https://litterbox.catbox.moe/resources/internals/api.php",
            data={"reqtype": "fileupload", "time": "72h"},
            files={"fileToUpload": ("image.jpg", jpeg_bytes, "image/jpeg")},
            timeout=15,
        )
        if resp.status_code == 200 and resp.text.startswith("https://"):
            return resp.text.strip()
        log.info(f"          [IMG] litterbox response: {resp.status_code}")
    except Exception as e:
        log.info(f"          [IMG] litterbox error: {e}")
    return None


def _verify_hosted_image(url):
    """HEAD-check a hosted image URL to confirm it has content."""
    try:
        resp = http_requests.head(url, timeout=10, allow_redirects=True)
        length = int(resp.headers.get("content-length", 0))
        if resp.status_code == 200 and length > 0:
            return True
        log.debug(f"          [IMG] Verify failed: status={resp.status_code} length={length}")
    except Exception as e:
        log.debug(f"          [IMG] Verify error: {e}")
    return False


def _upload_to_imgur(jpeg_bytes):
    """Upload JPEG bytes to Imgur (anonymous). Returns direct URL or None."""
    try:
        import base64
        b64 = base64.b64encode(jpeg_bytes).decode("utf-8")
        resp = http_requests.post(
            "https://api.imgur.com/3/image",
            headers={"Authorization": f"Client-ID {IMGUR_CLIENT_ID}"},
            data={"image": b64, "type": "base64"},
            timeout=30,
        )
        if resp.status_code == 200:
            data = resp.json()
            link = data.get("data", {}).get("link", "")
            if link:
                # Ensure HTTPS
                link = link.replace("http://", "https://")
                return link
        log.info(f"          [IMG] Imgur response: {resp.status_code} {resp.text[:200]}")
    except Exception as e:
        log.info(f"          [IMG] Imgur error: {e}")
    return None


def _upload_to_freeimage(jpeg_bytes):
    """Upload JPEG bytes to freeimage.host (iili.io CDN). Returns direct URL or None."""
    FREEIMAGE_API_KEY = "6d207e02198a847aa98d0a2a901485a5"
    try:
        import base64
        b64 = base64.b64encode(jpeg_bytes).decode("utf-8")
        resp = http_requests.post(
            "https://freeimage.host/api/1/upload",
            data={"key": FREEIMAGE_API_KEY, "source": b64, "format": "json"},
            timeout=30,
        )
        if resp.status_code == 200:
            data = resp.json()
            url = data.get("image", {}).get("url", "")
            if url:
                return url
        log.info(f"          [IMG] freeimage response: {resp.status_code}")
    except Exception as e:
        log.info(f"          [IMG] freeimage error: {e}")
    return None


def rehost_image(img_url):
    """Download image, convert to JPEG, upload to hosting. Returns URL for Amazon."""
    if not img_url:
        return None

    # Clean the URL
    if img_url.startswith("//"):
        img_url = "https:" + img_url

    # Skip tiny thumbnails/swatches — Amazon requires min 1000px
    if _is_thumbnail_url(img_url):
        log.info(f"          [IMG] Skipping thumbnail: {img_url}")
        return "SKIPPED"

    # Strip AliExpress resize suffixes to get full-size image
    img_url = re.sub(r'_\d+x\d+[^.]*\.', '.', img_url)
    img_url = re.sub(r'\.(jpg|png|jpeg)_\d+x\d+[^.]*', r'.\1', img_url, flags=re.IGNORECASE)

    # Download and convert to proper JPEG
    jpeg_bytes = None
    try:
        jpeg_bytes = _download_and_convert(img_url)
    except Exception:
        pass

    if not jpeg_bytes:
        return None

    _save_image_locally(jpeg_bytes, img_url)
    log.info(f"          [IMG] Downloaded {len(jpeg_bytes)} bytes, uploading...")

    # Try imgbb first (reliable, Amazon-accessible, full-size URLs)
    # Skip if rate-limited (3+ consecutive failures)
    if getattr(rehost_image, '_imgbb_fails', 0) < 3:
        try:
            import base64
            b64 = base64.b64encode(jpeg_bytes).decode("utf-8")
            resp = http_requests.post(
                "https://api.imgbb.com/1/upload",
                data={"key": IMGBB_API_KEY, "image": b64},
                timeout=30,
            )
            if resp.status_code == 200:
                data = resp.json()
                img_data = data.get("data", {})
                # IMPORTANT: use image.url (full-size original), NOT display_url
                # display_url is a 640px thumbnail which fails Amazon's 1000px minimum
                url = (img_data.get("image", {}).get("url", "")
                       or img_data.get("display_url", "")
                       or img_data.get("url", ""))
                if url:
                    # Verify the uploaded image is accessible before returning
                    if _verify_hosted_image(url):
                        log.info(f"          [IMG] imgbb: {url}")
                        rehost_image._imgbb_fails = 0
                        return url
                    else:
                        log.warning(f"          [IMG] imgbb uploaded but not accessible: {url}")
            log.warning(f"          [IMG] imgbb response: {resp.status_code} {resp.text[:200]}")
            rehost_image._imgbb_fails = getattr(rehost_image, '_imgbb_fails', 0) + 1
            if rehost_image._imgbb_fails >= 3:
                log.warning("          [IMG] imgbb rate-limited — skipping for remaining images")
        except Exception as e:
            log.info(f"          [IMG] imgbb error: {e}")
            rehost_image._imgbb_fails = getattr(rehost_image, '_imgbb_fails', 0) + 1

    # Try freeimage.host as fallback
    if getattr(rehost_image, '_freeimage_fails', 0) < 5:
        hosted_url = _upload_to_freeimage(jpeg_bytes)
        if hosted_url and _verify_hosted_image(hosted_url):
            log.info(f"          [IMG] freeimage (iili.io): {hosted_url}")
            rehost_image._freeimage_fails = 0
            return hosted_url
        rehost_image._freeimage_fails = getattr(rehost_image, '_freeimage_fails', 0) + 1
        if rehost_image._freeimage_fails >= 5:
            log.warning("          [IMG] freeimage rate-limited — skipping for remaining images")

    # Try Imgur as fallback
    if getattr(rehost_image, '_imgur_fails', 0) < 5:
        hosted_url = _upload_to_imgur(jpeg_bytes)
        if hosted_url and _verify_hosted_image(hosted_url):
            log.info(f"          [IMG] Imgur: {hosted_url}")
            rehost_image._imgur_fails = 0
            return hosted_url
        rehost_image._imgur_fails = getattr(rehost_image, '_imgur_fails', 0) + 1
        if rehost_image._imgur_fails >= 5:
            log.warning("          [IMG] Imgur rate-limited — skipping for remaining images")

    # Try catbox as last resort
    hosted_url = _upload_to_catbox(jpeg_bytes)
    if hosted_url and _verify_hosted_image(hosted_url):
        log.info(f"          [IMG] catbox: {hosted_url}")
        return hosted_url

    # Try litterbox as absolute last resort
    hosted_url = _upload_to_litterbox(jpeg_bytes)
    if hosted_url and _verify_hosted_image(hosted_url):
        log.info(f"          [IMG] litterbox: {hosted_url}")
        return hosted_url

    log.warning(f"          [IMG] All hosting failed for: {img_url[:80]}")
    return None


# ---------------------------------------------------------------------------
# Post-processing helpers
# ---------------------------------------------------------------------------
def is_resin_model(title):
    """Strict filter: only accept genuine resin models, figures, busts, dioramas."""
    t = title.lower()
    # Exclusions always win
    for ex in RESIN_EXCLUDE:
        if ex in t:
            return False
    # Strong include — these terms are specific enough on their own
    for inc in RESIN_INCLUDE:
        if inc in t:
            return True
    # Soft include — only if "resin" is also in the title
    if "resin" in t:
        for inc in RESIN_SOFT_INCLUDE:
            if inc in t:
                return True
    return False


def parse_price(price_str):
    if not price_str or price_str == "N/A":
        return None
    cleaned = re.sub(r'[^\d.,]', '', price_str)
    if ',' in cleaned and '.' not in cleaned:
        cleaned = cleaned.replace(',', '.')
    elif ',' in cleaned and '.' in cleaned:
        cleaned = cleaned.replace(',', '')
    try:
        return float(cleaned)
    except ValueError:
        return None


def ali_to_gbp(price_usd, shipping_str=None):
    """Calculate Amazon UK sell price from AliExpress cost.

    Shipping is scraped from AliExpress detail pages and is already in GBP
    (AliExpress shows shipping in the user's local currency).
    If no shipping was scraped, assumes free shipping (£0).

    Profit = sell_price - Amazon total fees - product cost - shipping
    Where Amazon total fees = (sell_price * REFERRAL_FEE) + PER_ITEM_FEE

    Target: profit >= 30% of sell price OR profit >= £7.50
            — whichever gives the higher sell price.
    """
    if not price_usd:
        return DEFAULT_PRICE_GBP
    cost_gbp = price_usd * USD_TO_GBP
    # Shipping is already in GBP from AliExpress (e.g. "3.52", "Free")
    shipping_gbp = 0.0
    if shipping_str:
        s = shipping_str.lower().strip()
        if s != "free":
            parsed = parse_price(shipping_str)
            if parsed is not None:
                shipping_gbp = parsed
    sourcing_cost = cost_gbp + shipping_gbp

    # --- Price for 30% margin ---
    # profit = sell - sell*referral - per_item - sourcing_cost
    # We want: profit >= 0.30 * sell
    # sell - sell*referral - per_item - sourcing_cost >= 0.30 * sell
    # sell * (1 - referral - 0.30) >= per_item + sourcing_cost
    # sell >= (per_item + sourcing_cost) / (1 - referral - 0.30)
    denom_margin = 1 - AMAZON_REFERRAL_FEE - TARGET_PROFIT_MARGIN
    if denom_margin <= 0:
        return DEFAULT_PRICE_GBP
    price_for_margin = (AMAZON_PER_ITEM_FEE + sourcing_cost) / denom_margin

    # --- Price for £7.50 minimum profit ---
    # profit = sell * (1 - referral) - per_item - sourcing_cost >= 7.50
    # sell >= (7.50 + per_item + sourcing_cost) / (1 - referral)
    price_for_min_profit = (MIN_PROFIT_GBP + AMAZON_PER_ITEM_FEE + sourcing_cost) / (1 - AMAZON_REFERRAL_FEE)

    # Use whichever gives the higher sell price
    sell_price = max(price_for_margin, price_for_min_profit)
    sell_price = round(sell_price, 2)
    if sell_price < MIN_SELL_PRICE:
        sell_price = MIN_SELL_PRICE
    return sell_price


def _has_trademark_risk(title):
    """Check if title contains trademarked brand/team/player names that Amazon will reject."""
    # Common trademarks that trigger error 18653 "Trademark Logo Misuse"
    TRADEMARK_TERMS = [
        # Football/Soccer players & teams
        r'messi', r'ronaldo', r'cr7', r'mbapp[eé]', r'mbp', r'neymar', r'haaland',
        r'vini\s*jr', r'vinicius', r'bellingham',
        r'emirates', r'barcelona', r'real\s*madrid', r'man\s*utd', r'manchester',
        r'liverpool', r'chelsea', r'arsenal', r'psg', r'juventus', r'bayern',
        # Sports leagues
        r'fifa', r'nba', r'nfl', r'premier\s*league', r'la\s*liga', r'champions\s*league',
        # Major brands
        r'nike', r'adidas', r'puma', r'supreme', r'gucci', r'louis\s*vuitton',
        r'chanel', r'hermes', r'rolex', r'apple', r'samsung', r'sony',
        r'nintendo', r'playstation', r'xbox', r'marvel', r'dc\s*comics',
        r'disney', r'pokemon', r'pikachu', r'star\s*wars', r'harry\s*potter',
        r'lego', r'transformers', r'barbie', r'hot\s*wheels',
        # Nintendo IP
        r'zelda', r'link.*hyrule', r'hyrule', r'triforce', r'ganondorf', r'ganon',
        # Anime (commonly enforced)
        r'dragon\s*ball', r'naruto', r'one\s*piece', r'demon\s*slayer',
        r'attack\s*on\s*titan', r'jujutsu\s*kaisen', r'my\s*hero\s*academia',
    ]
    title_lower = title.lower()
    for term in TRADEMARK_TERMS:
        # Use simple substring search for short terms (cr7, mbp, psg etc)
        # and word boundary for longer terms to avoid false positives
        if len(term.replace('\\s*', '').replace('[eé]', 'e')) <= 4:
            if re.search(term, title_lower):
                return True
        else:
            if re.search(r'\b' + term + r'\b', title_lower):
                return True
    return False


def clean_title(title):
    """Clean title of all Amazon-prohibited phrases."""
    if not title:
        return "Model Kit"
    title = re.sub(r'[^\w\s\-\.,&\'\"/()\[\]]', ' ', title)
    # Remove ALL prohibited Amazon phrases (case insensitive)
    prohibited = [
        r'free\s*shipping', r'best\s*seller', r'hot\s*sale',
        r'hot\s*new', r'new\s*arrival', r'wholesale', r'dropship\w*',
        r'cheap', r'lowest\s*price', r'factory\s*direct',
        r'top\s*selling', r'limited\s*time', r'special\s*offer',
        r'big\s*sale', r'clearance', r'on\s*sale', r'promotion',
        r'buy\s*\d+\s*get', r'aliexpress', r'ali\s*express',
        r'china\s*direct', r'from\s*china',
        r'boy\s*gift', r'girl\s*gift', r'gift\s*for\s*\w+',
    ]
    for phrase in prohibited:
        title = re.sub(r'(?i)\b' + phrase + r'\b', '', title)
    title = re.sub(r'\s+', ' ', title).strip()
    if len(title) > 200:
        title = title[:197] + "..."
    if not title or len(title) < 3:
        title = "Model Kit"
    return title


def _detect_scale(title):
    """Extract scale from title like 1/35, 1/64, etc."""
    m = re.search(r'1/(\d+)', title)
    return m.group(0) if m else None


def _detect_theme(title):
    """Detect the product theme from title."""
    t = title.lower()
    if any(w in t for w in ["wwii", "ww2", "world war", "military", "soldier", "infantry",
                             "tank crew", "rifleman", "gunner", "paratrooper", "marines"]):
        return "Military"
    if any(w in t for w in ["fantasy", "dragon", "elf", "orc", "minotaur", "demon",
                             "knight", "warrior", "wizard", "monster", "imp"]):
        return "Fantasy"
    if any(w in t for w in ["sci-fi", "science fiction", "mecha", "robot", "mars",
                             "space", "cyberpunk", "futuristic"]):
        return "Science Fiction"
    if any(w in t for w in ["anime", "manga", "solo leveling", "collectible model"]):
        return "Anime"
    if any(w in t for w in ["christmas", "decoration", "ornament", "garden", "landscape"]):
        return "Decorative"
    if any(w in t for w in ["football", "soccer", "sport"]):
        return "Sports"
    if any(w in t for w in ["historical", "centurion", "roman", "napoleonic", "civil war",
                             "medieval", "templar", "crusade", "regiment"]):
        return "Historical"
    if any(w in t for w in ["diorama", "miniature", "scene", "street", "garage", "city"]):
        return "Diorama"
    if any(w in t for w in ["pilot", "air force", "spitfire", "fighter"]):
        return "Aviation"
    return "Collectible Figures"


def _detect_figure_type(title):
    """Detect toy figure type from title."""
    t = title.lower()
    if any(w in t for w in ["bust", "1/10", "1/9", "1/12 bust"]):
        return "Busts"
    if any(w in t for w in ["diorama", "scene", "landscape", "miniature figure"]):
        return "Miniatures"
    if any(w in t for w in ["soldier", "infantry", "military", "tank crew", "rifleman",
                             "gunner", "pilot", "marines"]):
        return "Soldier Figures"
    if any(w in t for w in ["statue", "collectible", "anime"]):
        return "Statues"
    if any(w in t for w in ["animal", "dog", "cat", "horse", "fox", "christmas"]):
        return "Animal Figures"
    return "Action Figures"


def _detect_animal(title):
    """Detect animal type if present in title."""
    t = title.lower()
    animals = {
        "dragon": "Dragon", "horse": "Horse", "dog": "Dog", "cat": "Cat",
        "fox": "Fox", "wolf": "Wolf", "eagle": "Eagle", "lion": "Lion",
        "bear": "Bear", "dinosaur": "Dinosaur", "scorpion": "Scorpion",
        "mouse": "Mouse", "bull": "Bull", "minotaur": "Bull",
    }
    for keyword, animal in animals.items():
        if keyword in t:
            return animal
    return None


def _detect_material(title):
    """Detect material from title."""
    t = title.lower()
    if "resin" in t:
        return "Resin"
    if "metal" in t or "die-cast" in t or "diecast" in t:
        return "Metal"
    if "plastic" in t or "pvc" in t:
        return "Plastic"
    return "Resin"


def _detect_num_pieces(title):
    """Try to detect number of pieces/figures from title."""
    t = title.lower()
    # "5 soldiers", "3 people", "10 people", "4 figure", "15 figure"
    m = re.search(r'(\d+)\s*(?:people|soldiers|figures?|pieces?|men|person)', t)
    if m:
        return int(m.group(1))
    # "set of 3", "pack of 5"
    m = re.search(r'(?:set|pack|kit)\s*(?:of\s*)?(\d+)', t)
    if m:
        return int(m.group(1))
    return 1


def make_bullets(title):
    """Generate product-specific bullet points based on title analysis."""
    bullets = []
    text = title.lower()
    scale = _detect_scale(title)
    theme = _detect_theme(title)
    material = _detect_material(title)
    num = _detect_num_pieces(title)

    # Material-specific
    if material == "Resin":
        bullets.append(f"Premium quality resin model kit with fine detail casting for painting and display")
    elif material == "Metal":
        bullets.append(f"Die-cast metal construction for durability and realistic weight")

    # Scale-specific
    if scale:
        bullets.append(f"Accurately proportioned {scale} scale model compatible with other {scale} scale collections")

    # Theme-specific
    if "Military" in theme or "Aviation" in theme:
        bullets.append("Historically inspired design based on real military reference material")
    elif "Fantasy" in theme:
        bullets.append("Richly detailed fantasy design perfect for tabletop gaming or display shelves")
    elif "Diorama" in theme:
        bullets.append("Ideal for creating realistic diorama scenes and miniature displays")

    # Kit features
    if "unpainted" in text or "unassembled" in text:
        bullets.append("Unassembled and unpainted kit allowing full creative customisation")
    if "bust" in text:
        bullets.append("Detailed bust format showcasing intricate facial and upper body features")

    # Quantity
    if num > 1:
        bullets.append(f"Includes {num} individual figures in one complete set")

    # Fill remaining with quality-focused generics
    generic = [
        f"Made from high-quality {material.lower()} material for lasting display quality",
        "Perfect collectible gift for model enthusiasts, hobbyists and painters",
        "Securely packaged to ensure safe delivery of all parts and components",
        "Suitable for experienced modellers and collectors aged 14 and above",
        "Excellent addition to any scale model or miniature figure collection",
    ]
    for g in generic:
        if len(bullets) >= 5:
            break
        if g not in bullets:
            bullets.append(g)
    return bullets[:5]


def _extract_specs_from_ali_desc(ali_desc):
    """Extract useful specifications from AliExpress description text.

    Returns two lists: (specs_dict, feature_sentences)
      - specs_dict: key-value pairs like {"Material": "Resin", "Height": "15cm"}
      - feature_sentences: clean descriptive sentences about the product
    """
    if not ali_desc:
        return {}, []
    specs = {}
    features = []
    lines = ali_desc.replace('|', '\n').split('\n')

    # Spam filter
    spam_words = ['aliexpress', 'ali express', 'wholesale', 'dropship',
                  'free shipping', 'buy now', 'click here', 'add to cart',
                  'hot sale', 'best seller', 'factory direct', 'cheap',
                  'wish list', 'feedback', 'store', 'shop now', 'lowest price',
                  'order now', 'limited time', 'flash sale', 'coupon',
                  'customer service', 'dear friend', 'dear buyer', 'note:',
                  'please note', 'warm tips', 'kindly note', 'reminder']

    # Spec extraction patterns — map to clean labels
    spec_labels = [
        (r'(?:material|made\s+(?:of|from))\s*[:\-]?\s*(.+)', 'Material'),
        (r'(?:size|dimensions?)\s*[:\-]?\s*(.+)', 'Size'),
        (r'(?:height)\s*[:\-]?\s*(.+)', 'Height'),
        (r'(?:width)\s*[:\-]?\s*(.+)', 'Width'),
        (r'(?:length)\s*[:\-]?\s*(.+)', 'Length'),
        (r'(?:weight)\s*[:\-]?\s*(.+)', 'Weight'),
        (r'(?:scale)\s*[:\-]?\s*(.+)', 'Scale'),
        (r'(?:colou?r)\s*[:\-]?\s*(.+)', 'Colour'),
        (r'(?:package\s+includes?|includes?|contents?|what.s in the box)\s*[:\-]?\s*(.+)', 'Includes'),
        (r'(?:suitable\s+for|recommended\s+(?:for|age))\s*[:\-]?\s*(.+)', 'Suitable For'),
        (r'(?:type|style)\s*[:\-]?\s*(.+)', 'Type'),
        (r'(?:number\s+of\s+pieces|pieces|parts)\s*[:\-]?\s*(.+)', 'Pieces'),
    ]

    seen_keys = set()
    seen_features = set()

    for line in lines:
        line = line.strip()
        if not line or len(line) < 5 or len(line) > 300:
            continue
        low = line.lower()

        # Skip spam
        if any(w in low for w in spam_words):
            continue
        # Skip brand and country of origin
        if low.startswith('brand') or 'country of origin' in low or low.startswith('origin'):
            continue
        if 'china' in low and ('origin' in low or 'made in' in low):
            continue
        # Skip lines that are mostly punctuation, caps-lock shouting, or prices
        if re.search(r'[!]{2,}|[$€£¥]\s*\d|http|www\.|\.com|\.cn|@', line):
            continue

        # Try to extract as a spec key-value pair
        matched_spec = False
        for pat, label in spec_labels:
            m = re.search(pat, line, re.IGNORECASE)
            if m and label not in seen_keys:
                val = m.group(1).strip().rstrip(':').rstrip('-').rstrip('.')
                # Clean up the value
                val = re.sub(r'\s+', ' ', val)
                if val and len(val) > 1 and len(val) < 150:
                    specs[label] = val
                    seen_keys.add(label)
                matched_spec = True
                break

        # Also catch "Key: Value" format directly (colon only, not hyphen)
        if not matched_spec:
            kv = re.match(r'^([A-Za-z][A-Za-z\s]{2,20})\s*:\s*(.{2,100})$', line)
            if kv:
                key = kv.group(1).strip().title()
                val = kv.group(2).strip().rstrip('.')
                if key not in seen_keys and not any(w in key.lower() for w in spam_words):
                    specs[key] = val
                    seen_keys.add(key)
                    matched_spec = True

        # Keep as a feature sentence if informative
        if not matched_spec and 15 < len(line) < 200:
            # Must look like a real sentence or description, not a header/label
            feat_key = line.lower()[:40]
            if feat_key not in seen_features:
                seen_features.add(feat_key)
                features.append(line)

    return specs, features[:8]


def make_description(title, ali_description=None):
    """Generate a clean, professional Amazon product description.

    Builds a well-formatted description from:
    1. The product title (cleaned)
    2. AliExpress specs (key-value pairs from listing)
    3. AliExpress description text (feature sentences)
    4. Title-derived info (scale, material, piece count)
    """
    clean = clean_title(title)
    text = title.lower()
    scale = _detect_scale(title)
    theme = _detect_theme(title)
    material = _detect_material(title)
    num = _detect_num_pieces(title)

    # Extract real specs and features from AliExpress description
    ali_specs, ali_features = _extract_specs_from_ali_desc(ali_description)
    has_ali_data = bool(ali_specs or ali_features)

    sections = []

    # --- Section 1: Opening paragraph — product summary ---
    opener_parts = [clean]
    # Build a natural opening sentence with key attributes
    attrs = []
    mat = ali_specs.get("Material", material)
    if mat:
        attrs.append(f"crafted from {mat.lower()}")
    if scale:
        attrs.append(f"in {scale} scale")
    if num > 1:
        attrs.append(f"featuring {num} pieces")
    if attrs:
        opener_parts.append(" — " + ", ".join(attrs) + ".")
    else:
        opener_parts.append(".")

    # Add a theme-appropriate second sentence
    theme_lines = {
        "Military": "A detailed figure capturing authentic military character and equipment.",
        "Aviation": "A finely sculpted figure capturing the spirit of aviation history.",
        "Fantasy": "A striking fantasy figure with intricate sculpted detail throughout.",
        "Science Fiction": "A dynamic sci-fi figure with futuristic detail and design.",
        "Historical": "A carefully researched figure reflecting historical accuracy and period detail.",
        "Anime": "A detailed collectible figure with dynamic posing and sharp sculpted features.",
        "Diorama": "An ideal piece for building immersive miniature scenes and displays.",
        "Decorative": "A beautifully detailed piece suitable for display and home decoration.",
    }
    theme_line = theme_lines.get(theme, "A high-quality collectible figure with excellent sculpted detail.")
    opener_parts.append(" " + theme_line)
    sections.append("".join(opener_parts))

    # --- Section 2: Product features from the actual listing ---
    if ali_features:
        clean_features = []
        for feat in ali_features[:5]:
            feat = feat.strip()
            if not feat:
                continue
            feat = feat[0].upper() + feat[1:]
            if not feat.endswith('.'):
                feat += '.'
            clean_features.append(feat)
        if clean_features:
            sections.append("\n".join(clean_features))

    # --- Section 3: Specifications table ---
    spec_items = []
    # Add AliExpress specs first (from the real listing)
    for label, val in ali_specs.items():
        if label == "Material":
            continue  # already used in opener
        spec_items.append(f"  {label}: {val}")
    # Fill in from title if listing didn't provide them
    if scale and "Scale" not in ali_specs:
        spec_items.append(f"  Scale: {scale}")
    if material and "Material" not in ali_specs:
        spec_items.append(f"  Material: {material}")
    if num > 1 and "Pieces" not in ali_specs:
        spec_items.append(f"  Pieces: {num}")
    if spec_items:
        sections.append("Specifications:\n" + "\n".join(spec_items[:10]))

    # --- Section 4: Kit / assembly info ---
    kit_info = []
    if "unpainted" in text and "unassembled" in text:
        kit_info.append("Supplied unassembled and unpainted — a rewarding project for experienced modellers.")
    elif "unpainted" in text:
        kit_info.append("Supplied unpainted, allowing full creative freedom with your choice of colours.")
    elif "unassembled" in text:
        kit_info.append("Supplied unassembled — some modelling experience recommended.")
    if num > 1 and not any("pieces" in k.lower() for k in ali_specs):
        kit_info.append(f"This set includes {num} individual pieces.")
    if kit_info:
        sections.append(" ".join(kit_info))

    # --- Section 5: Closing ---
    if not has_ali_data:
        sections.append("Please refer to the product images for full detail on what is included.")

    return "\n\n".join(sections)


# ---------------------------------------------------------------------------
# Amazon template filling
# ---------------------------------------------------------------------------
def find_amazon_template():
    xlsm_files = [f for f in os.listdir(".") if f.endswith(".xlsm") and "upload" not in f.lower() and "processing" not in f.lower()]
    if not xlsm_files:
        return None
    # Prefer TOY_FIGURE template
    for f in xlsm_files:
        if "toy_figure" in f.lower() or "toyfigure" in f.lower():
            return f
    return xlsm_files[0]


def detect_columns(ws):
    cols = {}
    max_used = 0
    for c in range(1, 460):
        val = ws.cell(row=3, column=c).value
        if val:
            cols[str(val).strip().lower()] = c
            max_used = c
        val2 = ws.cell(row=2, column=c).value
        if val2:
            key2 = str(val2).strip().lower()
            if key2 not in cols:
                cols[key2] = c
            max_used = max(max_used, c)

    # Note: Do NOT dynamically add columns — Amazon rejects unknown field headings (error 90061).
    # Only use columns that already exist in the template.

    return cols


def _fill_toy_figure_fields(ws, row, col):
    """Fill required TOY_FIGURE dimension fields with defaults."""
    fields = {
        "unit_count": 1,
        "unit_count_type": "Count",
        "length_height_floor_to_top": 10,
        "length_height_floor_to_top_unit_of_measure": "Centimetres",
        "length_width_side_to_side": 5,
        "length_width_side_to_side_unit_of_measure": "Centimetres",
        "length_head_to_toe": 10,
        "length_head_to_toe_unit_of_measure": "Centimetres",
    }
    for field, value in fields.items():
        c = col(field)
        if c:
            ws.cell(row=row, column=c, value=value)


def _fill_quality_attributes(ws, row, col, title):
    """Fill quality listing attributes: theme, material, figure type, age range, etc."""
    theme = _detect_theme(title)
    figure_type = _detect_figure_type(title)
    material = _detect_material(title)
    animal = _detect_animal(title)
    num_pieces = _detect_num_pieces(title)
    scale = _detect_scale(title)

    # Theme (subject)
    c = col("theme")
    if c:
        ws.cell(row=row, column=c, value=theme)

    # Material
    c = col("material_type")
    if c:
        ws.cell(row=row, column=c, value=material)

    # Age range
    c = col("age_range_description")
    if c:
        ws.cell(row=row, column=c, value="14 years and up")

    # Target gender
    c = col("target_gender")
    if c:
        ws.cell(row=row, column=c, value="Unisex")

    # Skill level
    c = col("skill_level")
    if c:
        if "unpainted" in title.lower() or "unassembled" in title.lower():
            ws.cell(row=row, column=c, value="Advanced")
        else:
            ws.cell(row=row, column=c, value="Intermediate")

    # Number of pieces
    c = col("number_of_pieces")
    if c:
        ws.cell(row=row, column=c, value=num_pieces)

    # Scale (if detected)
    if scale:
        c = col("scale_name")
        if c:
            ws.cell(row=row, column=c, value=scale)

    # Item type name
    c = col("item_type_name")
    if c:
        ws.cell(row=row, column=c, value=figure_type)

    # Style
    c = col("style_name")
    if c:
        if "bust" in title.lower():
            ws.cell(row=row, column=c, value="Bust")
        elif "diorama" in title.lower():
            ws.cell(row=row, column=c, value="Diorama")
        else:
            ws.cell(row=row, column=c, value="Figure")

    # Special features
    special = []
    t = title.lower()
    if "unpainted" in t:
        special.append("Unpainted")
    if "unassembled" in t:
        special.append("Unassembled")
    if "resin" in t:
        special.append("Resin Cast")
    if scale:
        special.append(f"{scale} Scale")
    if "hand" in t or "handmade" in t:
        special.append("Handcrafted")
    for i, feat in enumerate(special[:5]):
        c = col(f"special_features{i+1}")
        if c:
            ws.cell(row=row, column=c, value=feat)

    # Subject (animal theme if applicable)
    if animal:
        c = col("unknown_subject")  # 'subject' field in template
        if c:
            ws.cell(row=row, column=c, value=animal)


def _fill_offer_fields(ws, row, col, col_map, sell_price):
    """Set ALL price, fulfillment, and offer fields needed for Buy Box / Featured Offer."""
    # UK Price (the actual Buy Box price) — Amazon UK marketplace ID
    uk_price_field = "purchasable_offer[marketplace_id=a1f83g8c2aro7p]#1.our_price#1.schedule#1.value_with_tax"
    c = col(uk_price_field)
    if c:
        ws.cell(row=row, column=c, value=sell_price)
    else:
        # Fallback: search for the UK price field
        for field in col_map:
            if "our_price" in field and "a1f83g8c2aro7p" in field:
                ws.cell(row=row, column=col_map[field], value=sell_price)
                break

    # List price with tax (for strikethrough display)
    c = col("list_price_with_tax")
    if c:
        ws.cell(row=row, column=c, value=sell_price)

    # Business price — enables B2B offers and helps Featured Offer eligibility
    c = col("business_price")
    if c:
        ws.cell(row=row, column=c, value=sell_price)

    # Condition
    c = col("condition_type")
    if c:
        ws.cell(row=row, column=c, value="New")

    # Fulfillment
    c = col("fulfillment_availability#1.fulfillment_channel_code")
    if c:
        ws.cell(row=row, column=c, value="DEFAULT")
    c = col("fulfillment_availability#1.quantity")
    if c:
        ws.cell(row=row, column=c, value=QUANTITY)
    c = col("fulfillment_availability#1.lead_time_to_ship_max_days")
    if c:
        ws.cell(row=row, column=c, value=HANDLING_DAYS)


def fill_amazon_template(template_path, products):
    """Fill Amazon .xlsm template. Handles parent/child variations, all images."""
    import openpyxl
    wb = openpyxl.load_workbook(template_path, keep_vba=True)
    ws = wb["Template"]
    col_map = detect_columns(ws)

    def col(field_name):
        return col_map.get(field_name.lower(), None)

    start_row = 4
    filled = 0

    for product in products:
        pid = product.get("id", "")
        raw_title = product.get("product_title", "")
        title = clean_title(raw_title)

        # Skip products with trademarked brand/player/team names (error 18653)
        if _has_trademark_risk(raw_title) or _has_trademark_risk(title):
            log.warning(f"  SKIP trademark risk: {raw_title[:80]}")
            continue

        price_str = product.get("product_price", "")
        images = product.get("rehosted_images", [])
        variations_raw = product.get("variations", "")
        variation_images_raw = product.get("variation_images", "")

        price_usd = parse_price(price_str)
        shipping_str = product.get("shipping", "")
        sell_price = ali_to_gbp(price_usd, shipping_str=shipping_str)
        ali_desc = product.get("ali_description", "")
        bullets = make_bullets(title)
        description = make_description(title, ali_description=ali_desc)

        # Parse variations
        variations = []
        if variations_raw:
            try:
                variations = json.loads(variations_raw)
            except (json.JSONDecodeError, TypeError):
                pass

        # Determine if we need parent/child structure
        # Only create parent/child if there are image-based variations (e.g. color/style)
        has_variation_images = False
        color_variation = None
        for var in variations:
            for opt in var.get("options", []):
                if opt.get("image"):
                    has_variation_images = True
                    color_variation = var
                    break
            if has_variation_images:
                break

        if has_variation_images and color_variation and len(color_variation.get("options", [])) > 1:
            # === PARENT/CHILD LISTING ===
            parent_sku = "ALI-" + str(pid)

            # --- Parent row ---
            row = start_row + filled

            c = col("feed_product_type")
            if c:
                ws.cell(row=row, column=c, value=PRODUCT_TYPE)
            c = col("item_sku")
            if c:
                ws.cell(row=row, column=c, value=parent_sku)
            c = col("brand_name")
            if c:
                ws.cell(row=row, column=c, value=BRAND)
            c = col("external_product_id_type")
            if c:
                ws.cell(row=row, column=c, value="product_id_exempt")
            # Leave external_product_id empty for exempt
            c = col("item_name")
            if c:
                ws.cell(row=row, column=c, value=title)
            c = col("manufacturer")
            if c:
                ws.cell(row=row, column=c, value=BRAND)
            c = col("part_number")
            if c:
                ws.cell(row=row, column=c, value="RN-" + str(pid)[-8:])
            c = col("recommended_browse_nodes")
            if c:
                ws.cell(row=row, column=c, value=BROWSE_NODE)
            c = col("product_description")
            if c:
                ws.cell(row=row, column=c, value=description)
            # Parent: set parentage
            c = col("parent_child")
            if c:
                ws.cell(row=row, column=c, value="Parent")
            c = col("variation_theme")
            if c:
                ws.cell(row=row, column=c, value="Color")

            for i, bp in enumerate(["bullet_point1", "bullet_point2", "bullet_point3", "bullet_point4", "bullet_point5"]):
                c = col(bp)
                if c and i < len(bullets):
                    ws.cell(row=row, column=c, value=bullets[i])

            c = col("generic_keywords")
            if c:
                words = re.findall(r'\b[a-zA-Z]{3,}\b', title.lower())
                ws.cell(row=row, column=c, value=" ".join(list(dict.fromkeys(words))[:20]))

            c = col("country_of_origin")
            if c:
                ws.cell(row=row, column=c, value="China")
            c = col("item_weight")
            if c:
                ws.cell(row=row, column=c, value=0.5)
            c = col("item_weight_unit_of_measure")
            if c:
                ws.cell(row=row, column=c, value="KG")
            c = col("batteries_required")
            if c:
                ws.cell(row=row, column=c, value="No")
            c = col("are_batteries_included")
            if c:
                ws.cell(row=row, column=c, value="No")
            for dg in ["supplier_declared_dg_hz_regulation1", "supplier_declared_dg_hz_regulation2",
                        "supplier_declared_dg_hz_regulation3", "supplier_declared_dg_hz_regulation4",
                        "supplier_declared_dg_hz_regulation5"]:
                c = col(dg)
                if c:
                    ws.cell(row=row, column=c, value="Not Applicable")
            c = col("is_expiration_dated_product")
            if c:
                ws.cell(row=row, column=c, value="No")
            _fill_toy_figure_fields(ws, row, col)
            _fill_quality_attributes(ws, row, col, title)
            _fill_offer_fields(ws, row, col, col_map, sell_price)

            # Main image on parent row
            main_img = images[0] if images else ""
            c = col("main_image_url")
            if c and main_img:
                ws.cell(row=row, column=c, value=main_img)

            filled += 1

            # --- Child rows (one per variation option) ---
            for opt_idx, option in enumerate(color_variation.get("options", [])):
                row = start_row + filled
                opt_name = option.get("name", f"Style {opt_idx + 1}")
                child_sku = f"ALI-{pid}-{opt_idx + 1:02d}"

                c = col("feed_product_type")
                if c:
                    ws.cell(row=row, column=c, value=PRODUCT_TYPE)
                c = col("item_sku")
                if c:
                    ws.cell(row=row, column=c, value=child_sku)
                c = col("brand_name")
                if c:
                    ws.cell(row=row, column=c, value=BRAND)
                c = col("external_product_id_type")
                if c:
                    ws.cell(row=row, column=c, value="product_id_exempt")
                c = col("item_name")
                if c:
                    ws.cell(row=row, column=c, value=f"{title} - {opt_name}")
                c = col("manufacturer")
                if c:
                    ws.cell(row=row, column=c, value=BRAND)
                c = col("part_number")
                if c:
                    ws.cell(row=row, column=c, value=f"RN-{str(pid)[-6:]}-{opt_idx + 1:02d}")
                c = col("recommended_browse_nodes")
                if c:
                    ws.cell(row=row, column=c, value=BROWSE_NODE)

                # Parent/child relationship
                c = col("parent_child")
                if c:
                    ws.cell(row=row, column=c, value="Child")
                c = col("parent_sku")
                if c:
                    ws.cell(row=row, column=c, value=parent_sku)
                c = col("relationship_type")
                if c:
                    ws.cell(row=row, column=c, value="Variation")
                c = col("variation_theme")
                if c:
                    ws.cell(row=row, column=c, value="Color")
                c = col("color_name")
                if c:
                    ws.cell(row=row, column=c, value=opt_name[:50] if opt_name else f"Style {opt_idx + 1}")

                # Main image — use variation image if available, otherwise first product image
                opt_img = option.get("rehosted_image", "")
                main_img = opt_img or (images[0] if images else "")
                c = col("main_image_url")
                if c and main_img:
                    ws.cell(row=row, column=c, value=main_img)

                # Other images — fill remaining slots with product gallery images
                other_imgs = [img for img in images if img != main_img]
                for img_idx, img_field in enumerate(["other_image_url1", "other_image_url2", "other_image_url3",
                                                      "other_image_url4", "other_image_url5", "other_image_url6",
                                                      "other_image_url7", "other_image_url8"]):
                    c = col(img_field)
                    if c and img_idx < len(other_imgs):
                        ws.cell(row=row, column=c, value=other_imgs[img_idx])

                c = col("product_description")
                if c:
                    ws.cell(row=row, column=c, value=description)

                for i, bp in enumerate(["bullet_point1", "bullet_point2", "bullet_point3", "bullet_point4", "bullet_point5"]):
                    c = col(bp)
                    if c and i < len(bullets):
                        ws.cell(row=row, column=c, value=bullets[i])

                c = col("country_of_origin")
                if c:
                    ws.cell(row=row, column=c, value="China")
                c = col("item_weight")
                if c:
                    ws.cell(row=row, column=c, value=0.5)
                c = col("item_weight_unit_of_measure")
                if c:
                    ws.cell(row=row, column=c, value="KG")
                c = col("batteries_required")
                if c:
                    ws.cell(row=row, column=c, value="No")
                c = col("are_batteries_included")
                if c:
                    ws.cell(row=row, column=c, value="No")
                for dg in ["supplier_declared_dg_hz_regulation1", "supplier_declared_dg_hz_regulation2",
                            "supplier_declared_dg_hz_regulation3", "supplier_declared_dg_hz_regulation4",
                            "supplier_declared_dg_hz_regulation5"]:
                    c = col(dg)
                    if c:
                        ws.cell(row=row, column=c, value="Not Applicable")
                c = col("is_expiration_dated_product")
                if c:
                    ws.cell(row=row, column=c, value="No")
                _fill_toy_figure_fields(ws, row, col)
                _fill_quality_attributes(ws, row, col, title)
                _fill_offer_fields(ws, row, col, col_map, sell_price)

                filled += 1

        else:
            # === SIMPLE LISTING (no variations with images) ===
            row = start_row + filled

            c = col("feed_product_type")
            if c:
                ws.cell(row=row, column=c, value=PRODUCT_TYPE)
            c = col("item_sku")
            if c:
                ws.cell(row=row, column=c, value="ALI-" + str(pid))
            c = col("brand_name")
            if c:
                ws.cell(row=row, column=c, value=BRAND)
            c = col("external_product_id_type")
            if c:
                ws.cell(row=row, column=c, value="product_id_exempt")
            # Leave external_product_id empty for exempt
            c = col("item_name")
            if c:
                ws.cell(row=row, column=c, value=title)
            c = col("manufacturer")
            if c:
                ws.cell(row=row, column=c, value=BRAND)
            c = col("part_number")
            if c:
                ws.cell(row=row, column=c, value="RN-" + str(pid)[-8:])
            c = col("recommended_browse_nodes")
            if c:
                ws.cell(row=row, column=c, value=BROWSE_NODE)
            c = col("product_description")
            if c:
                ws.cell(row=row, column=c, value=description)

            # Main image
            main_img = images[0] if images else ""
            c = col("main_image_url")
            if c and main_img:
                ws.cell(row=row, column=c, value=main_img)

            # Other images (up to 8)
            other_imgs = images[1:9] if len(images) > 1 else []
            for img_idx, img_field in enumerate(["other_image_url1", "other_image_url2", "other_image_url3",
                                                  "other_image_url4", "other_image_url5", "other_image_url6",
                                                  "other_image_url7", "other_image_url8"]):
                c = col(img_field)
                if c and img_idx < len(other_imgs):
                    ws.cell(row=row, column=c, value=other_imgs[img_idx])

            for i, bp in enumerate(["bullet_point1", "bullet_point2", "bullet_point3", "bullet_point4", "bullet_point5"]):
                c = col(bp)
                if c and i < len(bullets):
                    ws.cell(row=row, column=c, value=bullets[i])

            c = col("generic_keywords")
            if c:
                words = re.findall(r'\b[a-zA-Z]{3,}\b', title.lower())
                ws.cell(row=row, column=c, value=" ".join(list(dict.fromkeys(words))[:20]))

            c = col("country_of_origin")
            if c:
                ws.cell(row=row, column=c, value="China")
            c = col("item_weight")
            if c:
                ws.cell(row=row, column=c, value=0.5)
            c = col("item_weight_unit_of_measure")
            if c:
                ws.cell(row=row, column=c, value="KG")
            c = col("batteries_required")
            if c:
                ws.cell(row=row, column=c, value="No")
            c = col("are_batteries_included")
            if c:
                ws.cell(row=row, column=c, value="No")
            for dg in ["supplier_declared_dg_hz_regulation1", "supplier_declared_dg_hz_regulation2",
                        "supplier_declared_dg_hz_regulation3", "supplier_declared_dg_hz_regulation4",
                        "supplier_declared_dg_hz_regulation5"]:
                c = col(dg)
                if c:
                    ws.cell(row=row, column=c, value="Not Applicable")
            c = col("is_expiration_dated_product")
            if c:
                ws.cell(row=row, column=c, value="No")
            _fill_toy_figure_fields(ws, row, col)
            _fill_quality_attributes(ws, row, col, title)
            _fill_offer_fields(ws, row, col, col_map, sell_price)

            filled += 1

        if filled % 50 == 0:
            log.info("  Filled %d rows...", filled)

    # --- Output as tab-delimited text ---
    # Only include columns that have a valid row3 header (field name).
    # Empty headers cause Amazon error 90061 "field heading is invalid".
    max_col = max(ws.max_column or 308, 460)
    # Columns Amazon rejects with error 90061 "field heading is invalid"
    INVALID_FIELD_HEADINGS = {"quantity_price_type",
                               "quantity_lower_bound1", "quantity_price1",
                               "quantity_lower_bound2", "quantity_price2",
                               "quantity_lower_bound3", "quantity_price3",
                               "quantity_lower_bound4", "quantity_price4",
                               "quantity_lower_bound5", "quantity_price5"}

    valid_cols = []
    for c in range(1, max_col + 1):
        r3 = ws.cell(row=3, column=c).value
        if r3 and str(r3).strip():
            r3s = str(r3).strip()
            # Skip the processing report error columns that Amazon adds back
            if r3s.startswith("::"):
                continue
            # Skip columns Amazon rejects as invalid headings
            if r3s.lower() in INVALID_FIELD_HEADINGS:
                continue
            valid_cols.append(c)

    row1_vals = []
    row2_vals = []
    row3_vals = []
    for c in valid_cols:
        row1_vals.append(str(ws.cell(row=1, column=c).value or ""))
        row2_vals.append(str(ws.cell(row=2, column=c).value or ""))
        row3_vals.append(str(ws.cell(row=3, column=c).value or ""))

    data_rows = []
    for r in range(start_row, start_row + filled):
        row_data = []
        for c in valid_cols:
            val = ws.cell(row=r, column=c).value
            row_data.append(str(val) if val is not None else "")
        data_rows.append(row_data)

    # Cache worksheet data before closing (needed for offer update file)
    ws_copy_r1 = {c: ws.cell(row=1, column=c).value for c in range(1, max_col + 1)}
    ws_copy_r2 = {c: ws.cell(row=2, column=c).value for c in range(1, max_col + 1)}
    ws_copy_r3 = {c: ws.cell(row=3, column=c).value for c in range(1, max_col + 1)}
    ws_copy_data = {}
    for r in range(start_row, start_row + filled):
        for c in range(1, max_col + 1):
            val = ws.cell(row=r, column=c).value
            if val is not None:
                ws_copy_data[(r, c)] = val

    wb.close()

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_name = f"amazon_upload_{ts}.txt"
    with open(output_name, "w", encoding="utf-8") as f:
        f.write("\t".join(row1_vals) + "\n")
        f.write("\t".join(row2_vals) + "\n")
        f.write("\t".join(row3_vals) + "\n")
        for row_data in data_rows:
            f.write("\t".join(row_data) + "\n")

    # --- Also generate offer-only PartialUpdate file ---
    # Amazon often creates the product but doesn't attach the offer on first upload.
    # This separate file forces offers onto existing listings.
    offer_fields_needed = [
        'feed_product_type', 'item_sku', 'update_delete', 'condition_type',
        'list_price_with_tax', 'business_price',
        'fulfillment_availability#1.fulfillment_channel_code',
        'fulfillment_availability#1.quantity',
        'fulfillment_availability#1.lead_time_to_ship_max_days',
        'purchasable_offer[marketplace_id=a1f83g8c2aro7p]#1.our_price#1.schedule#1.value_with_tax',
    ]
    offer_col_indices = []
    for f in offer_fields_needed:
        c = col_map.get(f.lower())
        if c:
            offer_col_indices.append(c)
    if offer_col_indices:
        offer_r1 = [str(ws_copy_r1.get(c, "")) for c in offer_col_indices]
        offer_r2 = [str(ws_copy_r2.get(c, "")) for c in offer_col_indices]
        offer_r3 = [str(ws_copy_r3.get(c, "")) for c in offer_col_indices]
        offer_name = f"amazon_offer_update_{ts}.txt"
        with open(offer_name, "w", encoding="utf-8") as f:
            f.write("\t".join(offer_r1) + "\n")
            f.write("\t".join(offer_r2) + "\n")
            f.write("\t".join(offer_r3) + "\n")
            for r in range(start_row, start_row + filled):
                row_data = []
                for ci, c in enumerate(offer_col_indices):
                    field = offer_fields_needed[ci]
                    if field == 'update_delete':
                        row_data.append("PartialUpdate")
                    else:
                        val = ws_copy_data.get((r, c))
                        row_data.append(str(val) if val is not None else "")
                f.write("\t".join(row_data) + "\n")
        log.info("  Also generated offer update file: %s", offer_name)
        log.info("  Upload this AFTER the main file to fix any missing offers.")

    return output_name, filled


# ---------------------------------------------------------------------------
# Post-processing pipeline
# ---------------------------------------------------------------------------
def post_process(csv_path):
    log.info("=" * 60)
    log.info("POST-PROCESSING PIPELINE")
    log.info("=" * 60)

    # --- Step 1: Load and deduplicate ---
    log.info("Step 1: Loading and deduplicating...")
    with open(csv_path, "r", encoding="utf-8-sig") as f:
        reader = csv.DictReader(f)
        fieldnames = list(reader.fieldnames)
        rows = list(reader)

    original_count = len(rows)
    seen_ids = set()
    seen_titles = set()
    unique_rows = []
    for row in rows:
        pid = row.get("id", "").strip()
        title = row.get("product_title", "").strip().lower()
        if pid and pid in seen_ids:
            continue
        if title and title in seen_titles:
            continue
        if pid:
            seen_ids.add(pid)
        if title:
            seen_titles.add(title)
        unique_rows.append(row)

    dupes = original_count - len(unique_rows)
    log.info("  %d products -> %d unique (%d duplicates removed)", original_count, len(unique_rows), dupes)

    # --- Step 2: Filter for resin models ---
    log.info("Step 2: Filtering for resin models / model kits...")
    resin_rows = []
    rejected = []
    for row in unique_rows:
        title = row.get("product_title", "")
        if is_resin_model(title):
            resin_rows.append(row)
        else:
            rejected.append(title[:60])

    log.info("  %d resin models found out of %d unique products", len(resin_rows), len(unique_rows))
    log.info("  %d non-resin products filtered out", len(rejected))

    if not resin_rows:
        log.warning("  No resin models found! Check your search URLs.")
        log.info("  Sample rejected titles:")
        for t in rejected[:10]:
            log.info("    - %s", t)
        return

    # Save filtered CSV
    base = os.path.splitext(csv_path)[0]
    filtered_path = f"{base}_resin_models.csv"
    with open(filtered_path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames, extrasaction="ignore")
        w.writeheader()
        w.writerows(resin_rows)
    log.info("  Saved filtered CSV: %s", filtered_path)

    # --- Step 3: Rehost ALL images (parallel) ---
    log.info("Step 3: Rehosting images (Amazon-compatible JPEG hosting)...")
    rehosted_count = 0
    failed_count = 0

    # Collect all image URLs with back-references to where results go
    upload_tasks = []  # list of (row_index, slot_type, slot_key, img_url)
    for row_idx, row in enumerate(resin_rows):
        all_images_str = row.get("product_images", "")
        all_images = [img.strip() for img in all_images_str.split("|") if img.strip()] if all_images_str else []
        if not all_images:
            single_img = row.get("product_image", "")
            if single_img:
                all_images = [single_img]
        for img_i, img_url in enumerate(all_images[:MAX_IMAGES]):
            upload_tasks.append((row_idx, "main", img_i, img_url))

        variations_raw = row.get("variations", "")
        if variations_raw:
            try:
                variations = json.loads(variations_raw)
                for var_i, var in enumerate(variations):
                    for opt_i, opt in enumerate(var.get("options", [])):
                        opt_img = opt.get("image", "")
                        if opt_img:
                            upload_tasks.append((row_idx, "var", (var_i, opt_i), opt_img))
            except (json.JSONDecodeError, TypeError):
                pass

    log.info("  %d images to rehost across %d products (parallel, 3 workers)...",
             len(upload_tasks), len(resin_rows))

    # Run uploads in parallel
    results = {}  # task_index -> new_url
    with ThreadPoolExecutor(max_workers=3) as pool:
        future_map = {pool.submit(rehost_image, task[3]): i for i, task in enumerate(upload_tasks)}
        for future in as_completed(future_map):
            idx = future_map[future]
            try:
                results[idx] = future.result()
            except Exception:
                results[idx] = None
            done = len(results)
            if done % 20 == 0:
                log.info("    Processed %d / %d images...", done, len(upload_tasks))

    # Apply results back to rows
    for task_idx, (row_idx, slot_type, slot_key, img_url) in enumerate(upload_tasks):
        new_url = results.get(task_idx)
        row = resin_rows[row_idx]
        if new_url and new_url != "SKIPPED":
            if slot_type == "main":
                row.setdefault("rehosted_images", [])
                # Store with index to preserve order
                row.setdefault("_rehost_ordered", [])
                row["_rehost_ordered"].append((slot_key, new_url))
            else:
                var_i, opt_i = slot_key
                variations = json.loads(row.get("variations", "[]"))
                variations[var_i]["options"][opt_i]["rehosted_image"] = new_url
                row["variations"] = json.dumps(variations)
            rehosted_count += 1
        elif new_url == "SKIPPED":
            pass
        else:
            failed_count += 1
            log.warning("    FAILED to rehost: %s", img_url[:80])

    # Finalize ordered main images
    for row in resin_rows:
        ordered = row.pop("_rehost_ordered", [])
        ordered.sort(key=lambda x: x[0])
        row["rehosted_images"] = [url for _, url in ordered]

    log.info("  Rehosted %d images, %d failed", rehosted_count, failed_count)

    # --- Step 4: Fill Amazon template ---
    log.info("Step 4: Looking for Amazon .xlsm template...")
    template_path = find_amazon_template()
    if not template_path:
        log.warning("  No .xlsm Amazon template found in current directory.")
        log.info("  Place the Amazon ART_CRAFT_KIT.xlsm template here and re-run.")
        log.info("  Filtered CSV saved at: %s", filtered_path)
        return

    log.info("  Using template: %s", template_path)
    log.info("  Filling %d products into Amazon template...", len(resin_rows))

    try:
        output_file, count = fill_amazon_template(template_path, resin_rows)
        log.info("=" * 60)
        log.info("  DONE! %d rows -> %s", count, output_file)
        log.info("=" * 60)
        log.info("")
        log.info("BEFORE UPLOADING:")
        log.info("  1. Make sure GTIN exemption is approved for brand 'Generic' in Toys > Toy Figures category")
        log.info("     Seller Central > Catalogue > Add Products > 'I need to apply for GTIN exemption'")
        log.info("  2. Upload via Catalogue > Add Products via Upload")
        log.info("  3. Review titles and prices")
        log.info("  4. Brand is set to 'Generic' throughout")
        log.info("  5. Products with variations will have parent + child rows")
    except ImportError:
        log.error("  openpyxl not installed! Run: pip3 install openpyxl")
        log.info("  Filtered CSV saved at: %s", filtered_path)
    except Exception as e:
        log.error("  Error filling template: %s", e)
        import traceback
        traceback.print_exc()
        log.info("  Filtered CSV saved at: %s", filtered_path)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
def main():
    global _cached_moduleanalysis_url, _store_desc_strategy, _store_desc_failures
    parser = argparse.ArgumentParser(
        description="Scrape AliExpress products and generate Amazon bulk upload file"
    )
    parser.add_argument("urls_file", help="Text file with AliExpress URLs (one per line)")
    parser.add_argument("-o", "--output", default=None, help="Output CSV path")
    parser.add_argument("--skip-details", action="store_true",
                        help="Skip visiting individual product pages (faster but only 1 image)")
    parser.add_argument("--proxy", default=None,
                        help="Proxy server URL (e.g. http://user:pass@host:port or socks5://host:port)")
    parser.add_argument("--limit", type=int, default=0,
                        help="Limit total number of products to scrape (0 = no limit)")
    parser.add_argument("--resume", action="store_true",
                        help="Resume from existing CSV — skip already-scraped products")
    args = parser.parse_args()

    lines = Path(args.urls_file).read_text().splitlines()
    urls = [l.strip() for l in lines if l.strip() and not l.strip().startswith("#")]
    if not urls:
        print("No URLs found.")
        sys.exit(1)

    ts = datetime.now().strftime("%Y-%m-%d_%H%M")
    out = args.output or f"aliexpress_scrape_{ts}.csv"

    # Auto-detect resume: if output file exists and --resume not explicitly set,
    # check if there's data to resume from
    resume = args.resume
    if not resume and args.output and os.path.exists(args.output):
        resume = True
        log.info("Existing output file found — auto-resuming.")

    csv_out = LiveCSV(out, resume=resume)
    log.info("Output: %s (%d products already scraped)", out, csv_out.count)

    # Start local proxy forwarders for SOCKS5 proxies
    proxy_local_urls = []
    if not args.proxy and PROXY_POOL:
        proxy_local_urls = start_proxy_forwarders()
    proxy_index = [0]  # mutable so nested functions can update it

    def get_proxy_server():
        """Get the current proxy server URL."""
        if args.proxy:
            return args.proxy
        if proxy_local_urls:
            return proxy_local_urls[proxy_index[0] % len(proxy_local_urls)]
        return None

    def rotate_proxy():
        """Switch to the next proxy in the pool."""
        if proxy_local_urls and not args.proxy:
            proxy_index[0] += 1
            log.info("  Rotated to proxy: %s", get_proxy_server())

    with sync_playwright() as pw:
        browser = None
        context = None
        tab = None

        def ensure_browser(force_new=False):
            nonlocal browser, context, tab
            if not force_new:
                try:
                    if tab:
                        tab.url
                        return
                except Exception:
                    pass
            log.info("Opening browser...")
            try:
                if context:
                    context.close()
            except Exception:
                pass
            try:
                if browser:
                    browser.close()
            except Exception:
                pass
            launch_kwargs = dict(
                headless=False,
                channel="msedge",
                args=["--disable-blink-features=AutomationControlled"],
            )
            proxy_server = get_proxy_server()
            if proxy_server:
                launch_kwargs["proxy"] = {"server": proxy_server}
                log.info("  Using proxy: %s", proxy_server)
            browser = pw.chromium.launch(**launch_kwargs)
            ctx_kwargs = dict(
                viewport={"width": 1280, "height": 800},
                locale="en-US",
            )
            context = browser.new_context(**ctx_kwargs)
            context.add_init_script("""
                Object.defineProperty(navigator, 'webdriver', { get: () => undefined });
            """)
            tab = context.new_page()

        # --- Login to AliExpress before scraping ---
        ensure_browser()
        log.info("=" * 60)
        log.info(">>> Please log in to AliExpress in the browser window. <<<")
        log.info("=" * 60)
        log.info("Navigating to AliExpress login...")
        try:
            tab.goto("https://login.aliexpress.com/", wait_until="domcontentloaded", timeout=30000)
            log.info("  Login page loaded.")
        except Exception as e:
            log.warning("  Login page failed (%s), trying main page...", str(e)[:80])
            try:
                tab.goto("https://www.aliexpress.com/", wait_until="domcontentloaded", timeout=30000)
                log.info("  Main page loaded.")
            except Exception as e2:
                log.warning("  Main page also failed: %s", str(e2)[:80])

        # Wait for user to complete login
        # Check if already logged in (has account icon/name) or on login page
        logged_in = False
        while not logged_in:
            try:
                # Check if we're on a login/passport page
                current_url = tab.url.lower()
                on_login_page = any(w in current_url for w in ["login", "passport", "signin"])

                if not on_login_page:
                    # We navigated away from login — check if actually logged in
                    # Look for account indicators (avatar, username, "My Account")
                    account_indicators = tab.evaluate("""
                    () => {
                        // Check for common logged-in indicators
                        const sels = [
                            '[class*="my-account"]', '[class*="MyAccount"]',
                            '[class*="user-name"]', '[class*="UserName"]',
                            '[class*="avatar"]', '[class*="Avatar"]',
                            'a[href*="buyer.aliexpress"]',
                            '[class*="account-signed"]',
                            'img[class*="avatar"]',
                        ];
                        for (const sel of sels) {
                            const el = document.querySelector(sel);
                            if (el) return true;
                        }
                        // Check if "Sign in" text is still showing (not logged in)
                        const body = document.body.innerText || '';
                        if (body.includes('My Account') || body.includes('My Orders')) return true;
                        return false;
                    }
                    """)
                    if account_indicators:
                        logged_in = True
                        break

                    # Also accept if user just navigated to the main page
                    # (they might have been already logged in via cookies)
                    if "aliexpress.com" in current_url and not on_login_page:
                        # Give user a moment, then ask
                        tab.wait_for_timeout(2000)
                        # Re-check
                        account_check = tab.evaluate("""
                        () => {
                            const body = document.body.innerText || '';
                            // If "Sign in" or "Join" prominent, not logged in
                            const signInBtn = document.querySelector('a[href*="login"], [class*="sign-in"], [data-role="sign-in"]');
                            if (signInBtn && signInBtn.offsetParent !== null) return false;
                            return true;
                        }
                        """)
                        if account_check:
                            logged_in = True
                            break
            except Exception:
                pass

            if not logged_in:
                print("\a", flush=True)  # Beep
                log.info("  Waiting for login... (log in and the scraper will continue automatically)")
                tab.wait_for_timeout(3000)

        log.info(">>> Login detected! Starting scrape... <<<")
        log.info("=" * 60)

        for i, url in enumerate(urls, 1):
            url = sort_by_orders(url)
            log.info("[%d/%d] %s", i, len(urls), url)

            # Reset store-level cache for new URL
            _cached_moduleanalysis_url = ""
            _store_desc_strategy = ""
            _store_desc_failures = 0

            ensure_browser()

            try:
                tab.goto(url, wait_until="domcontentloaded", timeout=30000)
            except Exception as e:
                err = str(e).lower()
                if "closed" in err or "crashed" in err:
                    log.warning("  Browser closed — reopening...")
                    tab = None
                    ensure_browser()
                    try:
                        tab.goto(url, wait_until="domcontentloaded", timeout=30000)
                    except Exception as e2:
                        log.warning("  Load error: %s", e2)
                        continue
                else:
                    try:
                        if is_captcha(tab):
                            handle_captcha(tab)
                            try:
                                tab.goto(url, wait_until="domcontentloaded", timeout=30000)
                            except Exception:
                                continue
                        else:
                            log.warning("  Load error: %s", e)
                            continue
                    except Exception:
                        log.warning("  Load error: %s", e)
                        continue

            # Check for IP block after initial page load
            if is_blocked(tab) and PROXY_POOL:
                log.warning("  IP blocked — rotating proxy and retrying...")
                rotate_proxy()
                ensure_browser(force_new=True)
                try:
                    tab.goto(url, wait_until="domcontentloaded", timeout=30000)
                except Exception:
                    pass
                if is_blocked(tab):
                    log.warning("  Still blocked after proxy rotation — skipping URL")
                    continue

            pg = 1
            orders_sorted = False
            low_sales_stop = False
            no_new_pages = 0
            while pg <= MAX_PAGES:
                log.info("  Page %d", pg)
                # Build page-specific URL so CAPTCHA recovery returns to correct page
                page_url = sort_by_orders(url)
                if pg > 1:
                    parsed = urlparse(page_url)
                    qs = parse_qs(parsed.query, keep_blank_values=True)
                    qs["page"] = [str(pg)]
                    page_url = urlunparse(parsed._replace(query=urlencode(qs, doseq=True)))
                wait_ready(tab, page_url)
                dismiss_popups(tab)

                # On first page, click "Orders" sort button if available
                if pg == 1 and not orders_sorted:
                    click_orders_sort(tab)
                    orders_sorted = True
                    # Re-extract after sorting
                    tab.wait_for_timeout(1000)

                products = scroll_and_extract(tab)

                # If no products found, check if CAPTCHA appeared during scrolling
                if not products:
                    if is_captcha(tab):
                        log.warning("  CAPTCHA appeared during extraction — pausing...")
                        handle_captcha(tab)
                        # Re-navigate and retry extraction after CAPTCHA solved
                        try:
                            tab.goto(page_url, wait_until="domcontentloaded", timeout=30000)
                            wait_ready(tab, page_url)
                            dismiss_popups(tab)
                            products = scroll_and_extract(tab)
                        except Exception:
                            pass
                    if not products and pg > 1:
                        log.info("  No products on page %d — done.", pg)
                        break

                # --- Stop at low sales (< 5 sold) when sorted by orders ---
                # Since results are sorted by orders desc, once we see < 5 sales
                # all remaining products will also have < 5, so stop this URL.
                # Include products with >= 5 sales, stop at the first with < 5.
                MIN_SALES_CUTOFF = 5
                filtered_products = []
                seen_any_sales = False
                for p in products:
                    sales_str = p.get("total_sales", "") or p.get("trade_info", "") or ""
                    # Parse "123 sold", "1,000+ sold", "5 sold", "3K+ sold", "1.2K sold" etc.
                    m = re.match(r'([\d,\.]+)\s*([KkMm])?\+?\s*[Ss]old', sales_str)
                    if m:
                        seen_any_sales = True
                        raw_num = float(m.group(1).replace(",", ""))
                        suffix = (m.group(2) or "").upper()
                        if suffix == "K":
                            raw_num *= 1000
                        elif suffix == "M":
                            raw_num *= 1000000
                        sales_num = int(raw_num)
                        if sales_num < MIN_SALES_CUTOFF:
                            log.info("    Product '%s' has %d sales (< %d) — stopping this store.",
                                     p.get("product_title", "")[:60], sales_num, MIN_SALES_CUTOFF)
                            low_sales_stop = True
                            break
                    elif seen_any_sales:
                        # No sales text after seeing products with sales = 0 sales
                        log.info("    Product '%s' has no sales data — stopping this store.",
                                 p.get("product_title", "")[:60])
                        low_sales_stop = True
                        break
                    filtered_products.append(p)
                products = filtered_products

                if low_sales_stop:
                    if products:
                        log.info("    Processing %d products before cutoff...", len(products))
                    else:
                        break

                # --- Skip already-scraped products (resume support) ---
                before_skip = len(products)
                products = [p for p in products if not csv_out.already_scraped(p.get("id", ""))]
                skipped = before_skip - len(products)
                if skipped:
                    log.info("    Skipped %d already-scraped products", skipped)

                # --- Apply limit ---
                if args.limit > 0:
                    remaining = args.limit - csv_out.count
                    if remaining <= 0:
                        log.info("  Reached product limit (%d). Stopping.", args.limit)
                        break
                    products = products[:remaining]

                # --- Visit each product detail page for ALL images + variations ---
                # Use parallel tabs for speed, fall back to sequential if needed.
                if not args.skip_details and products:
                    detail_results = None
                    # Try parallel detail scraping first (PARALLEL_TABS tabs)
                    if PARALLEL_TABS > 1:
                        detail_results = scrape_details_parallel(context, products, tab)
                    # Fall back to sequential if parallel failed or PARALLEL_TABS==1
                    if detail_results is None:
                        detail_results = []
                        detail_tab = None
                        try:
                            detail_tab = context.new_page()
                        except Exception as e:
                            log.warning("  Could not open detail tab: %s", e)
                        if detail_tab:
                            for p_idx, product in enumerate(products):
                                pid = product["id"]
                                product_url = product["product_url"]
                                if p_idx > 0:
                                    time.sleep(random.uniform(1.0, 1.8))
                                log.info("    [%d/%d] Fetching details for %s...", p_idx + 1, len(products), pid)
                                handle_captcha(tab)
                                detail_results.append(scrape_product_detail(detail_tab, product_url, pid, context=context, main_tab=tab))
                                try:
                                    for p in context.pages:
                                        if p != tab and p != detail_tab:
                                            p.close()
                                except Exception:
                                    pass
                            try:
                                detail_tab.close()
                            except Exception:
                                pass

                    # Apply detail results to products
                    if detail_results:
                        for p_idx, product in enumerate(products):
                            detail = detail_results[p_idx] if p_idx < len(detail_results) else None
                            if not detail:
                                continue
                            if detail["all_images"]:
                                product["product_images"] = "|".join(detail["all_images"])
                                if not product["product_image"] or product["product_image"].startswith("//"):
                                    product["product_image"] = detail["all_images"][0]
                            if detail["variations"]:
                                product["variations"] = json.dumps(detail["variations"])
                            if detail["detail_title"] and len(detail["detail_title"]) > len(product.get("product_title", "")):
                                product["product_title"] = detail["detail_title"]
                            # Fill in price from detail page when search page had N/A
                            if detail.get("detail_price") and (not product.get("product_price") or product["product_price"] == "N/A"):
                                product["product_price"] = detail["detail_price"]
                            # Fill in shipping cost from detail page
                            if detail.get("detail_shipping"):
                                product["shipping"] = detail["detail_shipping"]
                            # Fill in AliExpress description from detail page
                            if detail.get("detail_description"):
                                product["ali_description"] = detail["detail_description"]

                prev_total = csv_out.count
                csv_out.add(products, url)
                new_count = csv_out.count - prev_total
                log.info("  Page %d: %d products, %d new (total: %d)", pg, len(products), new_count, csv_out.count)

                if args.limit > 0 and csv_out.count >= args.limit:
                    log.info("  Reached product limit (%d). Stopping.", args.limit)
                    break

                if new_count == 0:
                    no_new_pages += 1
                    if no_new_pages >= 2:
                        log.info("  No new products for %d consecutive pages — done with this URL.", no_new_pages)
                        break
                    else:
                        log.info("  No new products on page %d — will try one more page.", pg)
                else:
                    no_new_pages = 0

                if low_sales_stop:
                    log.info("  Low sales cutoff reached — moving to next URL.")
                    break

                # --- Navigate to next page ---
                # Close any leftover popup tabs
                close_extra_tabs(context, tab)

                # Main tab is STILL on search results — just go to next page
                pg += 1
                log.info("  Navigating to page %d...", pg)

                # Try clicking pagination button first (works for store pages
                # where ?page=N URL param is ignored)
                clicked = click_next(tab, pg - 1)
                if clicked:
                    log.info("    Clicked pagination button for page %d", pg)
                    tab.wait_for_timeout(1500)
                    # Wait for new content to load
                    try:
                        tab.wait_for_selector("a[href*='/item/']", timeout=8000)
                    except Exception:
                        pass
                else:
                    # Fall back to direct URL navigation
                    next_page_url = sort_by_orders(url)
                    parsed = urlparse(next_page_url)
                    qs = parse_qs(parsed.query, keep_blank_values=True)
                    qs["page"] = [str(pg)]
                    next_page_url = urlunparse(parsed._replace(query=urlencode(qs, doseq=True)))
                    try:
                        tab.goto(next_page_url, wait_until="domcontentloaded", timeout=30000)
                        wait_ready(tab, next_page_url)
                    except Exception:
                        log.info("  Could not reach page %d — done.", pg)
                        break

                time.sleep(random.uniform(1.0, 1.8))

            if args.limit > 0 and csv_out.count >= args.limit:
                break

        try:
            context.close()
        except Exception:
            pass
        try:
            if browser:
                browser.close()
        except Exception:
            pass

    csv_out.close()
    log.info("Done! %d products -> %s", csv_out.count, out)

    # Post-process
    post_process(out)


if __name__ == "__main__":
    main()
