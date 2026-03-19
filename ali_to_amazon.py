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
import os
import random
import re
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
PARALLEL_TABS = 3               # Number of tabs for parallel detail fetching

# SOCKS5 proxy pool — rotated per URL to spread traffic
PROXY_POOL = [
    {
        "server": "socks5://165.49.88.29:11000",
        "username": "nodemavenJstTb",
        "password": "ROr1Sg4IVXzs",
    },
    {
        "server": "socks5://78.24.126.8:12324",
        "username": "14ae8bf2e23dd",
        "password": "77c507a188",
    },
]

# ---- SMART PRICING CONFIG ----
TARGET_PROFIT_MARGIN = 0.30
AMAZON_REFERRAL_FEE = 0.1545
AMAZON_PER_ITEM_FEE = 0.75
USD_TO_GBP = 0.79
ALI_SHIPPING_ESTIMATE = 2.00
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
    def __init__(self, path):
        self.path = path
        self.count = 0
        self._seen = set()
        self._f = open(path, "w", newline="", encoding="utf-8")
        self._w = csv.DictWriter(self._f, fieldnames=FIELDS, extrasaction="ignore")
        self._w.writeheader()
        self._f.flush()

    def add(self, rows, source_url):
        dupes = 0
        for r in rows:
            pid = r.get("id", "")
            if pid in self._seen:
                dupes += 1
                continue
            self._seen.add(pid)
            r["source_url"] = source_url
            self._w.writerow(r)
            self.count += 1
        self._f.flush()
        if dupes:
            log.info("  Skipped %d duplicate products", dupes)

    def close(self):
        self._f.close()


# ---------------------------------------------------------------------------
# URL helpers
# ---------------------------------------------------------------------------
def sort_by_orders(url):
    parsed = urlparse(url)
    qs = parse_qs(parsed.query, keep_blank_values=True)
    qs["SortType"] = ["total_tranpro_desc"]
    return urlunparse(parsed._replace(query=urlencode(qs, doseq=True)))


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
        const pm = cardText.match(/(?:US\\s*)?[\\$€£¥₽]\\s*[\\d,]+\\.?\\d*/);
        if (pm) {
            price = pm[0].trim();
        } else {
            const pm2 = cardText.match(/\\d+[,.]\\d{2}/);
            if (pm2) price = '$' + pm2[0];
        }

        let sales = '';
        const sm = cardText.match(/(\\d[\\d,\\.]*\\+?)\\s*[Ss]old/);
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
    };

    // --- Get ALL product images ---
    // Strategy 1: Look for image gallery/carousel thumbnails
    const gallerySelectors = [
        '.image-view-magnifier-wrap img',
        '.images-view-item img',
        '[class*="slider"] img[src*="alicdn"]',
        '[class*="gallery"] img[src*="alicdn"]',
        '[class*="image-view"] img',
        '.product-image-panel img',
        '.mag-img img',
        // Thumbnail strip
        '[class*="thumbnail"] img[src*="alicdn"]',
        '.images-view-wrap img',
    ];
    const imgSet = new Set();

    for (const sel of gallerySelectors) {
        const imgs = document.querySelectorAll(sel);
        for (const img of imgs) {
            let src = img.getAttribute('src') || img.getAttribute('data-src') || '';
            if (!src || src.includes('placeholder') || src.includes('48x48')) continue;
            // Clean up thumbnail URLs to get full size
            // AliExpress uses _50x50.jpg_ or _120x120.jpg_ for thumbnails
            src = src.replace(/_\d+x\d+[^.]*\./g, '.');
            // Remove any size suffix like .jpg_50x50.jpg
            src = src.replace(/\.(jpg|png|jpeg)_\d+x\d+[^.]*/gi, '.$1');
            // Ensure https
            if (src.startsWith('//')) src = 'https:' + src;
            if (src.includes('alicdn.com') && !imgSet.has(src)) {
                imgSet.add(src);
                result.images.push(src);
            }
        }
    }

    // Strategy 2: Look in page scripts for image data (most reliable)
    const scripts = document.querySelectorAll('script');
    for (const script of scripts) {
        const text = script.textContent || '';
        // Look for imagePathList or similar
        const imgListMatch = text.match(/"imagePathList"\\s*:\\s*\\[([^\\]]+)\\]/);
        if (imgListMatch) {
            const urls = imgListMatch[1].match(/"(https?:[^"]+)"/g);
            if (urls) {
                for (let url of urls) {
                    url = url.replace(/"/g, '');
                    if (url.startsWith('//')) url = 'https:' + url;
                    url = url.replace(/_\d+x\d+[^.]*\\./g, '.');
                    if (!imgSet.has(url)) {
                        imgSet.add(url);
                        result.images.push(url);
                    }
                }
            }
        }
    }

    // Strategy 3: Look for any large product images on the page
    const allImgs = document.querySelectorAll('img[src*="alicdn.com"]');
    for (const img of allImgs) {
        let src = img.getAttribute('src') || '';
        if (!src || src.includes('avatar') || src.includes('icon') || src.includes('logo')) continue;
        if (src.includes('48x48') || src.includes('placeholder')) continue;
        // Only include reasonably sized images
        const rect = img.getBoundingClientRect();
        if (rect.width < 80 && rect.height < 80 && !src.includes('_50x50') && !src.includes('_120x120')) continue;

        src = src.replace(/_\d+x\d+[^.]*\\./g, '.');
        src = src.replace(/\\.(jpg|png|jpeg)_\d+x\d+[^.]*/gi, '.$1');
        if (src.startsWith('//')) src = 'https:' + src;
        if (!imgSet.has(src)) {
            imgSet.add(src);
            result.images.push(src);
        }
    }

    // --- Get variations (SKU properties) ---
    // Look for variation/SKU selectors
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
                imgUrl = img.getAttribute('src') || img.getAttribute('data-src') || '';
                if (imgUrl.startsWith('//')) imgUrl = 'https:' + imgUrl;
                // Get full size version
                imgUrl = imgUrl.replace(/_\d+x\d+[^.]*\\./g, '.');
                imgUrl = imgUrl.replace(/\\.(jpg|png|jpeg)_\d+x\d+[^.]*/gi, '.$1');
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

    // Get price
    const priceEl = document.querySelector(
        '[class*="product-price-current"], [class*="uniform-banner-box-price"], ' +
        '[class*="price--current"], .product-price-value'
    );
    if (priceEl) result.price = priceEl.innerText.trim();

    return result;
}
"""


def scrape_product_detail(tab, product_url, product_id):
    """Visit a product detail page and extract all images + variations."""
    result = {
        "all_images": [],
        "variations": [],
        "detail_title": "",
        "detail_price": "",
    }

    try:
        tab.goto(product_url, wait_until="domcontentloaded", timeout=15000)
        # Wait for images to load
        try:
            tab.wait_for_selector('img[src*="alicdn"]', timeout=3000)
        except Exception:
            pass

        # Dismiss any popups
        dismiss_popups(tab)

        data = tab.evaluate(DETAIL_EXTRACT_JS)

        if data.get("images"):
            result["all_images"] = data["images"][:MAX_IMAGES]
        if data.get("variations"):
            result["variations"] = data["variations"]
        if data.get("title"):
            result["detail_title"] = data["title"]
        if data.get("price"):
            result["detail_price"] = data["price"]

    except Exception as e:
        log.debug("  Detail scrape failed for %s: %s", product_id, str(e)[:80])

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

        # Start navigation on all tabs simultaneously
        for i, product in enumerate(batch):
            pid = product["id"]
            product_url = product["product_url"]
            idx = batch_start + i
            log.info("    [%d/%d] Fetching details for %s...", idx + 1, len(products), pid)
            try:
                tabs[i].goto(product_url, wait_until="domcontentloaded", timeout=15000)
            except Exception as e:
                log.debug("  Detail nav failed for %s: %s", pid, str(e)[:80])
            # Small delay between tab navigations to reduce rate-limit risk
            time.sleep(random.uniform(0.3, 0.6))

        # Wait briefly for images to load on all tabs
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
                    tabs[i].goto(product["product_url"], wait_until="domcontentloaded", timeout=15000)
                except Exception:
                    pass
            time.sleep(0.8)

        # Extract data from all tabs
        for i, product in enumerate(batch):
            idx = batch_start + i
            pid = product["id"]
            result = {
                "all_images": [],
                "variations": [],
                "detail_title": "",
                "detail_price": "",
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

    # Try auto-solve (slider drag, simple button clicks — NOT image challenges)
    auto_att = 0
    while is_captcha(tab) and auto_att < 3:
        if try_solve_captcha(tab):
            auto_att += 1
            tab.wait_for_timeout(2000)
            # For AliExpress slider/button CAPTCHAs, a reload may help confirm
            if is_captcha(tab):
                try:
                    tab.reload(wait_until="domcontentloaded", timeout=15000)
                except Exception:
                    pass
                tab.wait_for_timeout(1000)
        else:
            break
    if not is_captcha(tab):
        log.info("  CAPTCHA auto-solved!")
        return
    # Manual solve needed — user must solve image challenge or other CAPTCHA
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
            # Try auto-solve first (checkbox, slider, button)
            auto_attempts = 0
            while is_captcha(tab) and auto_attempts < 3:
                if try_solve_captcha(tab):
                    auto_attempts += 1
                    # Reload to check if solve worked
                    try:
                        tab.reload(wait_until="domcontentloaded", timeout=15000)
                    except Exception:
                        pass
                    tab.wait_for_timeout(1000)
                else:
                    break
            if is_captcha(tab):
                # Auto-solve failed — ask user (do NOT reload while they solve)
                log.warning(">>> CAPTCHA detected! Solve it in the browser window. <<<")
                print("\a", flush=True)
                poll_count = 0
                while is_captcha(tab):
                    tab.wait_for_timeout(2000)
                    poll_count += 1
                    # Periodically reload to detect the solve
                    if poll_count % 3 == 0:
                        try:
                            tab.reload(wait_until="domcontentloaded", timeout=15000)
                        except Exception:
                            pass
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


SCROLL_JS = """
async () => {
    const step = window.innerHeight * 2;
    const delay = ms => new Promise(r => setTimeout(r, ms));
    let h = document.body.scrollHeight;
    let y = 0;
    while (y < h) {
        y += step;
        window.scrollTo(0, y);
        await delay(80);
        h = document.body.scrollHeight;
    }
    window.scrollTo(0, document.body.scrollHeight);
    await delay(150);
}
"""


def scroll_and_extract(tab):
    try:
        tab.evaluate(SCROLL_JS)
    except Exception:
        pass
    products = extract(tab)
    stale = 0
    while stale < 2:
        try:
            tab.evaluate("window.scrollTo(0, document.body.scrollHeight)")
            tab.wait_for_timeout(300)
        except Exception:
            break
        new = extract(tab)
        if len(new) > len(products):
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
                    return url
                else:
                    log.warning(f"          [IMG] imgbb uploaded but not accessible: {url}")
        log.warning(f"          [IMG] imgbb response: {resp.status_code} {resp.text[:200]}")
    except Exception as e:
        log.info(f"          [IMG] imgbb error: {e}")

    # Try freeimage.host as fallback
    hosted_url = _upload_to_freeimage(jpeg_bytes)
    if hosted_url and _verify_hosted_image(hosted_url):
        log.info(f"          [IMG] freeimage (iili.io): {hosted_url}")
        return hosted_url

    # Try Imgur as fallback
    hosted_url = _upload_to_imgur(jpeg_bytes)
    if hosted_url and _verify_hosted_image(hosted_url):
        log.info(f"          [IMG] Imgur: {hosted_url}")
        return hosted_url

    # Try catbox as last resort
    hosted_url = _upload_to_catbox(jpeg_bytes)
    if hosted_url and _verify_hosted_image(hosted_url):
        log.info(f"          [IMG] catbox: {hosted_url}")
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


def ali_to_gbp(price_usd):
    if not price_usd:
        return DEFAULT_PRICE_GBP
    cost_gbp = price_usd * USD_TO_GBP
    total_cost = cost_gbp + ALI_SHIPPING_ESTIMATE
    denominator = 1 - AMAZON_REFERRAL_FEE - TARGET_PROFIT_MARGIN
    if denominator <= 0:
        return DEFAULT_PRICE_GBP
    sell_price = (total_cost + AMAZON_PER_ITEM_FEE) / denominator
    sell_price = round(sell_price, 2)
    actual_profit = sell_price - (sell_price * AMAZON_REFERRAL_FEE) - AMAZON_PER_ITEM_FEE - total_cost
    if actual_profit < 6.0:
        sell_price = (6.0 + AMAZON_PER_ITEM_FEE + total_cost) / (1 - AMAZON_REFERRAL_FEE)
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


def make_description(title):
    """Generate a detailed, product-specific Amazon description."""
    clean = clean_title(title)
    text = title.lower()
    scale = _detect_scale(title)
    theme = _detect_theme(title)
    material = _detect_material(title)
    num = _detect_num_pieces(title)

    parts = [clean + "."]

    # Opening based on theme
    if "Military" in theme:
        parts.append(f"This {material.lower()} model kit captures the detail and character of military history.")
    elif "Fantasy" in theme:
        parts.append(f"This {material.lower()} fantasy model kit features intricate sculpting and dynamic posing.")
    elif "Diorama" in theme:
        parts.append(f"These miniature figures are perfect for creating vivid, lifelike diorama scenes.")
    elif "Historical" in theme:
        parts.append(f"This historically inspired {material.lower()} figure captures the period with authentic detail.")
    elif "Anime" in theme:
        parts.append(f"This premium {material.lower()} collectible statue features high-quality sculpting and finish.")
    elif "Sports" in theme:
        parts.append(f"A fun and detailed collectible figure for sports fans and figure collectors alike.")
    else:
        parts.append(f"This {material.lower()} model kit features carefully sculpted details for an impressive display piece.")

    # Scale info
    if scale:
        parts.append(f"Built to {scale} scale, this model is compatible with other figures and accessories in the same scale range.")

    # Kit details
    if "unpainted" in text or "unassembled" in text:
        parts.append("Supplied unassembled and unpainted, giving you complete freedom to bring this model to life with your own colour scheme and finishing techniques.")
    if num > 1:
        parts.append(f"This set includes {num} individual figures, each with their own unique pose and character detail.")

    # Closing
    parts.append(f"Crafted from high-quality {material.lower()} for sharp detail and durability.")
    parts.append("An excellent choice for collectors, painters, and hobbyists looking for their next project or display piece.")
    parts.append("Please refer to the product images for a detailed view of the model and its features.")

    return " ".join(parts)


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
        sell_price = ali_to_gbp(price_usd)
        bullets = make_bullets(title)
        description = make_description(title)

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
                               "quantity_lower_bound5", "quantity_price5",
                               "business_price"}

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

    log.info("  %d images to rehost across %d products (parallel, 6 workers)...",
             len(upload_tasks), len(resin_rows))

    # Run uploads in parallel
    results = {}  # task_index -> new_url
    with ThreadPoolExecutor(max_workers=6) as pool:
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
    args = parser.parse_args()

    lines = Path(args.urls_file).read_text().splitlines()
    urls = [l.strip() for l in lines if l.strip() and not l.strip().startswith("#")]
    if not urls:
        print("No URLs found.")
        sys.exit(1)

    ts = datetime.now().strftime("%Y-%m-%d_%H%M")
    out = args.output or f"aliexpress_scrape_{ts}.csv"
    csv_out = LiveCSV(out)
    log.info("Output: %s", out)

    proxy_index = [0]  # mutable so nested functions can update it

    def get_proxy_config():
        """Get the current proxy config from pool, --proxy flag, or None."""
        if args.proxy:
            return {"server": args.proxy}
        if PROXY_POOL:
            return PROXY_POOL[proxy_index[0] % len(PROXY_POOL)]
        return None

    def rotate_proxy():
        """Switch to the next proxy in the pool."""
        if PROXY_POOL and not args.proxy:
            proxy_index[0] += 1
            p = get_proxy_config()
            log.info("  Rotated to proxy: %s", p["server"])

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
                args=["--disable-blink-features=AutomationControlled"],
            )
            proxy = get_proxy_config()
            if proxy:
                proxy_cfg = {"server": proxy["server"]}
                if proxy.get("username"):
                    proxy_cfg["username"] = proxy["username"]
                    proxy_cfg["password"] = proxy.get("password", "")
                launch_kwargs["proxy"] = proxy_cfg
                log.info("  Using proxy: %s", proxy["server"])
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
        try:
            tab.goto("https://login.aliexpress.com/", wait_until="domcontentloaded", timeout=30000)
        except Exception:
            # Fallback URL
            try:
                tab.goto("https://www.aliexpress.com/", wait_until="domcontentloaded", timeout=30000)
            except Exception:
                pass

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
                products = scroll_and_extract(tab)

                if not products and pg > 1:
                    log.info("  No products on page %d — done.", pg)
                    break

                # --- Apply limit ---
                if args.limit > 0:
                    remaining = args.limit - csv_out.count
                    if remaining <= 0:
                        log.info("  Reached product limit (%d). Stopping.", args.limit)
                        break
                    products = products[:remaining]

                # --- Visit each product detail page for ALL images + variations ---
                used_sequential = False
                if not args.skip_details:
                    # Try parallel fetching first (3x faster)
                    detail_results = scrape_details_parallel(context, products, tab)

                    if detail_results is None:
                        # Fallback to sequential if parallel tabs failed
                        used_sequential = True
                        log.info("    Using sequential detail fetching...")
                        detail_results = []
                        for p_idx, product in enumerate(products):
                            pid = product["id"]
                            product_url = product["product_url"]
                            log.info("    [%d/%d] Fetching details for %s...", p_idx + 1, len(products), pid)
                            handle_captcha(tab)
                            detail_results.append(scrape_product_detail(tab, product_url, pid))
                            time.sleep(random.uniform(0.1, 0.3))

                    # Apply detail results to products
                    for p_idx, product in enumerate(products):
                        detail = detail_results[p_idx]
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

                prev_total = csv_out.count
                csv_out.add(products, url)
                new_count = csv_out.count - prev_total
                log.info("  Page %d: %d products, %d new (total: %d)", pg, len(products), new_count, csv_out.count)

                if args.limit > 0 and csv_out.count >= args.limit:
                    log.info("  Reached product limit (%d). Stopping.", args.limit)
                    break

                if new_count == 0 and pg > 2:
                    log.info("  No new products — done with this URL.")
                    break

                # --- Navigate to next page ---
                # Check if the main tab is still on the results page.
                # CAPTCHA or redirects during parallel scraping can move it.
                on_results = False
                try:
                    has_items = tab.query_selector("a[href*='/item/']")
                    on_results = has_items is not None and not is_captcha(tab)
                except Exception:
                    pass

                if not on_results:
                    # Main tab lost its position — handle CAPTCHA if needed
                    handle_captcha(tab)
                    # Navigate back to the results page we were on
                    log.info("    Returning to search results (page %d)...", pg)
                    # Try browser back first (preserves store page state)
                    recovered = False
                    try:
                        for _ in range(10):
                            tab.go_back(wait_until="domcontentloaded", timeout=10000)
                            handle_captcha(tab)
                            has_items = tab.query_selector("a[href*='/item/']")
                            if has_items and not is_captcha(tab):
                                recovered = True
                                break
                    except Exception:
                        pass
                    if not recovered:
                        # Fallback: navigate to URL directly
                        current_page_url = sort_by_orders(url)
                        if pg > 1:
                            parsed = urlparse(current_page_url)
                            qs = parse_qs(parsed.query, keep_blank_values=True)
                            qs["page"] = [str(pg)]
                            current_page_url = urlunparse(parsed._replace(query=urlencode(qs, doseq=True)))
                        try:
                            tab.goto(current_page_url, wait_until="domcontentloaded", timeout=30000)
                            wait_ready(tab, current_page_url)
                        except Exception:
                            pass

                # Scroll to bottom so pagination buttons are visible
                try:
                    tab.evaluate("window.scrollTo(0, document.body.scrollHeight)")
                    tab.wait_for_timeout(300)
                except Exception:
                    pass

                pg += 1
                log.info("  Navigating to page %d...", pg)
                if click_next(tab, pg):
                    try:
                        tab.wait_for_selector("a[href*='/item/']", timeout=8000)
                    except Exception:
                        pass
                else:
                    # Fallback: try direct URL navigation (works for search pages)
                    log.info("  click_next failed, trying direct URL...")
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

                time.sleep(random.uniform(0.1, 0.3))

            if args.limit > 0 and csv_out.count >= args.limit:
                break

        try:
            context.close()
            browser.close()
        except Exception:
            pass

    csv_out.close()
    log.info("Done! %d products -> %s", csv_out.count, out)

    # Post-process
    post_process(out)


if __name__ == "__main__":
    main()
