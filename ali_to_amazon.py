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
HANDLING_DAYS = 8
QUANTITY = 5
MAX_PAGES = 5
MAX_IMAGES = 9                  # Amazon allows main + 8 other images

# ---- SMART PRICING CONFIG ----
TARGET_PROFIT_MARGIN = 0.30
AMAZON_REFERRAL_FEE = 0.1545
AMAZON_PER_ITEM_FEE = 0.75
USD_TO_GBP = 0.79
ALI_SHIPPING_ESTIMATE = 2.00
MIN_SELL_PRICE = 5.99

# ---- IMAGE HOSTING ----
IMGBB_API_KEY = "dd9a3b6ab5cabf1a45a24736ffe29e42"

# Keywords for resin model filtering
RESIN_INCLUDE = [
    "resin", "model kit", "model figure", "figure kit", "garage kit",
    "gk kit", "unpainted", "unassembled", "1/6 scale", "1/8 scale",
    "1/10 scale", "1/12 scale", "1/24 scale", "1/35 scale",
    "statue kit", "bust kit", "diorama", "miniature figure",
    "scale model", "resin cast", "resin figure", "resin statue",
    "moc", "building block", "micro block", "brick set", "brick model",
    "nano block", "diamond block", "mini block", "architecture model",
    "military model", "tank model", "ship model", "airplane model",
    "car model kit", "gundam", "mecha", "robot model",
]

RESIN_EXCLUDE = [
    "phone case", "screen protector", "earphone", "headphone",
    "charger", "cable", "adapter", "usb", "bluetooth",
    "clothing", "shirt", "dress", "pants", "shoe", "sock",
    "food", "snack", "drink", "supplement", "vitamin",
    "cosmetic", "makeup", "skincare", "perfume", "shampoo",
    "pet food", "dog food", "cat food",
    "sticker", "decal only", "poster", "wall art",
    "silicone mold", "silicone mould", "candle mold",
    "jewelry mold", "epoxy mold", "soap mold",
    "resin art supply", "resin pigment", "resin dye",
    "jeep", "ford", "toyota", "bmw", "mercedes", "audi",
    "ferrari", "lamborghini", "porsche", "tesla", "honda",
    "marvel", "disney", "star wars", "pokemon", "transformers",
    "warhammer", "games workshop", "bandai", "kotobukiya", "hasbro",
    "funko", "lego", "nike", "adidas", "supreme",
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
        tab.goto(product_url, wait_until="domcontentloaded", timeout=20000)
        # Wait for images to load
        try:
            tab.wait_for_selector('img[src*="alicdn"]', timeout=5000)
        except Exception:
            pass
        time.sleep(1)  # Let lazy images load

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
                                          "slide to verify", "puzzle", "drag the slider"]):
                    return True
    except Exception:
        pass
    return False


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
            log.warning(">>> CAPTCHA detected! Solve it in the browser window. <<<")
            print("\a", flush=True)
            while is_captcha(tab):
                tab.wait_for_timeout(2000)
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
    const step = window.innerHeight;
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
    try:
        tab.evaluate(SCROLL_JS)
    except Exception:
        pass
    products = extract(tab)
    stale = 0
    while stale < 2:
        try:
            tab.evaluate("window.scrollTo(0, document.body.scrollHeight)")
            tab.wait_for_timeout(500)
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
        tab.wait_for_timeout(100)
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
            longest = max(w, h)
            if longest < 1000:
                scale = 1000 / longest
                img = img.resize((int(w * scale), int(h * scale)), Image.LANCZOS)
            if img.mode in ('RGBA', 'P', 'LA'):
                bg = Image.new('RGB', img.size, (255, 255, 255))
                if img.mode == 'P':
                    img = img.convert('RGBA')
                bg.paste(img, mask=img.split()[-1] if 'A' in img.mode else None)
                img = bg
            elif img.mode != 'RGB':
                img = img.convert('RGB')
            jpeg_buffer = BytesIO()
            img.save(jpeg_buffer, format='JPEG', quality=92)
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

    # Try imgbb first (reliable, Amazon-compatible)
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
            # Use display_url or image.url for DIRECT image link
            # data.url is the viewer page (HTML), not the image itself
            img_data = data.get("data", {})
            url = (img_data.get("display_url", "")
                   or img_data.get("image", {}).get("url", "")
                   or img_data.get("url", ""))
            if url:
                log.info(f"          [IMG] imgbb: {url}")
                return url
        log.warning(f"          [IMG] imgbb response: {resp.status_code} {resp.text[:200]}")
    except Exception as e:
        log.info(f"          [IMG] imgbb error: {e}")

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
    t = title.lower()
    for ex in RESIN_EXCLUDE:
        if ex in t:
            return False
    for inc in RESIN_INCLUDE:
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


def clean_title(title):
    """Clean title of all Amazon-prohibited phrases."""
    if not title:
        return "Model Kit"
    title = re.sub(r'[^\w\s\-\.,&\'\"/()\[\]]', ' ', title)
    # Remove ALL prohibited Amazon phrases (case insensitive)
    prohibited = [
        r'free\s*shipping', r'best\s*seller', r'hot\s*sale',
        r'new\s*arrival', r'wholesale', r'dropship\w*',
        r'cheap', r'lowest\s*price', r'factory\s*direct',
        r'top\s*selling', r'limited\s*time', r'special\s*offer',
        r'big\s*sale', r'clearance', r'on\s*sale', r'promotion',
        r'buy\s*\d+\s*get', r'aliexpress', r'ali\s*express',
        r'china\s*direct', r'from\s*china',
    ]
    for phrase in prohibited:
        title = re.sub(r'(?i)\b' + phrase + r'\b', '', title)
    title = re.sub(r'\s+', ' ', title).strip()
    if len(title) > 200:
        title = title[:197] + "..."
    if not title or len(title) < 3:
        title = "Model Kit"
    return title


def make_bullets(title):
    bullets = []
    text = title.lower()
    if "resin" in text:
        bullets.append("Resin model kit suitable for hobbyists and collectors")
    if "build" in text or "block" in text or "moc" in text:
        bullets.append("Building blocks set with detailed design")
    if any(w in text for w in ["1/6", "1/8", "1/10", "1/12", "1/24", "1/35", "scale"]):
        bullets.append("Scale model with detailed features")
    if "unpainted" in text or "unassembled" in text:
        bullets.append("Unpainted kit for experienced modellers")
    generic = [
        "Suitable for display or collection purposes",
        "Model kit for hobbyists",
        "Packaged securely for delivery",
        "Suitable for adults and older children",
        "Detailed design for model enthusiasts",
    ]
    for g in generic:
        if len(bullets) >= 5:
            break
        if g not in bullets:
            bullets.append(g)
    return bullets[:5]


def make_description(title):
    return (
        clean_title(title) + ". "
        "This item makes an excellent addition to any model collection or display. "
        "Carefully crafted with attention to detail. "
        "Perfect as a gift or for personal enjoyment. "
        "Please check the images for full product details and specifications."
    )


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
        title = clean_title(product.get("product_title", ""))
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
            c = col("condition_type")
            if c:
                ws.cell(row=row, column=c, value="New")
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
            c = col("list_price_with_tax")
            if c:
                ws.cell(row=row, column=c, value=sell_price)

            # Price GBP (UK) — also set on parent to avoid "Missing Offer"
            for field in col_map:
                if "our_price" in field and "a1f83g8c2aro7p" in field:
                    ws.cell(row=row, column=col_map[field], value=sell_price)
                    break
            c = col("business_price")
            if c:
                ws.cell(row=row, column=c, value=sell_price)

            # Fulfillment on parent too
            c = col("fulfillment_availability#1.fulfillment_channel_code")
            if c:
                ws.cell(row=row, column=c, value="DEFAULT")
            c = col("fulfillment_availability#1.quantity")
            if c:
                ws.cell(row=row, column=c, value=QUANTITY)
            c = col("fulfillment_availability#1.lead_time_to_ship_max_days")
            if c:
                ws.cell(row=row, column=c, value=HANDLING_DAYS)

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
                c = col("condition_type")
                if c:
                    ws.cell(row=row, column=c, value="New")
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

                # Price GBP (UK)
                for field in col_map:
                    if "our_price" in field and "a1f83g8c2aro7p" in field:
                        ws.cell(row=row, column=col_map[field], value=sell_price)
                        break
                c = col("list_price_with_tax")
                if c:
                    ws.cell(row=row, column=c, value=sell_price)
                c = col("business_price")
                if c:
                    ws.cell(row=row, column=c, value=sell_price)

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
            c = col("condition_type")
            if c:
                ws.cell(row=row, column=c, value="New")
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

            # Price GBP (UK)
            for field in col_map:
                if "our_price" in field and "a1f83g8c2aro7p" in field:
                    ws.cell(row=row, column=col_map[field], value=sell_price)
                    break
            c = col("list_price_with_tax")
            if c:
                ws.cell(row=row, column=c, value=sell_price)
            c = col("business_price")
            if c:
                ws.cell(row=row, column=c, value=sell_price)

            filled += 1

        if filled % 50 == 0:
            log.info("  Filled %d rows...", filled)

    # --- Output as tab-delimited text ---
    max_col = ws.max_column or 308
    row1_vals = []
    row2_vals = []
    row3_vals = []
    for c in range(1, max_col + 1):
        row1_vals.append(str(ws.cell(row=1, column=c).value or ""))
        row2_vals.append(str(ws.cell(row=2, column=c).value or ""))
        row3_vals.append(str(ws.cell(row=3, column=c).value or ""))

    data_rows = []
    for r in range(start_row, start_row + filled):
        row_data = []
        for c in range(1, max_col + 1):
            val = ws.cell(row=r, column=c).value
            row_data.append(str(val) if val is not None else "")
        data_rows.append(row_data)

    wb.close()

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_name = f"amazon_upload_{ts}.txt"
    with open(output_name, "w", encoding="utf-8") as f:
        f.write("\t".join(row1_vals) + "\n")
        f.write("\t".join(row2_vals) + "\n")
        f.write("\t".join(row3_vals) + "\n")
        for row_data in data_rows:
            f.write("\t".join(row_data) + "\n")

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

    with sync_playwright() as pw:
        browser = None
        context = None
        tab = None

        def ensure_browser():
            nonlocal browser, context, tab
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
            browser = pw.chromium.launch(
                headless=False,
                args=["--disable-blink-features=AutomationControlled"],
            )
            context = browser.new_context(
                viewport={"width": 1920, "height": 1080},
                locale="en-US",
            )
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
                            log.warning(">>> CAPTCHA detected! Solve it in the browser window. <<<")
                            print("\a", flush=True)
                            while is_captcha(tab):
                                tab.wait_for_timeout(2000)
                            log.info(">>> CAPTCHA solved! Reloading... <<<")
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

            pg = 1
            while pg <= MAX_PAGES:
                log.info("  Page %d", pg)
                wait_ready(tab, url)
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
                if not args.skip_details:
                    for p_idx, product in enumerate(products):
                        pid = product["id"]
                        product_url = product["product_url"]
                        log.info("    [%d/%d] Fetching details for %s...", p_idx + 1, len(products), pid)

                        # Check for CAPTCHA before each detail visit
                        if is_captcha(tab):
                            log.warning(">>> CAPTCHA detected! Solve it. <<<")
                            print("\a", flush=True)
                            while is_captcha(tab):
                                tab.wait_for_timeout(2000)

                        detail = scrape_product_detail(tab, product_url, pid)

                        # Store all images as pipe-separated
                        if detail["all_images"]:
                            product["product_images"] = "|".join(detail["all_images"])
                            # Update main image to first detail image if better
                            if not product["product_image"] or product["product_image"].startswith("//"):
                                product["product_image"] = detail["all_images"][0]

                        # Store variations as JSON
                        if detail["variations"]:
                            product["variations"] = json.dumps(detail["variations"])

                        # Update title if detail page has a better one
                        if detail["detail_title"] and len(detail["detail_title"]) > len(product.get("product_title", "")):
                            product["product_title"] = detail["detail_title"]

                        time.sleep(random.uniform(0.3, 0.8))

                    # Navigate back to search results page
                    log.info("    Returning to search results...")
                    try:
                        current_page_url = sort_by_orders(url)
                        if pg > 1:
                            parsed = urlparse(current_page_url)
                            qs = parse_qs(parsed.query, keep_blank_values=True)
                            qs["page"] = [str(pg)]
                            current_page_url = urlunparse(parsed._replace(query=urlencode(qs, doseq=True)))
                        tab.goto(current_page_url, wait_until="domcontentloaded", timeout=30000)
                        tab.wait_for_selector("a[href*='/item/']", timeout=5000)
                    except Exception:
                        pass

                prev_total = csv_out.count
                csv_out.add(products, url)
                new_count = csv_out.count - prev_total
                log.info("  Page %d: %d products, %d new (total: %d)", pg, len(products), new_count, csv_out.count)

                if args.limit > 0 and csv_out.count >= args.limit:
                    log.info("  Reached product limit (%d). Stopping.", args.limit)
                    break

                if new_count == 0 and pg > 1:
                    log.info("  No new products — done with this URL.")
                    break

                if not click_next(tab, pg):
                    log.info("  No next page — done.")
                    break

                try:
                    tab.wait_for_selector("a[href*='/item/']", timeout=5000)
                except Exception:
                    pass

                pg += 1
                time.sleep(random.uniform(0.2, 0.5))

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
