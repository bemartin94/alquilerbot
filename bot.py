#!/usr/bin/env python3
"""
Apartment alert bot — scrapes ZonaProp + ArgenProp every 10 minutes
and sends a Telegram message for each new listing found.

Alerts are configured in alerts.json (same directory as this file).
Each alert entry may have a "zonaprop_url" and/or "argenprop_url".
Add as many alert objects as you like; each runs on every cycle.
"""
import html as html_mod
import json
import logging
import os
import re
import time
from pathlib import Path

import requests
import cloudscraper
from bs4 import BeautifulSoup
from playwright.sync_api import sync_playwright

# ── Config ────────────────────────────────────────────────────────────────────
TELEGRAM_TOKEN   = os.environ.get("TELEGRAM_TOKEN", "")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID", "")
INTERVAL_MINUTES = 10

ALERTS_FILE = Path(__file__).parent / "alerts.json"
SEEN_FILE   = Path(__file__).parent / "seen.json"


def load_sources() -> list[dict]:
    """Build the flat SOURCES list from alerts.json."""
    if not ALERTS_FILE.exists():
        raise FileNotFoundError(f"No se encontró {ALERTS_FILE}. Creá ese archivo con tus alertas.")
    alerts = json.loads(ALERTS_FILE.read_text(encoding="utf-8"))
    sources = []
    for alert in alerts:
        label = alert.get("name", "Alerta")
        for zp_url in alert.get("zonaprop_urls", []):
            sources.append({
                "name": f"ZonaProp · {label}",
                "emoji": "🟠",
                "url": zp_url,
                "scraper": "zonaprop",
                "referer": "https://www.zonaprop.com.ar/",
            })
        for ap_url in alert.get("argenprop_urls", []):
            sources.append({
                "name": f"ArgenProp · {label}",
                "emoji": "🔵",
                "url": ap_url,
                "scraper": "argenprop",
                "referer": "https://www.argenprop.com/",
            })
        for ml_url in alert.get("mercadolibre_urls", []):
            sources.append({
                "name": f"MercadoLibre · {label}",
                "emoji": "🟡",
                "url": ml_url.split("#")[0],  # los fragmentos (#...) son solo client-side
                "scraper": "mercadolibre",
                "referer": "https://inmuebles.mercadolibre.com.ar/",
            })
    return sources

BASE_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/124.0.0.0 Safari/537.36"
    ),
    "Accept-Language": "es-AR,es;q=0.9",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
}

# ── Logging ───────────────────────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        logging.StreamHandler(),
        logging.FileHandler(Path(__file__).parent / "bot.log", encoding="utf-8"),
    ],
)
log = logging.getLogger(__name__)


# ── Persistence ───────────────────────────────────────────────────────────────
def load_seen() -> set:
    if SEEN_FILE.exists():
        return set(json.loads(SEEN_FILE.read_text(encoding="utf-8")))
    return set()


def save_seen(seen: set):
    SEEN_FILE.write_text(json.dumps(sorted(seen)), encoding="utf-8")


# ── Telegram ──────────────────────────────────────────────────────────────────
def send_message(text: str):
    api_url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
    try:
        r = requests.post(
            api_url,
            json={"chat_id": TELEGRAM_CHAT_ID, "text": text, "parse_mode": "HTML"},
            timeout=15,
        )
        if not r.ok:
            log.error("Telegram error %s: %s", r.status_code, r.text)
        else:
            log.info("Telegram OK (chat_id=%s)", TELEGRAM_CHAT_ID)
        r.raise_for_status()
    except Exception as e:
        log.error("Telegram error: %s", e)


# ── HTTP helper ───────────────────────────────────────────────────────────────
def fetch(url: str, referer: str, use_cloudscraper: bool = False) -> BeautifulSoup | None:
    try:
        if use_cloudscraper:
            session = cloudscraper.create_scraper(browser={"browser": "chrome", "platform": "windows"})
        else:
            session = requests.Session()
        session.headers.update({**BASE_HEADERS, "Referer": referer})
        resp = session.get(url, timeout=30)
        resp.raise_for_status()
        resp.encoding = "utf-8"
        return BeautifulSoup(resp.text, "lxml")
    except Exception as e:
        log.error("Fetch error (%s): %s", url, e)
        return None


# ── ZonaProp scraper ──────────────────────────────────────────────────────────
def scrape_zonaprop(source: dict) -> list[dict]:
    soup = fetch(source["url"], source["referer"])
    if not soup:
        return []

    results = []
    for card in soup.select("div[data-id]"):
        listing_id = card.get("data-id", "").strip()
        if not listing_id:
            continue

        address  = _text(card, "[class*='location-address']")
        price    = _text(card, "h2[class*='postingPrices-module__price']")
        expenses = _text(card, "[class*='expenses']")
        features = _text(card, "[class*='posting-main-features-block']", sep=" · ")

        link_el = card.select_one("a[href*='propiedades']")
        if link_el:
            path = link_el.get("href", "").split("?")[0]
            link = f"https://www.zonaprop.com.ar{path}" if path.startswith("/") else path
        else:
            link = f"https://www.zonaprop.com.ar/propiedades/clasificado/{listing_id}.html"

        results.append(_listing(f"zp_{listing_id}", address, price, expenses, features, link))

    log.info("[ZonaProp] %d listings scraped", len(results))
    return results


# ── MercadoLibre scraper ──────────────────────────────────────────────────────
def scrape_mercadolibre(source: dict) -> list[dict]:
    soup = fetch(source["url"], source["referer"])
    if not soup:
        return []

    results = []
    for item in soup.select("li.ui-search-layout__item"):
        link_el = (
            item.select_one("a.poly-component__title")
            or item.select_one("a.ui-search-link")
        )
        if not link_el:
            continue

        href = link_el.get("href", "").split("?")[0].split("#")[0]
        m = re.search(r"MLA-?(\d+)", href)
        if not m:
            continue
        listing_id = m.group(1)

        title    = _clean(link_el.get_text(" ", strip=True))
        loc_el   = item.select_one("span.poly-component__location")
        address  = _clean(loc_el.get_text(strip=True)) if loc_el else title

        cur_el   = item.select_one("span.andes-money-amount__currency-symbol")
        frac_el  = item.select_one("span.andes-money-amount__fraction")
        if frac_el:
            cur   = _clean(cur_el.get_text(strip=True)) if cur_el else "$"
            price = f"{cur} {_clean(frac_el.get_text(strip=True))}"
        else:
            price = ""

        features = " · ".join(
            _clean(a.get_text(strip=True))
            for a in item.select("li.poly-attributes-list__item")
            if a.get_text(strip=True)
        )

        results.append(_listing(f"ml_{listing_id}", address, price, "", features, href))

    log.info("[MercadoLibre] %d listings scraped", len(results))
    return results


# ── ArgenProp scraper ─────────────────────────────────────────────────────────
def _fetch_with_browser(url: str) -> BeautifulSoup | None:
    try:
        with sync_playwright() as p:
            browser = p.chromium.launch(headless=True)
            ctx  = browser.new_context(
                user_agent=BASE_HEADERS["User-Agent"],
                locale="es-AR",
            )
            page = ctx.new_page()
            page.goto(url, wait_until="domcontentloaded", timeout=30_000)
            content = page.content()
            browser.close()
        return BeautifulSoup(content, "lxml")
    except Exception as e:
        log.error("Browser fetch error (%s): %s", url, e)
        return None


def scrape_argenprop(source: dict) -> list[dict]:
    soup = _fetch_with_browser(source["url"])
    if not soup:
        return []

    results = []
    for item in soup.select("div.listing__item"):
        link_el = item.select_one("a.card[href]")
        if not link_el:
            continue

        href = link_el.get("href", "")
        # ID is the number at the end of the slug, e.g. "--19612650"
        m = re.search(r"--(\d+)$", href)
        if not m:
            continue
        listing_id = m.group(1)

        address  = _text(link_el, "p.card__address")
        features = _text(link_el, "ul.card__main-features", sep=" · ")

        # Price: full p.card__price text minus the expenses span
        price_el    = link_el.select_one("p.card__price")
        expenses_el = link_el.select_one("span.card__expenses")
        expenses = _clean(expenses_el.get_text(" ", strip=True)).lstrip("+ ") if expenses_el else ""
        if price_el:
            # Collect text from all children except the expenses span
            parts = []
            for child in price_el.children:
                cls = " ".join(getattr(child, "attrs", {}).get("class") or [])
                if "expenses" in cls:
                    continue
                text = child.get_text(strip=True) if hasattr(child, "get_text") else str(child).strip()
                if text:
                    parts.append(text)
            price = _clean(" ".join(parts))
        else:
            price = ""

        link = f"https://www.argenprop.com{href}"
        results.append(_listing(f"ap_{listing_id}", address, price, expenses, features, link))

    log.info("[ArgenProp] %d listings scraped", len(results))
    return results


# ── Shared helpers ────────────────────────────────────────────────────────────
def _clean(text: str) -> str:
    """Decode HTML entities and collapse whitespace."""
    return re.sub(r"\s+", " ", html_mod.unescape(text)).strip()


def _text(el, selector: str, sep: str = " ") -> str:
    found = el.select_one(selector)
    return _clean(found.get_text(sep, strip=True)) if found else ""


def _listing(uid, address, price, expenses, features, link) -> dict:
    return {
        "id": uid,
        "address": address or "Sin dirección",
        "price": price,
        "expenses": expenses,
        "features": features,
        "link": link,
    }


def format_listing(listing: dict, source: dict) -> str:
    price_line = listing["price"]
    if listing["expenses"]:
        price_line += f"  +  {listing['expenses']}"

    return (
        f"{source['emoji']} <b>{source['name']}</b> — <b>{listing['address']}</b>\n"
        f"💰 {price_line}\n"
        f"📐 {listing['features']}\n"
        f'🔗 <a href="{listing["link"]}">Ver publicación</a>'
    )


# ── Main loop ─────────────────────────────────────────────────────────────────
SCRAPERS = {
    "zonaprop":      scrape_zonaprop,
    "argenprop":     scrape_argenprop,
    "mercadolibre":  scrape_mercadolibre,
}


def check():
    seen = load_seen()
    total_new = 0

    for source in load_sources():
        scraper_fn = SCRAPERS[source["scraper"]]
        listings   = scraper_fn(source)

        if not listings:
            log.warning("[%s] No listings — possible block or page change", source["name"])
            continue

        new = [l for l in listings if l["id"] not in seen]
        log.info("[%s] %d new listing(s)", source["name"], len(new))

        for l in new:
            send_message(format_listing(l, source))
            seen.add(l["id"])
            time.sleep(0.4)

        total_new += len(new)

    save_seen(seen)
    log.info("Cycle done — %d new total", total_new)



def main():
    import sys
    once = "--once" in sys.argv

    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        print(
            "\nERROR: Faltan variables de entorno.\n"
            "Configuralas antes de correr el bot:\n\n"
            "  CMD de Windows:\n"
            "    set TELEGRAM_TOKEN=123456:ABCdef...\n"
            "    set TELEGRAM_CHAT_ID=987654321\n\n"
            "  PowerShell:\n"
            "    $env:TELEGRAM_TOKEN='123456:ABCdef...'\n"
            "    $env:TELEGRAM_CHAT_ID='987654321'\n"
        )
        return

    if once:
        check()
        return

    sources = load_sources()
    alert_names = "\n".join(f"  • {s['name']}" for s in sources)
    log.info("Bot iniciado con %d fuente(s). Chequeando cada %d minutos.", len(sources), INTERVAL_MINUTES)
    send_message(
        "✅ <b>Bot de departamentos iniciado</b>\n"
        f"📡 Alertas activas:\n{alert_names}\n"
        f"⏱ Chequeo cada {INTERVAL_MINUTES} minutos."
    )

    while True:
        check()
        log.info("Durmiendo %d minutos…", INTERVAL_MINUTES)
        time.sleep(INTERVAL_MINUTES * 60)


if __name__ == "__main__":
    main()
