#!/usr/bin/env python3
"""
Multi-user apartment alert bot.
Users configure their search via natural language → Gemini interprets it.
Scrapes ZonaProp + MercadoLibre every 12 minutes per user.
Deploy on Fly.io (persistent process).
"""

import asyncio
import html as html_mod
import json
import logging
import os
import re
import time
import unicodedata
import uuid
from pathlib import Path

from aiohttp import web as aiohttp_web
from groq import AsyncGroq
import requests
from curl_cffi import requests as cffi_requests
from apscheduler.schedulers.asyncio import AsyncIOScheduler
from bs4 import BeautifulSoup
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup, WebAppInfo
from telegram.ext import (
    Application,
    PicklePersistence,
    CallbackQueryHandler,
    CommandHandler,
    ConversationHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

# ── Config ─────────────────────────────────────────────────────────────────────
TELEGRAM_TOKEN = os.environ["TELEGRAM_TOKEN"]
GROQ_API_KEY   = os.environ["GROQ_API_KEY"]
DATA_DIR       = Path(os.environ.get("DATA_DIR", Path(__file__).parent))
USERS_FILE     = DATA_DIR / "users.json"
WEB_APP_URL    = os.environ.get("WEB_APP_URL", "")  # e.g. https://alquilerbot.fly.dev
APP_DIR        = Path(__file__).parent

AWAITING_DESCRIPTION  = 1
AWAITING_CONFIRMATION = 2
AWAITING_MORE_ALERTS  = 3
AWAITING_EDIT_DESC    = 4
AWAITING_ZONE_CONFIRM = 5
AWAITING_TIPO         = 6
AWAITING_AMBIENTES    = 7
AWAITING_METROS       = 8
AWAITING_PRECIO       = 9
AWAITING_EXPENSAS     = 10
AWAITING_EXTRAS       = 11
AWAITING_EDIT_CHOICE  = 12
AWAITING_EDIT_FIELD   = 13

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger(__name__)

groq_client = AsyncGroq(api_key=GROQ_API_KEY)

BASE_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/124.0.0.0 Safari/537.36"
    ),
    "Accept-Language": "es-AR,es;q=0.9",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
}

_ELECTRIC_KEYWORDS = re.compile(
    r"\b(sin\s+gas|todo\s+el[eé]ctric[oa]|calefacci[oó]n\s+el[eé]ctric[oa]|"
    r"cocina\s+el[eé]ctric[oa]|no\s+tiene\s+gas|sin\s+gasoducto)\b",
    re.IGNORECASE,
)

# ── User storage ───────────────────────────────────────────────────────────────
def load_users() -> dict:
    if USERS_FILE.exists():
        return json.loads(USERS_FILE.read_text(encoding="utf-8"))
    return {}

def save_users(users: dict):
    USERS_FILE.write_text(
        json.dumps(users, indent=2, ensure_ascii=False), encoding="utf-8"
    )

# ── Scraping helpers ───────────────────────────────────────────────────────────
def _clean(text: str) -> str:
    return re.sub(r"\s+", " ", html_mod.unescape(text)).strip()

def _text(el, selector: str, sep: str = " ") -> str:
    found = el.select_one(selector)
    return _clean(found.get_text(sep, strip=True)) if found else ""

def _parse_price(text: str) -> int:
    digits = re.sub(r"[^\d]", "", text)
    return int(digits) if digits else 0

_AGE_RE = re.compile(
    r"(\d+)\s*(hora|día|dia|semana|mes|año|ano)",
    re.IGNORECASE,
)

def _days_ago(text: str) -> int | None:
    """Parse ZonaProp date strings → integer days ago, or None if unparseable."""
    if not text:
        return None
    t = text.lower()
    if "hoy" in t or "hora" in t:
        return 0
    m = _AGE_RE.search(t)
    if not m:
        return None  # unknown — don't filter out
    n, unit = int(m.group(1)), m.group(2).lower()
    if "día" in unit or "dia" in unit:
        return n
    if "semana" in unit:
        return n * 7
    if "mes" in unit:
        return n * 30
    if "año" in unit or "ano" in unit:
        return n * 365
    return None

def _listing(uid, address, price, expenses, features, link, days_ago=None) -> dict:
    return {
        "id": uid,
        "address": address or "Sin dirección",
        "price": price,
        "expenses": expenses,
        "features": features,
        "link": link,
        "days_ago": days_ago,
    }

# Cloudflare on Fly IPs rejects some profiles intermittently; sessions keep the clearance cookies once one passes.
_IMPERSONATE = ("chrome131", "chrome124")  # max 2 tries per cycle: bursts are what trigger blocks
_sessions: dict = {}

def _session(imp: str):
    if imp not in _sessions:
        _sessions[imp] = cffi_requests.Session(impersonate=imp)
    return _sessions[imp]

def fetch(url: str, referer: str) -> BeautifulSoup | None:
    for imp in _IMPERSONATE:
        try:
            resp = _session(imp).get(url, headers={"Referer": referer}, timeout=30)
            if resp.status_code == 200:
                return BeautifulSoup(resp.content, "lxml", from_encoding="utf-8")
            log.warning("Fetch %s (%s): HTTP %s", url, imp, resp.status_code)
            if resp.headers.get("x-amzn-waf-action"):
                break  # AWS WAF challenge: retrying with another profile only extends the block
        except Exception as e:
            log.warning("Fetch %s (%s): %s", url, imp, e)
    log.error("Fetch error (%s): all profiles failed", url)
    return None

def scrape_zonaprop(url: str) -> list[dict]:
    soup = fetch(url, "https://www.zonaprop.com.ar/")
    if not soup:
        return []
    results = []
    for card in soup.select("div[data-id]"):
        listing_id = card.get("data-id", "").strip()
        if not listing_id:
            continue
        street   = _text(card, "[class*='location-address']")
        hood     = _text(card, "[class*='location-text']").split(",")[0].strip()
        address  = f"{street}, {hood}" if hood else street
        price    = _text(card, "h2[class*='postingPrices-module__price']")
        expenses = _text(card, "[class*='expenses']")
        features = _text(card, "[class*='posting-main-features-block']", sep=" · ")
        pub_text = _text(card, "[class*='antiquity-date'], [class*='Antiquity'], [class*='posting-date']")
        link_el  = card.select_one("a[href*='propiedades']")
        if link_el:
            path = link_el.get("href", "").split("?")[0]
            link = f"https://www.zonaprop.com.ar{path}" if path.startswith("/") else path
        else:
            link = f"https://www.zonaprop.com.ar/propiedades/clasificado/{listing_id}.html"
        results.append(_listing(f"zp_{listing_id}", address, price, expenses, features, link, _days_ago(pub_text)))
    log.info("[ZonaProp] %d listings", len(results))
    return results

def scrape_mercadolibre(url: str) -> list[dict]:
    soup = fetch(url.split("#")[0], "https://inmuebles.mercadolibre.com.ar/")
    if not soup:
        return []
    results = []
    for item in soup.select("li.ui-search-layout__item"):
        link_el = item.select_one("a.poly-component__title") or item.select_one("a.ui-search-link")
        if not link_el:
            continue
        href = link_el.get("href", "").split("?")[0].split("#")[0]
        m = re.search(r"MLA-?(\d+)", href)
        if not m:
            continue
        listing_id = m.group(1)
        loc_el    = item.select_one("span.poly-component__location")
        loc_raw   = _clean(loc_el.get_text(strip=True)) if loc_el else ""
        loc_parts = [p.strip() for p in loc_raw.split(",")]
        address   = ", ".join(loc_parts[:-1]) if len(loc_parts) > 2 else loc_raw
        cur_el    = item.select_one("span.andes-money-amount__currency-symbol")
        frac_el   = item.select_one("span.andes-money-amount__fraction")
        if frac_el:
            cur   = _clean(cur_el.get_text(strip=True)) if cur_el else "$"
            price = f"{cur} {_clean(frac_el.get_text(strip=True))}"
        else:
            price = ""
        features = " · ".join(
            _clean(a.get_text(strip=True))
            for a in item.select("li.poly-attributes_list__item")
            if a.get_text(strip=True)
        )
        pub_el   = item.select_one("[class*='poly-component__highlights']") or item.select_one("time")
        pub_text = _clean(pub_el.get_text(strip=True)) if pub_el else ""
        results.append(_listing(f"ml_{listing_id}", address, price, "", features, href, _days_ago(pub_text)))
    log.info("[MercadoLibre] %d listings", len(results))
    return results

# ── Remax (JSON API; no location filter that works, so filter barrios client-side) ──
REMAX_API   = "https://api-ar.redremax.com/remaxweb-ar/api/listings/findAllWithEntrepreneurships"
REMAX_TYPES = {"departamento": "1,2,3,4,5,6,7,8", "casa": "9,10,11", "ph": "12"}
_usd_rate   = {"value": 0, "ts": 0.0}

def _norm(s: str) -> str:
    return unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode().lower().strip()

def usd_ars_rate() -> int:
    if time.time() - _usd_rate["ts"] < 3600 and _usd_rate["value"]:
        return _usd_rate["value"]
    try:
        r = requests.get("https://dolarapi.com/v1/dolares/oficial", timeout=10)
        _usd_rate.update(value=int(r.json()["venta"]), ts=time.time())
    except Exception as e:
        log.warning("Dollar rate fetch failed: %s", e)
    return _usd_rate["value"]

def remax_params(alert: dict, user: dict) -> dict:
    """Barrios/tipos/ambientes for Remax; older alerts lack these fields, so derive from ZonaProp URL / user zones."""
    zp = " ".join(alert.get("zonaprop_urls", []))
    tipos = alert.get("tipos") or [t for t, slug in
                                   (("departamento", "departamentos"), ("ph", "ph"), ("casa", "casas"))
                                   if re.search(rf"[/-]{slug}[-]", zp)] or list(REMAX_TYPES)
    m = re.search(r"desde-(\d+)-hasta-(\d+)-ambientes", zp)
    return {
        "barrios": alert.get("barrios") or user.get("zones") or [],
        "tipos":   tipos,
        "min_amb": alert.get("min_ambientes") or (int(m.group(1)) if m else 0),
        "max_amb": alert.get("max_ambientes") or (int(m.group(2)) if m else 0),
    }

def scrape_remax(alert: dict, params: dict) -> list[dict]:
    barrios = [_norm(b) for b in params["barrios"]]
    if not barrios:
        return []
    type_ids = ",".join(REMAX_TYPES[t] for t in params["tipos"] if t in REMAX_TYPES)
    min_p = alert.get("min_price", 200000)
    max_p = alert.get("max_rent_price") or alert.get("max_total_price") or 10**9
    rate  = usd_ars_rate()

    queries = [("2", min_p, max_p, 2)]
    if rate:
        queries.append(("1", min_p // rate, max_p // rate + 1, 1))

    raw = []
    for currency_id, lo, hi, pages in queries:
        for page in range(pages):
            url = (f"{REMAX_API}?page={page}&pageSize=100&sort=-createdAt&in=operationId:2"
                   f"&in=typeId:{type_ids}&eq=currencyId:{currency_id}&gte=price:{lo}&lte=price:{hi}")
            try:
                resp = cffi_requests.get(url, impersonate="chrome124", timeout=30)
                raw += resp.json()["data"]["data"]
            except Exception as e:
                log.warning("[Remax] fetch failed (%s): %s", url, e)
                break

    results = []
    for l in raw:
        geo = _norm(l.get("geoLabel") or "")
        if not ("capital federal" in geo or "buenos aires" in geo):
            continue
        place = geo.split(",")[0]
        if not any(b in place or place in b for b in barrios):
            continue
        rooms = l.get("totalRooms") or 0
        if params["min_amb"] and rooms and rooms < params["min_amb"]:
            continue
        if params["max_amb"] and rooms and rooms > params["max_amb"]:
            continue

        price = l.get("price") or 0
        usd_note = ""
        if (l.get("currency") or {}).get("value") == "USD":
            usd_note = f" · 💵 publicado en USD {price:,} (oficial ${rate:,})".replace(",", ".")
            price *= rate
        exp = l.get("expensesPrice") or 0
        m2  = l.get("dimensionCovered") or l.get("dimensionTotalBuilt")
        features = f"{rooms} amb." + (f" · {round(m2)} m² cubiertos" if m2 else "") + f" · {l.get('title', '')}{usd_note}"
        type_id = (l.get("type") or {}).get("id", 0)
        results.append({**_listing(
            f"rx_{l['id']}",
            f"{l.get('displayAddress', '')}, {l.get('geoLabel', '').split(',')[0]}",
            f"$ {int(price):,}".replace(",", "."),
            f"$ {int(exp):,}".replace(",", ".") if exp else "",
            features,
            f"https://www.remax.com.ar/listings/{l.get('slug', l['id'])}",
        ), "tipo": "PH" if type_id == 12 else "Casa" if type_id in (9, 10, 11) else "Depto"})
    log.info("[Remax] %d raw, %d in barrios", len(raw), len(results))
    return results

ARGENPROP_SLUG_FIXES = {"la-paternal": "paternal", "villa-gral-mitre": "villa-general-mitre"}

def _argenprop_slug(barrio: str) -> str:
    s = re.sub(r"\bgral\b\.?", "general", _norm(barrio))
    s = re.sub(r"[^a-z0-9]+", "-", s).strip("-")
    return ARGENPROP_SLUG_FIXES.get(s, s)

def argenprop_url(alert: dict, params: dict) -> str | None:
    """New ArgenProp URL scheme: /{tipos}/alquiler/{barrios}/{ambientes}/pesos-{min}-{max}/orden-masnuevos"""
    if not params["barrios"]:
        return None
    tipo_slug = {"departamento": "departamentos", "ph": "ph", "casa": "casas"}
    tipos    = "-o-".join(sorted(tipo_slug[t] for t in params["tipos"] if t in tipo_slug)) or "departamentos"
    barrios  = "-o-".join(sorted({_argenprop_slug(b) for b in params["barrios"]}))
    parts    = [tipos, "alquiler", barrios]
    if params["max_amb"]:
        amb = range(max(params["min_amb"], 1), min(params["max_amb"], 5) + 1)
        parts.append("-o-".join("monoambiente" if n == 1 else f"{n}-ambientes" for n in amb))
    max_p = alert.get("max_rent_price") or alert.get("max_total_price")
    if max_p:
        parts.append(f"pesos-{alert.get('min_price', 0)}-{max_p}")
    parts.append("orden-masnuevos")
    return "https://www.argenprop.com/" + "/".join(parts)

# One page per cycle: more requests trip ArgenProp's AWS WAF rate rule on Fly's IP.
def scrape_argenprop(url: str, pages: int = 1) -> list[dict]:
    results = []
    for page in range(1, pages + 1):
        soup = fetch(url + (f"?pagina-{page}" if page > 1 else ""), "https://www.argenprop.com/")
        if not soup:
            break
        cards = soup.select("div.listing__item")
        if not cards:
            break
        results += _parse_argenprop_cards(cards)
    log.info("[ArgenProp] %d listings", len(results))
    return results

def _parse_argenprop_cards(cards) -> list[dict]:
    results = []
    for card in cards:
        link_el = card.select_one("a[href]")
        if not link_el:
            continue
        href = link_el.get("href", "")
        if not href.startswith("http"):
            href = "https://www.argenprop.com" + href
        uid = card.get("id") or re.sub(r"[^a-z0-9]", "_", href.split("/")[-1].lower())[:40]
        address  = _text(card, ".card__address, .listing__address, [class*='address']")
        hood     = _text(card, ".card__location, .listing__location, [class*='location']").split(",")[0].strip()
        if hood and hood.lower() not in address.lower():
            address = f"{address}, {hood}" if address else hood
        price    = _text(card, ".card__price, .listing__price, [class*='price']")
        expenses = _text(card, "[class*='expens'], [class*='expense']")
        features = " · ".join(
            _clean(li.get_text(strip=True))
            for li in card.select(".card__main-features li, .card__details li, .listing__details li")
            if li.get_text(strip=True)
        )
        exp_amount = _parse_price(expenses)
        expenses = f"$ {exp_amount:,}".replace(",", ".") if exp_amount else ""
        title = _text(card, ".card__title")
        if title:
            features = f"{features} · {title}" if features else title
        if not price:
            continue
        pub_text = _text(card, "[class*='date'], [class*='time'], [class*='fecha'], [class*='publicad']")
        results.append(_listing(f"ap_{uid}", address, price, expenses, features, href, _days_ago(pub_text)))
    return results

def fetch_ml_expenses(url: str) -> str:
    soup = fetch(url, "https://inmuebles.mercadolibre.com.ar/")
    if not soup:
        return ""
    for row in soup.select("tr"):
        header = row.select_one("th")
        value  = row.select_one("td")
        if header and value and "expensa" in header.get_text(strip=True).lower():
            val = _clean(value.get_text(strip=True))
            if val and val not in ("0 ARS", "0"):
                return val
    return ""

_RESERVED = re.compile(r'\breservad[oa]\b', re.IGNORECASE)

def _matches_exclude(text: str, rules: list) -> bool:
    """Return True if text matches any exclusion rule.
    Each rule is either:
      - a string  → excluded if that string appears
      - a list    → excluded only if ALL strings in the list appear (AND logic)
    Rules are combined with OR.
    """
    for rule in rules:
        if isinstance(rule, list):
            if all(kw.lower() in text for kw in rule):
                return True
        else:
            if rule.lower() in text:
                return True
    return False

MAX_LISTING_AGE_DAYS = 14

def filter_listings(listings: list, alert: dict) -> list:
    min_p    = alert.get("min_price", 200000)
    max_t    = alert.get("max_total_price", 0)
    max_r    = alert.get("max_rent_price", 0)
    min_m2   = alert.get("min_m2", 0)
    required = [kw.lower() for kw in alert.get("require_keywords", [])]
    excluded = [kw.lower() for kw in alert.get("exclude_keywords", [])]
    out = []
    for l in listings:
        # Date filter: skip listings older than MAX_LISTING_AGE_DAYS
        age = l.get("days_ago")
        if age is not None and age > MAX_LISTING_AGE_DAYS:
            continue

        rent = _parse_price(l["price"])
        if rent < min_p:
            continue
        if max_r and rent > max_r:
            continue

        # m2 filter: parse from features text if min_m2 is set
        if min_m2:
            m2_match = re.search(r'(\d+)\s*m[²2]', l.get("features", ""), re.IGNORECASE)
            if m2_match and int(m2_match.group(1)) < min_m2:
                continue

        exp_parsed = _parse_price(l["expenses"])
        # If max_total is set and expenses aren't shown, estimate 25% of rent conservatively
        if max_t and not l["expenses"] and rent > 0:
            exp_parsed = int(rent * 0.25)
        total = rent + exp_parsed
        if max_t and total > max_t:
            continue
        # Reject "reservado" anywhere in the listing text
        text = f"{l['address']} {l['features']}".lower()
        if _RESERVED.search(text):
            continue
        if _ELECTRIC_KEYWORDS.search(text):
            continue
        if required and not any(kw in text for kw in required):
            continue
        if excluded and _matches_exclude(text, excluded):
            continue
        out.append(l)
    return out

def get_alerts(user: dict) -> list:
    """Returns list of alerts, migrating old flat config transparently."""
    if "alerts" in user:
        return user["alerts"]
    flat = {k: v for k, v in user.items() if k not in ("seen", "active")}
    if flat.get("zonaprop_urls") or flat.get("mercadolibre_urls"):
        return [flat]
    return []

def add_alert(chat_id: str, alert: dict):
    users = load_users()
    if chat_id not in users:
        users[chat_id] = {"active": True, "seen": [], "alerts": []}
    user = users[chat_id]
    # Migrate flat config to alerts array if needed
    if "alerts" not in user:
        old = {k: v for k, v in user.items() if k not in ("seen", "active")}
        user["alerts"] = [old] if (old.get("zonaprop_urls") or old.get("mercadolibre_urls")) else []
        for k in list(old.keys()):
            user.pop(k, None)
    alert.setdefault("_id", uuid.uuid4().hex[:8])
    user["alerts"].append(alert)
    user.setdefault("active", True)
    user.setdefault("seen", [])
    save_users(users)

TIPO_ICON = {"Depto": "🏢", "PH": "🏘️", "Casa": "🏠"}
_TIPO_CODES = {"ap": "Depto", "departamento": "Depto", "departamentos": "Depto",
               "ph": "PH", "ca": "Casa", "casa": "Casa", "casas": "Casa"}

def _infer_tipo(link: str, source_url: str = "") -> str:
    patterns = (
        (link,       r"/clasificado/alcl(ap|ca|ph)"),                     # ZonaProp
        (link,       r"argenprop\.com/(departamento|ph|casa)-"),          # ArgenProp
        (source_url, r"mercadolibre\.com\.ar/(departamentos|ph|casas)/"), # ML: from the search URL
    )
    for text, pat in patterns:
        m = re.search(pat, text or "")
        if m:
            return _TIPO_CODES[m.group(1)]
    return ""

def format_listing(l: dict) -> str:
    rent     = _parse_price(l["price"])
    expenses = _parse_price(l["expenses"])
    total    = rent + expenses
    price_line = l["price"]
    if l["expenses"]:
        price_line += f" + {l['expenses']} expensas = ${total:,.0f} total".replace(",", ".")
    else:
        price_line += " (expensas: no informadas)"
    tipo = l.get("tipo", "")
    header = f"{TIPO_ICON[tipo]} {tipo} · " if tipo in TIPO_ICON else ""
    return (
        f"{header}<b>{l['address']}</b>\n"
        f"{price_line}\n"
        f"{l['features']}\n"
        f'<a href="{l["link"]}">Ver publicación</a>'
    )

# ── Gemini ─────────────────────────────────────────────────────────────────────
GEMINI_PROMPT = """
Sos un asistente de búsqueda de departamentos en Argentina.
El usuario te describe qué está buscando. Interpretá su pedido y generá las URLs de búsqueda.
Devolvé SOLO un JSON válido, sin texto adicional ni bloques de código.

## Formato ZonaProp
https://www.zonaprop.com.ar/{tipos}-alquiler-{barrios}-{ambientes}-{m2}-{precio}-pesos-orden-publicado-descendente.html
- tipos: departamentos | casas | ph | casas-departamentos-ph (separados por -)
- barrios: nombres en minúscula con guiones, separados por - (ej: palermo-villa-crespo)
- ambientes: desde-1-hasta-3-ambientes (omitir si no se especifica)
- m2: mas-30-m2-cubiertos (omitir si no se especifica)
- precio: 200000-700000

Barrios CABA: palermo, villa-crespo, colegiales, belgrano, belgrano-r, nunez, saavedra, coghlan, villa-urquiza, villa-pueyrredon, villa-ortuzar, parque-chas, agronomia, la-paternal, chacarita, villa-del-parque, villa-devoto, caballito, boedo, recoleta
Barrios GBA: florida, vicente-lopez, martinez, olivos, san-isidro

## Formato ArgenProp
https://www.argenprop.com/{tipo}-alquiler-en-{barrio}--precio-desde-{min}-hasta-{max}

- tipo: departamento | ph | casa
- barrio: nombre en minúscula con guiones (ej: palermo, villa-crespo, villa-urquiza)
- precio en ARS

Ejemplo: https://www.argenprop.com/departamento-alquiler-en-palermo--precio-desde-200000-hasta-700000

Barrios CABA para ArgenProp: palermo, villa-crespo, colegiales, belgrano, nunez, saavedra, coghlan, villa-urquiza, villa-pueyrredon, villa-ortuzar, parque-chas, agronomia, la-paternal, chacarita, villa-del-parque, villa-devoto, florida

## Formato MercadoLibre
https://inmuebles.mercadolibre.com.ar/{tipo}/alquiler/{zona}/{barrios}/_PriceRange_{min}ARS-{max}ARS_NoIndex_True_TOTAL*AREA_{m2}m%C2%B2-*
- tipo: departamentos | ph | casas
- zona CABA: capital-federal
- zona GBA: bsas-gba-norte/vicente-lopez/florida (para Florida)
- barrios: nombreA-o-nombreB-o-nombreC
- m2: metros cuadrados mínimos (usá 30 si no se especifica)

Barrios CABA para ML: palermo, villa-crespo, colegiales, belgrano-r, nunez, saavedra, coghlan, villa-urquiza, villa-pueyrredon, villa-ortuzar, parque-chas, agronomia, paternal, chacarita, villa-devoto, parque-centenario

## Conversión de precios (MUY IMPORTANTE)
Primero convertí el precio mencionado a pesos ARS:
- "800k", "800K", "800.000", "800 mil" → 800000
- "1m", "1M", "1 millón", "1kk", "1.000.000" → 1000000
- "1.5m", "1,5m", "1.5M" → 1500000
- Número sin unidad bajo 10000 (ej: "1000") → multiplicar por 1000 → 1000000
- Número sin unidad entre 10000 y 9999999 → usarlo tal cual

Luego aplicá las reglas:
- `max_rent_price`: precio máximo de ALQUILER que se usa en las URLs de búsqueda
- `max_total_price`: precio máximo TOTAL (alquiler + expensas) usado para filtrar después

Casos:
1. "hasta 800k incluyendo expensas" / "todo incluido" / "en total" / "con expensas":
   → max_total_price = 800000, max_rent_price = 640000 (80%)

2. "hasta 800k de alquiler" / solo alquiler / sin aclaración:
   → max_rent_price = 800000, max_total_price = 960000 (120%)

3. No especifica: tratalo como caso 2.

- Las URLs SIEMPRE usan max_rent_price en el rango de precio
- min_price es SIEMPRE 200000
- Si el usuario no especifica tipo, usá departamentos, ph y casas
- Si no especifica m2 mínimo, usá 30

## Zona CABA completa
Si el usuario dice "CABA", "Capital Federal", "Ciudad de Buenos Aires" sin barrios específicos,
usá una lista amplia de barrios: palermo, villa-crespo, colegiales, belgrano, nunez, saavedra,
villa-urquiza, caballito, boedo, recoleta, almagro, flores, floresta, villa-del-parque,
villa-devoto, chacarita, paternal, parque-centenario, san-telmo, montserrat, puerto-madero
- Generá una URL de ZonaProp y una de ML por tipo de propiedad

## require_keywords
Si el usuario menciona características que deben estar presentes en la publicación, incluílas en `require_keywords`. El filtro busca que al menos UNA de esas palabras aparezca en la dirección o features del listado en los resultados de búsqueda.

IMPORTANTE — Solo agregá keywords que realmente aparecen en los cards de resultados de ZonaProp/MercadoLibre:
✅ SÍ agregar: balcón, terraza, cochera, patio, jardín, luminoso, amenities, pileta, "cocina separada"
❌ NO agregar: gas, eléctrico, inducción, calefacción, agua caliente — estos detalles NO aparecen en los cards de búsqueda, solo en la página interna del listado. Poner "gas" como require_keyword filtraría TODOS los resultados.

IMPORTANTE: Si un requisito es CONDICIONAL ("si es monoambiente que tenga X", "si fuera de 1 ambiente X"):
- Si la búsqueda es SOLO ese tipo (ej: solo monoambientes), agregá el requisito normalmente.
- Si la búsqueda incluye VARIOS tipos de ambientes, NO lo agregues.

Ejemplos:
- "que tenga balcón o patio" → require_keywords: ["balcon", "balcón", "patio", "terraza"]
- "con cochera" → require_keywords: ["cochera", "garage"]
- "cocina separada" → require_keywords: ["cocina separada", "cocina independiente"]
- "que tenga gas (no eléctrico)" → require_keywords: [] (no aparece en los cards — usá exclude_keywords para "eléctrico", "inducción")
- búsqueda: 1-3 ambientes + "si es monoambiente que tenga cocina separada" → require_keywords: []

## exclude_keywords
Si el usuario menciona características que NO quiere, usá `exclude_keywords`. Es una lista de reglas combinadas con OR. Cada regla puede ser:
- Un string: se excluye si ESA palabra/frase aparece en el listado.
- Un array de strings: se excluye solo si TODAS las frases del array aparecen juntas (AND).

Usá arrays para condiciones combinadas y así evitar falsos positivos.

Ejemplos:
- "no quiero laterales" → ["lateral"]
- "no quiero primer piso al frente" → [["primer piso", "al frente"], ["1° piso", "al frente"], ["piso 1", "al frente"]]
  ↳ Esto NO filtra "primer piso contrafrente" porque necesita "al frente" también presente.
- "no quiero primer piso" (sin importar orientación) → ["primer piso", "1° piso", "piso 1"]
- "sin monoambientes" → ["monoambiente"]
Dejá el array vacío si no hay exclusiones.

## Mensajes que NO son búsquedas
Si el mensaje del usuario NO describe una propiedad que quiere alquilar (por ejemplo: un saludo,
una pregunta sobre el bot, el nombre de un comando como "alertas" o "ayuda", o texto sin relación),
NO inventes una búsqueda. Devolvé exactamente: {"no_es_busqueda": true}

## Respuesta (SOLO JSON, nada más):
{
  "name": "nombre corto descriptivo de esta alerta (ej: Deptos 2amb Palermo)",
  "summary": "descripción clara en español de lo que entendiste",
  "zonaprop_urls": ["url1"],
  "argenprop_urls": ["url1"],
  "mercadolibre_urls": ["url1"],
  "min_price": 200000,
  "max_rent_price": 640000,
  "max_total_price": 800000,
  "min_m2": 30,
  "barrios": ["Villa Urquiza", "Saavedra"],
  "tipos": ["departamento", "ph", "casa"],
  "min_ambientes": 1,
  "max_ambientes": 3,
  "require_keywords": [],
  "exclude_keywords": []
}
`barrios`: nombres de barrio/localidad tal como se escriben normalmente (con tildes), uno por elemento.
`tipos`: subconjunto de ["departamento", "ph", "casa"].
`min_ambientes`/`max_ambientes`: rango de ambientes pedido (monoambiente = 1); 0 si no se especificó.
"""

async def interpret_search(description: str) -> dict | None:
    for attempt in range(2):
        try:
            resp = await groq_client.chat.completions.create(
                model="qwen/qwen3.8-27b",
                messages=[
                    {"role": "system", "content": GEMINI_PROMPT},
                    {"role": "user",   "content": f"Búsqueda del usuario: {description}"},
                ],
                temperature=0.2,
                max_tokens=4096,
            )
            text = resp.choices[0].message.content.strip()
            log.info("Groq raw (attempt %d): %s", attempt + 1, text[:200])
            text = re.sub(r"<think>.*?</think>", "", text, flags=re.DOTALL)
            text = re.sub(r"^```(?:json)?\s*", "", text.strip())
            text = re.sub(r"\s*```$", "", text)
            return json.loads(text.strip())
        except json.JSONDecodeError as e:
            log.error("Groq JSON parse error (attempt %d): %s | text: %s", attempt + 1, e, text[:300])
        except Exception as e:
            log.error("Groq error (attempt %d): %s", attempt + 1, e)
        if attempt == 0:
            await asyncio.sleep(1)
    return None

# ── Telegram handlers ──────────────────────────────────────────────────────────
async def cmd_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    return await cmd_buscar(update, ctx)

def _map_keyboard():
    return InlineKeyboardMarkup([[
        InlineKeyboardButton("🗺️ Elegir barrios en el mapa", web_app=WebAppInfo(url=f"{WEB_APP_URL}/map"))
    ]])

async def cmd_buscar(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    chat_id = str(update.effective_chat.id)
    users   = load_users()
    saved   = users.get(chat_id, {}).get("zones", [])

    if saved and WEB_APP_URL:
        lista = ", ".join(saved)
        keyboard = InlineKeyboardMarkup([[
            InlineKeyboardButton("✅ Sí, los mismos", callback_data="zones_keep"),
            InlineKeyboardButton("🗺️ Cambiar", web_app=WebAppInfo(url=f"{WEB_APP_URL}/map")),
        ]])
        await update.message.reply_text(
            f"Hola! La última vez buscaste en: <b>{lista}</b>\n\n¿Seguís buscando en esas zonas?",
            parse_mode="HTML",
            reply_markup=keyboard,
        )
        return AWAITING_ZONE_CONFIRM
    elif WEB_APP_URL:
        await update.message.reply_text(
            "Hola! ¿En qué zona de Buenos Aires estás buscando?",
            reply_markup=_map_keyboard(),
        )
        return AWAITING_ZONE_CONFIRM
    else:
        await update.message.reply_text("Hola! ¿Qué estás buscando? Contame barrios, tipo, tamaño y precio máximo:")
        return AWAITING_DESCRIPTION

async def handle_zone_confirm(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Handle zones_keep / zones_change callback buttons."""
    query   = update.callback_query
    chat_id = str(query.from_user.id)
    await query.answer()
    if query.data == "zones_keep":
        users  = load_users()
        saved  = users.get(chat_id, {}).get("zones", [])
        ctx.user_data["barrios_mapa"] = saved
        await query.edit_message_text(
            f"Zonas: <b>{', '.join(saved)}</b>", parse_mode="HTML",
        )
        return await _start_wizard(query.message, ctx)

def _find_alert_idx(alerts: list, aid: str) -> int:
    """Return 0-based index of alert with _id==aid, or positional if aid is numeric."""
    for i, a in enumerate(alerts):
        if a.get("_id") == aid:
            return i
    # fallback: numeric position (old alerts without _id)
    if aid.isdigit():
        idx = int(aid) - 1
        if 0 <= idx < len(alerts):
            return idx
    return -1

async def handle_alert_del_button(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Handle inline 🗑️ Borrar button from /alertas."""
    query   = update.callback_query
    chat_id = str(query.from_user.id)
    await query.answer()
    aid = query.data.split(":", 1)[1]

    users  = load_users()
    user   = users.get(chat_id)
    alerts = get_alerts(user) if user else []
    idx    = _find_alert_idx(alerts, aid)

    if idx < 0:
        await query.edit_message_text("⚠️ Esa alerta ya no existe.")
        return

    removed = alerts.pop(idx)
    if "alerts" not in user:
        user["alerts"] = alerts
    save_users(users)
    name = removed.get("name") or removed.get("summary", f"Alerta {idx+1}")
    await query.edit_message_text(f"🗑️ <i>Alerta eliminada: {name}</i>", parse_mode="HTML")

def _edit_menu_kb(aid: str) -> InlineKeyboardMarkup:
    b = lambda label, key: InlineKeyboardButton(label, callback_data=f"ef_{key}:{aid}")
    return InlineKeyboardMarkup([
        [b("📐 Metros mínimos", "m2"),   b("💰 Presupuesto", "precio")],
        [b("🏢 Tipo propiedad", "tipo"), b("🛏️ Ambientes", "ambientes")],
        [b("📍 Zona", "zona"),           b("✨ Extras / keywords", "extras")],
        [b("❌ Cancelar", "cancel")],
    ])

async def _show_edit_menu(send_fn, alert: dict, idx: int):
    aid = alert.get("_id") or str(idx + 1)
    name = alert.get("name") or alert.get("summary", f"Alerta {idx+1}")
    lines = [f"✏️ <b>Editando alerta {idx+1}: {name}</b>", ""]
    if alert.get("min_m2"):
        lines.append(f"📐 Metros mín: {alert['min_m2']} m²")
    if alert.get("max_total_price"):
        lines.append(f"💰 Presupuesto máx total: ${alert['max_total_price']:,}")
    elif alert.get("max_rent_price"):
        lines.append(f"💰 Alquiler máx: ${alert['max_rent_price']:,}")
    if alert.get("require_keywords"):
        lines.append(f"✨ Extras: {', '.join(alert['require_keywords'])}")
    lines.append("\n¿Qué querés cambiar?")
    await send_fn("\n".join(lines), parse_mode="HTML", reply_markup=_edit_menu_kb(aid))

async def handle_alert_edit_button(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Handle inline ✏️ Editar button from /alertas — entry point into ConversationHandler."""
    query   = update.callback_query
    chat_id = str(query.from_user.id)
    await query.answer()
    aid = query.data.split(":", 1)[1]

    users  = load_users()
    user   = users.get(chat_id)
    alerts = get_alerts(user) if user else []
    idx    = _find_alert_idx(alerts, aid)

    if idx < 0:
        await query.edit_message_text("⚠️ Esa alerta ya no existe. Usá /alertas para ver las actuales.")
        return ConversationHandler.END

    ctx.user_data["editing_idx"] = idx
    await _show_edit_menu(
        lambda text, **kw: query.edit_message_text(text, **kw),
        alerts[idx], idx,
    )
    return AWAITING_EDIT_CHOICE

async def handle_web_app_data(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    data    = json.loads(update.effective_message.web_app_data.data)
    barrios = data.get("barrios", [])
    if not barrios:
        await update.message.reply_text(
            "No seleccionaste ningún barrio.",
            reply_markup=_map_keyboard() if WEB_APP_URL else None,
        )
        return AWAITING_ZONE_CONFIRM
    # Save zones at user level
    chat_id = str(update.effective_chat.id)
    users   = load_users()
    users.setdefault(chat_id, {"active": True, "seen": [], "alerts": []})
    users[chat_id]["zones"] = barrios
    save_users(users)
    ctx.user_data["barrios_mapa"] = barrios
    lista = ", ".join(barrios)
    await update.message.reply_text(f"Perfecto, <b>{lista}</b>.", parse_mode="HTML")
    return await _start_wizard(update.message, ctx)

async def cmd_stop(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    chat_id = str(update.effective_chat.id)
    users = load_users()
    if chat_id in users:
        users[chat_id]["active"] = False
        save_users(users)
        await update.message.reply_text("Alertas pausadas. Usá /buscar para reactivar.")
    else:
        await update.message.reply_text("No tenés alertas activas.")

async def cmd_alertas(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    chat_id = str(update.effective_chat.id)
    users   = load_users()
    user    = users.get(chat_id)
    alerts  = get_alerts(user) if user else []
    if not alerts:
        await update.message.reply_text("No tenés alertas configuradas. Enviame un mensaje para empezar.")
        return
    active = user.get("active", True)
    status = "activas" if active else "pausadas"
    await update.message.reply_text(f"Tus alertas ({status}):", parse_mode="HTML")
    for i, a in enumerate(alerts, 1):
        aid     = a.get("_id") or str(i)  # fallback to position for old alerts without _id
        name    = a.get("name") or a.get("summary", f"Alerta {i}")
        summary = a.get("summary", "")
        text    = f"<b>{i}. {name}</b>" + (f"\n{summary}" if summary and summary != name else "")
        kb = InlineKeyboardMarkup([[
            InlineKeyboardButton("✏️ Editar", callback_data=f"alert_edit:{aid}"),
            InlineKeyboardButton("🗑️ Borrar", callback_data=f"alert_del:{aid}"),
        ]])
        await update.message.reply_text(text, parse_mode="HTML", reply_markup=kb)
    await update.message.reply_text("Usá /buscar para agregar una nueva alerta.")

async def cmd_borrar(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    chat_id = str(update.effective_chat.id)
    args    = ctx.args
    users   = load_users()
    user    = users.get(chat_id)
    alerts  = get_alerts(user) if user else []
    if not args or not args[0].isdigit():
        await update.message.reply_text("Usá /borrar <número> (ej: /borrar 1). Usá /alertas para ver los números.")
        return
    idx = int(args[0]) - 1
    if idx < 0 or idx >= len(alerts):
        await update.message.reply_text(f"No existe la alerta {idx+1}. Usá /alertas para ver las disponibles.")
        return
    removed = alerts.pop(idx)
    if "alerts" not in user:
        user["alerts"] = alerts
    save_users(users)
    await update.message.reply_text(f"Alerta eliminada: {removed.get('name') or removed.get('summary','')}")

async def cmd_borrar_todo(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    chat_id = str(update.effective_chat.id)
    users   = load_users()
    user    = users.get(chat_id)
    if not user or not get_alerts(user):
        await update.message.reply_text("No tenés alertas configuradas.")
        return
    user["alerts"] = []
    save_users(users)
    await update.message.reply_text("Todas las alertas fueron eliminadas. Usá /buscar para agregar nuevas.")

async def cmd_resetseen(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    chat_id = str(update.effective_chat.id)
    users   = load_users()
    user    = users.get(chat_id)
    if not user:
        await update.message.reply_text("No tenés alertas configuradas.")
        return
    count = len(user.get("seen", []))
    user["seen"] = []
    save_users(users)
    await update.message.reply_text(
        f"Listo, se borraron {count} publicaciones del historial visto.\n"
        "Usá /buscar para ver todos los resultados de nuevo."
    )

COMMANDS_TEXT = (
    "Estos son los comandos disponibles:\n\n"
    "/buscar — crear o agregar una nueva alerta\n"
    "/alertas — ver, editar o borrar tus alertas\n"
    "/stop — pausar las notificaciones\n"
    "/resetseen — volver a ver publicaciones ya mostradas\n"
    "/borrartodo — eliminar todas las alertas\n"
    "/help — ver esta lista de comandos"
)

async def cmd_help(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(COMMANDS_TEXT)

async def fallback_unknown(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "No entendí eso. Si querés buscar departamentos usá /buscar.\n\n" + COMMANDS_TEXT
    )

# Palabras sueltas que coinciden con un comando (escritas sin la "/")
_COMMAND_WORDS = {
    "buscar": "buscar", "busqueda": "buscar", "nueva alerta": "buscar",
    "alertas": "alertas", "alerta": "alertas", "mis alertas": "alertas",
    "ver alertas": "alertas", "estado": "alertas",
    "stop": "stop", "pausar": "stop", "parar": "stop",
    "resetseen": "resetseen",
    "borrartodo": "borrartodo", "borrar todo": "borrartodo",
    "borrar": "alertas", "editar": "alertas",
}
# Mensajes que claramente no son una búsqueda
_NON_SEARCH_WORDS = {
    "help", "ayuda", "comandos", "comando", "menu", "opciones", "info",
    "start", "inicio", "hola", "holaa", "buenas", "buen dia", "buenos dias",
    "buenas tardes", "buenas noches", "hey", "hi", "hello",
    "gracias", "muchas gracias", "ok", "okey", "dale", "listo", "genial",
    "chau", "adios", "?", "que hago", "como funciona", "que podes hacer",
}

def _non_search_reply(text: str) -> str | None:
    """If `text` is not a property search (a command word without '/', a greeting,
    a help request...), return the reply listing the commands. Otherwise None."""
    t = _norm(text)
    t = re.sub(r"[^\w\s?]", " ", t)           # drop "/", "!", "¿", etc.
    t = re.sub(r"\s+", " ", t).strip()
    if not t:
        return COMMANDS_TEXT
    if t in _COMMAND_WORDS:
        return f"¿Quisiste decir /{_COMMAND_WORDS[t]}? Los comandos van con una barra «/» adelante.\n\n" + COMMANDS_TEXT
    if t in _NON_SEARCH_WORDS or t.rstrip("?! ") in _NON_SEARCH_WORDS:
        return COMMANDS_TEXT
    return None

async def _reply_non_search(update: Update, ctx: ContextTypes.DEFAULT_TYPE, reply: str):
    """Show the commands and leave the conversation so the next message starts fresh."""
    ctx.user_data.pop("pending", None)
    await update.message.reply_text(reply, parse_mode="HTML")
    return ConversationHandler.END

async def cmd_editar(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    chat_id = str(update.effective_chat.id)
    args    = ctx.args
    users   = load_users()
    user    = users.get(chat_id)
    alerts  = get_alerts(user) if user else []
    if not args or not args[0].isdigit():
        await update.message.reply_text("Usá /editar <número> (ej: /editar 1). Usá /alertas para ver los números.")
        return
    idx = int(args[0]) - 1
    if idx < 0 or idx >= len(alerts):
        await update.message.reply_text(f"No existe la alerta {idx+1}. Usá /alertas para ver las disponibles.")
        return
    ctx.user_data["editing_idx"] = idx
    await _show_edit_menu(update.message.reply_text, alerts[idx], idx)
    return AWAITING_EDIT_CHOICE

async def handle_edit_choice(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Handle field selection buttons in the edit menu."""
    query   = update.callback_query
    chat_id = str(query.from_user.id)
    await query.answer()
    data, _, aid = query.data.partition(":")

    if data == "ef_cancel":
        await query.edit_message_text("Edición cancelada.")
        return ConversationHandler.END

    users  = load_users()
    alerts = get_alerts(users.get(chat_id)) if users.get(chat_id) else []
    idx    = _find_alert_idx(alerts, aid) if aid else ctx.user_data.get("editing_idx", -1)
    if idx is None or idx < 0 or idx >= len(alerts):
        await query.edit_message_text("⚠️ Esa alerta ya no existe. Usá /alertas para ver las actuales.")
        return ConversationHandler.END
    ctx.user_data["editing_idx"] = idx

    field_prompts = {
        "ef_m2":        ("min_m2",           "¿Cuántos m² mínimo?\nEj: <b>35</b>, <b>40</b>"),
        "ef_precio":    ("max_total_price",   "¿Cuál es el nuevo presupuesto máximo <b>total</b> (alquiler + expensas)?\nEj: <b>800k</b>, <b>1.2M</b>"),
        "ef_extras":    ("require_keywords",  "¿Qué palabras clave necesitás? (separadas por coma, o <b>ninguna</b> para limpiar)\nEj: <b>cochera, balcón</b>"),
        "ef_tipo":      ("_tipo_nlp",         "¿Qué tipo de propiedad?\nEj: <b>departamento</b>, <b>casa</b>, <b>PH</b>, <b>cualquiera</b>"),
        "ef_ambientes": ("_ambientes_nlp",    "¿Cuántos ambientes?\nEj: <b>2</b>, <b>2 a 3</b>, <b>3+</b>, <b>monoambiente</b>"),
        "ef_zona":      ("_zona_nlp",         "¿En qué zona o barrios querés buscar?\nEj: <b>Palermo, Villa Crespo</b>, <b>zona norte GBA</b>"),
    }
    if data not in field_prompts:
        return ConversationHandler.END

    field, prompt = field_prompts[data]
    ctx.user_data["edit_field"] = field
    await query.edit_message_text(prompt, parse_mode="HTML")
    return AWAITING_EDIT_FIELD

async def handle_edit_field_value(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Handle the user's typed value for a specific field."""
    text    = update.message.text.strip()
    chat_id = str(update.effective_chat.id)
    field   = ctx.user_data.get("edit_field")
    idx     = ctx.user_data.get("editing_idx")

    users  = load_users()
    user   = users.get(chat_id)
    alerts = get_alerts(user) if user else []
    if not user or idx is None or idx >= len(alerts):
        await update.message.reply_text("Algo falló, intentá de nuevo con /editar.")
        return ConversationHandler.END

    alert = alerts[idx]

    # Simple numeric field: min_m2
    if field == "min_m2":
        m = re.search(r'\d+', text)
        if not m:
            await update.message.reply_text("No entendí el número. Escribí solo el valor, ej: <b>35</b>", parse_mode="HTML")
            return AWAITING_EDIT_FIELD
        alert["min_m2"] = int(m.group())
        save_users(users)
        await update.message.reply_text(f"Metros mínimos actualizado a <b>{alert['min_m2']} m²</b>.", parse_mode="HTML")
        return ConversationHandler.END

    # Price field: max_total_price
    if field == "max_total_price":
        # Parse "800k", "1.2M", "900000" → int
        raw = text.strip().replace(".", "").replace(",", "").replace(" ", "")
        m   = re.match(r'^(\d+(?:\.\d+)?)\s*([kmKM]?)$', text.strip().replace(",", "").replace(".", ""))
        # Try a more lenient parse
        num_match = re.search(r'(\d[\d\s\.]*)', text.replace(",", ""))
        num_str   = re.sub(r'\s', '', num_match.group(1)) if num_match else ""
        suffix    = re.search(r'[kmKM]', text, re.IGNORECASE)
        if not num_str:
            await update.message.reply_text("No entendí el precio. Escribí algo como <b>800k</b> o <b>1.2M</b>.", parse_mode="HTML")
            return AWAITING_EDIT_FIELD
        val = int(float(num_str))
        if suffix:
            s = suffix.group().lower()
            if s == "k":
                val *= 1000
            elif s == "m":
                val *= 1_000_000
        if val < 10_000:   # assume "thousands" if bare number
            val *= 1000
        alert["max_total_price"] = val
        alert["max_rent_price"]  = int(val * 0.8)
        save_users(users)
        await update.message.reply_text(f"Presupuesto máximo actualizado a <b>${val:,}</b>.", parse_mode="HTML")
        return ConversationHandler.END

    # Keywords field
    if field == "require_keywords":
        if text.lower() in ("ninguna", "ninguno", "no", "-", "nada"):
            alert["require_keywords"] = []
        else:
            alert["require_keywords"] = [k.strip() for k in re.split(r'[,;]', text) if k.strip()]
        save_users(users)
        kws = alert["require_keywords"]
        msg = f"Palabras clave actualizadas: <b>{', '.join(kws)}</b>." if kws else "Palabras clave eliminadas."
        await update.message.reply_text(msg, parse_mode="HTML")
        return ConversationHandler.END

    # NLP-based fields (tipo, ambientes, zona): regenerate URLs
    if field in ("_tipo_nlp", "_ambientes_nlp", "_zona_nlp"):
        summary = alert.get("summary", alert.get("name", ""))
        field_label = {"_tipo_nlp": "tipo de propiedad", "_ambientes_nlp": "ambientes", "_zona_nlp": "zona"}.get(field, field)
        new_desc = f"{summary} — cambiar {field_label} a: {text}"
        await update.message.reply_text("Un segundo, actualizando la búsqueda...")
        result = await interpret_search(new_desc)
        if not result:
            await update.message.reply_text("No pude interpretar el cambio. Intentá con /editar de nuevo.")
            return ConversationHandler.END
        result["_editing_idx"] = idx
        ctx.user_data["pending"] = result
        await update.message.reply_text(
            f"Nueva versión:\n\n<b>{result['summary']}</b>\n\n"
            "¿Confirmás? Respondé <b>si</b> o <b>no</b>.",
            parse_mode="HTML"
        )
        return AWAITING_CONFIRMATION

    await update.message.reply_text("Algo falló, intentá de nuevo.")
    return ConversationHandler.END

async def handle_edit_description(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Full rewrite via NLP."""
    desc = update.message.text.strip()
    if len(desc) < 5:
        await update.message.reply_text(
            "La descripción es muy corta. Contame qué cambios querés hacer, ej: <i>2 ambientes en Palermo, hasta 800k total</i>",
            parse_mode="HTML",
        )
        return AWAITING_EDIT_DESC
    await update.message.reply_text("Un segundo, estoy interpretando los cambios...")
    result = await interpret_search(desc)
    if not result:
        await update.message.reply_text(
            "No pude interpretar la descripción. Intentá de nuevo con más detalles."
        )
        return AWAITING_EDIT_DESC
    result["_editing_idx"] = ctx.user_data.get("editing_idx")
    ctx.user_data["pending"] = result
    await update.message.reply_text(
        f"Nueva versión:\n\n<b>{result['summary']}</b>\n\n"
        "¿Confirmás el reemplazo? Respondé <b>si</b> o <b>no</b>.",
        parse_mode="HTML"
    )
    return AWAITING_CONFIRMATION

async def cmd_estado(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    await cmd_alertas(update, ctx)

# ── Step-by-step wizard ────────────────────────────────────────────────────────

async def _start_wizard(msg, ctx: ContextTypes.DEFAULT_TYPE):
    """Begin the wizard: ask for property type. `msg` is a Message object."""
    ctx.user_data.pop("wizard", None)
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("🏢 Depto",     callback_data="tipo_depto"),
        InlineKeyboardButton("🏠 Casa",      callback_data="tipo_casa"),
        InlineKeyboardButton("🏘️ PH",        callback_data="tipo_ph"),
        InlineKeyboardButton("✅ Cualquiera", callback_data="tipo_todos"),
    ]])
    await msg.reply_text(
        "¿Qué tipo de propiedad buscás?",
        reply_markup=kb,
    )
    return AWAITING_TIPO

async def handle_wizard_tipo(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    tipo_map = {
        "tipo_depto": "departamento",
        "tipo_casa":  "casa",
        "tipo_ph":    "PH",
        "tipo_todos": "departamento, PH o casa",
    }
    label_map = {
        "tipo_depto": "🏢 Departamento",
        "tipo_casa":  "🏠 Casa",
        "tipo_ph":    "🏘️ PH",
        "tipo_todos": "✅ Cualquier tipo",
    }
    tipo = tipo_map.get(query.data, "departamento, PH o casa")
    ctx.user_data.setdefault("wizard", {})["tipo"] = tipo
    await query.edit_message_text(label_map.get(query.data, "✅ Cualquier tipo"))
    await query.message.reply_text(
        "¿Cuántos ambientes buscás?\n"
        "Ej: <b>2</b>, <b>2 a 3</b>, <b>3+</b>, <b>monoambiente</b>",
        parse_mode="HTML",
    )
    return AWAITING_AMBIENTES

async def handle_wizard_ambientes(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    ctx.user_data.setdefault("wizard", {})["ambientes"] = update.message.text.strip()
    await update.message.reply_text(
        "¿Superficie mínima en m²?\n"
        "Ej: <b>40</b>, <b>55m2</b> (o escribí <b>no importa</b>)",
        parse_mode="HTML",
    )
    return AWAITING_METROS

async def handle_wizard_metros(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    val = update.message.text.strip().lower()
    if val not in ("no importa", "no", "cualquiera", "-"):
        ctx.user_data.setdefault("wizard", {})["metros"] = update.message.text.strip()
    await update.message.reply_text(
        "¿Cuál es tu presupuesto máximo <b>total</b> (alquiler + expensas)?\n"
        "Ej: <b>800k</b>, <b>1.2M</b>, <b>900.000</b>",
        parse_mode="HTML",
    )
    return AWAITING_PRECIO

def _normalize_precio(raw: str) -> str:
    """If user types a plain number ≤ 9999 with no suffix, append 'k' (assume miles)."""
    s = raw.strip().replace(".", "").replace(",", "")
    if s.isdigit():
        n = int(s)
        if n <= 9999:
            return f"{n}k"
    return raw.strip()

async def handle_wizard_precio(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    wizard = ctx.user_data.setdefault("wizard", {})
    wizard["precio_raw"] = _normalize_precio(update.message.text)
    wizard["expensas_incluidas"] = True
    await update.message.reply_text(
        "¿Necesitás algo especial?\n"
        "Ej: <b>cochera</b>, <b>balcón</b>, <b>luminoso</b>, <b>terraza</b> "
        "(o escribí <b>no</b> si no hay nada más)",
        parse_mode="HTML",
    )
    return AWAITING_EXTRAS

async def handle_wizard_extras(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    chat_id = str(update.effective_chat.id)
    wizard  = ctx.user_data.get("wizard", {})
    val = update.message.text.strip().lower()
    if val not in ("no", "nada", "ninguno", "ninguna", "-"):
        wizard["extras"] = update.message.text.strip()

    # Load saved zones
    zones = ctx.user_data.get("barrios_mapa") or load_users().get(chat_id, {}).get("zones", [])

    # Build description for NLP
    tipo = wizard.get("tipo", "departamento, PH o casa")
    parts = [f"Busco {tipo}"]
    if wizard.get("ambientes"):
        parts.append(f"de {wizard['ambientes']} ambiente(s)")
    if zones:
        parts.append(f"en {', '.join(zones)}")
    if wizard.get("metros"):
        parts.append(f"con al menos {wizard['metros']} m2")
    if wizard.get("precio_raw"):
        sufijo = " incluyendo expensas" if wizard.get("expensas_incluidas") else " solo de alquiler"
        parts.append(f"hasta {wizard['precio_raw']}{sufijo}")
    if wizard.get("extras"):
        parts.append(f"que tenga {wizard['extras']}")

    desc = ", ".join(parts)
    if zones:
        desc = f"Zonas preferidas del usuario: {', '.join(zones)}. " + desc

    await update.message.reply_text("Un segundo, estoy armando tu búsqueda...")
    result = await interpret_search(desc)
    if not result:
        await update.message.reply_text(
            "No entendí bien los extras. ¿Podés reescribirlos? Ej: <b>gas natural, cochera</b> (o escribí <b>no</b>)",
            parse_mode="HTML",
        )
        return AWAITING_EXTRAS

    # Stamp wizard intent so _show_confirmation shows the right price label
    if "expensas_incluidas" in wizard:
        result["_expensas_incluidas"] = wizard["expensas_incluidas"]

    return await _show_confirmation(update, ctx, result)

async def _show_confirmation(update: Update, ctx: ContextTypes.DEFAULT_TYPE, result: dict):
    """Save pending result and show confirmation with price note."""
    ctx.user_data["pending"] = result
    max_r = result.get("max_rent_price", 0)
    max_t = result.get("max_total_price", 0)
    expensas_incluidas = result.get("_expensas_incluidas")  # set by wizard
    if max_t and expensas_incluidas is True:
        fmt_t = f"${max_t:,.0f}".replace(",", ".")
        price_note = f"💰 Precio: hasta {fmt_t} en total (alquiler + expensas)"
    elif max_r and expensas_incluidas is False:
        fmt_r = f"${max_r:,.0f}".replace(",", ".")
        price_note = f"💰 Precio: hasta {fmt_r} de alquiler, sin contar expensas"
    elif max_r and max_t:
        # free-text path: guess from ratio
        fmt_r = f"${max_r:,.0f}".replace(",", ".")
        fmt_t = f"${max_t:,.0f}".replace(",", ".")
        if (max_t / max_r) < 1.15:
            price_note = f"💰 Precio: hasta {fmt_t} en total (alquiler + expensas)"
        else:
            price_note = f"💰 Precio: hasta {fmt_r} de alquiler, sin contar expensas"
    else:
        price_note = ""
    msg = f"Esto es lo que entendí:\n\n<b>{result['summary']}</b>\n\n"
    if price_note:
        msg += f"{price_note}\n\n"
    msg += "¿Confirmás? Respondé <b>si</b> o <b>no</b>."
    await update.message.reply_text(msg, parse_mode="HTML")
    return AWAITING_CONFIRMATION

# ── Entry point: routes to wizard or free-text ────────────────────────────────

async def receive_description(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Entry point for plain text. If /submit-zones set a wizard step, start wizard."""
    chat_id = str(update.effective_chat.id)
    step = load_users().get(chat_id, {}).get("_wizard_step")
    if step != "ambientes":
        reply = _non_search_reply(update.message.text or "")
        if reply:
            return await _reply_non_search(update, ctx, reply)
    if step == "ambientes":
        # Clear the flag (PTB takes over from here)
        users = load_users()
        users[chat_id].pop("_wizard_step", None)
        save_users(users)
        # barrios already saved; load them into user_data
        ctx.user_data["barrios_mapa"] = users[chat_id].get("zones", [])
        return await handle_wizard_ambientes(update, ctx)
    return await _receive_description_freetext(update, ctx)

async def _receive_description_freetext(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    desc         = update.message.text.strip()
    chat_id      = str(update.effective_chat.id)
    reply = _non_search_reply(desc)
    if reply:
        return await _reply_non_search(update, ctx, reply)
    if len(desc) < 5:
        await update.message.reply_text(
            "La descripción es muy corta. Contame qué estás buscando, ej: <i>2 ambientes en Palermo, hasta 800k total</i>",
            parse_mode="HTML",
        )
        return AWAITING_DESCRIPTION
    barrios_mapa = ctx.user_data.get("barrios_mapa")
    if not barrios_mapa:
        barrios_mapa = load_users().get(chat_id, {}).get("zones", [])
        if barrios_mapa:
            ctx.user_data["barrios_mapa"] = barrios_mapa
    if barrios_mapa:
        desc = f"Zonas preferidas del usuario (usá estas si no menciona otras): {', '.join(barrios_mapa)}. Descripción: {desc}"
    await update.message.reply_text("Un segundo, estoy interpretando tu búsqueda...")
    result = await interpret_search(desc)
    if result and result.get("no_es_busqueda"):
        return await _reply_non_search(
            update, ctx,
            "Eso no parece una búsqueda de propiedad. Si querés crear una alerta, "
            "contame qué buscás (ej: <i>2 ambientes en Palermo hasta 800k</i>) o usá /buscar.\n\n"
            + COMMANDS_TEXT,
        )
    if not result:
        await update.message.reply_text(
            "No pude interpretar la búsqueda. "
            "¿Podés aclarar qué barrios, tipo de propiedad y precio máximo buscás?"
        )
        return AWAITING_DESCRIPTION
    return await _show_confirmation(update, ctx, result)

async def handle_confirmation(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    text    = update.message.text.lower().strip()
    chat_id = str(update.effective_chat.id)

    if text in ("si", "sí", "yes", "s", "ok", "dale", "confirmo"):
        alert   = ctx.user_data.pop("pending", {})
        edit_idx = alert.pop("_editing_idx", None)
        if edit_idx is not None:
            users = load_users()
            user  = users.get(chat_id)
            if user and "alerts" in user and edit_idx < len(user["alerts"]):
                user["alerts"][edit_idx] = alert
                save_users(users)
            await update.message.reply_text(
                f"Alerta actualizada: <b>{alert.get('name') or alert.get('summary','')}</b>",
                parse_mode="HTML"
            )
            return ConversationHandler.END
        add_alert(chat_id, alert)
        await update.message.reply_text(
            f"✅ Alerta guardada: <b>{alert.get('name') or alert.get('summary','')}</b>\n\n"
            "🔍 Buscando publicaciones de la última semana que coincidan...",
            parse_mode="HTML"
        )
        # Immediate scrape for this user
        tg_app = ctx.application
        users  = load_users()
        user   = users.get(chat_id, {})
        user.setdefault("active", True)
        count  = await scrape_user(tg_app, chat_id, user)
        save_users(users)
        if count == 0:
            await update.message.reply_text(
                "No encontré publicaciones recientes que coincidan. "
                "Voy a revisar cada 15 minutos y te aviso cuando aparezca algo nuevo."
            )
        else:
            await update.message.reply_text(
                f"Te mandé {count} publicación(es) reciente(s) que encontré. "
                "Voy a revisar cada 15 minutos y te aviso cuando haya algo nuevo."
            )
        await update.message.reply_text(
            "💡 Podés usar /alertas para ver, editar o borrar tus alertas en cualquier momento."
        )
        await update.message.reply_text("¿Querés agregar otra alerta con distintos criterios? (si/no)")
        return AWAITING_MORE_ALERTS

    if text in ("no", "n"):
        await update.message.reply_text("Contame de nuevo qué estás buscando. Podés ser más específico.")
        return AWAITING_DESCRIPTION

    reply = _non_search_reply(text)
    if reply:
        return await _reply_non_search(update, ctx, reply)
    await update.message.reply_text("Respondé <b>si</b> o <b>no</b>.", parse_mode="HTML")
    return AWAITING_CONFIRMATION

async def handle_more_alerts(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    text    = update.message.text.lower().strip()
    chat_id = str(update.effective_chat.id)

    if text in ("si", "sí", "yes", "s"):
        return await _start_wizard(update.message, ctx)

    users  = load_users()
    n      = len(get_alerts(users.get(chat_id, {})))
    await update.message.reply_text(
        f"Listo! Tenés {n} alerta(s) configurada(s). Te aviso cuando aparezcan publicaciones.\n"
        "Usá /alertas para ver o borrar alertas, /buscar para agregar más, /stop para pausar.",
    )
    return ConversationHandler.END

# ── Scraper job ────────────────────────────────────────────────────────────────
async def scrape_user(app: Application, chat_id: str, user: dict) -> int:
    """Scrape all alerts for one user. Returns count of new listings sent."""
    seen  = set(user.get("seen", []))
    total = 0
    loop  = asyncio.get_event_loop()

    for alert in get_alerts(user):
        sources = (
            [("zonaprop",     u) for u in alert.get("zonaprop_urls",     [])]
            + [("argenprop",  u) for u in [argenprop_url(alert, remax_params(alert, user))] if u]
            + [("mercadolibre", u) for u in alert.get("mercadolibre_urls", [])]
            + [("remax", None)]
        )
        for scraper_name, url in sources:
            if scraper_name == "zonaprop":
                listings = scrape_zonaprop(url)
            elif scraper_name == "remax":
                listings = scrape_remax(alert, remax_params(alert, user))
            elif scraper_name == "argenprop":
                listings = scrape_argenprop(url)
            else:
                listings = scrape_mercadolibre(url)

            if scraper_name == "mercadolibre":
                for l in listings:
                    if not l["expenses"]:
                        l["expenses"] = await loop.run_in_executor(
                            None, lambda link=l["link"]: fetch_ml_expenses(link)
                        )

            for l in listings:
                l.setdefault("tipo", _infer_tipo(l["link"], url or ""))
            listings = filter_listings(listings, alert)
            new = [l for l in listings if l["id"] not in seen]

            for l in new:
                try:
                    await app.bot.send_message(
                        chat_id=int(chat_id),
                        text=format_listing(l),
                        parse_mode="HTML",
                    )
                    seen.add(l["id"])
                    total += 1
                    await asyncio.sleep(0.4)
                except Exception as e:
                    log.error("Error sending to %s: %s", chat_id, e)

    user["seen"] = sorted(seen)
    return total

async def scrape_all(app: Application):
    users = load_users()
    if not users:
        return
    changed = False
    for chat_id, user in users.items():
        if not user.get("active", True):
            continue
        await scrape_user(app, chat_id, user)
        changed = True
    if changed:
        save_users(users)
    log.info("Scrape cycle done for %d user(s)", len(users))

# ── Main ───────────────────────────────────────────────────────────────────────
async def _http_map(request):
    return aiohttp_web.FileResponse(APP_DIR / "map.html")

async def _http_geojson(request):
    path = APP_DIR / "barrios.geojson"
    if not path.exists():
        raise aiohttp_web.HTTPNotFound()
    return aiohttp_web.FileResponse(path, headers={"Content-Type": "application/geo+json"})

async def _http_conurbano(request):
    path = APP_DIR / "conurbano.geojson"
    if not path.exists():
        raise aiohttp_web.HTTPNotFound()
    return aiohttp_web.FileResponse(path, headers={"Content-Type": "application/geo+json"})

_BOT_APP = None  # set in main() before HTTP server starts

async def _http_submit_zones(request):
    """Receive zone selection from the map mini app (POST /submit-zones)."""
    try:
        body    = await request.json()
        chat_id = int(body["chat_id"])
        barrios = body.get("barrios", [])
    except Exception:
        return aiohttp_web.Response(text="bad request", status=400)

    if not barrios:
        return aiohttp_web.Response(text="no barrios", status=400)

    chat_id_str = str(chat_id)
    users = load_users()
    users.setdefault(chat_id_str, {"active": True, "seen": [], "alerts": []})
    users[chat_id_str]["zones"] = barrios
    save_users(users)

    lista = ", ".join(barrios)
    users[chat_id_str]["_wizard_step"] = "ambientes"
    save_users(users)
    if _BOT_APP:
        await _BOT_APP.bot.send_message(
            chat_id=chat_id,
            text=f"Perfecto, <b>{lista}</b>.",
            parse_mode="HTML",
        )
        await _BOT_APP.bot.send_message(
            chat_id=chat_id,
            text=(
                "¿Cuántos ambientes buscás?\n"
                "Ej: <b>2</b>, <b>2 a 3</b>, <b>3+</b>, <b>monoambiente</b>"
            ),
            parse_mode="HTML",
        )
    return aiohttp_web.Response(text="ok")

async def start_http_server():
    http_app = aiohttp_web.Application()
    http_app.router.add_get("/map", _http_map)
    http_app.router.add_get("/barrios.geojson", _http_geojson)
    http_app.router.add_get("/conurbano.geojson", _http_conurbano)
    http_app.router.add_get("/health", lambda r: aiohttp_web.Response(text="ok"))
    http_app.router.add_post("/submit-zones", _http_submit_zones)
    runner = aiohttp_web.AppRunner(http_app)
    await runner.setup()
    site = aiohttp_web.TCPSite(runner, "0.0.0.0", 8080)
    await site.start()
    log.info("HTTP server listening on :8080")

_NON_CARD_KEYWORDS = {"gas", "eléctrico", "electrico", "inducción", "induccion",
                      "calefacción", "calefaccion", "agua caliente"}

def _migrate_users():
    """One-time migrations on startup."""
    users = load_users()
    changed = False
    for user in users.values():
        for alert in user.get("alerts", []):
            # Add _id if missing
            if "_id" not in alert:
                alert["_id"] = uuid.uuid4().hex[:8]
                changed = True
            # Remove keywords that don't appear in listing cards
            rk = alert.get("require_keywords", [])
            new_rk = [k for k in rk if k.lower() not in _NON_CARD_KEYWORDS]
            if new_rk != rk:
                alert["require_keywords"] = new_rk
                changed = True
    if changed:
        save_users(users)
        log.info("Migration applied to users.json")

def main():
    _migrate_users()
    persistence = PicklePersistence(filepath=DATA_DIR / "conversations.pickle")
    app = Application.builder().token(TELEGRAM_TOKEN).persistence(persistence).build()

    edit_choice = CallbackQueryHandler(handle_edit_choice, pattern=r"^ef_\w+:[\w]+$")
    conv = ConversationHandler(
        name="main",
        persistent=True,
        entry_points=[
            edit_choice,
            CommandHandler("start",  cmd_start),
            CommandHandler("buscar", cmd_buscar),
            CommandHandler("editar", cmd_editar),
            CallbackQueryHandler(handle_alert_edit_button, pattern=r"^alert_edit:[\w]+$"),
            MessageHandler(filters.StatusUpdate.WEB_APP_DATA, handle_web_app_data),
            MessageHandler(filters.TEXT & ~filters.COMMAND, receive_description),
        ],
        states={
            AWAITING_ZONE_CONFIRM: [
                CallbackQueryHandler(handle_zone_confirm, pattern="^zones_keep$"),
                MessageHandler(filters.StatusUpdate.WEB_APP_DATA, handle_web_app_data),
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_description),
            ],
            AWAITING_DESCRIPTION:  [
                MessageHandler(filters.StatusUpdate.WEB_APP_DATA, handle_web_app_data),
                MessageHandler(filters.TEXT & ~filters.COMMAND, _receive_description_freetext),
            ],
            AWAITING_TIPO:         [CallbackQueryHandler(handle_wizard_tipo, pattern="^tipo_(depto|casa|ph|todos)$")],
            AWAITING_AMBIENTES:    [MessageHandler(filters.TEXT & ~filters.COMMAND, handle_wizard_ambientes)],
            AWAITING_METROS:       [MessageHandler(filters.TEXT & ~filters.COMMAND, handle_wizard_metros)],
            AWAITING_PRECIO:       [MessageHandler(filters.TEXT & ~filters.COMMAND, handle_wizard_precio)],
            AWAITING_EXTRAS:       [MessageHandler(filters.TEXT & ~filters.COMMAND, handle_wizard_extras)],
            AWAITING_CONFIRMATION: [MessageHandler(filters.TEXT & ~filters.COMMAND, handle_confirmation)],
            AWAITING_MORE_ALERTS:  [
                MessageHandler(filters.StatusUpdate.WEB_APP_DATA, handle_web_app_data),
                MessageHandler(filters.TEXT & ~filters.COMMAND, handle_more_alerts),
            ],
            AWAITING_EDIT_CHOICE:  [edit_choice],
            AWAITING_EDIT_FIELD:   [MessageHandler(filters.TEXT & ~filters.COMMAND, handle_edit_field_value)],
            AWAITING_EDIT_DESC:    [MessageHandler(filters.TEXT & ~filters.COMMAND, handle_edit_description)],
        },
        fallbacks=[
            CommandHandler("start", cmd_start),
            CallbackQueryHandler(handle_alert_edit_button, pattern=r"^alert_edit:[\w]+$"),
            edit_choice,
        ],
        allow_reentry=True,
    )

    app.add_handler(conv)
    app.add_handler(CallbackQueryHandler(handle_alert_del_button, pattern=r"^alert_del:[\w]+$"))
    app.add_handler(CommandHandler("stop",       cmd_stop))
    app.add_handler(CommandHandler("estado",     cmd_estado))
    app.add_handler(CommandHandler("alertas",    cmd_alertas))
    app.add_handler(CommandHandler("borrar",     cmd_borrar))
    app.add_handler(CommandHandler("borrartodo", cmd_borrar_todo))
    app.add_handler(CommandHandler("editar",     cmd_editar))
    app.add_handler(CommandHandler("resetseen",  cmd_resetseen))
    app.add_handler(CommandHandler("help",       cmd_help))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, fallback_unknown))
    app.add_handler(MessageHandler(filters.COMMAND, fallback_unknown))  # /comandos desconocidos

    # Start HTTP server and scraper scheduler
    global _BOT_APP
    _BOT_APP = app
    loop = asyncio.get_event_loop()
    loop.run_until_complete(start_http_server())

    scheduler = AsyncIOScheduler()
    scheduler.add_job(
        scrape_all,
        "interval",
        minutes=15,
        jitter=120,
        id="scraper",
        args=[app],
    )
    scheduler.start()
    log.info("Bot iniciado. Scrapeando cada 15 minutos.")

    app.run_polling(drop_pending_updates=True)

if __name__ == "__main__":
    main()
