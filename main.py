#!/usr/bin/env python3
"""
Multi-user apartment alert bot.
Users configure their search via natural language → Gemini interprets it.
Scrapes ZonaProp + MercadoLibre every 12 minutes per user.
Deploy on Fly.io (persistent process).
"""

import asyncio
import ctypes
import gc
import html as html_mod
import json
import logging
import os
import re
import time
import unicodedata
import uuid
from pathlib import Path

import aiohttp
from aiohttp import web as aiohttp_web
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
    ApplicationHandlerStop,
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
AWAITING_INITIAL_SEND = 14
AWAITING_DUENO        = 15
INITIAL_SEND_DAYS     = 7   # "las de la última semana" al guardar una alerta

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger(__name__)
try:  # copia de los logs en el volumen para poder revisarlos (máx ~1.5 MB)
    from logging.handlers import RotatingFileHandler
    _fh = RotatingFileHandler(DATA_DIR / "bot.log", maxBytes=500_000, backupCount=2, encoding="utf-8")
    _fh.setFormatter(logging.Formatter("%(asctime)s [%(levelname)s] %(message)s"))
    logging.getLogger().addHandler(_fh)
    logging.getLogger("httpx").setLevel(logging.WARNING)  # sin una línea por cada getUpdates
except OSError:
    pass

GROQ_URL = "https://api.groq.com/openai/v1/chat/completions"

# ── Memoria ────────────────────────────────────────────────────────────────────
# La máquina tiene 256 MB. glibc crea un "arena" de malloc por hilo (los
# run_in_executor usan hilos) y no devuelve al sistema la memoria liberada;
# limitar arenas y llamar malloc_trim tras cada ciclo evita que el RSS crezca.
try:
    _libc = ctypes.CDLL("libc.so.6")
    _libc.mallopt(-8, 2)  # M_ARENA_MAX = 2
except OSError:
    _libc = None

def release_memory():
    gc.collect()
    if _libc is not None:
        _libc.malloc_trim(0)

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

def _listing(uid, address, price, expenses, features, link, days_ago=None, expenses_note="") -> dict:
    return {
        "id": uid,
        "address": address or "Sin dirección",
        "price": price,
        "expenses": expenses,
        "expenses_note": expenses_note,
        "features": features,
        "link": link,
        "days_ago": days_ago,
    }

# ── Expensas: monto real o lo que diga la publicación ──────────────────────────
EXP_NONE     = "sin expensas"
EXP_INCLUDED = "expensas incluidas"

_EXP_NONE_RE = re.compile(
    r"\bsin\s+expensas|\bno\s+(?:paga|tiene|abona|posee)\s+expensas|"   # sin \b final: "Sin expensasServicios"
    r"\bexpensas\s*[:\-]?\s*(?:no\s+(?:paga|tiene|abona|posee)\b|cero\b|\$?\s*0(?![\d.,]))",
    re.IGNORECASE)
_EXP_INCLUDED_RE = re.compile(
    r"\b(?:incluye|incluyen|incluido|incluida|incluidas|incluidos)\s+(?:las\s+)?expensas\b|"
    r"\bexpensas\s+incluidas\b",
    re.IGNORECASE)
# Número de expensas: "132.000", "132. 000" (espacio tras el punto), "160", "45000".
_EXP_NUM = r"(\d{1,3}(?:[.,]\s?\d{3})+|\d{1,7})(?![\d.,]*\s*(?:m2|m²|amb|dorm))"
# "Expensas $132. 000 aprox", "expensas: $ 60.000", "$ 60.000 de expensas", "Expensas $700"
_EXP_AMOUNT_RE = re.compile(
    r"\bexpensas\s*(?:de|:|aprox\.?|aproximadas)?\s*\$\s*" + _EXP_NUM + r"|"
    r"\$\s*" + _EXP_NUM + r"\s*(?:de\s+)?expensas\b|"
    r"\bexpensas\s*[:=]?\s*(?:de\s+)?(\d{1,3}(?:\.\d{3})+)\b",   # "Expensas: 45.000" (sin $)
    re.IGNORECASE)

def _exp_value(val: int) -> int | None:
    """Normaliza un monto de expensas. 0 o 1 = sin expensas (los portales usan $1
    como "no tiene"); de 2 a 999 se escribió en miles ("160" = $160.000)."""
    if val <= 1:
        return 0
    if val < 1000:
        return val * 1000
    return val if val <= 3_000_000 else None

def _fmt_ars(v: int) -> str:
    return f"$ {v:,}".replace(",", ".")

def _expenses_info(structured: str, text: str = "") -> tuple[str, str]:
    """(expensas, nota). `expensas` es el monto ("$ 60.000") o "" si no hay monto;
    `nota` es EXP_NONE / EXP_INCLUDED / "" (no informadas).
    Prioridad: monto del campo estructurado > monto en el texto > "sin expensas" /
    "incluidas" en el texto > campo estructurado en 0 > no informadas."""
    field = _exp_value(_parse_price(structured)) if structured and re.search(r"\d", structured) else None
    if field:
        return _fmt_ars(field), ""
    for m in _EXP_AMOUNT_RE.finditer(text or ""):
        val = _exp_value(int(re.sub(r"\D", "", next(g for g in m.groups() if g)) or 0))
        if val:
            return _fmt_ars(val), ""
    if _EXP_NONE_RE.search(text or ""):
        return "", EXP_NONE
    if _EXP_INCLUDED_RE.search(text or ""):
        return "", EXP_INCLUDED
    if field == 0:
        return "", EXP_NONE      # el anunciante cargó 0 (o $1) de expensas
    return "", ""

# ── Dueño directo ──────────────────────────────────────────────────────────────
_OWNER_TEXT_RE = re.compile(
    r"due[ñn][oa]\s+directo|due[ñn][oa]\s+alquila|alquila\s+due[ñn][oa]|sin\s+comisi[oó]n|"
    r"inmobiliarias\s+abstenerse|abstenerse\s+inmobiliarias|trato\s+directo\s+con\s+(?:el\s+)?due[ñn]",
    re.IGNORECASE)
_AGENCY_NAME_RE = re.compile(
    r"propiedades|inmobiliari|real\s*estate|bienes\s+ra[ií]ces|broker|negocios|desarrollos|"
    r"\bs\.?\s?a\.?$|\bs\.?r\.?l\.?|\bgroup\b|grupo|estudio|asociados|remax|re/max",
    re.IGNORECASE)

def _owner_from_text(text: str) -> bool:
    return bool(_OWNER_TEXT_RE.search(text or ""))

def _argenprop_owner(publisher: str, text: str) -> bool:
    """ArgenProp muestra a los particulares como nombre + inicial ("Marcelo Jose O")
    y a las inmobiliarias con el nombre completo."""
    name = (publisher or "").strip()
    if _AGENCY_NAME_RE.search(name):
        return False
    if re.search(r"\s[A-Za-zÁÉÍÓÚÑáéíóúñ]\.?$", name):
        return True
    return _owner_from_text(text)

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

def _zonaprop_owner_flags(soup) -> dict:
    """postingId -> True si ZonaProp lo marca como "Dueño directo"."""
    script = soup.find("script", string=re.compile(r"__PRELOADED_STATE__"))
    if not script or not script.string:
        return {}
    try:
        src = script.string
        start = re.search(r"__PRELOADED_STATE__\s*=\s*", src).end()
        state, _ = json.JSONDecoder().raw_decode(src, start)
        posts = state["listStore"]["listPostings"]
    except Exception as e:
        log.warning("[ZonaProp] no pude leer el JSON de la página: %s", e)
        return {}
    return {str(p.get("postingId")): any(f.get("featureId") == "duenoDirecto" for f in (p.get("flagsFeatures") or []))
            for p in posts}

def scrape_zonaprop(url: str) -> list[dict]:
    soup = fetch(url, "https://www.zonaprop.com.ar/")
    if not soup:
        return []
    owners  = _zonaprop_owner_flags(soup)
    results = []
    for card in soup.select("div[data-id]"):
        listing_id = card.get("data-id", "").strip()
        if not listing_id:
            continue
        street   = _text(card, "[class*='location-address']")
        hood     = _text(card, "[class*='location-text']").split(",")[0].strip()
        address  = f"{street}, {hood}" if hood else street
        price    = _text(card, "h2[class*='postingPrices-module__price']")
        expenses, exp_note = _expenses_info(_text(card, "[class*='expenses']"), card.get_text(" ", strip=True))
        features = _text(card, "[class*='posting-main-features-block']", sep=" · ")
        pub_text = _text(card, "[class*='antiquity-date'], [class*='Antiquity'], [class*='posting-date']")
        link_el  = card.select_one("a[href*='propiedades']")
        if link_el:
            path = link_el.get("href", "").split("?")[0]
            link = f"https://www.zonaprop.com.ar{path}" if path.startswith("/") else path
        else:
            link = f"https://www.zonaprop.com.ar/propiedades/clasificado/{listing_id}.html"
        l = _listing(f"zp_{listing_id}", address, price, expenses, features, link, _days_ago(pub_text), exp_note)
        l["owner"] = owners.get(listing_id) or _owner_from_text(card.get_text(" ", strip=True))
        results.append(l)
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
        r = cffi_requests.get("https://dolarapi.com/v1/dolares/oficial", timeout=10)
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
    max_p = _price_limits(alert)[0] or 10**9
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
        exp, exp_note = _expenses_info(
            str(l.get("expensesPrice")) if l.get("expensesPrice") else "",
            f"{l.get('title', '')} {l.get('description', '')}",
        )
        cov = l.get("dimensionCovered") or 0
        tot = l.get("dimensionTotalBuilt") or 0
        m2  = (f" · {round(tot)} m² tot." if tot else "") + (f" · {round(cov)} m² cubiertos" if cov else "")
        features = f"{rooms} amb.{m2} · {l.get('title', '')}{usd_note}"
        type_id = (l.get("type") or {}).get("id", 0)
        results.append({**_listing(
            f"rx_{l['id']}",
            f"{l.get('displayAddress', '')}, {l.get('geoLabel', '').split(',')[0]}",
            f"$ {int(price):,}".replace(",", "."),
            exp,
            features,
            f"https://www.remax.com.ar/listings/{l.get('slug', l['id'])}",
            expenses_note=exp_note,
        ), "owner": False, "tipo": "PH" if type_id == 12 else "Casa" if type_id in (9, 10, 11) else "Depto"})
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
    max_p = _price_limits(alert)[0]
    if max_p:
        parts.append(f"pesos-{alert.get('min_price', 0)}-{max_p}")
    if alert.get("solo_dueno"):
        parts.append("dueno-directo")   # filtro "Tipo de anunciante" de ArgenProp
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
        expenses, exp_note = _expenses_info(expenses, card.get_text(" ", strip=True))
        title = _text(card, ".card__title")
        if title:
            features = f"{features} · {title}" if features else title
        if not price:
            continue
        pub_text = _text(card, "[class*='date'], [class*='time'], [class*='fecha'], [class*='publicad']")
        l = _listing(f"ap_{uid}", address, price, expenses, features, href, _days_ago(pub_text), exp_note)
        l["owner"] = _argenprop_owner(_text(card, ".card__agent-name"), card.get_text(" ", strip=True))
        results.append(l)
    return results

def fetch_ml_expenses(url: str) -> tuple[str, str] | None:
    """(expensas, nota) leídas de la publicación de ML (tabla + descripción).
    None si no se pudo abrir la página."""
    soup = fetch(url, "https://inmuebles.mercadolibre.com.ar/")
    if not soup:
        return None
    table_val = ""
    for row in soup.select("tr"):
        header = row.select_one("th")
        value  = row.select_one("td")
        if header and value and "expensa" in header.get_text(strip=True).lower():
            table_val = _clean(value.get_text(strip=True))
            break
    desc = soup.select_one("p.ui-pdp-description__content")
    desc = desc.get_text(" ", strip=True) if desc else ""
    seller = soup.find(string=re.compile(r'"seller_type"\s*:'))
    m = re.search(r'"seller_type"\s*:\s*"(\w+)"', str(seller or ""))
    if m:
        _ml_owner_cache[url] = m.group(1) != "real_estate_agency" or _owner_from_text(desc)
    elif _owner_from_text(desc):
        _ml_owner_cache[url] = True
    return _expenses_info(table_val, desc)

_ml_owner_cache: dict = {}   # link -> es dueño directo (se llena al abrir el detalle)

def fetch_remax_expenses(link: str) -> tuple[str, str] | None:
    """(expensas, nota) desde el detalle de Remax (API findBySlug: expensesPrice +
    descripción completa). None si no se pudo consultar."""
    slug = link.rstrip("/").rsplit("/", 1)[-1]
    try:
        resp = cffi_requests.get(f"{REMAX_API.rsplit('/', 1)[0]}/findBySlug/{slug}",
                                 impersonate="chrome124", timeout=20)
        data = resp.json()
        data = data.get("data", data) if isinstance(data, dict) else {}
    except Exception as e:
        log.warning("[Remax] detalle %s: %s", slug, e)
        return None
    exp = data.get("expensesPrice")
    return _expenses_info(str(int(exp)) if exp else "", f"{data.get('title', '')} {data.get('description', '')}")

# Fuentes cuya descripción completa solo está en la publicación (ZonaProp y
# ArgenProp ya la traen entera en la tarjeta del listado).
DETAIL_EXPENSES = {"mercadolibre": fetch_ml_expenses, "remax": fetch_remax_expenses}

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

def _price_limits(alert: dict) -> tuple[int, int]:
    """(tope de alquiler, tope total) de una alerta.

    - Presupuesto TOTAL (alquiler + expensas): se buscan alquileres hasta el total
      y después se filtra por alquiler + expensas reales. Sin expensas cuenta solo
      el alquiler. Tope total = presupuesto.
    - Solo ALQUILER: tope de alquiler = presupuesto, sin tope total.

    Alertas viejas guardaban 80%/120% del presupuesto; el modo se deduce del
    flag del wizard o de esa proporción (total → t/r = 1.25, alquiler → 1.2)."""
    max_t = alert.get("max_total_price") or 0
    max_r = alert.get("max_rent_price") or 0
    total_mode = alert.get("_expensas_incluidas")
    if total_mode is None:
        if max_t and max_r:
            total_mode = max_t / max_r >= 1.225 or max_t == max_r
        else:
            total_mode = bool(max_t)
    if total_mode and max_t:
        return max_t, max_t
    return (max_r or max_t), 0

_M2 = r"(\d+(?:[.,]\d+)?)\s*m[²2]"
def _m2_total(features: str) -> tuple[int | None, bool]:
    """(m² totales, exacto). Totales explícitos ("50 m² tot.") o sin calificar
    ("50 m²") son exactos; cubiertos + descubiertos/semicubiertos también.
    Si solo se conocen los cubiertos devuelve (cubiertos, False)."""
    f = features or ""
    num = lambda m: int(float(m.group(1).replace(",", ".")))
    m = re.search(_M2 + r"\s*(?:tot|total)", f, re.IGNORECASE)
    if m:
        return num(m), True
    cub   = re.search(_M2 + r"\s*cub", f, re.IGNORECASE)
    extra = sum(num(x) for x in re.finditer(_M2 + r"\s*(?:descub|semicub|semi)", f, re.IGNORECASE))
    if cub:
        return num(cub) + extra, bool(extra)
    m = re.search(_M2 + r"(?!\s*(?:cub|descub|semi))", f, re.IGNORECASE)
    if m:
        return num(m), True
    return None, False

def _apply_price_cap(url: str, alert: dict) -> str:
    """Reescribe el precio máximo de una URL de búsqueda guardada con el tope
    actual (las alertas viejas tienen el 80% del presupuesto en la URL)."""
    cap, _ = _price_limits(alert)
    if not cap or not url:
        return url
    url = re.sub(r"-(\d+)-\d+-pesos", rf"-\g<1>-{cap}-pesos", url)              # ZonaProp
    url = re.sub(r"(_PriceRange_\d+ARS-)\d+(ARS)", rf"\g<1>{cap}\g<2>", url)      # MercadoLibre
    url = re.sub(r"(--precio-desde-\d+-hasta-)\d+", rf"\g<1>{cap}", url)          # ArgenProp
    return url

def _apply_alert_params(url: str, alert: dict) -> str:
    """Ajusta una URL guardada a los valores actuales de la alerta: tope de precio
    y m² mínimos TOTALES. ZonaProp solo filtra por m² cubiertos, así que ese
    filtro se saca de la URL y se aplica después sobre los totales."""
    url = _apply_price_cap(url, alert)
    url = re.sub(r"-mas-\d+-m2-cubiertos", "", url)                                # ZonaProp
    url = re.sub(r"desde-(\d+)-hasta-ambientes", r"desde-\1-hasta-5-ambientes", url)  # ZonaProp "2+"
    if alert.get("min_m2"):
        url = re.sub(r"(TOTAL\*AREA_)\d+(m)", rf"\g<1>{int(alert['min_m2'])}\g<2>", url)  # MercadoLibre
    return url

# Un depto casi siempre tiene expensas: si no están informadas y el alquiler solo
# ya supera este % del presupuesto total, no entra. Casas y PH se muestran igual.
DEPTO_UNKNOWN_EXP_MAX_SHARE = 0.90

def filter_listings(listings: list, alert: dict, max_age: int = MAX_LISTING_AGE_DAYS) -> list:
    min_p    = alert.get("min_price", 200000)
    max_r, max_t = _price_limits(alert)
    min_m2   = alert.get("min_m2", 0)
    required = [kw.lower() for kw in alert.get("require_keywords", [])]
    excluded = [kw.lower() for kw in alert.get("exclude_keywords", [])]
    out = []
    for l in listings:
        # Date filter: skip listings older than MAX_LISTING_AGE_DAYS
        age = l.get("days_ago")
        if age is not None and age > max_age:
            continue

        rent = _parse_price(l["price"])
        if rent < min_p:
            continue
        if max_r and rent > max_r:
            continue

        # m² mínimos TOTALES. ML en el listado solo muestra cubiertos, pero su
        # búsqueda ya filtra por superficie total, así que ahí no se descarta.
        if min_m2:
            total_m2, exact = _m2_total(l.get("features", ""))
            if total_m2 is not None and total_m2 < 10:
                total_m2 = None  # dato mal cargado ("2 m² cubie."): no descartar por eso
            if total_m2 is not None and total_m2 < min_m2 and (exact or not l["id"].startswith("ml_")):
                continue

        # Expensas reales; si la publicación no tiene, cuenta solo el alquiler.
        total = rent + _parse_price(l["expenses"])
        if (max_t and l.get("tipo") == "Depto" and not l["expenses"]
                and not l.get("expenses_note") and rent > max_t * DEPTO_UNKNOWN_EXP_MAX_SHARE):
            continue  # depto en el límite con expensas no informadas
        if max_t and total > max_t:
            continue
        # Solo dueño directo (excluyente): si no está confirmado, no entra.
        if alert.get("solo_dueno") and l.get("owner") is not True:
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
    user["active"] = True  # crear una alerta reactiva las notificaciones pausadas con /stop
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
    elif l.get("expenses_note"):
        price_line += f" ({l['expenses_note']})"
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
https://www.zonaprop.com.ar/{tipos}-alquiler-{barrios}-{ambientes}-{precio}-pesos-orden-publicado-descendente.html
- tipos: departamentos | casas | ph | casas-departamentos-ph (separados por -)
- barrios: nombres en minúscula con guiones, separados por - (ej: palermo-villa-crespo)
- ambientes: desde-1-hasta-3-ambientes (omitir si no se especifica; "2 o más" → desde-2-hasta-5-ambientes)
- m2: NO incluir el filtro de m² en ZonaProp (solo filtra cubiertos; los m² totales se filtran después)
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
- m2: metros cuadrados mínimos TOTALES (usá 30 si no se especifica)

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
   → max_total_price = 800000, max_rent_price = 800000
   (se buscan alquileres hasta 800k y después se filtra por alquiler + expensas)

2. "hasta 800k de alquiler" / solo alquiler / sin aclaración:
   → max_rent_price = 800000, max_total_price = 0

3. No especifica precio: NO inventes uno. max_rent_price = 0, max_total_price = 0 y no
   pongas rango de precio en las URLs (ZonaProp sin el tramo "-{min}-{max}-pesos",
   MercadoLibre sin "_PriceRange_...", ArgenProp sin "--precio-desde-...").

- Las URLs usan max_rent_price en el rango de precio (si es 0, sin rango de precio)
- min_price es SIEMPRE 200000
- Si el usuario no especifica tipo, usá departamentos, ph y casas
- Si no especifica m2 mínimo, usá 30. Los m² son siempre TOTALES (en el summary escribí "m² totales")

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
  "max_rent_price": 800000,
  "max_total_price": 800000,
  "min_m2": 30,
  "barrios": ["Villa Urquiza", "Saavedra"],
  "tipos": ["departamento", "ph", "casa"],
  "min_ambientes": 1,
  "max_ambientes": 3,
  "require_keywords": [],
  "exclude_keywords": [],
  "solo_dueno": false
}
`solo_dueno`: true solo si el usuario pide publicaciones de dueño directo / sin inmobiliarias.
`barrios`: nombres de barrio/localidad tal como se escriben normalmente (con tildes), uno por elemento.
`tipos`: subconjunto de ["departamento", "ph", "casa"].
`min_ambientes`/`max_ambientes`: rango de ambientes pedido (monoambiente = 1); 0 si no se especificó.
"""

async def _groq_chat(messages: list, **params) -> str:
    """Chat completion contra la API de Groq (compatible OpenAI) usando aiohttp,
    sin el SDK de groq (ahorra ~10 MB de RAM)."""
    payload = {"model": "qwen/qwen3.8-27b", "messages": messages, **params}
    headers = {"Authorization": f"Bearer {GROQ_API_KEY}"}
    timeout = aiohttp.ClientTimeout(total=60)
    async with aiohttp.ClientSession(timeout=timeout) as session:
        async with session.post(GROQ_URL, json=payload, headers=headers) as resp:
            if resp.status != 200:
                raise RuntimeError(f"Groq HTTP {resp.status}: {(await resp.text())[:300]}")
            data = await resp.json()
    return data["choices"][0]["message"]["content"] or ""

async def interpret_search(description: str, correction: bool = False) -> dict | None:
    if correction:
        description += ("\n(IMPORTANTE: esto ES una búsqueda de propiedad con una corrección del usuario; "
                        "devolvé la búsqueda completa corregida, nunca no_es_busqueda)")
    text = ""
    for attempt in range(2):
        try:
            text = (await _groq_chat(
                [
                    {"role": "system", "content": GEMINI_PROMPT},
                    {"role": "user",   "content": f"Búsqueda del usuario: {description}"},
                ],
                temperature=0.2,
                max_tokens=4096,
            )).strip()
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
    chat_id = str(update.effective_chat.id)
    name    = html_mod.escape(update.effective_user.first_name or "") if update.effective_user else ""
    hola    = f"¡Hola{', ' + name if name else ''}! 👋"
    user    = load_users().get(chat_id, {})
    alerts  = get_alerts(user)
    if alerts:
        n  = len(alerts)
        pl = "s" if n != 1 else ""
        if user.get("active", True):
            estado = (f"Tenés <b>{n} alerta{pl}</b> activa{pl} y te sigo avisando "
                      "cuando aparecen publicaciones nuevas. Podés verlas con /alertas.")
        else:
            estado = (f"Tenés <b>{n} alerta{pl}</b>, pero las notificaciones están pausadas. "
                      "Se reactivan cuando guardes una búsqueda. Podés verlas con /alertas.")
        await update.message.reply_text(
            f"{hola} Qué bueno verte de nuevo.\n\n{estado}\n\n"
            "Si querés, armamos una búsqueda nueva 👇",
            parse_mode="HTML",
        )
    else:
        await update.message.reply_text(
            f"{hola} Soy tu asistente para encontrar alquiler en Buenos Aires 🏠\n\n"
            "Así funciona:\n"
            "1️⃣ Me contás qué buscás: zona, ambientes, metros y presupuesto.\n"
            "2️⃣ Reviso ZonaProp, ArgenProp, MercadoLibre y Remax cada 15 minutos.\n"
            "3️⃣ Te aviso por acá apenas aparece algo que te sirva.\n\n"
            "Arranquemos 👇",
            parse_mode="HTML",
        )
    return await cmd_buscar(update, ctx, greet=False)

def _map_keyboard():
    return InlineKeyboardMarkup([[
        InlineKeyboardButton("🗺️ Elegir barrios en el mapa", web_app=WebAppInfo(url=f"{WEB_APP_URL}/map"))
    ]])

async def cmd_buscar(update: Update, ctx: ContextTypes.DEFAULT_TYPE, greet: bool = True):
    chat_id = str(update.effective_chat.id)
    hola    = "Hola! " if greet else ""
    users   = load_users()
    saved   = users.get(chat_id, {}).get("zones", [])

    if saved and WEB_APP_URL:
        lista = ", ".join(saved)
        keyboard = InlineKeyboardMarkup([[
            InlineKeyboardButton("✅ Sí, los mismos", callback_data="zones_keep"),
            InlineKeyboardButton("🗺️ Cambiar", web_app=WebAppInfo(url=f"{WEB_APP_URL}/map")),
        ]])
        await update.message.reply_text(
            f"{hola}La última vez buscaste en: <b>{lista}</b>\n\n¿Seguís buscando en esas zonas?",
            parse_mode="HTML",
            reply_markup=keyboard,
        )
        return AWAITING_ZONE_CONFIRM
    elif WEB_APP_URL:
        await update.message.reply_text(
            f"{hola}¿En qué zona de Buenos Aires estás buscando?",
            reply_markup=_map_keyboard(),
        )
        return AWAITING_ZONE_CONFIRM
    else:
        await update.message.reply_text(f"{hola}¿Qué estás buscando? Contame barrios, tipo, tamaño y precio máximo:")
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
        [b("👤 Dueño directo sí/no", "dueno")],
        [b("❌ Cancelar", "cancel")],
    ])

async def _show_edit_menu(send_fn, alert: dict, idx: int):
    aid = alert.get("_id") or str(idx + 1)
    name = alert.get("name") or alert.get("summary", f"Alerta {idx+1}")
    lines = [f"✏️ <b>Editando alerta {idx+1}: {name}</b>", ""]
    if alert.get("min_m2"):
        lines.append(f"📐 Metros mín: {alert['min_m2']} m² totales")
    rent_cap, total_cap = _price_limits(alert)
    if total_cap:
        lines.append(f"💰 Presupuesto máx total: {_fmt_ars(total_cap)}")
    elif rent_cap:
        lines.append(f"💰 Alquiler máx: {_fmt_ars(rent_cap)}")
    if alert.get("require_keywords"):
        lines.append(f"✨ Extras: {', '.join(alert['require_keywords'])}")
    lines.append("👤 Solo dueño directo" if alert.get("solo_dueno") else "🤝 Dueños e inmobiliarias")
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
    # Mensaje nuevo al final del chat: la tarjeta de la alerta en la lista queda igual.
    await _show_edit_menu(
        lambda text, **kw: ctx.bot.send_message(query.message.chat_id, text, **kw),
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

def _alert_params_line(a: dict) -> str:
    """Valores reales de la alerta (no dependen del texto que armó Groq)."""
    parts = []
    if a.get("min_m2"):
        parts.append(f"📐 {a['min_m2']} m² totales mín.")
    rent_cap, total_cap = _price_limits(a)
    if total_cap:
        parts.append(f"💰 hasta {_fmt_ars(total_cap)} total")
    elif rent_cap:
        parts.append(f"💰 hasta {_fmt_ars(rent_cap)} de alquiler")
    if a.get("solo_dueno"):
        parts.append("👤 solo dueño directo")
    return " · ".join(parts)

def _refresh_alert_text(alert: dict, field: str):
    """Actualiza nombre y resumen tras editar m² o presupuesto."""
    name, summary = alert.get("name", ""), alert.get("summary", "")
    if field == "min_m2":
        v = alert["min_m2"]
        summary = re.sub(r"\b\d+\s*m(?:2|²)(?:\s*(?:totales|cubiertos))?", f"{v} m² totales", summary, count=1)
        name    = re.sub(r"\b\d+\s*m(?:2|²)", f"{v}m2", name, count=1)
    elif field == "max_total_price":
        v = alert["max_total_price"]
        k = f"{v / 1_000_000:g}M" if v >= 1_000_000 else f"{v // 1000}k"
        summary = re.sub(r"(?:\$\s?)?\d{1,3}(?:\.\d{3})+(?:\s*ARS)?", f"{v:,} ARS".replace(",", "."), summary, count=1)
        name    = re.sub(r"\b\d+(?:[.,]\d+)?\s*[kKM]\b", k, name, count=1)
    alert["name"], alert["summary"] = name, summary

_SUMMARY_M2_RE = re.compile(
    r",?\s*(?:con\s+)?(?:un\s+)?(?:m[ií]nimo|al\s+menos|de\s+al\s+menos|desde)\s+(?:de\s+)?"
    r"\d+\s*m(?:2|²)(?:\s*(?:totales|cubiertos|cuadrados))?", re.IGNORECASE)
_SUMMARY_PRICE_RE = re.compile(
    r",?\s*(?:y\s+)?(?:con\s+un\s+)?(?:presupuesto\s+)?(?:m[aá]ximo\s+)?(?:de\s+)?hasta\s+(?:\$\s?)?\d[\d.,]*(?:\s*(?:ARS|pesos|k|K|M|mil)\b)*"
    r"(?:\s+(?:incluyendo|con|en\s+total|de\s+alquiler|sin\s+contar|m[aá]s|\+)[^,.;]*)?", re.IGNORECASE)

def _summary_without_params(summary: str) -> str:
    """Resumen sin m² ni precio (se muestran aparte en _alert_params_line)."""
    t = _SUMMARY_PRICE_RE.sub("", _SUMMARY_M2_RE.sub("", summary or ""))
    t = re.sub(r"\s+([,.;])", r"\1", t)
    t = re.sub(r",\s*([.;])", r"\1", t)
    t = re.sub(r"\s{2,}", " ", t).strip(" ,;")
    return t

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
        shown   = dict(a)  # nombre/resumen alineados con los valores reales (alertas viejas)
        if shown.get("min_m2"):
            _refresh_alert_text(shown, "min_m2")
        if _price_limits(shown)[1]:
            shown["max_total_price"] = _price_limits(shown)[1]
            _refresh_alert_text(shown, "max_total_price")
        name    = html_mod.escape(shown.get("name") or shown.get("summary", f"Alerta {i}"))
        summary = html_mod.escape(_summary_without_params(shown.get("summary", "")))
        params  = _alert_params_line(a)
        text    = (f"<b>{i}. {name}</b>" + (f"\n{summary}" if summary and summary != name else "")
                   + (f"\n{params}" if params else ""))
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
    await update.message.reply_text(REJECT_TEXT)

# ── Rechazo de comandos escritos como texto ───────────────────────────────────
# Dentro de un flujo (/buscar, /editar...) se acepta lenguaje natural; solo se
# rechaza un mensaje si ENTERO es un comando. Fuera de un flujo, cualquier texto
# se rechaza (ver receive_description).
_CMD_WORDS = {
    "alerta", "alertas", "buscar", "stop", "estado", "borrar", "borrartodo",
    "editar", "resetseen", "start", "help", "ayuda", "comando", "comandos",
    "menu", "inicio", "opciones", "pausar",
}
# Mensajes completos que son comandos o no son búsquedas (saludos, etc.).
_NON_SEARCH_MSGS = {
    "nueva alerta", "mis alertas", "ver alertas", "ver mis alertas", "borrar todo",
    "hola", "holaa", "buenas", "buen dia", "buenos dias", "buenas tardes",
    "buenas noches", "hey", "hi", "hello", "gracias", "muchas gracias",
    "chau", "adios", "info",
}
_CMD_RE = re.compile(r"(?:%s)(?: \d+)?" % "|".join(sorted(_CMD_WORDS)))

REJECT_TEXT = "Eso no es una búsqueda.\n\n" + COMMANDS_TEXT

def _is_command_like(text: str) -> bool:
    """True si el mensaje entero es un comando (ej: "alertas", "borrar 1", "/stop")
    o un saludo suelto. Frases en lenguaje natural devuelven False."""
    t = _norm(text)
    if t.startswith("/"):
        return True
    t = re.sub(r"[^\w\s]", " ", t)
    t = re.sub(r"\s+", " ", t).strip()
    return not t or t in _NON_SEARCH_MSGS or bool(_CMD_RE.fullmatch(t))

async def reject_command_like(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Corre antes que cualquier otro handler: si el texto es un comando, lo
    rechaza mostrando la lista de comandos y corta el procesamiento."""
    msg = update.message
    if msg and msg.text and _is_command_like(msg.text):
        await msg.reply_text(REJECT_TEXT)
        raise ApplicationHandlerStop

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

    if data == "ef_dueno":   # alterna solo dueño directo / indistinto
        users  = load_users()
        alerts = get_alerts(users.get(chat_id)) if users.get(chat_id) else []
        idx    = _find_alert_idx(alerts, aid) if aid else -1
        if idx is None or idx < 0 or idx >= len(alerts):
            await query.edit_message_text("⚠️ Esa alerta ya no existe. Usá /alertas para ver las actuales.")
            return ConversationHandler.END
        alerts[idx]["solo_dueno"] = not alerts[idx].get("solo_dueno")
        save_users(users)
        await query.edit_message_text(
            "👤 Ahora solo te mando publicaciones de <b>dueño directo</b>." if alerts[idx]["solo_dueno"]
            else "🤝 Ahora te mando publicaciones de <b>dueños e inmobiliarias</b>.", parse_mode="HTML")
        return ConversationHandler.END

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
        "ef_m2":        ("min_m2",           "¿Cuántos m² <b>totales</b> mínimo?\nEj: <b>35</b>, <b>40</b>"),
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
    labels = {"ef_m2": "Metros mínimos", "ef_precio": "Presupuesto", "ef_extras": "Extras",
              "ef_tipo": "Tipo de propiedad", "ef_ambientes": "Ambientes", "ef_zona": "Zona"}
    name = alerts[idx].get("name") or alerts[idx].get("summary", f"Alerta {idx+1}")
    # El menú queda como resumen (sin botones) y la pregunta va al final del chat.
    await query.edit_message_text(
        f"✏️ Editando alerta {idx+1}: <b>{html_mod.escape(name)}</b> → {labels.get(data, '')}",
        parse_mode="HTML",
    )
    await ctx.bot.send_message(query.message.chat_id, prompt, parse_mode="HTML")
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
        _refresh_alert_text(alert, "min_m2")
        save_users(users)
        await update.message.reply_text(f"Metros mínimos actualizado a <b>{alert['min_m2']} m² totales</b>.", parse_mode="HTML")
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
        alert["max_rent_price"]  = val
        alert["_expensas_incluidas"] = True
        _refresh_alert_text(alert, "max_total_price")
        save_users(users)
        await update.message.reply_text(f"Presupuesto máximo actualizado a <b>{_fmt_ars(val)}</b>.", parse_mode="HTML")
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

def _tipo_keyboard(prefix: str = "tipo_") -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[
        InlineKeyboardButton("🏢 Depto",       callback_data=f"{prefix}depto"),
        InlineKeyboardButton("🏠 Casa o PH",   callback_data=f"{prefix}casaph"),
        InlineKeyboardButton("✅ Cualquiera",  callback_data=f"{prefix}todos"),
    ]])

async def _start_wizard(msg, ctx: ContextTypes.DEFAULT_TYPE):
    """Begin the wizard: ask for property type. `msg` is a Message object."""
    ctx.user_data.pop("wizard", None)
    await msg.reply_text("¿Qué tipo de propiedad buscás?", reply_markup=_tipo_keyboard())
    return AWAITING_TIPO

async def handle_wizard_tipo(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    tipo_map = {
        "tipo_depto": "departamento",
        "tipo_casa":  "casa",
        "tipo_ph":    "PH",
        "tipo_casaph": "casa o PH",
        "tipo_todos": "departamento, PH o casa",
    }
    label_map = {
        "tipo_depto": "🏢 Departamento",
        "tipo_casa":  "🏠 Casa",
        "tipo_ph":    "🏘️ PH",
        "tipo_casaph": "🏠 Casa o PH",
        "tipo_todos": "✅ Cualquier tipo",
    }
    key  = "tipo_" + query.data.split("_", 1)[1]   # tipo_x o maptipo_x
    tipo = tipo_map.get(key, "departamento, PH o casa")
    ctx.user_data.setdefault("wizard", {})["tipo"] = tipo
    await query.edit_message_text(label_map.get(key, "✅ Cualquier tipo"))
    await query.message.reply_text(
        "¿Cuántos ambientes buscás?\n"
        "Ej: <b>2</b>, <b>2 a 3</b>, <b>3+</b>, <b>monoambiente</b>",
        parse_mode="HTML",
    )
    return AWAITING_AMBIENTES

async def handle_map_tipo(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Tipo elegido después de seleccionar barrios en el mapa (/submit-zones)."""
    chat_id = str(update.callback_query.message.chat_id)
    users   = load_users()
    user    = users.get(chat_id, {})
    if user.get("_wizard_step") != "tipo":   # botón viejo
        await update.callback_query.answer()
        return ConversationHandler.END
    user.pop("_wizard_step", None)
    save_users(users)
    ctx.user_data.pop("wizard", None)
    ctx.user_data["barrios_mapa"] = user.get("zones", [])
    return await handle_wizard_tipo(update, ctx)

async def handle_wizard_ambientes(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    ctx.user_data.setdefault("wizard", {})["ambientes"] = update.message.text.strip()
    await update.message.reply_text(
        "¿Superficie mínima en m² <b>totales</b>?\n"
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
        "¿Querés solo publicaciones de <b>dueño directo</b>?",
        parse_mode="HTML",
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("👤 Solo dueño directo", callback_data="dueno_si"),
            InlineKeyboardButton("🤝 Indistinto",         callback_data="dueno_no"),
        ]]),
    )
    return AWAITING_DUENO

async def handle_wizard_dueno(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    solo = query.data == "dueno_si"
    ctx.user_data.setdefault("wizard", {})["solo_dueno"] = solo
    await query.edit_message_text("👤 Solo dueño directo" if solo else "🤝 Dueño directo o inmobiliaria")
    await query.message.reply_text(
        "¿Necesitás algo especial?\n"
        "Ej: <b>cochera</b>, <b>balcón</b>, <b>luminoso</b>, <b>terraza</b> "
        "(o escribí <b>no</b> si no hay nada más)",
        parse_mode="HTML",
    )
    return AWAITING_EXTRAS

async def handle_wizard_dueno_text(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("Elegí una de las dos opciones de arriba 👆")
    return AWAITING_DUENO

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
        parts.append(f"con al menos {wizard['metros']} m2 totales")
    if wizard.get("precio_raw"):
        sufijo = " incluyendo expensas" if wizard.get("expensas_incluidas") else " solo de alquiler"
        parts.append(f"hasta {wizard['precio_raw']}{sufijo}")
    if wizard.get("extras"):
        parts.append(f"que tenga {wizard['extras']}")
    if wizard.get("solo_dueno"):
        parts.append("solo de dueño directo")

    desc = ", ".join(parts)
    if zones:
        desc = f"Zonas preferidas del usuario: {', '.join(zones)}. " + desc

    ctx.user_data["last_desc"] = desc
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
    result["solo_dueno"] = bool(wizard.get("solo_dueno"))

    return await _show_confirmation(update, ctx, result)

async def _show_confirmation(update: Update, ctx: ContextTypes.DEFAULT_TYPE, result: dict):
    """Save pending result and show confirmation with price note."""
    ctx.user_data["pending"] = result
    rent_cap, total_cap = _price_limits(result)
    fmt = lambda v: f"${v:,.0f}".replace(",", ".")
    if total_cap:
        price_note = f"💰 Precio: hasta {fmt(total_cap)} en total (alquiler + expensas)"
    elif rent_cap:
        price_note = f"💰 Precio: hasta {fmt(rent_cap)} de alquiler, sin contar expensas"
    else:
        price_note = "💰 Precio: sin tope (no indicaste un máximo)"
    msg = f"Esto es lo que entendí:\n\n<b>{result['summary']}</b>\n\n"
    if price_note:
        msg += f"{price_note}\n\n"
    msg += "¿Confirmás? Respondé <b>si</b> o <b>no</b>."
    await update.message.reply_text(msg, parse_mode="HTML")
    return AWAITING_CONFIRMATION

# ── Entry point: routes to wizard or free-text ────────────────────────────────

class _MapWizardPending(filters.MessageFilter):
    """Matches only when the map (/submit-zones) left this chat waiting for the
    'ambientes' answer. Needed because the ConversationHandler has
    allow_reentry=True, so entry points are checked BEFORE the current state's
    handlers: a catch-all text entry point would swallow every wizard answer."""
    def filter(self, message) -> bool:
        return load_users().get(str(message.chat_id), {}).get("_wizard_step") in ("ambientes", "tipo")

MAP_WIZARD_PENDING = _MapWizardPending()

async def receive_description(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Plain text outside a flow. Only continues if /submit-zones (map) set a wizard
    step; otherwise the message is rejected with the command list."""
    chat_id = str(update.effective_chat.id)
    step = load_users().get(chat_id, {}).get("_wizard_step")
    if step == "tipo":
        await update.message.reply_text("Elegí el tipo de propiedad con los botones de arriba 👆")
        return None
    if step == "ambientes":
        # Clear the flag (PTB takes over from here)
        users = load_users()
        users[chat_id].pop("_wizard_step", None)
        save_users(users)
        # barrios already saved; load them into user_data
        ctx.user_data["barrios_mapa"] = users[chat_id].get("zones", [])
        return await handle_wizard_ambientes(update, ctx)
    # Texto suelto fuera de un flujo conversacional: no es una búsqueda.
    await update.message.reply_text(REJECT_TEXT)
    return ConversationHandler.END

async def receive_description_in_flow(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Plain text while /buscar asks about zones: map wizard step or free-text search."""
    chat_id = str(update.effective_chat.id)
    if load_users().get(chat_id, {}).get("_wizard_step") == "ambientes":
        return await receive_description(update, ctx)
    return await _receive_description_freetext(update, ctx)

async def _receive_description_freetext(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    desc         = update.message.text.strip()
    chat_id      = str(update.effective_chat.id)
    previous     = ctx.user_data.pop("correcting", None) and ctx.user_data.get("last_desc")
    if previous:
        # Corrección de la búsqueda anterior: se mantiene todo lo demás.
        combined = (
            f"{previous}\nCorrección del usuario (aplicala y mantené todo lo demás igual, "
            f"incluido el precio si no lo cambia): {desc}"
        )
        await update.message.reply_text("Un segundo, estoy aplicando el cambio...")
        result = await interpret_search(combined, correction=True)
        if result and result.get("no_es_busqueda"):
            log.warning("Groq devolvió no_es_busqueda para una corrección, reintento: %r", desc)
            result = await interpret_search(combined, correction=True)
        if result and not result.get("no_es_busqueda"):
            ctx.user_data["last_desc"] = combined
            _keep_uncorrected(result, ctx.user_data.get("prev_result") or {}, desc,
                              ctx.user_data.get("wizard", {}).get("expensas_incluidas"))
            return await _show_confirmation(update, ctx, result)
        log.error("No se pudo aplicar la corrección %r (resultado: %r)", desc, result)
        ctx.user_data["correcting"] = True   # sigue la búsqueda anterior
        await update.message.reply_text(
            "No pude aplicar ese cambio. Probá escribirlo de otra forma; lo demás sigue igual.\n"
            "Ej: <i>2 ambientes o más</i>, <i>que sea casa o PH</i>, <i>hasta 1M</i>",
            parse_mode="HTML",
        )
        return AWAITING_DESCRIPTION
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
    ctx.user_data["last_desc"] = desc
    await update.message.reply_text("Un segundo, estoy interpretando tu búsqueda...")
    result = await interpret_search(desc)
    if result and result.get("no_es_busqueda"):
        ctx.user_data.pop("pending", None)
        await update.message.reply_text(REJECT_TEXT)
        return ConversationHandler.END
    if not result:
        await update.message.reply_text(
            "No pude interpretar la búsqueda. "
            "¿Podés aclarar qué barrios, tipo de propiedad y precio máximo buscás?"
        )
        return AWAITING_DESCRIPTION
    return await _show_confirmation(update, ctx, result)

_CORR_PRICE_RE = re.compile(
    r"precio|presupuesto|\$|mill|expensa|alquiler|plata|pesos|"
    r"\d+(?:[.,]\d+)?\s*(?:k|mil|m)\b|\d{3,}(?:\.\d{3})*(?!\s*(?:m2|m²|metro|mts))", re.IGNORECASE)
_CORR_M2_RE    = re.compile(r"m2|m²|metro|mts|superficie", re.IGNORECASE)

_CORR_MODE_RE = re.compile(r"alquiler|expensa|total|todo\s+incluido", re.IGNORECASE)

def _keep_uncorrected(result: dict, prev: dict, correction: str, total_default: bool | None = None):
    """Tras una corrección, lo que el usuario no mencionó queda como antes
    (sin depender de que Groq lo respete): precio, modo del precio y m² mínimos.
    `total_default`: modo del wizard si la búsqueda anterior no tenía precio."""
    if not prev:
        return
    if _CORR_PRICE_RE.search(correction) and not _CORR_MODE_RE.search(correction):
        # Cambió el monto pero no dijo si es total o de alquiler: se mantiene el modo.
        prev_total = bool(_price_limits(prev)[1]) if _price_limits(prev)[0] else total_default
        amount = max(result.get("max_total_price") or 0, result.get("max_rent_price") or 0)
        if amount and prev_total is not None:
            result["max_rent_price"] = amount
            result["max_total_price"] = amount if prev_total else 0
            result["_expensas_incluidas"] = prev_total
    elif not _CORR_PRICE_RE.search(correction):
        for k in ("max_rent_price", "max_total_price", "min_price", "_expensas_incluidas"):
            if k in prev:
                result[k] = prev[k]
            else:
                result.pop(k, None)
        if _price_limits(result)[1]:
            _refresh_alert_text(result, "max_total_price")
    if "solo_dueno" in prev:
        if re.search(r"due[ñn]o|particular", correction, re.IGNORECASE):
            result["solo_dueno"] = not re.search(r"\bno\b|indistinto|cualquiera|tambi[eé]n\s+inmobiliaria", correction, re.IGNORECASE)
        elif re.search(r"inmobiliaria|indistinto", correction, re.IGNORECASE):
            result["solo_dueno"] = False
        else:
            result["solo_dueno"] = prev["solo_dueno"]
    if not _CORR_M2_RE.search(correction) and prev.get("min_m2"):
        result["min_m2"] = prev["min_m2"]
        _refresh_alert_text(result, "min_m2")

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
        ctx.user_data["initial_alert_id"] = alert.get("_id")
        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton("📬 Última semana + las nuevas", callback_data="initial_week")],
            [InlineKeyboardButton("🔔 Solo las nuevas", callback_data="initial_new")],
        ])
        await update.message.reply_text(
            f"✅ Alerta guardada: <b>{html_mod.escape(alert.get('name') or alert.get('summary', ''))}</b>\n\n"
            "En los dos casos te aviso de cada publicación nueva que aparezca. "
            "¿Querés además las que ya están publicadas?\n"
            "• <b>Última semana + las nuevas</b>: ahora te mando las de los últimos 7 días.\n"
            "• <b>Solo las nuevas</b>: ahora no te mando nada.",
            parse_mode="HTML",
            reply_markup=kb,
        )
        return AWAITING_INITIAL_SEND

    if text in ("no", "n"):
        if ctx.user_data.get("last_desc"):
            ctx.user_data["correcting"] = True
            ctx.user_data["prev_result"] = ctx.user_data.get("pending", {})
            await update.message.reply_text(
                "¿Qué querés cambiar? Lo demás queda igual.\n"
                "Ej: <i>que sea casa o PH</i>, <i>hasta 1M</i>, <i>agregá Saavedra</i>",
                parse_mode="HTML",
            )
        else:
            await update.message.reply_text("Contame de nuevo qué estás buscando. Podés ser más específico.")
        return AWAITING_DESCRIPTION

    await update.message.reply_text("Respondé <b>si</b> o <b>no</b>.", parse_mode="HTML")
    return AWAITING_CONFIRMATION

async def handle_initial_send(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Botones tras guardar una alerta: mandar la última semana o solo las nuevas."""
    query   = update.callback_query
    chat_id = str(query.message.chat_id)
    await query.answer()
    only_new = query.data == "initial_new"
    aid      = ctx.user_data.pop("initial_alert_id", None)
    send     = lambda text: ctx.bot.send_message(query.message.chat_id, text)
    if not aid:  # botón viejo
        await query.edit_message_reply_markup(reply_markup=None)
        return ConversationHandler.END
    await query.edit_message_text(
        query.message.text_html.split("\n\n")[0] + "\n\n" +
        ("🔔 Te aviso solo de las nuevas." if only_new else "📬 Buscando las de la última semana..."),
        parse_mode="HTML",
    )
    users = load_users()
    user  = users.get(chat_id, {})
    count = await scrape_user(ctx.application, chat_id, user, only_alert=aid,
                              silent=only_new, max_age=INITIAL_SEND_DAYS)
    save_users(users)
    release_memory()
    if only_new:
        await send("Listo. Voy a revisar cada 15 minutos y te aviso apenas aparezca algo nuevo.")
    elif count == 0:
        await send("No encontré publicaciones de la última semana que coincidan. "
                   "Voy a revisar cada 15 minutos y te aviso cuando aparezca algo nuevo.")
    else:
        await send(f"Te mandé {count} publicación(es) de la última semana. "
                   "Voy a revisar cada 15 minutos y te aviso cuando haya algo nuevo.")
    await send("💡 Podés usar /alertas para ver, editar o borrar tus alertas en cualquier momento.")
    await send("¿Querés agregar otra alerta con distintos criterios? (si/no)")
    return AWAITING_MORE_ALERTS

async def handle_initial_send_text(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("Elegí una de las dos opciones de arriba 👆")
    return AWAITING_INITIAL_SEND

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
async def scrape_user(app: Application, chat_id: str, user: dict, only_alert: str | None = None,
                      silent: bool = False, max_age: int = MAX_LISTING_AGE_DAYS) -> int:
    """Scrape the user's alerts (or only `only_alert`, by _id). Returns how many
    new listings were sent. With silent=True nothing is sent: every listing
    currently published is marked as seen, so only future ones are notified."""
    seen  = set(user.get("seen", []))
    total = 0
    loop  = asyncio.get_event_loop()

    for alert in get_alerts(user):
        if only_alert and alert.get("_id") != only_alert:
            continue
        sources = (
            [("zonaprop",     _apply_alert_params(u, alert)) for u in alert.get("zonaprop_urls", [])]
            + [("argenprop",  u) for u in [argenprop_url(alert, remax_params(alert, user))] if u]
            + [("mercadolibre", _apply_alert_params(u, alert)) for u in alert.get("mercadolibre_urls", [])]
            + ([] if alert.get("solo_dueno") else [("remax", None)])   # Remax: solo inmobiliarias
        )
        for scraper_name, url in sources:
            if scraper_name == "zonaprop":
                listings = scrape_zonaprop(url)
            elif scraper_name == "remax":
                listings = scrape_remax(alert, remax_params(alert, user))
            elif scraper_name == "argenprop":
                listings = scrape_argenprop(url)
                if "/dueno-directo/" in (url or ""):
                    for l in listings:
                        l["owner"] = True   # ya filtrado por ArgenProp
                    log.info("[ArgenProp] dueño directo: %d listings", len(listings))
            else:
                listings = scrape_mercadolibre(url)

            if silent:
                seen.update(l["id"] for l in listings)
                continue

            detail = DETAIL_EXPENSES.get(scraper_name)
            if detail:
                # Expensas sin informar en el listado: se revisa la publicación
                # (campo + descripción). Solo nuevas y que entren por alquiler.
                rent_cap  = _price_limits(alert)[0]
                need_owner = alert.get("solo_dueno") and scraper_name == "mercadolibre"
                for l in listings:
                    if l["id"] in seen or (rent_cap and _parse_price(l["price"]) > rent_cap):
                        continue
                    if (l["expenses"] or l.get("expenses_note")) and not need_owner:
                        continue
                    info = await loop.run_in_executor(None, lambda link=l["link"], f=detail: f(link))
                    if info and not (l["expenses"] or l.get("expenses_note")):
                        l["expenses"], l["expenses_note"] = info
                    if scraper_name == "mercadolibre":
                        l["owner"] = _ml_owner_cache.pop(l["link"], None)

            for l in listings:
                l.setdefault("tipo", _infer_tipo(l["link"], url or ""))
            listings = filter_listings(listings, alert, max_age)
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
    release_memory()
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
    users[chat_id_str]["_wizard_step"] = "tipo"
    save_users(users)
    if _BOT_APP:
        await _BOT_APP.bot.send_message(
            chat_id=chat_id,
            text=f"Perfecto, <b>{html_mod.escape(lista)}</b>.",
            parse_mode="HTML",
        )
        await _BOT_APP.bot.send_message(
            chat_id=chat_id,
            text="¿Qué tipo de propiedad buscás?",
            reply_markup=_tipo_keyboard("maptipo_"),
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
            # Solo para la respuesta de ambientes tras elegir barrios en el mapa.
            # Cualquier otro texto fuera de un flujo cae en fallback_unknown.
            MessageHandler(filters.TEXT & ~filters.COMMAND & MAP_WIZARD_PENDING, receive_description),
            CallbackQueryHandler(handle_map_tipo, pattern="^maptipo_(depto|casaph|todos)$"),
        ],
        states={
            AWAITING_ZONE_CONFIRM: [
                CallbackQueryHandler(handle_zone_confirm, pattern="^zones_keep$"),
                MessageHandler(filters.StatusUpdate.WEB_APP_DATA, handle_web_app_data),
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_description_in_flow),
            ],
            AWAITING_DESCRIPTION:  [
                MessageHandler(filters.StatusUpdate.WEB_APP_DATA, handle_web_app_data),
                MessageHandler(filters.TEXT & ~filters.COMMAND, _receive_description_freetext),
            ],
            AWAITING_TIPO:         [CallbackQueryHandler(handle_wizard_tipo, pattern="^tipo_(depto|casa|ph|casaph|todos)$")],
            AWAITING_AMBIENTES:    [MessageHandler(filters.TEXT & ~filters.COMMAND, handle_wizard_ambientes)],
            AWAITING_METROS:       [MessageHandler(filters.TEXT & ~filters.COMMAND, handle_wizard_metros)],
            AWAITING_PRECIO:       [MessageHandler(filters.TEXT & ~filters.COMMAND, handle_wizard_precio)],
            AWAITING_DUENO:        [
                CallbackQueryHandler(handle_wizard_dueno, pattern="^dueno_(si|no)$"),
                MessageHandler(filters.TEXT & ~filters.COMMAND, handle_wizard_dueno_text),
            ],
            AWAITING_EXTRAS:       [MessageHandler(filters.TEXT & ~filters.COMMAND, handle_wizard_extras)],
            AWAITING_CONFIRMATION: [MessageHandler(filters.TEXT & ~filters.COMMAND, handle_confirmation)],
            AWAITING_INITIAL_SEND: [
                CallbackQueryHandler(handle_initial_send, pattern="^initial_(week|new)$"),
                MessageHandler(filters.TEXT & ~filters.COMMAND, handle_initial_send_text),
            ],
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

    # Grupo -1: se evalúa antes que la conversación y los comandos.
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, reject_command_like), group=-1)
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
