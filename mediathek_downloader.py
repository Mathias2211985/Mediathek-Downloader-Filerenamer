# -*- coding: utf-8 -*-
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
try:
    from tkinterdnd2 import TkinterDnD, DND_FILES
    HAS_DND = True
except ImportError:
    HAS_DND = False

try:
    from PIL import Image, ImageTk
    import io as _io
    HAS_PIL = True
except ImportError:
    HAS_PIL = False
import requests
import threading
import os
import sys
import re
import time
import subprocess
import json
import shutil
import hashlib
import uuid
import collections
import difflib
import unicodedata
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime

API_URL        = "https://mediathekviewweb.de/api/query"
ARD_SEARCH_URL = "https://api.ardmediathek.de/search/vods"
ARD_ITEM_URL   = "https://api.ardmediathek.de/item/{id}?devicetype=pc&embedded=false"
ZDF_PORTAL_URL = "https://www.zdf.de"
ZDF_API_URL    = "https://api.zdf.de"

# Watchlist neben der .exe / .py speichern
BASE_DIR = os.path.dirname(sys.executable if getattr(sys, "frozen", False)
                           else os.path.abspath(__file__))
WATCHLIST_FILE = os.path.join(BASE_DIR, "watchlist.json")
HASH_FILE      = os.path.join(BASE_DIR, "downloaded_hashes.txt")

CHANNELS = [
    "Alle", "ARD", "ZDF", "3Sat", "Arte", "BR", "HR", "MDR",
    "NDR", "RBB", "SR", "SWR", "WDR", "ORF", "SRF", "PHOENIX",
    "KIKA", "ZDFinfo", "ZDFneo", "ONE", "tagesschau24"
]

# Serien-Aliase für das Einsortieren nach dem Umbenennen.
# Links: Serienname wie er im Dateinamen steht, rechts: gewünschter Ordnername.
# Erweiterbar – einfach neue Zeilen hinzufügen.
# Die ID wird NICHT hier eingetragen – sie kommt aus der Zuordnung und wird
# beim Einsortieren als "{tvdb-…}" angehängt (Einstellung "Serien-ID im
# Ordnernamen"). Nur reine Namen hier, sonst entstehen zwei Schemata.
SERIEN_ALIAS: dict[str, str] = {
    "Hubert ohne Staller": "Hubert und Staller",
    "Hubert und Staller":  "Hubert und Staller",
}

LANG_OPTIONS = ["Alle", "Deutsch", "OV (Originalversion)", "OmU (mit UT)", "Sorbisch"]

# Schlüsselwörter im Titel für Sprachfilterung
_OV_TERMS       = ("(ov)", "(originalversion)", "(originalsprache)", "(englisch)",
                   "(englische fassung)", "(of)")
_OMU_TERMS      = ("(omu)", "(ot)", "(ut)", "mit untertiteln", "mit deutschen untertiteln")
_ACCESS_TERMS   = ("hörgeschädigte", "gebärdensprache", "hörfassung", "audiodeskription")
_MINORITY_TERMS = ("pěskowčik", "hornjoserbski", "dolnoserbski", "sorbisch",
                   "obersorbisch", "niedersorbisch", "hornoso")


def _classify_language(title_lower):
    if any(t in title_lower for t in _ACCESS_TERMS):   return "Barrierefreiheit"
    if any(t in title_lower for t in _OV_TERMS):       return "OV"
    if any(t in title_lower for t in _OMU_TERMS):      return "OmU"
    if any(t in title_lower for t in _MINORITY_TERMS): return "Sorbisch"
    return "Deutsch"


def _apply_language_filter(results, lang):
    if not lang or lang == "Alle":
        return results
    out = []
    for r in results:
        cat = _classify_language(r.get("title", "").lower())
        if lang.startswith("OV")    and cat == "OV":           out.append(r)
        elif lang.startswith("OmU") and cat == "OmU":          out.append(r)
        elif lang == "Sorbisch"     and cat == "Sorbisch":     out.append(r)
        elif lang == "Deutsch"      and cat == "Deutsch":      out.append(r)
    return out


QUALITY_HELP = (
    "HD     → beste Qualität (fällt auf Normal zurück falls HD fehlt)\n"
    "Normal → Standard-Qualität (fällt auf SD zurück falls nötig)\n"
    "SD     → kleinste Datei, niedrigste Qualität"
)

STATUS_ICON = {
    "waiting":     "⏳ Wartend",
    "downloading": "⬇ Lädt …",
    "done":        "✓ Fertig",
    "error":       "✗ Fehler",
    "skipped":     "⏭ Übersprungen",
}
STATUS_TAG = {
    "waiting": "st_wait", "downloading": "st_dl",
    "done": "st_done",    "error": "st_err", "skipped": "st_skip",
}

# ═══════════════════════════════════════════════════════════════════════════════
# Hilfsfunktionen
# ═══════════════════════════════════════════════════════════════════════════════

def _pick_url(item, quality):
    if quality == "HD":
        return (item.get("url_video_hd") or item.get("url_video") or item.get("url_video_sd"))
    if quality == "SD":
        return (item.get("url_video_sd") or item.get("url_video"))
    return (item.get("url_video") or item.get("url_video_hd") or item.get("url_video_sd"))


# Trennende verbotene Zeichen werden durch ein Leerzeichen ersetzt, nicht
# gelöscht – sonst kleben Wörter zusammen. TheTVDB nennt z.B. die Serie
# "Hubert und/ohne Staller"; Löschen ergab daraus "Hubert undohne Staller".
_ILLEGAL_SEP_RE   = re.compile(r'[\\/:|]')
_ILLEGAL_DROP_RE  = re.compile(r'[*?"<>\x00-\x1f]')
# Rückwärtskompatibler Name (wird an anderen Stellen referenziert)
_ILLEGAL_CHARS_RE = re.compile(r'[\\/:*?"<>|\x00-\x1f]')

def _safe_str(s, max_len=120, **_):
    s = unicodedata.normalize("NFC", str(s))
    s = _ILLEGAL_SEP_RE.sub(' ', s)
    s = _ILLEGAL_DROP_RE.sub('', s)
    s = re.sub(r' {2,}', ' ', s)
    return s.strip('. ')[:max_len]


def _safe_filename(title):
    return _safe_str(title)


def _safe_dirname(topic, max_len=60):
    raw = topic.strip() if topic.strip() else "Sonstiges"
    return _safe_str(raw, max_len)


def _item_hash(item):
    """Eindeutiger Hash pro Folge für Watchlist-Tracking."""
    key = "|".join([
        item.get("channel", ""),
        item.get("topic",   ""),
        item.get("title",   ""),
        str(item.get("timestamp", "")),
    ])
    return hashlib.md5(key.encode()).hexdigest()[:16]


# ── ARD Mediathek ─────────────────────────────────────────────────────────────

def _ard_resolve_streams(item_id):
    try:
        url  = ARD_ITEM_URL.format(id=item_id)
        resp = requests.get(url, timeout=15, headers={"Accept": "application/json"})
        data = resp.json()
        embedded  = (data.get("mediaCollection") or {}).get("embedded") or {}
        streams   = embedded.get("streams", [])
        main      = next((s for s in streams if s.get("kind") == "main"), None) or \
                    (streams[0] if streams else {})
        media     = main.get("media", [])
        mp4s      = [m for m in media if "mp4" in m.get("mimeType", "").lower()]
        mp4s.sort(key=lambda m: m.get("maxHResolutionPx") or 0)
        url_sd    = mp4s[0].get("url", "")  if mp4s          else ""
        url_hd    = mp4s[-1].get("url", "") if len(mp4s) > 1 else url_sd
        if not url_sd:
            hls    = [m for m in media if "mpegURL" in m.get("mimeType", "")]
            url_sd = url_hd = (hls[0].get("url", "") if hls else "")
        subs         = embedded.get("subtitles", [])
        url_subtitle = subs[0].get("url", "") if subs else ""
        return url_sd, url_hd, url_subtitle
    except Exception:
        return "", "", ""


def _search_ard(topic, channel="Alle", size=100):
    try:
        params = {"searchString": topic, "pageNumber": 0, "pageSize": min(size, 100)}
        resp   = requests.get(ARD_SEARCH_URL, params=params, timeout=20,
                              headers={"Accept": "application/json"})
        resp.raise_for_status()
        items  = resp.json().get("_embedded", {}).get("mt:item", []) or []
    except Exception:
        return []
    results = []
    with ThreadPoolExecutor(max_workers=10) as pool:
        id_map = {it["id"]: it for it in items if it.get("id")}
        futs   = {pool.submit(_ard_resolve_streams, iid): iid for iid in id_map}
        for fut, iid in futs.items():
            item = id_map[iid]
            try:
                url_sd, url_hd, url_sub = fut.result(timeout=20)
            except Exception:
                continue
            if not url_sd and not url_hd:
                continue
            embedded   = item.get("_embedded", {})
            show       = embedded.get("mt:show") or item.get("show") or {}
            pub_svc    = embedded.get("mt:publicationService") or item.get("publicationService") or {}
            topic_name = show.get("longTitle") or show.get("title") or topic
            ch_name    = pub_svc.get("name") or "ARD"
            ts = 0
            bd = item.get("broadcastedOn", "")
            if bd:
                try:
                    ts = int(datetime.fromisoformat(bd.replace("Z", "+00:00")).timestamp())
                except Exception:
                    pass
            results.append({
                "topic": topic_name, "title": item.get("title", ""),
                "channel": ch_name, "timestamp": ts,
                "duration": item.get("duration", 0) or 0,
                "url_video": url_sd, "url_video_hd": url_hd,
                "url_video_sd": url_sd, "url_subtitle": url_sub,
                "_source": "ARD",
            })
    return results


# ── ZDF Mediathek ─────────────────────────────────────────────────────────────

_zdf_api_key  = None
_zdf_key_lock = threading.Lock()


def _get_zdf_api_key():
    global _zdf_api_key
    with _zdf_key_lock:
        if _zdf_api_key:
            return _zdf_api_key
        try:
            resp = requests.get(ZDF_PORTAL_URL + "/", timeout=15,
                                headers={"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                                         "AppleWebKit/537.36 Chrome/120.0.0.0 Safari/537.36"})
            m = re.search(r'"apiToken"\s*:\s*"([^"\s]{10,})"', resp.text)
            if m:
                _zdf_api_key = m.group(1)
        except Exception:
            pass
    return _zdf_api_key


def _zdf_resolve_streams(ptmd_url, key):
    try:
        url  = (ptmd_url.replace("{playerId}", "ngplayer_2_3")
                        .replace("%7BplayerId%7D", "ngplayer_2_3"))
        resp = requests.get(url, timeout=15,
                            headers={"Api-Auth": f"Bearer {key}",
                                     "Accept": "application/vnd.de.zdf.v1.0+json"})
        data   = resp.json()
        plist  = data.get("priorityList", [])
        url_sd = url_hd = ""
        for priority in plist:
            for fmt in priority.get("formitaeten", []):
                if "mp4" not in fmt.get("mimeType", "").lower():
                    continue
                u = fmt.get("url", "")
                if not u:
                    continue
                q = fmt.get("quality", "").lower()
                if q in ("high", "veryhigh", "hd", "uhd"):
                    url_hd = url_hd or u
                else:
                    url_sd = url_sd or u
        url_sd = url_sd or url_hd
        url_hd = url_hd or url_sd
        url_sub = ""
        for cap in data.get("captions", []):
            if cap.get("format", "").lower() in ("webvtt", "vtt", "xml"):
                url_sub = cap.get("uri", "")
                break
        return url_sd, url_hd, url_sub
    except Exception:
        return "", "", ""


def _search_zdf(topic, channel="Alle", size=100):
    key = _get_zdf_api_key()
    if not key:
        return []
    try:
        headers  = {"Api-Auth": f"Bearer {key}",
                    "Accept": "application/vnd.de.zdf.v1.0+json"}
        params   = {"q": topic, "contentTypes": "episode",
                    "limit": min(size, 100), "offset": 0}
        resp     = requests.get(f"{ZDF_API_URL}/search/documents",
                                params=params, headers=headers, timeout=20)
        resp.raise_for_status()
        raw_list = resp.json().get("http://zdf.de/rels/results/results", [])
    except Exception:
        return []
    results = []
    with ThreadPoolExecutor(max_workers=10) as pool:
        ptmd_map = {}
        for item in raw_list:
            ptmd = item.get("http://zdf.de/rels/streams/ptmd-template", "")
            if ptmd:
                ptmd_map[pool.submit(_zdf_resolve_streams, ptmd, key)] = item
        for fut, item in ptmd_map.items():
            try:
                url_sd, url_hd, url_sub = fut.result(timeout=20)
            except Exception:
                continue
            if not url_sd and not url_hd:
                continue
            brand      = item.get("http://zdf.de/rels/brand") or {}
            topic_name = brand.get("title") or topic
            ts = 0
            ed = item.get("editorialDate", "")
            if ed:
                try:
                    ts = int(datetime.fromisoformat(ed).timestamp())
                except Exception:
                    pass
            results.append({
                "topic": topic_name, "title": item.get("title", ""),
                "channel": item.get("tvService", "ZDF"), "timestamp": ts,
                "duration": item.get("duration", 0) or 0,
                "url_video": url_sd, "url_video_hd": url_hd,
                "url_video_sd": url_sd, "url_subtitle": url_sub,
                "_source": "ZDF",
            })
    return results


def _merge_deduplicate(primary, *extras):
    seen = set()
    out  = []
    def _key(item):
        d = item.get("timestamp", 0)
        date_str = datetime.fromtimestamp(d).strftime("%Y-%m-%d") if d else ""
        return (item.get("title", "").strip().lower(), date_str)
    for item in primary:
        k = _key(item)
        if k not in seen:
            seen.add(k)
            out.append(item)
    for lst in extras:
        for item in lst:
            k = _key(item)
            if k not in seen:
                seen.add(k)
                out.append(item)
    return out


# ── Episode-Erkennung ─────────────────────────────────────────────────────────

_EP_PATTERNS = [
    r'\((\d{1,4})/\d+\)',                        # (3/8)
    r'\bFolge[\s._]+(\d{1,4})\b',               # Folge 3 / Folge.3
    r'\bEpisode[\s._]+(\d{1,4})\b',             # Episode 3 / Episode.3
    r'\bTeil[\s._]+(\d{1,4})\b',                # Teil 3 / Teil.3
    r'\b(\d{1,4})\.\s*(?:Folge|Teil|Episode)',  # 3. Folge
    r'\((\d{1,4})\)\s*$',                       # (3) am Titelende
    r'(?<![A-Za-z])E(\d{1,4})(?![A-Za-z\d])',  # E040 / E1155 (kein SxxExx-Prefix nötig)
]

_SE_RE = re.compile(r'S(\d{1,4})[_. ]?[xE](\d{1,4})', re.IGNORECASE)

# Senderkürzel – EINE Quelle für beide Regexe unten, damit sie nicht
# auseinanderlaufen.
#
# BEWUSST NICHT enthalten: ONE, SUPER, NICK, DISNEY. Das sind zwar Sender,
# aber viel häufiger gewöhnliche Wörter in Titeln. "ONE" machte aus
# "One Piece" ein "Piece", "SUPER" aus dem Episodentitel "Der Super-Roller"
# ein "Der". Ein falsch beschnittener Name führt zu falscher Zuordnung;
# ein nicht entferntes Senderkürzel kostet höchstens einen Klick.
_CHANNELS_RE_SRC = (r'ARD|ZDF|MDR|NDR|WDR|SWR|BR|HR|RBB|ORF|3SAT|ARTE|'
                    r'PHOENIX|KiKA|RTL|SAT1?|PRO7|VOX|DMAX|TELE5|FUNK')

# Nur am Anfang – für den Seriennamen
_CHANNEL_PREFIX_RE = re.compile(rf'^(?:{_CHANNELS_RE_SRC})[ _-]+', re.IGNORECASE)

# Überall im Namen – für den Episodentitel
_CHANNEL_ANY_RE = re.compile(rf'\b(?:{_CHANNELS_RE_SRC})\b', re.IGNORECASE)

# Release-Gruppe am Ende ("-YTS", "-NIMA4K", "-STARS"). Bewusst nur bei
# GROSSSCHREIBUNG oder Ziffern – sonst verschwindet aus dem echten Titel
# "Der Super-Roller" das "-Roller".
_RELEASE_SUFFIX_RE = re.compile(r'[-–]\s*(?=[^a-z\s]{2,}\s*$)\w{2,}\s*$')

_VIDEO_EXTS = {".mp4", ".mkv", ".avi", ".mov", ".wmv", ".ts", ".m4v",
               ".flv", ".webm", ".mpg", ".mpeg", ".m2ts", ".mts"}

_QUALITY_RE = re.compile(
    r'\b(720p|1080p|2160p|4K|UHD|BluRay|BRRip|WEB[-.]?DL|WEBRip|DVDRip|'
    r'HDTV|x264|x265|H\.?264|H\.?265|AVC|HEVC|AAC|AC3|DTS|HDR|SDR|'
    r'REMUX|NF|AMZN|DSNP|HULU)\b',
    re.IGNORECASE)


def _fix_mojibake(s):
    """Korrigiert UTF-8-Bytes die fälschlich als Latin-1 gelesen wurden."""
    try:
        return s.encode('latin-1').decode('utf-8')
    except (UnicodeEncodeError, UnicodeDecodeError):
        return s


def _normalize_title(text):
    """Kleinbuchstaben, Umlaute ersetzen, nur a-z/0-9/Leerzeichen."""
    t = _fix_mojibake(text).lower()
    t = t.replace("ä", "ae").replace("ö", "oe").replace("ü", "ue")
    t = t.replace("ß", "ss").replace("é", "e").replace("è", "e")
    t = re.sub(r'[^a-z0-9 ]', ' ', t)
    return re.sub(r'\s+', ' ', t).strip()


# ── Serienname aus Dateinamen (Gruppierung) ──────────────────────────────────

# Führender Artikel: faltet "Die Pfefferkörner" / "Pfefferkörner" zusammen.
# Läuft NACH _normalize_title, also bereits kleingeschrieben.
_ARTICLE_RE = re.compile(r'^(?:die|der|das|the)\s+')

# Führende Nummerierung eigener Dateien: "1_Wickie und die starken Männer"
_LEADNUM_RE = re.compile(r'^\d{1,3}[_\s.\-]+')

# Mehrteiler-Suffix
_PART_RE = re.compile(r'\b(?:Teil|Part|Pt\.?)\s*(\d+)\b', re.IGNORECASE)

# Marker, ab dem der Serienname endet. Der LINKESTE Treffer gewinnt –
# bei "Show S2026E156 S10_E08.mp4" ergibt das "Show" und nicht
# "Show S2026E156".
_CUT_PATTERNS = [
    _SE_RE.pattern,                                # S14E07 / S2024E02 / S02e040 / S10_E08
    r'\b\d{1,2}x\d{2,3}\b',                        # 1x05
    r'\bFolge[\s._]*\d', r'\bTeil[\s._]*\d', r'\bEpisode[\s._]*\d',
    r'\b\d{1,4}\.\s*(?:Folge|Teil|Episode)\b',
    r'\b(?:19|20)\d{2}[-_.]\d{2}[-_.]\d{2}\b',     # 2024-03-15 (Datumsdateien)
    r'\bvom\s+\d{1,2}\.\d{1,2}\.',                 # vom 16.03.2024
    r'\(\d{1,4}/\d{1,4}\)',                        # (3/8)
    # Die folgenden zwei greifen für die eigenen Downloads dieser App:
    # _series_filename fällt auf "{topic} E{ep} {titel}" bzw.
    # "{topic} S{jahr} {titel}" zurück, wenn Folge/Zeitstempel fehlen.
    r'(?<![A-Za-z])E\d{1,4}(?![A-Za-z\d])',
    r'\bS(?:19|20)\d{2}\b(?![xE\d])',
]
_CUT_RE = re.compile("|".join("(?:%s)" % p for p in _CUT_PATTERNS),
                     re.IGNORECASE)


def _with_source_ext(new_name, src_filename):
    """Übernimmt die Dateiendung der Quelldatei in den neuen Namen.

    Die Formatvorlagen enden fest auf ".mp4" – ohne diese Korrektur würde
    aus einer .mkv beim Umbenennen eine .mp4, obwohl sich am Inhalt nichts
    ändert.
    """
    src_ext = os.path.splitext(src_filename)[1]
    if not src_ext:
        return new_name
    base, ext = os.path.splitext(new_name)
    return base + src_ext if ext.lower() != src_ext.lower() else new_name


def _abs_map_from_episodes(episodes):
    """Absolute Folgennummer → (Staffel, Folge) der offiziellen Reihenfolge.

    Wird aus der bereits geladenen offiziellen Liste abgeleitet: alle
    regulären Folgen (ohne Specials, also Staffel ≥ 1) nach Staffel und
    Folge sortiert und ab 1 durchnummeriert.

    Der `/episodes/absolute/`-Endpunkt von TheTVDB taugt dafür NICHT – er
    meldet für jede Folge `seasonNumber: 1` und liefert damit nur eine
    Identitätsabbildung. Diese Ableitung funktioniert dagegen für alle
    Quellen gleich und braucht keine zusätzliche Abfrage.

    Beispiel One Piece: Folge 1155 der Dateien → (Staffel, Folge) laut TVDB.
    """
    regulaer = sorted(k for k in episodes if k[0] is not None and k[0] >= 1)
    return {abs_n: k for abs_n, k in enumerate(regulaer, start=1)}


def _part_num(filename):
    """Mehrteiler-Nummer aus dem Dateinamen, oder None."""
    m = _PART_RE.search(filename)
    return int(m.group(1)) if m else None


def _series_from_filename(fname):
    """Serienname aus EINEM Dateinamen.

    Gibt '' zurück wenn kein Struktur-Marker (S/E, Folge, Datum …) gefunden
    wurde – dann wird bewusst NICHT geraten.
    """
    name = _fix_mojibake(os.path.splitext(os.path.basename(fname))[0])
    m = _CUT_RE.search(name)
    if not m:
        return ""
    s = re.sub(r'[._]+', ' ', name[:m.start()])
    s = _QUALITY_RE.sub(' ', s)
    s = re.sub(r'\s+', ' ', s).strip(" -–_.")
    s = _CHANNEL_PREFIX_RE.sub('', s).strip()
    s = _LEADNUM_RE.sub('', s).strip()
    s = re.sub(r'\s*\((?:19|20)\d{2}\)\s*$', '', s)   # "Hubert ohne Staller (2011)"
    s = re.sub(r'\s+', ' ', s).strip(" -–_.")
    # Mindestens 2 Zeichen ohne Leerraum – "24" bleibt damit ein gültiger Name
    if len(re.sub(r'\s', '', s)) < 2:
        return ""
    return s


# Ordnernamen, die sicher KEIN Serienname sind
_GENERIC_DIRS = {
    "downloads", "download", "extracted", "extrahiert", "entpackt", "temp",
    "tmp", "neu", "new", "video", "videos", "filme", "movies", "serien",
    "series", "tv", "media", "mediathek", "unsortiert", "sonstiges",
    "nicht umgewandelt", "fertig", "eingang", "incoming", "complete",
}

# Staffel-Ordner: "Staffel 01", "Season 1", "S01" …
_SEASON_DIR_RE = re.compile(
    r'^(?:staffel|season|s)[\s._-]*\d{1,4}$', re.IGNORECASE)


# Sample-Dateien aus Scene-Releases: kurze Ausschnitte, keine echten Folgen.
# "sample" als eigenes Wort – trennt auch "-sample", ".sample", "_sample" ab.
_SAMPLE_RE = re.compile(r'(?<![A-Za-z])sample(?![A-Za-z])', re.IGNORECASE)

# Oberhalb dieser Größe gilt eine Datei trotz "sample" im Namen als echt –
# schützt davor, eine reguläre Folge mit dem Wort im Titel wegzuwerfen.
_SAMPLE_MAX_BYTES = 300 * 1024 * 1024


def _is_sample_file(directory, filename):
    """Ist das eine Sample-/Beispieldatei (und damit zu ignorieren)?"""
    in_name = bool(_SAMPLE_RE.search(os.path.splitext(filename)[0]))
    parent  = os.path.basename(os.path.abspath(directory or "").rstrip("\\/"))
    in_dir  = bool(_SAMPLE_RE.fullmatch(parent.strip()))
    if not (in_name or in_dir):
        return False
    # Große Dateien sind trotz des Wortes keine Samples
    try:
        if os.path.getsize(os.path.join(directory, filename)) > _SAMPLE_MAX_BYTES:
            return False
    except OSError:
        pass
    return True


# Begleitdateien, die zu einer Videodatei gehören und mitwandern müssen
_SIDECAR_EXTS = {".srt", ".ass", ".ssa", ".sub", ".idx", ".vtt", ".sup",
                 ".mediathek", ".nfo"}


def _sidecar_files(directory, video_filename):
    """Begleitdateien einer Videodatei (Untertitel, .mediathek, .nfo).

    Findet auch sprachmarkierte Varianten wie "Folge.de.srt" oder
    "Folge.ger.forced.srt". Gibt [(pfad, endungs_teil)] zurück, wobei
    endungs_teil alles nach dem Basisnamen ist ("(.de).srt").
    """
    base = os.path.splitext(video_filename)[0]
    if not os.path.isdir(directory):
        return []
    out = []
    for f in os.listdir(directory):
        if f == video_filename or not f.startswith(base):
            continue
        rest = f[len(base):]
        if os.path.splitext(f)[1].lower() in _SIDECAR_EXTS:
            out.append((os.path.join(directory, f), rest))
    return out


def _series_from_dirname(directory):
    """Serienname aus dem ORDNER, in dem die Datei liegt.

    Für Dateien, deren Name die Serie nicht enthält (z.B. nur
    "156. Die Reise nach Walhalla.mp4" im Ordner "Robin Hood").
    Staffel-Ordner werden übersprungen, generische Ordner abgelehnt.
    """
    d = os.path.abspath(directory or "")
    for _ in range(2):                      # ggf. eine Staffel-Ebene überspringen
        name = os.path.basename(d.rstrip("\\/"))
        if not name or len(name) < 2:
            return ""
        if _SEASON_DIR_RE.match(name.strip()):
            d = os.path.dirname(d)          # eine Ebene höher
            continue
        if name.strip().lower() in _GENERIC_DIRS:
            return ""
        cleaned = re.sub(r'[._]+', ' ', name)
        # Scene-Metadaten abschneiden – Release-Ordner heißen z.B.
        # "Roseanne.S01.COMPLETE.COLLECTION.German.AC3.DL.FS.DVDRip.x264.-.BUX".
        # Ohne diesen Schnitt wird der ganze Release-Name zum Gruppenschlüssel
        # und jede Staffel bildet eine eigene Gruppe.
        m_cut = _CUT_RE.search(cleaned)
        if m_cut and m_cut.start() > 0:
            cleaned = cleaned[:m_cut.start()]
        cleaned = re.sub(r'\bS\d{1,4}\b', ' ', cleaned, flags=re.IGNORECASE)
        cleaned = re.sub(r'\b(?:COMPLETE|COLLECTION|SEASON|STAFFEL|BOXSET|'
                         r'MULTI|DL|GERMAN|ENGLISH|DUBBED|SUBBED)\b', ' ',
                         cleaned, flags=re.IGNORECASE)
        cleaned = _QUALITY_RE.sub(' ', cleaned)
        cleaned = re.sub(r'\b(?:AC3|DTS|FS|WS|XviD|DivX|BDRip|HDRip|TVRip|WEB|'
                         r'PROPER|REPACK|INTERNAL|UNRATED|EXTENDED|UNCUT|'
                         r'DOKU|RETAIL)\b',
                         ' ', cleaned, flags=re.IGNORECASE)
        cleaned = re.sub(r'[-–]\s*\w{2,}\s*$', '', cleaned)   # Encoder-Suffix
        cleaned = _CHANNEL_PREFIX_RE.sub('', cleaned).strip()
        cleaned = re.sub(r'\s*\((?:19|20)\d{2}\)\s*$', '', cleaned)
        cleaned = re.sub(r'\s{2,}', ' ', cleaned).strip(" -–_.")
        if len(re.sub(r'\s', '', cleaned)) < 2:
            return ""
        return cleaned
    return ""


def _series_group_key(raw):
    """Gruppen-Schlüssel: fasst reine Schreibvarianten zusammen.

    Bewusst KEIN Fuzzy-Matching: difflib("dragon ball z", "dragon ball gt")
    liegt bei 0.89 und "hubert ohne staller"/"hubert und staller" bei 0.87 –
    jede Schwelle in dieser Region wäre entweder wirkungslos oder
    zusammenführend falsch. Varianten werden per Hand zusammengeführt.
    """
    k = _ARTICLE_RE.sub('', _normalize_title(raw))
    k = re.sub(r'\b(?:19|20)\d{2}\b$', '', k).strip()
    k = re.sub(r'\b(?:german|deutsch|dl|ut|ov|hd|sd)\b', ' ', k)
    return re.sub(r'\s+', ' ', k).strip()


# Erwartete Gruppen-Schlüssel für reale Dateinamen. Schützt die Gruppierung
# gegen unbeabsichtigte Änderungen an _CUT_RE / _series_group_key.
# Prüfen mit:  python mediathek_downloader.py --selftest
_GROUP_SELFTEST = [
    ("Hubert ohne Staller S14E07 Folge 130 Der Tote im Kornfeld.mp4", "hubert ohne staller"),
    ("Robin Hood S2024E02 156. Die Reise nach Walhalla (2) pt2.mp4",  "robin hood"),
    ("KiKA Robin Hood S2024E03 157. Titel.mp4",                       "robin hood"),
    ("Dragon Ball Z S02e040 Der Kampf beginnt.mp4",                   "dragon ball z"),
    ("Der Bergdoktor S18E03 Heimweh.mp4",                             "bergdoktor"),
    ("Die Pfefferkoerner S19E05 Der Fall.mp4",                        "pfefferkoerner"),
    ("Pfefferkörner S19E06 Nochwas.mp4",                              "pfefferkoerner"),
    ("Löwenzahn S2025 Peter und der Wolf.mp4",                        "loewenzahn"),
    ("Loewenzahn E05 Anderer Titel.mp4",                              "loewenzahn"),
    ("Die Sendung mit der Maus 2024-03-15 Lachgeschichten.mp4",       "sendung mit der maus"),
    ("Tatort vom 16.03.2024 Der Fall.mp4",                            "tatort"),
    ("1_Wickie und die starken Maenner E01 Start.mp4",                "wickie und die starken maenner"),
    ("Wickie und die starken Männer E02 Weiter.mp4",                  "wickie und die starken maenner"),
    ("Bibi und Tina 1x05 Der Ausritt.mp4",                            "bibi und tina"),
    ("Sendung Episode 12 Titel.mp4",                                  "sendung"),
    ("Die ins Gras beissen Teil 2 Fortsetzung.mp4",                    "ins gras beissen"),
    ("Waldis Welt S03E04 Teil 1.mp4",                                  "waldis welt"),
    # Filme / markerlose Namen dürfen KEINE Gruppe bilden
    ("Beast.2026.German.2160p.UHD.BluRay.HEVC-NIMA4K.mkv",            ""),
    ("Irgendein Film ohne Marker.mp4",                                ""),
]


def _run_group_selftest():
    """Prüft _series_from_filename/_series_group_key. Gibt Fehlerzahl zurück."""
    fails = 0
    for fname, expected in _GROUP_SELFTEST:
        raw = _series_from_filename(fname)
        got = _series_group_key(raw) if raw else ""
        if got != expected:
            fails += 1
            print(f"FEHLER  {fname}\n        erwartet={expected!r}  erhalten={got!r}")
    total = len(_GROUP_SELFTEST)
    print(f"Gruppierung-Selbsttest: {total - fails}/{total} OK"
          + ("" if not fails else f"  –  {fails} Fehler"))
    return fails


def _best_episode_match(candidate, episodes):
    """Findet die ähnlichste Episode; gibt (s, e, title, ratio) zurück."""
    if not candidate or len(candidate) < 2:
        return None, None, None, 0.0
    norm_cand = _normalize_title(candidate)
    cand_words = set(norm_cand.split())
    best = (None, None, None, 0.0)
    for (ss, ee), title in episodes.items():
        norm_t = _normalize_title(title)
        if not cand_words.intersection(w for w in norm_t.split() if len(w) > 2):
            continue
        ratio = difflib.SequenceMatcher(None, norm_cand, norm_t).ratio()
        if ratio > best[3]:
            best = (ss, ee, title, ratio)
    return best


def _parse_movie_filename(filename):
    """Extrahiert Filmtitel und Erscheinungsjahr aus einem Dateinamen."""
    name = os.path.splitext(filename)[0]
    name = _fix_mojibake(name)
    name = unicodedata.normalize("NFC", name)
    name = re.sub(r'[_.]', ' ', name)
    name = _QUALITY_RE.sub(' ', name)
    name = _CHANNEL_PREFIX_RE.sub('', name).strip()
    m = re.search(r'\b(19\d{2}|20[0-2]\d)\b', name)
    year = m.group(1) if m else None
    if m:
        name = name[:m.start()]
    name = re.sub(r'\s+', ' ', name).strip(' -–_([{')
    return name, year


def _scan_se_tags(folder):
    """Durchsucht alle Unterordner rekursiv nach .mp4-Dateien.
    Gibt (full_tags, ep_numbers) zurück:
      full_tags  – Menge von 'SxxExx'-Strings (z.B. {'S2024E03', 'S03E10'})
      ep_numbers – Menge der reinen Folgennummern (int) aus allen SxxExx-Treffern
    """
    full_tags  = set()
    ep_numbers = set()
    if not os.path.isdir(folder):
        return full_tags, ep_numbers
    for root, _dirs, files in os.walk(folder):
        for fname in files:
            if os.path.splitext(fname)[1].lower() in _VIDEO_EXTS:
                for m in _SE_RE.finditer(fname):
                    full_tags.add(m.group(0).upper())
                    ep_numbers.add(int(m.group(2)))
    return full_tags, ep_numbers


def _scan_sidecar_hashes(folder):
    """Liest alle .mediathek-Sidecar-Dateien rekursiv aus.
    Gibt Dict {hash: mp4_pfad} zurück – nur wenn das zugehörige .mp4 noch existiert."""
    result = {}
    if not os.path.isdir(folder):
        return result
    for root, _dirs, files in os.walk(folder):
        for fname in files:
            if fname.endswith(".mediathek"):
                try:
                    with open(os.path.join(root, fname), encoding="utf-8") as f:
                        h = f.read().strip()
                    if h:
                        mp4 = os.path.splitext(os.path.join(root, fname))[0] + ".mp4"
                        if os.path.isfile(mp4):
                            result[h] = mp4
                except Exception:
                    pass
    return result


def _write_sidecar(filepath, item_hash):
    """Schreibt eine .mediathek-Sidecar-Datei neben die heruntergeladene MP4."""
    sidecar = os.path.splitext(filepath)[0] + ".mediathek"
    try:
        with open(sidecar, "w", encoding="utf-8") as f:
            f.write(item_hash)
    except Exception:
        pass


def _item_se_tag(item):
    """Berechnet den SxxExx-Tag eines API-Ergebnisses, z.B. 'S2024E03'.
    Gibt None zurück wenn Folge oder Jahr nicht erkennbar."""
    ep  = _extract_episode(item.get("title", ""))
    ts  = item.get("timestamp", 0)
    yr  = datetime.fromtimestamp(ts).year if ts else None
    if ep and yr:
        return f"S{yr}E{ep:02d}".upper()
    if ep:
        return f"E{ep:02d}".upper()
    return None


def _extract_episode(title):
    for pat in _EP_PATTERNS:
        m = re.search(pat, title, re.IGNORECASE)
        if m:
            return int(m.group(1))
    return None


def _series_filename(topic, title, timestamp):
    """Gibt Dateinamen im Format Serientitel S2024E03 Folgentitel zurück."""
    ep        = _extract_episode(title)
    year      = datetime.fromtimestamp(timestamp).year if timestamp else None
    base      = _safe_dirname(topic)
    safe_title = _safe_filename(title)
    if year and ep:
        return f"{base} S{year}E{ep:02d} {safe_title}"
    if ep:
        return f"{base} E{ep:02d} {safe_title}"
    if year:
        return f"{base} S{year} {safe_title}"
    return safe_title


# ── Dateipfad ─────────────────────────────────────────────────────────────────

def _build_filepath(folder, topic, title, timestamp=0, series_fmt=False):
    series_dir = os.path.join(folder, _safe_dirname(topic))
    if series_fmt:
        year       = datetime.fromtimestamp(timestamp).year if timestamp else None
        season_dir = os.path.join(series_dir, f"Staffel {year}") if year else series_dir
        filename   = _series_filename(topic, title, timestamp) + ".mp4"
    else:
        season_dir = series_dir
        filename   = _safe_filename(title) + ".mp4"
    return season_dir, os.path.join(season_dir, filename)


# ── ffprobe ───────────────────────────────────────────────────────────────────

def _find_ffprobe():
    return shutil.which("ffprobe")


def _probe_resolution(url, ffprobe_path="ffprobe"):
    try:
        result = subprocess.run(
            [ffprobe_path, "-v", "quiet", "-print_format", "json",
             "-show_streams", "-select_streams", "v:0", "-i", url],
            capture_output=True, text=True, timeout=18
        )
        data    = json.loads(result.stdout)
        streams = data.get("streams", [])
        if not streams:
            return None
        w = streams[0].get("width",  0)
        h = streams[0].get("height", 0)
        if not w or not h:
            return None
        label = {1080: "Full HD", 720: "HD", 576: "576p",
                 540: "540p", 480: "480p", 360: "SD", 270: "SD"}.get(h, "")
        return f"{w}×{h}" + (f"  ({label})" if label else "")
    except Exception:
        return None


# ── Formatierung ──────────────────────────────────────────────────────────────

def _fmt_size(b):
    if b <= 0: return "—"
    if b < 1024 ** 2: return f"{b/1024:.0f} KB"
    return f"{b/1024**2:.1f} MB"

def _fmt_speed(bps):
    if bps <= 0: return ""
    if bps < 1024 ** 2: return f"{bps/1024:.0f} KB/s"
    return f"{bps/1024**2:.1f} MB/s"

def _fmt_eta(secs):
    """Verbleibende Zeit als lesbaren String formatieren."""
    if secs <= 0 or secs > 86400:
        return ""
    secs = int(secs)
    if secs < 60:
        return f"~{secs}s"
    m, s = divmod(secs, 60)
    if m < 60:
        return f"~{m}:{s:02d}min"
    h, m = divmod(m, 60)
    return f"~{h}h{m:02d}min"

def _bar(pct, width=10):
    filled = int(pct / 100 * width)
    return "█" * filled + "░" * (width - filled) + f"  {pct:3.0f}%"


# ═══════════════════════════════════════════════════════════════════════════════
# Tooltip
# ═══════════════════════════════════════════════════════════════════════════════
# TheTVDB-Client
# ═══════════════════════════════════════════════════════════════════════════════

class TVDBClient:
    BASE = "https://api4.thetvdb.com/v4"

    def __init__(self, api_key):
        self.api_key = api_key
        self.token   = None

    def authenticate(self):
        r = requests.post(f"{self.BASE}/login",
                          json={"apikey": self.api_key}, timeout=10)
        r.raise_for_status()
        self.token = r.json()["data"]["token"]

    def _h(self):
        return {"Authorization": f"Bearer {self.token}"}

    # ISO-639-2 → ISO-639-1 mapping für TVDB-Suche
    _LANG3_TO_2 = {"deu": "de", "eng": "en", "fra": "fr", "spa": "es", "jpn": "ja"}

    def search_series(self, name, lang=None):
        """Gibt Liste von {'id', 'name', 'year', 'primary_language', 'overview'} zurück,
        sortiert so dass Einträge in der Zielsprache zuerst kommen."""
        params = {"query": name, "type": "series"}
        if lang:
            params["language"] = self._LANG3_TO_2.get(lang, lang)
        r = requests.get(f"{self.BASE}/search",
                         params=params,
                         headers=self._h(), timeout=10)
        r.raise_for_status()
        preferred = self._LANG3_TO_2.get(lang, lang) if lang else None
        results = []
        for item in r.json().get("data", []):
            pl = (item.get("primary_language") or "").lower()
            results.append({
                "id":               item.get("tvdb_id") or item.get("id", ""),
                "name":             item.get("name", ""),
                "year":             item.get("year", ""),
                "primary_language": pl,
                "overview":         (item.get("overview") or "")[:120],
            })
        # Einträge in der Zielsprache nach oben sortieren
        if preferred:
            results.sort(key=lambda x: 0 if x["primary_language"] == preferred else 1)
        return results

    def get_series_name(self, series_id, lang, fallback_name=""):
        """Gibt den Seriennamen in der gewünschten Sprache zurück.
        Versucht erst den 3-Zeichen-Code, dann den 2-Zeichen-Code."""
        for code in dict.fromkeys([lang, self._LANG3_TO_2.get(lang, lang)]):
            try:
                r = requests.get(
                    f"{self.BASE}/series/{series_id}/translations/{code}",
                    headers=self._h(), timeout=10)
                r.raise_for_status()
                name = (r.json().get("data") or {}).get("name", "").strip()
                if name:
                    return name
            except Exception:
                pass
        return fallback_name

    def get_episodes(self, series_id, lang="deu", primary_lang="", order="official"):
        """Gibt Dict {(staffel, folge): episodenname} zurück.
        Lädt Englisch als Basis, legt dann die Zielsprache darüber.
        Übersetzungen die identisch mit der Originalsprache sind werden
        ignoriert — das sind TVDB-Fallbacks, keine echten Übersetzungen.
        order: "official" (staffelbasiert) oder "absolute" (durchgehend, z.B. für Anime)."""

        lang2        = self._LANG3_TO_2.get(lang, lang)          # "deu" → "de"
        primary_lang2 = self._LANG3_TO_2.get(primary_lang, primary_lang)  # "fra" → "fr"
        ep_order = order if order in ("official", "absolute", "dvd", "alternate") else "official"

        def _fetch(target_lang):
            result = {}
            page = 0
            while True:
                try:
                    # Sprache als Pfad-Parameter (TVDB v4), nicht als Query-Parameter
                    r = requests.get(
                        f"{self.BASE}/series/{series_id}/episodes/{ep_order}/{target_lang}",
                        params={"page": page},
                        headers=self._h(), timeout=15)
                    r.raise_for_status()
                    payload = r.json()
                    data = payload.get("data", {})
                    eps  = data.get("episodes", [])
                except Exception:
                    break
                if not eps:
                    break
                for ep in eps:
                    if ep_order == "absolute":
                        # Im absoluten Modus gibt /episodes/absolute/ die absolute
                        # Folgennummer direkt im "number"-Feld zurück.
                        # Staffel = 1 als Platzhalter (Plex-konform: S01E001..S01E291)
                        s = 1
                        e = ep.get("number", 0)
                    else:
                        s = ep.get("seasonNumber", 0)
                        e = ep.get("number",       0)
                    name = (ep.get("name") or "").strip()
                    # s is not None statt "if s": Season 0 (Specials) hat s=0
                    # was als falsy gewertet würde und alle Specials verwirft
                    if s is not None and e and name:
                        result[(s, e)] = name
                # ACHTUNG: TheTVDB liefert "links" auf der OBERSTEN Ebene der
                # Antwort, nicht in "data". Wer in data sucht, findet nie ein
                # "next" und bricht nach der ersten Seite ab – bei One Piece
                # wurden so nur 500 von über 1100 Episoden geladen.
                if not (payload.get("links") or {}).get("next"):
                    break
                page += 1
            return result

        eng = _fetch("eng")

        if lang in ("eng", "en"):
            return eng

        # 2-Zeichen-Code zuerst – TVDB v4 bevorzugt ISO-639-1 beim lang-Param
        translated = _fetch(lang2)
        if not translated and lang2 != lang:
            translated = _fetch(lang)

        # Wenn die Zielsprache == Originalsprache der Serie (z.B. Deutsch bei
        # einer deutschen Produktion), sind die Übersetzungen identisch mit dem
        # Original – der bisherige Filter würde alles verwerfen. Hier einfach
        # die Übersetzungen direkt über Englisch legen.
        target_is_original = (
            primary_lang and
            (lang2 == self._LANG3_TO_2.get(primary_lang, primary_lang)
             or lang == primary_lang
             or lang2 == primary_lang))

        result = dict(eng)
        if target_is_original:
            # Zielsprache = Originalsprache → jede vorhandene Übersetzung nehmen
            for key, name in translated.items():
                if name:
                    result[key] = name
        else:
            # Originalsprache laden um TVDB-Fallbacks zu erkennen
            orig = {}
            if primary_lang and primary_lang not in ("eng", "en"):
                orig = _fetch(primary_lang)
                if not orig and primary_lang2 != primary_lang:
                    orig = _fetch(primary_lang2)

            def _norm(s):
                return unicodedata.normalize("NFC", (s or "").strip().lower())

            for key, name in translated.items():
                if not name:
                    continue
                if key not in result:
                    # Kein englischer Titel vorhanden → Übersetzung nehmen,
                    # auch wenn sie dem Original gleicht. Sonst fiele die
                    # Folge ganz heraus: "Floridor" (Die drei Musketiere)
                    # heißt auf Deutsch wie auf Französisch gleich und
                    # verschwand dadurch komplett aus der Liste.
                    result[key] = name
                elif _norm(name) != _norm(orig.get(key, "")):
                    # Echte Übersetzung (weicht vom Original ab) → bevorzugen
                    result[key] = name

        return result

    def build_abs_map(self, series_id):
        """Gibt {abs_ep_num: (season, per_season_ep)} zurück.
        Nützlich wenn Dateinamen absolute Episodennummern statt Staffel-Episodennummern enthalten
        (z.B. S02e040 meint absolute Folge 40, in TVDB aber S2E1)."""
        abs_eps = []
        page = 0
        while True:
            try:
                r = requests.get(
                    f"{self.BASE}/series/{series_id}/episodes/absolute/eng",
                    params={"page": page},
                    headers=self._h(), timeout=15)
                r.raise_for_status()
                data = r.json().get("data", {})
                eps  = data.get("episodes", [])
            except Exception:
                break
            if not eps:
                break
            for ep in eps:
                abs_n  = ep.get("number", 0)
                season = ep.get("seasonNumber", 0)
                if abs_n and season is not None:
                    abs_eps.append((abs_n, season))
            if not data.get("links", {}).get("next"):
                break
            page += 1

        # Innerhalb jeder Staffel nach absoluter Nummer sortieren → Rang = per-Staffel-EP
        from collections import defaultdict
        by_season = defaultdict(list)
        for abs_n, season in abs_eps:
            by_season[season].append(abs_n)
        result = {}
        for season, nums in by_season.items():
            for rank, abs_n in enumerate(sorted(nums), start=1):
                result[abs_n] = (season, rank)
        return result


# ═══════════════════════════════════════════════════════════════════════════════
# TheMovieDB-Client
# ═══════════════════════════════════════════════════════════════════════════════

class TMDBClient:
    BASE = "https://api.themoviedb.org/3"

    def __init__(self, api_key):
        self.api_key = api_key

    def _get(self, path, **params):
        params["api_key"] = self.api_key
        r = requests.get(f"{self.BASE}{path}", params=params, timeout=10)
        r.raise_for_status()
        return r.json()

    IMG_BASE = "https://image.tmdb.org/t/p/w154"

    def search_movies(self, query, language="de", year=None):
        params = {"query": query, "language": language}
        if year:
            params["year"] = year
        data = self._get("/search/movie", **params)
        results = []
        for item in data.get("results", [])[:10]:
            results.append({
                "id":             item["id"],
                "title":          item.get("title", ""),
                "original_title": item.get("original_title", ""),
                "year":           (item.get("release_date") or "")[:4],
                "overview":       (item.get("overview") or "")[:160],
                "poster_path":    item.get("poster_path") or "",
            })
        return results

    def poster_url(self, poster_path):
        return f"{self.IMG_BASE}{poster_path}" if poster_path else ""


class TraktClient:
    """Serien-Quelle über Trakt.tv – schnittstellenkompatibel mit TVDBClient."""
    BASE = "https://api.trakt.tv"

    _LANG3_TO_2 = {"deu": "de", "eng": "en", "fra": "fr", "spa": "es", "jpn": "ja"}

    def __init__(self, client_id):
        self.client_id = client_id

    def authenticate(self):
        pass   # Öffentliche Endpunkte brauchen nur die Client-ID

    def _h(self):
        return {"Content-Type":     "application/json",
                "trakt-api-version": "2",
                "trakt-api-key":     self.client_id}

    def search_series(self, name, lang=None):
        r = requests.get(f"{self.BASE}/search/show",
                         params={"query": name, "extended": "full", "limit": 20},
                         headers=self._h(), timeout=15)
        r.raise_for_status()
        results = []
        for item in r.json():
            show = item.get("show") or {}
            ids  = show.get("ids") or {}
            sid  = ids.get("trakt") or ids.get("slug")
            if not sid:
                continue
            results.append({
                "id":               sid,
                "name":             show.get("title", ""),
                "year":             show.get("year", "") or "",
                "primary_language": (show.get("language") or "").lower(),
                "overview":         (show.get("overview") or "")[:120],
            })
        preferred = self._LANG3_TO_2.get(lang, lang) if lang else None
        if preferred:
            results.sort(key=lambda x: 0 if x["primary_language"] == preferred else 1)
        return results

    def get_series_name(self, series_id, lang, fallback_name=""):
        lang2 = self._LANG3_TO_2.get(lang, lang)
        try:
            r = requests.get(f"{self.BASE}/shows/{series_id}/translations/{lang2}",
                             headers=self._h(), timeout=10)
            r.raise_for_status()
            for tr in r.json():
                title = (tr.get("title") or "").strip()
                if title:
                    return title
        except Exception:
            pass
        return fallback_name

    def get_episodes(self, series_id, lang="deu", primary_lang="", order="official"):
        """Gibt {(staffel, folge): titel} zurück. Englisch als Basis,
        Zielsprache wird pro Staffel darübergelegt."""
        lang2 = self._LANG3_TO_2.get(lang, lang)
        result = {}
        try:
            r = requests.get(f"{self.BASE}/shows/{series_id}/seasons",
                             params={"extended": "episodes"},
                             headers=self._h(), timeout=20)
            r.raise_for_status()
            seasons = r.json()
        except Exception:
            return result

        season_nums = []
        for season in seasons:
            s_num = season.get("number")
            if s_num is None:
                continue
            season_nums.append(s_num)
            for ep in season.get("episodes") or []:
                e_num = ep.get("number")
                title = (ep.get("title") or "").strip()
                if e_num is not None and title:
                    result[(s_num, e_num)] = title

        if lang2 == "en":
            return result

        # Übersetzungen pro Staffel nachladen und überlagern
        def _translate_season(s_num):
            try:
                rr = requests.get(f"{self.BASE}/shows/{series_id}/seasons/{s_num}",
                                  params={"translations": lang2},
                                  headers=self._h(), timeout=15)
                rr.raise_for_status()
                out = {}
                for ep in rr.json():
                    e_num = ep.get("number")
                    if e_num is None:
                        continue
                    for tr in ep.get("translations") or []:
                        if (tr.get("language") or "").lower() != lang2:
                            continue
                        t = (tr.get("title") or "").strip()
                        if t:
                            out[(s_num, e_num)] = t
                        break
                return out
            except Exception:
                return {}

        with ThreadPoolExecutor(max_workers=4) as pool:
            for translated in pool.map(_translate_season, season_nums):
                result.update(translated)
        return result

    def build_abs_map(self, series_id):
        return {}   # Trakt bietet keine absolute Reihenfolge


class TVmazeClient:
    """Serien-Quelle über TVmaze – schnittstellenkompatibel mit TVDBClient.

    Kein API-Key nötig. WICHTIG: TVmaze hat KEINE Übersetzungsebene –
    Episodentitel liegen immer in der Originalsprache der Serie vor.
    Für deutsche Produktionen (ARD/ZDF/KiKA) sind sie damit deutsch,
    für synchronisierte Auslandsserien bleiben sie fremdsprachig.
    """
    BASE = "https://api.tvmaze.com"

    # TVmaze liefert Sprachen als englische Klarnamen
    _LANG3_TO_NAME = {"deu": "German", "eng": "English", "fra": "French",
                      "spa": "Spanish", "jpn": "Japanese", "ita": "Italian"}

    def __init__(self, _unused=None):
        pass

    def authenticate(self):
        pass   # TVmaze ist komplett offen

    def search_series(self, name, lang=None):
        r = requests.get(f"{self.BASE}/search/shows",
                         params={"q": name}, timeout=15)
        r.raise_for_status()
        results = []
        for item in r.json():
            show = item.get("show") or {}
            sid  = show.get("id")
            if not sid:
                continue
            net = (show.get("network") or show.get("webChannel") or {}).get("name") or ""
            summary = re.sub(r"<[^>]+>", "", show.get("summary") or "")
            premiered = show.get("premiered") or ""
            results.append({
                "id":               sid,
                "name":             show.get("name", ""),
                "year":             premiered[:4],
                "primary_language": (show.get("language") or "").lower(),
                "overview":         (f"{net} – " if net else "") + summary[:120],
            })
        # Serien in der Zielsprache nach oben sortieren
        want = (self._LANG3_TO_NAME.get(lang, lang) or "").lower() if lang else None
        if want:
            results.sort(key=lambda x: 0 if x["primary_language"] == want else 1)
        return results

    def get_series_name(self, series_id, lang, fallback_name=""):
        try:
            r = requests.get(f"{self.BASE}/shows/{series_id}", timeout=10)
            r.raise_for_status()
            title = (r.json().get("name") or "").strip()
            if title:
                return title
        except Exception:
            pass
        return fallback_name

    def _fetch_episodes(self, series_id):
        r = requests.get(f"{self.BASE}/shows/{series_id}/episodes",
                         params={"specials": 1}, timeout=20)
        r.raise_for_status()
        return r.json()

    def get_episodes(self, series_id, lang="deu", primary_lang="", order="official"):
        """Gibt {(staffel, folge): titel} zurück.

        TVmaze kennt keine Übersetzungen – es kommt immer die
        Originalsprache der Serie zurück (bei deutschen Serien also Deutsch).
        """
        result = {}
        try:
            eps = self._fetch_episodes(series_id)
        except Exception:
            return result

        if order == "absolute":
            # Durchgehend nummerieren (Specials überspringen)
            regular = sorted(
                (e for e in eps
                 if e.get("season") and e.get("number") is not None
                 and (e.get("type") or "regular") == "regular"),
                key=lambda e: (e["season"], e["number"]))
            for abs_n, ep in enumerate(regular, start=1):
                title = (ep.get("name") or "").strip()
                if title:
                    result[(1, abs_n)] = title
            return result

        for ep in eps:
            s_num = ep.get("season")
            e_num = ep.get("number")
            title = (ep.get("name") or "").strip()
            if s_num is None or not title:
                continue
            if e_num is None:
                s_num, e_num = 0, len([k for k in result if k[0] == 0]) + 1
            result[(s_num, e_num)] = title
        return result

    def build_abs_map(self, series_id):
        """Absolute Folgennummer → (Staffel, Folge). Aus der Episodenliste
        abgeleitet: alle regulären Folgen nach Staffel/Folge sortiert
        und ab 1 durchnummeriert."""
        try:
            eps = self._fetch_episodes(series_id)
        except Exception:
            return {}
        regular = sorted(
            (e for e in eps
             if e.get("season") and e.get("number") is not None
             and (e.get("type") or "regular") == "regular"),
            key=lambda e: (e["season"], e["number"]))
        return {abs_n: (ep["season"], ep["number"])
                for abs_n, ep in enumerate(regular, start=1)}


class OMDbClient:
    """Film-Quelle über OMDb (IMDb-Daten) – kompatibel mit TMDBClient."""
    BASE = "https://www.omdbapi.com/"

    def __init__(self, api_key):
        self.api_key = api_key

    def _get(self, **params):
        params["apikey"] = self.api_key
        r = requests.get(self.BASE, params=params, timeout=10)
        r.raise_for_status()
        return r.json()

    def search_movies(self, query, language="de", year=None):
        params = {"s": query, "type": "movie"}
        if year:
            params["y"] = year
        data = self._get(**params)
        if data.get("Response") != "True":
            return []
        hits = data.get("Search", [])[:10]

        def _detail(hit):
            imdb_id = hit.get("imdbID", "")
            title   = hit.get("Title", "")
            yr      = (hit.get("Year") or "")[:4]
            poster  = hit.get("Poster", "")
            overview = ""
            try:
                d = self._get(i=imdb_id, plot="short")
                if d.get("Response") == "True":
                    overview = (d.get("Plot") or "")[:160]
                    poster   = d.get("Poster") or poster
            except Exception:
                pass
            return {
                "id":             imdb_id,
                "title":          title,
                "original_title": title,   # OMDb liefert keinen Originaltitel
                "year":           yr,
                "overview":       overview,
                "poster_path":    poster if poster and poster != "N/A" else "",
            }

        with ThreadPoolExecutor(max_workers=5) as pool:
            return list(pool.map(_detail, hits))

    def poster_url(self, poster_path):
        return poster_path or ""   # OMDb liefert bereits vollständige URLs


# ═══════════════════════════════════════════════════════════════════════════════

class Tooltip:
    def __init__(self, widget, text):
        self._tip = None
        widget.bind("<Enter>", lambda _: self._show(widget, text))
        widget.bind("<Leave>", lambda _: self._hide())

    def _show(self, widget, text):
        x = widget.winfo_rootx() + 20
        y = widget.winfo_rooty() + widget.winfo_height() + 4
        self._tip = tw = tk.Toplevel(widget)
        tw.wm_overrideredirect(True)
        tw.wm_geometry(f"+{x}+{y}")
        tk.Label(tw, text=text, justify=tk.LEFT,
                 background="#ffffe0", relief=tk.SOLID, borderwidth=1,
                 font=("Segoe UI", 9)).pack()

    def _hide(self):
        if self._tip:
            self._tip.destroy()
            self._tip = None


# ═══════════════════════════════════════════════════════════════════════════════
# Hauptklasse
# ═══════════════════════════════════════════════════════════════════════════════

class MediathekDownloader:
    def __init__(self, root):
        self.root = root
        self.root.title("Mediathek Downloader")
        self.root.geometry("1200x780")
        self.root.minsize(980, 660)

        self.results            = []
        self.download_folder    = os.path.expanduser("~/Downloads")
        self._cancel_flag       = False
        self._dl_jobs           = {}
        self._dl_remaining      = collections.deque()   # aktuelle Job-Reihenfolge (veränderbar)
        self._dl_queue          = []   # wartende Download-Batches
        self._iid_to_item       = {}
        self._probe_cancel      = False
        self._ffprobe           = _find_ffprobe()
        self._watchlist         = self._load_watchlist()
        self._dl_known_hashes, self._dl_known_filenames = self._load_dl_hashes()
        self._active_dl_threads = 0
        self._wl_checked        = set()   # iids mit Watchlist-Haken
        self._wl_loading        = False   # Guard: verhindert Save-Loop beim Laden
        self._pause_event       = threading.Event()
        self._pause_event.set()           # gesetzt = läuft, gelöscht = pausiert

        self._setup_ui()
        self._populate_watchlist_tree()

        # Auto-Check beim Start
        if self._watchlist.get("auto_check_on_start") and self._watchlist.get("entries"):
            self.root.after(1500, self._start_watchlist_check)

        # Zeitplan-Thread starten
        threading.Thread(target=self._scheduler_loop, daemon=True).start()

    # ═══════════════════════════════════════════════════════════════════════════
    # UI-Aufbau
    # ═══════════════════════════════════════════════════════════════════════════

    def _setup_ui(self):
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=8, pady=8)

        self.tab_search    = ttk.Frame(self.notebook)
        self.tab_dl        = ttk.Frame(self.notebook)
        self.tab_watchlist = ttk.Frame(self.notebook)
        self.tab_rename    = ttk.Frame(self.notebook)

        self.notebook.add(self.tab_search,    text="  🔍 Suche  ")
        self.notebook.add(self.tab_dl,        text="  ⬇ Downloads  ")
        self.notebook.add(self.tab_watchlist, text="  📋 Watchlist  ")
        self.notebook.add(self.tab_rename,    text="  ✏ Umbenennen  ")

        self._build_search_tab(self.tab_search)
        self._build_download_tab(self.tab_dl)
        self._build_watchlist_tab(self.tab_watchlist)
        self._build_rename_tab(self.tab_rename)

        bar = ttk.Frame(self.root)
        bar.pack(fill=tk.X, padx=10, pady=(0, 6))
        self.status_var = tk.StringVar(value="Bereit.")
        ttk.Label(bar, textvariable=self.status_var, anchor=tk.W).pack(
            side=tk.LEFT, fill=tk.X, expand=True)

    # ── Such-Tab ──────────────────────────────────────────────────────────────

    def _build_search_tab(self, parent):
        sf = ttk.LabelFrame(parent, text="Suche", padding=10)
        sf.pack(fill=tk.X, padx=8, pady=(8, 4))

        ttk.Label(sf, text="Sendung / Thema:").grid(row=0, column=0, sticky=tk.W, padx=4)
        self.topic_var = tk.StringVar()
        ttk.Entry(sf, textvariable=self.topic_var, width=28).grid(row=0, column=1, padx=4)

        ttk.Label(sf, text="Titel (optional):").grid(row=0, column=2, sticky=tk.W, padx=4)
        self.title_var = tk.StringVar()
        ttk.Entry(sf, textvariable=self.title_var, width=28).grid(row=0, column=3, padx=4)

        ttk.Label(sf, text="Sender:").grid(row=0, column=4, sticky=tk.W, padx=4)
        self.channel_var = tk.StringVar(value="Alle")
        ttk.Combobox(sf, textvariable=self.channel_var, values=CHANNELS,
                     width=14, state="readonly").grid(row=0, column=5, padx=4)

        ttk.Label(sf, text="Sprache:").grid(row=0, column=6, sticky=tk.W, padx=4)
        self.language_var = tk.StringVar(value="Alle")
        ttk.Combobox(sf, textvariable=self.language_var, values=LANG_OPTIONS,
                     width=18, state="readonly").grid(row=0, column=7, padx=4)

        ttk.Label(sf, text="Max. Ergebnisse:").grid(row=1, column=0, sticky=tk.W, padx=4, pady=6)
        self.size_var = tk.IntVar(value=50)
        ttk.Spinbox(sf, from_=10, to=300, increment=10,
                    textvariable=self.size_var, width=8).grid(row=1, column=1, padx=4, sticky=tk.W)

        dur_f = ttk.Frame(sf)
        dur_f.grid(row=1, column=2, columnspan=3, sticky=tk.W, padx=4, pady=6)
        ttk.Label(dur_f, text="Dauer:  min").pack(side=tk.LEFT)
        self.dur_min_var = tk.StringVar(value="")
        ttk.Spinbox(dur_f, from_=0, to=600, textvariable=self.dur_min_var,
                    width=5).pack(side=tk.LEFT, padx=2)
        ttk.Label(dur_f, text="min  –  max").pack(side=tk.LEFT, padx=(4, 0))
        self.dur_max_var = tk.StringVar(value="")
        ttk.Spinbox(dur_f, from_=0, to=600, textvariable=self.dur_max_var,
                    width=5).pack(side=tk.LEFT, padx=2)
        ttk.Label(dur_f, text="min  (leer = kein Limit)").pack(side=tk.LEFT, padx=2)

        self.search_btn = ttk.Button(sf, text="🔍  Suchen", command=self._start_search)
        self.search_btn.grid(row=1, column=5, padx=4)
        ttk.Button(sf, text="📋  Zur Watchlist",
                   command=self._add_search_to_watchlist).grid(row=1, column=6, padx=4)

        # Barrierefreiheits-Filter
        acc_f = ttk.Frame(sf)
        acc_f.grid(row=2, column=0, columnspan=6, sticky=tk.W, padx=4, pady=(2, 0))
        self.filter_access_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(
            acc_f, text='Barrierefreiheits-Versionen ausblenden  (Hörgeschädigte / Gebärdensprache / Hörfassung / Audiodeskription)',
            variable=self.filter_access_var
        ).pack(side=tk.LEFT)

        # ffprobe-Zeile
        fp_f = ttk.Frame(sf)
        fp_f.grid(row=3, column=0, columnspan=6, sticky=tk.W, padx=4, pady=(4, 0))
        if self._ffprobe:
            ttk.Label(fp_f, text=f"ffprobe: {self._ffprobe}",
                      foreground="darkgreen").pack(side=tk.LEFT, padx=2)
        else:
            ttk.Label(fp_f, text="ffprobe nicht gefunden – Pfad angeben:",
                      foreground="red").pack(side=tk.LEFT, padx=2)
        self._ffprobe_path_var = tk.StringVar(value=self._ffprobe or "")
        if not self._ffprobe:
            ttk.Entry(fp_f, textvariable=self._ffprobe_path_var,
                      width=30).pack(side=tk.LEFT, padx=2)
            ttk.Button(fp_f, text="…", width=3,
                       command=self._browse_ffprobe).pack(side=tk.LEFT, padx=2)
        self.probe_btn = ttk.Button(fp_f, text="🔎  Auflösung prüfen",
                                    command=self._start_probe, state=tk.DISABLED)
        self.probe_btn.pack(side=tk.LEFT, padx=(12, 2))
        self.probe_status_var = tk.StringVar(value="")
        ttk.Label(fp_f, textvariable=self.probe_status_var,
                  foreground="gray").pack(side=tk.LEFT, padx=4)

        # Legende
        leg = ttk.Frame(sf)
        leg.grid(row=4, column=0, columnspan=6, sticky=tk.W, padx=4, pady=(2, 0))
        tk.Label(leg, text="  ", background="#ffe680", relief=tk.GROOVE).pack(side=tk.LEFT)
        ttk.Label(leg, text=" = Duplikat   ").pack(side=tk.LEFT)
        tk.Label(leg, text="  ", background="#d0f0d0", relief=tk.GROOVE).pack(side=tk.LEFT)
        ttk.Label(leg, text=" = Datei vorhanden").pack(side=tk.LEFT)

        # Ergebnisliste
        rf = ttk.LabelFrame(parent, text="Ergebnisse", padding=8)
        rf.pack(fill=tk.BOTH, expand=True, padx=8, pady=4)

        cols = ("wl", "channel", "topic", "title", "date", "duration", "hd")
        self.tree = ttk.Treeview(rf, columns=cols, show="headings", selectmode="extended")
        self.tree.heading("wl",       text="📋")
        self.tree.heading("channel",  text="Sender")
        self.tree.heading("topic",    text="Sendung")
        self.tree.heading("title",    text="Titel")
        self.tree.heading("date",     text="Datum")
        self.tree.heading("duration", text="Dauer")
        self.tree.heading("hd",       text="Auflösung")
        self.tree.column("wl",       width=28,  anchor=tk.CENTER, stretch=False)
        self.tree.column("channel",  width=75,  anchor=tk.CENTER)
        self.tree.column("topic",    width=155)
        self.tree.column("title",    width=310)
        self.tree.column("date",     width=85,  anchor=tk.CENTER)
        self.tree.column("duration", width=65,  anchor=tk.CENTER)
        self.tree.column("hd",       width=140, anchor=tk.CENTER)
        self.tree.tag_configure("duplicate", background="#ffe680")
        self.tree.tag_configure("exists",    background="#d0f0d0")
        self.tree.bind("<Button-1>", self._tree_click)

        vsb = ttk.Scrollbar(rf, orient=tk.VERTICAL,   command=self.tree.yview)
        hsb = ttk.Scrollbar(rf, orient=tk.HORIZONTAL, command=self.tree.xview)
        self.tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")
        hsb.grid(row=1, column=0, sticky="ew")
        rf.rowconfigure(0, weight=1)
        rf.columnconfigure(0, weight=1)

        # Download-Optionen
        df = ttk.LabelFrame(parent, text="Download starten", padding=10)
        df.pack(fill=tk.X, padx=8, pady=(4, 8))

        ttk.Label(df, text="Qualität:").grid(row=0, column=0, padx=4)
        self.quality_var = tk.StringVar(value="HD")
        q_box = ttk.Combobox(df, textvariable=self.quality_var,
                              values=["HD", "Normal", "SD"], width=9, state="readonly")
        q_box.grid(row=0, column=1, padx=4)
        Tooltip(q_box, QUALITY_HELP)
        ttk.Label(df, text="(?)", foreground="gray").grid(row=0, column=2)


        ttk.Label(df, text="Speicherort:").grid(row=0, column=3, padx=4)
        self.folder_var = tk.StringVar(value=self.download_folder)
        ttk.Entry(df, textvariable=self.folder_var, width=36).grid(row=0, column=4, padx=4)
        ttk.Button(df, text="…", width=3,
                   command=self._choose_folder).grid(row=0, column=5, padx=2)

        self.skip_dupes_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(df, text="Duplikate überspringen",
                        variable=self.skip_dupes_var).grid(
            row=1, column=0, columnspan=2, sticky=tk.W, padx=4, pady=4)

        ttk.Label(df, text="Vorhandene:").grid(row=1, column=2, sticky=tk.W, padx=(4, 2))
        self.exist_action_var = tk.StringVar(value="skip")
        ttk.Combobox(df, textvariable=self.exist_action_var,
                     values=["skip", "overwrite", "size"],
                     state="readonly", width=12).grid(row=1, column=3, sticky=tk.W, padx=2)
        ttk.Label(df, text="(skip=überspr. | overwrite=überschr. | size=Größe prüfen)",
                  foreground="gray").grid(row=1, column=4, columnspan=2, sticky=tk.W, padx=2)

        self.subtitles_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(df, text="Untertitel herunterladen (falls verfügbar)",
                        variable=self.subtitles_var).grid(
            row=2, column=0, columnspan=2, sticky=tk.W, padx=4, pady=2)

        self.series_fmt_var = tk.BooleanVar(value=False)
        cb_sf = ttk.Checkbutton(df,
            text="Serienformat-Benennung  (Serientitel S2024E03 Folgentitel.mp4)",
            variable=self.series_fmt_var)
        cb_sf.grid(row=2, column=2, columnspan=3, sticky=tk.W, padx=4)
        Tooltip(cb_sf,
            "Erkennt Folgennummern automatisch aus dem Titel:\n"
            "  'Folge 3', '(3/8)', 'Teil 3', '3. Folge' …\n"
            "Beispiel: Tatort S2024E03 Folge 3.mp4")

        ttk.Button(df, text="Alle auswählen",
                   command=self._select_all).grid(row=1, column=5, padx=8, rowspan=2)
        self.dl_btn = ttk.Button(df, text="⬇  Herunterladen",
                                 command=self._start_download)
        self.dl_btn.grid(row=1, column=6, padx=4, rowspan=2)
        ttk.Button(df, text="📋  Zur Watchlist",
                   command=self._add_checked_to_watchlist).grid(
            row=0, column=6, padx=4, pady=(0, 2))

    # ── Download-Tab ──────────────────────────────────────────────────────────

    def _build_download_tab(self, parent):
        top = ttk.Frame(parent)
        top.pack(fill=tk.X, padx=8, pady=(8, 4))
        self.dl_summary_var = tk.StringVar(value="Keine Downloads.")
        ttk.Label(top, textvariable=self.dl_summary_var,
                  font=("Segoe UI", 10, "bold")).pack(side=tk.LEFT, padx=4)
        ttk.Button(top, text="🧹 Erledigte löschen",
                   command=self._clear_done).pack(side=tk.RIGHT, padx=4)
        ttk.Button(top, text="🗑 Liste leeren",
                   command=self._clear_all_jobs).pack(side=tk.RIGHT, padx=4)
        self.retry_btn = ttk.Button(top, text="🔁 Fehler erneut",
                                    command=self._retry_failed_jobs)
        self.retry_btn.pack(side=tk.RIGHT, padx=4)
        self.stop_sel_btn = ttk.Button(top, text="⏹ Auswahl stoppen",
                                       command=self._cancel_selected_jobs)
        self.stop_sel_btn.pack(side=tk.RIGHT, padx=4)
        self.cancel_btn = ttk.Button(top, text="⏹ Alle abbrechen",
                                     command=self._cancel_downloads, state=tk.DISABLED)
        self.cancel_btn.pack(side=tk.RIGHT, padx=4)
        self.pause_btn = ttk.Button(top, text="⏸ Pause",
                                    command=self._toggle_pause, state=tk.DISABLED)
        self.pause_btn.pack(side=tk.RIGHT, padx=4)
        ttk.Separator(top, orient=tk.VERTICAL).pack(side=tk.RIGHT, fill=tk.Y, padx=6, pady=3)
        ttk.Button(top, text="↓", width=2,
                   command=self._move_selected_down).pack(side=tk.RIGHT, padx=1)
        ttk.Button(top, text="↑", width=2,
                   command=self._move_selected_up).pack(side=tk.RIGHT, padx=1)
        ttk.Label(top, text="Reihenfolge:").pack(side=tk.RIGHT, padx=(4, 2))

        pf = ttk.Frame(parent)
        pf.pack(fill=tk.X, padx=8, pady=(0, 4))
        ttk.Label(pf, text="Gesamt:").pack(side=tk.LEFT, padx=4)
        self.total_progress = ttk.Progressbar(pf, mode="determinate", length=400)
        self.total_progress.pack(side=tk.LEFT, padx=4)
        self.total_pct_var = tk.StringVar(value="")
        ttk.Label(pf, textvariable=self.total_pct_var, width=8).pack(side=tk.LEFT)
        ttk.Separator(pf, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=12, pady=2)
        ttk.Label(pf, text="Max. KB/s:").pack(side=tk.LEFT, padx=(0, 2))
        self.speed_limit_var = tk.StringVar(
            value=str(self._watchlist.get("speed_limit_kbps", 0)))
        sp_entry = ttk.Entry(pf, textvariable=self.speed_limit_var, width=7)
        sp_entry.pack(side=tk.LEFT)
        self.speed_limit_var.trace_add("write", lambda *_: self._save_speed_limit())
        ttk.Label(pf, text="(0 = unbegrenzt)", foreground="gray").pack(side=tk.LEFT, padx=4)

        # ── Zeitgesteuerte Geschwindigkeit ────────────────────────────────────
        tf = ttk.Frame(parent)
        tf.pack(fill=tk.X, padx=8, pady=(0, 2))
        self.time_limit_var = tk.BooleanVar(
            value=bool(self._watchlist.get("time_limit_enabled", False)))
        ttk.Checkbutton(tf, text="Zeitsteuerung:", variable=self.time_limit_var,
                        command=self._save_speed_limit).pack(side=tk.LEFT, padx=(0, 4))
        ttk.Label(tf, text="Volle Speed").pack(side=tk.LEFT)
        self.tl_fullstart_var = tk.StringVar(
            value=self._watchlist.get("time_limit_day_end", "22:00"))
        ttk.Entry(tf, textvariable=self.tl_fullstart_var, width=6).pack(side=tk.LEFT, padx=2)
        self.tl_fullstart_var.trace_add("write", lambda *_: self._save_speed_limit())
        ttk.Label(tf, text="–").pack(side=tk.LEFT)
        self.tl_fullend_var = tk.StringVar(
            value=self._watchlist.get("time_limit_day_start", "06:00"))
        ttk.Entry(tf, textvariable=self.tl_fullend_var, width=6).pack(side=tk.LEFT, padx=2)
        self.tl_fullend_var.trace_add("write", lambda *_: self._save_speed_limit())
        ttk.Label(tf, text="  Tageslimit:").pack(side=tk.LEFT, padx=(8, 2))
        self.tl_daykbps_var = tk.StringVar(
            value=str(self._watchlist.get("time_limit_day_kbps", 500)))
        ttk.Entry(tf, textvariable=self.tl_daykbps_var, width=6).pack(side=tk.LEFT, padx=2)
        self.tl_daykbps_var.trace_add("write", lambda *_: self._save_speed_limit())
        ttk.Label(tf, text="KB/s", foreground="gray").pack(side=tk.LEFT)

        lf = ttk.LabelFrame(parent, text="Dateien", padding=6)
        lf.pack(fill=tk.BOTH, expand=True, padx=8, pady=(0, 8))
        dl_cols = ("status", "topic", "title", "channel", "progress", "size", "speed")
        self.dl_tree = ttk.Treeview(lf, columns=dl_cols, show="headings",
                                    selectmode="extended", height=16)
        self.dl_tree.heading("status",   text="Status")
        self.dl_tree.heading("topic",    text="Serie / Sendung")
        self.dl_tree.heading("title",    text="Titel")
        self.dl_tree.heading("channel",  text="Sender")
        self.dl_tree.heading("progress", text="Fortschritt")
        self.dl_tree.heading("size",     text="Größe")
        self.dl_tree.heading("speed",    text="Geschw.")
        self.dl_tree.column("status",   width=125, anchor=tk.CENTER)
        self.dl_tree.column("topic",    width=170)
        self.dl_tree.column("title",    width=220)
        self.dl_tree.column("channel",  width=70,  anchor=tk.CENTER)
        self.dl_tree.column("progress", width=165, anchor=tk.W)
        self.dl_tree.column("size",     width=95,  anchor=tk.CENTER)
        self.dl_tree.column("speed",    width=85,  anchor=tk.CENTER)
        self.dl_tree.tag_configure("st_wait", foreground="#888888")
        self.dl_tree.tag_configure("st_dl",   background="#ddeeff", foreground="#003399")
        self.dl_tree.tag_configure("st_done", background="#d4edda", foreground="#155724")
        self.dl_tree.tag_configure("st_err",  background="#f8d7da", foreground="#721c24")
        self.dl_tree.tag_configure("st_skip", foreground="#666666")
        dl_vsb = ttk.Scrollbar(lf, orient=tk.VERTICAL, command=self.dl_tree.yview)
        self.dl_tree.configure(yscrollcommand=dl_vsb.set)
        self.dl_tree.grid(row=0, column=0, sticky="nsew")
        dl_vsb.grid(row=0, column=1, sticky="ns")
        lf.rowconfigure(0, weight=1)
        lf.columnconfigure(0, weight=1)

        self._dl_ctx_menu = tk.Menu(self.dl_tree, tearoff=0)
        self._dl_ctx_menu.add_command(label="🔁  Neu starten",
                                      command=self._restart_selected_jobs)
        self._dl_ctx_menu.add_separator()
        self._dl_ctx_menu.add_command(label="↑  Nach oben",
                                      command=self._move_selected_up)
        self._dl_ctx_menu.add_command(label="↓  Nach unten",
                                      command=self._move_selected_down)
        self._dl_ctx_menu.add_separator()
        self._dl_ctx_menu.add_command(label="📁  Ordner öffnen",
                                      command=self._open_selected_folder)
        self._dl_ctx_menu.add_separator()
        self._dl_ctx_menu.add_command(label="⏹  Stoppen",
                                      command=self._cancel_selected_jobs)
        self._dl_ctx_menu.add_command(label="🗑  Aus Liste entfernen",
                                      command=self._remove_selected_jobs)
        self._dl_ctx_menu.add_command(label="🗑  Datei löschen + entfernen",
                                      command=self._delete_selected_files)
        self.dl_tree.bind("<Button-3>",    self._show_dl_ctx_menu)
        self.dl_tree.bind("<Delete>",      lambda e: self._remove_selected_jobs())
        self.dl_tree.bind("<Control-Up>",  lambda e: self._move_selected_up())
        self.dl_tree.bind("<Control-Down>",lambda e: self._move_selected_down())

    # ── Watchlist-Tab ─────────────────────────────────────────────────────────

    def _build_watchlist_tab(self, parent):
        # Downloadpfad
        pf = ttk.LabelFrame(parent, text="Download-Pfad", padding=8)
        pf.pack(fill=tk.X, padx=8, pady=(8, 4))
        ttk.Label(pf, text="Speicherort:").pack(side=tk.LEFT, padx=4)
        self.wl_folder_var = tk.StringVar(
            value=self._watchlist.get("folder", os.path.expanduser("~/Downloads")))
        ttk.Entry(pf, textvariable=self.wl_folder_var, width=50).pack(side=tk.LEFT, padx=4)
        ttk.Button(pf, text="…",
                   command=self._choose_wl_folder).pack(side=tk.LEFT, padx=2)
        ttk.Label(pf, text="  Hier landen alle Watchlist-Downloads. Unterordner werden automatisch angelegt.",
                  foreground="gray").pack(side=tk.LEFT, padx=8)

        # Eingabe-Bereich
        ef = ttk.LabelFrame(parent, text="Neue Sendung hinzufügen", padding=10)
        ef.pack(fill=tk.X, padx=8, pady=(4, 4))

        ttk.Label(ef, text="Sendung / Thema:").grid(row=0, column=0, sticky=tk.W, padx=4)
        self.wl_topic_var = tk.StringVar()
        ttk.Entry(ef, textvariable=self.wl_topic_var, width=24).grid(row=0, column=1, padx=4)

        ttk.Label(ef, text="Sender:").grid(row=0, column=2, sticky=tk.W, padx=4)
        self.wl_channel_var = tk.StringVar(value="Alle")
        ttk.Combobox(ef, textvariable=self.wl_channel_var, values=CHANNELS,
                     width=12, state="readonly").grid(row=0, column=3, padx=4)

        ttk.Label(ef, text="Titelfilter:").grid(row=0, column=4, sticky=tk.W, padx=4)
        self.wl_filter_var = tk.StringVar()
        ttk.Entry(ef, textvariable=self.wl_filter_var, width=20).grid(row=0, column=5, padx=4)

        ttk.Label(ef, text="Qualität:").grid(row=0, column=6, sticky=tk.W, padx=4)
        self.wl_quality_var = tk.StringVar(value="HD")
        ttk.Combobox(ef, textvariable=self.wl_quality_var,
                     values=["HD", "Normal", "SD"],
                     width=8, state="readonly").grid(row=0, column=7, padx=4)

        ttk.Button(ef, text="+ Hinzufügen",
                   command=self._add_watchlist_entry).grid(row=0, column=8, padx=8)

        # Watchlist-Tabelle
        wf = ttk.LabelFrame(parent, text="Gespeicherte Sendungen", padding=8)
        wf.pack(fill=tk.BOTH, expand=True, padx=8, pady=4)

        wl_cols = ("topic", "channel", "filter", "quality", "duration",
                   "schedule", "last_checked", "dl_count")
        self.wl_tree = ttk.Treeview(wf, columns=wl_cols, show="headings", selectmode="extended")
        self.wl_tree.heading("topic",        text="Sendung")
        self.wl_tree.heading("channel",      text="Sender")
        self.wl_tree.heading("filter",       text="Titelfilter")
        self.wl_tree.heading("quality",      text="Qualität")
        self.wl_tree.heading("duration",     text="Dauer (min)")
        self.wl_tree.heading("schedule",     text="Zeitplan")
        self.wl_tree.heading("last_checked", text="Zuletzt geprüft")
        self.wl_tree.heading("dl_count",     text="Bekannt (?)")
        self.wl_tree.column("topic",        width=160)
        self.wl_tree.column("channel",      width=70,  anchor=tk.CENTER)
        self.wl_tree.column("filter",       width=110)
        self.wl_tree.column("quality",      width=60,  anchor=tk.CENTER)
        self.wl_tree.column("duration",     width=80,  anchor=tk.CENTER)
        self.wl_tree.column("schedule",     width=130, anchor=tk.CENTER)
        self.wl_tree.column("last_checked", width=120, anchor=tk.CENTER)
        self.wl_tree.column("dl_count",     width=70,  anchor=tk.CENTER)
        Tooltip(self.wl_tree,
            "Bekannt = Folgen die bereits auf der Festplatte liegen\n"
            "(egal ob via Watchlist oder manuell heruntergeladen).\n"
            "Diese werden beim nächsten Check automatisch übersprungen.")
        wl_vsb = ttk.Scrollbar(wf, orient=tk.VERTICAL, command=self.wl_tree.yview)
        self.wl_tree.configure(yscrollcommand=wl_vsb.set)
        self.wl_tree.grid(row=0, column=0, sticky="nsew")
        wl_vsb.grid(row=0, column=1, sticky="ns")
        wf.rowconfigure(0, weight=1)
        wf.columnconfigure(0, weight=1)
        self.wl_tree.bind("<<TreeviewSelect>>", self._on_wl_entry_select)

        # Einstellungen pro Eintrag
        of = ttk.LabelFrame(parent,
            text="Einstellungen für ausgewählten Eintrag", padding=8)
        of.pack(fill=tk.X, padx=8, pady=(0, 4))
        ttk.Label(of, text="← Eintrag wählen", foreground="gray").pack(
            side=tk.RIGHT, padx=8)

        self.wl_filter_access_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(of,
            text="Barrierefreiheits-Versionen ausblenden  (Hörgeschädigte / Gebärdensprache / Hörfassung / Audiodeskription)",
            variable=self.wl_filter_access_var,
            command=self._save_wl_entry_settings).pack(side=tk.LEFT, padx=4)

        self.wl_subtitles_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(of, text="Untertitel herunterladen",
            variable=self.wl_subtitles_var,
            command=self._save_wl_entry_settings).pack(side=tk.LEFT, padx=16)

        self.wl_series_fmt_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(of, text="Serienformat-Benennung  (Serientitel S2024E03 Folgentitel.mp4)",
            variable=self.wl_series_fmt_var,
            command=self._save_wl_entry_settings).pack(side=tk.LEFT, padx=16)

        dur_of = ttk.Frame(of)
        dur_of.pack(side=tk.LEFT, padx=20)
        ttk.Label(dur_of, text="Dauer:  min").pack(side=tk.LEFT)
        self.wl_dur_min_var = tk.StringVar(value="")
        self.wl_dur_min_var.trace_add("write", lambda *_: self._save_wl_entry_settings())
        ttk.Spinbox(dur_of, from_=0, to=600, textvariable=self.wl_dur_min_var,
                    width=5, command=self._save_wl_entry_settings).pack(side=tk.LEFT, padx=2)
        ttk.Label(dur_of, text="–  max").pack(side=tk.LEFT, padx=(4, 0))
        self.wl_dur_max_var = tk.StringVar(value="")
        self.wl_dur_max_var.trace_add("write", lambda *_: self._save_wl_entry_settings())
        ttk.Spinbox(dur_of, from_=0, to=600, textvariable=self.wl_dur_max_var,
                    width=5, command=self._save_wl_entry_settings).pack(side=tk.LEFT, padx=2)
        ttk.Label(dur_of, text="min").pack(side=tk.LEFT, padx=2)

        lang_of = ttk.Frame(of)
        lang_of.pack(side=tk.LEFT, padx=16)
        ttk.Label(lang_of, text="Sprache:").pack(side=tk.LEFT)
        self.wl_lang_var = tk.StringVar(value="Alle")
        wl_lang_box = ttk.Combobox(lang_of, textvariable=self.wl_lang_var,
                                   values=LANG_OPTIONS, width=18, state="readonly")
        wl_lang_box.pack(side=tk.LEFT, padx=4)
        wl_lang_box.bind("<<ComboboxSelected>>",
                         lambda _: self._save_wl_entry_settings())

        exist_of = ttk.Frame(of)
        exist_of.pack(side=tk.LEFT, padx=16)
        ttk.Label(exist_of, text="Vorhandene:").pack(side=tk.LEFT)
        self.wl_exist_action_var = tk.StringVar(value="skip")
        wl_exist_box = ttk.Combobox(exist_of, textvariable=self.wl_exist_action_var,
                                    values=["skip", "overwrite", "size"],
                                    width=10, state="readonly")
        wl_exist_box.pack(side=tk.LEFT, padx=4)
        wl_exist_box.bind("<<ComboboxSelected>>",
                          lambda _: self._save_wl_entry_settings())

        sched_of = ttk.LabelFrame(of, text="Automatischer Zeitplan", padding=4)
        sched_of.pack(side=tk.LEFT, padx=16, pady=2)
        ttk.Label(sched_of, text="Tag:").pack(side=tk.LEFT)
        self.wl_sched_day_var = tk.StringVar(value="Deaktiviert")
        _day_box = ttk.Combobox(sched_of, textvariable=self.wl_sched_day_var,
                                values=["Deaktiviert", "Täglich",
                                        "Montag", "Dienstag", "Mittwoch",
                                        "Donnerstag", "Freitag", "Samstag", "Sonntag"],
                                width=12, state="readonly")
        _day_box.pack(side=tk.LEFT, padx=4)
        _day_box.bind("<<ComboboxSelected>>", lambda _: self._save_wl_entry_settings())
        ttk.Label(sched_of, text="Uhrzeiten:").pack(side=tk.LEFT, padx=(8, 0))
        self.wl_sched_time_var = tk.StringVar(value="")
        self.wl_sched_time_var.trace_add("write", lambda *_: self._save_wl_entry_settings())
        _time_entry = ttk.Entry(sched_of, textvariable=self.wl_sched_time_var, width=22)
        _time_entry.pack(side=tk.LEFT, padx=4)
        Tooltip(_time_entry,
                "Eine oder mehrere Uhrzeiten, kommagetrennt.\n"
                "Beispiel: 08:00, 14:00, 22:00")
        ttk.Label(sched_of, text="(HH:MM, HH:MM, …)", foreground="gray").pack(side=tk.LEFT)

        # Steuerung
        bf = ttk.Frame(parent)
        bf.pack(fill=tk.X, padx=8, pady=(4, 8))

        self.wl_check_btn = ttk.Button(bf, text="🔄  Jetzt alle prüfen & herunterladen",
                                       command=self._start_watchlist_check)
        self.wl_check_btn.pack(side=tk.LEFT, padx=4)

        self.wl_auto_var = tk.BooleanVar(
            value=self._watchlist.get("auto_check_on_start", True))
        ttk.Checkbutton(bf, text="Beim Programmstart automatisch prüfen",
                        variable=self.wl_auto_var,
                        command=self._save_watchlist).pack(side=tk.LEFT, padx=12)

        ttk.Button(bf, text="Auswahl entfernen",
                   command=self._remove_watchlist_entries).pack(side=tk.RIGHT, padx=4)
        ttk.Button(bf, text="🔁 Verlauf bereinigen",
                   command=self._reset_watchlist_entries).pack(side=tk.RIGHT, padx=4)
        ttk.Button(bf, text="🔁 Alle zurücksetzen",
                   command=self._reset_all_watchlist_entries).pack(side=tk.RIGHT, padx=4)

        self.wl_status_var = tk.StringVar(value="")
        ttk.Label(bf, textvariable=self.wl_status_var,
                  foreground="gray").pack(side=tk.LEFT, padx=12)

    # ═══════════════════════════════════════════════════════════════════════════
    # Suche
    # ── Umbenennen-Tab ────────────────────────────────────────────────────────

    def _build_rename_tab(self, parent):
        self._tvdb_series_data = []
        self._tvdb_file_rows   = []   # [{dir, filename, s, e, gid, rv_iid, …}]
        self._tvdb_episodes    = {}   # {(s, e): title} – Einzelserien-Legacy
        self._tvdb_serie_name  = ""
        # ── Mehrere Serien in einem Durchgang ────────────────────────────────
        self._tvdb_rows_by_iid  = {}     # rv_iid -> row  (autoritative Bindung)
        self._tvdb_groups       = {}     # gid -> group-dict
        self._tvdb_group_order  = []     # Anzeigereihenfolge der Gruppen
        self._tvdb_api_cache    = {}     # (source, series_id, lang, order) -> payload
        self._tvdb_search_cache = {}     # (source, query, lang) -> results
        self._tvdb_load_roots   = set()  # selbst gewählte Ordner – nie löschen
        self._tvdb_skipped_samples = 0   # übersprungene Sample-Dateien
        self._tvdb_batch_busy   = False  # läuft ein Zuordnungslauf?
        self._tvdb_batch_token  = 0      # entwertet verspätete Threads
        self._tvdb_watchdog     = None   # after()-Handle
        self.rename_mode_var   = tk.StringVar(value="series")

        # ── Kopfzeile: Modus, Quelle, Einstellungen, Status ──────────────────
        # Bewusst EINE schmale Zeile – API-Keys und Formatvorlagen sind
        # Einmal-Einstellungen und liegen im Dialog „⚙ API & Format“.
        # Der gewonnene Platz kommt den Dateilisten zugute.
        head = ttk.Frame(parent)
        head.pack(fill=tk.X, padx=8, pady=(8, 4))
        self._rename_mode_toggle = head

        ttk.Label(head, text="Modus:").pack(side=tk.LEFT, padx=(4, 2))
        ttk.Radiobutton(head, text="📺 Serien", variable=self.rename_mode_var,
                        value="series",
                        command=self._on_rename_mode_change).pack(side=tk.LEFT, padx=4)
        ttk.Radiobutton(head, text="🎬 Filme", variable=self.rename_mode_var,
                        value="movie",
                        command=self._on_rename_mode_change).pack(side=tk.LEFT, padx=4)

        ttk.Separator(head, orient="vertical").pack(side=tk.LEFT, fill=tk.Y, padx=10)

        # Quelle – gehört nach oben, weil sie das Ergebnis sichtbar beeinflusst
        self.series_source_var = tk.StringVar(
            value=self._watchlist.get("series_source", "TheTVDB"))
        self.movie_source_var = tk.StringVar(
            value=self._watchlist.get("movie_source", "TheMovieDB"))
        ttk.Label(head, text="Quelle:").pack(side=tk.LEFT, padx=(0, 2))
        self._src_box = ttk.Combobox(head, textvariable=self.series_source_var,
                                     width=12, state="readonly",
                                     values=["TheTVDB", "Trakt.tv", "TVmaze"])
        self._src_box.pack(side=tk.LEFT, padx=2)
        self._src_box.bind("<<ComboboxSelected>>", lambda _: self._save_source_choice())
        Tooltip(self._src_box,
                "TheTVDB = Standard, beste deutsche Episodentitel\n"
                "Trakt.tv = Alternative wenn TVDB nichts findet\n"
                "TVmaze  = ohne API-Key; deutsche Titel bei deutschen\n"
                "          Produktionen (ARD/ZDF/KiKA), sonst Originalsprache\n"
                "Hinweis: die {tvdb-…}-ID im Ordnernamen gibt es nur bei TheTVDB.")

        _api_btn = ttk.Button(head, text="⚙ API & Format",
                              command=self._show_api_settings)
        _api_btn.pack(side=tk.LEFT, padx=10)
        Tooltip(_api_btn, "API-Keys, Sprache, Reihenfolge und Namensvorlage")

        self.tvdb_status_var = tk.StringVar(value="")
        ttk.Label(head, textvariable=self.tvdb_status_var,
                  foreground="gray").pack(side=tk.LEFT, padx=8)

        # ── Einstellungs-Variablen (Widgets liegen im ⚙-Dialog) ──────────────
        self.tvdb_key_var   = tk.StringVar(value=self._watchlist.get("tvdb_api_key", ""))
        self.tvdb_lang_var  = tk.StringVar(value=self._watchlist.get("tvdb_lang", "deu"))
        self.tvdb_order_var = tk.StringVar(value=self._watchlist.get("tvdb_order", "official"))
        self.tvdb_fmt_var   = tk.StringVar(
            value=self._watchlist.get("tvdb_fmt", "{serie} - S{s:02d}E{e:02d} - {titel}.mp4"))
        self.trakt_key_var  = tk.StringVar(value=self._watchlist.get("trakt_client_id", ""))
        self.tmdb_key_var   = tk.StringVar(value=self._watchlist.get("tmdb_api_key", ""))
        self.tmdb_lang_var  = tk.StringVar(value=self._watchlist.get("tmdb_lang", "de"))
        self.tmdb_fmt_var   = tk.StringVar(
            value=self._watchlist.get("tmdb_fmt", "{titel} ({jahr}).mp4"))
        self.omdb_key_var   = tk.StringVar(value=self._watchlist.get("omdb_api_key", ""))

        # (Die früheren Blöcke „Serien-Einstellungen“ und
        #  „Film-Einstellungen“ liegen jetzt im Dialog _show_api_settings –
        #  sie belegten rund 200 px Höhe, die den Dateilisten fehlten.)

        # ── Seriensuche (oben rechts) ─────────────────────────────────────────
        qf = ttk.LabelFrame(parent, text="Serie zuordnen", padding=8)
        qf.pack(fill=tk.X, padx=8, pady=(0, 4))

        # Klassische Einzelserien-Zeile – bleibt sichtbar solange nur EINE
        # Serie erkannt wurde, damit der bisherige Ablauf unverändert bleibt.
        single = ttk.Frame(qf)
        single.pack(fill=tk.X)
        self._qf_single_row = single

        ttk.Label(single, text="Serienname:").pack(side=tk.LEFT, padx=4)
        self.tvdb_search_var = tk.StringVar()
        ttk.Entry(single, textvariable=self.tvdb_search_var,
                  width=24).pack(side=tk.LEFT, padx=4)
        self.tvdb_search_btn = ttk.Button(single, text="🔍 Suchen",
                                          command=self._tvdb_search_series)
        self.tvdb_search_btn.pack(side=tk.LEFT, padx=4)

        ttk.Label(single, text="Gefundene Serie:").pack(side=tk.LEFT, padx=(12, 4))
        self.tvdb_series_var = tk.StringVar()
        self.tvdb_series_box = ttk.Combobox(single, textvariable=self.tvdb_series_var,
                                            width=34, state="readonly")
        self.tvdb_series_box.pack(side=tk.LEFT, padx=4)

        self.tvdb_match_btn = ttk.Button(single, text="📋 Zuordnen",
                                         command=self._tvdb_run_match,
                                         state=tk.DISABLED)
        self.tvdb_match_btn.pack(side=tk.LEFT, padx=8)
        # Die Statusanzeige sitzt jetzt in der Kopfzeile – hier keine zweite,
        # sonst würde tvdb_status_var überschrieben und die obere wäre tot.

        # ── Gruppen-Ansicht (nur bei mehreren erkannten Serien) ──────────────
        self._grp_frame = ttk.Frame(qf)
        # (wird von _rebuild_groups ein-/ausgeblendet)

        g_cols = ("serie", "count", "assigned", "state")
        self.grp_tree = ttk.Treeview(self._grp_frame, columns=g_cols,
                                     show="headings", height=5,
                                     selectmode="browse")
        self.grp_tree.heading("serie",    text="Serie (aus Dateinamen)")
        self.grp_tree.heading("count",    text="Dateien")
        self.grp_tree.heading("assigned", text="Zugeordnete Serie")
        self.grp_tree.heading("state",    text="Status")
        self.grp_tree.column("serie",    width=200, anchor=tk.W)
        self.grp_tree.column("count",    width=70,  anchor=tk.CENTER)
        self.grp_tree.column("assigned", width=250, anchor=tk.W)
        self.grp_tree.column("state",    width=110, anchor=tk.W)
        self.grp_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.grp_tree.tag_configure("grp_ok",     background="#d4edda", foreground="#155724")
        self.grp_tree.tag_configure("grp_ambig",  background="#fff3cd", foreground="#856404")
        self.grp_tree.tag_configure("grp_failed", background="#f8d7da", foreground="#721c24")
        self.grp_tree.tag_configure("grp_none",   foreground="#888888")

        self.grp_tree.bind("<<TreeviewSelect>>", self._on_grp_select)
        self.grp_tree.bind("<Double-1>",         lambda _: self._grp_pick_series())

        gbtn = ttk.Frame(self._grp_frame)
        gbtn.pack(side=tk.RIGHT, fill=tk.Y, padx=(6, 0))
        ttk.Button(gbtn, text="🔍 Serie wählen …",
                   command=self._grp_pick_series).pack(fill=tk.X, pady=1)
        ttk.Button(gbtn, text="⇵ Zusammenführen",
                   command=self._grp_merge).pack(fill=tk.X, pady=1)
        ttk.Button(gbtn, text="↺ Zurücksetzen",
                   command=self._grp_reset).pack(fill=tk.X, pady=1)
        self.grp_status_var = tk.StringVar(value="")
        ttk.Label(gbtn, textvariable=self.grp_status_var,
                  foreground="gray").pack(anchor="w", pady=(4, 0))

        self._qf_frame = qf   # store for show/hide

        # ── Film-Suche (nur im Film-Modus sichtbar) ───────────────────────────
        self._tmdb_qf_frame = ttk.LabelFrame(parent, text="Filme zuordnen", padding=8)
        # (packed/hidden by _on_rename_mode_change)
        self.tmdb_match_btn = ttk.Button(self._tmdb_qf_frame,
                                         text="🎬 Alle Filme suchen",
                                         command=self._tmdb_run_match)
        self.tmdb_match_btn.pack(side=tk.LEFT, padx=8)
        self.tmdb_status_var = tk.StringVar(value="")
        ttk.Label(self._tmdb_qf_frame, textvariable=self.tmdb_status_var,
                  foreground="gray").pack(side=tk.LEFT, padx=4)

        # ── Zwei Panels nebeneinander ─────────────────────────────────────────
        pw = ttk.PanedWindow(parent, orient=tk.HORIZONTAL)
        pw.pack(fill=tk.BOTH, expand=True, padx=8, pady=4)

        # ── Linke Seite: Dateien ──────────────────────────────────────────────
        lf = ttk.LabelFrame(pw, text="Dateien  (Drag & Drop oder Ordner/Dateien wählen)",
                            padding=6)
        pw.add(lf, weight=1)

        l_cols = ("serie", "fname", "se")
        self.lv_tree = ttk.Treeview(lf, columns=l_cols, show="headings",
                                    selectmode="extended", height=18)
        self.lv_tree.heading("serie", text="Serie")
        self.lv_tree.heading("fname", text="Dateiname")
        self.lv_tree.heading("se",    text="Erkannt")
        self.lv_tree.column("serie", width=145)
        self.lv_tree.column("fname", width=230)
        self.lv_tree.column("se",    width=70, anchor=tk.CENTER)
        lv_vsb = ttk.Scrollbar(lf, orient=tk.VERTICAL)
        self.lv_tree.configure(yscrollcommand=lv_vsb.set)
        lv_vsb.configure(command=self._sync_scroll_from_left)
        self.lv_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        lv_vsb.pack(side=tk.LEFT, fill=tk.Y)

        wm_text = ("📂  Dateien oder Ordner\nhier hineinziehen"
                   if HAS_DND else
                   "📁  Ordner / Dateien-Button\nnutzen (kein Drag & Drop)")
        self._lv_watermark = tk.Label(lf, text=wm_text,
                                      fg="#b0b0b0", font=("", 10),
                                      justify=tk.CENTER, bg="white")
        self._lv_watermark.place(in_=self.lv_tree, relx=0.5, rely=0.42,
                                 anchor=tk.CENTER)

        lb_btns = ttk.Frame(lf)
        lb_btns.pack(fill=tk.X, pady=(4, 0))
        self.scan_btn = ttk.Button(lb_btns, text="🔄 Scan-Ordner einlesen",
                                   command=self._tvdb_scan_folder)
        self.scan_btn.pack(fill=tk.X, padx=4, pady=1)
        Tooltip(self.scan_btn,
                "Liest den fest eingestellten Ordner ein – je nach Modus den\n"
                "Serien- oder den Film-Scan-Ordner. Unterordner werden\n"
                "mitgenommen, Sample-Dateien übersprungen.\n"
                "Die Ordner stellst du über ⚙ bei den Einsortier-Einstellungen ein.")
        ttk.Separator(lb_btns, orient="horizontal").pack(fill=tk.X, padx=4, pady=3)
        ttk.Button(lb_btns, text="📁 Ordner",
                   command=self._tvdb_add_folder).pack(fill=tk.X, padx=4, pady=1)
        ttk.Button(lb_btns, text="🎬 Dateien",
                   command=self._tvdb_add_files).pack(fill=tk.X, padx=4, pady=1)
        ttk.Button(lb_btns, text="🗑 Leeren",
                   command=self._tvdb_clear_files).pack(fill=tk.X, padx=4, pady=1)
        ttk.Label(lb_btns, text="(Strg+Klick = mehrere)",
                  foreground="gray").pack(pady=(4, 0))

        # Drag & Drop registrieren
        if HAS_DND:
            self.lv_tree.drop_target_register(DND_FILES)
            self.lv_tree.dnd_bind("<<Drop>>", self._tvdb_on_drop)

        # ── Rechte Seite: TheTVDB-Treffer ────────────────────────────────────
        rf = ttk.LabelFrame(pw, text="TheTVDB Zuordnung", padding=6)
        pw.add(rf, weight=1)

        r_cols = ("new_name", "ep_title", "status")
        self.rv_tree = ttk.Treeview(rf, columns=r_cols, show="headings",
                                    selectmode="extended", height=18)
        self.rv_tree.heading("new_name",  text="Neuer Dateiname")
        self.rv_tree.heading("ep_title",  text="Episodentitel (TheTVDB)")
        self.rv_tree.heading("status",    text="")
        self.rv_tree.column("new_name",  width=290)
        self.rv_tree.column("ep_title",  width=180)
        self.rv_tree.column("status",    width=30, anchor=tk.CENTER)
        self.rv_tree.tag_configure("ok_high", background="#d4edda", foreground="#155724")  # ≥85% grün
        self.rv_tree.tag_configure("ok_mid",  background="#eaf4d0", foreground="#3a6b00")  # 60-85% gelbgrün
        self.rv_tree.tag_configure("ok_se",   background="#cce5ff", foreground="#004085")  # S/E-Treffer blau
        self.rv_tree.tag_configure("nomatch", background="#fff3cd", foreground="#856404")  # kein Treffer gelb
        self.rv_tree.tag_configure("nose",    foreground="#aaaaaa")                        # kein S/E grau
        self.rv_tree.tag_configure("ok_manual", background="#e2d9f3", foreground="#3d2a6b") # manuell violett
        self.rv_tree.tag_configure("ok_movie", background="#d4edda", foreground="#155724") # Film grün
        self.rv_tree.tag_configure("ok_low",  background="#ffe0b2", foreground="#7a4100")  # prüfen orange
        rv_vsb = ttk.Scrollbar(rf, orient=tk.VERTICAL)
        self.rv_tree.configure(yscrollcommand=rv_vsb.set)
        rv_vsb.configure(command=self._sync_scroll_from_right)
        self.rv_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        rv_vsb.pack(side=tk.LEFT, fill=tk.Y)

        # Rechtsklick-Kontextmenü
        self._rv_menu = tk.Menu(self.rv_tree, tearoff=0)
        self._rv_menu.add_command(label="🔧  Folge korrigieren …",
                                  command=self._tvdb_fix_episode)
        self._rv_menu.add_command(label="✏  Manuell bearbeiten",
                                  command=self._tvdb_manual_edit)
        self._rv_menu.add_command(label="🔍  Erneut suchen (andere Serie)",
                                  command=self._tvdb_research_selected)
        self.rv_tree.bind("<Button-3>", self._show_rv_menu)
        # Doppelklick auf eine Zeile öffnet direkt die Korrektur
        self.rv_tree.bind("<Double-1>", lambda _: self._tvdb_fix_episode())
        for _t in (self.lv_tree, self.rv_tree):
            _t.bind("<MouseWheel>", self._sync_mousewheel)
        # <ButtonRelease-1> statt <<TreeviewSelect>>: feuert nur bei echten
        # Mausklicks, NICHT bei programmatischem selection_set() → kein Loop.
        self.lv_tree.bind("<ButtonRelease-1>", self._on_lv_select)
        self.rv_tree.bind("<ButtonRelease-1>", self._on_rv_select)

        rb_btns = ttk.Frame(rf)
        rb_btns.pack(fill=tk.X, pady=(4, 0))
        ttk.Button(rb_btns, text="Alle ✓ auswählen",
                   command=self._rv_select_matched).pack(fill=tk.X, padx=4, pady=1)
        self.tvdb_ask_btn = ttk.Button(rb_btns, text="❓ Titel manuell eingeben",
                                       command=self._tvdb_ask_unmatched_btn,
                                       state=tk.DISABLED)
        self.tvdb_ask_btn.pack(fill=tk.X, padx=4, pady=1)
        _fix_btn = ttk.Button(rb_btns, text="🔧 Folge korrigieren …",
                              command=self._tvdb_fix_episode)
        _fix_btn.pack(fill=tk.X, padx=4, pady=1)
        Tooltip(_fix_btn,
                "Für die markierte Zeile Staffel/Folge eintippen oder einen\n"
                "Folgentitel suchen – auch wenn die Zeile schon (falsch)\n"
                "zugeordnet ist. Doppelklick auf eine Zeile geht auch.")
        self.tvdb_apply_btn = ttk.Button(rb_btns, text="✏  Auswahl umbenennen",
                                         command=self._tvdb_apply_rename,
                                         state=tk.DISABLED)
        self.tvdb_apply_btn.pack(fill=tk.X, padx=4, pady=1)
        self.tvdb_apply_all_btn = ttk.Button(
            rb_btns, text="✅  Alle umbenennen",
            command=self._tvdb_apply_all_rename,
            state=tk.DISABLED)
        self.tvdb_apply_all_btn.pack(fill=tk.X, padx=4, pady=1)

        ttk.Separator(rb_btns, orient="horizontal").pack(fill=tk.X, padx=4, pady=4)
        self.sort_after_rename_var = tk.BooleanVar(value=True)
        sort_row = ttk.Frame(rb_btns)
        sort_row.pack(fill=tk.X, padx=4)
        ttk.Checkbutton(sort_row, text="📁 Danach einsortieren",
                        variable=self.sort_after_rename_var).pack(side=tk.LEFT)
        ttk.Button(sort_row, text="⚙", width=3,
                   command=self._show_sort_settings).pack(side=tk.RIGHT, padx=2)

    # ═══════════════════════════════════════════════════════════════════════════
    # TheTVDB-Logik
    # ═══════════════════════════════════════════════════════════════════════════

    # ── Synchrones Scrollen ───────────────────────────────────────────────────

    def _sync_scroll_from_left(self, *args):
        self.lv_tree.yview(*args)
        self.rv_tree.yview(*args)

    def _sync_scroll_from_right(self, *args):
        self.rv_tree.yview(*args)
        self.lv_tree.yview(*args)

    def _sync_mousewheel(self, event):
        delta = -1 * (event.delta // 120)
        self.lv_tree.yview_scroll(delta, "units")
        self.rv_tree.yview_scroll(delta, "units")
        return "break"

    def _on_lv_select(self, event=None):
        # Gebunden auf <ButtonRelease-1>: feuert nur bei echtem Klick,
        # nicht bei programmatischem selection_set() → kein rekursiver Loop.
        sel = self.lv_tree.selection()
        if not sel:
            return
        # Über die Zeilen-Bindung statt über die Position spiegeln
        for row in self._tvdb_file_rows:
            if row.get("lv_iid") == sel[0]:
                target = row.get("rv_iid", "")
                if self.rv_tree.exists(target):
                    self.rv_tree.selection_set(target)
                    self.rv_tree.see(target)
                return
        idx = self.lv_tree.index(sel[0])
        rv_children = self.rv_tree.get_children()
        if idx < len(rv_children):
            target = rv_children[idx]
            self.rv_tree.selection_set(target)
            self.rv_tree.see(target)

    def _on_rv_select(self, event=None):
        sel = self.rv_tree.selection()
        if not sel:
            return
        row = self._tvdb_rows_by_iid.get(sel[0])
        if row is not None:
            target = row.get("lv_iid", "")
            if self.lv_tree.exists(target):
                self.lv_tree.selection_set(target)
                self.lv_tree.see(target)
            return
        idx = self.rv_tree.index(sel[0])
        lv_children = self.lv_tree.get_children()
        if idx < len(lv_children):
            target = lv_children[idx]
            self.lv_tree.selection_set(target)
            self.lv_tree.see(target)

    # ── Einstellungen ─────────────────────────────────────────────────────────

    def _save_tvdb_key(self):
        self._watchlist["tvdb_api_key"]    = self.tvdb_key_var.get().strip()
        self._watchlist["tvdb_lang"]       = self.tvdb_lang_var.get()
        self._watchlist["tvdb_fmt"]        = self.tvdb_fmt_var.get()
        self._watchlist["tvdb_order"]      = self.tvdb_order_var.get()
        self._watchlist["series_source"]   = self.series_source_var.get()
        self._watchlist["trakt_client_id"] = self.trakt_key_var.get().strip()
        self._save_watchlist()
        self.tvdb_status_var.set("✓ Gespeichert.")

    def _save_speed_limit(self):
        try:
            val = max(0, int(self.speed_limit_var.get() or 0))
        except ValueError:
            return
        self._watchlist["speed_limit_kbps"]     = val
        self._watchlist["time_limit_enabled"]    = self.time_limit_var.get()
        self._watchlist["time_limit_day_end"]    = self.tl_fullstart_var.get().strip()
        self._watchlist["time_limit_day_start"]  = self.tl_fullend_var.get().strip()
        try:
            self._watchlist["time_limit_day_kbps"] = max(1, int(self.tl_daykbps_var.get() or 500))
        except ValueError:
            pass
        self._save_watchlist()

    def _tvdb_client(self):
        if self.series_source_var.get() == "TVmaze":
            return TVmazeClient()   # kein Key nötig

        if self.series_source_var.get() == "Trakt.tv":
            cid = self.trakt_key_var.get().strip()
            if not cid:
                messagebox.showwarning("Client-ID fehlt",
                    "Bitte Trakt.tv Client-ID eingeben und speichern.\n"
                    "Kostenlos: trakt.tv → Settings → Your API Apps")
                return None
            return TraktClient(cid)

        key = self.tvdb_key_var.get().strip()
        if not key:
            messagebox.showwarning("API-Key fehlt",
                "Bitte TheTVDB API-Key eingeben und speichern.\n"
                "Kostenlos: thetvdb.com → Account → API Access")
            return None
        return TVDBClient(key)

    # ── Dateien laden (Drag & Drop / Ordner / Auswahl) ────────────────────────

    @staticmethod
    def _parse_dnd(data):
        """Parst tkinterdnd2 Drop-Daten → Liste von Pfaden."""
        paths, data = [], data.strip()
        while data:
            if data.startswith("{"):
                end = data.find("}")
                paths.append(data[1:end] if end != -1 else data[1:])
                data = data[end + 1:].strip() if end != -1 else ""
            else:
                parts = data.split(" ", 1)
                paths.append(parts[0])
                data = parts[1].strip() if len(parts) > 1 else ""
        return paths

    def _tvdb_on_drop(self, event):
        # Während eines laufenden Zuordnungslaufs nichts dazuladen – sonst
        # zeigen die Snapshots des Workers auf eine veränderte Liste.
        if self._tvdb_batch_busy:
            return
        for path in self._parse_dnd(event.data):
            if os.path.isdir(path):
                self._tvdb_load_roots.add(path)
                self._load_files_from_folder(path)
            elif os.path.splitext(path)[1].lower() in _VIDEO_EXTS:
                self._tvdb_load_roots.add(os.path.dirname(path))
                self._add_file_row(os.path.dirname(path), os.path.basename(path))
        self._tvdb_refresh_match_panel()

    def _scan_folder_for_mode(self):
        """Gibt (pfad, bezeichnung) des Scan-Ordners für den aktuellen Modus."""
        if self.rename_mode_var.get() == "movie":
            return self._watchlist.get("scan_movie_folder", "").strip(), "Film"
        return self._watchlist.get("scan_series_folder", "").strip(), "Serien"

    def _tvdb_scan_folder(self):
        """Liest den fest eingestellten Scan-Ordner ein (Knopfdruck)."""
        if self._tvdb_batch_busy:
            return
        folder, bez = self._scan_folder_for_mode()
        if not folder:
            if messagebox.askyesno(
                    f"{bez}-Scan-Ordner fehlt",
                    f"Für {'Filme' if bez == 'Film' else 'Serien'} ist noch kein "
                    "Scan-Ordner eingestellt.\n\nJetzt einstellen?"):
                self._show_sort_settings()
            return
        if not os.path.isdir(folder):
            messagebox.showerror(
                "Ordner nicht gefunden",
                f"Der {bez}-Scan-Ordner existiert nicht:\n{folder}")
            return

        # Bereits geladene Dateien nicht doppelt aufnehmen
        vorhanden = {(r["dir"], r["filename"]) for r in self._tvdb_file_rows}
        vor_zeilen  = len(self._tvdb_file_rows)
        vor_samples = self._tvdb_skipped_samples

        self._tvdb_load_roots.add(folder)
        neu = 0
        for root_dir, _dirs, files in os.walk(folder):
            for fname in sorted(files):
                if os.path.splitext(fname)[1].lower() not in _VIDEO_EXTS:
                    continue
                if (root_dir, fname) in vorhanden:
                    continue
                self._add_file_row(root_dir, fname)
                neu += 1

        neu_geladen = len(self._tvdb_file_rows) - vor_zeilen
        neu_samples = self._tvdb_skipped_samples - vor_samples

        if not neu_geladen:
            hinweis = f"Keine neuen Dateien in:\n{folder}"
            if neu_samples:
                hinweis += f"\n\n({neu_samples} Sample-Datei(en) übersprungen)"
            messagebox.showinfo(f"{bez}-Scan", hinweis)

        self._tvdb_refresh_match_panel()

    def _tvdb_add_folder(self):
        if self._tvdb_batch_busy:
            return
        folder = filedialog.askdirectory(title="Ordner mit MP4-Dateien wählen")
        if folder:
            self._tvdb_load_roots.add(folder)
            self._load_files_from_folder(folder)
            self._tvdb_refresh_match_panel()

    def _tvdb_add_files(self):
        if self._tvdb_batch_busy:
            return
        files = filedialog.askopenfilenames(
            title="Videodateien wählen",
            filetypes=[("Videodateien", "*.mp4 *.mkv *.avi *.mov *.wmv *.ts *.m4v *.flv *.webm *.mpg *.mpeg *.m2ts *.mts"),
                       ("Alle Dateien", "*.*")])
        for fp in files:
            self._tvdb_load_roots.add(os.path.dirname(fp))
            self._add_file_row(os.path.dirname(fp), os.path.basename(fp))
        self._tvdb_refresh_match_panel()

    def _update_lv_watermark(self):
        if self.lv_tree.get_children():
            self._lv_watermark.place_forget()
        else:
            self._lv_watermark.place(in_=self.lv_tree, relx=0.5, rely=0.42,
                                     anchor=tk.CENTER)

    def _tvdb_clear_files(self):
        if self._tvdb_batch_busy:
            return
        self.lv_tree.delete(*self.lv_tree.get_children())
        self.rv_tree.delete(*self.rv_tree.get_children())
        self._tvdb_file_rows.clear()
        self._tvdb_rows_by_iid.clear()
        self._tvdb_groups.clear()
        self._tvdb_group_order.clear()
        self._tvdb_load_roots.clear()
        self._tvdb_skipped_samples = 0
        self._tvdb_series_data = []
        self._rebuild_groups()
        self.tvdb_apply_btn.configure(state=tk.DISABLED)
        self.tvdb_apply_all_btn.configure(state=tk.DISABLED)
        self.tvdb_ask_btn.configure(state=tk.DISABLED)
        self.tvdb_status_var.set("")
        self._update_lv_watermark()

    def _load_files_from_folder(self, folder):
        for root_dir, _dirs, files in os.walk(folder):
            for fname in sorted(files):
                if os.path.splitext(fname)[1].lower() in _VIDEO_EXTS:
                    self._add_file_row(root_dir, fname)

    def _add_file_row(self, directory, fname):
        # Sample-Dateien gar nicht erst aufnehmen – das sind Ausschnitte aus
        # Scene-Releases, keine Folgen und keine Filme.
        if _is_sample_file(directory, fname):
            self._tvdb_skipped_samples += 1
            return
        if self.rename_mode_var.get() == "movie":
            title_guess, year = _parse_movie_filename(fname)
            row = {"dir": directory, "filename": fname, "s": None, "e": None,
                   "year": year, "title_guess": title_guess,
                   "gid": "__movie__", "series_raw": "", "adopted": False,
                   "part": None, "matched_gid": None, "matched_epoch": None}
            lv_iid = self.lv_tree.insert("", tk.END, values=("—", fname, year or "?"))
            rv_iid = self.rv_tree.insert("", tk.END, tags=("nose",),
                                         values=("—", "—", "?"))
            row["lv_iid"], row["rv_iid"] = lv_iid, rv_iid
            self._tvdb_file_rows.append(row)
            self._tvdb_rows_by_iid[rv_iid] = row
            return
        matches = list(_SE_RE.finditer(fname))
        if matches:
            # Gibt es mehrere Treffer (z.B. S2026E156 und S10_E08), bevorzuge
            # den mit der kleinsten Staffelnummer — jahresbasierte (≥1900) nur
            # als letzten Ausweg
            m = min(matches, key=lambda x: int(x.group(1)))
            s  = int(m.group(1))
            e  = int(m.group(2))
            se = m.group(0).upper()
        else:
            s  = None
            e  = _extract_episode(os.path.splitext(fname)[0])
            se = f"E{e:02d}" if e else "—"
        series_raw = _series_from_filename(fname)
        row = {"dir": directory, "filename": fname, "s": s, "e": e,
               "series_raw": series_raw,
               "gid": _series_group_key(series_raw) if series_raw else "",
               "adopted": False, "part": _part_num(fname),
               "matched_gid": None, "matched_epoch": None}
        lv_iid = self.lv_tree.insert("", tk.END,
                                    values=(series_raw or "—", fname, se))
        rv_iid = self.rv_tree.insert("", tk.END, tags=("nose",),
                                     values=("—", "—", "?"))
        row["lv_iid"], row["rv_iid"] = lv_iid, rv_iid
        self._tvdb_file_rows.append(row)
        self._tvdb_rows_by_iid[rv_iid] = row

    @staticmethod
    def _guess_series_name(filenames):
        """Extract likely series name from list of filenames (text before SxxExx / Folge)."""
        def _clean(raw):
            s = re.sub(r'[._]', ' ', raw).strip()
            s = _CHANNEL_PREFIX_RE.sub('', s).strip()
            return s

        for fname in filenames:
            name = os.path.splitext(os.path.basename(fname))[0]
            m = _SE_RE.search(name)
            if m:
                candidate = _clean(name[:m.start()].strip(' _.--'))
                if candidate:
                    return candidate
            m2 = re.search(r'\bFolge\s*\d|\bTeil\s*\d|\bEpisode\s*\d', name, re.IGNORECASE)
            if m2:
                candidate = _clean(name[:m2.start()].strip(' _.-'))
                if candidate:
                    return candidate
        return ""

    # ═══════════════════════════════════════════════════════════════════════════
    # Gruppierung nach Serie (mehrere Serien in einem Durchgang)
    # ═══════════════════════════════════════════════════════════════════════════

    _GRP_STATE_LABEL = {
        "NEW":        ("—",              "grp_none"),
        "RESOLVING":  ("lädt …",         "grp_none"),
        "RESOLVED":   ("✓",              "grp_ok"),
        "AMBIGUOUS":  ("⚠ unklar",       "grp_ambig"),
        "FAILED":     ("✗ Fehler",       "grp_failed"),
        "UNRESOLVED": ("keine Serie",    "grp_none"),
    }

    def _regroup_file_rows(self):
        """Ordnet alle geladenen Dateien Serien-Gruppen zu (rein lokal)."""
        if self.rename_mode_var.get() == "movie":
            return

        for row in self._tvdb_file_rows:
            raw = _series_from_filename(row["filename"])
            row["series_raw"] = raw
            row["gid"]        = _series_group_key(raw) if raw else ""
            row["adopted"]    = False

        # Etablierte Gruppen: mindestens 2 Dateien mit eigenem Marker.
        # Ein Einzelgänger darf keine weiteren Dateien adoptieren.
        counts, display = {}, {}
        for row in self._tvdb_file_rows:
            if row["gid"]:
                counts[row["gid"]] = counts.get(row["gid"], 0) + 1
                display.setdefault(row["gid"], row["series_raw"])
        established = {g: display[g] for g, c in counts.items() if c >= 2}

        # Zweite Stufe: markerlose Dateien per Namenspräfix adoptieren
        for row in self._tvdb_file_rows:
            if row["gid"]:
                continue
            norm = _normalize_title(os.path.splitext(row["filename"])[0])
            for gid in sorted(established, key=len, reverse=True):
                if not norm.startswith(gid + " "):
                    continue
                rest = norm[len(gid):]
                # Sieht der Rest nach Film/Release aus? Dann nicht adoptieren.
                if re.search(r'\b(?:19|20)\d{2}\b', rest) or _QUALITY_RE.search(rest):
                    continue
                row["gid"]        = gid
                row["series_raw"] = established[gid]
                row["adopted"]    = True
                break

        # Dritte Stufe: Serienname aus dem ORDNER holen. Greift für Dateien,
        # deren Name die Serie nicht enthält – z.B. "156. Die Reise.mp4"
        # im Ordner "Robin Hood".
        for row in self._tvdb_file_rows:
            if row["gid"]:
                continue
            raw = _series_from_dirname(row.get("dir", ""))
            if raw:
                row["series_raw"] = raw
                row["gid"]        = _series_group_key(raw)
                row["adopted"]    = True     # sichtbar als abgeleitet markieren

        # Serie-Spalte in der Dateiliste aktualisieren (Adoption sichtbar machen)
        for row in self._tvdb_file_rows:
            if not self.lv_tree.exists(row.get("lv_iid", "")):
                continue
            cell = row["series_raw"] or "—"
            if row["adopted"]:
                cell += " *"
            vals = list(self.lv_tree.item(row["lv_iid"], "values"))
            if len(vals) == 3:
                vals[0] = cell
                self.lv_tree.item(row["lv_iid"], values=tuple(vals))

        self._rebuild_groups()

    def _rebuild_groups(self):
        """Baut _tvdb_groups aus den Zeilen neu auf und zeichnet grp_tree."""
        counts, adopted, display = {}, {}, {}
        for row in self._tvdb_file_rows:
            gid = row.get("gid") or ""
            if gid == "__movie__":
                continue
            counts[gid]  = counts.get(gid, 0) + 1
            adopted[gid] = adopted.get(gid, 0) + (1 if row.get("adopted") else 0)
            if row.get("series_raw"):
                display.setdefault(gid, row["series_raw"])

        # Bestehende Gruppen (mit Auflösung) erhalten, neue anlegen
        for gid in list(self._tvdb_groups):
            if gid not in counts:
                del self._tvdb_groups[gid]
        for gid, n in counts.items():
            grp = self._tvdb_groups.get(gid)
            if grp is None:
                grp = {"gid": gid, "raw": display.get(gid, ""),
                       "state": "UNRESOLVED" if not gid else "NEW",
                       "epoch": 0, "series": None, "candidates": [],
                       "serie_name": "", "episodes": {}, "abs_map": {},
                       "order": "", "message": ""}
                self._tvdb_groups[gid] = grp
            grp["n_files"]   = n
            grp["n_adopted"] = adopted.get(gid, 0)
            if display.get(gid):
                grp["raw"] = display[gid]

        # Reihenfolge: benannte Gruppen alphabetisch, "ohne Serie" zuletzt
        self._tvdb_group_order = sorted(
            (g for g in self._tvdb_groups if g),
            key=lambda g: self._tvdb_groups[g]["raw"].lower())
        if "" in self._tvdb_groups:
            self._tvdb_group_order.append("")

        self._redraw_grp_tree()

    def _redraw_grp_tree(self):
        self.grp_tree.delete(*self.grp_tree.get_children())
        real = [g for g in self._tvdb_group_order if g]
        # Gruppen-Ansicht nur zeigen wenn es wirklich mehrere Serien gibt
        show = len(real) > 1 or ("" in self._tvdb_groups and real)
        if show:
            # Gruppen-Baum übernimmt die Serienauswahl – die klassische
            # Einzelserien-Zeile wäre dann ein zweiter Weg für dasselbe
            self._qf_single_row.pack_forget()
            if not self._grp_frame.winfo_ismapped():
                self._grp_frame.pack(fill=tk.BOTH, expand=True, pady=(2, 0))
        else:
            self._grp_frame.pack_forget()
            if not self._qf_single_row.winfo_ismapped():
                self._qf_single_row.pack(fill=tk.X)

        for gid in self._tvdb_group_order:
            grp = self._tvdb_groups[gid]
            label, tag = self._GRP_STATE_LABEL.get(grp["state"], ("—", "grp_none"))
            if grp["state"] == "AMBIGUOUS" and grp["candidates"]:
                label = f"⚠ {len(grp['candidates'])} Treffer"
            if grp["state"] == "RESOLVED" and grp.get("n_ok") is not None:
                label = f"✓ {grp['n_ok']}/{grp['n_files']}"

            cnt = str(grp["n_files"])
            if grp.get("n_adopted"):
                cnt += f" ({grp['n_adopted']} zugeordnet*)"

            if gid:
                name = grp["raw"]
                assigned = (grp["serie_name"] or
                            (grp["series"]["name"] if grp["series"] else
                             "— bitte auswählen —"))
            else:
                name, assigned = "⚠ Ohne Serie", "—"

            self.grp_tree.insert("", tk.END, iid="g:" + gid, tags=(tag,),
                                 values=(name, cnt, assigned, label))

        n_real = len(real)
        self.grp_status_var.set(
            f"{len(self._tvdb_file_rows)} Dateien · {n_real} Serie(n) erkannt"
            if n_real else "")

    def _selected_gid(self):
        sel = self.grp_tree.selection()
        if not sel:
            return None
        gid = sel[0][2:]      # "g:" abschneiden
        return gid if gid in self._tvdb_groups else None

    def _on_grp_select(self, *_):
        """Markiert die Dateien der gewählten Gruppe in beiden Listen."""
        gid = self._selected_gid()
        if gid is None:
            return
        lv, rv = [], []
        for row in self._tvdb_file_rows:
            if row.get("gid") == gid:
                if self.lv_tree.exists(row.get("lv_iid", "")):
                    lv.append(row["lv_iid"])
                if self.rv_tree.exists(row.get("rv_iid", "")):
                    rv.append(row["rv_iid"])
        if lv:
            self.lv_tree.selection_set(lv)
            self.lv_tree.see(lv[0])
        if rv:
            self.rv_tree.selection_set(rv)
            self.rv_tree.see(rv[0])

    # ── Auflösung einer Gruppe auf eine API-Serie ─────────────────────────────

    def _score_candidates(self, raw, results):
        """Bewertet Suchtreffer. Verweigert bei Unentschieden die Auswahl."""
        key = _series_group_key(raw)
        scored = []
        for r in results:
            rk = _series_group_key(r.get("name", ""))
            score = 1.0 if rk == key else difflib.SequenceMatcher(
                None, key, rk).ratio()
            scored.append((score, r))
        scored.sort(key=lambda t: -t[0])
        if not scored:
            return "FAILED", scored
        if scored[0][0] < 0.80:
            return "AMBIGUOUS", scored
        # Zwei praktisch gleich gute Treffer → NICHT raten.
        # Genau der Robin-Hood-Fall: TVDB liefert mehrere Serien "Robin Hood".
        if len(scored) > 1 and scored[1][0] >= scored[0][0] - 0.05:
            return "AMBIGUOUS", scored
        return "RESOLVED", scored

    def _remembered_series(self, gid):
        src = self.series_source_var.get()
        return (self._watchlist.get("series_id_map", {})
                .get(src, {}).get(gid))

    def _remember_series(self, gid, series):
        src = self.series_source_var.get()
        m = self._watchlist.setdefault("series_id_map", {}).setdefault(src, {})
        m[gid] = {"id": series["id"], "name": series.get("name", ""),
                  "primary_language": series.get("primary_language", "")}
        self._save_watchlist()

    def _cached_search(self, client, query, lang):
        key = (self.series_source_var.get(), _series_group_key(query), lang)
        if key not in self._tvdb_search_cache:
            self._tvdb_search_cache[key] = client.search_series(query, lang=lang)
        return self._tvdb_search_cache[key]

    def _cached_payload(self, client, series, lang, order):
        """Episoden + abs_map + Anzeigename einer Serie, gecacht."""
        key = (self.series_source_var.get(), series["id"], lang, order)
        if key in self._tvdb_api_cache:
            return self._tvdb_api_cache[key]

        primary = series.get("primary_language", "")
        episodes = client.get_episodes(series["id"], lang,
                                      primary_lang=primary, order=order)
        used_order = order
        if not episodes and order == "absolute":
            episodes = client.get_episodes(series["id"], lang,
                                           primary_lang=primary, order="official")
            used_order = "official"
        abs_map = {}
        if used_order == "official":
            # Aus der offiziellen Liste ableiten – quellenunabhängig, korrekt
            # und ohne zusätzliche Abfrage (siehe _abs_map_from_episodes).
            abs_map = _abs_map_from_episodes(episodes)
        serie_name = client.get_series_name(series["id"], lang,
                                           fallback_name=series.get("name", ""))
        serie_name = self._clean_api_series_name(serie_name)
        payload = {"episodes": episodes, "abs_map": abs_map,
                   "serie_name": serie_name, "order": used_order}
        self._tvdb_api_cache[key] = payload
        return payload

    @staticmethod
    def _clean_api_series_name(name):
        """Räumt Zusätze auf, die APIs zur Unterscheidung anhängen.

        Betrifft NUR den Seriennamen, nicht Episodentitel:
        - "Der Bergdoktor (2008)"      → "Der Bergdoktor"
          (der Jahreszusatz erzeugte neben dem bestehenden Ordner einen zweiten)
        - "Hubert und/ohne Staller"    → "Hubert und Staller"
          TheTVDB schreibt umbenannte Serien als Alternative. Der erste Zweig
          ist der Originaltitel. Ohne diese Behandlung entstand aus dem
          gelöschten Schrägstrich "Hubert undohne Staller".
        """
        n = (name or "").strip()
        n = re.sub(r'\s*\((?:19|20)\d{2}\)\s*$', '', n).strip() or n
        # Alternative "A/B" auf den ersten Zweig reduzieren
        m = re.search(r'(\S+)/(\S+)', n)
        if m:
            n = n.replace(m.group(0), m.group(1)).strip()
            n = re.sub(r'\s{2,}', ' ', n)
        return n or (name or "")

    def _resolve_group_sync(self, client, grp):
        """Löst eine Gruppe auf eine API-Serie auf. Läuft im Worker-Thread."""
        lang  = self.tvdb_lang_var.get()
        order = self.tvdb_order_var.get()

        # 1) Bereits bestätigte Zuordnung → ohne Suche übernehmen
        if grp["series"] is None:
            remembered = self._remembered_series(grp["gid"])
            if remembered:
                grp["series"] = dict(remembered)

        # 2) Noch nichts? Mit dem Namen aus dem Dateinamen suchen.
        #    Bewusst OHNE die Einsortier-Aliase: die sind Plex-ORDNERNAMEN
        #    (z.B. "Hubert und Staller {tmdb-53193}") und als Suchbegriff
        #    wertlos – sie liefern 0 Treffer. Weicht der API-Name vom
        #    Dateinamen ab, regelt das series_id_map nach einmaliger Bestätigung.
        if grp["series"] is None:
            results = self._cached_search(client, grp["raw"], lang)
            state, scored = self._score_candidates(grp["raw"], results)
            grp["candidates"] = [r for _s, r in scored]
            if state != "RESOLVED":
                grp["state"] = state
                grp["message"] = ("Keine Serie gefunden" if state == "FAILED"
                                  else "Mehrere mögliche Serien")
                return False
            grp["series"] = scored[0][1]

        # 3) Episoden laden
        payload = self._cached_payload(client, grp["series"], lang, order)
        if not payload["episodes"]:
            grp["state"]   = "FAILED"
            grp["message"] = "Keine Episoden gefunden"
            return False
        grp["episodes"]   = payload["episodes"]
        grp["abs_map"]    = payload["abs_map"]
        grp["serie_name"] = payload["serie_name"]
        grp["order"]      = payload["order"]
        grp["state"]      = "RESOLVED"
        grp["message"]    = ""
        return True

    # ── Batch-Runner ─────────────────────────────────────────────────────────

    def _assert_alignment(self):
        """Prüft dass Dateiliste und Trefferliste synchron sind."""
        n_lv  = len(self.lv_tree.get_children())
        n_rv  = len(self.rv_tree.get_children())
        n_row = len(self._tvdb_file_rows)
        n_map = len(self._tvdb_rows_by_iid)
        if n_lv == n_rv == n_row == n_map:
            return True
        messagebox.showerror(
            "Interner Zustand",
            "Datei- und Trefferliste sind nicht synchron "
            f"({n_lv}/{n_rv}/{n_row}/{n_map}).\n"
            'Bitte "🗑 Leeren" klicken und die Dateien neu laden.')
        return False

    def _set_batch_ui(self, running):
        state = tk.DISABLED if running else tk.NORMAL
        for attr in ("tvdb_search_btn", "tvdb_match_btn", "scan_btn"):
            w = getattr(self, attr, None)
            if w is not None:
                try:
                    w.configure(state=state)
                except Exception:
                    pass
        if running:
            for attr in ("tvdb_ask_btn", "tvdb_apply_btn", "tvdb_apply_all_btn"):
                w = getattr(self, attr, None)
                if w is not None:
                    try:
                        w.configure(state=tk.DISABLED)
                    except Exception:
                        pass

    def _arm_watchdog(self, token):
        if self._tvdb_watchdog is not None:
            try:
                self.root.after_cancel(self._tvdb_watchdog)
            except Exception:
                pass
        self._tvdb_watchdog = self.root.after(
            90000, lambda: self._watchdog_fire(token))

    def _watchdog_fire(self, token):
        if token != self._tvdb_batch_token or not self._tvdb_batch_busy:
            return
        # Hängenden Lauf entwerten und UI freigeben – ohne das bliebe der
        # Tab in einem console=False-Build dauerhaft ausgegraut.
        self._tvdb_batch_token += 1
        self._tvdb_batch_busy = False
        self._set_batch_ui(False)
        self.tvdb_status_var.set(
            "Zuordnung antwortet nicht – bitte erneut versuchen.")

    def _tvdb_match_all(self, gids=None):
        """Ordnet alle (oder die angegebenen) Gruppen zu."""
        if self._tvdb_batch_busy:
            return
        if not self._tvdb_file_rows:
            return
        if not self._assert_alignment():
            return
        client = self._tvdb_client()
        if not client:
            return

        plan = []
        for gid in (gids if gids is not None else self._tvdb_group_order):
            grp = self._tvdb_groups.get(gid)
            if not grp or not gid:          # "ohne Serie" wird übersprungen
                continue
            iids = [r["rv_iid"] for r in self._tvdb_file_rows
                    if r.get("gid") == gid
                    and self.rv_tree.exists(r.get("rv_iid", ""))]
            if iids:
                plan.append((grp, iids))
        if not plan:
            self.tvdb_status_var.set("Keine zuordenbare Serie erkannt.")
            return

        self._tvdb_batch_token += 1
        token = self._tvdb_batch_token
        self._tvdb_batch_busy = True
        self._set_batch_ui(True)
        self._arm_watchdog(token)
        threading.Thread(target=self._tvdb_batch_thread,
                         args=(client, plan, token), daemon=True).start()

    def _tvdb_batch_thread(self, client, plan, token):
        _here = os.path.dirname(sys.executable if getattr(sys, "frozen", False)
                                else os.path.abspath(__file__))
        dbg_path = os.path.join(_here, "tvdb_match_debug.txt")
        debug_lines, problems = [], []
        try:
            try:
                client.authenticate()
            except Exception as exc:
                problems.append(f"Anmeldung fehlgeschlagen: {exc}")
                return

            total = len(plan)
            for i, (grp, iids) in enumerate(plan, start=1):
                if token != self._tvdb_batch_token:
                    return
                label = grp["raw"] or "?"
                self.root.after(0, lambda i=i, t=total, l=label: (
                    self.tvdb_status_var.set(f"Gruppe {i}/{t}: {l} – lade Episoden …"),
                    self._arm_watchdog(token)))
                try:
                    grp["state"] = "RESOLVING"
                    self.root.after(0, self._redraw_grp_tree)
                    if not self._resolve_group_sync(client, grp):
                        problems.append(f"{label}: {grp['message']}")
                        debug_lines.append(
                            f"\n=== {label} → NICHT AUFGELÖST ({grp['message']}) ===\n")
                        self.root.after(0, self._redraw_grp_tree)
                        continue

                    debug_lines.append(
                        f"\n=== {label} → {grp['serie_name']} "
                        f"(id {grp['series']['id']}, {len(grp['episodes'])} Episoden) ===\n")
                    grp["epoch"] += 1
                    self._run_match(
                        client, grp["series"], grp["episodes"], iids, dbg_path,
                        abs_map=grp["abs_map"], serie_name=grp["serie_name"],
                        debug_sink=debug_lines)
                    self.root.after(0, self._stamp_group, grp["gid"],
                                    grp["epoch"], iids, token)
                except Exception as exc:
                    grp["state"]   = "FAILED"
                    grp["message"] = str(exc)[:120]
                    problems.append(f"{label}: {exc}")
                    import traceback
                    debug_lines.append(f"\n=== {label} → FEHLER ===\n")
                    debug_lines.append(traceback.format_exc())
                    self.root.after(0, self._redraw_grp_tree)
        finally:
            try:
                with open(dbg_path, "w", encoding="utf-8") as f:
                    f.writelines(debug_lines)
            except Exception:
                pass
            self.root.after(0, self._tvdb_batch_done, token, problems)

    def _stamp_group(self, gid, epoch, iids, token):
        """Markiert Zeilen als zu dieser Gruppe/Epoche gehörend (UI-Thread)."""
        if token != self._tvdb_batch_token:
            return
        for iid in iids:
            row = self._tvdb_rows_by_iid.get(iid)
            if row is not None:
                row["matched_gid"]   = gid
                row["matched_epoch"] = epoch
        grp = self._tvdb_groups.get(gid)
        if grp is not None:
            grp["n_ok"] = sum(
                1 for iid in iids
                if self.rv_tree.exists(iid) and self._rv_tag(iid) in self._OK_TAGS)
        self._redraw_grp_tree()

    def _tvdb_batch_done(self, token, problems=None):
        if token != self._tvdb_batch_token:
            return          # verspäteter Thread – nichts anfassen
        if self._tvdb_watchdog is not None:
            try:
                self.root.after_cancel(self._tvdb_watchdog)
            except Exception:
                pass
            self._tvdb_watchdog = None
        self._tvdb_batch_busy = False
        self._set_batch_ui(False)
        self._redraw_grp_tree()

        ok = sum(1 for i in self.rv_tree.get_children()
                 if self._rv_tag(i) in self._OK_TAGS)
        n_review = sum(1 for i in self.rv_tree.get_children()
                       if self._rv_tag(i) in self._REVIEW_TAGS)
        total = len(self._tvdb_file_rows)
        n_amb = sum(1 for g in self._tvdb_groups.values()
                    if g["state"] in ("AMBIGUOUS", "FAILED"))
        msg = f"✓ {ok} von {total} zugeordnet."
        if n_review:
            msg += f"  ⚠ {n_review} unsicher (orange) – bitte prüfen."
        if n_amb:
            msg += f"  {n_amb} Serie(n) offen – Gruppe anklicken und Serie wählen."
        self.tvdb_status_var.set(msg)

        if ok:
            self.tvdb_apply_btn.configure(state=tk.NORMAL)
            self.tvdb_apply_all_btn.configure(state=tk.NORMAL)
            self._rv_select_matched()
        if any(g["state"] == "RESOLVED" for g in self._tvdb_groups.values()):
            self.tvdb_ask_btn.configure(state=tk.NORMAL)

        # Genau EINE Sammelmeldung statt einem Dialog pro Gruppe
        if problems:
            messagebox.showwarning(
                "Nicht zugeordnet",
                "Diese Serien konnten nicht automatisch zugeordnet werden:\n\n"
                + "\n".join(f"• {p}" for p in problems[:10])
                + "\n\nBitte die Gruppe anklicken und „🔍 Serie wählen …\" nutzen.")

    def _tvdb_refresh_match_panel(self):
        self._update_lv_watermark()
        if self._tvdb_batch_busy:
            return
        count = len(self._tvdb_file_rows)
        # Übersprungene Sample-Dateien ausweisen, damit nicht der Eindruck
        # entsteht, es fehlten Dateien
        _s = self._tvdb_skipped_samples
        samples = f"  ({_s} Sample-Datei(en) übersprungen)" if _s else ""

        if not count:
            self._rebuild_groups()
            self.tvdb_status_var.set(
                f"Keine verwendbaren Dateien.{samples}" if _s else "")
            return

        if self.rename_mode_var.get() == "movie":
            self.tvdb_status_var.set(f"{count} Datei(en) geladen.{samples}")
            return

        self._regroup_file_rows()
        real = [g for g in self._tvdb_group_order if g]

        # Auch bei genau einer Serie über die Gruppen-Auflösung gehen: die
        # verweigert bei mehreren gleich guten Treffern die Auswahl, statt
        # blind den ersten zu nehmen (das war der Robin-Hood-Fehlgriff).
        if len(real) == 1:
            self.tvdb_search_var.set(self._tvdb_groups[real[0]]["raw"])

        if real:
            n_none = self._tvdb_groups.get("", {}).get("n_files", 0)
            extra = f", {n_none} ohne Serie" if n_none else ""
            self.tvdb_status_var.set(
                f"{count} Datei(en), {len(real)} Serie(n) erkannt{extra}{samples} – ordne zu …")
            if self._series_source_ready():
                self._tvdb_match_all()
                return
            self.tvdb_status_var.set(
                f"{count} Datei(en), {len(real)} Serie(n) erkannt{extra}{samples}.  "
                "Bitte API-Zugang eintragen.")
            return

        self.tvdb_status_var.set(
            f"{count} Datei(en) geladen{samples} – keine Serie im Dateinamen erkannt. "
            "Serie manuell suchen und Zuordnen klicken.")

    # ── Gruppen-Aktionen ─────────────────────────────────────────────────────

    def _reset_group_rows(self, gid):
        """Setzt die Trefferzellen einer Gruppe zurück, damit kein veralteter
        Name stehenbleibt."""
        for row in self._tvdb_file_rows:
            if row.get("gid") != gid:
                continue
            row["matched_gid"] = row["matched_epoch"] = None
            iid = row.get("rv_iid", "")
            if self.rv_tree.exists(iid):
                self.rv_tree.item(iid, tags=("nose",), values=("—", "—", "?"))

    def _grp_pick_series(self):
        """Dialog zur Auswahl der richtigen Serie für die markierte Gruppe."""
        if self._tvdb_batch_busy:
            return
        gid = self._selected_gid()
        if gid is None:
            messagebox.showinfo("Keine Gruppe",
                                "Bitte oben eine Serien-Gruppe anklicken.")
            return
        grp = self._tvdb_groups[gid]
        # Auch für "Ohne Serie" (gid == "") möglich: die gewählte Serie wird
        # dann allen Dateien dieser Gruppe zugewiesen.
        ungrouped = not gid

        win = tk.Toplevel(self.root)
        win.title("Serie wählen – " +
                  (grp["raw"] if not ungrouped
                   else f"{grp.get('n_files', 0)} Datei(en) ohne erkannte Serie"))
        win.resizable(False, False)
        win.grab_set()

        top = ttk.Frame(win)
        top.pack(fill=tk.X, padx=12, pady=(12, 4))
        ttk.Label(top, text="Suchbegriff:").pack(side=tk.LEFT)
        # Vorbelegung: bei "Ohne Serie" den Ordnernamen der ersten Datei
        # vorschlagen – oft steht die Serie dort drin
        _vorschlag = grp["raw"]
        if ungrouped:
            for _r in self._tvdb_file_rows:
                if _r.get("gid") == gid:
                    # Nur einen brauchbaren Ordnernamen vorschlagen – bei
                    # generischen Ordnern ("Downloads") lieber leer lassen
                    _vorschlag = _series_from_dirname(_r.get("dir", ""))
                    break
        q_var = tk.StringVar(value=_vorschlag)
        ttk.Entry(top, textvariable=q_var, width=30).pack(side=tk.LEFT, padx=6)

        cols = ("name", "year", "lang", "score")
        tv = ttk.Treeview(win, columns=cols, show="headings",
                          height=9, selectmode="browse")
        for c, txt, w in (("name", "Name", 260), ("year", "Jahr", 60),
                          ("lang", "Sprache", 70), ("score", "Treffer", 70)):
            tv.heading(c, text=txt)
            tv.column(c, width=w,
                      anchor=tk.W if c == "name" else tk.CENTER)
        tv.pack(fill=tk.BOTH, expand=True, padx=12, pady=4)

        results_ref = {"list": []}

        def _fill(results, preselect):
            tv.delete(*tv.get_children())
            _state, scored = self._score_candidates(q_var.get().strip(), results)
            results_ref["list"] = [r for _s, r in scored]
            for score, r in scored:
                tv.insert("", tk.END, values=(
                    r.get("name", ""), r.get("year", ""),
                    r.get("primary_language", ""), f"{score*100:.0f}%"))
            kids = tv.get_children()
            # Bei Unentschieden NICHTS vorauswählen – der Nutzer soll bewusst wählen
            if kids and preselect:
                tv.selection_set(kids[0])

        # Bereits geladene Kandidaten anzeigen; sonst frisch suchen
        if grp["candidates"]:
            _fill(grp["candidates"], preselect=(grp["state"] != "AMBIGUOUS"))
        status_var = tk.StringVar(value="")
        ttk.Label(win, textvariable=status_var,
                  foreground="gray").pack(padx=12, anchor="w")

        def _search():
            q = q_var.get().strip()
            if not q:
                return
            client = self._tvdb_client()
            if not client:
                return
            status_var.set("Suche läuft …")

            def _work():
                try:
                    client.authenticate()
                    res = self._cached_search(client, q, self.tvdb_lang_var.get())
                except Exception as exc:
                    self.root.after(0, lambda e=exc: status_var.set(f"Fehler: {e}"))
                    return
                self.root.after(0, lambda: (
                    _fill(res, preselect=True),
                    status_var.set(f"{len(res)} Serie(n) gefunden.")))
            threading.Thread(target=_work, daemon=True).start()

        remember_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(win, text="Serie für diesen Namen dauerhaft merken",
                        variable=remember_var).pack(padx=12, anchor="w", pady=(4, 0))

        def _apply():
            sel = tv.selection()
            if not sel:
                status_var.set("Bitte eine Serie in der Liste anklicken.")
                return
            series = results_ref["list"][tv.index(sel[0])]

            if ungrouped:
                # Dateien ohne erkannte Serie in eine echte Gruppe überführen
                iids = [r["rv_iid"] for r in self._tvdb_file_rows
                        if r.get("gid") == "" and self.rv_tree.exists(r.get("rv_iid", ""))]
                if not iids:
                    win.destroy()
                    return
                neu_gid = self._assign_series_to_rows(series, iids)
                if remember_var.get():
                    self._remember_series(neu_gid, series)
                win.destroy()
                self._tvdb_match_all([neu_gid])
                return

            grp["series"]     = series
            grp["candidates"] = results_ref["list"]
            grp["state"]      = "NEW"
            grp["serie_name"] = ""
            grp["episodes"]   = {}
            grp["n_ok"]       = None
            if remember_var.get():
                self._remember_series(gid, series)
            self._reset_group_rows(gid)
            win.destroy()
            self._tvdb_match_all([gid])

        btns = ttk.Frame(win)
        btns.pack(fill=tk.X, padx=12, pady=(6, 12))
        ttk.Button(btns, text="🔍 Suchen", command=_search).pack(side=tk.LEFT)
        ttk.Button(btns, text="Übernehmen", command=_apply).pack(side=tk.RIGHT)
        ttk.Button(btns, text="Abbrechen",
                   command=win.destroy).pack(side=tk.RIGHT, padx=6)
        tv.bind("<Double-1>", lambda _: _apply())

    def _grp_merge(self):
        """Führt die markierte Gruppe in eine andere zusammen."""
        if self._tvdb_batch_busy:
            return
        gid = self._selected_gid()
        if not gid:
            messagebox.showinfo("Keine Gruppe",
                                "Bitte oben eine Serien-Gruppe anklicken.")
            return
        others = [g for g in self._tvdb_group_order if g and g != gid]
        if not others:
            messagebox.showinfo("Nichts zum Zusammenführen",
                                "Es gibt nur diese eine Serien-Gruppe.")
            return

        win = tk.Toplevel(self.root)
        win.title("Gruppen zusammenführen")
        win.resizable(False, False)
        win.grab_set()
        ttk.Label(win, text=f'„{self._tvdb_groups[gid]["raw"]}“  '
                            f'({self._tvdb_groups[gid]["n_files"]} Dateien)  '
                            f'zusammenführen mit:').pack(padx=12, pady=(12, 6))
        labels = [f'{self._tvdb_groups[g]["raw"]}  '
                  f'({self._tvdb_groups[g]["n_files"]} Dateien)' for g in others]
        var = tk.StringVar(value=labels[0])
        ttk.Combobox(win, textvariable=var, values=labels, state="readonly",
                     width=44).pack(padx=12, pady=4)

        def _do():
            target = others[labels.index(var.get())]
            tgt = self._tvdb_groups[target]
            for row in self._tvdb_file_rows:
                if row.get("gid") == gid:
                    row["gid"]        = target
                    row["series_raw"] = tgt["raw"]
                    row["adopted"]    = True
                    iid = row.get("lv_iid", "")
                    if self.lv_tree.exists(iid):
                        vals = list(self.lv_tree.item(iid, "values"))
                        if len(vals) == 3:
                            vals[0] = tgt["raw"] + " *"
                            self.lv_tree.item(iid, values=tuple(vals))
            self._tvdb_groups.pop(gid, None)
            # Zielgruppe neu zuordnen, damit die dazugekommenen Dateien Namen bekommen
            tgt["n_ok"] = None
            self._reset_group_rows(target)
            self._rebuild_groups()
            win.destroy()
            self._tvdb_match_all([target])

        btns = ttk.Frame(win)
        btns.pack(fill=tk.X, padx=12, pady=(6, 12))
        ttk.Button(btns, text="Zusammenführen", command=_do).pack(side=tk.RIGHT)
        ttk.Button(btns, text="Abbrechen",
                   command=win.destroy).pack(side=tk.RIGHT, padx=6)

    def _grp_reset(self):
        """Verwirft die Zuordnung der markierten Gruppe (auch die gemerkte)."""
        if self._tvdb_batch_busy:
            return
        gid = self._selected_gid()
        if not gid:
            return
        grp = self._tvdb_groups[gid]
        src = self.series_source_var.get()
        remembered = self._watchlist.get("series_id_map", {}).get(src, {})
        if gid in remembered:
            if messagebox.askyesno(
                    "Gemerkte Serie verwerfen",
                    f'Für „{grp["raw"]}“ ist „{remembered[gid].get("name", "")}“ '
                    "gemerkt.\nDiese Zuordnung löschen?"):
                del remembered[gid]
                self._save_watchlist()
        grp.update({"series": None, "candidates": [], "state": "NEW",
                    "serie_name": "", "episodes": {}, "abs_map": {},
                    "n_ok": None, "message": ""})
        self._reset_group_rows(gid)
        self._redraw_grp_tree()
        self.tvdb_status_var.set(f'Gruppe „{grp["raw"]}“ zurückgesetzt.')

    def _series_source_ready(self):
        """Hat die gewählte Quelle die nötigen Zugangsdaten?"""
        src = self.series_source_var.get()
        if src == "TVmaze":
            return True
        if src == "Trakt.tv":
            return bool(self.trakt_key_var.get().strip())
        return bool(self.tvdb_key_var.get().strip())

    # ── Seriensuche ───────────────────────────────────────────────────────────

    def _tvdb_search_series(self, auto_match=False):
        name = self.tvdb_search_var.get().strip()
        if not name:
            return
        client = self._tvdb_client()
        if not client:
            return
        self.tvdb_search_btn.configure(state=tk.DISABLED)
        self.tvdb_status_var.set("Suche läuft …")
        threading.Thread(target=self._tvdb_search_thread,
                         args=(client, name, auto_match), daemon=True).start()

    def _tvdb_search_thread(self, client, name, auto_match=False):
        try:
            client.authenticate()
            results = client.search_series(name, lang=self.tvdb_lang_var.get())
        except Exception as exc:
            self.root.after(0, lambda e=exc:
                (messagebox.showerror("TVDB-Fehler", str(e)),
                 self.tvdb_status_var.set("Fehler.")))
            self.root.after(0, lambda: self.tvdb_search_btn.configure(state=tk.NORMAL))
            return
        def _update():
            self._tvdb_series_data = results
            labels = [
                f"{r['name']}  ({r['year']})"
                + (f"  [{r['primary_language']}]" if r.get("primary_language") else "")
                for r in results
            ]
            self.tvdb_series_box.configure(values=labels)
            if labels:
                self.tvdb_series_box.current(0)
                self.tvdb_match_btn.configure(state=tk.NORMAL)
                self.tvdb_status_var.set(
                    f"{len(results)} Serie(n) gefunden – 'Zuordnen' klicken.")
            else:
                self.tvdb_status_var.set("Keine Ergebnisse.")
            self.tvdb_search_btn.configure(state=tk.NORMAL)
        self.root.after(0, _update)

    # ── Zuordnen ──────────────────────────────────────────────────────────────

    def _assign_series_to_rows(self, series, iids):
        """Ordnet bestimmte Zeilen einer Serie zu (eigene Gruppe) und gibt
        deren gid zurück. Wird für die Einzelzeilen-Neusuche benutzt."""
        gid = _series_group_key(series.get("name", "")) or "__manual__"
        grp = self._tvdb_groups.get(gid)
        if grp is None:
            grp = {"gid": gid, "raw": series.get("name", ""), "state": "NEW",
                   "epoch": 0, "series": None, "candidates": [],
                   "serie_name": "", "episodes": {}, "abs_map": {},
                   "order": "", "message": "", "n_files": 0, "n_adopted": 0}
            self._tvdb_groups[gid] = grp
        grp["series"] = series
        grp["state"]  = "NEW"
        grp["n_ok"]   = None
        for iid in iids:
            row = self._tvdb_rows_by_iid.get(iid)
            if row is None:
                continue
            row["gid"]        = gid
            row["series_raw"] = series.get("name", "")
            row["adopted"]    = True
            row["matched_gid"] = row["matched_epoch"] = None
            lv_iid = row.get("lv_iid", "")
            if self.lv_tree.exists(lv_iid):
                vals = list(self.lv_tree.item(lv_iid, "values"))
                if len(vals) == 3:
                    vals[0] = series.get("name", "") + " *"
                    self.lv_tree.item(lv_iid, values=tuple(vals))
        self._rebuild_groups()
        return gid

    def _tvdb_run_match(self, series_override=None, target_iids=None):
        """Weiche auf die Gruppen-Zuordnung.

        Ohne Argumente: die in der Combobox gewählte Serie auf die (einzige)
        erkannte Gruppe anwenden. Mit series_override/target_iids: die
        angegebenen Zeilen einer eigenen Gruppe für diese Serie zuordnen.
        """
        if self._tvdb_batch_busy:
            return
        if not self._tvdb_file_rows:
            messagebox.showinfo("Keine Dateien",
                                "Bitte erst Dateien oder einen Ordner hinzufügen.")
            return

        idx = self.tvdb_series_box.current()
        if series_override:
            series = series_override
        elif idx >= 0 and self._tvdb_series_data:
            series = self._tvdb_series_data[idx]
        else:
            return

        if target_iids:
            gid = self._assign_series_to_rows(series, list(target_iids))
            self._tvdb_match_all([gid])
            return

        # Combobox-Pfad: Serie auf die erkannten Gruppen anwenden
        real = [g for g in self._tvdb_group_order if g]
        if len(real) == 1:
            gid = real[0]
        else:
            gid = self._selected_gid()
            if gid is None or not gid:
                # Mehrere Gruppen, keine markiert → alle ohne feste Serie zuordnen
                self._tvdb_match_all()
                return
        grp = self._tvdb_groups[gid]
        grp["series"] = series
        grp["state"]  = "NEW"
        grp["n_ok"]   = None
        self._reset_group_rows(gid)
        self._tvdb_match_all([gid])

    # (_tvdb_match_thread entfernt – Episodenladen und Fehlerbehandlung liegen
    #  jetzt in _resolve_group_sync / _cached_payload / _tvdb_batch_thread,
    #  damit es nur EINEN Weg gibt.)

    def _run_match(self, client, series, episodes, target_iids, dbg_path,
                   abs_map=None, serie_name=None, debug_sink=None):
        fmt        = self.tvdb_fmt_var.get()
        lang       = self.tvdb_lang_var.get()
        if serie_name is None:
            serie_name = client.get_series_name(series["id"], lang,
                                                fallback_name=series["name"])
            # Einzelserien-Legacy: globalen Zustand nur setzen wenn NICHT
            # gruppenweise gearbeitet wird (sonst zeigt er auf die letzte Gruppe)
            self._tvdb_episodes   = episodes
            self._tvdb_serie_name = serie_name

        # Zeilen über die autoritative iid-Bindung auflösen, nicht über
        # Listenpositionen – ein Fehlindex würde sonst die falsche Datei
        # umbenennen, ohne eine Exception zu werfen.
        if target_iids:
            rows_to_update = [(iid, self._tvdb_rows_by_iid[iid])
                              for iid in target_iids
                              if iid in self._tvdb_rows_by_iid]
        else:
            rows_to_update = [(iid, self._tvdb_rows_by_iid[iid])
                              for iid in self.rv_tree.get_children()
                              if iid in self._tvdb_rows_by_iid]

        # ── Hilfsfunktionen ──────────────────────────────────────────────────────

        def _find_by_ep(ep_num):
            """Alle (Staffel, Folge) mit dieser Folgennummer.

            Staffel 0 (Specials) kommt ans ENDE: eine nackte Folgennummer im
            Dateinamen meint praktisch immer eine reguläre Folge. Ohne das
            gewann bei Serien mit Specials die Staffel 0 – bei Dragon Ball Kai
            landeten so die Folgen 1-9 auf den Buu-Arc-Specials.
            """
            return sorted(((ss, ee) for (ss, ee) in episodes if ee == ep_num),
                          key=lambda k: (k[0] == 0, k[0], k[1]))

        _normalize = _normalize_title

        # Sendernamen überall im Dateinamen entfernen (nicht nur am Anfang)
        # Gemeinsame Senderliste (Modulebene) – enthält bewusst kein
        # ONE/SUPER/NICK/DISNEY, das sind zu häufig echte Titelwörter
        _channel_any_re = _CHANNEL_ANY_RE

        def _title_from_filename(filename):
            """Extrahiert den Episodentitel-Anteil aus dem Dateinamen."""
            name = os.path.splitext(filename)[0]
            name = _fix_mojibake(name)
            name = re.sub(r'[_.]', ' ', name)
            # Sender überall entfernen (Präfix und mitten im Namen)
            name = _channel_any_re.sub('', name).strip()
            # Serienname-Präfix entfernen — Jahreszahl in Klammern vorher abschneiden
            serie_clean = re.sub(r'\s*\(\d{4}\)\s*$', '', serie_name).strip()
            safe_serie  = re.escape(re.sub(r'[_.]', ' ', serie_clean).strip())
            name = re.sub(r'^' + safe_serie + r'\s*[-–]?\s*',
                          '', name, flags=re.IGNORECASE).strip()
            # Jahreszahl in Klammern die nach dem Serienpräfix übrig bleibt entfernen
            # z.B. "Der Bergdoktor (2008)" → nach Strip von "Der Bergdoktor" bleibt "(2008)"
            name = re.sub(r'^\s*\(\d{4}\)\s*[-–]?\s*', '', name).strip()
            # Falls der vollständige Serienname nicht greift (z.B. "Robin Hood" statt
            # "Robin Hood – Schlitzohr von Sherwood"), auch den Teil vor dem ersten
            # Trennzeichen versuchen
            if name.lower().startswith(serie_clean.lower()[:6]):
                serie_short = re.split(r'\s*[–—:|]\s*', serie_clean)[0].strip()
                if serie_short and serie_short != serie_clean:
                    safe_short = re.escape(serie_short)
                    name = re.sub(r'^' + safe_short + r'\s*[-–_]?\s*',
                                  '', name, flags=re.IGNORECASE).strip()
            # S/E-Tag entfernen (vollständig SxxExx sowie alleinstehende Sxx/Exx-Fragmente)
            name = _SE_RE.sub('', name)
            name = re.sub(r'\bS\d{1,4}\b', '', name)   # z.B. "S2026" ohne E-Teil
            name = re.sub(r'\bE\d{1,4}\b', '', name)   # z.B. "E08"  ohne S-Teil
            name = name.strip()
            # Datumsangaben entfernen  (z.B. 2024-03-15 oder 20240315)
            name = re.sub(r'\b\d{4}[-_]\d{2}[-_]\d{2}\b', '', name)
            name = re.sub(r'\b20\d{6}\b', '', name)
            # Nur reine Folgennummer-Angaben entfernen die KEIN Titelwort danach haben
            # (z.B. "Folge 3" am Ende, "(3/8)") — aber NICHT "Teil 2" da Teil des Titels
            name = re.sub(r'\((\d{1,4})/\d+\)', ' ', name)
            name = re.sub(r'\b(?:Folge|Episode)\s+\d{1,4}\b', ' ', name, flags=re.IGNORECASE)
            name = re.sub(r'\b\d{1,4}\.\s*(?:Folge|Episode)\b', ' ', name, flags=re.IGNORECASE)
            name = re.sub(r'\(\d{1,4}\)\s*$', ' ', name)
            # Teil/Part-Angaben entfernen – werden separat als Plex-pt-Suffix behandelt
            name = re.sub(r'\b(?:Teil|Part|Pt\.?)\s*\d+\b', ' ', name, flags=re.IGNORECASE)
            # Qualitäts-Suffixe und Scene-Release-Metadaten entfernen
            name = re.sub(r'\b\d{3,4}[pP]\b', ' ', name)                   # 720p 1080p
            name = re.sub(r'\b(HD|SD|UT|OV)\b', ' ', name, flags=re.IGNORECASE)
            name = re.sub(r'\b(19|20)\d{2}\b', ' ', name)                   # Jahreszahlen
            name = re.sub(
                r'\b(?:German|English|French|Spanish|Italian|Japanese|'
                r'Deutsch|Ml|Multi|Dubbed|Subbed|DL)\b', ' ', name, flags=re.IGNORECASE)
            name = re.sub(
                r'\b(?:Bluray|BDRip|BRRip|WEBRip|WEB-?DL|HDTV|'
                r'DVDRip|DVD|HDRip|Anime)\b', ' ', name, flags=re.IGNORECASE)
            name = re.sub(
                r'\b(?:x264|x265|HEVC|AVC|H\.?264|H\.?265|XviD|DivX)\b',
                ' ', name, flags=re.IGNORECASE)
            # Release-Gruppe am Ende (z.B. "-YTS", "-NIMA4K") – nur bei
            # Grossschreibung/Ziffern, damit "Der Super-Roller" heil bleibt
            name = _RELEASE_SUFFIX_RE.sub('', name)
            return re.sub(r'\s{2,}', ' ', name).strip(' -–_')

        def _best_title_match(candidate):
            """Sucht den ähnlichsten TheTVDB-Episodentitel; gibt (s, e, title, ratio) zurück."""
            if not candidate or len(candidate) < 4:
                return None, None, None, 0.0
            norm_cand = _normalize(candidate)
            # Wortmenge des Kandidaten für schnellen Vorfilter
            cand_words = set(norm_cand.split())
            best = (None, None, None, 0.0)
            for (ss, ee), title in episodes.items():
                norm_t = _normalize(title)
                # Schneller Vorfilter: mindestens 1 gemeinsames Wort (>2 Buchstaben)
                if not cand_words.intersection(
                        w for w in norm_t.split() if len(w) > 2):
                    continue
                ratio = difflib.SequenceMatcher(None, norm_cand, norm_t).ratio()
                if ratio > best[3]:
                    best = (ss, ee, title, ratio)
            return best

        # ── Matching-Schleife ─────────────────────────────────────────────────────

        updates = []

        debug_lines = debug_sink if debug_sink is not None else []
        debug_lines.extend([
            f"Serie: {serie_name}  |  Episoden geladen: {len(episodes)}"
            f"  |  {len(rows_to_update)} Datei(en)\n",
            f"{'Dateiname':<55} {'S/E':<10} {'Kandidat':<30} {'Strategie':<5} {'Treffer'}\n",
            "-" * 120 + "\n",
        ])

        # Teilnummer-Erkennung (Teil 1, Teil 2, Part 1, Part 2 …)
        _part_re = re.compile(r'\b(?:Teil|Part|Pt\.?)\s*(\d+)\b', re.IGNORECASE)

        for iid, file_row in rows_to_update:
            s, e = file_row.get("s"), file_row.get("e")
            ep_title  = None
            matched_s = s
            matched_e = e
            match_ratio    = 0.0
            match_strategy = 0
            needs_review   = False

            # Teilnummer aus dem Dateinamen extrahieren (für Plex-Suffix später)
            _pm = _part_re.search(file_row["filename"])
            part_num = int(_pm.group(1)) if _pm else None

            # Strategie 1: Titelvergleich – Episodenname aus dem Dateinamen
            # gegen TheTVDB-Titel abgleichen (Schwellwert 0.60)
            candidate = _title_from_filename(file_row["filename"])
            ms, me, title, ratio = _best_title_match(candidate)
            if ratio >= 0.60:
                # Wenn der Dateiname eine explizite S/E-Nummer enthält und
                # Strategie 1 eine ANDERE Episode vorschlägt → prüfe ob
                # der exakte S/E-Treffer (Strategie 2) existiert.
                # Falls ja, bevorzuge den exakten Treffer (z.B. S00E03 statt
                # S00E04 bei ähnlichen Titeln wie "Weihnachtsspecial 20xx").
                if (s is not None and e is not None
                        and (ms != s or me != e)
                        and episodes.get((s, e))):
                    exact_title = episodes[(s, e)]
                    matched_s, matched_e = s, e
                    ep_title       = exact_title
                    match_strategy = 2
                else:
                    matched_s, matched_e = ms, me
                    ep_title       = title
                    match_ratio    = ratio
                    match_strategy = 1
                    # Der Dateiname nennt eine Staffel/Folge, die es in DIESER
                    # Quelle nicht gibt, und der Titel passt nur mittelmäßig.
                    # Typisch dafür, dass die Quelle die Folge nicht kennt
                    # (z.B. TVmaze hat Hubert nur bis Staffel 13) – dann wird
                    # sonst ein plausibel klingender, falscher Titel gewählt.
                    if (s is not None and e is not None
                            and not episodes.get((s, e))
                            and ratio < 0.85):
                        needs_review = True

            if not ep_title and s is not None and e is not None:
                # Strategie 2: exakter (Staffel, Folge)-Treffer
                ep_title = episodes.get((s, e))
                if ep_title:
                    matched_s, matched_e = s, e
                    match_strategy = 2

                if not ep_title and s >= 1900:
                    # Strategie 3: jahresbasierte Staffel (S2024E10) →
                    # Suche anhand reiner Folgennummer
                    cands = _find_by_ep(e)
                    if cands:
                        matched_s, matched_e = cands[0]
                        ep_title = episodes[(matched_s, matched_e)]
                        match_strategy = 3

                if not ep_title and abs_map:
                    # Strategie 5: absolute Episodennummer → TVDB-Staffel/Folge-Mapping
                    # (Dateiname z.B. S02e040 meint absolute Folge 40 der Serie,
                    #  in TVDB official-Reihenfolge aber S2E1)
                    mapped = abs_map.get(e)
                    if mapped:
                        ep_title = episodes.get(mapped)
                        if ep_title:
                            matched_s, matched_e = mapped
                            match_strategy = 5

                if not ep_title:
                    # Strategie 2b: Staffelnummer im Dateinamen stimmt nicht
                    # mit TVDB überein. Suche über alle Staffeln nach Folgennr.
                    cands = _find_by_ep(e)
                    if len(cands) == 1:
                        # Eindeutiger Treffer → nehmen
                        matched_s, matched_e = cands[0]
                        ep_title = episodes[(matched_s, matched_e)]
                        match_strategy = 3
                    elif len(cands) > 1 and candidate:
                        # Mehrere Kandidaten → nur nehmen wenn Titel gut passt
                        best_r, best_k = 0.0, None
                        for ck in cands:
                            r = difflib.SequenceMatcher(
                                None,
                                _normalize(candidate),
                                _normalize(episodes[ck])).ratio()
                            if r > best_r:
                                best_r, best_k = r, ck
                        if best_r >= 0.55 and best_k:
                            matched_s, matched_e = best_k
                            ep_title = episodes[best_k]
                            match_ratio    = best_r
                            match_strategy = 3
                    # Kein Titel oder mehrdeutig ohne guten Titelabgleich →
                    # KEIN TREFFER, "Titel eingeben"-Button aktiviert sich

            if not ep_title and e is not None and s is None:
                # Strategie 4: kein Staffel-Tag, nur Folgennummer
                cands = _find_by_ep(e)
                if cands:
                    matched_s, matched_e = cands[0]
                    ep_title = episodes[(matched_s, matched_e)]
                    match_strategy = 4
                elif abs_map:
                    # Strategie 5 auch OHNE Staffelangabe: bei Anime sind die
                    # Dateien durchgehend nummeriert (One Piece 1155), die
                    # Datenbank gliedert aber in Staffeln. Ohne diesen Zweig
                    # blieben alle Folgen jenseits der längsten Staffel ohne
                    # Treffer.
                    mapped = abs_map.get(e)
                    if mapped and episodes.get(mapped):
                        matched_s, matched_e = mapped
                        ep_title = episodes[mapped]
                        match_strategy = 5

            se_str = f"S{s}E{e}" if s is not None and e is not None else (f"E{e}" if e else "—")
            debug_lines.append(
                f"{file_row['filename']:<55} {se_str:<10} {candidate[:28]:<30} "
                f"{'St'+str(match_strategy):<5} "
                f"{'S'+str(matched_s)+'E'+str(matched_e)+' '+str(ep_title) if ep_title else 'KEIN TREFFER'}\n"
            )

            if ep_title:
                safe_t = _safe_str(ep_title)
                try:
                    new_name = fmt.format(
                        serie=_safe_str(serie_name),
                        s=matched_s, e=matched_e, titel=safe_t)
                except Exception:
                    new_name = file_row["filename"]
                # Plex-konformes Mehrteil-Suffix: "- pt1", "- pt2" …
                # Suffix muss VOR der Dateiendung eingefügt werden!
                if part_num:
                    _base, _ext = os.path.splitext(new_name)
                    new_name = f"{_base} - pt{part_num}{_ext}"
                new_name = _with_source_ext(new_name, file_row["filename"])
                if needs_review:
                    tag    = "ok_low"
                    status = f"prüfen {match_ratio*100:.0f}%" + (f" pt{part_num}" if part_num else "")
                elif match_strategy == 1:
                    tag    = "ok_high" if match_ratio >= 0.85 else "ok_mid"
                    status = f"{match_ratio*100:.0f}%"  + (f" pt{part_num}" if part_num else "")
                else:
                    tag    = "ok_se"
                    status = "S/E" + (f" pt{part_num}" if part_num else "")
                updates.append((iid, new_name, ep_title, status, tag))
            elif s is None and e is None:
                updates.append((iid, file_row["filename"], "kein S/E erkannt", "—", "nose"))
            else:
                updates.append((iid, file_row["filename"], "kein Treffer", "—", "nomatch"))

        # Bei gruppenweiser Zuordnung (debug_sink gesetzt) schreibt der
        # Batch-Runner die Datei EINMAL am Ende – sonst würde jede Gruppe
        # die Ausgabe der vorherigen abschneiden.
        if debug_sink is None:
            try:
                with open(dbg_path, "w", encoding="utf-8") as f:
                    f.writelines(debug_lines)
            except Exception:
                pass

        self.root.after(0, self._tvdb_apply_updates, updates)
        return updates

    def _tvdb_apply_updates(self, updates):
        unmatched_iids = []
        for iid, new_name, ep_title, status, tag in updates:
            if self.rv_tree.exists(iid):
                self.rv_tree.item(iid, tags=(tag,),
                                  values=(new_name, ep_title, status))
                if tag in ("nomatch", "nose"):
                    unmatched_iids.append(iid)
        self.tvdb_match_btn.configure(state=tk.NORMAL)
        # Über den GESAMTEN Baum zählen, nicht nur über dieses Teil-Update –
        # sonst zeigt ein Teillauf "1 von 25" obwohl 25 zugeordnet sind.
        ok = sum(1 for i in self.rv_tree.get_children()
                 if self._rv_tag(i) in self._OK_TAGS)
        total = len(self._tvdb_file_rows)
        self.tvdb_status_var.set(f"✓ {ok} von {total} zugeordnet.")
        if ok:
            self.tvdb_apply_btn.configure(state=tk.NORMAL)
            self.tvdb_apply_all_btn.configure(state=tk.NORMAL)
            self._rv_select_matched()
        if unmatched_iids and (self._tvdb_episodes or any(
                g["state"] == "RESOLVED" for g in self._tvdb_groups.values())):
            self.tvdb_ask_btn.configure(state=tk.NORMAL)

    # ── Manuelle Titelabfrage für nicht erkannte Dateien ─────────────────────

    def _tvdb_ask_unmatched_btn(self):
        """Startet die manuelle Titelabfrage für alle nicht erkannten Zeilen."""
        iids = [iid for iid in self.rv_tree.get_children()
                if self._rv_tag(iid) in ("nomatch", "nose")]
        if iids:
            self._tvdb_ask_unmatched(iids)

    def _tvdb_ask_unmatched(self, iids):
        """Zeigt für jede nicht erkannte Datei einen Dialog zur Titeleingabe."""
        remaining = [iid for iid in iids if self.rv_tree.exists(iid)
                     and self._rv_tag(iid) in ("nomatch", "nose")]
        if not remaining:
            return

        iid = remaining[0]
        row = self._tvdb_rows_by_iid.get(iid)
        if row is None:
            self._tvdb_ask_unmatched(remaining[1:])
            return
        fname = row["filename"]

        # Episodenliste der Gruppe DIESER Zeile verwenden – nicht die global
        # zuletzt geladene. Sonst bekäme eine Robin-Hood-Datei den Titel und
        # Seriennamen der Serie, die zufällig als letzte gematcht wurde.
        grp = self._tvdb_groups.get(row.get("gid"))
        if grp and grp["state"] == "RESOLVED":
            ask_episodes, ask_serie = grp["episodes"], grp["serie_name"]
        else:
            ask_episodes, ask_serie = self._tvdb_episodes, self._tvdb_serie_name
        if not ask_episodes:
            # Ohne Episodenliste kann hier nichts gebildet werden
            self._tvdb_ask_unmatched(remaining[1:])
            return

        win = tk.Toplevel(self.root)
        win.title("Folgentitel eingeben")
        win.resizable(False, False)
        win.transient(self.root)

        ttk.Label(win, text="Datei:", font=("", 9, "bold")).grid(
            row=0, column=0, sticky=tk.W, padx=12, pady=(12, 0))
        ttk.Label(win, text=fname, wraplength=420, justify=tk.LEFT).grid(
            row=1, column=0, columnspan=2, sticky=tk.W, padx=12, pady=(0, 8))

        remaining_count = len(remaining)
        ttk.Label(win,
                  text=f"Wie heißt diese Folge?  ({remaining_count} nicht erkannt)",
                  font=("", 9)).grid(row=2, column=0, columnspan=2,
                                     sticky=tk.W, padx=12, pady=(0, 4))

        var = tk.StringVar()
        entry = ttk.Entry(win, textvariable=var, width=46)
        entry.grid(row=3, column=0, columnspan=2, padx=12, pady=(0, 4))
        entry.focus()

        hint_var = tk.StringVar()
        ttk.Label(win, textvariable=hint_var, foreground="gray",
                  font=("", 8)).grid(row=4, column=0, columnspan=2,
                                     sticky=tk.W, padx=12, pady=(0, 8))

        skip_rest = tk.BooleanVar(value=False)

        _part_re_ask = re.compile(r'\b(?:Teil|Part|Pt\.?)\s*(\d+)\b', re.IGNORECASE)
        _pm_ask      = _part_re_ask.search(fname)
        part_num_ask = int(_pm_ask.group(1)) if _pm_ask else None

        def _do_search():
            title_input = var.get().strip()
            if not title_input:
                hint_var.set("Bitte einen Titel eingeben.")
                return
            ms, me, ep_title, ratio = _best_episode_match(
                title_input, ask_episodes)
            if ratio < 0.40 or ep_title is None:
                hint_var.set(f"Kein Treffer gefunden (beste Übereinstimmung: {ratio*100:.0f}%). "
                             "Anderen Titel versuchen.")
                return
            fmt       = self.tvdb_fmt_var.get()
            serie     = ask_serie
            safe_t    = _safe_str(ep_title)
            try:
                new_name = fmt.format(serie=_safe_str(serie),
                                      s=ms, e=me, titel=safe_t)
            except Exception:
                new_name = ep_title
            # Plex-konformes Mehrteil-Suffix VOR der Dateiendung einfügen
            if part_num_ask:
                _base, _ext = os.path.splitext(new_name)
                new_name = f"{_base} - pt{part_num_ask}{_ext}"
            new_name = _with_source_ext(new_name, fname)
            tag    = "ok_high" if ratio >= 0.85 else "ok_mid"
            status = f"{ratio*100:.0f}%" + (f" pt{part_num_ask}" if part_num_ask else "")
            self.rv_tree.item(iid, tags=(tag,),
                              values=(new_name, ep_title, status))
            # Zeile als zur Gruppe gehörend stempeln, sonst sperrt sie das
            # Sicherheitstor beim Umbenennen
            if grp is not None:
                row["matched_gid"]   = row.get("gid")
                row["matched_epoch"] = grp["epoch"]
            self.tvdb_apply_btn.configure(state=tk.NORMAL)
            self.tvdb_apply_all_btn.configure(state=tk.NORMAL)
            _ok_count = sum(1 for i in self.rv_tree.get_children()
                            if self._rv_tag(i) in self._OK_TAGS)
            total = len(self._tvdb_file_rows)
            self.tvdb_status_var.set(f"✓ {_ok_count} von {total} zugeordnet.")
            win.destroy()
            self.root.after(100, lambda: self._tvdb_ask_unmatched(remaining[1:]))

        def _skip():
            win.destroy()
            self.root.after(100, lambda: self._tvdb_ask_unmatched(remaining[1:]))

        def _skip_all():
            skip_rest.set(True)
            win.destroy()

        btn_frame = ttk.Frame(win)
        btn_frame.grid(row=5, column=0, columnspan=2, pady=(0, 12))
        ttk.Button(btn_frame, text="Zuordnen", command=_do_search).pack(
            side=tk.LEFT, padx=6)
        ttk.Button(btn_frame, text="Überspringen", command=_skip).pack(
            side=tk.LEFT, padx=6)
        ttk.Button(btn_frame, text="Alle überspringen", command=_skip_all).pack(
            side=tk.LEFT, padx=6)

        win.bind("<Return>", lambda _: _do_search())
        win.bind("<Escape>", lambda _: _skip())

    # ── Kontextmenü rechte Seite ──────────────────────────────────────────────

    def _show_rv_menu(self, event):
        iid = self.rv_tree.identify_row(event.y)
        if iid:
            self.rv_tree.selection_set(iid)
            self._rv_menu.post(event.x_root, event.y_root)

    def _tvdb_fix_episode(self):
        """Korrigiert die Zuordnung EINER Zeile – auch wenn sie bereits
        (falsch) zugeordnet ist.

        Zwei Wege: Staffel/Folge eintippen, oder einen Titel suchen. Beides
        wird gegen die bereits geladene Episodenliste der Gruppe aufgelöst,
        es ist also keine neue Abfrage nötig.
        """
        sel = self.rv_tree.selection()
        if not sel:
            messagebox.showinfo("Keine Zeile",
                                "Bitte rechts eine Zeile anklicken.")
            return
        iid = sel[0]
        row = self._tvdb_rows_by_iid.get(iid)
        if row is None:
            return

        grp = self._tvdb_groups.get(row.get("gid"))
        if grp and grp.get("episodes"):
            episodes, serie_name = grp["episodes"], grp["serie_name"]
        else:
            episodes, serie_name = self._tvdb_episodes, self._tvdb_serie_name
        if not episodes:
            messagebox.showinfo(
                "Keine Episodenliste",
                "Für diese Datei ist noch keine Serie zugeordnet.\n"
                "Bitte zuerst die Serie zuordnen lassen.")
            return

        cur_vals = self.rv_tree.item(iid, "values")
        cur_name = cur_vals[0] if cur_vals else ""

        win = tk.Toplevel(self.root)
        win.title("Folge korrigieren")
        win.resizable(False, False)
        win.grab_set()

        ttk.Label(win, text="Datei:", font=("", 9, "bold")).grid(
            row=0, column=0, sticky=tk.W, padx=12, pady=(12, 0))
        ttk.Label(win, text=row["filename"], wraplength=430,
                  justify=tk.LEFT).grid(row=1, column=0, columnspan=4,
                                        sticky=tk.W, padx=12)
        ttk.Label(win, text=f"Serie: {serie_name}   ({len(episodes)} Episoden)",
                  foreground="gray").grid(row=2, column=0, columnspan=4,
                                          sticky=tk.W, padx=12, pady=(0, 2))
        ttk.Label(win, text=f"bisher: {cur_name}", foreground="#856404",
                  wraplength=430, justify=tk.LEFT).grid(
            row=3, column=0, columnspan=4, sticky=tk.W, padx=12, pady=(0, 8))

        ttk.Separator(win, orient="horizontal").grid(
            row=4, column=0, columnspan=4, sticky="ew", padx=8, pady=4)

        # ── Weg 1: Staffel/Folge ─────────────────────────────────────────────
        ttk.Label(win, text="Staffel / Folge eingeben:",
                  font=("", 9, "bold")).grid(row=5, column=0, columnspan=4,
                                             sticky=tk.W, padx=12, pady=(4, 2))
        s_var = tk.StringVar(value=str(row.get("s") or ""))
        e_var = tk.StringVar(value=str(row.get("e") or ""))
        se_frame = ttk.Frame(win)
        se_frame.grid(row=6, column=0, columnspan=4, sticky=tk.W, padx=12)
        ttk.Label(se_frame, text="S").pack(side=tk.LEFT)
        ttk.Entry(se_frame, textvariable=s_var, width=5).pack(side=tk.LEFT, padx=(2, 6))
        ttk.Label(se_frame, text="E").pack(side=tk.LEFT)
        ttk.Entry(se_frame, textvariable=e_var, width=5).pack(side=tk.LEFT, padx=2)

        # ── Weg 2: Titel ─────────────────────────────────────────────────────
        ttk.Label(win, text="… oder Folgentitel suchen:",
                  font=("", 9, "bold")).grid(row=7, column=0, columnspan=4,
                                             sticky=tk.W, padx=12, pady=(10, 2))
        t_var = tk.StringVar()
        ttk.Entry(win, textvariable=t_var, width=46).grid(
            row=8, column=0, columnspan=4, sticky=tk.W, padx=12)

        vorschau = tk.StringVar(value="")
        ttk.Label(win, textvariable=vorschau, foreground="#155724",
                  wraplength=430, justify=tk.LEFT).grid(
            row=9, column=0, columnspan=4, sticky=tk.W, padx=12, pady=(8, 4))

        gefunden = {"key": None, "titel": None}

        def _bilde_namen(ms, me, titel):
            fmt = self.tvdb_fmt_var.get()
            try:
                nn = fmt.format(serie=_safe_str(serie_name),
                                s=ms, e=me, titel=_safe_str(titel))
            except Exception:
                nn = titel
            if row.get("part"):
                _b, _x = os.path.splitext(nn)
                nn = f"{_b} - pt{row['part']}{_x}"
            return _with_source_ext(nn, row["filename"])

        def _pruefe_se(*_):
            try:
                ms, me = int(s_var.get()), int(e_var.get())
            except ValueError:
                return
            titel = episodes.get((ms, me))
            if titel:
                gefunden.update(key=(ms, me), titel=titel)
                vorschau.set(f"S{ms:02d}E{me:02d} – {titel}\n→ {_bilde_namen(ms, me, titel)}")
            else:
                gefunden.update(key=None, titel=None)
                vorschau.set(f"⚠ S{ms:02d}E{me:02d} gibt es in dieser Serie nicht.")

        def _suche_titel():
            q = t_var.get().strip()
            if not q:
                return
            ms, me, titel, ratio = _best_episode_match(q, episodes)
            if not titel or ratio < 0.35:
                gefunden.update(key=None, titel=None)
                vorschau.set(f"⚠ Kein passender Titel gefunden "
                             f"(beste Übereinstimmung {ratio*100:.0f}%).")
                return
            gefunden.update(key=(ms, me), titel=titel)
            s_var.set(str(ms)); e_var.set(str(me))
            vorschau.set(f"{ratio*100:.0f}%  S{ms:02d}E{me:02d} – {titel}\n"
                         f"→ {_bilde_namen(ms, me, titel)}")

        s_var.trace_add("write", _pruefe_se)
        e_var.trace_add("write", _pruefe_se)

        def _uebernehmen():
            if not gefunden["key"]:
                vorschau.set("⚠ Bitte erst eine gültige Folge bestimmen.")
                return
            ms, me = gefunden["key"]
            neu = _bilde_namen(ms, me, gefunden["titel"])
            self.rv_tree.item(iid, tags=("ok_manual",),
                              values=(neu, gefunden["titel"], "korrigiert"))
            # Zeile stempeln, sonst sperrt das Sicherheitstor sie
            if grp is not None:
                row["matched_gid"]   = row.get("gid")
                row["matched_epoch"] = grp["epoch"]
            row["s"], row["e"] = ms, me
            self.tvdb_apply_btn.configure(state=tk.NORMAL)
            self.tvdb_apply_all_btn.configure(state=tk.NORMAL)
            self.tvdb_status_var.set(f"Folge korrigiert: S{ms:02d}E{me:02d} – {gefunden['titel']}")
            win.destroy()

        btns = ttk.Frame(win)
        btns.grid(row=10, column=0, columnspan=4, sticky="ew", padx=12, pady=(4, 12))
        ttk.Button(btns, text="🔍 Titel suchen", command=_suche_titel).pack(side=tk.LEFT)
        ttk.Button(btns, text="Übernehmen", command=_uebernehmen).pack(side=tk.RIGHT)
        ttk.Button(btns, text="Abbrechen",
                   command=win.destroy).pack(side=tk.RIGHT, padx=6)
        win.bind("<Return>", lambda _: (_suche_titel() if t_var.get().strip()
                                        else _uebernehmen()))
        _pruefe_se()

    def _tvdb_manual_edit(self):
        sel = self.rv_tree.selection()
        if not sel:
            return
        iid      = sel[0]
        cur_vals = self.rv_tree.item(iid, "values")
        cur_name = cur_vals[0] if cur_vals else ""

        win = tk.Toplevel(self.root)
        win.title("Manuell bearbeiten")
        win.resizable(False, False)
        win.grab_set()
        ttk.Label(win, text="Neuer Dateiname:").pack(padx=12, pady=(12, 4))
        var = tk.StringVar(value=cur_name)
        e   = ttk.Entry(win, textvariable=var, width=50)
        e.pack(padx=12, pady=4)
        e.select_range(0, tk.END)
        e.focus()
        def _apply():
            new_name = var.get().strip()
            if new_name:
                self.rv_tree.item(iid, tags=("ok_manual",),
                                  values=(new_name, "manuell", "✓"))
                self.tvdb_apply_btn.configure(state=tk.NORMAL)
            win.destroy()
        ttk.Button(win, text="Übernehmen", command=_apply).pack(pady=(4, 12))
        win.bind("<Return>", lambda _: _apply())

    def _tvdb_research_selected(self):
        sel = self.rv_tree.selection()
        if not sel:
            return
        win = tk.Toplevel(self.root)
        win.title("Erneut suchen")
        win.resizable(False, False)
        win.grab_set()
        ttk.Label(win, text="Anderen Seriennamen suchen:").pack(padx=12, pady=(12, 4))
        var = tk.StringVar()
        e   = ttk.Entry(win, textvariable=var, width=36)
        e.pack(padx=12, pady=4)
        e.focus()
        result_var = tk.StringVar()
        result_box = ttk.Combobox(win, textvariable=result_var, width=36, state="readonly")
        result_box.pack(padx=12, pady=4)
        _results = []

        def _search():
            name = var.get().strip()
            if not name:
                return
            client = self._tvdb_client()
            if not client:
                return
            def _thread():
                try:
                    client.authenticate()
                    found = client.search_series(name, lang=self.tvdb_lang_var.get())
                except Exception:
                    found = []
                def _upd():
                    _results.clear()
                    _results.extend(found)
                    result_box.configure(
                        values=[f"{r['name']}  ({r['year']})" for r in found])
                    if found:
                        result_box.current(0)
                self.root.after(0, _upd)
            threading.Thread(target=_thread, daemon=True).start()

        def _apply():
            idx = result_box.current()
            if idx >= 0 and _results:
                win.destroy()
                self._tvdb_run_match(series_override=_results[idx],
                                     target_iids=list(sel))
            win.destroy()

        ttk.Button(win, text="🔍 Suchen", command=_search).pack(pady=4)
        ttk.Button(win, text="Zuordnen", command=_apply).pack(pady=(4, 12))

    # Tags, die einen verwendbaren neuen Dateinamen bedeuten und automatisch
    # für "Alle umbenennen" ausgewählt werden
    _OK_TAGS = ("ok_high", "ok_mid", "ok_se", "ok_manual", "ok_movie")

    # Zur Prüfung markiert: der Vorschlag steht da, wird aber NICHT automatisch
    # ausgewählt. Der Nutzer kann die Zeile bewusst markieren und umbenennen.
    _REVIEW_TAGS = ("ok_low",)

    def _rv_tag(self, iid):
        """Erstes Tag einer Zeile, oder '' wenn keins gesetzt ist."""
        tags = self.rv_tree.item(iid, "tags")
        return tags[0] if tags else ""

    def _rv_select_matched(self):
        to_sel = [iid for iid in self.rv_tree.get_children()
                  if self._rv_tag(iid) in self._OK_TAGS]
        if to_sel:
            self.rv_tree.selection_set(to_sel)

    # ── Umbenennen ausführen ──────────────────────────────────────────────────

    def _tvdb_apply_all_rename(self):
        """Alle grün gematchten Einträge umbenennen (wie FileBot's Rename-Button)."""
        self._rv_select_matched()
        self._tvdb_apply_rename()

    @staticmethod
    def _resolve_folder_name(raw_serie, aliases):
        """Ordnername für eine Serie bestimmen.

        Probiert mehrere Schreibweisen gegen die Alias-Tabelle, damit ein
        vorhandener Alias auch dann greift, wenn die API einen Zusatz
        anhängt. TheTVDB liefert z.B. "Der Bergdoktor (2008)" – ohne diese
        Behandlung entstand daneben ein zweiter Ordner, obwohl der Alias
        "Der Bergdoktor" existiert.
        """
        raw = (raw_serie or "").strip()
        # Kandidaten in absteigender Genauigkeit
        cands = [raw]
        no_year = re.sub(r'\s*\((?:19|20)\d{2}\)\s*$', '', raw).strip()
        if no_year and no_year != raw:
            cands.append(no_year)

        # TheTVDB schreibt umbenannte Serien als Alternative mit Schrägstrich:
        # "Hubert und/ohne Staller". Beide Varianten einzeln probieren, damit ein
        # bereits vorhandener Alias für eine der Schreibweisen greift.
        for base in list(cands):
            alt = re.search(r'(\S+)/(\S+)', base)
            if alt:
                cands.append(base.replace(alt.group(0), alt.group(1)))
                cands.append(base.replace(alt.group(0), alt.group(2)))

        for c in cands:
            if c in aliases:
                return aliases[c]
        # Unabhängig von Groß-/Kleinschreibung und Umlaut-Schreibweise vergleichen
        norm_map = {_series_group_key(k): v for k, v in aliases.items()}
        for c in cands:
            hit = norm_map.get(_series_group_key(c))
            if hit:
                return hit
        # Kein Alias: den Namen ohne API-Jahreszusatz verwenden, damit nicht
        # neben einem bestehenden Ordner ein zweiter mit "(Jahr)" entsteht.
        # Verbotene Zeichen (z.B. der Schrägstrich) müssen raus, sonst
        # interpretiert os.path.join sie als Unterordner.
        return _safe_dirname(no_year or raw)

    @staticmethod
    def _movie_group_dir(stem, modus):
        """Gruppierungs-Ebene für einen Film: Buchstabe, Jahrzehnt oder Jahr.

        stem  = Dateiname ohne Endung, z.B. "Inception (2010)"
        modus = "none" | "letter" | "decade" | "year"
        Gibt "" zurück, wenn keine Ebene eingezogen werden soll.
        """
        if modus == "letter":
            titel = re.sub(r'\s*\((?:19|20)\d{2}\)\s*$', '', stem).strip()
            c = (titel[:1] or "#").upper()
            # Umlaute/Akzente auf den Grundbuchstaben falten – sonst entstünde
            # ein Ordner "Ä" direkt neben "A"
            c = {"Ä": "A", "Ö": "O", "Ü": "U", "ß": "S"}.get(c, c)
            c = "".join(ch for ch in unicodedata.normalize("NFD", c)
                        if not unicodedata.combining(ch)) or "#"
            if c.isdigit():
                return "0-9"
            return c if c.isalpha() else "#"

        if modus in ("decade", "year"):
            m = re.search(r'\((19|20)(\d{2})\)', stem) or re.search(r'\b((?:19|20)\d{2})\b', stem)
            if not m:
                return "Ohne Jahr"
            jahr = int(m.group(0).strip("()")) if m.lastindex == 1 else int(m.group(1) + m.group(2))
            return str(jahr) if modus == "year" else f"{jahr // 10 * 10}er"

        return ""

    def _sort_into_movie_folder(self, base_dir: str, filename: str,
                                conflict_cb=None):
        """Verschiebt einen Film in den Film-Zielordner.

        Struktur nach zwei unabhängigen Einstellungen:
          movie_group_mode : none | letter | decade | year   (Gruppierungs-Ebene)
          movie_subfolder  : eigener Ordner je Film (Plex-Empfehlung)
        Beispiel mit beidem: Filme\\I\\Inception (2010)\\Inception (2010).mkv
        """
        dest_root = self._watchlist.get("movie_dest_folder", "").strip()
        if not dest_root:
            # Kein eigener Film-Ordner gesetzt → auf den Serien-Zielordner
            # zurückfallen, sonst bliebe die Datei einfach liegen
            dest_root = self._watchlist.get("sort_dest_folder", "").strip()
        root = dest_root if dest_root else base_dir

        stem = os.path.splitext(filename)[0]
        gruppe = self._movie_group_dir(
            stem, self._watchlist.get("movie_group_mode", "none"))
        if gruppe:
            root = os.path.join(root, _safe_dirname(gruppe, max_len=40))
        if self._watchlist.get("movie_subfolder", True):
            ziel_ordner = os.path.join(root, _safe_dirname(stem, max_len=120))
        else:
            ziel_ordner = root
        os.makedirs(ziel_ordner, exist_ok=True)

        src  = os.path.join(base_dir, filename)
        ziel = os.path.join(ziel_ordner, filename)
        if os.path.abspath(src) == os.path.abspath(ziel):
            return ziel, None          # liegt schon richtig
        if os.path.exists(ziel):
            fehler = self._loese_konflikt(src, ziel, filename,
                                          base_dir, conflict_cb)
            if fehler is not None:
                return (None, fehler) if fehler else (ziel, None)

        # Begleitdateien (Untertitel, .nfo) mitnehmen
        begleiter = _sidecar_files(base_dir, filename)
        shutil.move(src, ziel)
        stem_neu = os.path.splitext(filename)[0]
        for pfad, rest in begleiter:
            try:
                shutil.move(pfad, os.path.join(ziel_ordner, stem_neu + rest))
            except OSError:
                pass
        return ziel, None

    def _show_id_migration(self):
        """Einmalige Umstellung bestehender Serienordner auf `Name {tvdb-ID}`."""
        root_dir = self._watchlist.get("sort_dest_folder", "").strip()
        if not root_dir or not os.path.isdir(root_dir):
            messagebox.showerror(
                "Zielordner fehlt",
                "Es ist kein gültiger Serien-Zielordner eingestellt.")
            return
        if self.series_source_var.get() != "TheTVDB":
            messagebox.showwarning(
                "Quelle umstellen",
                "Für {tvdb-…}-IDs muss die Quelle auf TheTVDB stehen.\n"
                f"Aktuell: {self.series_source_var.get()}")
            return
        client = self._tvdb_client()
        if not client:
            return

        ordner = sorted(
            d for d in os.listdir(root_dir)
            if os.path.isdir(os.path.join(root_dir, d))
            and not self._FOLDER_ID_RE.search(d))
        if not ordner:
            messagebox.showinfo(
                "Nichts zu tun",
                "Alle Serienordner haben bereits eine ID-Markierung.")
            return

        win = tk.Toplevel(self.root)
        win.title("Serienordner auf ID-Schema umstellen")
        win.grab_set()
        ttk.Label(win, text=f"Zielordner: {root_dir}",
                  foreground="gray").pack(anchor="w", padx=12, pady=(12, 0))
        ttk.Label(win, text=f"{len(ordner)} Ordner ohne ID gefunden. "
                            "Suche die Serien bei TheTVDB …",
                  font=("", 9, "bold")).pack(anchor="w", padx=12, pady=(4, 6))

        cols = ("alt", "serie", "neu", "status")
        tv = ttk.Treeview(win, columns=cols, show="headings",
                          height=min(16, len(ordner) + 1), selectmode="none")
        for c, txt, w in (("alt", "Ordner jetzt", 190), ("serie", "Gefundene Serie", 180),
                          ("neu", "Neuer Name", 230), ("status", "Status", 90)):
            tv.heading(c, text=txt)
            tv.column(c, width=w, anchor=tk.W)
        tv.pack(fill=tk.BOTH, expand=True, padx=12, pady=4)
        tv.tag_configure("ok",   background="#d4edda", foreground="#155724")
        tv.tag_configure("skip", foreground="#888888")
        tv.tag_configure("warn", background="#fff3cd", foreground="#856404")

        status_var = tk.StringVar(value="Suche läuft …")
        ttk.Label(win, textvariable=status_var).pack(anchor="w", padx=12)

        plan = []          # [(alter_pfad, neuer_pfad, anzeige)]

        # Alias-Rückwärtsabbildung: Ordnername → ursprünglicher Suchbegriff
        aliases = {**SERIEN_ALIAS, **self._watchlist.get("sort_aliases", {})}
        rueck = {}
        for k, v in aliases.items():
            rueck.setdefault(self._FOLDER_ID_RE.sub('', v).strip(), k)

        def _suchen():
            try:
                client.authenticate()
            except Exception as exc:
                self.root.after(0, lambda e=exc: status_var.set(f"Fehler: {e}"))
                return
            for name in ordner:
                sid = sname = None
                grund = ""
                # 1) Schon bestätigte Zuordnung nutzen
                gemerkt = self._remembered_series(_series_group_key(name))
                if not gemerkt and name in rueck:
                    gemerkt = self._remembered_series(_series_group_key(rueck[name]))
                if gemerkt:
                    sid, sname = gemerkt.get("id"), gemerkt.get("name", name)
                else:
                    # 2) Suchen – Alias-Rückwärtsname zuerst probieren
                    for query in [rueck.get(name), name]:
                        if not query:
                            continue
                        try:
                            res = self._cached_search(
                                client, query, self.tvdb_lang_var.get())
                        except Exception as exc:
                            grund = str(exc)[:40]
                            continue
                        state, scored = self._score_candidates(query, res)
                        if state == "RESOLVED":
                            sid   = scored[0][1]["id"]
                            sname = scored[0][1].get("name", query)
                            break
                        grund = ("mehrere Treffer" if state == "AMBIGUOUS"
                                 else "nicht gefunden")
                self.root.after(0, _zeile, name, sid, sname, grund)
            self.root.after(0, _fertig)

        def _zeile(name, sid, sname, grund):
            alt = os.path.join(root_dir, name)
            if not sid:
                tv.insert("", tk.END, tags=("warn",),
                          values=(name, "—", "—", grund or "unklar"))
                return
            neu_name = f"{name} {{tvdb-{sid}}}"
            neu = os.path.join(root_dir, neu_name)
            if os.path.exists(neu):
                tv.insert("", tk.END, tags=("skip",),
                          values=(name, sname, neu_name, "existiert"))
                return
            plan.append((alt, neu, neu_name))
            tv.insert("", tk.END, tags=("ok",),
                      values=(name, sname, neu_name, "wird umbenannt"))

        def _fertig():
            unklar = len(ordner) - len(plan)
            status_var.set(
                f"{len(plan)} Ordner werden umbenannt"
                + (f", {unklar} übersprungen (gelb – bitte von Hand prüfen)"
                   if unklar else ""))
            btn_go.configure(state=tk.NORMAL if plan else tk.DISABLED)

        def _ausfuehren():
            if not plan:
                return
            if not messagebox.askyesno(
                    "Umbenennen bestätigen",
                    f"{len(plan)} Serienordner werden umbenannt.\n\n"
                    "Plex muss die Bibliothek danach neu einlesen.\n\nFortfahren?"):
                return
            fertig, fehler = 0, []
            for alt, neu, _n in plan:
                try:
                    os.rename(alt, neu)
                    fertig += 1
                except Exception as exc:
                    fehler.append(f"{os.path.basename(alt)}: {exc}")
            win.destroy()
            msg = f"✓ {fertig} Ordner umbenannt."
            if fehler:
                msg += f"  {len(fehler)} Fehler."
                messagebox.showerror("Fehler", "\n".join(fehler[:8]))
            self.tvdb_status_var.set(msg)
            messagebox.showinfo("Fertig", msg)

        btns = ttk.Frame(win)
        btns.pack(fill=tk.X, padx=12, pady=(6, 12))
        btn_go = ttk.Button(btns, text="Umbenennen", command=_ausfuehren,
                            state=tk.DISABLED)
        btn_go.pack(side=tk.RIGHT)
        ttk.Button(btns, text="Abbrechen",
                   command=win.destroy).pack(side=tk.RIGHT, padx=6)

        threading.Thread(target=_suchen, daemon=True).start()

    def _cleanup_leftovers(self, start_dir):
        """Räumt einen abgearbeiteten Quellordner KOMPLETT ab.

        Bedingung: unter start_dir liegt keine echte Videodatei mehr (Samples
        zählen nicht als echt). Dann wird der gesamte Rest gelöscht – Samples,
        .nfo, .txt, Subs-Ordner, alles. Untertitel der verschobenen Folge sind
        vorher mitgewandert (_sidecar_files), gehen also nicht verloren.

        Gibt die Zahl gelöschter Dateien zurück (0 = nichts angefasst).
        """
        d = os.path.abspath(start_dir)
        if not os.path.isdir(d):
            return 0

        # Sicherungen wie beim Ordner-Aufräumen: Stammordner, Zielordner und
        # selbst gewählte Ordner niemals ausräumen
        parts = [p for p in d.replace("\\", "/").split("/") if p]
        if len(parts) < 3:
            return 0
        dest_root = os.path.abspath(
            self._watchlist.get("sort_dest_folder", "").strip() or os.sep)
        if d == dest_root or dest_root.startswith(d + os.sep):
            return 0
        if d in {os.path.abspath(p) for p in self._tvdb_load_roots}:
            return 0
        movie_root = self._watchlist.get("movie_dest_folder", "").strip()
        if movie_root and (d == os.path.abspath(movie_root)
                           or os.path.abspath(movie_root).startswith(d + os.sep)):
            return 0

        # Liegt noch eine echte Videodatei darin? Dann Finger weg.
        n_dateien = 0
        for r, _dirs, fs in os.walk(d):
            for f in fs:
                n_dateien += 1
                if (os.path.splitext(f)[1].lower() in _VIDEO_EXTS
                        and not _is_sample_file(r, f)):
                    return 0
        if not n_dateien:
            return 0            # schon leer – übernimmt _prune_empty_dirs

        try:
            shutil.rmtree(d)
        except OSError:
            return 0
        return n_dateien

    def _prune_empty_dirs(self, start_dir, max_levels=3):
        """Entfernt start_dir und dessen leer gewordene Elternordner.

        Löscht ausschließlich Ordner, die KEINEN einzigen Eintrag mehr haben –
        es geht also nie eine Datei verloren. Mehrere Sicherungen verhindern,
        dass ein Stammordner erwischt wird.
        """
        removed = []
        dest_root = os.path.abspath(
            self._watchlist.get("sort_dest_folder", "").strip() or os.sep)
        # Ordner, die der Nutzer selbst ausgewählt hat, bleiben immer stehen –
        # geleert werden dürfen nur die Unterordner darin.
        load_roots = {os.path.abspath(p) for p in self._tvdb_load_roots}

        d = os.path.abspath(start_dir)
        for _ in range(max_levels):
            if not os.path.isdir(d):
                break
            # Laufwerks-/Stammordner und zu flache Pfade niemals anfassen
            parts = [p for p in d.replace("\\", "/").split("/") if p]
            if len(parts) < 3:            # z.B. C:/Users -> zu flach
                break
            # Zielordner und alles darüber ist tabu
            if d == dest_root or dest_root.startswith(d + os.sep):
                break
            # Selbst gewählter Lade-Ordner ist tabu
            if d in load_roots:
                break
            try:
                if os.listdir(d):         # noch irgendetwas drin → aufhören
                    break
                parent = os.path.dirname(d)
                os.rmdir(d)               # rmdir schlägt fehl wenn nicht leer
                removed.append(d)
                d = parent
            except OSError:
                break
        return removed

    # Bereits vorhandene ID-Markierung in einem Ordnernamen
    _FOLDER_ID_RE = re.compile(r'\{(?:tvdb|tmdb|imdb|anidb)-[^}]+\}',
                               re.IGNORECASE)

    def _folder_with_id(self, name, series_id):
        """Hängt ` {tvdb-<id>}` an den Ordnernamen (Plex-Konvention).

        Nur für TheTVDB: bei TVmaze/Trakt ist series_id KEINE TVDB-ID, ein
        `{tvdb-…}` daraus wäre falsch und würde Plex auf die falsche Serie
        führen. Ein Alias, der schon eine ID enthält, bleibt unangetastet.
        """
        if not name or not series_id:
            return name
        if not self._watchlist.get("folder_append_id", True):
            return name
        if self.series_source_var.get() != "TheTVDB":
            return name                      # fremde ID – nicht als tvdb ausgeben
        if self._FOLDER_ID_RE.search(name):
            return name                      # schon eine ID vorhanden
        return f"{name} {{tvdb-{series_id}}}"

    def _frage_konflikt(self, src, ziel):
        """Fragt bei vorhandener Zieldatei nach. Gibt (aktion, fuer_alle) zurück."""
        def _mb(p):
            try:
                return f"{os.path.getsize(p) / 1024 / 1024:,.0f} MB".replace(",", ".")
            except OSError:
                return "?"

        win = tk.Toplevel(self.root)
        win.title("Datei schon vorhanden")
        win.resizable(False, False)
        win.grab_set()

        ttk.Label(win, text=os.path.basename(ziel), font=("", 9, "bold"),
                  wraplength=460, justify=tk.LEFT).pack(
            anchor="w", padx=14, pady=(14, 2))
        ttk.Label(win, text="liegt im Zielordner bereits.",
                  foreground="gray").pack(anchor="w", padx=14)

        info = ttk.Frame(win)
        info.pack(fill=tk.X, padx=14, pady=10)
        for i, (label, pfad) in enumerate((("Vorhanden:", ziel), ("Neu:", src))):
            ttk.Label(info, text=label, width=11).grid(row=i, column=0, sticky=tk.W)
            ttk.Label(info, text=_mb(pfad), width=12).grid(row=i, column=1, sticky=tk.W)
            ttk.Label(info, text=os.path.dirname(pfad), foreground="gray",
                      wraplength=330, justify=tk.LEFT).grid(row=i, column=2, sticky=tk.W)

        alle_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(win, text="Für alle weiteren Fälle in diesem Durchgang übernehmen",
                        variable=alle_var).pack(anchor="w", padx=14, pady=(0, 8))

        ergebnis = {"aktion": "skip"}

        def _w(a):
            ergebnis["aktion"] = a
            win.destroy()

        btns = ttk.Frame(win)
        btns.pack(fill=tk.X, padx=14, pady=(0, 14))
        b_ow = ttk.Button(btns, text="Überschreiben", command=lambda: _w("overwrite"))
        b_ow.pack(side=tk.LEFT)
        Tooltip(b_ow, "Die vorhandene Datei wird gelöscht und durch die neue ersetzt.")
        b_del = ttk.Button(btns, text="Neue löschen", command=lambda: _w("delete"))
        b_del.pack(side=tk.LEFT, padx=6)
        Tooltip(b_del, "Die vorhandene Datei bleibt. Die neue Datei wird gelöscht\n"
                       "(samt ihrer Untertitel).")
        ttk.Button(btns, text="Überspringen",
                   command=lambda: _w("skip")).pack(side=tk.RIGHT)

        win.protocol("WM_DELETE_WINDOW", lambda: _w("skip"))
        self.root.wait_window(win)
        return ergebnis["aktion"], alle_var.get()

    def _loese_konflikt(self, src, ziel, filename, base_dir, conflict_cb):
        """Behandelt eine bereits vorhandene Zieldatei.

        Rückgabe: None  = weitermachen (Ziel ist jetzt frei)
                  ""    = erledigt, nichts mehr zu tun (Quelle gelöscht)
                  Text  = Fehler-/Hinweismeldung, Datei bleibt liegen
        """
        aktion = conflict_cb(src, ziel) if conflict_cb else "skip"

        if aktion == "overwrite":
            try:
                os.remove(ziel)
            except OSError as exc:
                return f"Überschreiben fehlgeschlagen: {filename} ({exc})"
            return None

        if aktion == "delete":
            # Zieldatei behalten, Quelle samt Begleitdateien wegwerfen
            try:
                for pfad, _rest in _sidecar_files(base_dir, filename):
                    try:
                        os.remove(pfad)
                    except OSError:
                        pass
                os.remove(src)
            except OSError as exc:
                return f"Löschen fehlgeschlagen: {filename} ({exc})"
            return ""

        return f"Schon vorhanden: {filename}"

    def _sort_into_series_folder(self, base_dir: str, filename: str,
                                 serie_hint=None, series_id=None,
                                 conflict_cb=None):
        """Verschiebt <base_dir>/<filename> nach <Ziel>/<Serie>/Staffel XX/<filename>.

        serie_hint: wenn gesetzt, wird dieser Serienname statt des aus dem
        Dateinamen abgeleiteten benutzt. Ohne Hint ist das Verhalten unverändert.
        Gibt (ziel_pfad, fehlermeldung) zurück; fehlermeldung ist None bei Erfolg.
        """
        # Staffel 2-4 Stellen: deckt auch jahresbasierte Staffeln (S2024E02) ab,
        # die die Mediathek für laufende Serien liefert.
        m = re.match(
            r'^(.*?)\s+-\s+S(\d{2,4})E\d{1,4}(?:\s+-\s+.+)?(\.\w+)$',
            filename, re.IGNORECASE)
        if not m:
            return None, f"Muster nicht erkannt: {filename}"

        raw_serie = (serie_hint or m.group(1)).strip()
        staffel   = int(m.group(2))

        # Aliase: zuerst watchlist-Einträge, dann die eingebauten Defaults
        aliases = {**SERIEN_ALIAS, **self._watchlist.get("sort_aliases", {})}
        serie   = self._resolve_folder_name(raw_serie, aliases)

        # Vorhandenen Ordner OHNE ID weiterbenutzen, statt daneben einen
        # zweiten mit ID anzulegen – sonst zerfällt die Serie in zwei Ordner
        serie_mit_id = self._folder_with_id(serie, series_id)
        if serie_mit_id != serie:
            _root_vorab = (self._watchlist.get("sort_dest_folder", "").strip()
                           or base_dir)
            if (not os.path.isdir(os.path.join(_root_vorab, serie_mit_id))
                    and os.path.isdir(os.path.join(_root_vorab, serie))):
                serie_mit_id = serie
        serie = serie_mit_id

        season_fmt = self._watchlist.get("sort_season_fmt", "Staffel {s:02d}")
        try:
            staffel_name = season_fmt.format(s=staffel)
        except Exception:
            staffel_name = f"Staffel {staffel:02d}"

        # Zielordner: konfigurierter Stammordner hat Vorrang, sonst Quellordner
        dest_root = self._watchlist.get("sort_dest_folder", "").strip()
        root = dest_root if dest_root else base_dir
        ziel_ordner = os.path.join(root, serie, staffel_name)
        os.makedirs(ziel_ordner, exist_ok=True)

        src  = os.path.join(base_dir, filename)
        ziel = os.path.join(ziel_ordner, filename)
        if os.path.abspath(src) == os.path.abspath(ziel):
            return ziel, None          # liegt schon am richtigen Platz
        if os.path.exists(ziel):
            fehler = self._loese_konflikt(src, ziel, filename,
                                          base_dir, conflict_cb)
            if fehler is not None:
                return (None, fehler) if fehler else (ziel, None)

        # Begleitdateien (Untertitel, .mediathek, .nfo) mitnehmen
        begleiter = _sidecar_files(base_dir, filename)
        shutil.move(src, ziel)
        stem = os.path.splitext(filename)[0]
        for pfad, rest in begleiter:
            try:
                shutil.move(pfad, os.path.join(ziel_ordner, stem + rest))
            except OSError:
                pass
        return ziel, None

    def _show_sort_settings(self):
        dlg = tk.Toplevel(self.root)
        dlg.title("Einsortier-Einstellungen")
        dlg.resizable(False, False)
        dlg.grab_set()

        pad = {"padx": 10, "pady": 4}

        # ── Zielordner ───────────────────────────────────────────────────────
        ttk.Label(dlg, text="Zielordner (Serien-Stammordner):", font=("", 9, "bold")).grid(
            row=0, column=0, columnspan=2, sticky="w", **pad)
        dest_var = tk.StringVar(value=self._watchlist.get("sort_dest_folder", ""))
        dest_frame = ttk.Frame(dlg)
        dest_frame.grid(row=1, column=0, columnspan=2, sticky="ew", padx=10, pady=(0, 2))
        ttk.Entry(dest_frame, textvariable=dest_var, width=40).pack(side=tk.LEFT)
        ttk.Button(dest_frame, text="…",
                   command=lambda: dest_var.set(
                       filedialog.askdirectory(title="Serien-Stammordner wählen",
                                              initialdir=dest_var.get() or os.path.expanduser("~"))
                       or dest_var.get())).pack(side=tk.LEFT, padx=4)
        ttk.Label(dlg, text="Leer lassen = Dateien bleiben im Quellordner und werden dort einsortiert",
                  foreground="gray").grid(row=2, column=0, columnspan=2,
                                         sticky="w", padx=10, pady=(0, 2))

        prune_var = tk.BooleanVar(
            value=self._watchlist.get("sort_prune_empty", True))
        prune_cb = ttk.Checkbutton(
            dlg, text="🗑 Leer gewordene Quellordner entfernen",
            variable=prune_var)
        prune_cb.grid(row=3, column=0, columnspan=2, sticky="w", padx=10, pady=(0, 2))

        # Umgang mit bereits vorhandenen Zieldateien
        EX = [("nachfragen",                  "ask"),
              ("immer überschreiben",         "overwrite"),
              ("neue Datei immer löschen",    "delete"),
              ("immer überspringen",          "skip")]
        ex_labels, ex_modes = [e[0] for e in EX], [e[1] for e in EX]
        _cur_ex = self._watchlist.get("sort_exist_action", "ask")
        ex_var = tk.StringVar(
            value=ex_labels[ex_modes.index(_cur_ex)] if _cur_ex in ex_modes
            else ex_labels[0])
        ex_row = ttk.Frame(dlg)
        ex_row.grid(row=4, column=0, columnspan=2, sticky="w", padx=10, pady=(2, 8))
        ttk.Label(ex_row, text="Datei schon im Zielordner:").pack(side=tk.LEFT)
        _ex_box = ttk.Combobox(ex_row, textvariable=ex_var, values=ex_labels,
                               state="readonly", width=24)
        _ex_box.pack(side=tk.LEFT, padx=6)
        Tooltip(_ex_box,
                "nachfragen          → Dialog je Fall, mit Größenvergleich und\n"
                "                      „für alle übernehmen“\n"
                "überschreiben       → vorhandene Datei wird ersetzt\n"
                "neue Datei löschen  → vorhandene bleibt, die neue wird gelöscht\n"
                "überspringen        → nichts tun, Datei bleibt im Quellordner")
        Tooltip(prune_cb,
                "Nach dem Einsortieren werden Ordner gelöscht, die dadurch\n"
                "vollständig leer geworden sind (und deren ebenfalls leere\n"
                "Elternordner, bis zu 3 Ebenen).\n"
                "Ein abgearbeiteter Quellordner wird KOMPLETT abgeräumt\n"
                "(Samples, .nfo, .txt, Subs-Ordner) – aber nur, wenn darin\n"
                "keine echte Videodatei mehr liegt. Untertitel der\n"
                "verschobenen Folge wandern vorher mit und bleiben erhalten.\n"
                "Ordner mit noch vorhandenem Inhalt werden nie angefasst,\n"
                "der Zielordner und der selbst gewählte Ordner ebenfalls nicht.")

        ttk.Separator(dlg, orient="horizontal").grid(
            row=5, column=0, columnspan=2, sticky="ew", padx=8, pady=(0, 6))

        # ── Staffelordner-Format ─────────────────────────────────────────────
        ttk.Label(dlg, text="Staffelordner-Format:", font=("", 9, "bold")).grid(
            row=6, column=0, columnspan=2, sticky="w", **pad)

        PRESETS = [
            ("Staffel 01  (2 Stellen)",   "Staffel {s:02d}"),
            ("Staffel 001  (3 Stellen)",  "Staffel {s:03d}"),
            ("Staffel 1  (keine Null)",   "Staffel {s}"),
            ("Season 01  (2 Stellen)",    "Season {s:02d}"),
            ("Season 001  (3 Stellen)",   "Season {s:03d}"),
            ("Season 1  (keine Null)",    "Season {s}"),
            ("S01",                       "S{s:02d}"),
            ("Eigenes Format …",          "__custom__"),
        ]
        preset_labels  = [p[0] for p in PRESETS]
        preset_formats = [p[1] for p in PRESETS]

        saved_fmt = self._watchlist.get("sort_season_fmt", "Staffel {s:02d}")
        # Gespeichertes Format → passende Vorauswahl
        if saved_fmt in preset_formats:
            initial_idx = preset_formats.index(saved_fmt)
        else:
            initial_idx = len(PRESETS) - 1   # "Eigenes Format"

        preset_var = tk.StringVar(value=preset_labels[initial_idx])
        preset_box = ttk.Combobox(dlg, textvariable=preset_var,
                                  values=preset_labels, state="readonly", width=30)
        preset_box.grid(row=7, column=0, columnspan=2, sticky="w", padx=10, pady=(0, 4))

        fmt_var = tk.StringVar(value=saved_fmt if initial_idx == len(PRESETS) - 1 else "")
        custom_frame = ttk.Frame(dlg)
        custom_entry = ttk.Entry(custom_frame, textvariable=fmt_var, width=28)
        custom_entry.pack(side=tk.LEFT)
        ttk.Label(custom_frame, text="  {s} = Staffelnummer",
                  foreground="gray").pack(side=tk.LEFT)

        def _on_preset_change(*_):
            lbl = preset_var.get()
            idx = preset_labels.index(lbl)
            if preset_formats[idx] == "__custom__":
                custom_frame.grid(row=8, column=0, columnspan=2,
                                  sticky="w", padx=10, pady=(0, 8))
            else:
                custom_frame.grid_remove()

        preset_box.bind("<<ComboboxSelected>>", _on_preset_change)
        if initial_idx == len(PRESETS) - 1:
            custom_frame.grid(row=8, column=0, columnspan=2,
                              sticky="w", padx=10, pady=(0, 8))

        def _get_fmt():
            lbl = preset_var.get()
            idx = preset_labels.index(lbl)
            fmt = preset_formats[idx]
            return fmt_var.get().strip() or "Staffel {s:02d}" if fmt == "__custom__" else fmt

        ttk.Separator(dlg, orient="horizontal").grid(
            row=9, column=0, columnspan=2, sticky="ew", padx=8, pady=(4, 0))

        # ── Serien-Aliase ────────────────────────────────────────────────────
        ttk.Label(dlg, text="Serien-Aliase:", font=("", 9, "bold")).grid(
            row=10, column=0, columnspan=2, sticky="w", **pad)
        ttk.Label(dlg, text="Von (Name im Dateinamen)  →  Nach (Ordnername)",
                  foreground="gray").grid(row=11, column=0, columnspan=2,
                                         sticky="w", padx=10, pady=(0, 2))

        list_frame = ttk.Frame(dlg)
        list_frame.grid(row=12, column=0, columnspan=2, padx=10, pady=(0, 4), sticky="ew")
        lb = tk.Listbox(list_frame, height=8, width=62, selectmode=tk.SINGLE,
                        font=("Consolas", 9))
        lb.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sb = ttk.Scrollbar(list_frame, orient="vertical", command=lb.yview)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        lb.configure(yscrollcommand=sb.set)

        # Eingebaute Defaults + watchlist-Aliase zusammenführen
        merged = {**SERIEN_ALIAS, **self._watchlist.get("sort_aliases", {})}
        for von, nach in sorted(merged.items()):
            lb.insert(tk.END, f"{von:<35}→  {nach}")

        # Eingabezeile
        inp_frame = ttk.Frame(dlg)
        inp_frame.grid(row=13, column=0, columnspan=2, padx=10, pady=(0, 4), sticky="ew")
        ttk.Label(inp_frame, text="Von:").pack(side=tk.LEFT)
        von_var  = tk.StringVar()
        nach_var = tk.StringVar()
        ttk.Entry(inp_frame, textvariable=von_var,  width=22).pack(side=tk.LEFT, padx=4)
        ttk.Label(inp_frame, text="→").pack(side=tk.LEFT)
        ttk.Entry(inp_frame, textvariable=nach_var, width=22).pack(side=tk.LEFT, padx=4)

        def _refresh_lb():
            lb.delete(0, tk.END)
            for vv, nn in sorted(merged.items()):
                lb.insert(tk.END, f"{vv:<35}→  {nn}")

        def _on_lb_select(*_):
            sel = lb.curselection()
            if not sel:
                return
            text = lb.get(sel[0])
            parts = text.split("→", 1)
            von_var.set(parts[0].strip())
            nach_var.set(parts[1].strip() if len(parts) > 1 else "")

        lb.bind("<<ListboxSelect>>", _on_lb_select)

        def _add_alias():
            v = von_var.get().strip()
            n = nach_var.get().strip()
            if not v or not n:
                return
            merged[v] = n
            _refresh_lb()
            von_var.set("")
            nach_var.set("")

        def _remove_alias():
            sel = lb.curselection()
            if not sel:
                return
            text = lb.get(sel[0])
            von_key = text.split("→")[0].strip()
            merged.pop(von_key, None)
            _refresh_lb()
            von_var.set("")
            nach_var.set("")

        btn_row = ttk.Frame(dlg)
        btn_row.grid(row=14, column=0, columnspan=2, padx=10, pady=(0, 8), sticky="w")
        ttk.Button(btn_row, text="Hinzufügen",  command=_add_alias).pack(side=tk.LEFT, padx=2)
        ttk.Button(btn_row, text="Entfernen",   command=_remove_alias).pack(side=tk.LEFT, padx=2)

        ttk.Separator(dlg, orient="horizontal").grid(
            row=15, column=0, columnspan=2, sticky="ew", padx=8, pady=(6, 4))

        # ── Filme (eigene Einsortierung, ohne Staffelstruktur) ───────────────
        ttk.Label(dlg, text="🎬 Filme – eigener Zielordner:",
                  font=("", 9, "bold")).grid(row=16, column=0, columnspan=2,
                                             sticky="w", **pad)
        mdest_var = tk.StringVar(value=self._watchlist.get("movie_dest_folder", ""))
        mdest_frame = ttk.Frame(dlg)
        mdest_frame.grid(row=17, column=0, columnspan=2, sticky="ew", padx=10, pady=(0, 2))
        ttk.Entry(mdest_frame, textvariable=mdest_var, width=40).pack(side=tk.LEFT)
        ttk.Button(mdest_frame, text="…",
                   command=lambda: mdest_var.set(
                       filedialog.askdirectory(
                           title="Film-Stammordner wählen",
                           initialdir=mdest_var.get() or os.path.expanduser("~"))
                       or mdest_var.get())).pack(side=tk.LEFT, padx=4)
        ttk.Label(dlg, text="Leer lassen = wie bei Serien (Zielordner oben)",
                  foreground="gray").grid(row=18, column=0, columnspan=2,
                                          sticky="w", padx=10, pady=(0, 2))

        # Gruppierungs-Ebene
        MGROUPS = [("keine Gruppierung",        "none"),
                   ("nach Anfangsbuchstabe",    "letter"),
                   ("nach Jahrzehnt",           "decade"),
                   ("nach Jahr",                "year")]
        mg_labels  = [g[0] for g in MGROUPS]
        mg_modes   = [g[1] for g in MGROUPS]
        _cur_mode  = self._watchlist.get("movie_group_mode", "none")
        mgrp_var = tk.StringVar(
            value=mg_labels[mg_modes.index(_cur_mode)] if _cur_mode in mg_modes
            else mg_labels[0])
        mg_row = ttk.Frame(dlg)
        mg_row.grid(row=19, column=0, columnspan=2, sticky="w", padx=10, pady=(2, 2))
        ttk.Label(mg_row, text="Ordner-Ebene:").pack(side=tk.LEFT)
        _mg_box = ttk.Combobox(mg_row, textvariable=mgrp_var, values=mg_labels,
                               state="readonly", width=24)
        _mg_box.pack(side=tk.LEFT, padx=6)
        Tooltip(_mg_box,
                "keine        → Filme\\Inception (2010).mkv\n"
                "Buchstabe    → Filme\\I\\…        (Titel-Anfang; Zahlen unter 0-9)\n"
                "Jahrzehnt    → Filme\\2010er\\…\n"
                "Jahr         → Filme\\2010\\…\n"
                "Filme ohne Jahreszahl landen unter „Ohne Jahr“.")

        msub_var = tk.BooleanVar(value=self._watchlist.get("movie_subfolder", True))
        msub_cb = ttk.Checkbutton(
            dlg, text="Zusätzlich für jeden Film einen eigenen Unterordner",
            variable=msub_var)
        msub_cb.grid(row=20, column=0, columnspan=2, sticky="w", padx=10, pady=(0, 2))
        Tooltip(msub_cb,
                "An  → …\\Inception (2010)\\Inception (2010).mkv\n"
                "      Plex-Empfehlung: Untertitel und Bilder liegen beim Film\n"
                "Aus → …\\Inception (2010).mkv\n"
                "Lässt sich mit jeder Ordner-Ebene oben kombinieren.\n"
                "Filme bekommen nie einen Staffel-Ordner.")

        _mex = ttk.Label(dlg, text="", foreground="#3a6b00", justify=tk.LEFT)
        _mex.grid(row=21, column=0, columnspan=2, sticky="w", padx=10, pady=(2, 8))

        def _upd_movie_example(*_):
            root_txt = mdest_var.get().strip() or "<Zielordner oben>"
            modus = mg_modes[mg_labels.index(mgrp_var.get())]
            teile = [root_txt]
            g = self._movie_group_dir("Inception (2010)", modus)
            if g:
                teile.append(g)
            if msub_var.get():
                teile.append("Inception (2010)")
            teile.append("Inception (2010).mkv")
            _mex.config(text="→ " + "\\".join(teile))

        msub_var.trace_add("write", _upd_movie_example)
        mdest_var.trace_add("write", _upd_movie_example)
        mgrp_var.trace_add("write", _upd_movie_example)
        _upd_movie_example()

        ttk.Separator(dlg, orient="horizontal").grid(
            row=22, column=0, columnspan=2, sticky="ew", padx=8, pady=(6, 4))

        # ── Scan-Ordner (Knopfdruck im Umbenennen-Tab) ───────────────────────
        ttk.Label(dlg, text="🔄 Scan-Ordner (Knopf „Scan-Ordner einlesen“):",
                  font=("", 9, "bold")).grid(row=23, column=0, columnspan=2,
                                             sticky="w", **pad)

        scan_s_var = tk.StringVar(value=self._watchlist.get("scan_series_folder", ""))
        scan_m_var = tk.StringVar(value=self._watchlist.get("scan_movie_folder", ""))

        def _ordner_zeile(row, label, var, titel):
            fr = ttk.Frame(dlg)
            fr.grid(row=row, column=0, columnspan=2, sticky="ew", padx=10, pady=1)
            ttk.Label(fr, text=label, width=8).pack(side=tk.LEFT)
            ttk.Entry(fr, textvariable=var, width=36).pack(side=tk.LEFT)
            ttk.Button(fr, text="…",
                       command=lambda: var.set(
                           filedialog.askdirectory(
                               title=titel,
                               initialdir=var.get() or os.path.expanduser("~"))
                           or var.get())).pack(side=tk.LEFT, padx=4)

        _ordner_zeile(22, "Serien:", scan_s_var, "Scan-Ordner für Serien wählen")
        _ordner_zeile(23, "Filme:",  scan_m_var, "Scan-Ordner für Filme wählen")
        ttk.Label(dlg, text="Der Ordner mit den NEUEN Dateien (Downloads), nicht die "
                            "fertige Bibliothek. Unterordner werden mitgelesen.",
                  foreground="gray", wraplength=430, justify=tk.LEFT).grid(
            row=26, column=0, columnspan=2, sticky="w", padx=10, pady=(2, 8))

        ttk.Separator(dlg, orient="horizontal").grid(
            row=27, column=0, columnspan=2, sticky="ew", padx=8, pady=(6, 4))

        # ── Plex-ID im Ordnernamen ───────────────────────────────────────────
        ttk.Label(dlg, text="🆔 Serien-ID im Ordnernamen (für Plex):",
                  font=("", 9, "bold")).grid(row=28, column=0, columnspan=2,
                                             sticky="w", **pad)
        id_var = tk.BooleanVar(value=self._watchlist.get("folder_append_id", True))
        id_cb = ttk.Checkbutton(
            dlg, text="Ordnernamen um {tvdb-…} ergänzen", variable=id_var)
        id_cb.grid(row=29, column=0, columnspan=2, sticky="w", padx=10, pady=(0, 2))
        Tooltip(id_cb,
                "Ergebnis:  Roseanne {tvdb-77068}\\Staffel 01\\…\n"
                "Plex erkennt die Serie damit eindeutig.\n"
                "Wirkt nur bei Quelle = TheTVDB (nur dort ist die ID eine\n"
                "echte TVDB-ID). Ein Alias, der schon eine ID enthält, und\n"
                "ein bereits vorhandener Ordner ohne ID bleiben unberührt.")
        ttk.Button(dlg, text="Bestehende Serienordner jetzt umstellen …",
                   command=self._show_id_migration).grid(
            row=30, column=0, columnspan=2, sticky="w", padx=10, pady=(2, 8))

        ttk.Separator(dlg, orient="horizontal").grid(
            row=31, column=0, columnspan=2, sticky="ew", padx=8, pady=4)

        def _save():
            self._watchlist["sort_season_fmt"]    = _get_fmt()
            self._watchlist["sort_dest_folder"]   = dest_var.get().strip()
            self._watchlist["sort_prune_empty"]   = bool(prune_var.get())
            self._watchlist["sort_exist_action"]  = ex_modes[
                ex_labels.index(ex_var.get())]
            self._watchlist["movie_dest_folder"]  = mdest_var.get().strip()
            self._watchlist["movie_subfolder"]    = bool(msub_var.get())
            self._watchlist["movie_group_mode"]   = mg_modes[
                mg_labels.index(mgrp_var.get())]
            self._watchlist["scan_series_folder"] = scan_s_var.get().strip()
            self._watchlist["scan_movie_folder"]  = scan_m_var.get().strip()
            self._watchlist["folder_append_id"]   = bool(id_var.get())
            # Nur vom Default abweichende Einträge in der watchlist speichern
            custom = {v: n for v, n in merged.items() if SERIEN_ALIAS.get(v) != n}
            self._watchlist["sort_aliases"] = custom
            self._save_watchlist()
            dlg.destroy()

        ok_row = ttk.Frame(dlg)
        ok_row.grid(row=32, column=0, columnspan=2, pady=(0, 10))
        ttk.Button(ok_row, text="Speichern", command=_save).pack(side=tk.LEFT, padx=6)
        ttk.Button(ok_row, text="Abbrechen", command=dlg.destroy).pack(side=tk.LEFT, padx=6)

    def _row_rename_allowed(self, row, iid):
        """Sicherheitstor: darf diese Zeile umbenannt werden?

        Verhindert dass eine Datei mit dem Namen einer anderen Serie
        umbenannt wird, wenn die Gruppenzuordnung nicht sauber ist.
        """
        tag = self._rv_tag(iid)
        if tag == "ok_manual":
            return True          # handgetippter Name ist immer erlaubt
        # "prüfen"-Zeilen sind erlaubt, wenn der Nutzer sie bewusst markiert hat
        # (sie werden von _rv_select_matched nicht automatisch ausgewählt)
        allowed = self._OK_TAGS + self._REVIEW_TAGS
        gid = row.get("gid")
        if gid == "__movie__":
            return tag in allowed            # Film-Modus: unverändert
        grp = self._tvdb_groups.get(gid)
        if grp is None:
            # Kein Gruppen-Zustand (klassischer Einzelserien-Lauf) → wie bisher
            return tag in allowed
        if grp["state"] != "RESOLVED":
            return False
        if row.get("matched_gid") != gid:
            return False
        if row.get("matched_epoch") != grp["epoch"]:
            return False
        return tag in allowed

    def _tvdb_apply_rename(self):
        if self._tvdb_batch_busy:
            return
        selected = self.rv_tree.selection()
        if not selected:
            return

        to_rename, blocked = [], []
        for iid in selected:
            file_row = self._tvdb_rows_by_iid.get(iid)
            if file_row is None:
                continue
            vals     = self.rv_tree.item(iid, "values")
            new_name = vals[0] if vals else ""
            if not new_name or new_name == "—":
                continue
            # Endung der QUELLDATEI beibehalten: die Formatvorlagen enden fest
            # auf ".mp4" – ohne das würde aus einer .mkv eine .mp4, obwohl der
            # Inhalt unverändert bleibt.
            src_ext = os.path.splitext(file_row["filename"])[1]
            _base, new_ext = os.path.splitext(new_name)
            if src_ext and new_ext.lower() != src_ext.lower():
                new_name = _base + src_ext
            # Dateien mit bereits richtigem Namen NICHT überspringen – sie
            # müssen trotzdem einsortiert und aus der Liste genommen werden.
            # Das Umbenennen selbst entfällt dann einfach.
            if not self._row_rename_allowed(file_row, iid):
                blocked.append(file_row["filename"])
                continue
            to_rename.append((iid, file_row, new_name))

        # Seriennamen JETZT festhalten: nach dem Umbenennen werden die Zeilen
        # entfernt und _rebuild_groups() löscht die dann leeren Gruppen – der
        # Hinweis für das Einsortieren wäre sonst verloren und es würde auf den
        # Dateinamen-Präfix zurückfallen (Hubert landete so im falschen Ordner).
        serie_hints, serie_ids = {}, {}
        for iid, file_row, _n in to_rename:
            grp = self._tvdb_groups.get(file_row.get("gid"))
            if not grp:
                continue
            if grp.get("serie_name"):
                serie_hints[iid] = grp["serie_name"]
            if grp.get("series") and grp["series"].get("id"):
                serie_ids[iid] = grp["series"]["id"]

        if blocked:
            if self.rename_mode_var.get() == "movie":
                grund = ("weil ihnen noch kein Filmtitel zugeordnet ist")
                rat   = "Bitte zuerst „🎬 Filme zuordnen“ ausführen."
            else:
                grund = "weil ihre Serie nicht eindeutig zugeordnet ist"
                rat   = "Bitte oben die Gruppe anklicken und die Serie wählen."
            messagebox.showwarning(
                "Übersprungen",
                f"{len(blocked)} Datei(en) werden übersprungen, {grund}:\n\n"
                + "\n".join(f"• {b}" for b in blocked[:8])
                + f"\n\n{rat}")

        if not to_rename:
            if not blocked:
                messagebox.showinfo(
                    "Nichts zu tun",
                    "Alle ausgewählten Dateien haben bereits den richtigen Namen.")
            return

        # Vorschau nach Serie gruppieren, damit bei gemischten Batches sichtbar
        # ist welche Serie welche Dateien bekommt
        by_group = {}
        for _iid, r, n in to_rename:
            if r.get("gid") == "__movie__":
                label = "Filme"
            else:
                grp = self._tvdb_groups.get(r.get("gid"))
                label = ((grp["serie_name"] or grp["raw"]) if grp
                         else (r.get("series_raw") or "—"))
            by_group.setdefault(label, []).append((r["filename"], n))

        n_gleich = sum(1 for _i, r, n in to_rename if n == r["filename"])
        parts = []
        for label in sorted(by_group):
            items = by_group[label]
            parts.append(f"▸ {label}  ({len(items)})")
            gezeigt = 0
            for old, new in items:
                if gezeigt >= 3:
                    break
                if old == new:
                    parts.append(f"    {old}\n    → Name bereits richtig, wird nur einsortiert")
                else:
                    parts.append(f"    {old}\n    → {new}")
                gezeigt += 1
            if len(items) > 3:
                parts.append(f"    … ({len(items) - 3} weitere)")
        if blocked:
            parts.append(f"\n▸ {len(blocked)} Datei(en) werden übersprungen")
        preview = "\n".join(parts)

        n_neu = len(to_rename) - n_gleich
        kopf = []
        if n_neu:
            kopf.append(f"{n_neu} umbenennen")
        if n_gleich:
            kopf.append(f"{n_gleich} nur einsortieren (Name schon richtig)")
        if not messagebox.askyesno(
                "Umbenennen bestätigen",
                f"{len(to_rename)} Datei(en): " + ", ".join(kopf) + f"?\n\n{preview}"):
            return

        errors        = []
        renamed       = 0
        schon_ok      = 0          # Name war bereits richtig
        remove_iids   = []
        for iid, file_row, new_name in to_rename:
            if new_name == file_row["filename"]:
                # Nichts umzubenennen – aber einsortieren und aus der Liste
                schon_ok += 1
                remove_iids.append(iid)
                continue
            src = os.path.join(file_row["dir"], file_row["filename"])
            dst = os.path.join(file_row["dir"], new_name)
            # Begleitdateien VOR dem Umbenennen einsammeln – danach passt der
            # Basisname nicht mehr
            begleiter = _sidecar_files(file_row["dir"], file_row["filename"])
            neu_base  = os.path.splitext(new_name)[0]
            try:
                os.rename(src, dst)
                for pfad, rest in begleiter:
                    try:
                        os.rename(pfad, os.path.join(file_row["dir"],
                                                     neu_base + rest))
                    except OSError:
                        pass
                remove_iids.append(iid)
                renamed += 1
            except Exception as exc:
                errors.append(f"{file_row['filename']}: {exc}")

        # Erfolgreich umbenannte Zeilen entfernen – per IDENTITÄT, nicht per
        # Index. Ein Fehlindex würde hier die falsche Zeile löschen.
        if remove_iids:
            done = set(remove_iids)
            for iid in remove_iids:
                row = self._tvdb_rows_by_iid.pop(iid, None)
                if self.rv_tree.exists(iid):
                    self.rv_tree.delete(iid)
                if row is None:
                    continue
                lv_iid = row.get("lv_iid", "")
                if self.lv_tree.exists(lv_iid):
                    self.lv_tree.delete(lv_iid)
                try:
                    self._tvdb_file_rows.remove(row)
                except ValueError:
                    pass
            self._update_lv_watermark()
            self._rebuild_groups()

        # ── Einsortieren ──────────────────────────────────────────────────────
        sorted_count = 0
        sort_errors  = []
        touched_dirs = set()

        # Umgang mit bereits vorhandenen Zieldateien
        _kf = {"alle": None, "overwrite": 0, "delete": 0, "skip": 0}

        def _konflikt(src, ziel):
            modus = self._watchlist.get("sort_exist_action", "ask")
            if modus in ("overwrite", "delete", "skip"):
                aktion = modus
            elif _kf["alle"]:
                aktion = _kf["alle"]
            else:
                aktion, fuer_alle = self._frage_konflikt(src, ziel)
                if fuer_alle:
                    _kf["alle"] = aktion
            _kf[aktion] = _kf.get(aktion, 0) + 1
            return aktion

        if self.sort_after_rename_var.get() and remove_iids:
            done_iids = set(remove_iids)
            for iid, file_row, new_name in to_rename:
                if iid not in done_iids:
                    continue
                if file_row.get("gid") == "__movie__":
                    # Filme haben keine Staffelstruktur – eigener Weg
                    _, err = self._sort_into_movie_folder(
                        file_row["dir"], new_name, conflict_cb=_konflikt)
                else:
                    # Vorher festgehaltenen Seriennamen benutzen – die Gruppe
                    # existiert an dieser Stelle nicht mehr
                    _, err = self._sort_into_series_folder(
                        file_row["dir"], new_name,
                        serie_hint=serie_hints.get(iid),
                        series_id=serie_ids.get(iid),
                        conflict_cb=_konflikt)
                if err:
                    sort_errors.append(err)
                else:
                    sorted_count += 1
                    touched_dirs.add(file_row["dir"])

        # ── Leer gewordene Quellordner entfernen ─────────────────────────────
        pruned, n_reste_weg = [], 0
        if touched_dirs and self._watchlist.get("sort_prune_empty", True):
            # Abgearbeitete Quellordner komplett abräumen (Samples, .nfo, Subs …)
            for d in touched_dirs:
                n_reste_weg += self._cleanup_leftovers(d)
            # Tiefste zuerst, damit Elternordner danach ebenfalls leer sein können
            for d in sorted(touched_dirs, key=lambda p: -len(p)):
                pruned.extend(self._prune_empty_dirs(d))

        msg = f"✓ {renamed} Datei(en) umbenannt."
        if schon_ok:
            msg += f"  {schon_ok} war(en) schon richtig benannt."
        if sorted_count:
            msg += f"  📁 {sorted_count} einsortiert."
        if _kf["overwrite"]:
            msg += f"  ♻ {_kf['overwrite']} überschrieben."
        if _kf["delete"]:
            msg += f"  🗑 {_kf['delete']} doppelte gelöscht."
        if _kf["skip"]:
            msg += f"  ⏭ {_kf['skip']} übersprungen (schon vorhanden)."
        if n_reste_weg:
            msg += f"  🗑 {n_reste_weg} Restdatei(en) gelöscht."
        if pruned:
            msg += f"  🗑 {len(pruned)} leere(r) Ordner entfernt."
        if errors:
            msg += f"  {len(errors)} Fehler."

        # Erklären, WARUM noch Zeilen in der Liste stehen – sonst wirkt es
        # so, als hätte das Umbenennen etwas vergessen
        rest = list(self.rv_tree.get_children())
        if rest:
            n_review = n_none = n_gate = 0
            for _iid in rest:
                _tag = self._rv_tag(_iid)
                _row = self._tvdb_rows_by_iid.get(_iid)
                if _tag in self._REVIEW_TAGS:
                    n_review += 1
                elif _tag in ("nomatch", "nose"):
                    n_none += 1
                elif _row is not None and not self._row_rename_allowed(_row, _iid):
                    n_gate += 1
            teile = []
            if n_review: teile.append(f"{n_review} unsicher (orange – bitte prüfen)")
            if n_none:   teile.append(f"{n_none} ohne Treffer")
            if n_gate:   teile.append(f"{n_gate} ohne zugeordnete Serie")
            msg += (f"  |  {len(rest)} Datei(en) bleiben übrig"
                    + (": " + ", ".join(teile) if teile else ""))
        self.tvdb_status_var.set(msg)
        if errors:
            messagebox.showerror("Fehler", "\n".join(errors[:10]))
        if sort_errors:
            messagebox.showwarning("Einsortieren – Hinweise", "\n".join(sort_errors[:10]))

    # ═══════════════════════════════════════════════════════════════════════════
    # Modus-Umschaltung & TMDB-Logik
    # ═══════════════════════════════════════════════════════════════════════════

    def _on_rename_mode_change(self):
        """Schaltet zwischen Serien- und Film-Modus um.

        Nur noch der Zuordnungs-Bereich wird getauscht – die Einstellungen
        liegen im ⚙-Dialog und brauchen kein Ein-/Ausblenden mehr.
        """
        mode   = self.rename_mode_var.get()
        toggle = self._rename_mode_toggle
        if mode == "series":
            self._tmdb_qf_frame.pack_forget()
            self._qf_frame.pack(fill=tk.X, padx=8, pady=(0, 4), after=toggle)
            self._src_box.configure(textvariable=self.series_source_var,
                                    values=["TheTVDB", "Trakt.tv", "TVmaze"])
            self.rv_tree.heading("ep_title", text="Episodentitel (TheTVDB)")
        else:
            self._qf_frame.pack_forget()
            self._tmdb_qf_frame.pack(fill=tk.X, padx=8, pady=(0, 4), after=toggle)
            self._src_box.configure(textvariable=self.movie_source_var,
                                    values=["TheMovieDB", "OMDb (IMDb)"])
            self.rv_tree.heading("ep_title", text="Filmtitel (TMDB)")
        self._tvdb_clear_files()

    def _save_source_choice(self):
        """Quellenwahl aus der Kopfzeile sichern."""
        if self.rename_mode_var.get() == "movie":
            self._watchlist["movie_source"] = self.movie_source_var.get()
        else:
            self._watchlist["series_source"] = self.series_source_var.get()
        self._save_watchlist()

    def _show_api_settings(self):
        """API-Keys, Sprache, Reihenfolge und Namensvorlage.

        Lag früher dauerhaft im Umbenennen-Tab und belegte dort rund 200 px,
        obwohl man es einmal einstellt und nie wieder anschaut.
        """
        dlg = tk.Toplevel(self.root)
        dlg.title("API & Format")
        dlg.resizable(False, False)
        dlg.grab_set()

        nb = ttk.Notebook(dlg)
        nb.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        tab_s = ttk.Frame(nb, padding=10)
        tab_m = ttk.Frame(nb, padding=10)
        nb.add(tab_s, text="  📺 Serien  ")
        nb.add(tab_m, text="  🎬 Filme  ")
        nb.select(tab_m if self.rename_mode_var.get() == "movie" else tab_s)

        def _key_zeile(parent, row, label, var, hinweis, width=36):
            ttk.Label(parent, text=label).grid(row=row, column=0, sticky=tk.W,
                                              padx=4, pady=4)
            e = ttk.Entry(parent, textvariable=var, width=width, show="*")
            e.grid(row=row, column=1, padx=4, pady=4, sticky=tk.W)
            ttk.Button(parent, text="👁", width=3,
                       command=lambda: e.configure(
                           show="" if e.cget("show") else "*")
                       ).grid(row=row, column=2, padx=2)
            ttk.Label(parent, text=hinweis, foreground="gray").grid(
                row=row, column=3, columnspan=2, padx=6, sticky=tk.W)

        # ── Serien ───────────────────────────────────────────────────────────
        _key_zeile(tab_s, 0, "TheTVDB API-Key:", self.tvdb_key_var,
                   "thetvdb.com → Account → API Access")
        _key_zeile(tab_s, 1, "Trakt Client-ID:", self.trakt_key_var,
                   "trakt.tv → Settings → Your API Apps", width=30)

        ttk.Label(tab_s, text="Sprache:").grid(row=2, column=0, sticky=tk.W, padx=4, pady=4)
        _lb = ttk.Combobox(tab_s, textvariable=self.tvdb_lang_var, width=8,
                           state="readonly", values=["deu", "eng", "fra", "spa", "jpn"])
        _lb.grid(row=2, column=1, sticky=tk.W, padx=4)
        Tooltip(_lb, "deu=Deutsch  eng=Englisch  fra=Französisch  spa=Spanisch")

        ttk.Label(tab_s, text="Reihenfolge:").grid(row=3, column=0, sticky=tk.W, padx=4, pady=4)
        _ob = ttk.Combobox(tab_s, textvariable=self.tvdb_order_var, width=12,
                           state="readonly", values=["official", "absolute"])
        _ob.grid(row=3, column=1, sticky=tk.W, padx=4)
        Tooltip(_ob, "official = Staffel-basiert (Standard)\n"
                     "absolute = Durchgehende Nummerierung (Anime wie Dragon Ball Z)")

        ttk.Label(tab_s, text="Namensvorlage:").grid(row=4, column=0, sticky=tk.W,
                                                     padx=4, pady=4)
        _fe = ttk.Entry(tab_s, textvariable=self.tvdb_fmt_var, width=52)
        _fe.grid(row=4, column=1, columnspan=3, padx=4, sticky=tk.W)
        Tooltip(_fe, "Platzhalter: {serie}  {s}  {e}  {titel}\n"
                     "Beispiel: {serie} - S{s:02d}E{e:02d} - {titel}.mp4\n"
                     "→ Bibi und Tina - S03E10 - Er will leben.mp4\n"
                     "Für absolute Reihenfolge: {serie} - E{e:03d} - {titel}.mp4\n"
                     "Die Dateiendung wird immer von der Quelldatei übernommen.")

        # ── Filme ────────────────────────────────────────────────────────────
        _key_zeile(tab_m, 0, "TheMovieDB API-Key:", self.tmdb_key_var,
                   "themoviedb.org → Einstellungen → API")
        _key_zeile(tab_m, 1, "OMDb API-Key:", self.omdb_key_var,
                   "omdbapi.com/apikey.aspx (kostenlos)", width=28)

        ttk.Label(tab_m, text="Sprache:").grid(row=2, column=0, sticky=tk.W, padx=4, pady=4)
        _mlb = ttk.Combobox(tab_m, textvariable=self.tmdb_lang_var, width=8,
                            state="readonly", values=["de", "en", "fr", "es", "ja", "it"])
        _mlb.grid(row=2, column=1, sticky=tk.W, padx=4)

        ttk.Label(tab_m, text="Namensvorlage:").grid(row=3, column=0, sticky=tk.W,
                                                     padx=4, pady=4)
        _mfe = ttk.Entry(tab_m, textvariable=self.tmdb_fmt_var, width=44)
        _mfe.grid(row=3, column=1, columnspan=3, padx=4, sticky=tk.W)
        Tooltip(_mfe, "Platzhalter: {titel}  {jahr}  {originaltitel}\n"
                      "Beispiel: {titel} ({jahr}).mp4  →  Inception (2010).mp4\n"
                      "Die Dateiendung wird immer von der Quelldatei übernommen.")

        def _speichern():
            self._save_tvdb_key()
            self._save_tmdb_key()
            dlg.destroy()

        btns = ttk.Frame(dlg)
        btns.pack(fill=tk.X, padx=10, pady=(0, 10))
        ttk.Button(btns, text="💾 Speichern", command=_speichern).pack(side=tk.RIGHT)
        ttk.Button(btns, text="Abbrechen",
                   command=dlg.destroy).pack(side=tk.RIGHT, padx=6)

    def _save_tmdb_key(self):
        self._watchlist["tmdb_api_key"] = self.tmdb_key_var.get().strip()
        self._watchlist["tmdb_lang"]    = self.tmdb_lang_var.get()
        self._watchlist["tmdb_fmt"]     = self.tmdb_fmt_var.get()
        self._watchlist["movie_source"] = self.movie_source_var.get()
        self._watchlist["omdb_api_key"] = self.omdb_key_var.get().strip()
        self._save_watchlist()
        self.tmdb_status_var.set("✓ Gespeichert.")
        self.root.after(2000, lambda: self.tmdb_status_var.set(""))

    def _tmdb_client(self):
        if self.movie_source_var.get().startswith("OMDb"):
            key = self.omdb_key_var.get().strip()
            if not key:
                messagebox.showwarning("API-Key fehlt",
                    "Bitte OMDb API-Key eingeben und speichern.\n"
                    "Kostenlos: omdbapi.com/apikey.aspx")
                return None
            return OMDbClient(key)

        key = self.tmdb_key_var.get().strip()
        if not key:
            messagebox.showwarning("API-Key fehlt",
                "Bitte TheMovieDB API-Key eingeben und speichern.\n"
                "Kostenlos: themoviedb.org → Einstellungen → API")
            return None
        return TMDBClient(key)

    def _tmdb_run_match(self):
        if not self._tvdb_file_rows:
            messagebox.showinfo("Keine Dateien",
                                "Bitte erst Dateien oder einen Ordner hinzufügen.")
            return
        client = self._tmdb_client()
        if not client:
            return
        self.tmdb_match_btn.configure(state=tk.DISABLED)
        self.tmdb_status_var.set("Suche läuft …")
        threading.Thread(target=self._tmdb_match_thread,
                         args=(client,), daemon=True).start()

    def _tmdb_match_thread(self, client):
        lang     = self.tmdb_lang_var.get()
        fmt      = self.tmdb_fmt_var.get()
        all_iids = self.rv_tree.get_children()
        auto_updates   = []
        picker_queue   = []
        no_match_queue = []   # (iid, file_row) – kein Treffer

        _here    = os.path.dirname(sys.executable if getattr(sys, "frozen", False)
                                   else os.path.abspath(__file__))
        dbg_path = os.path.join(_here, "tmdb_match_debug.txt")
        dbg      = [
            f"Sprache: {lang}\n",
            f"{'Dateiname':<50} {'Erkannter Titel':<30} {'Jahr':<6} "
            f"{'Treffer':<4} {'Ergebnis'}\n",
            "-" * 120 + "\n",
        ]

        for iid, file_row in zip(all_iids, self._tvdb_file_rows):
            title_guess = file_row.get("title_guess", "")
            year        = file_row.get("year")
            fname       = file_row["filename"]

            if not title_guess:
                auto_updates.append((iid, fname, "kein Titel erkannt", "—", "nose"))
                dbg.append(f"{fname:<50} {'—':<30} {year or '':<6} 0    kein Titel\n")
                continue

            try:
                results = client.search_movies(title_guess, language=lang, year=year)
                if not results and year:
                    results = client.search_movies(title_guess, language=lang)
            except Exception as exc:
                auto_updates.append((iid, fname, str(exc)[:60], "!", "nomatch"))
                dbg.append(f"{fname:<50} {title_guess:<30} {year or '':<6} ERR  {exc}\n")
                continue

            n = len(results)
            if not results:
                no_match_queue.append((iid, file_row))
                dbg.append(f"{fname:<50} {title_guess:<30} {year or '':<6} 0    KEIN TREFFER\n")
            elif n == 1:
                auto_updates.append(self._tmdb_make_update(iid, results[0], fmt, year))
                m = results[0]
                dbg.append(f"{fname:<50} {title_guess:<30} {year or '':<6} 1    "
                           f"{m['title']} ({m['year']})\n")
            else:
                picker_queue.append((iid, file_row, results, fmt, client))
                top3 = "  |  ".join(f"{r['title']} ({r['year']})" for r in results[:3])
                dbg.append(f"{fname:<50} {title_guess:<30} {year or '':<6} {n:<4} "
                           f"AUSWAHL: {top3}\n")

        try:
            with open(dbg_path, "w", encoding="utf-8") as f:
                f.writelines(dbg)
        except Exception:
            pass

        self.root.after(0, self._tmdb_apply_auto,
                        auto_updates, picker_queue, no_match_queue)

    def _tmdb_make_update(self, iid, movie, fmt, fallback_year=""):
        title      = movie["title"]
        orig       = movie["original_title"]
        movie_year = movie.get("year") or fallback_year or ""
        try:
            new_name = fmt.format(
                titel=_safe_str(title, allowed=" _-.,!()"),
                originaltitel=_safe_str(orig, allowed=" _-.,!()"),
                jahr=movie_year)
        except Exception:
            new_name = f"{_safe_str(title)} ({movie_year})"
        _row = self._tvdb_rows_by_iid.get(iid)
        if _row:
            new_name = _with_source_ext(new_name, _row["filename"])
        return (iid, new_name, title, "✓", "ok_movie")

    def _tmdb_apply_auto(self, auto_updates, picker_queue, no_match_queue=None):
        ok = 0
        for iid, new_name, film_title, status, tag in auto_updates:
            if self.rv_tree.exists(iid):
                self.rv_tree.item(iid, tags=(tag,),
                                  values=(new_name, film_title, status))
                if tag == "ok_movie":
                    ok += 1
        self._tmdb_ok_count  = ok
        self._tmdb_no_match  = list(no_match_queue or [])
        total = len(self._tvdb_file_rows)

        if picker_queue:
            n_nm = len(self._tmdb_no_match)
            msg  = f"{ok} automatisch – {len(picker_queue)} zur Auswahl"
            if n_nm:
                msg += f" – {n_nm} nicht gefunden"
            self.tmdb_status_var.set(msg + " …")
            self._tmdb_show_picker(picker_queue, 0)
        elif self._tmdb_no_match:
            self.tmdb_status_var.set(
                f"{ok} automatisch – {len(self._tmdb_no_match)} nicht gefunden …")
            self._tmdb_ask_title(self._tmdb_no_match, 0)
        else:
            self._tmdb_finish(ok, total)

    def _tmdb_finish(self, ok, total):
        self.tmdb_match_btn.configure(state=tk.NORMAL)
        self.tmdb_status_var.set(f"✓ {ok} von {total} gefunden.")
        if ok:
            self.tvdb_apply_btn.configure(state=tk.NORMAL)
            self.tvdb_apply_all_btn.configure(state=tk.NORMAL)

    # ── Film-Auswahl-Dialog ───────────────────────────────────────────────────

    def _tmdb_show_picker(self, queue, idx):
        if idx >= len(queue):
            if self._tmdb_no_match:
                self._tmdb_ask_title(self._tmdb_no_match, 0)
            else:
                self._tmdb_finish(self._tmdb_ok_count, len(self._tvdb_file_rows))
            return

        iid, file_row, results, fmt, client = queue[idx]
        fname = file_row.get("filename", "")
        year  = file_row.get("year", "")

        win = tk.Toplevel(self.root)
        win.title("Film auswählen")
        win.transient(self.root)
        win.grab_set()
        win.resizable(True, True)

        # ── Kopfzeile ────────────────────────────────────────────────────────
        hdr = ttk.Frame(win)
        hdr.pack(fill=tk.X, padx=12, pady=(10, 4))
        ttk.Label(hdr, text=f"Datei:  ", font=("", 9, "bold")).pack(side=tk.LEFT)
        ttk.Label(hdr, text=fname, foreground="#444").pack(side=tk.LEFT)
        remaining = len(queue) - idx
        ttk.Label(hdr, text=f"   ({remaining} verbleibend)",
                  foreground="gray").pack(side=tk.LEFT)

        # ── Scrollbarer Bereich ───────────────────────────────────────────────
        outer = ttk.Frame(win)
        outer.pack(fill=tk.BOTH, expand=True, padx=12, pady=4)

        canvas = tk.Canvas(outer, width=580, height=340, highlightthickness=0)
        vsb    = ttk.Scrollbar(outer, orient=tk.VERTICAL, command=canvas.yview)
        canvas.configure(yscrollcommand=vsb.set)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        scroll_frame = ttk.Frame(canvas)
        canvas_win   = canvas.create_window((0, 0), window=scroll_frame,
                                            anchor=tk.NW)

        def _on_cf_resize(e):
            canvas.configure(scrollregion=canvas.bbox("all"))
            canvas.itemconfig(canvas_win, width=canvas.winfo_width())
        scroll_frame.bind("<Configure>", _on_cf_resize)
        canvas.bind("<Configure>",
                    lambda e: canvas.itemconfig(canvas_win,
                                                width=e.width))
        canvas.bind("<MouseWheel>",
                    lambda e: canvas.yview_scroll(-1*(e.delta//120), "units"))

        # Duplikate nach TMDB-ID entfernen
        seen_ids = set()
        unique_results = []
        for r in results:
            if r["id"] not in seen_ids:
                seen_ids.add(r["id"])
                unique_results.append(r)
        results = unique_results

        POSTER_W, POSTER_H = 92, 138

        # Grauer Platzhalter als echtes Pixel-Bild (verhindert riesige Label)
        if HAS_PIL:
            _ph_img = Image.new("RGB", (POSTER_W, POSTER_H), "#dddddd")
            _ph_photo = ImageTk.PhotoImage(_ph_img)
        else:
            _ph_photo = None

        selected_var = tk.IntVar(value=0)
        row_frames   = []
        _photo_refs  = [_ph_photo] if _ph_photo else []

        def _highlight(i):
            selected_var.set(i)
            for j, rf in enumerate(row_frames):
                rf.configure(
                    relief=tk.SOLID if j == i else tk.FLAT,
                    borderwidth=2 if j == i else 0)

        def _bind_row(widget, n):
            widget.bind("<Button-1>", lambda e, _n=n: _highlight(_n))
            for child in widget.winfo_children():
                _bind_row(child, n)

        for i, movie in enumerate(results):
            rf = tk.Frame(scroll_frame, cursor="hand2",
                          relief=tk.FLAT, borderwidth=0, bg="#f8f8f8")
            rf.pack(fill=tk.X, padx=4, pady=3)
            row_frames.append(rf)

            # Poster – mit echtem Pixel-Platzhalterbild
            if _ph_photo:
                poster_lbl = tk.Label(rf, image=_ph_photo, bg="#dddddd")
            else:
                poster_lbl = tk.Label(rf, text="🎬", font=("", 20),
                                      bg="#dddddd", width=6)
            poster_lbl.grid(row=0, column=0, rowspan=3,
                            padx=(6, 10), pady=6, sticky=tk.NW)

            # Textinfos
            tk.Label(rf, text=movie["title"],
                     font=("", 11, "bold"), bg="#f8f8f8",
                     anchor=tk.W).grid(row=0, column=1, sticky=tk.W)
            sub = f"{movie['year']}   Originaltitel: {movie['original_title']}"
            tk.Label(rf, text=sub, font=("", 8), fg="#666",
                     bg="#f8f8f8", anchor=tk.W).grid(
                row=1, column=1, sticky=tk.W)
            overview = movie.get("overview", "")
            tk.Label(rf, text=overview, wraplength=400,
                     font=("", 9), fg="#333", bg="#f8f8f8",
                     justify=tk.LEFT, anchor=tk.W).grid(
                row=2, column=1, sticky=tk.W, pady=(0, 4))

            _bind_row(rf, i)

            # Poster asynchron laden
            if HAS_PIL and movie.get("poster_path"):
                url = client.poster_url(movie["poster_path"])
                def _load_poster(u=url, lbl=poster_lbl):
                    try:
                        resp = requests.get(u, timeout=8)
                        resp.raise_for_status()
                        img = Image.open(_io.BytesIO(resp.content))
                        img = img.resize((POSTER_W, POSTER_H), Image.LANCZOS)
                        ph  = ImageTk.PhotoImage(img)
                        _photo_refs.append(ph)
                        win.after(0, lambda p=ph, l=lbl:
                                  (l.configure(image=p, bg="#fff"),
                                   setattr(l, "image", p)))
                    except Exception:
                        pass
                threading.Thread(target=_load_poster, daemon=True).start()

        _highlight(0)

        # ── Schaltflächen ─────────────────────────────────────────────────────
        btn_frame = ttk.Frame(win)
        btn_frame.pack(fill=tk.X, padx=12, pady=(4, 10))

        def _accept():
            chosen = results[selected_var.get()]
            upd = self._tmdb_make_update(iid, chosen, fmt, year)
            if self.rv_tree.exists(iid):
                self.rv_tree.item(iid, tags=(upd[4],),
                                  values=(upd[1], upd[2], upd[3]))
                if upd[4] == "ok_movie":
                    self._tmdb_ok_count += 1
            win.destroy()
            self.root.after(50, lambda: self._tmdb_show_picker(queue, idx+1))

        def _skip():
            win.destroy()
            self.root.after(50, lambda: self._tmdb_show_picker(queue, idx+1))

        def _skip_all():
            win.destroy()
            if self._tmdb_no_match:
                self.root.after(50, lambda: self._tmdb_ask_title(
                    self._tmdb_no_match, 0))
            else:
                self._tmdb_finish(self._tmdb_ok_count,
                                  len(self._tvdb_file_rows))

        ttk.Button(btn_frame, text="✅  Auswählen",
                   command=_accept).pack(side=tk.LEFT, padx=6)
        ttk.Button(btn_frame, text="Überspringen",
                   command=_skip).pack(side=tk.LEFT, padx=6)
        ttk.Button(btn_frame, text="Alle überspringen",
                   command=_skip_all).pack(side=tk.LEFT, padx=6)

        win.bind("<Return>", lambda _: _accept())
        win.bind("<Escape>", lambda _: _skip())

        # Fenster zentrieren
        win.update_idletasks()
        w, h = win.winfo_width(), win.winfo_height()
        x = self.root.winfo_rootx() + (self.root.winfo_width()  - w) // 2
        y = self.root.winfo_rooty() + (self.root.winfo_height() - h) // 2
        win.geometry(f"+{x}+{y}")

    # ── Titeleingabe bei keinem Treffer ──────────────────────────────────────

    def _tmdb_ask_title(self, queue, idx):
        if idx >= len(queue):
            self._tmdb_finish(self._tmdb_ok_count, len(self._tvdb_file_rows))
            return

        iid, file_row = queue[idx]
        fname       = file_row.get("filename", "")
        year_guess  = file_row.get("year", "")
        fmt         = self.tmdb_fmt_var.get()
        lang        = self.tmdb_lang_var.get()
        client      = self._tmdb_client()

        win = tk.Toplevel(self.root)
        win.title("Filmtitel eingeben")
        win.transient(self.root)
        win.grab_set()
        win.resizable(False, False)

        remaining = len(queue) - idx
        ttk.Label(win, text="Datei:", font=("", 9, "bold")).grid(
            row=0, column=0, sticky=tk.W, padx=12, pady=(12, 0))
        ttk.Label(win, text=fname, wraplength=420,
                  justify=tk.LEFT).grid(
            row=1, column=0, columnspan=2, sticky=tk.W, padx=12, pady=(0, 8))
        ttk.Label(win,
                  text=f"Kein Treffer gefunden. Wie heißt dieser Film?  "
                       f"({remaining} verbleibend)",
                  font=("", 9)).grid(
            row=2, column=0, columnspan=2, sticky=tk.W, padx=12, pady=(0, 4))

        title_var = tk.StringVar(value=file_row.get("title_guess", ""))
        year_var  = tk.StringVar(value=year_guess or "")

        f_title = ttk.Frame(win)
        f_title.grid(row=3, column=0, columnspan=2, sticky=tk.EW, padx=12)
        ttk.Label(f_title, text="Titel:").pack(side=tk.LEFT)
        title_entry = ttk.Entry(f_title, textvariable=title_var, width=38)
        title_entry.pack(side=tk.LEFT, padx=(4, 12))
        ttk.Label(f_title, text="Jahr:").pack(side=tk.LEFT)
        ttk.Entry(f_title, textvariable=year_var, width=6).pack(side=tk.LEFT)

        hint_var = tk.StringVar()
        ttk.Label(win, textvariable=hint_var, foreground="gray",
                  font=("", 8)).grid(
            row=4, column=0, columnspan=2, sticky=tk.W, padx=12, pady=(2, 6))

        title_entry.focus()
        title_entry.select_range(0, tk.END)

        def _search():
            t = title_var.get().strip()
            y = year_var.get().strip() or None
            if not t:
                hint_var.set("Bitte einen Titel eingeben.")
                return
            if not client:
                hint_var.set("Kein TMDB-API-Key eingetragen.")
                return
            hint_var.set("Suche …")
            win.update_idletasks()
            try:
                results = client.search_movies(t, language=lang, year=y)
                if not results and y:
                    results = client.search_movies(t, language=lang)
            except Exception as exc:
                hint_var.set(f"Fehler: {exc}")
                return

            if not results:
                hint_var.set("Immer noch kein Treffer. Anderen Titel versuchen.")
                return

            win.destroy()
            if len(results) == 1:
                upd = self._tmdb_make_update(iid, results[0], fmt, y or year_guess)
                if self.rv_tree.exists(iid):
                    self.rv_tree.item(iid, tags=(upd[4],),
                                      values=(upd[1], upd[2], upd[3]))
                    self._tmdb_ok_count += 1
                self.root.after(50, lambda: self._tmdb_ask_title(queue, idx + 1))
            else:
                single_queue = [(iid, file_row, results, fmt, client)]
                self._tmdb_no_match = queue[idx + 1:]
                self.root.after(50, lambda: self._tmdb_show_picker(
                    single_queue, 0))

        def _skip():
            win.destroy()
            self.root.after(50, lambda: self._tmdb_ask_title(queue, idx + 1))

        def _skip_all():
            win.destroy()
            self._tmdb_finish(self._tmdb_ok_count, len(self._tvdb_file_rows))

        btn = ttk.Frame(win)
        btn.grid(row=5, column=0, columnspan=2, pady=(0, 12))
        ttk.Button(btn, text="Suchen", command=_search).pack(
            side=tk.LEFT, padx=6)
        ttk.Button(btn, text="Überspringen", command=_skip).pack(
            side=tk.LEFT, padx=6)
        ttk.Button(btn, text="Alle überspringen", command=_skip_all).pack(
            side=tk.LEFT, padx=6)

        win.bind("<Return>", lambda _: _search())
        win.bind("<Escape>", lambda _: _skip())

        win.update_idletasks()
        w = win.winfo_width()
        h = win.winfo_height()
        x = self.root.winfo_rootx() + (self.root.winfo_width()  - w) // 2
        y = self.root.winfo_rooty() + (self.root.winfo_height() - h) // 2
        win.geometry(f"+{x}+{y}")

    def _tmdb_apply_updates(self, updates):
        # Rückwärtskompatibel – wird von anderen Stellen noch gerufen
        ok = 0
        for iid, new_name, film_title, status, tag in updates:
            if self.rv_tree.exists(iid):
                self.rv_tree.item(iid, tags=(tag,),
                                  values=(new_name, film_title, status))
                if tag == "ok_movie":
                    ok += 1
        self.tmdb_match_btn.configure(state=tk.NORMAL)
        total = len(self._tvdb_file_rows)
        self.tmdb_status_var.set(f"✓ {ok} von {total} gefunden.")
        if ok:
            self.tvdb_apply_btn.configure(state=tk.NORMAL)
            self.tvdb_apply_all_btn.configure(state=tk.NORMAL)

    # ═══════════════════════════════════════════════════════════════════════════

    def _start_search(self):
        self.search_btn.state(["disabled"])
        self.status_var.set("Suche läuft …")
        threading.Thread(target=self._search_thread, daemon=True).start()

    def _search_thread(self):
        queries = []
        topic   = self.topic_var.get().strip()
        title   = self.title_var.get().strip()
        channel = self.channel_var.get()
        if topic:   queries.append({"fields": ["topic"],   "query": topic})
        if title:   queries.append({"fields": ["title"],   "query": title})
        if channel != "Alle":
            queries.append({"fields": ["channel"], "query": channel})
        if not queries:
            self.root.after(0, lambda: messagebox.showwarning(
                "Hinweis", "Bitte mindestens ein Suchkriterium eingeben."))
            self.root.after(0, lambda: self.search_btn.state(["!disabled"]))
            return
        payload = {"queries": queries, "sortBy": "timestamp",
                   "sortOrder": "desc", "future": False,
                   "offset": 0, "size": self.size_var.get()}
        try:
            resp = requests.post(API_URL, json=payload,
                                 headers={"Content-Type": "text/plain"}, timeout=20)
            resp.raise_for_status()
            self.results = resp.json().get("result", {}).get("results", [])
            self.root.after(0, self._populate_results)
        except Exception as exc:
            self.root.after(0, lambda e=exc: messagebox.showerror("Fehler", str(e)))
            self.root.after(0, lambda: self.status_var.set("Fehler bei der Suche."))
        finally:
            self.root.after(0, lambda: self.search_btn.state(["!disabled"]))

    def _duration_limits(self):
        def _p(v):
            s = v.get().strip()
            return int(s) * 60 if s.isdigit() else None
        return _p(self.dur_min_var), _p(self.dur_max_var)

    def _populate_results(self):
        self.tree.delete(*self.tree.get_children())
        self._iid_to_item.clear()
        self._wl_checked.clear()
        self._probe_cancel = True
        self.probe_status_var.set("")
        folder = self.folder_var.get()
        dur_min, dur_max = self._duration_limits()
        series_fmt = self.series_fmt_var.get()

        seen: dict = {}
        for item in self.results:
            k = (item.get("topic","").strip().lower(), item.get("title","").strip().lower())
            seen[k] = seen.get(k, 0) + 1
        dup_keys = {k for k, v in seen.items() if v > 1}

        _ACCESS_TERMS = ("hörgeschädigte", "gebärdensprache", "hörfassung", "audiodeskription")
        filter_access = self.filter_access_var.get()
        lang          = self.language_var.get()

        results_filtered = _apply_language_filter(self.results, lang)

        shown = dup_count = 0
        n_dur = n_access = 0          # getrennt zählen, damit erkennbar ist
        n_lang = len(self.results) - len(results_filtered)   # WARUM nichts kommt
        for item in results_filtered:
            dur = item.get("duration", 0) or 0
            if dur_min is not None and dur < dur_min: n_dur += 1; continue
            if dur_max is not None and dur > dur_max: n_dur += 1; continue
            if filter_access:
                tit_low = item.get("title", "").lower()
                top_low = item.get("topic", "").lower()
                if any(t in tit_low or t in top_low for t in _ACCESS_TERMS):
                    n_access += 1; continue

            ts  = item.get("timestamp", 0)
            ch  = item.get("channel", "")
            top = item.get("topic",   "")
            tit = item.get("title",   "")
            k   = (top.strip().lower(), tit.strip().lower())

            # Stufe 1: beide Format-Varianten prüfen
            exists = any(
                os.path.isfile(_build_filepath(folder, top, tit, ts, f)[1])
                for f in (series_fmt, not series_fmt)
            )
            is_dup = k in dup_keys

            tag = ("duplicate" if is_dup else "exists" if exists else "")
            if is_dup: dup_count += 1

            res = "HD  (?)" if item.get("url_video_hd") else "—"
            iid = self.tree.insert("", tk.END, tags=(tag,), values=(
                "☐",
                ch, top, tit,
                datetime.fromtimestamp(ts).strftime("%d.%m.%Y") if ts else "",
                f"{dur//60}:{dur%60:02d}" if dur else "",
                res
            ))
            self._iid_to_item[iid] = item
            shown += 1

        parts = [f"{shown} Ergebnisse"]
        # Jeden Filter einzeln ausweisen – sonst ist bei 0 Ergebnissen nicht
        # erkennbar, ob die Suche nichts fand oder ein Filter alles entfernt hat
        if n_dur:    parts.append(f"{n_dur} durch Dauer-Filter")
        if n_access: parts.append(f"{n_access} durch Barrierefrei-Filter")
        if n_lang:   parts.append(f"{n_lang} durch Sprach-Filter")
        if dup_count: parts.append(f"{dup_count} Duplikate (gelb)")

        if shown == 0:
            if not self.results:
                parts.append("→ Suche lieferte nichts. "
                             "Sendung/Titel und Sender prüfen "
                             "(Titel-Feld leer lassen, wenn unsicher)")
            elif n_dur or n_access or n_lang:
                parts.append("→ alle Treffer wurden von Filtern entfernt")
        self.status_var.set("  |  ".join(parts))
        has_fp = bool(self._ffprobe_path_var.get().strip())
        self.probe_btn.configure(state=tk.NORMAL if (shown and has_fp) else tk.DISABLED)

    def _tree_click(self, event):
        """Klick auf die ☐/☑-Spalte toggelt den Watchlist-Haken."""
        region = self.tree.identify_region(event.x, event.y)
        if region != "cell":
            return
        col = self.tree.identify_column(event.x)
        if col != "#1":   # Spalte 1 = wl
            return
        iid = self.tree.identify_row(event.y)
        if not iid:
            return
        if iid in self._wl_checked:
            self._wl_checked.discard(iid)
            vals = list(self.tree.item(iid, "values"))
            vals[0] = "☐"
        else:
            self._wl_checked.add(iid)
            vals = list(self.tree.item(iid, "values"))
            vals[0] = "☑"
        self.tree.item(iid, values=vals)

    def _add_checked_to_watchlist(self):
        """Fügt alle ☑-markierten Sendungen zur Watchlist hinzu."""
        if not self._wl_checked:
            messagebox.showinfo("Watchlist",
                "Bitte erst Sendungen mit ☐ markieren (Klick auf die Checkbox-Spalte).")
            return
        added = 0
        existing_topics = {e["topic"].lower() for e in self._watchlist.get("entries", [])}
        for iid in list(self._wl_checked):
            item = self._iid_to_item.get(iid)
            if not item:
                continue
            topic = item.get("topic", "").strip()
            ch    = item.get("channel", "Alle")
            if not topic or topic.lower() in existing_topics:
                continue
            entry = {
                "id":             hashlib.md5(f"{ch}|{topic}".encode()).hexdigest()[:12],
                "topic":          topic,
                "channel":        ch,
                "title_filter":   "",
                "quality":        self.quality_var.get(),
                "dur_min":        "",
                "dur_max":        "",
                "filter_access":  True,
                "subtitles":      True,
                "series_fmt":     False,
                "downloaded_ids": [],
                "last_checked":   "",
            }
            self._watchlist.setdefault("entries", []).append(entry)
            existing_topics.add(topic.lower())
            added += 1
        if added:
            self._save_watchlist()
            self._populate_watchlist_tree()
            self.notebook.select(self.tab_watchlist)
            messagebox.showinfo("Watchlist", f"{added} Sendung(en) zur Watchlist hinzugefügt.")
        else:
            messagebox.showinfo("Watchlist",
                "Alle markierten Sendungen sind bereits in der Watchlist.")

    def _add_search_to_watchlist(self):
        """Fügt das eingegebene Thema mit allen aktuellen Einstellungen zur Watchlist hinzu."""
        topic = self.topic_var.get().strip()
        if not topic:
            messagebox.showwarning("Watchlist",
                "Bitte zuerst ein Sendung / Thema in das Suchfeld eingeben.")
            return
        ch = self.channel_var.get()
        existing_topics = {e["topic"].lower() for e in self._watchlist.get("entries", [])}
        if topic.lower() in existing_topics:
            messagebox.showinfo("Watchlist",
                f'"{topic}" ist bereits in der Watchlist.')
            return
        entry = {
            "id":             hashlib.md5(f"{ch}|{topic}".encode()).hexdigest()[:12],
            "topic":          topic,
            "channel":        ch,
            "title_filter":   self.title_var.get().strip(),
            "quality":        self.quality_var.get(),
            "dur_min":        self.dur_min_var.get().strip(),
            "dur_max":        self.dur_max_var.get().strip(),
            "filter_access":  self.filter_access_var.get(),
            "subtitles":      self.subtitles_var.get(),
            "series_fmt":     self.series_fmt_var.get(),
            "language":       self.language_var.get(),
            "downloaded_ids": [],
            "last_checked":   "",
        }
        self._watchlist.setdefault("entries", []).append(entry)
        self._save_watchlist()
        self._populate_watchlist_tree()
        self.notebook.select(self.tab_watchlist)
        messagebox.showinfo("Watchlist", f'"{topic}" zur Watchlist hinzugefügt.')

    # ═══════════════════════════════════════════════════════════════════════════
    # Auflösungs-Probe
    # ═══════════════════════════════════════════════════════════════════════════

    def _browse_ffprobe(self):
        path = filedialog.askopenfilename(
            title="ffprobe.exe auswählen",
            filetypes=[("ffprobe", "ffprobe.exe"), ("Alle", "*.*")])
        if path:
            self._ffprobe_path_var.set(path)
            self._ffprobe = path
            if self._iid_to_item:
                self.probe_btn.configure(state=tk.NORMAL)

    def _start_probe(self):
        items_to_probe = list(self._iid_to_item.items())
        if not items_to_probe: return
        self._probe_cancel = False
        self.probe_btn.configure(state=tk.DISABLED)
        self.probe_status_var.set(f"0 / {len(items_to_probe)} geprüft …")
        threading.Thread(target=self._probe_thread, args=(items_to_probe,), daemon=True).start()

    def _probe_thread(self, items_to_probe):
        ffprobe  = self._ffprobe_path_var.get().strip() or "ffprobe"
        total    = len(items_to_probe)
        done_cnt = 0

        def probe_one(args):
            iid, item = args
            if self._probe_cancel: return iid, None
            url = (item.get("url_video_hd") or item.get("url_video") or item.get("url_video_sd"))
            return iid, (_probe_resolution(url, ffprobe) or "unbekannt") if url else (iid, "—")

        with ThreadPoolExecutor(max_workers=4) as pool:
            for iid, resolution in pool.map(probe_one, items_to_probe):
                if self._probe_cancel: break
                done_cnt += 1
                res_text  = resolution or "—"
                def _update(i=iid, r=res_text, n=done_cnt):
                    if not self.tree.exists(i): return
                    vals = list(self.tree.item(i, "values"))
                    vals[5] = r
                    self.tree.item(i, values=vals)
                    self.probe_status_var.set(
                        f"{n} / {total} geprüft …" if n < total else f"✓ {total} geprüft")
                self.root.after(0, _update)
        self.root.after(0, lambda: self.probe_btn.configure(state=tk.NORMAL))

    # ═══════════════════════════════════════════════════════════════════════════
    # Download
    # ═══════════════════════════════════════════════════════════════════════════

    def _select_all(self):
        self.tree.selection_set(self.tree.get_children())

    def _choose_folder(self):
        folder = filedialog.askdirectory(initialdir=self.folder_var.get())
        if folder: self.folder_var.set(folder)

    def _start_download(self, items=None, quality=None, folder=None,
                        skip_dupes=None, exist_action=None,
                        subtitles=None, series_fmt=None,
                        on_done=None, seen_hashes=None):
        """Startet Download. Ohne Argumente: benutzt UI-Auswahl."""
        if items is None:
            selected = self.tree.selection()
            if not selected:
                messagebox.showinfo("Hinweis",
                    "Bitte zuerst Einträge auswählen\n(oder 'Alle auswählen').")
                return
            indices = [self.tree.index(iid) for iid in selected]
            items   = [self.results[i] for i in indices if i < len(self.results)]

        if not items: return

        quality       = quality       or self.quality_var.get()
        folder        = folder        or self.folder_var.get()
        skip_dupes    = skip_dupes    if skip_dupes    is not None else self.skip_dupes_var.get()
        exist_action  = exist_action  if exist_action  is not None else self.exist_action_var.get()
        subtitles     = subtitles     if subtitles     is not None else self.subtitles_var.get()
        series_fmt    = series_fmt    if series_fmt    is not None else self.series_fmt_var.get()

        self.notebook.select(self.tab_dl)

        job_list = []
        for item in items:
            iid = self.dl_tree.insert("", tk.END, tags=("st_wait",), values=(
                STATUS_ICON["waiting"], item.get("topic", ""), item.get("title", ""),
                item.get("channel", ""), _bar(0), "—", ""))
            job = {"iid": iid, "item": item, "status": "waiting", "done": 0, "total": 0,
                   "_cancel": False}
            self._dl_jobs[iid] = job
            job_list.append(job)

        self._update_dl_summary()

        batch = (job_list, folder, quality, skip_dupes, exist_action,
                 subtitles, series_fmt, on_done, seen_hashes)

        if self._active_dl_threads > 0:
            # Noch ein Download läuft → einreihen, nicht sofort starten
            self._dl_queue.append(batch)
            queued_items = sum(len(b[0]) for b in self._dl_queue)
            self.status_var.set(
                f"{queued_items} Datei(en) warten bis der laufende Download fertig ist …")
            return

        self._cancel_flag = False
        self._pause_event.set()
        self._active_dl_threads += 1
        self.cancel_btn.configure(state=tk.NORMAL)
        self.pause_btn.configure(state=tk.NORMAL, text="⏸ Pause")
        self.total_progress.configure(value=0)
        threading.Thread(target=self._download_thread, args=batch, daemon=True).start()

    def _download_thread(self, job_list, folder, quality, skip_dupes, exist_action,
                         subtitles, series_fmt, on_done=None, seen_hashes=None):
        # Gemeinsame Deque – UI kann Reihenfolge zur Laufzeit ändern
        self._dl_remaining = collections.deque(job_list)
        seen_titles:  set = set()
        total_jobs    = len(job_list)
        finished      = 0
        newly_done    = []

        os.makedirs(folder, exist_ok=True)

        while self._dl_remaining:
            job = self._dl_remaining.popleft()
            if self._cancel_flag or job.get("_cancel"):
                self._set_job_status(job, "skipped", note="Abgebrochen")
                finished += 1; continue

            item = job["item"]
            tit  = item.get("title",   "unbekannt")
            top  = item.get("topic",   "")
            ts   = item.get("timestamp", 0)

            dedup_key = (top.strip().lower(), tit.strip().lower())
            if skip_dupes and dedup_key in seen_titles:
                self._set_job_status(job, "skipped", note="Duplikat")
                finished += 1; self._update_total_progress(finished, total_jobs); continue
            seen_titles.add(dedup_key)

            url = _pick_url(item, quality)
            if not url:
                self._set_job_status(job, "error", note="Kein Stream")
                finished += 1; self._update_total_progress(finished, total_jobs); continue
            job["_url"] = url

            item_series_fmt = item.get("_wl_series_fmt", series_fmt) if series_fmt is None else series_fmt
            if item_series_fmt is None: item_series_fmt = False
            subdir, filepath = _build_filepath(folder, top, tit, ts, item_series_fmt)
            os.makedirs(subdir, exist_ok=True)
            job["_filepath"]  = filepath
            item_subtitles_resolved = item.get("_wl_subtitles", subtitles) if subtitles is None else subtitles
            if item_subtitles_resolved is None: item_subtitles_resolved = True
            job["_subtitles"] = item_subtitles_resolved

            action = item.get("_wl_exist_action") or exist_action or "skip"
            if os.path.isfile(filepath):
                if action == "skip":
                    self._set_job_status(job, "skipped", note="Vorhanden")
                    # Datei existiert → als bekannt markieren damit der nächste
                    # Check sie nicht erneut einreiht und die Zählung stimmt
                    if item.get("_wl_entry_id"):
                        item["_skipped_existing"] = True
                        newly_done.append(item)
                    finished += 1; self._update_total_progress(finished, total_jobs); continue
                elif action == "size":
                    local_sz  = os.path.getsize(filepath)
                    remote_sz = self._head_size(url)
                    if remote_sz > 0 and local_sz == remote_sz:
                        self._set_job_status(job, "skipped",
                                             note=f"Vorhanden ({_fmt_size(local_sz)} = Server)")
                        if item.get("_wl_entry_id"):
                            item["_skipped_existing"] = True
                            newly_done.append(item)
                        finished += 1; self._update_total_progress(finished, total_jobs); continue
                    # Größen unterschiedlich → alte Datei löschen, komplett neu laden
                    # (Resume wäre falsch: könnte andere Qualitätsstufe oder andere Version sein)
                    try:
                        os.remove(filepath)
                    except OSError:
                        pass

            # Watchlist-Hash-Check (Folge schon bekannt?)
            if seen_hashes is not None and _item_hash(item) in seen_hashes:
                self._set_job_status(job, "skipped", note="Bereits bekannt")
                finished += 1; self._update_total_progress(finished, total_jobs); continue

            self._set_job_status(job, "downloading")
            ok = self._download_file(job, url, filepath)

            if ok:
                self._set_job_status(job, "done")
                h = _item_hash(item)
                if h not in self._dl_known_hashes:
                    self._dl_known_hashes.add(h)
                    self._dl_known_filenames.add(os.path.basename(filepath))
                    self._append_dl_hash(h, filepath)
                item["_downloaded_filepath"] = filepath
                newly_done.append(item)
                _write_sidecar(filepath, h)

                # Untertitel
                item_subtitles = job["_subtitles"]
                if item_subtitles:
                    sub_url = item.get("url_subtitle", "")
                    if sub_url:
                        ext      = os.path.splitext(sub_url.split("?")[0])[1] or ".srt"
                        sub_path = os.path.splitext(filepath)[0] + ext
                        try:
                            urllib.request.urlretrieve(sub_url, sub_path)
                        except Exception:
                            pass

            finished += 1
            self._update_total_progress(finished, total_jobs)

        self.root.after(0, self._download_all_done)
        if on_done:
            self.root.after(0, lambda: on_done(newly_done))

    def _head_size(self, url):
        try:
            req = urllib.request.Request(url, method="HEAD",
                                         headers={"User-Agent": "Mozilla/5.0"})
            with urllib.request.urlopen(req, timeout=10) as r:
                return int(r.headers.get("Content-Length", -1))
        except Exception:
            return -1

    def _get_max_bps(self):
        if self._watchlist.get("time_limit_enabled"):
            try:
                now = datetime.now()
                h   = now.hour + now.minute / 60.0
                s_h, s_m = map(int, self._watchlist.get("time_limit_day_start", "06:00").split(":"))
                e_h, e_m = map(int, self._watchlist.get("time_limit_day_end",   "22:00").split(":"))
                day_start = s_h + s_m / 60.0
                day_end   = e_h + e_m / 60.0
                in_daytime = (day_start <= h < day_end) if day_start < day_end \
                             else not (day_end <= h < day_start)
                if in_daytime:
                    kbps = int(self._watchlist.get("time_limit_day_kbps", 500) or 500)
                    return max(1, kbps) * 1024
            except (ValueError, AttributeError):
                pass
        try:
            kbps = max(0, int(self._watchlist.get("speed_limit_kbps", 0) or 0))
            return kbps * 1024 if kbps > 0 else 0
        except (ValueError, TypeError):
            return 0

    def _download_file(self, job, url, filepath):
        MAX_RETRIES  = 6
        RETRY_DELAY  = 3
        chunk_size   = 65536
        last_exc     = None

        def _is_cancelled():
            return self._cancel_flag or job.get("_cancel", False)

        for attempt in range(MAX_RETRIES):
            if _is_cancelled():
                self._set_job_status(job, "skipped", note="Abgebrochen")
                return False

            # Pause abwarten bevor (erneutem) Verbindungsaufbau
            while not self._pause_event.is_set():
                if _is_cancelled():
                    self._set_job_status(job, "skipped", note="Abgebrochen")
                    return False
                time.sleep(0.2)

            # Fortsetzen ab bereits heruntergeladenem Teil
            resume_pos = 0
            mode       = "wb"
            headers    = {"User-Agent": "Mozilla/5.0"}
            if os.path.isfile(filepath):
                resume_pos = os.path.getsize(filepath)
                if resume_pos > 0:
                    headers["Range"] = f"bytes={resume_pos}-"
                    mode = "ab"

            if attempt > 0:
                self._set_job_status(job, "waiting",
                                     note=f"Verbinde neu … ({attempt + 1}/{MAX_RETRIES})")

            try:
                req = urllib.request.Request(url, headers=headers)
                with urllib.request.urlopen(req, timeout=30) as response:
                    status = response.status
                    if status == 200 and resume_pos > 0:
                        # Server ignoriert Range → von vorne
                        resume_pos = 0
                        mode       = "wb"

                    total = int(response.headers.get("Content-Length", 0))
                    if status == 206:
                        total += resume_pos

                    # Ersten bekannten Gesamtwert merken – bleibt über alle Retry-Versuche erhalten,
                    # damit spätere Verbindungen ohne Content-Length trotzdem geprüft werden können.
                    if total > 0 and not job.get("_known_total"):
                        job["_known_total"] = total

                    job["total"]  = total or job.get("_known_total", 0)
                    job["status"] = "downloading"
                    job["note"]   = ""
                    done          = resume_pos
                    t_last        = time.time()
                    bytes_last    = done
                    chunk_t0      = t_last

                    with open(filepath, mode) as f:
                        while True:
                            if _is_cancelled():
                                self._set_job_status(job, "skipped", note="Abgebrochen")
                                return False
                            while not self._pause_event.is_set():
                                if _is_cancelled():
                                    self._set_job_status(job, "skipped", note="Abgebrochen")
                                    return False
                                time.sleep(0.2)
                            chunk = response.read(chunk_size)
                            if not chunk:
                                break
                            f.write(chunk)
                            done += len(chunk)
                            job["done"] = done
                            max_bps = self._get_max_bps()
                            if max_bps > 0:
                                elapsed_c  = time.time() - chunk_t0
                                expected_c = len(chunk) / max_bps
                                if elapsed_c < expected_c:
                                    time.sleep(expected_c - elapsed_c)
                            chunk_t0 = time.time()
                            now     = time.time()
                            elapsed = now - t_last
                            if elapsed >= 0.4:
                                speed      = (done - bytes_last) / elapsed
                                bytes_last = done
                                t_last     = now
                                pct = (done / total * 100) if total else 0
                                self.root.after(0, self._refresh_job_row,
                                                job, pct, done, total, speed)

                # Vollständigkeits-Check: tatsächliche Dateigröße vs. besten bekannten Wert
                actual      = os.path.getsize(filepath) if os.path.isfile(filepath) else done
                known_total = job.get("_known_total", 0)
                check_total = known_total or total   # nimm den besten bekannten Wert
                if check_total > 0 and actual < check_total:
                    raise Exception(
                        f"Unvollständig: {_fmt_size(actual)} von {_fmt_size(check_total)} "
                        f"({actual * 100 // check_total} %) – wird fortgesetzt")
                return True

            except Exception as exc:
                last_exc = exc
                if _is_cancelled():
                    self._set_job_status(job, "skipped", note="Abgebrochen")
                    return False
                # Bei HTTP 404 auf einen Resume-Versuch (Range-Request):
                # Manche Server unterstützen kein Byte-Range → Teildatei löschen,
                # nächster Versuch startet komplett neu von vorne.
                if (isinstance(exc, urllib.error.HTTPError) and exc.code == 404
                        and resume_pos > 0):
                    try:
                        if os.path.isfile(filepath):
                            os.remove(filepath)
                    except OSError:
                        pass
                    self._set_job_status(job, "waiting", note="404 bei Resume – starte neu …")
                # Bei Verbindungsabbruch während eines Resumes ebenfalls neu starten.
                elif (resume_pos > 0 and "RemoteDisconnected" in type(exc).__name__):
                    try:
                        if os.path.isfile(filepath):
                            os.remove(filepath)
                    except OSError:
                        pass
                    self._set_job_status(job, "waiting",
                                         note="Verbindungsabbruch beim Resume – starte neu …")
                if attempt < MAX_RETRIES - 1:
                    # Kurz warten, dann erneut versuchen
                    for _ in range(RETRY_DELAY * 5):
                        if _is_cancelled():
                            self._set_job_status(job, "skipped", note="Abgebrochen")
                            return False
                        time.sleep(0.2)

        self._set_job_status(job, "error", note=str(last_exc)[:80])
        return False

    # ── Download-Tab Hilfsmethoden ─────────────────────────────────────────────

    def _set_job_status(self, job, status, note=""):
        job["status"] = status
        iid  = job["iid"]
        icon = STATUS_ICON[status] + (f" ({note})" if note else "")
        tag  = STATUS_TAG[status]
        done  = job.get("done",  0)
        total = job.get("total", 0)
        pct   = (done / total * 100) if total else (100 if status == "done" else 0)
        self.root.after(0, lambda:
            self.dl_tree.item(iid, tags=(tag,), values=(
                icon,
                job["item"].get("topic",   ""),
                job["item"].get("title",   ""),
                job["item"].get("channel", ""),
                _bar(pct),
                f"{_fmt_size(done)} / {_fmt_size(total)}" if total else _fmt_size(done),
                ""
            )) if self.dl_tree.exists(iid) else None)
        self.root.after(0, self._update_dl_summary)

    def _refresh_job_row(self, job, pct, done, total, speed):
        iid = job["iid"]
        if not self.dl_tree.exists(iid): return
        # ETA berechnen und an Geschwindigkeit anhängen
        speed_str = _fmt_speed(speed)
        if speed > 0 and total > done > 0:
            eta = _fmt_eta((total - done) / speed)
            if eta:
                speed_str += f"  {eta}"
        self.dl_tree.item(iid, tags=("st_dl",), values=(
            STATUS_ICON["downloading"],
            job["item"].get("topic",   ""),
            job["item"].get("title",   ""),
            job["item"].get("channel", ""),
            _bar(pct),
            f"{_fmt_size(done)} / {_fmt_size(total)}" if total else _fmt_size(done),
            speed_str
        ))

    def _update_total_progress(self, finished, total):
        pct = int(finished / total * 100) if total else 0
        self.root.after(0, lambda:
            (self.total_progress.configure(value=pct),
             self.total_pct_var.set(f"{pct} %")))

    def _update_dl_summary(self):
        counts = {}
        for job in self._dl_jobs.values():
            counts[job["status"]] = counts.get(job["status"], 0) + 1
        parts = []
        if counts.get("downloading"): parts.append(f"⬇ {counts['downloading']} läuft")
        if counts.get("waiting"):     parts.append(f"⏳ {counts['waiting']} wartend")
        if counts.get("done"):        parts.append(f"✓ {counts['done']} fertig")
        if counts.get("error"):       parts.append(f"✗ {counts['error']} Fehler")
        if counts.get("skipped"):     parts.append(f"⏭ {counts['skipped']} übersprungen")
        self.dl_summary_var.set("  |  ".join(parts) if parts else "Keine Downloads.")
        active = counts.get("downloading", 0) + counts.get("waiting", 0)
        self.notebook.tab(self.tab_dl,
            text=f"  ⬇ Downloads ({active})  " if active else "  ⬇ Downloads  ")

    def _download_all_done(self):
        self._active_dl_threads = max(0, self._active_dl_threads - 1)
        if self._active_dl_threads == 0 and self._dl_queue:
            # Nächsten Batch aus der Warteschlange starten
            next_batch = self._dl_queue.pop(0)
            self._cancel_flag = False
            self._pause_event.set()
            self._active_dl_threads += 1
            self.total_progress.configure(value=0)
            if next_batch[1] == "_retry_":
                # Retry-Batch (kein normaler Download-Batch)
                threading.Thread(target=self._retry_thread,
                                 args=(next_batch[0],), daemon=True).start()
            else:
                threading.Thread(target=self._download_thread,
                                 args=next_batch, daemon=True).start()
            remaining = sum(len(b[0]) for b in self._dl_queue)
            self.status_var.set(
                f"Nächster Batch startet … ({remaining} weitere Datei(en) noch in Warteschlange)"
                if remaining else "Nächster Batch startet …")
            return
        if self._active_dl_threads == 0:
            self._pause_event.set()
            self.cancel_btn.configure(state=tk.DISABLED)
            self.pause_btn.configure(state=tk.DISABLED, text="⏸ Pause")
        self._update_dl_summary()
        counts = {}
        for job in self._dl_jobs.values():
            counts[job["status"]] = counts.get(job["status"], 0) + 1
        parts = []
        if counts.get("done"):    parts.append(f"{counts['done']} heruntergeladen")
        if counts.get("skipped"): parts.append(f"{counts['skipped']} übersprungen")
        if counts.get("error"):   parts.append(f"{counts['error']} Fehler")
        self.status_var.set("Fertig  –  " + "  |  ".join(parts))

    def _toggle_pause(self):
        if self._pause_event.is_set():
            self._pause_event.clear()
            self.pause_btn.configure(text="▶ Weiter")
            self.status_var.set("Pausiert.")
        else:
            self._pause_event.set()
            self.pause_btn.configure(text="⏸ Pause")
            self.status_var.set("Läuft …")

    def _cancel_downloads(self):
        self._cancel_flag = True
        self._dl_queue.clear()   # wartende Batches verwerfen
        self._pause_event.set()  # aus Pause heraus abbrechen ermöglichen
        self.cancel_btn.configure(state=tk.DISABLED)
        self.pause_btn.configure(state=tk.DISABLED, text="⏸ Pause")
        self.status_var.set("Abbrechen …")

    def _clear_done(self):
        to_remove = [iid for iid, job in self._dl_jobs.items()
                     if job["status"] in ("done", "skipped", "error")]
        for iid in to_remove:
            if self.dl_tree.exists(iid): self.dl_tree.delete(iid)
            del self._dl_jobs[iid]
        self._update_dl_summary()

    def _clear_all_jobs(self):
        if any(j["status"] == "downloading" for j in self._dl_jobs.values()):
            if not messagebox.askyesno("Löschen?",
                                       "Es laufen noch Downloads. Trotzdem löschen?"):
                return
        self._dl_queue.clear()
        self.dl_tree.delete(*self.dl_tree.get_children())
        self._dl_jobs.clear()
        self.total_progress.configure(value=0)
        self.total_pct_var.set("")
        self._update_dl_summary()

    def _show_dl_ctx_menu(self, event):
        iid = self.dl_tree.identify_row(event.y)
        if iid:
            if iid not in self.dl_tree.selection():
                self.dl_tree.selection_set(iid)
            self._dl_ctx_menu.post(event.x_root, event.y_root)

    def _remove_selected_jobs(self):
        for iid in list(self.dl_tree.selection()):
            if iid in self._dl_jobs and self._dl_jobs[iid]["status"] == "downloading":
                continue   # laufende nicht entfernen
            if self.dl_tree.exists(iid):
                self.dl_tree.delete(iid)
            self._dl_jobs.pop(iid, None)
        self._update_dl_summary()

    def _sync_remaining_to_tree(self):
        """Baut _dl_remaining neu auf – in der Reihenfolge wie der Baum sie zeigt.
        So spielt es keine Rolle ob gerade laufende Jobs den Deque-Index verschieben."""
        in_remaining = {j["iid"] for j in self._dl_remaining}
        self._dl_remaining = collections.deque(
            self._dl_jobs[iid]
            for iid in self.dl_tree.get_children()
            if iid in self._dl_jobs and iid in in_remaining
        )

    def _move_selected_up(self):
        """Verschiebt den ausgewählten wartenden Eintrag eine Position nach oben."""
        sel = self.dl_tree.selection()
        if not sel:
            self.status_var.set("↑ Kein Eintrag ausgewählt")
            return
        iid = sel[0]
        status = self._dl_jobs.get(iid, {}).get("status", "?")
        if status != "waiting":
            self.status_var.set(f"↑ Nur wartende Einträge verschiebbar (aktuell: {status})")
            return
        all_iids = list(self.dl_tree.get_children())
        idx = all_iids.index(iid)
        if idx == 0:
            self.status_var.set("↑ Bereits an erster Stelle")
            return
        self.dl_tree.move(iid, "", idx - 1)
        self._sync_remaining_to_tree()
        self.dl_tree.selection_set(iid)
        self.dl_tree.see(iid)
        self.status_var.set(f"↑ Position {idx+1} → {idx}  (Warteschlange: {len(self._dl_remaining)} Jobs)")

    def _move_selected_down(self):
        """Verschiebt den ausgewählten wartenden Eintrag eine Position nach unten."""
        sel = self.dl_tree.selection()
        if not sel:
            self.status_var.set("↓ Kein Eintrag ausgewählt")
            return
        iid = sel[-1]
        status = self._dl_jobs.get(iid, {}).get("status", "?")
        if status != "waiting":
            self.status_var.set(f"↓ Nur wartende Einträge verschiebbar (aktuell: {status})")
            return
        all_iids = list(self.dl_tree.get_children())
        idx = all_iids.index(iid)
        if idx >= len(all_iids) - 1:
            self.status_var.set("↓ Bereits an letzter Stelle")
            return
        self.dl_tree.move(iid, "", idx + 1)
        self._sync_remaining_to_tree()
        self.dl_tree.selection_set(iid)
        self.dl_tree.see(iid)
        self.status_var.set(f"↓ Position {idx+1} → {idx+2}  (Warteschlange: {len(self._dl_remaining)} Jobs)")

    def _cancel_selected_jobs(self):
        """Stoppt die ausgewählten Downloads (wartend → sofort; laufend → nach aktuellem Chunk)."""
        changed = 0
        for iid in list(self.dl_tree.selection()):
            job = self._dl_jobs.get(iid)
            if not job:
                continue
            if job["status"] == "waiting":
                # Noch nicht gestartet → sofort als abgebrochen markieren
                self._set_job_status(job, "skipped", note="Abgebrochen")
                changed += 1
            elif job["status"] == "downloading":
                # Läuft → per Flag beim nächsten Chunk-Check abbrechen
                job["_cancel"] = True
                changed += 1
        if changed:
            self._update_dl_summary()

    def _open_selected_folder(self):
        """Öffnet den Ordner der ausgewählten Datei im Windows-Explorer."""
        for iid in list(self.dl_tree.selection()):
            job = self._dl_jobs.get(iid)
            if not job:
                continue
            fp = job.get("_filepath", "")
            if fp:
                if os.path.isfile(fp):
                    # Datei im Explorer markieren
                    subprocess.Popen(["explorer", "/select,", os.path.normpath(fp)])
                elif os.path.isdir(os.path.dirname(fp)):
                    subprocess.Popen(["explorer", os.path.normpath(os.path.dirname(fp))])
            break  # bei Mehrfachauswahl nur einmal öffnen

    def _cancel_selected_waiting(self):
        """Setzt wartende (noch nicht gestartete) ausgewählte Downloads auf Abgebrochen."""
        changed = 0
        for iid in list(self.dl_tree.selection()):
            job = self._dl_jobs.get(iid)
            if job and job["status"] == "waiting":
                self._set_job_status(job, "skipped", note="Abgebrochen")
                changed += 1
        if changed:
            self._update_dl_summary()

    def _delete_selected_files(self):
        """Löscht die heruntergeladenen Dateien von der HDD und entfernt die Einträge."""
        sel = [iid for iid in self.dl_tree.selection()
               if iid in self._dl_jobs and self._dl_jobs[iid]["status"] != "downloading"]
        if not sel:
            messagebox.showinfo("Hinweis",
                "Keine Einträge ausgewählt (laufende Downloads können nicht gelöscht werden).")
            return
        files_to_del = []
        for iid in sel:
            fp = self._dl_jobs[iid].get("_filepath", "")
            if fp and os.path.isfile(fp):
                files_to_del.append((iid, fp))
        if files_to_del:
            preview = "\n".join(os.path.basename(f) for _, f in files_to_del[:6])
            if len(files_to_del) > 6:
                preview += f"\n… ({len(files_to_del)-6} weitere)"
            if not messagebox.askyesno(
                    "Dateien löschen",
                    f"{len(files_to_del)} Datei(en) wirklich von der HDD löschen?\n\n{preview}"):
                return
            for _, fp in files_to_del:
                try:
                    os.remove(fp)
                except OSError:
                    pass
        # Einträge ohne Datei einfach aus der Liste entfernen (kein Bestätigen nötig)
        for iid in sel:
            if self.dl_tree.exists(iid):
                self.dl_tree.delete(iid)
            self._dl_jobs.pop(iid, None)
        self._update_dl_summary()

    def _restart_selected_jobs(self):
        """Startet ausgewählte Einträge komplett neu – funktioniert für jeden Status
        (Fehler, Übersprungen, Fertig) und löst URL/Pfad frisch auf."""
        sel = [iid for iid in self.dl_tree.selection()
               if iid in self._dl_jobs
               and self._dl_jobs[iid]["status"] != "downloading"]
        if not sel:
            return
        items = [self._dl_jobs[iid]["item"] for iid in sel]
        # Alte Einträge entfernen
        for iid in sel:
            if self.dl_tree.exists(iid):
                self.dl_tree.delete(iid)
            self._dl_jobs.pop(iid, None)
        self._update_dl_summary()
        # Frisch einreihen mit aktuellen UI-Einstellungen
        self._start_download(items=items)

    def _retry_selected_jobs(self):
        iids = [iid for iid in self.dl_tree.selection()
                if iid in self._dl_jobs and self._dl_jobs[iid]["status"] == "error"]
        self._retry_failed_jobs(iids=iids if iids else None)

    def _retry_failed_jobs(self, iids=None):
        if iids is not None:
            jobs = [self._dl_jobs[i] for i in iids if i in self._dl_jobs]
        else:
            jobs = [j for j in self._dl_jobs.values() if j["status"] == "error"]

        retryable = [j for j in jobs if j.get("_url") and j.get("_filepath")]
        if not retryable:
            messagebox.showinfo("Wiederholen",
                "Keine Fehler gefunden, die wiederholt werden können.\n"
                "(Fehler ohne Stream-URL, z. B. 'Kein Stream', können nicht wiederholt werden.)")
            return

        for job in retryable:
            job["done"] = 0
            self._set_job_status(job, "waiting")
        self._update_dl_summary()

        if self._active_dl_threads > 0:
            # Retry als Lambda in die Queue legen (kein regulärer Batch, aber gleiche Mechanik)
            self._dl_queue.append((retryable, "_retry_", None, None, None, None, None, None, None))
            self.status_var.set("Retry wartet bis der laufende Download fertig ist …")
            return

        self._cancel_flag = False
        self._pause_event.set()
        self._active_dl_threads += 1
        self.cancel_btn.configure(state=tk.NORMAL)
        self.pause_btn.configure(state=tk.NORMAL, text="⏸ Pause")
        threading.Thread(target=self._retry_thread, args=(retryable,), daemon=True).start()

    def _retry_thread(self, job_list):
        for job in job_list:
            if self._cancel_flag:
                self._set_job_status(job, "skipped", note="Abgebrochen")
                continue
            url      = job["_url"]
            filepath = job["_filepath"]
            os.makedirs(os.path.dirname(filepath), exist_ok=True)

            self._set_job_status(job, "downloading")
            ok = self._download_file(job, url, filepath)

            if ok:
                self._set_job_status(job, "done")
                _write_sidecar(filepath, _item_hash(job["item"]))
                if job.get("_subtitles"):
                    sub_url = job["item"].get("url_subtitle", "")
                    if sub_url:
                        ext      = os.path.splitext(sub_url.split("?")[0])[1] or ".srt"
                        sub_path = os.path.splitext(filepath)[0] + ext
                        try:
                            urllib.request.urlretrieve(sub_url, sub_path)
                        except Exception:
                            pass

        self.root.after(0, self._download_all_done)

    # ═══════════════════════════════════════════════════════════════════════════
    # Watchlist
    # ═══════════════════════════════════════════════════════════════════════════
    # Zeitplan-Logik
    # ═══════════════════════════════════════════════════════════════════════════

    _WEEKDAY_NAMES = ["Montag", "Dienstag", "Mittwoch",
                      "Donnerstag", "Freitag", "Samstag", "Sonntag"]

    def _scheduler_loop(self):
        """Läuft im Hintergrund, prüft alle 30 Sekunden ob ein Zeitplan fällig ist."""
        while True:
            time.sleep(30)
            now = datetime.now()
            for entry in list(self._watchlist.get("entries", [])):
                sday  = entry.get("schedule_day",  "Deaktiviert")
                stime = entry.get("schedule_time", "").strip()
                if sday == "Deaktiviert" or not stime:
                    continue

                # Passt der Wochentag?
                if sday != "Täglich":
                    if self._WEEKDAY_NAMES[now.weekday()] != sday:
                        continue

                # Mehrere Uhrzeiten kommagetrennt unterstützen (z.B. "08:00, 14:00, 22:00")
                raw_times = [t.strip() for t in stime.split(",") if t.strip()]
                for raw_t in raw_times:
                    try:
                        h, m = map(int, raw_t.split(":"))
                    except ValueError:
                        continue

                    # Ist die Uhrzeit erreicht?
                    sched_dt = now.replace(hour=h, minute=m, second=0, microsecond=0)
                    if now < sched_dt:
                        continue

                    # Wurde seit dieser Planzeit heute schon geprüft?
                    last = entry.get("last_auto_checked", "")
                    if last:
                        try:
                            last_dt = datetime.fromisoformat(last)
                            if last_dt.date() == now.date() and last_dt >= sched_dt:
                                continue   # diesen Slot heute bereits ausgeführt
                        except ValueError:
                            pass

                    # Eintrag als ausgeführt markieren und Check auslösen
                    entry["last_auto_checked"] = now.isoformat(timespec="seconds")
                    self._save_watchlist()
                    self.root.after(0, lambda e=entry: self._run_scheduled_check(e))
                    break  # nur einmal pro Durchlauf auslösen; nächster Slot beim nächsten Tick

    def _run_scheduled_check(self, entry):
        """Prüft einen einzelnen Watchlist-Eintrag (aufgerufen vom Scheduler)."""
        topic = entry.get("topic", "")
        self.wl_status_var.set(f"Zeitplan: pruefe '{topic}' ...")
        self.wl_check_btn.configure(state=tk.DISABLED)
        threading.Thread(
            target=self._watchlist_check_thread,
            args=([entry],), daemon=True).start()

    # ═══════════════════════════════════════════════════════════════════════════

    def _load_watchlist(self):
        if os.path.isfile(WATCHLIST_FILE):
            try:
                with open(WATCHLIST_FILE, encoding="utf-8") as f:
                    return json.load(f)
            except Exception:
                pass
        return {"auto_check_on_start": True, "entries": []}

    def _load_dl_hashes(self):
        """Lädt Hash-Datei: Format hash|/pfad/datei.mp4 – gibt (hashes, filenames) zurück."""
        known_hashes    = set()
        known_filenames = set()
        if not os.path.isfile(HASH_FILE):
            return known_hashes, known_filenames
        try:
            with open(HASH_FILE, encoding="utf-8") as f:
                for line in f:
                    line = line.strip()
                    if not line:
                        continue
                    parts = line.split("|", 1)
                    known_hashes.add(parts[0])
                    if len(parts) > 1 and parts[1]:
                        known_filenames.add(os.path.basename(parts[1]))
        except Exception:
            pass
        return known_hashes, known_filenames

    def _append_dl_hash(self, item_hash, filepath=""):
        try:
            with open(HASH_FILE, "a", encoding="utf-8") as f:
                f.write(f"{item_hash}|{filepath}\n")
        except Exception:
            pass

    def _choose_wl_folder(self):
        folder = filedialog.askdirectory(initialdir=self.wl_folder_var.get())
        if folder:
            self.wl_folder_var.set(folder)
            self._save_watchlist()

    def _save_watchlist(self):
        self._watchlist["auto_check_on_start"] = self.wl_auto_var.get()
        self._watchlist["folder"]              = self.wl_folder_var.get()
        try:
            with open(WATCHLIST_FILE, "w", encoding="utf-8") as f:
                json.dump(self._watchlist, f, ensure_ascii=False, indent=2)
        except Exception as exc:
            messagebox.showerror("Fehler", f"Watchlist konnte nicht gespeichert werden:\n{exc}")

    def _on_wl_entry_select(self, _event=None):
        """Lädt die Einstellungen des gewählten Eintrags in die Optionsfelder."""
        sel = self.wl_tree.selection()
        if not sel:
            return
        entry = next((e for e in self._watchlist.get("entries", [])
                      if e["id"] == sel[0]), None)
        if not entry:
            return
        self._wl_loading = True
        self.wl_filter_access_var.set(entry.get("filter_access", True))
        self.wl_subtitles_var.set(entry.get("subtitles", True))
        self.wl_series_fmt_var.set(entry.get("series_fmt", False))
        self.wl_dur_min_var.set(entry.get("dur_min", ""))
        self.wl_dur_max_var.set(entry.get("dur_max", ""))
        self.wl_lang_var.set(entry.get("language", "Alle"))
        self.wl_sched_day_var.set(entry.get("schedule_day", "Deaktiviert"))
        self.wl_sched_time_var.set(entry.get("schedule_time", ""))
        self.wl_exist_action_var.set(entry.get("exist_action", "skip"))
        self._wl_loading = False

    def _save_wl_entry_settings(self):
        """Speichert die aktuellen Optionsfelder in den ausgewählten Eintrag."""
        if self._wl_loading:
            return
        sel = self.wl_tree.selection()
        if not sel:
            return
        for e in self._watchlist.get("entries", []):
            if e["id"] == sel[0]:
                e["filter_access"] = self.wl_filter_access_var.get()
                e["subtitles"]     = self.wl_subtitles_var.get()
                e["series_fmt"]    = self.wl_series_fmt_var.get()
                e["dur_min"]       = self.wl_dur_min_var.get().strip()
                e["dur_max"]       = self.wl_dur_max_var.get().strip()
                e["language"]      = self.wl_lang_var.get()
                e["schedule_day"]  = self.wl_sched_day_var.get()
                e["schedule_time"] = self.wl_sched_time_var.get().strip()
                e["exist_action"]  = self.wl_exist_action_var.get()
                break
        self._save_watchlist()
        # Tabelle neu aufbauen ohne die Auswahl zu verlieren
        self._populate_watchlist_tree()
        if sel:
            self.wl_tree.selection_set(sel)

    def _populate_watchlist_tree(self):
        self.wl_tree.delete(*self.wl_tree.get_children())
        for entry in self._watchlist.get("entries", []):
            checked = entry.get("last_checked", "—")
            if checked and checked != "—":
                try:
                    checked = datetime.fromisoformat(checked).strftime("%d.%m.%Y %H:%M")
                except Exception:
                    pass
            d_min = entry.get("dur_min", "")
            d_max = entry.get("dur_max", "")
            dur_str = (f"{d_min}–{d_max}" if d_min and d_max
                       else f"≥{d_min}" if d_min
                       else f"≤{d_max}" if d_max
                       else "—")
            sday  = entry.get("schedule_day",  "Deaktiviert")
            stime = entry.get("schedule_time", "").strip()
            if sday == "Deaktiviert" or not stime:
                sched_str = "—"
            elif sday == "Täglich":
                sched_str = f"täglich {stime}"
            else:
                sched_str = f"{sday[:2]}. {stime}"   # z. B. "So. 22:30"
            self.wl_tree.insert("", tk.END, iid=entry["id"], values=(
                entry.get("topic",       ""),
                entry.get("channel",     "Alle"),
                entry.get("title_filter",""),
                entry.get("quality",     "HD"),
                dur_str,
                sched_str,
                checked,
                len(entry.get("downloaded_ids", [])),
            ))

    def _add_watchlist_entry(self):
        topic = self.wl_topic_var.get().strip()
        if not topic:
            messagebox.showwarning("Hinweis", "Bitte Sendung / Thema eingeben.")
            return
        entry = {
            "id":             str(uuid.uuid4())[:8],
            "topic":          topic,
            "channel":        self.wl_channel_var.get(),
            "title_filter":   self.wl_filter_var.get().strip(),
            "quality":        self.wl_quality_var.get(),
            "dur_min":        self.wl_dur_min_var.get().strip(),
            "dur_max":        self.wl_dur_max_var.get().strip(),
            "filter_access":  self.wl_filter_access_var.get(),
            "subtitles":      self.wl_subtitles_var.get(),
            "series_fmt":     self.wl_series_fmt_var.get(),
            "language":       self.wl_lang_var.get(),
            "last_checked":   None,
            "downloaded_ids": [],
        }
        self._watchlist.setdefault("entries", []).append(entry)
        self._save_watchlist()
        self._populate_watchlist_tree()
        self.wl_topic_var.set("")
        self.wl_filter_var.set("")
        self.wl_dur_min_var.set("")
        self.wl_dur_max_var.set("")

    def _remove_watchlist_entries(self):
        selected = self.wl_tree.selection()
        if not selected:
            messagebox.showinfo("Hinweis", "Bitte zuerst Einträge auswählen.")
            return
        ids = set(selected)
        self._watchlist["entries"] = [
            e for e in self._watchlist.get("entries", []) if e["id"] not in ids]
        self._save_watchlist()
        self._populate_watchlist_tree()

    def _reset_all_watchlist_entries(self):
        entries = self._watchlist.get("entries", [])
        if not entries:
            messagebox.showinfo("Hinweis", "Watchlist ist leer.")
            return
        if not messagebox.askyesno(
                "Alle zurücksetzen",
                f"Download-Verlauf ALLER {len(entries)} Einträge löschen?\n"
                "Alle Folgen werden beim nächsten Check erneut heruntergeladen."):
            return
        for e in entries:
            e["downloaded_ids"] = []
            e["reset_pending"]  = True
        self._save_watchlist()
        self._populate_watchlist_tree()
        self.wl_status_var.set(f"Verlauf aller {len(entries)} Einträge bereinigt.")

    def _reset_watchlist_entries(self):
        selected = self.wl_tree.selection()
        if not selected:
            messagebox.showinfo("Hinweis", "Bitte zuerst Einträge auswählen.")
            return
        if not messagebox.askyesno(
                "Verlauf bereinigen",
                "Download-Verlauf der gewählten Einträge löschen?\n"
                "Alle Folgen werden beim nächsten Check erneut heruntergeladen."):
            return
        ids = set(selected)
        for e in self._watchlist.get("entries", []):
            if e["id"] in ids:
                e["downloaded_ids"] = []
                e["reset_pending"]  = True   # Disk-Checks beim nächsten Check überspringen
        self._save_watchlist()
        self._populate_watchlist_tree()
        self.wl_status_var.set("Verlauf bereinigt.")

    def _start_watchlist_check(self):
        entries = self._watchlist.get("entries", [])
        if not entries:
            messagebox.showinfo("Watchlist leer",
                                "Füge zuerst Sendungen zur Watchlist hinzu.")
            return
        self.wl_check_btn.configure(state=tk.DISABLED)
        self.wl_status_var.set("Prüfe …")
        threading.Thread(target=self._watchlist_check_thread,
                         args=(entries,), daemon=True).start()

    def _watchlist_check_thread(self, entries):
        all_new_items = []
        folder        = self.wl_folder_var.get()
        _ACCESS_TERMS = ("hörgeschädigte", "gebärdensprache", "hörfassung", "audiodeskription")

        def _parse_min(s):
            s = str(s).strip()
            return int(s) * 60 if s.isdigit() else None

        for entry in entries:
            if self._cancel_flag: break

            topic_q = entry["topic"]
            ch      = entry.get("channel", "Alle")
            tf      = entry.get("title_filter", "").strip()
            queries = [{"fields": ["topic"], "query": topic_q}]
            if ch != "Alle":
                queries.append({"fields": ["channel"], "query": ch})
            if tf:
                queries.append({"fields": ["title"], "query": tf})

            payload = {"queries": queries, "sortBy": "timestamp",
                       "sortOrder": "desc", "future": False, "offset": 0, "size": 1000}

            def _fetch_mvw():
                try:
                    resp = requests.post(API_URL, json=payload,
                                         headers={"Content-Type": "text/plain"}, timeout=20)
                    resp.raise_for_status()
                    items = resp.json().get("result", {}).get("results", [])
                    for it in items:
                        it.setdefault("_source", "MVW")
                    return items
                except Exception:
                    return []

            with ThreadPoolExecutor(max_workers=3) as pool:
                f_mvw = pool.submit(_fetch_mvw)
                f_ard = pool.submit(_search_ard, topic_q, ch, 100)
                f_zdf = pool.submit(_search_zdf, topic_q, ch, 100)
                mvw_res = f_mvw.result(timeout=30)
                ard_res = f_ard.result(timeout=90)
                zdf_res = f_zdf.result(timeout=90)

            results = _merge_deduplicate(mvw_res, ard_res, zdf_res)

            # Einstellungen pro Eintrag
            filter_access = entry.get("filter_access", True)
            subtitles     = entry.get("subtitles",     True)
            series_fmt    = entry.get("series_fmt",    False)

            # Dauer-Filter (pro Eintrag)
            dur_min = _parse_min(entry.get("dur_min", ""))
            dur_max = _parse_min(entry.get("dur_max", ""))
            if dur_min is not None:
                results = [r for r in results if (r.get("duration") or 0) >= dur_min]
            if dur_max is not None:
                results = [r for r in results if (r.get("duration") or 0) <= dur_max]

            # Barrierefreiheits-Filter
            if filter_access:
                results = [r for r in results
                           if not any(t in r.get("title",  "").lower() or
                                      t in r.get("topic",  "").lower()
                                      for t in _ACCESS_TERMS)]

            # Sprachfilter
            results = _apply_language_filter(results, entry.get("language", "Alle"))

            known        = set(entry.get("downloaded_ids", []))
            reset_active = entry.get("reset_pending", False)

            # Kandidaten-Ordner für den Scan (verschiedene Namens-Schreibweisen)
            topic_str  = entry.get("topic", "")
            scan_dirs  = {
                os.path.join(folder, _safe_dirname(topic_str)),   # Tool-eigene Schreibweise
                os.path.join(folder, topic_str.strip()),          # Literal-Name
                folder,                                           # Fallback: Root
            }

            # Ordner bei jedem Prüflauf frisch einlesen (keine Zwischenspeicherung)
            sidecar_map  = {}   # hash → mp4_pfad (nur existierende Dateien)
            disk_tags    = set()
            disk_ep_nums = set()
            for sd in scan_dirs:
                sidecar_map.update(_scan_sidecar_hashes(sd))
                ft, en = _scan_se_tags(sd)
                disk_tags    |= ft
                disk_ep_nums |= en

            def _file_exists_for(item):
                """Prüft ob die MP4 für dieses Item in irgendeiner Format-Variante existiert."""
                for fmt_flag in (series_fmt, not series_fmt):
                    _, fp = _build_filepath(
                        folder,
                        item.get("topic",   ""),
                        item.get("title",   ""),
                        item.get("timestamp", 0),
                        fmt_flag
                    )
                    if os.path.isfile(fp):
                        return True
                return False

            # transient_seen: nur für diesen Check-Lauf – wird NICHT in downloaded_ids
            # gespeichert, damit Reset dauerhaft wirkt und nicht beim nächsten Check
            # durch den Disk-Scan überschrieben wird.
            transient_seen = set(known) | self._dl_known_hashes

            for item in results:
                h = _item_hash(item)

                if h in transient_seen:
                    if reset_active:
                        # Nach Reset: alles neu einreihen, transient_seen ignorieren
                        transient_seen.discard(h)
                        known.discard(h)
                    else:
                        # In downloaded_ids, aber Datei inzwischen gelöscht? → erneut einreihen
                        if h in known and not _file_exists_for(item) and h not in sidecar_map:
                            known.discard(h)
                            transient_seen.discard(h)
                        else:
                            continue

                if not reset_active:
                    # Stufe 1: Sidecar = Datei vollständig bestätigt – nur überspringen
                    if h in sidecar_map:
                        transient_seen.add(h); continue

                    # Stufe 2: Datei vorhanden – nicht doppelt einreihen
                    if _file_exists_for(item):
                        transient_seen.add(h); continue

                    # Stufe 2b: Dateiname-Check – gleicher Dateiname wie ein bekannter Download?
                    for fmt_flag in (series_fmt, not series_fmt):
                        _, would_be = _build_filepath(
                            folder, item.get("topic", ""), item.get("title", ""),
                            item.get("timestamp", 0), fmt_flag)
                        if os.path.basename(would_be) in self._dl_known_filenames:
                            transient_seen.add(h)
                            break
                    if h in transient_seen:
                        continue

                    # Stufe 3a: Exakter SxxExx-Tag (z.B. S2024E03)
                    tag = _item_se_tag(item)
                    if tag and tag in disk_tags:
                        transient_seen.add(h); continue

                    # Stufe 3b: Nur Folgennummer (Fallback)
                    ep = _extract_episode(item.get("title", ""))
                    if ep and ep in disk_ep_nums:
                        transient_seen.add(h)

            # Reset-Flag löschen – nächster Check verhält sich wieder normal
            if reset_active:
                entry.pop("reset_pending", None)

            # Nur gelöschte Einträge aus downloaded_ids entfernen (known wurde ggf. bereinigt)
            entry["downloaded_ids"] = list(known)

            new_items = [r for r in results if _item_hash(r) not in transient_seen]

            for item in new_items:
                item["_wl_entry_id"]      = entry["id"]
                item["_wl_quality"]       = entry.get("quality", "HD")
                item["_wl_subtitles"]     = subtitles
                item["_wl_series_fmt"]    = series_fmt
                item["_wl_exist_action"]  = entry.get("exist_action", "skip")
            all_new_items.extend(new_items)

            entry["last_checked"] = datetime.now().isoformat(timespec="seconds")

        self._save_watchlist()
        self.root.after(0, self._populate_watchlist_tree)

        if not all_new_items:
            self.root.after(0, lambda: (
                self.wl_status_var.set("Keine neuen Folgen."),
                self.wl_check_btn.configure(state=tk.NORMAL)
            ))
            return

        self.root.after(0, lambda n=len(all_new_items):
            self.wl_status_var.set(f"{n} neue Folge(n) gefunden – Download startet …"))

        # Neue Folgen herunterladen
        seen_hashes = set()
        for e in self._watchlist.get("entries", []):
            seen_hashes.update(e.get("downloaded_ids", []))

        # Bereits in der Queue (wartend oder laufend) → nicht doppelt einreihen
        queued_hashes = {
            _item_hash(j["item"])
            for j in self._dl_jobs.values()
            if j["status"] in ("waiting", "downloading")
        }
        seen_hashes |= queued_hashes

        def on_done(newly_downloaded):
            # Hashes in Watchlist eintragen (heruntergeladen + vorhanden-übersprungen)
            by_entry: dict = {}
            for item in newly_downloaded:
                eid = item.get("_wl_entry_id")
                if eid:
                    h = _item_hash(item)
                    lst = by_entry.setdefault(eid, [])
                    if h not in lst:
                        lst.append(h)
            for entry in self._watchlist.get("entries", []):
                hashes = by_entry.get(entry["id"], [])
                ids = entry.setdefault("downloaded_ids", [])
                for h in hashes:
                    if h not in ids:
                        ids.append(h)
            self._save_watchlist()
            self._populate_watchlist_tree()
            self.wl_check_btn.configure(state=tk.NORMAL)
            dl_count      = sum(1 for it in newly_downloaded
                                if not it.get("_skipped_existing"))
            skipped_count = sum(1 for it in newly_downloaded
                                if it.get("_skipped_existing"))
            parts = []
            if dl_count:      parts.append(f"✓ {dl_count} heruntergeladen")
            if skipped_count: parts.append(f"{skipped_count} bereits vorhanden")
            self.wl_status_var.set("  |  ".join(parts) if parts else "✓ Fertig.")

        quality = all_new_items[0].get("_wl_quality", "HD") if all_new_items else "HD"
        self.root.after(0, lambda:
            self._start_download(
                items=all_new_items,
                quality=quality,
                folder=folder,
                skip_dupes=True,
                exist_action="skip",
                subtitles=None,     # wird per Item überschrieben (_wl_subtitles)
                series_fmt=None,    # wird per Item überschrieben (_wl_series_fmt)
                on_done=on_done,
                seen_hashes=seen_hashes,
            )
        )


# ═══════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    if "--selftest" in sys.argv:
        sys.exit(1 if _run_group_selftest() else 0)

    root = TkinterDnD.Tk() if HAS_DND else tk.Tk()
    try:
        root.tk.call("tk", "scaling", 1.3)
    except Exception:
        pass
    MediathekDownloader(root)
    root.mainloop()
