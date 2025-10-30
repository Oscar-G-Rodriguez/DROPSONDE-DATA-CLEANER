#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
end-to-end dropsonde archive organizer & converter
- handles non-af/noaa bundles, af non-d splitting and merging, and "already d" shortcuts
- mirrors operproc-like folders into done/operproc via flightmap + dindex
"""

import os
import re
import sys
import tarfile
import tempfile
import shutil
import time
import pytz
import gzip
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Iterable
from collections import defaultdict
from datetime import datetime, timedelta

#
# config (edit these to match your environment)
#

# portable but defaults to your windows path
BASE_DIR = Path(os.getenv("AVAPS_BASE_DIR", r"C:\Users\osci2\Downloads\INTERNSHIP\AOML\DROPSONDE\DATA"))

INPUT_ROOT   = Path(os.getenv("AVAPS_INPUT",   BASE_DIR / "NOT DONE"))
OUTPUT_ROOT  = Path(os.getenv("AVAPS_OUTPUT",  BASE_DIR / "Done"))
STAGING_ROOT = Path(os.getenv("AVAPS_STAGING", BASE_DIR / "inprogress"))
ERRORS_ROOT  = Path(os.getenv("AVAPS_ERRORS",  BASE_DIR / "errors"))

# fixed campaign → letter mapping (folder name decides campaign family)
FIXED_CODES = {
    "TPARC": "U", "AFRES": "U", "ADEOS": "U",
    "CAMEX": "NASA", "NAMMA": "NASA",
    "RAINEX": "NRL", "CANADA": "CANADA",
}

# campaigns that should not be treated as noaa-aircraft-letter missions
IGNORED_CAMPAIGN_PREFIXES = (
    "FASTEX", "EPIC", "ADEOS", "MISC",
    "NORPEX", "NASA97", "SNOWBAND", "WSR",
)

# legacy letter normalization for af containers found in filenames (e.g., "20130606A1" → "20130606U1")
NAME_SWAPS = {
    "A": "U",
    # add more swaps if you encounter other legacy letters for af
}

# map aircraft identifiers → noaa mission letters
# strict only: no generic type strings like "G-IV", "WP-3D"
NOAA_AIRCRAFT_TO_LETTER = {
    "NOAA42": "H", "N42RF": "H",
    "NOAA43": "I", "N43RF": "I",
    "N49RF": "N",
}

# leading container token at the very start of a filename:
#  e.g., 20221108U1_DFRD.tar, 20231021H1, 19970527N2_NETCDF.tgz
LEADING_CONTAINER_TOKEN = re.compile(
    r"^(?P<date>\d{8})(?P<letter>[A-Za-z0-9]+)(?P<num>\d+)\b", re.I
)

# --- af / recon mission/tail surrogates seen in footers/mission line ---
AF_SURROGATE_PATTERNS = [
    re.compile(r"\b(AF\d{3})\b", re.I),        # AF301, AF309, AF304 ...
    re.compile(r"\b(TEAL\s?\d{2,3})\b", re.I), # TEAL 72, TEAL92 ...
    re.compile(r"\b(RECON\s?\d{2,3})\b", re.I),# RECON 30 ...
    re.compile(r"\b(\d{4}[A-Z])\b", re.I),     # 0324A, 0912A ...
]
INDEX_BASENAMES = {"index", "index.htm", "index.html"}

# af splitting thresholds
AF_SPLIT_GAP_HOURS = 2                     # split groups when gap > 2 hours
AF_MERGE_CONTINUITY_MINUTES = 30           # merge continuation within 30 minutes
AF_REQUIRE_SAME_CHANNEL_FOR_MERGE = True   # never merge across channels

# time normalization behavior
ROUND_FRACTIONS = False  # by default we truncate hhmmss.ss to hhmmss, set true to round to nearest

# whether to preserve original files (copy) or move; we copy to be safer
COPY_MODE = True

#
# utility datatypes
#

@dataclass
class FileParseResult:
    path: Path
    has_lau_token: bool = False
    lau_dt: Optional[datetime] = None          # parsed from "avaps-t## lau" line or rescue
    launch_dt_from_footer: Optional[datetime] = None  # parsed from "launch time (y,m,d,h,m,s)" in com footer
    earliest_data_dt: Optional[datetime] = None
    latest_data_dt: Optional[datetime] = None
    end_dt: Optional[datetime] = None          # parsed from "avaps-t## end" line
    project_or_mission: Optional[str] = None
    aircraft_type: Optional[str] = None
    aircraft_id: Optional[str] = None          # rhs token after comma in "aircraft type/id"
    channel: Optional[int] = None
    mission_letter_hint: Optional[str] = None
    mission_flight_number_hint: Optional[int] = None
    af_code_hint: Optional[str] = None         # new: AF### / TEAL## / RECON## / ####A
    raw_lines: Optional[List[str]] = None
    encoding_used: str = "utf-8"


@dataclass
class BundleDecision:
    og_bundle_id: str
    is_af: bool = False
    is_noaa: bool = False
    is_already_d_container: bool = False
    container_name: Optional[str] = None
    nonaf_letter: Optional[str] = None
    flight_number: Optional[int] = None
    flight_date: Optional[datetime] = None
    reason: Optional[str] = None


@dataclass
class FlightMapEntry:
    container: str
    files: Dict[str, str] = field(default_factory=dict)  # abs_source_path → d_filename


#
# logging helpers
#

class Logger:
    def __init__(self, errors_root: Path):
        # use true UTC when appending Z (zulu) for precision/clarity
        ts = datetime.now(pytz.UTC).strftime("%Y%m%dT%H%M%SZ")
        self.root = errors_root / ts
        (self.root / "logs").mkdir(parents=True, exist_ok=True)
        self.errors_fp = (self.root / "logs" / f"errors_{ts}.txt").open("a", encoding="utf-8")
        self.actions_fp = (self.root / "logs" / f"actions_{ts}.txt").open("a", encoding="utf-8")
        self.summary_fp = (self.root / "logs" / f"summary_{ts}.txt").open("a", encoding="utf-8")

    def err(self, msg: str):
        self.errors_fp.write(msg.rstrip() + "\n"); self.errors_fp.flush()

    def act(self, msg: str):
        self.actions_fp.write(msg.rstrip() + "\n"); self.actions_fp.flush()

    def sum(self, msg: str):
        self.summary_fp.write(msg.rstrip() + "\n"); self.summary_fp.flush()

    def close(self):
        for fp in (self.errors_fp, self.actions_fp, self.summary_fp):
            try:
                fp.close()
            except Exception:
                pass


#
# general helpers (parsing, time, strings)
#

LAU_RE = re.compile(r"^\s*avaps-t\d+\s+lau\b", re.I)
END_RE = re.compile(r"^\s*avaps-t\d+\s+end\b", re.I)
GENERIC_LAU = re.compile(r"\blau\b", re.I)

DATE_YYMMDD = re.compile(r"\b(\d{2})(\d{2})(\d{2})\b")
TIME_HHMMSS_F = re.compile(r"\b(\d{2})(\d{2})(\d{2})(?:\.(\d+))?\b")

def expand_yy_to_yyyy(yy: str) -> int:
    y = int(yy)
    if 97 <= y <= 99:
        return 1900 + y
    return 2000 + y  # 00..24

def norm_time_hhmmss(hh: str, mm: str, ss: str, frac: Optional[str]) -> Tuple[int, int, int]:
    h, m, s = int(hh), int(mm), int(ss)
    if frac and ROUND_FRACTIONS:
        try:
            f_val = float("0." + frac)
            if f_val >= 0.5:
                s += 1
        except Exception:
            pass
    if s > 59: s = 59
    if m > 59: m = 59
    if h > 23: h = 23
    if s < 0: s = 0
    if m < 0: m = 0
    if h < 0: h = 0
    return h, m, s

def compose_dt_yy_mm_dd_hhmmss(yy: str, mo: str, dd: str, hh: str, mm: str, ss: str, frac: Optional[str]) -> datetime:
    yyyy = expand_yy_to_yyyy(yy)
    h, m, s = norm_time_hhmmss(hh, mm, ss, frac)
    try:
        return datetime(yyyy, int(mo), int(dd), h, m, s)
    except ValueError:
        mo_i = max(1, min(12, int(mo)))
        dd_i = max(1, min(28, int(dd)))  # clamp day safely
        return datetime(yyyy, mo_i, dd_i, h, m, s)

def parse_launch_time_footer(line: str) -> Optional[datetime]:
    m = re.search(r"launch time\s*\(y,m,d,h,m,s\)\s*:\s*(\d{4})-(\d{2})-(\d{2})\s*,\s*(\d{2}):(\d{2}):(\d{2})", line, re.I)
    if m:
        yyyy, mo, dd, hh, mm, ss = [int(g) for g in m.groups()]
        return datetime(yyyy, mo, dd, hh, mm, ss)
    return None

def parse_aircraft_type_id(line: str) -> Tuple[Optional[str], Optional[str]]:
    m = re.search(r"aircraft\s+type/id\s*:\s*(.+?),\s*(.+?)\s*$", line, re.I)
    if not m:
        return None, None
    typ = m.group(1).strip().upper()
    tail = m.group(2).strip().upper()
    return typ, tail

def parse_project_name(line: str) -> Optional[str]:
    m = re.search(r"project\s+name/mission\s+id\s*:\s*(.+?)\s*$", line, re.I)
    if m:
        return m.group(1).strip()
    return None

def parse_channel_from_datatype(line: str) -> Optional[int]:
    m = re.search(r"channel\s+(\d+)", line, re.I)
    if m:
        try:
            return int(m.group(1))
        except Exception:
            return None
    return None

def sanitize_letter(letter: str) -> str:
    return re.sub(r"[^A-Za-z0-9]", "", letter)

def container_regex() -> re.Pattern:
    return re.compile(r"^(?P<date>\d{8})(?P<letter>[A-Za-z0-9]+)(?P<num>\d+)_DFILES(?:\.(?:tar\.gz|tgz|tar))?$", re.I)

def dfile_regex() -> re.Pattern:
    return re.compile(r"^D(?P<date>\d{8})_(?P<time>\d{6})(?:\.\d+)?(?:\.(?P<channel>\d{1,3}))?$", re.I)

def has_token(line: str, token: str) -> bool:
    return token.lower() in line.lower()

def looks_like_index_file(p: Path) -> bool:
    base = p.name.lower()
    stem = p.stem.lower()
    return (base in INDEX_BASENAMES) or (stem in INDEX_BASENAMES)

def _find_af_code(s: str) -> Optional[str]:
    for pat in AF_SURROGATE_PATTERNS:
        m = pat.search(s)
        if m:
            return m.group(1).upper()
    return None

#
# campaign + org helpers
#

def classify_campaign_from_folder(campaign: str) -> Tuple[bool, bool, Optional[str]]:
    c = campaign.upper()
    for p in IGNORED_CAMPAIGN_PREFIXES:
        if c.startswith(p):
            break
    for key, letter in FIXED_CODES.items():
        if c.startswith(key):
            is_af = (key == "AFRES")
            return is_af, False, letter
    if c.startswith("HURR"):
        return False, True, None
    return False, False, None

def resolve_noaa_letter(aircraft_type: Optional[str], aircraft_id: Optional[str]) -> Optional[str]:
    tokens = []
    if aircraft_id:
        tokens.append(aircraft_id.upper())
    if aircraft_type:
        tokens.append(aircraft_type.upper())
    for t in tokens:
        for key, letter in NOAA_AIRCRAFT_TO_LETTER.items():
            if key in t:
                return letter
    return None

#
# file parsing
#

def read_text_lines(path: Path, logger: Logger) -> Tuple[List[str], str]:
    data = None
    enc_used = "utf-8"
    for enc in ("utf-8", "cp1252", "latin-1"):
        try:
            data = path.read_text(encoding=enc, errors="strict")
            enc_used = enc
            break
        except Exception:
            data = None
    if data is None:
        try:
            data = path.read_bytes().decode("utf-8", errors="replace")
            enc_used = "utf-8/replace"
        except Exception as e:
            logger.err(f"[read_error] {path} :: {e}")
            return [], "unknown"
    data = data.replace("\r\n", "\n").replace("\r", "\n").replace("\x00", "")
    return data.splitlines(), enc_used

def parse_sonde_file(path: Path, logger: Logger, keep_lines: bool = True) -> FileParseResult:
    lines, enc = read_text_lines(path, logger)
    res = FileParseResult(path=path, raw_lines=(lines if keep_lines else None), encoding_used=enc)

    earliest_dt: Optional[datetime] = None
    latest_dt: Optional[datetime] = None

    for idx, line in enumerate(lines):
        low = line.lower()

        # lau detection
        if "lau" in low and re.search(r"\blau\b", line, re.I):
            res.has_lau_token = True
            parts = line.strip().split()
            lau_idx = None
            for i, p in enumerate(parts):
                if p.upper() == "LAU":
                    lau_idx = i
                    break
            dt = None
            if lau_idx is not None and lau_idx + 3 < len(parts):
                ymd_tok = parts[lau_idx + 2]
                tim_tok = parts[lau_idx + 3].rstrip(",;:")
                if not re.fullmatch(r"\d{6}", ymd_tok):
                    ymd_digits = re.sub(r"\D", "", ymd_tok)
                    if len(ymd_digits) >= 6:
                        ymd_tok = ymd_digits[:6]
                    else:
                        ymd_tok = None
                m_time = re.fullmatch(r"(\d{6})(?:\.(\d+))?", tim_tok)
                frac = None
                if not m_time:
                    dig = re.sub(r"\D", "", tim_tok)
                    if len(dig) >= 6:
                        hhmmss = dig[:6]
                        frac = (dig[6:] or None)
                        m_time = re.match(r"(\d{6})", hhmmss)
                if ymd_tok and m_time:
                    hhmmss = (m_time.group(1) if "." not in tim_tok
                              else re.fullmatch(r"(\d{6})(?:\.(\d+))?", tim_tok).group(1))
                    frac = (None if "." not in tim_tok
                            else re.fullmatch(r"(\d{6})(?:\.(\d+))?", tim_tok).group(2))
                    yy, mo, dd = ymd_tok[0:2], ymd_tok[2:4], ymd_tok[4:6]
                    hh, mm, ss = hhmmss[0:2], hhmmss[2:4], hhmmss[4:6]
                    try:
                        dt = compose_dt_yy_mm_dd_hhmmss(yy, mo, dd, hh, mm, ss, frac)
                    except Exception:
                        dt = None
            if dt is None:
                dm = DATE_YYMMDD.search(line)
                tm = TIME_HHMMSS_F.search(line)
                if not (dm and tm):
                    for neighbor in (idx - 1, idx + 1):
                        if 0 <= neighbor < len(lines):
                            dm = dm or DATE_YYMMDD.search(lines[neighbor])
                            tm = tm or TIME_HHMMSS_F.search(lines[neighbor])
                            if dm and tm:
                                break
                if dm and tm:
                    try:
                        yy, mo, dd = dm.group(1), dm.group(2), dm.group(3)
                        hh, mm, ss, frac = tm.group(1), tm.group(2), tm.group(3), tm.group(4)
                        dt = compose_dt_yy_mm_dd_hhmmss(yy, mo, dd, hh, mm, ss, frac)
                    except Exception:
                        dt = None
            if dt:
                res.lau_dt = dt

        # com fields + tail parsing
        if "aircraft type/id" in low:
            typ, tail = parse_aircraft_type_id(line)
            if typ:
                res.aircraft_type = typ
            if tail:
                res.aircraft_id = tail
            else:
                for k in range(1, 4):
                    if idx + k >= len(lines):
                        break
                    nxt = lines[idx + k].strip()
                    if not nxt:
                        continue
                    m = re.search(r"\b(\d{2,}-\d{3,})\b", nxt)
                    if not m:
                        m = re.search(r"\b([A-Z]?\d{3,6}[A-Z]?)\b", nxt, re.I)
                    if m:
                        res.aircraft_id = m.group(1).upper()
                        break

        if "project name/mission id" in low:
            res.project_or_mission = parse_project_name(line)
            code = _find_af_code(line)
            if code and not res.af_code_hint:
                res.af_code_hint = code

        if any(k in low for k in ("flight", "mission", "aircraft")):
            code2 = _find_af_code(line)
            if code2 and not res.af_code_hint:
                res.af_code_hint = code2
            if (not res.aircraft_id) or res.aircraft_id.strip() in ("", "---"):
                if code2:
                    res.aircraft_id = res.aircraft_id or code2

        if "data type/data channel" in low:
            ch = parse_channel_from_datatype(line)
            if ch is not None:
                res.channel = ch

        if "launch time (y,m,d,h,m,s)" in low:
            m = re.search(
                r"launch time\s*\(y,m,d,h,m,s\)\s*:\s*(\d{4})[-/](\d{2})[-/](\d{2})\s*,\s*(\d{2}):(\d{2}):(\d{2})",
                line, re.I
            )
            if m:
                try:
                    yyyy, mo, dd, hh, mm, ss = [int(g) for g in m.groups()]
                    res.launch_dt_from_footer = datetime(yyyy, mo, dd, hh, mm, ss)
                except Exception:
                    pass
            else:
                dt = parse_launch_time_footer(line)
                if dt:
                    res.launch_dt_from_footer = dt

        if 'end' in low and END_RE.search(line):
            dm = DATE_YYMMDD.search(line)
            tm = TIME_HHMMSS_F.search(line)
            if dm and tm:
                try:
                    yy, mo, dd = dm.group(1), dm.group(2), dm.group(3)
                    hh, mm, ss, frac = tm.group(1), tm.group(2), tm.group(3), tm.group(4)
                    res.end_dt = compose_dt_yy_mm_dd_hhmmss(yy, mo, dd, hh, mm, ss, frac)
                except Exception:
                    pass

        # continuous dt scan (for earliest/latest windows)
        dm = DATE_YYMMDD.search(line)
        tm = TIME_HHMMSS_F.search(line)
        if dm and tm:
            try:
                dt = compose_dt_yy_mm_dd_hhmmss(dm.group(1), dm.group(2), dm.group(3),
                                                tm.group(1), tm.group(2), tm.group(3), tm.group(4))
                if earliest_dt is None or dt < earliest_dt:
                    earliest_dt = dt
                if latest_dt is None or dt > latest_dt:
                    latest_dt = dt
            except Exception:
                pass

    res.earliest_data_dt = earliest_dt
    res.latest_data_dt = latest_dt

    if res.has_lau_token and res.lau_dt is None:
        for i, ln in enumerate(lines):
            if "lau" in ln.lower():
                for j in (i - 1, i + 1):
                    if 0 <= j < len(lines):
                        dm = DATE_YYMMDD.search(lines[j])
                        tm = TIME_HHMMSS_F.search(lines[j])
                        if dm and tm:
                            try:
                                res.lau_dt = compose_dt_yy_mm_dd_hhmmss(dm.group(1), dm.group(2), dm.group(3),
                                                                         tm.group(1), tm.group(2), tm.group(3), tm.group(4))
                                break
                            except Exception:
                                pass
                if res.lau_dt:
                    break

    return res


#
# bundle processing
#

def is_archive(p: Path) -> bool:
    # only treat as archive if it's truly a tar-type (or tarfile can open it)
    name = p.name.lower()
    if name.endswith((".tar.gz", ".tgz", ".tar")):
        return True
    try:
        return tarfile.is_tarfile(p)
    except Exception:
        return False

def is_probably_text(p: Path) -> bool:
    return True

def is_already_d_container_name(name: str) -> Optional[Tuple[str, str, int]]:
    m = container_regex().match(name)
    if not m:
        return None
    ymd = m.group("date")
    letter = sanitize_letter(m.group("letter"))
    num = int(m.group("num"))
    for k, v in NAME_SWAPS.items():
        if letter.upper().startswith(k):
            letter = v + letter[len(k):]
            break
    return ymd, letter, num

def ensure_dirs(year: str):
    (OUTPUT_ROOT / year / "raw").mkdir(parents=True, exist_ok=True)
    (OUTPUT_ROOT / year / "operproc").mkdir(parents=True, exist_ok=True)
    (OUTPUT_ROOT / year / "no_launch").mkdir(parents=True, exist_ok=True)
    (OUTPUT_ROOT / year / "to_categorize").mkdir(parents=True, exist_ok=True)
    (STAGING_ROOT / year / "af_groups").mkdir(parents=True, exist_ok=True)
    (OUTPUT_ROOT / year / "no_tail").mkdir(parents=True, exist_ok=True)
    (OUTPUT_ROOT / year / "no_aircraft").mkdir(parents=True, exist_ok=True)

def unique_dst(dst: Path) -> Path:
    if not dst.exists():
        return dst
    stem, suf = dst.stem, dst.suffix
    k = 1
    while True:
        cand = dst.with_name(f"{stem}__{k}{suf}")
        if not cand.exists():
            return cand
        k += 1

def copy_or_move(src: Path, dst: Path, logger: Logger):
    dst.parent.mkdir(parents=True, exist_ok=True)
    if dst.exists():
        dst = unique_dst(dst)
    if COPY_MODE:
        shutil.copy2(src, dst)
        logger.act(f"[copy] {src} → {dst}")
    else:
        shutil.move(str(src), str(dst))
        logger.act(f"[move] {src} → {dst}")

def write_text(dst: Path, content: Iterable[str], logger: Logger):
    dst.parent.mkdir(parents=True, exist_ok=True)
    with dst.open("w", encoding="utf-8", newline="\n") as f:
        for line in content:
            f.write(line.rstrip("\n") + "\n")
    logger.act(f"[write] {dst}")

def extract_archive(archive_path: Path, into: Path, logger: Logger) -> Path:
    into.mkdir(parents=True, exist_ok=True)
    temp_dir = tempfile.mkdtemp(prefix="extract_", dir=str(into))
    root = Path(temp_dir)
    try:
        with tarfile.open(archive_path, "r:*") as tf:
            safe_members = []
            for m in tf.getmembers():
                if m.name.startswith("/") or ".." in Path(m.name).parts:
                    logger.err(f"[archive_skip_unsafe] {archive_path} :: {m.name}")
                    continue
                safe_members.append(m)
            try:
                tf.extractall(path=root, members=safe_members, filter="data")
            except TypeError:
                tf.extractall(path=root, members=safe_members)
        logger.act(f"[extract] {archive_path} → {root}")
        return root
    except Exception as e:
        logger.err(f"[archive_extract_error] {archive_path} :: {e}")
        return root

def walk_all_files(root: Path) -> List[Path]:
    return [p for p in root.rglob("*") if p.is_file()]

def list_top_level_dirs(root: Path) -> List[Path]:
    return [p for p in root.iterdir() if p.is_dir()]

def yyyymmdd_from_dt(dt: datetime) -> str:
    return dt.strftime("%Y%m%d")

def hhmmss_from_dt(dt: datetime) -> str:
    return dt.strftime("%H%M%S")

def d_stem(date_str: str, time_str: str) -> str:
    return f"D{date_str}_{time_str}"

def build_d_filename(dt: datetime, channel: Optional[int]) -> str:
    base = f"D{yyyymmdd_from_dt(dt)}_{hhmmss_from_dt(dt)}"
    if channel is not None:
        return f"{base}.{channel}"
    return base

def ensure_container(year: str, container: str) -> Path:
    target = OUTPUT_ROOT / year / "raw" / container
    target.mkdir(parents=True, exist_ok=True)
    return target

def operproc_dir_name_from_container(container: str) -> str:
    return re.sub(r"_DFILES$", "", container, flags=re.I)

def _dir_size_bytes(p: Path) -> int:
    return sum(f.stat().st_size for f in p.rglob("*") if f.is_file())

def retar_dfiles_for_year(output_root: Path, year: str, logger: "Logger"):
    raw_root = output_root / year / "raw"
    if not raw_root.exists():
        logger.act(f"[retar] skip year={year} (no raw dir)")
        return

    for d in sorted(raw_root.iterdir(), key=lambda p: p.name):
        if not (d.is_dir() and d.name.upper().endswith("_DFILES")):
            continue

        tgz = raw_root / f"{d.name}.tar.gz"
        if tgz.exists():
            logger.act(f"[retar_skip_exists] {tgz.name}")
            continue

        try:
            src_bytes = _dir_size_bytes(d)
            logger.act(f"[retar_pack] {d.name} ({src_bytes} bytes) → {tgz.name}")
            with tarfile.open(tgz, "w:gz") as tf:
                for f in d.rglob("*"):
                    if f.is_file():
                        arcname = d.name + "/" + str(f.relative_to(d)).replace("\\", "/")
                        info = tf.gettarinfo(str(f), arcname=arcname)
                        with f.open("rb") as fh:
                            tf.addfile(info, fh)

            ok = False
            try:
                with tarfile.open(tgz, "r:gz") as tf:
                    ok = any(m.isfile() for m in tf.getmembers())
            except Exception as e:
                logger.err(f"[retar_verify_error] {tgz} :: {e}")
                ok = False

            if ok:
                try:
                    shutil.rmtree(d, ignore_errors=True)
                    saved = src_bytes - (tgz.stat().st_size if tgz.exists() else 0)
                    logger.act(f"[retar_done] {tgz.name} saved≈{max(saved,0)} bytes")
                except Exception as e:
                    logger.err(f"[retar_cleanup_error] {d} :: {e}")
            else:
                try:
                    tgz.unlink(missing_ok=True)
                except Exception:
                    pass
                logger.err(f"[retar_abort] kept original folder: {d.name}")

        except Exception as e:
            logger.err(f"[retar_error] {d} :: {e}")

#
# main organizer class
#

class AvapsOrganizer:
    def __init__(self, input_root: Path, output_root: Path, staging_root: Path, errors_root: Path, logger: Logger):
        self.input_root = input_root
        self.output_root = output_root
        self.staging_root = staging_root
        self.errors_root = errors_root
        self.logger = logger

        # indices
        self.flight_map: Dict[str, FlightMapEntry] = {}
        self.dindex: Dict[str, str] = {}  # d_stem → container
        self.time_index: Dict[Tuple[str, str], List[Tuple[datetime, str]]] = defaultdict(list)
        self.legacy_container_map: Dict[str, str] = {}

        # accounting
        self.count_input_files = 0
        self.count_classified = 0
        self.count_no_launch = 0
        self.count_unplaceable_raw = 0
        self.count_operproc_placed = 0
        self.count_operproc_uncategorized = 0
        self.count_no_tail = 0
        self.count_no_aircraft = 0

        # keep track of processed years for post passes
        self.processed_years: List[str] = []

    # alias helpers

    def _add_legacy_aliases_for_container(self, container: str):
        bare = re.sub(r"_DFILES$", "", container, flags=re.I)
        self.legacy_container_map[bare.upper()] = container
        self.legacy_container_map[(bare + "_DFILES").upper()] = container

    def _register_legacy_aliases_from_name(self, name: str, container: str):
        tokens: List[str] = []
        base = name
        if "::" in base:
            parts = base.split("::")
            tokens.extend(parts)
            base = parts[-1]
        else:
            tokens.append(base)

        def strip_exts(s: str) -> str:
            return re.sub(r"\.(tar\.gz|tgz|tar|gz)$", "", s, flags=re.I)

        expanded: set = set()
        for t in tokens:
            t1 = t
            t2 = strip_exts(t1)
            t3 = t2.split('.')[0] if '.' in t2 else t2
            for cand in (t1, t2, t3):
                cand = cand.strip()
                if cand:
                    expanded.add(cand)

        for tok in expanded:
            self.legacy_container_map[tok.upper()] = container

    def _find_longest_legacy_prefix(self, filename: str) -> Tuple[Optional[str], Optional[str]]:
        up = filename.upper()
        best_key = None
        best_container = None
        best_len = 0
        for key_up, cont in self.legacy_container_map.items():
            if up.startswith(key_up) and len(key_up) > best_len:
                best_key = key_up
                best_container = cont
                best_len = len(key_up)
        return best_key, best_container

    # orchestration

    def run(self):
        start = time.perf_counter()
        years = [p for p in self.input_root.iterdir() if p.is_dir()]
        for year_dir in sorted(years, key=lambda p: p.name):
            year = year_dir.name
            self.logger.sum(f"[year_start] {year}")
            print(f"processing year {year} ...")
            try:
                ensure_dirs(year)
                self.process_year(year_dir, year)
                self.logger.sum(f"[year_done] {year}")
                self.processed_years.append(year)
            except Exception as e:
                import traceback
                self.logger.err(f"[year_fatal] {year} :: {e}")
                self.logger.err(traceback.format_exc())
                print(f"!! fatal error in year {year}, skipping; see errors log")
                continue

        self.write_maps_and_summary()
        elapsed = time.perf_counter() - start
        self.logger.sum(f"[timer] pipeline finished in {elapsed:.2f} seconds")
        print(f"pipeline finished in {elapsed:.2f} seconds")

    def process_year(self, year_dir: Path, year: str):
        campaigns = [p for p in year_dir.iterdir() if p.is_dir()]

        # 2) raw pass for every campaign (build dindex + legacy container map)
        for camp_dir in sorted(campaigns, key=lambda p: p.name):
            if camp_dir.name.lower() in ("raw", "operproc", "postproc", "plots"):
                continue
            raw_dir = camp_dir / "raw"
            if raw_dir.exists():
                self.process_raw_campaign(year, camp_dir.name, raw_dir)

        # 3) operproc pass only after raw is finished
        for camp_dir in sorted(campaigns, key=lambda p: p.name):
            if camp_dir.name.lower() in ("raw",):
                continue
            for p in camp_dir.iterdir():
                if p.is_dir() and p.name.lower() != "raw":
                    self.process_operproc_folder(year, p)

        # 4) sweep anything left in no_tail and try to classify it now
        self.process_no_tail_folder(year)

        # 5) second-chance salvage from to_categorize (benefits from new dindex entries)
        self.salvage_to_categorize(year)

        # 6) sweep no launch to move scientist note files to operproc
        self.process_scientist_logs_from_no_launch(year)

        # 7) space saver: pack raw D-files folders for this year
        retar_dfiles_for_year(self.output_root, year, self.logger)

    # raw campaign processing

    def process_raw_campaign(self, year: str, campaign: str, raw_dir: Path):
        is_af, is_noaa, fixed_letter = classify_campaign_from_folder(campaign)

        for item in sorted(raw_dir.iterdir(), key=lambda p: p.name):
            if item.is_file() and is_archive(item):
                self.handle_archive_bundle(year, campaign, item, is_af, is_noaa, fixed_letter)
            elif item.is_dir():
                self.handle_dir_bundle(year, campaign, item, is_af, is_noaa, fixed_letter)
            elif item.is_file():
                self.handle_loose_file_bundle(year, campaign, item, is_af, is_noaa, fixed_letter)

    def _maybe_gunzip(self, p: Path) -> Optional[Path]:
        # gunzip single-file .gz (not a tarball)
        if p.suffix.lower() == ".gz":
            try:
                if tarfile.is_tarfile(p):
                    return None
            except Exception:
                pass
            out = p.with_suffix("")
            try:
                with gzip.open(p, "rb") as src, open(out, "wb") as dst:
                    shutil.copyfileobj(src, dst)
                return out
            except Exception as e:
                self.logger.err(f"[gunzip_error] {p} :: {e}")
        return None

    def handle_archive_bundle(self, year: str, campaign: str, archive_path: Path, is_af: bool, is_noaa: bool, fixed_letter: Optional[str]):
        og_bundle_id = f"{year}/{campaign}/raw/{archive_path.name}"
        self.count_input_files += 1

        maybe = is_already_d_container_name(archive_path.name)
        if maybe:
            ymd, letter, num = maybe
            container = f"{ymd}{letter}{num}_DFILES"
            self.shortcut_already_d_archive(year, archive_path, container, og_bundle_id)
            return

        # if it's a simple .gz of a single text file, just gunzip and process
        mgz = self._maybe_gunzip(archive_path)
        if mgz and mgz.is_file():
            self.handle_loose_file_bundle(year, campaign, mgz, is_af, is_noaa, fixed_letter)
            return

        temp_root = extract_archive(archive_path, self.staging_root / year, self.logger)
        top_dirs = list_top_level_dirs(temp_root)
        if top_dirs:
            for d in top_dirs:
                self.handle_dir_bundle(year, campaign, d, is_af, is_noaa, fixed_letter, og_hint=og_bundle_id + "::" + d.name)
        else:
            files = walk_all_files(temp_root)
            self.process_bundle_files(year, campaign, files, is_af, is_noaa, fixed_letter, og_bundle_id=og_bundle_id)

    def handle_dir_bundle(self, year: str, campaign: str, dir_path: Path, is_af: bool, is_noaa: bool, fixed_letter: Optional[str], og_hint: Optional[str] = None):
        og_bundle_id = og_hint or f"{year}/{campaign}/raw/{dir_path.name}"
        maybe = is_already_d_container_name(dir_path.name)
        if maybe:
            ymd, letter, num = maybe
            container = f"{ymd}{letter}{num}_DFILES"
            self.shortcut_already_d_dir(year, dir_path, container, og_bundle_id)
            return

        files = [p for p in dir_path.rglob("*") if p.is_file()]
        if not files:
            self.logger.err(f"[empty_bundle] {og_bundle_id}")
            return
        self.process_bundle_files(year, campaign, files, is_af, is_noaa, fixed_letter, og_bundle_id=og_bundle_id)

    def handle_loose_file_bundle(self, year: str, campaign: str, file_path: Path, is_af: bool, is_noaa: bool, fixed_letter: Optional[str]):
        og_bundle_id = f"{year}/{campaign}/raw/{file_path.name}"
        self.process_bundle_files(year, campaign, [file_path], is_af, is_noaa, fixed_letter, og_bundle_id=og_bundle_id)

    # already-d shortcuts

    def shortcut_already_d_archive(self, year: str, archive_path: Path, container: str, og_bundle_id: str):
        self.logger.act(f"[already_d_archive] {archive_path.name} → {container}")
        target = ensure_container(year, container)
        temp_root = extract_archive(archive_path, self.staging_root / year, self.logger)

        self._add_legacy_aliases_for_container(container)
        self._register_legacy_aliases_from_name(archive_path.name, container)

        for p in temp_root.rglob("*"):
            if p.is_file():
                rel = p.relative_to(temp_root)
                dst = target / rel.name
                copy_or_move(p, dst, self.logger)
                m = dfile_regex().match(dst.name)
                if m:
                    stem = f"D{m.group('date')}_{m.group('time')}"
                    self.dindex[stem] = container
        self.flight_map[og_bundle_id] = FlightMapEntry(container=container, files={})
        self.count_classified += 1

    def shortcut_already_d_dir(self, year: str, dir_path: Path, container: str, og_bundle_id: str):
        self.logger.act(f"[already_d_dir] {dir_path.name} → {container}")
        target = ensure_container(year, container)

        self._add_legacy_aliases_for_container(container)
        self._register_legacy_aliases_from_name(dir_path.name, container)

        for p in dir_path.rglob("*"):
            if p.is_file():
                dst = target / p.name
                copy_or_move(p, dst, self.logger)
                m = dfile_regex().match(dst.name)
                if m:
                    stem = f"D{m.group('date')}_{m.group('time')}"
                    self.dindex[stem] = container
        self.flight_map[og_bundle_id] = FlightMapEntry(container=container, files={})
        self.count_classified += 1

    # core bundle logic

    def _secondary_global_lau_rescue(self, parsed: List[FileParseResult]):
        any_lau_dt = any(r.lau_dt for r in parsed)
        if any_lau_dt:
            return
        for r in parsed:
            if r.lau_dt:
                continue
            lines = r.raw_lines or []
            for i, ln in enumerate(lines):
                if "lau" in ln.lower():
                    for j in (i - 1, i + 1):
                        if 0 <= j < len(lines):
                            dm = DATE_YYMMDD.search(lines[j])
                            tm = TIME_HHMMSS_F.search(lines[j])
                            if dm and tm:
                                try:
                                    r.lau_dt = compose_dt_yy_mm_dd_hhmmss(dm.group(1), dm.group(2), dm.group(3),
                                                                           tm.group(1), tm.group(2), tm.group(3), tm.group(4))
                                    break
                                except Exception:
                                    pass
                    if r.lau_dt:
                        break

    def process_bundle_files(self, year: str, campaign: str, files: List[Path], is_af: bool, is_noaa: bool, fixed_letter: Optional[str], og_bundle_id: str):
        # memory: keep raw lines only when needed (af path)
        parsed: List[FileParseResult] = []
        for f in files:
            if not is_probably_text(f):
                continue
            res = parse_sonde_file(f, self.logger, keep_lines=is_af)
            parsed.append(res)

        if is_af:
            if int(year) >= 2015:
                self.logger.act(f"[simplified_af_2015+] bundle={og_bundle_id}")

                earliest_lau_dt = None
                for r in parsed:
                    dt = r.lau_dt or r.launch_dt_from_footer or r.earliest_data_dt
                    if dt:
                        if earliest_lau_dt is None or dt < earliest_lau_dt:
                            earliest_lau_dt = dt

                if earliest_lau_dt is None:
                    self.logger.err(f"[simplified_af_no_launch_time] {og_bundle_id} -> no_launch")
                    for r in parsed:
                        dst = OUTPUT_ROOT / year / "no_launch" / r.path.name
                        copy_or_move(r.path, dst, self.logger)
                    self.count_no_launch += 1
                    return

                ymd = yyyymmdd_from_dt(earliest_lau_dt)
                letter = "U"
                key = (ymd, letter)
                self.time_index[key].append((earliest_lau_dt, og_bundle_id))
                rank = 1 + sorted(self.time_index[key], key=lambda x: x[0]).index((earliest_lau_dt, og_bundle_id))
                container = f"{ymd}{letter}{rank}_DFILES"
                target = ensure_container(year, container)

                self._add_legacy_aliases_for_container(container)
                self._register_legacy_aliases_from_name(og_bundle_id.split("/")[-1], container)
                self.flight_map[og_bundle_id] = FlightMapEntry(container=container, files={})

                for r in parsed:
                    dt = r.lau_dt or r.launch_dt_from_footer or r.earliest_data_dt
                    if not dt:
                        self.logger.err(f"[file_missing_time] {r.path} in {og_bundle_id}")
                        continue
                    dt = dt.replace(year=int(ymd[:4]), month=int(ymd[4:6]), day=int(ymd[6:8]))
                    dname = build_d_filename(dt, r.channel)
                    dst = target / dname
                    copy_or_move(r.path, dst, self.logger)
                    self.flight_map[og_bundle_id].files[str(r.path)] = dname
                    self.dindex[d_stem(yyyymmdd_from_dt(dt), hhmmss_from_dt(dt))] = container

                self.count_classified += 1
                return
            else:
                self.classify_af_bundle(year, campaign, parsed, og_bundle_id)
                return

        self._secondary_global_lau_rescue(parsed)
        self._secondary_global_lau_rescue(parsed)
        has_any_lau = any(r.has_lau_token or r.lau_dt for r in parsed)

        self.logger.sum(
            f"[debug] {og_bundle_id} parsed={len(parsed)} "
            f"lau_tokens={sum(1 for r in parsed if r.has_lau_token)} "
            f"lau_dt={sum(1 for r in parsed if r.lau_dt)} "
            f"end_dt={sum(1 for r in parsed if r.end_dt)}"
        )

        if not has_any_lau:
            for r in parsed:
                dst = OUTPUT_ROOT / year / "no_launch" / r.path.name
                copy_or_move(r.path, dst, self.logger)
            self.logger.act(f"[no_launch_bundle] {og_bundle_id}")
            self.count_no_launch += 1
            return

        letter = None
        missing_aircraft = False

        if fixed_letter:
            letter = fixed_letter
        elif is_noaa:
            letter_counts = defaultdict(int)
            for r in parsed:
                ltr = resolve_noaa_letter(r.aircraft_type, r.aircraft_id)
                if ltr:
                    letter_counts[ltr] += 1
            if letter_counts:
                letter = sorted(letter_counts.items(), key=lambda kv: (-kv[1], kv[0]))[0][0]
            else:
                missing_aircraft = True

        if is_noaa and missing_aircraft:
            for r in parsed:
                dst = OUTPUT_ROOT / year / "no_aircraft" / r.path.name
                copy_or_move(r.path, dst, self.logger)
            self.logger.err(f"[noaa_no_aircraft] {og_bundle_id} :: diverted {len(parsed)} files to no_aircraft")
            self.count_no_aircraft += len(parsed)
            return

        if not letter:
            letter = "U"
        letter = sanitize_letter(letter)

        earliest_lau_dt = None
        for r in parsed:
            dt = r.lau_dt or r.launch_dt_from_footer or r.earliest_data_dt
            if dt:
                if earliest_lau_dt is None or dt < earliest_lau_dt:
                    earliest_lau_dt = dt

        if earliest_lau_dt is None:
            for r in parsed:
                dst = OUTPUT_ROOT / year / "no_launch" / r.path.name
                copy_or_move(r.path, dst, self.logger)
            self.logger.err(f"[unexpected_no_lau_after_rescue] {og_bundle_id}")
            self.count_no_launch += 1
            return

        ymd = yyyymmdd_from_dt(earliest_lau_dt)
        key = (ymd, letter)
        self.time_index[key].append((earliest_lau_dt, og_bundle_id))
        rank = 1 + sorted(self.time_index[key], key=lambda x: x[0]).index((earliest_lau_dt, og_bundle_id))

        container = f"{ymd}{letter}{rank}_DFILES"
        target = ensure_container(year, container)

        self._add_legacy_aliases_for_container(container)
        self._register_legacy_aliases_from_name(og_bundle_id.split("/")[-1], container)

        self.flight_map[og_bundle_id] = FlightMapEntry(container=container, files={})

        for r in parsed:
            dt = r.lau_dt or r.launch_dt_from_footer or r.earliest_data_dt
            if not dt:
                self.logger.err(f"[file_missing_time] {r.path} in {og_bundle_id}")
                continue
            dt = dt.replace(year=int(ymd[:4]), month=int(ymd[4:6]), day=int(ymd[6:8]))
            dname = build_d_filename(dt, r.channel)
            dst = target / dname
            copy_or_move(r.path, dst, self.logger)
            self.flight_map[og_bundle_id].files[str(r.path)] = dname
            self.dindex[d_stem(yyyymmdd_from_dt(dt), hhmmss_from_dt(dt))] = container

        self.count_classified += 1

    # af grouping / merging

    def classify_af_bundle(self, year: str, campaign: str, parsed: List[FileParseResult], og_bundle_id: str):
        if not parsed:
            self.logger.err(f"[af_empty_bundle] {og_bundle_id}")
            return

        def group_key(r: FileParseResult) -> str:
            tail = (r.aircraft_id or "").strip().upper()
            if tail and tail != "---":
                return tail
            hint = (r.af_code_hint or "").strip().upper()
            if hint:
                return hint
            return ""

        groups_by_key: Dict[str, List[FileParseResult]] = defaultdict(list)
        for r in parsed:
            groups_by_key[group_key(r)].append(r)

        if "" in groups_by_key:
            missing = groups_by_key[""]
            self.logger.err(f"[af_tail_missing] {og_bundle_id} :: diverting {len(missing)} files to no_tail")
            for r in missing:
                dst = OUTPUT_ROOT / year / "no_tail" / r.path.name
                copy_or_move(r.path, dst, self.logger)
            self.count_no_tail += len(missing)
            del groups_by_key[""]

        af_date_counters: Dict[str, int] = defaultdict(int)

        for key_token, files in groups_by_key.items():
            def first_dt(r: FileParseResult) -> datetime:
                return r.lau_dt or r.launch_dt_from_footer or r.earliest_data_dt or r.end_dt or datetime.max
            file_list = sorted(files, key=first_dt)

            current_group: List[FileParseResult] = []
            last_dt: Optional[datetime] = None
            produced_groups: List[List[FileParseResult]] = []

            for r in file_list:
                dt = first_dt(r)
                if last_dt is not None and dt is not None and (dt - last_dt) > timedelta(hours=AF_SPLIT_GAP_HOURS):
                    if current_group:
                        produced_groups.append(current_group)
                    current_group = [r]
                else:
                    current_group.append(r)
                last_dt = dt
            if current_group:
                produced_groups.append(current_group)

            for group in produced_groups:
                group_start = first_dt(group[0])
                if group_start is None or group_start is datetime.max:
                    usable = [x for x in (group[0].lau_dt, group[0].launch_dt_from_footer, group[0].earliest_data_dt, group[0].end_dt) if x]
                    if not usable:
                        self.logger.err(f"[af_group_no_datetime] {og_bundle_id}")
                        continue
                    group_start = usable[0]
                ymd = yyyymmdd_from_dt(group_start)

                af_date_counters[ymd] += 1
                flight_num = af_date_counters[ymd]
                container = f"{ymd}U{flight_num}_DFILES"
                target = ensure_container(year, container)

                self._add_legacy_aliases_for_container(container)
                self._register_legacy_aliases_from_name(og_bundle_id.split("/")[-1], container)

                if og_bundle_id not in self.flight_map:
                    self.flight_map[og_bundle_id] = FlightMapEntry(container=container, files={})
                else:
                    self.flight_map[og_bundle_id].container = container

                i = 0
                while i < len(group):
                    r = group[i]
                    base_dt = r.lau_dt or r.launch_dt_from_footer or r.earliest_data_dt or r.end_dt
                    if not base_dt:
                        i += 1
                        self.logger.err(f"[af_file_missing_time] {r.path} in {og_bundle_id}")
                        continue
                    base_dt = base_dt.replace(year=int(ymd[:4]), month=int(ymd[4:6]), day=int(ymd[6:8]))

                    merged_content: Optional[List[str]] = None
                    merged_sources: List[FileParseResult] = [r]
                    merged_channel = r.channel

                    if i + 1 < len(group):
                        nxt = group[i + 1]
                        same_channel_ok = (not AF_REQUIRE_SAME_CHANNEL_FOR_MERGE) or (r.channel == nxt.channel)
                        if ((not nxt.has_lau_token and nxt.lau_dt is None) and same_channel_ok):
                            prev_last = r.latest_data_dt or r.end_dt
                            nxt_first = nxt.earliest_data_dt
                            if prev_last and nxt_first:
                                delta = nxt_first - prev_last
                                if delta < timedelta(0):
                                    delta = -delta
                                if delta <= timedelta(minutes=AF_MERGE_CONTINUITY_MINUTES):
                                    merged_content = merge_g_files_keep_first_footer(r, nxt, self.logger)
                                    merged_sources.append(nxt)
                                    self.logger.act(f"[af_merge] {r.path.name} + {nxt.path.name} → single d")
                                    i += 1

                    dname = build_d_filename(base_dt, merged_channel)
                    dst = target / dname
                    if merged_content is not None:
                        write_text(dst, merged_content, self.logger)
                    else:
                        copy_or_move(r.path, dst, self.logger)

                    for src in merged_sources:
                        self.flight_map[og_bundle_id].files[str(src.path)] = dname
                    self.dindex[d_stem(yyyymmdd_from_dt(base_dt), hhmmss_from_dt(base_dt))] = container

                    i += 1

                self.count_classified += 1

    # sweep no_tail

    def process_no_tail_folder(self, year: str):
        root = self.output_root / year / "no_tail"
        if not root.exists():
            return
        moved = 0
        for p in sorted(root.iterdir(), key=lambda x: x.name):
            if not p.is_file():
                continue

            if looks_like_index_file(p):
                self.logger.act(f"[skip_index_no_tail] {p}")
                continue

            if is_archive(p):
                temp_root = extract_archive(p, self.staging_root / year, self.logger)
                files = walk_all_files(temp_root)
                if files:
                    og = f"{year}/no_tail/{p.name}"
                    self.classify_af_bundle(
                        year,
                        "AFRES",
                        [parse_sonde_file(f, self.logger, keep_lines=True) for f in files if is_probably_text(f)],
                        og_bundle_id=og
                    )
                    moved += 1
                else:
                    self.logger.err(f"[no_tail_empty_archive] {p}")
                continue

            m = re.match(r"^(D\d{8}_\d{6})", p.name, re.I)
            if m:
                stem = m.group(1).upper()
                container = self.dindex.get(stem)
                if not container:
                    ymd = stem[1:9]
                    letter = "U"
                    key = (ymd, letter)
                    self.time_index[key].append((datetime.strptime(ymd, "%Y%m%d"), stem))
                    rank = 1 + sorted(self.time_index[key], key=lambda x: x[0]).index((datetime.strptime(ymd, "%Y%m%d"), stem))
                    container = f"{ymd}{letter}{rank}_DFILES"
                    self._add_legacy_aliases_for_container(container)
                dst_dir = ensure_container(year, container)
                dst = dst_dir / p.name
                copy_or_move(p, dst, self.logger)
                self.dindex[stem] = container
                moved += 1
                continue

            if is_probably_text(p):
                res = parse_sonde_file(p, self.logger, keep_lines=True)
                og = f"{year}/no_tail/{p.name}"
                self.classify_af_bundle(year, "AFRES", [res], og_bundle_id=og)
                moved += 1
                continue

            dst = self.output_root / year / "to_categorize" / p.name
            copy_or_move(p, dst, self.logger)

        if moved:
            self.logger.act(f"[process_no_tail_folder] year={year} moved_or_classified={moved}")

    # sweep no launch (scientist logs → operproc)

    def _find_longest_legacy_prefix_in_content(self, content: str) -> Tuple[Optional[str], Optional[str]]:
        up = content.upper()
        best_key = None
        best_container = None
        best_len = 0
        for key_up, cont in self.legacy_container_map.items():
            if re.fullmatch(r"\d{8}[A-Z0-9]+\d+", key_up):
                if key_up in up and len(key_up) > best_len:
                    best_key = key_up
                    best_container = cont
                    best_len = len(key_up)
        return best_key, best_container

    def process_scientist_logs_from_no_launch(self, year: str):
        no_launch_dir = self.output_root / year / "no_launch"
        if not no_launch_dir.exists():
            return

        self.logger.act(f"[scan_no_launch_logs] starting for year {year}")
        moved_count = 0

        for p in list(no_launch_dir.iterdir()):
            if not p.is_file():
                continue

            try:
                with p.open("r", encoding="utf-8", errors="ignore") as f:
                    first_line = f.readline()
            except Exception as e:
                self.logger.err(f"[log_scan_read_error] could not read {p}: {e}")
                continue

            if "Dropwindsonde Scientist Log" in first_line:
                self.logger.act(f"[log_scan_found] found scientist log: {p.name}")
                container = None
                op_dir = None
                new_name = p.name

                m = re.match(r"^(D\d{8}_\d{6})", p.name, re.I)
                if m:
                    stem = m.group(1).upper()
                    container = self.dindex.get(stem)
                    if container:
                        op_dir = operproc_dir_name_from_container(container)
                    else:
                        self.logger.err(f"[log_scan_d_fail] d-file log {p.name} has no container in dindex.")
                        continue

                else:
                    content = p.read_text(encoding="utf-8", errors="ignore")
                    _matched_key, container = self._find_longest_legacy_prefix_in_content(content)
                    if container:
                        op_dir = operproc_dir_name_from_container(container)
                        new_name = f"{op_dir}_{p.name}"
                    else:
                        self.logger.err(f"[log_scan_content_fail] could not find mission id in log {p.name}.")
                        continue

                if op_dir:
                    dst = self.output_root / year / "operproc" / op_dir / new_name
                    copy_or_move(p, dst, self.logger)
                    moved_count += 1

        if moved_count > 0:
            self.logger.sum(f"[log_scan_summary] year={year} moved {moved_count} scientist logs from no_launch.")

    # operproc mirroring

    def process_operproc_folder(self, year: str, operproc_dir: Path):
        for p in operproc_dir.rglob("*"):
            if not p.is_file():
                continue

            name = p.name

            if Path(name).stem.lower() == "index":
                self.logger.act(f"[skip_index] {p}")
                continue

            m = re.match(r"^(D\d{8}_\d{6})", name, re.I)
            if m:
                stem = m.group(1).upper()
                container = self.dindex.get(stem)
                if container:
                    op_dir = operproc_dir_name_from_container(container)
                    dst = self.output_root / year / "operproc" / op_dir / name
                    copy_or_move(p, dst, self.logger)
                    self.count_operproc_placed += 1
                    continue

            lm = LEADING_CONTAINER_TOKEN.match(name)
            if lm:
                ymd = lm.group("date")
                letter = sanitize_letter(lm.group("letter"))
                num = int(lm.group("num"))
                for k, v in NAME_SWAPS.items():
                    if letter.upper().startswith(k):
                        letter = v + letter[len(k):]
                        break
                container = f"{ymd}{letter}{num}_DFILES"
                op_dir = operproc_dir_name_from_container(container)
                new_name = op_dir + name[lm.end():]
                dst = self.output_root / year / "operproc" / op_dir / new_name
                copy_or_move(p, dst, self.logger)
                self.count_operproc_placed += 1
                continue

            matched_key_up, container = self._find_longest_legacy_prefix(name)
            if container:
                op_dir = operproc_dir_name_from_container(container)
                new_name = op_dir + name[len(matched_key_up):]
                dst = self.output_root / year / "operproc" / op_dir / new_name
                copy_or_move(p, dst, self.logger)
                self.count_operproc_placed += 1
                continue

            cm = container_regex().search(name)
            if cm:
                ymd = cm.group("date")
                letter = sanitize_letter(cm.group("letter"))
                num = int(cm.group("num"))
                for k, v in NAME_SWAPS.items():
                    if letter.upper().startswith(k):
                        letter = v + letter[len(k):]
                        break
                container = f"{ymd}{letter}{num}_DFILES"
                op_dir = operproc_dir_name_from_container(container)
                token = f"{ymd}{letter}{num}_DFILES"
                new_name = op_dir + name[len(token):] if name.upper().startswith(token.upper()) else name
                dst = self.output_root / year / "operproc" / op_dir / new_name
                copy_or_move(p, dst, self.logger)
                self.count_operproc_placed += 1
                continue

            dst = self.output_root / year / "to_categorize" / name
            copy_or_move(p, dst, self.logger)
            self.count_operproc_uncategorized += 1

    # salvage pass

    def salvage_to_categorize(self, year: str):
        tc_dir = self.output_root / year / "to_categorize"
        if not tc_dir.exists():
            return
        moved = 0
        for p in sorted(tc_dir.iterdir(), key=lambda x: x.name):
            if not p.is_file():
                continue

            name = p.name

            m = re.match(r"^(D\d{8}_\d{6})", name, re.I)
            if m:
                stem = m.group(1).upper()
                container = self.dindex.get(stem)
                if container:
                    op_dir = operproc_dir_name_from_container(container)
                    dst = self.output_root / year / "operproc" / op_dir / name
                    copy_or_move(p, dst, self.logger)
                    moved += 1
                    continue

            lm = LEADING_CONTAINER_TOKEN.match(name)
            if lm:
                ymd = lm.group("date")
                letter = sanitize_letter(lm.group("letter"))
                num = int(lm.group("num"))
                for k, v in NAME_SWAPS.items():
                    if letter.upper().startswith(k):
                        letter = v + letter[len(k):]
                        break
                container = f"{ymd}{letter}{num}_DFILES"
                op_dir = operproc_dir_name_from_container(container)
                new_name = op_dir + name[lm.end():]
                dst = self.output_root / year / "operproc" / op_dir / new_name
                copy_or_move(p, dst, self.logger)
                moved += 1
                continue

            matched_key_up, container = self._find_longest_legacy_prefix(name)
            if container:
                op_dir = operproc_dir_name_from_container(container)
                new_name = op_dir + name[len(matched_key_up):]
                dst = self.output_root / year / "operproc" / op_dir / new_name
                copy_or_move(p, dst, self.logger)
                moved += 1
                continue

            cm = container_regex().search(name)
            if cm:
                ymd = cm.group("date")
                letter = sanitize_letter(cm.group("letter"))
                num = int(cm.group("num"))
                for k, v in NAME_SWAPS.items():
                    if letter.upper().startswith(k):
                        letter = v + letter[len(k):]
                        break
                container = f"{ymd}{letter}{num}_DFILES"
                op_dir = operproc_dir_name_from_container(container)
                token = f"{ymd}{letter}{num}_DFILES"
                new_name = op_dir + name[len(token):] if name.upper().startswith(token.upper()) else name
                dst = self.output_root / year / "operproc" / op_dir / new_name
                copy_or_move(p, dst, self.logger)
                moved += 1
                continue

        if moved:
            self.logger.act(f"[salvage_to_categorize] year={year} moved={moved}")

    # reconciliation & dumps

    def write_maps_and_summary(self):
        ts = datetime.now(pytz.UTC).strftime("%Y%m%dT%H%M%SZ")
        fmap_path = self.errors_root / self.logger.root.name / "logs" / f"flight_folder_map_{ts}.txt"
        with fmap_path.open("w", encoding="utf-8") as f:
            for og, entry in self.flight_map.items():
                f.write(f"[{og}] → {entry.container}\n")
                for src, dname in entry.files.items():
                    f.write(f"  {src} → {dname}\n")

        dindex_path = self.errors_root / self.logger.root.name / "logs" / f"dindex_{ts}.txt"
        with dindex_path.open("w", encoding="utf-8") as f:
            for stem, container in sorted(self.dindex.items()):
                f.write(f"{stem} → {container}\n")

        aliases_path = self.errors_root / self.logger.root.name / "logs" / f"legacy_container_aliases_{ts}.txt"
        with aliases_path.open("w", encoding="utf-8") as f:
            for k, v in sorted(self.legacy_container_map.items()):
                f.write(f"{k} -> {v}\n")

        self.logger.sum(f"[summary] input_files_seen={self.count_input_files}")
        self.logger.sum(f"[summary] classified_bundles={self.count_classified}")
        self.logger.sum(f"[summary] no_launch_bundles={self.count_no_launch}")
        self.logger.sum(f"[summary] operproc_placed={self.count_operproc_placed}")
        self.logger.sum(f"[summary] operproc_uncategorized={self.count_operproc_uncategorized}")
        self.logger.sum(f"[summary] raw_no_tail={self.count_no_tail}")
        self.logger.sum(f"[summary] raw_no_aircraft={self.count_no_aircraft}")

    #
    # g-file merge helper (keep first footer)
    #

    # (unchanged)
    # -------------------------------------------------------------------------

# keep these helpers outside class (they're used above)
def split_at_footer(lines: List[str]) -> Tuple[List[str], List[str]]:
    end_idx = -1
    for i, ln in enumerate(lines):
        if END_RE.search(ln):
            end_idx = i
            break
    if end_idx == -1:
        return lines, []
    return lines[:end_idx], lines[end_idx:]

def merge_g_files_keep_first_footer(first: FileParseResult, second: FileParseResult, logger: Logger) -> List[str]:
    l1 = first.raw_lines or []
    l2 = second.raw_lines or []
    body1, foot1 = split_at_footer(l1)
    body2, _ = split_at_footer(l2)
    merged = []
    merged.extend(body1)
    merged.extend(body2)
    merged.extend(foot1)
    logger.act(f"[merge_content] kept first footer from {first.path.name}")
    return merged

#
# AF-130 post-pass: group, convert to D, insert between existing flights, renumber
#

AF130_KEYS = ("AF-130", "AF130", "WC-130", "WC130", "C-130", "C130")

def _is_af130(r: FileParseResult) -> bool:
    t = (r.aircraft_type or "").upper()
    i = (r.aircraft_id or "").upper()
    s = (r.project_or_mission or "").upper()
    combo = " ".join((t, i, s))
    return any(k in combo for k in AF130_KEYS)

def _container_start_dt_from_dir(container_dir: Path) -> Optional[datetime]:
    times = []
    for f in container_dir.glob("D????????_??????*"):
        m = re.match(r"^D(\d{8})_(\d{6})", f.name)
        if m:
            try:
                dt = datetime.strptime(m.group(1) + m.group(2), "%Y%m%d%H%M%S")
                times.append(dt)
            except Exception:
                pass
    return min(times) if times else None

def _list_day_flights(output_root: Path, year: str, ymd: str) -> List[Tuple[int, str, datetime]]:
    root = output_root / year / "raw"
    out = []
    pat = re.compile(rf"^{ymd}U(\d+)_DFILES$", re.I)
    if root.exists():
        for d in root.iterdir():
            if not d.is_dir():
                continue
            m = pat.match(d.name)
            if not m:
                continue
            num = int(m.group(1))
            start = _container_start_dt_from_dir(d)
            if start:
                out.append((num, d.name, start))
    out.sort(key=lambda t: t[0])
    return out

def _shift_day_flights(output_root: Path, logger: Logger, dindex: Dict[str, str], ymd: str, year: str, start_from_num: int):
    raw_root = output_root / year / "raw"
    op_root  = output_root / year / "operproc"
    flights = _list_day_flights(output_root, year, ymd)
    for num, cont, _ in sorted(flights, key=lambda x: x[0], reverse=True):
        if num < start_from_num:
            continue
        old_cont = cont
        new_cont = f"{ymd}U{num+1}_DFILES"
        # raw rename
        (raw_root / old_cont).rename(raw_root / new_cont)
        # operproc rename
        old_op = operproc_dir_name_from_container(old_cont)
        new_op = operproc_dir_name_from_container(new_cont)
        old_op_dir = op_root / old_op
        if old_op_dir.exists():
            old_op_dir.rename(op_root / new_op)
        # fix internal file name prefixes
        op_dir = op_root / new_op
        if op_dir.exists():
            for f in op_dir.iterdir():
                if f.is_file() and f.name.startswith(old_op):
                    f.rename(op_dir / (new_op + f.name[len(old_op):]))
        # update dindex
        for stem, c in list(dindex.items()):
            if c == old_cont:
                dindex[stem] = new_cont
        logger.act(f"[renumber] {old_cont} → {new_cont}")

def post_insert_af130(logger: Logger, org: AvapsOrganizer, year: str, search_roots: Optional[List[Path]] = None):
    roots = search_roots or [
        OUTPUT_ROOT / year / "no_tail",
        OUTPUT_ROOT / year / "no_aircraft",
        OUTPUT_ROOT / year / "to_categorize",
    ]
    candidates: List[FileParseResult] = []
    for root in roots:
        if not root.exists():
            continue
        for p in root.iterdir():
            if not p.is_file():
                continue
            r = parse_sonde_file(p, logger, keep_lines=True)
            if _is_af130(r) and (r.lau_dt or r.launch_dt_from_footer or r.earliest_data_dt):
                candidates.append(r)

    if not candidates:
        logger.act(f"[af130_post] year={year} nothing found")
        return

    def first_dt(r: FileParseResult) -> datetime:
        return r.lau_dt or r.launch_dt_from_footer or r.earliest_data_dt or r.end_dt

    by_day: Dict[str, List[FileParseResult]] = defaultdict(list)
    for r in candidates:
        dt = first_dt(r)
        by_day[dt.strftime("%Y%m%d")].append(r)

    for ymd, items in by_day.items():
        items.sort(key=first_dt)

        groups: List[List[FileParseResult]] = []
        cur: List[FileParseResult] = []
        last: Optional[datetime] = None
        for r in items:
            dt = first_dt(r)
            if last and (dt - last) > timedelta(hours=AF_SPLIT_GAP_HOURS):
                if cur: groups.append(cur)
                cur = [r]
            else:
                cur.append(r)
            last = dt
        if cur: groups.append(cur)

        existing = _list_day_flights(OUTPUT_ROOT, year, ymd)

        for grp in groups:
            start_dt = first_dt(grp[0]).replace(year=int(ymd[:4]), month=int(ymd[4:6]), day=int(ymd[6:8]))

            insert_idx = 1
            for k, (_, _, t) in enumerate(existing, start=1):
                if start_dt > t:
                    insert_idx = k + 1

            if existing and insert_idx <= len(existing):
                _shift_day_flights(OUTPUT_ROOT, logger, org.dindex, ymd, year, start_from_num=insert_idx)
                existing = _list_day_flights(OUTPUT_ROOT, year, ymd)

            container = f"{ymd}U{insert_idx}_DFILES"
            target = ensure_container(year, container)
            org._add_legacy_aliases_for_container(container)

            if f"{ymd}U{insert_idx}_DFILES" not in [c for _, c, _ in existing]:
                existing.insert(insert_idx-1, (insert_idx, container, start_dt))

            # convert and place D files
            for r in grp:
                dt = first_dt(r).replace(year=int(ymd[:4]), month=int(ymd[4:6]), day=int(ymd[6:8]))
                dname = build_d_filename(dt, r.channel)
                dst = target / dname
                copy_or_move(r.path, dst, logger)
                org.dindex[d_stem(ymd, hhmmss_from_dt(dt))] = container
                if "af130_post" not in org.flight_map:
                    org.flight_map["af130_post"] = FlightMapEntry(container=container, files={})
                org.flight_map["af130_post"].files[str(r.path)] = dname

            logger.act(f"[af130_insert] {container} size={len(grp)} inserted_at={insert_idx}")

#
# main
#

def main():
    print('start')
    OUTPUT_ROOT.mkdir(parents=True, exist_ok=True)
    STAGING_ROOT.mkdir(parents=True, exist_ok=True)
    ERRORS_ROOT.mkdir(parents=True, exist_ok=True)

    logger = Logger(ERRORS_ROOT)
    try:
        org = AvapsOrganizer(INPUT_ROOT, OUTPUT_ROOT, STAGING_ROOT, ERRORS_ROOT, logger)
        org.run()

        # after the first pass, run AF-130 insertion for all processed years
        for y in org.processed_years:
            post_insert_af130(logger, org, y)

    finally:
        logger.close()

    print('done')


main()
