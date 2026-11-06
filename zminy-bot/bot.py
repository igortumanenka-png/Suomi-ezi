"""Стежить за графіком змін у Google-таблиці для кількох людей і пише в Telegram.

Таблиця - графік: у колонці A імена, угорі рядок із числами днів
(і над ним дні тижня: Ma Ti Ke To Pe La Su), десь угорі назва місяця
("Lokakuu / October 2026"). У клітинках - зміна людини на цей день (HAK6, V, 13-21...).
Кожен період - окрема вкладка з місяцем і роком у назві; бот сам знаходить
вкладки від минулого місяця до +3 місяців і читає їх усі.

Що робить бот:
  * тримає в каналі один великий пост з графіком PEOPLE - картинкою в кольорах
    таблиці (колір = місце роботи, PLACES) - і оновлює його, коли графік чи
    кольори змінюються (і опівночі); без кольорів чи Pillow - текстом;
  * кожні CHECK_MINUTES хвилин читає таблицю і, якщо в когось із PEOPLE
    щось додали чи змінили (на сьогодні й далі), одразу пише про це;
  * щовечора о SEND_HOUR надсилає зміни всіх PEOPLE на завтра.
  Сповіщення (зміни, "на завтра") не накопичуються: нове видаляє попереднє.
  * в особистих повідомленнях власник керує списком: надсилає ім'я з таблиці -
    бот починає стежити; /list - список із кнопками, щоб прибрати.

`python bot.py`             - працювати постійно
`python bot.py --now`       - одразу надіслати повідомлення на завтра
`python bot.py --check`     - показати вкладки й графік, як їх бачить бот (нічого не надсилає)
`python bot.py --find-chat` - показати ID груп/каналів, куди додали бота

Налаштування - файл .env поруч із bot.py (див. README.md):
  TELEGRAM_TOKEN   токен бота від @BotFather            (обов'язково)
  CHAT_ID          id групи / каналу                     (обов'язково)
  SHEET_URL        посилання на Google-таблицю           (обов'язково)
  PEOPLE           початковий список: імена через ";", як у колонці A; після "="
                   коротке ім'я для поста: Virtanen Matti=Matti; ... Далі список
                   живе в state.json і змінюється через бота в особистих.
  ADMINS           Telegram ID власників через ","; без нього власником стає
                   перший, хто напише боту /start
  SEND_HOUR        година вечірнього повідомлення, за замовчуванням 20
  CHECK_MINUTES    як часто перевіряти таблицю, за замовчуванням 5
"""

from __future__ import annotations

import csv
import difflib
import hashlib
import html
import io
import json
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
import zipfile
from datetime import date, datetime, timedelta
from pathlib import Path
from xml.etree import ElementTree

import picture

HERE = Path(__file__).resolve().parent
ENV_FILE = HERE / ".env"
STATE_FILE = HERE / "state.json"
TABS_EVERY = 3600  # як часто (с) перечитувати список вкладок
TABS_WINDOW = (-1, 3)  # які вкладки читати: місяці відносно поточного
TELEGRAM_LIMIT = 4000  # символів в одному повідомленні (у Telegram межа 4096)
BOARD_DAYS = 42  # скільки днів наперед показує великий пост
POLL_SECONDS = 50  # скільки чекати нових повідомлень боту за один запит до Telegram
BOARD_WEEKS = 3  # скільки тижнів на картинці з графіком

# Колір клітинки в таблиці = місце роботи (Owner, 2026-11-06). Червоний не вживають.
PLACES = {"9900ff": "холодний цех", "14bf5c": "теплий цех", "f1c232": "Сілок"}
DAY_OFF_COLOR = "00b0f0"  # блакитна "V" у легенді, якщо в таблиці V не знайшлось
COLOR_EMOJI = {
    "🟪": "9900ff", "🟩": "14bf5c", "🟨": "f1c232", "🟥": "ea4335", "🟦": "00b0f0", "🟧": "ff9900", "🟫": "8b5a2b",
}

WEEKDAYS_UA = ["пн", "вт", "ср", "чт", "пт", "сб", "нд"]
# Перші дві літери дня тижня у шапці таблиці -> номер дня (0 = понеділок).
WEEKDAY_HEADERS = {
    "ma": 0, "ti": 1, "ke": 2, "to": 3, "pe": 4, "la": 5, "su": 6,  # suomi
    "mo": 0, "tu": 1, "we": 2, "th": 3, "fr": 4, "sa": 5,  # english
    "пн": 0, "вт": 1, "ср": 2, "чт": 3, "пт": 4, "сб": 5, "нд": 6,  # українська
}
MONTHS = {
    name: number
    for number, names in enumerate(
        [
            ("tammikuu", "january", "січень"),
            ("helmikuu", "february", "лютий"),
            ("maaliskuu", "march", "березень"),
            ("huhtikuu", "april", "квітень"),
            ("toukokuu", "may", "травень"),
            ("kesäkuu", "june", "червень"),
            ("heinäkuu", "july", "липень"),
            ("elokuu", "august", "серпень"),
            ("syyskuu", "september", "вересень"),
            ("lokakuu", "october", "жовтень"),
            ("marraskuu", "november", "листопад"),
            ("joulukuu", "december", "грудень"),
        ],
        start=1,
    )
    for name in names
}


# --- налаштування -----------------------------------------------------------

def load_env(path: Path) -> None:
    """Читає KEY=VALUE з .env у змінні середовища (уже задані не перезаписує)."""
    if not path.exists():
        return
    for line in path.read_text(encoding="utf-8-sig").splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        os.environ.setdefault(key.strip(), value.strip().strip('"').strip("'"))


def people_from(text: str) -> list[str]:
    """Повні імена з PEOPLE (без коротких імен після "=")."""
    return list(short_names(text))


def short_names(text: str) -> dict[str, str]:
    """{"Virtanen Matti": "Matti", ...}; без "=" коротке ім'я - перше слово."""
    names = {}
    for item in re.split(r"[;\n]", text):
        name, _, short = item.partition("=")
        if name.strip():
            names[name.strip()] = short.strip() or name.split()[0]
    return names


# --- таблиця ----------------------------------------------------------------

def csv_url(sheet_url: str) -> str:
    """Перетворює звичайне посилання на таблицю в посилання на CSV-вивантаження."""
    if "output=csv" in sheet_url or "format=csv" in sheet_url:
        return sheet_url
    match = re.search(r"/spreadsheets/d/([a-zA-Z0-9_-]+)", sheet_url)
    if not match:
        raise ValueError(f"Не схоже на посилання на Google-таблицю: {sheet_url}")
    gid = re.search(r"[#&?]gid=(\d+)", sheet_url)
    url = f"https://docs.google.com/spreadsheets/d/{match.group(1)}/export?format=csv"
    return url + (f"&gid={gid.group(1)}" if gid else "")


def sheet_id(sheet_url: str) -> str:
    return re.search(r"/spreadsheets/d/([a-zA-Z0-9_-]+)", sheet_url).group(1)


def fetch(url: str) -> str:
    with urllib.request.urlopen(url, timeout=60) as response:
        return response.read().decode("utf-8-sig")


def download(url: str) -> str:
    """CSV однієї вкладки."""
    text = fetch(url)
    if text.lstrip().lower().startswith(("<!doctype", "<html")):
        raise RuntimeError("Google віддав сторінку входу, а не таблицю - відкрийте доступ за посиланням.")
    return text


def _js_unescape(text: str) -> str:
    def one(m: re.Match) -> str:
        code = m.group(1) or m.group(2)
        return chr(int(code, 16)) if code else m.group(3)

    return re.sub(r"\\x([0-9a-fA-F]{2})|\\u([0-9a-fA-F]{4})|\\(.)", one, text)


def tabs_from_html(page: str) -> list[tuple[str, str]]:
    """(назва, gid) усіх вкладок зі сторінки .../htmlview."""
    tabs: dict[str, str] = {}
    for name, gid in re.findall(r'name:\s*"((?:[^"\\]|\\.)*)"[^{}]*?gid:\s*"(\d+)"', page):
        tabs[gid] = _js_unescape(name).strip()
    for gid, name in re.findall(r'id="sheet-button-(\d+)"[^>]*>(?:\s*<a[^>]*>)?([^<]+)<', page):
        tabs.setdefault(gid, html.unescape(name).strip())
    return [(name, gid) for gid, name in tabs.items()]


def tab_month(title: str) -> tuple[int, int] | None:
    """"Lokakuu / October 2026" -> (2026, 10); без місяця чи року - None."""
    year = re.search(r"(20\d\d)", title)
    month = next((MONTHS[w] for w in re.findall(r"[^\W\d_]+", title.lower()) if w in MONTHS), None)
    return (int(year.group(1)), month) if year and month else None


def pick_tabs(tabs: list[tuple[str, str]], today: date) -> list[tuple[str, str]]:
    """Вкладки від минулого місяця до +3 місяців, по порядку."""
    now = today.year * 12 + today.month - 1
    picked = []
    for title, gid in tabs:
        ym = tab_month(title)
        if ym and TABS_WINDOW[0] <= ym[0] * 12 + ym[1] - 1 - now <= TABS_WINDOW[1]:
            picked.append((ym, title, gid))
    return [(title, gid) for _, title, gid in sorted(picked)]


def name_key(name: str) -> tuple[str, ...]:
    """"Virtanen Matti", "matti  virtanen" -> однаковий ключ."""
    return tuple(sorted(name.lower().split()))


def _day_number(cell: str) -> int | None:
    cell = cell.strip().rstrip(".")
    return int(cell) if cell.isdigit() and 1 <= int(cell) <= 31 else None


def _shift_month(year: int, month: int, by: int) -> tuple[int, int]:
    index = year * 12 + (month - 1) + by
    return index // 12, index % 12 + 1


def column_dates(rows: list[list[str]], today: date) -> dict[int, date]:
    """Номер колонки -> дата. Рядок днів - той, де найбільше чисел 1..31."""
    best_row, best_cols = -1, {}
    for r, row in enumerate(rows[:10]):
        cols = {c: d for c, cell in enumerate(row) if c > 0 and (d := _day_number(cell))}
        if len(cols) > len(best_cols):
            best_row, best_cols = r, cols
    if len(best_cols) < 3:
        raise ValueError("Не знайшов у таблиці рядок із числами днів.")

    month, year_hint = None, None
    for row in rows[: best_row + 1]:
        for cell in row:
            for word in re.findall(r"[^\W\d_]+", cell.lower()):
                month = month or MONTHS.get(word)
            if not year_hint and (found := re.search(r"\b(20\d\d)\b", cell)):
                year_hint = int(found.group(1))
    month = month or today.month
    years = (year_hint,) if year_hint else (today.year - 1, today.year, today.year + 1)

    weekdays = {}
    if best_row > 0:
        for c, cell in enumerate(rows[best_row - 1]):
            if (wd := WEEKDAY_HEADERS.get(cell.strip().lower()[:2])) is not None:
                weekdays[c] = wd

    # Числа йдуть підряд; коли число зменшилось - почався наступний місяць. Таблиця
    # може починатися з кінця попереднього місяця, а рік не написаний - тож пробуємо
    # варіанти і беремо той, що збігається з днями тижня й найближчий до сьогодні.
    best, best_score = {}, None
    for start_shift in (0, -1):
        for year in years:
            y, m = _shift_month(year, month, start_shift)
            result, prev = {}, 0
            try:
                for c in sorted(best_cols):
                    if best_cols[c] < prev:
                        y, m = _shift_month(y, m, 1)
                    prev = best_cols[c]
                    result[c] = date(y, m, best_cols[c])
            except ValueError:  # 31 вересня тощо - варіант неправильний
                continue
            matches = sum(result[c].weekday() == wd for c, wd in weekdays.items() if c in result)
            distance = min(abs((d - today).days) for d in result.values())
            score = (matches, start_shift == 0, -distance)
            if best_score is None or score > best_score:
                best, best_score = result, score
    return best


XLSX_NS = "{http://schemas.openxmlformats.org/spreadsheetml/2006/main}"
XLSX_REL = "{http://schemas.openxmlformats.org/officeDocument/2006/relationships}id"


def fetch_bytes(url: str) -> bytes:
    with urllib.request.urlopen(url, timeout=120) as response:
        return response.read()


def _cell_column(ref: str) -> int:
    """"AC82" -> 28 (з нуля)."""
    number = 0
    for ch in re.match(r"[A-Z]+", ref).group():
        number = number * 26 + ord(ch) - 64
    return number - 1


def read_xlsx(data: bytes, months: set[tuple[int, int]]) -> dict[str, list[list[tuple[str, str]]]]:
    """{вкладка: рядки клітинок (значення, колір фону "rrggbb" або "")} - лише вкладки цих місяців.

    Вкладку шукаємо за місяцем і роком у назві, а не за точною назвою: в Excel
    у назві не буває "/", тож "Lokakuu / October 2026" у файлі називається інакше.
    """
    book = zipfile.ZipFile(io.BytesIO(data))
    workbook = ElementTree.fromstring(book.read("xl/workbook.xml"))
    rels = ElementTree.fromstring(book.read("xl/_rels/workbook.xml.rels"))
    targets = {rel.get("Id"): rel.get("Target") for rel in rels}
    shared = []
    if "xl/sharedStrings.xml" in book.namelist():
        for item in ElementTree.fromstring(book.read("xl/sharedStrings.xml")).iter(f"{XLSX_NS}si"):
            shared.append("".join(t.text or "" for t in item.iter(f"{XLSX_NS}t")))
    styles = ElementTree.fromstring(book.read("xl/styles.xml"))
    fills = []
    fills_node, xfs_node = styles.find(f"{XLSX_NS}fills"), styles.find(f"{XLSX_NS}cellXfs")
    for fill in fills_node if fills_node is not None else []:
        pattern = fill.find(f"{XLSX_NS}patternFill")
        color = ""
        if pattern is not None and pattern.get("patternType") not in (None, "none"):
            fg = pattern.find(f"{XLSX_NS}fgColor")
            if fg is not None and fg.get("rgb"):
                color = fg.get("rgb")[-6:].lower()
        fills.append(color)
    style_fill = [int(xf.get("fillId", 0)) for xf in (xfs_node if xfs_node is not None else [])]

    tabs = {}
    for sheet in workbook.iter(f"{XLSX_NS}sheet"):
        title = sheet.get("name")
        if tab_month(title) not in months:
            continue
        target = targets[sheet.get(XLSX_REL)]
        root = ElementTree.fromstring(book.read(target.lstrip("/") if target.startswith("/") else "xl/" + target))
        grid: list[list[tuple[str, str]]] = []
        for row in root.iter(f"{XLSX_NS}row"):
            r = int(row.get("r")) - 1
            while len(grid) <= r:
                grid.append([])
            cells = grid[r]
            for cell in row.iter(f"{XLSX_NS}c"):
                col = _cell_column(cell.get("r"))
                while len(cells) <= col:
                    cells.append(("", ""))
                kind, v = cell.get("t"), cell.find(f"{XLSX_NS}v")
                if kind == "s" and v is not None:
                    value = shared[int(v.text)]
                elif kind == "inlineStr":
                    value = "".join(t.text or "" for t in cell.iter(f"{XLSX_NS}t"))
                else:
                    value = v.text if v is not None and v.text else ""
                if re.fullmatch(r"\d+\.0", value):
                    value = value[:-2]
                style = int(cell.get("s", 0))
                fill = style_fill[style] if style < len(style_fill) else 0
                cells[col] = (value, fills[fill] if fill < len(fills) else "")
        tabs[title] = grid
    return tabs


def read_colors(grid: list[list[tuple[str, str]]], people: list[str], today: date) -> dict[str, dict[str, str]]:
    """{ім'я: {"2026-11-09": "9900ff"}} - колір лише там, де в клітинці щось стоїть."""
    dates = column_dates([[value for value, _ in row] for row in grid], today)
    wanted = {name_key(p): p for p in people}
    found: dict[str, dict[str, str]] = {}
    for row in grid:
        person = wanted.get(name_key(row[0][0])) if row else None
        if person and person not in found:
            found[person] = {
                d.isoformat(): (row[c][1] if c < len(row) and row[c][0].strip() and row[c][1] != "ffffff" else "")
                for c, d in dates.items()
            }
    return found


def _distance(a: str, b: str) -> int:
    return sum(abs(x - y) for x, y in zip(picture._rgb(a), picture._rgb(b)))


def place_of(color: str) -> str | None:
    """Місце роботи за кольором клітинки (найближчий з PLACES)."""
    if not color:
        return None
    best = min(PLACES, key=lambda known: _distance(color, known))
    return PLACES[best] if _distance(color, best) <= 90 else None


def emoji_of(color: str) -> str:
    if not color:
        return ""
    best = min(COLOR_EMOJI, key=lambda e: _distance(color, COLOR_EMOJI[e]))
    return best if _distance(color, COLOR_EMOJI[best]) <= 150 else ""


def names_in_table(table: str) -> set[str]:
    """Усі імена з колонки A вкладки (рядки без цифр - шапку з місяцем пропускаємо)."""
    names = set()
    for row in csv.reader(io.StringIO(table)):
        name = " ".join(row[0].split()) if row else ""
        if name and not any(ch.isdigit() for ch in name):
            names.add(name)
    return names


def find_person(names: set[str], query: str) -> tuple[str | None, list[str]]:
    """Ім'я з таблиці, яке шукають, або до трьох схожих (без різниці регістру й порядку слів)."""
    by_key = {name_key(n): n for n in names}
    wanted = name_key(query)
    if wanted in by_key:
        return by_key[wanted], []
    words = set(wanted)
    containing = sorted(n for k, n in by_key.items() if words and words <= set(k))
    keys = {" ".join(k): n for k, n in by_key.items()}
    close = [keys[k] for k in difflib.get_close_matches(" ".join(wanted), keys, n=3, cutoff=0.6)]
    return None, list(dict.fromkeys(containing + close))[:3]


def read_schedule(table: str, people: list[str], today: date) -> dict[str, dict[str, str]]:
    """{ім'я: {"2026-10-09": "HAK6", ...}} для тих із people, хто є в таблиці."""
    rows = list(csv.reader(io.StringIO(table)))
    dates = column_dates(rows, today)
    wanted = {name_key(p): p for p in people}
    found: dict[str, dict[str, str]] = {}
    for row in rows:
        if not row:
            continue
        person = wanted.get(name_key(row[0]))
        if person and person not in found:
            found[person] = {
                d.isoformat(): (row[c].strip() if c < len(row) else "") for c, d in dates.items()
            }
    return found


# --- повідомлення -----------------------------------------------------------

def _day_label(day: date) -> str:
    return f"{WEEKDAYS_UA[day.weekday()]} {day:%d.%m}"


def find_changes(old: dict, new: dict, today: date) -> list[tuple[str, date, str, str]]:
    """(ім'я, дата, було, стало) - лише на сьогодні й далі, лише для вже відомих людей.

    Дата, якої немає в новій таблиці (наприклад, прибрали минулий місяць), - не зміна.
    """
    changes = []
    for person, days in new.items():
        if person not in old:
            continue  # уперше бачимо людину - просто запам'ятовуємо
        for day_text, value in sorted(days.items()):
            day = date.fromisoformat(day_text)
            if day < today:
                continue
            before = old[person].get(day_text, "")
            if value != before:
                changes.append((person, day, before, value))
    return changes


def _value(value: str | None, color: str = "") -> str:
    """Значення для картки: моноширинне; вихідний (V - vapaa) - з пальмою; колір = місце роботи."""
    if value is None:
        return "<i>ще немає в таблиці</i>"
    if not value:
        return "—"
    if value.lower() == "v":
        return f"🌴 <code>{html.escape(value)}</code>"
    place = place_of(color)
    mark = emoji_of(color)
    return (f"{mark} " if mark else "") + f"<code>{html.escape(value)}</code>" + (f" {place}" if place else "")


def _tree(lines: list[str]) -> list[str]:
    return [("└ " if i == len(lines) - 1 else "├ ") + line for i, line in enumerate(lines)]


def _day_card(title: str, day: date, schedule: dict, short: dict[str, str], colors: dict | None = None) -> list[str]:
    if all(person in schedule and schedule[person].get(day.isoformat()) == "" for person in short):
        return [f"{title} · {_day_label(day)}", "└ ні в кого нічого не стоїть"]
    colors = colors or {}
    rows = []
    for person, name in short.items():
        color = colors.get(person, {}).get(day.isoformat(), "")
        value = _value(schedule[person].get(day.isoformat()), color) if person in schedule else "<i>немає в таблиці</i>"
        rows.append(f"{html.escape(name)} · {value}")
    return [f"{title} · {_day_label(day)}"] + _tree(rows)


def changes_message(changes: list[tuple[str, date, str, str]], short: dict[str, str] | None = None,
                    colors: dict | None = None, moves: list[tuple] | None = None) -> str:
    short, colors = short or {}, colors or {}
    order = {person: i for i, person in enumerate(short)}  # як у PEOPLE
    lines = ["✏️ <b>Зміни в графіку</b>"]
    by_person: dict[str, list[str]] = {}
    for person, day, before, after in sorted(changes, key=lambda c: (order.get(c[0], len(order)), c[0], c[1])):
        new = _value(after, colors.get(person, {}).get(day.isoformat(), "")) if after else ""
        if not before:
            what = f"➕ {new}"
        elif not after:
            what = f"➖ <s>{html.escape(before)}</s>"
        else:
            what = f"<s>{html.escape(before)}</s> → {new}"
        by_person.setdefault(person, []).append(f"{_day_label(day)} · {what}")
    for person, day, value, before_color, after_color in moves or []:
        by_person.setdefault(person, []).append(
            f"{_day_label(day)} · <code>{html.escape(value)}</code>: "
            f"<s>{_place_label(before_color)}</s> → <b>{_place_label(after_color)}</b>"
        )
    for person, rows in by_person.items():
        lines += ["", f"👤 <b>{html.escape(short.get(person, person))}</b>"] + _tree(rows)
    return "\n".join(lines)


def split_message(text: str, limit: int = TELEGRAM_LIMIT) -> list[str]:
    """Ділить довгий текст по рядках на шматки, що влазять у повідомлення Telegram."""
    parts, current = [], ""
    for line in text.split("\n"):
        if current and len(current) + 1 + len(line) > limit:
            parts.append(current)
            current = line
        else:
            current = f"{current}\n{line}" if current else line
    return parts + [current] if current else parts


def tomorrow_message(schedule: dict, short: dict[str, str], tomorrow: date, colors: dict | None = None) -> str:
    return "\n".join(_day_card("🌙 <b>Завтра</b>", tomorrow, schedule, short, colors))


def find_moves(old_colors: dict, new_colors: dict, old: dict, new: dict, today: date) -> list[tuple]:
    """(ім'я, дата, значення, був колір, став колір): той самий запис, але інше місце роботи."""
    moves = []
    for person, days in new_colors.items():
        for day_text, color in sorted(days.items()):
            before = old_colors.get(person, {}).get(day_text)
            value = new.get(person, {}).get(day_text, "")
            if (before and color and before != color and date.fromisoformat(day_text) >= today
                    and value and value == old.get(person, {}).get(day_text)
                    and (place_of(before) or emoji_of(before)) != (place_of(color) or emoji_of(color))):
                moves.append((person, date.fromisoformat(day_text), value, before, color))
    return moves


def _place_label(color: str) -> str:
    return " ".join(x for x in (emoji_of(color), place_of(color) or "") if x) or "інший колір"


def board_caption(schedule: dict, short: dict[str, str], today: date, colors: dict) -> str:
    """Підпис під картинкою: сьогодні, завтра і що означають кольори."""
    lines = ["📋 <b>Графік змін</b>", ""]
    lines += _day_card("🟢 <b>Сьогодні</b>", today, schedule, short, colors) + [""]
    lines += _day_card("🔜 <b>Завтра</b>", today + timedelta(days=1), schedule, short, colors)
    legend = " · ".join(f"{emoji_of(color)} {name}" for color, name in PLACES.items()) + " · 🌴 V вихідний"
    return "\n".join(lines + ["", f"<i>{legend}</i>"])


def board_legend(colors: dict, schedule: dict) -> list[tuple[str, str]]:
    day_off = next((colors.get(p, {}).get(d) for p in schedule for d, v in schedule[p].items()
                    if v.strip().lower() == "v" and colors.get(p, {}).get(d)), DAY_OFF_COLOR)
    return [(color, name) for color, name in PLACES.items()] + [(day_off, "V - вихідний")]


def _week_title(monday: date, today: date) -> str:
    this_monday = today - timedelta(days=today.weekday())
    span = f"{monday:%d.%m} – {monday + timedelta(days=6):%d.%m}"
    if monday == this_monday:
        return f"Цей тиждень · {span}"
    if monday == this_monday + timedelta(days=7):
        return f"Наступний тиждень · {span}"
    return f"Тиждень · {span}"


def _shift(value: str) -> str:
    return ("🌴 " if value.lower() == "v" else "") + f"<b>{html.escape(value)}</b>"


def _day_line(day: date, schedule: dict, people: list[str], short: dict[str, str], today: date) -> str:
    """Один день для телефона: дата, під нею - хто що має; однакові зміни разом.

    пн 09.11
    Liisa, Juha <b>Sil 7-17</b> · Matti <b>HAK12</b>
    """
    groups: dict[str, list[str]] = {}
    for person in people:
        if value := schedule[person].get(day.isoformat()):
            groups.setdefault(value, []).append(html.escape(short[person]))
    label = f"<b>{_day_label(day)}</b>"
    if not groups:
        return f"{label} · —" + ("  ← сьогодні" if day == today else "")
    return label + ("  ← сьогодні" if day == today else "") + "\n" + " · ".join(f"{', '.join(names)} {_shift(value)}" for value, names in groups.items())


def board_message(schedule: dict, short: dict[str, str], today: date) -> str | None:
    """Великий пост: картки "сьогодні" і "завтра", далі тижні - цитатами, що розгортаються."""
    people = [p for p in short if p in schedule]
    days = sorted({d for p in people for d in schedule[p]})
    days = [date.fromisoformat(d) for d in days if d >= today.isoformat()][:BOARD_DAYS]
    while days and not any(schedule[p].get(days[-1].isoformat()) for p in people):
        days.pop()
    if not days:
        return None

    head = ["📋 <b>Графік змін</b>", ""]
    head += _day_card("🟢 <b>Сьогодні</b>", today, schedule, short) + [""]
    head += _day_card("🔜 <b>Завтра</b>", today + timedelta(days=1), schedule, short)

    weeks: dict[date, list[date]] = {}
    for d in days:
        weeks.setdefault(d - timedelta(days=d.weekday()), []).append(d)
    blocks = []
    for monday, week in weeks.items():
        current = monday <= today < monday + timedelta(days=7)
        body = "\n".join(_day_line(d, schedule, people, short, today) for d in week)
        quote = "<blockquote>" if current else "<blockquote expandable>"  # наступні тижні згорнуті
        blocks.append(f"\n📅 <b>{_week_title(monday, today)}</b>\n{quote}{body}</blockquote>")
    # Пост - одне повідомлення Telegram: дальні тижні, що не влазять, відкидаємо.
    while len(blocks) > 1 and len("\n".join(head + blocks)) > TELEGRAM_LIMIT - 200:
        blocks.pop()
    return "\n".join(head + blocks)


def message_link(chat_id: str, message_id: int) -> str | None:
    """Посилання на повідомлення в каналі/групі (для кнопки "Весь графік")."""
    if chat_id.startswith("-100"):
        return f"https://t.me/c/{chat_id[4:]}/{message_id}"
    if chat_id.startswith("@"):
        return f"https://t.me/{chat_id[1:]}/{message_id}"
    return None


# --- Telegram ---------------------------------------------------------------

HELP_TEXT = (
    "👋 <b>Як керувати ботом</b>\n\n"
    "Щоб я почав стежити за людиною, надішли її ім'я так, як у колонці A таблиці:\n"
    "<code>Virtanen Matti</code>\n\n"
    "Коротке ім'я для великого поста - після «=» (так само його й міняють):\n"
    "<code>Virtanen Matti = Matti</code>\n\n"
    "/list - за ким стежу (там же кнопки, щоб прибрати)\n"
    "/remove Ім'я - перестати стежити\n"
    "/help - ця підказка"
)


class TelegramError(RuntimeError):
    pass


def telegram(token: str, method: str, _timeout: float = 30, **params) -> dict | bool:
    data = urllib.parse.urlencode({k: v for k, v in params.items() if v is not None}).encode()
    url = f"https://api.telegram.org/bot{token}/{method}"
    try:
        with urllib.request.urlopen(url, data=data, timeout=_timeout) as response:
            return json.load(response)["result"]
    except urllib.error.HTTPError as error:
        raise TelegramError(f"Telegram відмовив ({method}): {error.code} {error.read().decode()}") from None


def telegram_upload(token: str, method: str, png: bytes, **params) -> dict | bool:
    """Запит до Telegram з картинкою (multipart): поле photo = png."""
    boundary = uuid.uuid4().hex
    body = io.BytesIO()
    for key, value in params.items():
        if value is None:
            continue
        body.write(f'--{boundary}\r\nContent-Disposition: form-data; name="{key}"\r\n\r\n{value}\r\n'.encode())
    body.write(f'--{boundary}\r\nContent-Disposition: form-data; name="photo"; filename="grafik.png"\r\n'
               "Content-Type: image/png\r\n\r\n".encode() + png + f"\r\n--{boundary}--\r\n".encode())
    request = urllib.request.Request(
        f"https://api.telegram.org/bot{token}/{method}", data=body.getvalue(),
        headers={"Content-Type": f"multipart/form-data; boundary={boundary}"},
    )
    try:
        with urllib.request.urlopen(request, timeout=60) as response:
            return json.load(response)["result"]
    except urllib.error.HTTPError as error:
        raise TelegramError(f"Telegram відмовив ({method}): {error.code} {error.read().decode()}") from None


def keyboard(buttons: list | None) -> str | None:
    """Кнопки під повідомленням: [(текст, ціль), ...] - один ряд, [[...], [...]] - кілька рядів.

    Ціль "https://..." - посилання; інше - дані для натискання (callback).
    """
    rows = buttons if buttons and isinstance(buttons[0], list) else [buttons or []]
    markup = [
        [{"text": text, ("url" if target.startswith("http") else "callback_data"): target}
         for text, target in row if target]
        for row in rows
    ]
    markup = [row for row in markup if row]
    return json.dumps({"inline_keyboard": markup}, ensure_ascii=False) if markup else None


def send(token: str, chat_id: str, text: str, buttons: list | None = None) -> list[int]:
    """Надсилає текст (довгий - кількома повідомленнями, кнопки - під останнім); повертає номери."""
    ids = []
    parts = split_message(text)
    for i, part in enumerate(parts):
        message = telegram(
            token, "sendMessage", chat_id=chat_id, text=part, parse_mode="HTML",
            link_preview_options=json.dumps({"is_disabled": True}),
            reply_markup=keyboard(buttons) if i == len(parts) - 1 else None,
        )
        ids.append(message["message_id"])
    return ids


def edit(token: str, chat_id: str, message_id: int, text: str, buttons: list | None = None) -> None:
    try:
        telegram(
            token, "editMessageText", chat_id=chat_id, message_id=message_id, text=text, parse_mode="HTML",
            link_preview_options=json.dumps({"is_disabled": True}), reply_markup=keyboard(buttons),
        )
    except TelegramError as error:
        if "message is not modified" not in str(error):
            raise


def delete(token: str, chat_id: str, message_ids: list[int]) -> None:
    """Видаляє повідомлення бота; старші за 48 год Telegram видалити не дає - пропускаємо."""
    for message_id in message_ids:
        try:
            telegram(token, "deleteMessage", chat_id=chat_id, message_id=message_id)
        except TelegramError as error:
            print(f"Не вдалося видалити повідомлення {message_id}: {error}")


def chats_from_updates(updates: list[dict]) -> dict[int, str]:
    """ID і назви чатів з відповіді getUpdates (повідомлення і додавання бота в групу)."""
    chats = {}
    for update in updates:
        for key in ("message", "channel_post", "my_chat_member", "edited_message"):
            chat = (update.get(key) or {}).get("chat")
            if chat:
                chats[chat["id"]] = chat.get("title") or chat.get("username") or chat.get("first_name", "")
    return chats


def find_chat(token: str) -> None:
    updates = telegram(token, "getUpdates", allowed_updates=json.dumps(["message", "channel_post", "my_chat_member"]))
    chats = chats_from_updates(updates)
    if not chats:
        print("Бот ще нікого не бачив. Додайте його в групу чи канал (або видаліть і додайте "
              "знову), напишіть там щось і запустіть ще раз.")
    for chat_id, title in chats.items():
        print(f"CHAT_ID={chat_id}    <- {title}")


# --- робота -----------------------------------------------------------------

def is_due(now: datetime, send_hour: int, last_sent: str) -> bool:
    """Час вечірнього повідомлення: уже SEND_HOUR або пізніше, а сьогодні ще не надсилали."""
    return now.hour >= send_hour and last_sent != now.date().isoformat()


def load_state() -> dict:
    try:
        return json.loads(STATE_FILE.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}


def save_state(state: dict) -> None:
    tmp = STATE_FILE.with_suffix(".tmp")
    tmp.write_text(json.dumps(state, ensure_ascii=False, indent=1), encoding="utf-8")
    tmp.replace(STATE_FILE)


class Bot:
    def __init__(self, env) -> None:
        self.token = env["TELEGRAM_TOKEN"]
        self.chat_id = env["CHAT_ID"]
        self.url = csv_url(env["SHEET_URL"])
        self.sheet_link = env["SHEET_URL"]
        self.sheet_id = sheet_id(env["SHEET_URL"])
        self.tabs: list[tuple[str, str | None]] = []
        self.tabs_read_at = -TABS_EVERY
        self.empty_tabs: set[str] = set()
        # Хто в списку: як збережено через бота (state.json), а вперше - з PEOPLE.
        saved = load_state().get("people")
        self.short: dict[str, str] = dict(saved) if saved is not None else short_names(env.get("PEOPLE", ""))
        self.admins = {int(a) for a in re.findall(r"\d+", env.get("ADMINS", ""))}
        self.table_names: set[str] = set()
        self.colors: dict[str, dict[str, str]] = {}  # з останньої перевірки; {} - кольорів немає
        self.colors_error = ""
        self.send_hour = int(env.get("SEND_HOUR") or 20)
        self.check_every = 60 * float(env.get("CHECK_MINUTES") or 5)

    @property
    def people(self) -> list[str]:
        return list(self.short)

    def watched_tabs(self, today: date) -> list[tuple[str, str | None]]:
        """Вкладки, які читати; список перечитується раз на годину."""
        if time.monotonic() - self.tabs_read_at < TABS_EVERY and self.tabs:
            return self.tabs
        self.tabs_read_at = time.monotonic()
        try:
            page = fetch(f"https://docs.google.com/spreadsheets/d/{self.sheet_id}/htmlview")
            picked = pick_tabs(tabs_from_html(page), today)
            if not picked:
                raise ValueError("не знайшов вкладок із місяцем і роком у назві")
            self.tabs = picked
        except Exception as error:
            if not self.tabs:  # ще жодного разу не вдалося - читаємо вкладку з SHEET_URL
                self.tabs = [("вкладка з SHEET_URL", None)]
            print(f"Список вкладок не прочитався ({error}); читаю: {', '.join(t for t, _ in self.tabs)}")
        return self.tabs

    def schedule(self, today: date) -> dict[str, dict[str, str]]:
        found: dict[str, dict[str, str]] = {}
        names: set[str] = set()
        for title, gid in self.watched_tabs(today):
            url = self.url if gid is None else (
                f"https://docs.google.com/spreadsheets/d/{self.sheet_id}/export?format=csv&gid={gid}"
            )
            text = download(url)
            names |= names_in_table(text)
            try:
                tab = read_schedule(text, self.people, today)
            except ValueError:  # вкладка ще порожня (графік не внесли) - поки пропускаємо
                if title not in self.empty_tabs:
                    print(f"Вкладка «{title}» поки без графіка - пропускаю.")
                self.empty_tabs.add(title)
                continue
            self.empty_tabs.discard(title)
            for person, days in tab.items():
                found.setdefault(person, {}).update(days)
        self.table_names = names
        self.colors = self.read_colors(today)
        missing = [p for p in self.people if p not in found]
        if missing:
            print(f"Не знайшов у таблиці: {', '.join(missing)}")
        return found

    def read_colors(self, today: date) -> dict[str, dict[str, str]]:
        """Кольори клітинок (місця роботи) з xlsx-вивантаження таблиці; не вдалося - {}."""
        months = {tab_month(title) for title, gid in self.tabs if gid is not None} - {None}
        if not months or not self.people:
            return {}
        try:
            tabs = read_xlsx(fetch_bytes(f"https://docs.google.com/spreadsheets/d/{self.sheet_id}/export?format=xlsx"),
                             months)
            if not tabs:
                raise ValueError("у файлі немає вкладок цих місяців")
            colors: dict[str, dict[str, str]] = {}
            for grid in tabs.values():
                try:
                    found = read_colors(grid, self.people, today)
                except ValueError:  # порожня вкладка
                    continue
                for person, days in found.items():
                    colors.setdefault(person, {}).update(days)
        except Exception as error:
            if str(error) != self.colors_error:
                print(f"Кольори з таблиці не прочиталися ({error}) - пост буде текстом.")
            self.colors_error = str(error)
            return {}
        if self.colors_error:
            print("Кольори з таблиці знову читаються.")
        self.colors_error = ""
        return colors

    def tick(self, now: datetime, state: dict) -> None:
        """Одна перевірка: зміни -> одразу; вечір -> повідомлення на завтра."""
        today = now.date()
        schedule = self.schedule(today)
        known = state.get("schedule", {})
        changes = find_changes(known, schedule, today)
        known_colors = state.get("colors", {})
        moves = find_moves(known_colors, self.colors, known, schedule, today) if self.colors else []
        if changes or moves:
            self.notify(state, changes_message(changes, self.short, self.colors, moves))
            print(f"{now:%d.%m %H:%M} надіслано {len(changes)} змін, {len(moves)} переведень")
        state["schedule"] = {**known, **schedule}  # кого не знайшли - пам'ятаємо як було
        if self.colors:
            state["colors"] = {**known_colors, **self.colors}
        save_state(state)

        self.update_board(state, now)

        if is_due(now, self.send_hour, state.get("last_evening", "")):
            self.notify(state, tomorrow_message(schedule, self.short, today + timedelta(days=1), self.colors))
            state["last_evening"] = today.isoformat()
            save_state(state)
            print(f"{now:%d.%m %H:%M} надіслано повідомлення на завтра")

    def notify(self, state: dict, text: str) -> None:
        """Нове сповіщення замість попереднього."""
        ids = send(self.token, self.chat_id, text, self.notice_buttons(state))
        delete(self.token, self.chat_id, state.get("last_notice", []))
        state["last_notice"] = ids
        save_state(state)

    def notice_buttons(self, state: dict) -> list[tuple[str, str]]:
        board = state.get("board_id")
        return [
            ("📋 Весь графік", message_link(self.chat_id, board) if board else None),
            ("📊 Таблиця", self.sheet_link),
        ]

    def update_board(self, state: dict, now: datetime) -> None:
        """Великий пост з графіком: картинка в кольорах таблиці, а якщо не вийшло - текст."""
        # Збій із кольорами на одній перевірці - малюємо з тими, що запам'ятали, а не міняємо пост на текст.
        colors = self.colors or state.get("colors", {})
        if colors and self.update_picture_board(state, now, colors):
            return
        self.update_text_board(state, now)

    def update_picture_board(self, state: dict, now: datetime, colors: dict) -> bool:
        schedule, today = state["schedule"], now.date()
        png = picture.draw_board(schedule, colors, self.short, today, board_legend(colors, schedule), BOARD_WEEKS)
        if png is None:
            return False
        caption = board_caption(schedule, self.short, today, colors)
        signature = hashlib.sha256(png + caption.encode()).hexdigest()
        if state.get("board_kind") == "photo" and signature == state.get("board_sig"):
            return True
        caption += f"\n\n🔄 <i>Оновлено {now:%d.%m о %H:%M}</i>"
        markup = keyboard([("📊 Відкрити таблицю", self.sheet_link)])
        board_id = state.get("board_id")
        if board_id and state.get("board_kind") == "photo":
            media = json.dumps({"type": "photo", "media": "attach://photo", "caption": caption, "parse_mode": "HTML"},
                               ensure_ascii=False)
            try:
                telegram_upload(self.token, "editMessageMedia", png, chat_id=self.chat_id, message_id=board_id,
                                media=media, reply_markup=markup)
            except TelegramError as error:
                if "message is not modified" not in str(error):
                    print(f"Картинка в пості не оновлюється ({error}); публікую нову.")
                    board_id = None
        else:
            board_id = None
        if not board_id:
            message = telegram_upload(self.token, "sendPhoto", png, chat_id=self.chat_id, caption=caption,
                                      parse_mode="HTML", reply_markup=markup)
            board_id = message["message_id"]
            old = state.get("board_id")
            if old:  # старий пост (текстовий чи зламаний) - прибрати
                delete(self.token, self.chat_id, [old])
            try:
                telegram(self.token, "pinChatMessage", chat_id=self.chat_id, message_id=board_id,
                         disable_notification="true")
            except TelegramError:
                print("Закріпити пост не вдалося - закріпіть вручну або дайте боту право редагувати повідомлення.")
        state.update(board_id=board_id, board_kind="photo", board_sig=signature, board_body=None)
        save_state(state)
        print(f"{now:%d.%m %H:%M} картинку з графіком оновлено")
        return True

    def update_text_board(self, state: dict, now: datetime) -> None:
        body = board_message(state["schedule"], self.short, now.date())
        if state.get("board_kind") == "photo":  # картинку текстом не відредагуєш - новий пост
            delete(self.token, self.chat_id, [state["board_id"]])
            state.update(board_id=None, board_kind="text", board_body=None)
        if body is None or body == state.get("board_body"):
            return
        text = f"{body}\n\n🔄 <i>Оновлено {now:%d.%m о %H:%M}</i>"
        buttons = [("📊 Відкрити таблицю", self.sheet_link)]
        board_id = state.get("board_id")
        if board_id:
            try:
                edit(self.token, self.chat_id, board_id, text, buttons)
            except TelegramError as error:  # пост видалили з каналу - зробимо новий
                print(f"Пост з графіком не редагується ({error}); створюю новий.")
                board_id = None
        if not board_id:
            board_id = send(self.token, self.chat_id, text, buttons)[0]
            try:
                telegram(self.token, "pinChatMessage", chat_id=self.chat_id, message_id=board_id,
                         disable_notification="true")
            except TelegramError:
                print("Закріпити пост не вдалося - закріпіть вручну або дайте боту право редагувати повідомлення.")
        state.update(board_id=board_id, board_body=body, board_kind="text")
        save_state(state)
        print(f"{now:%d.%m %H:%M} пост з графіком оновлено")

    # --- особисті повідомлення: власник керує списком людей ---

    def is_admin(self, state: dict, user_id: int) -> bool:
        return user_id in self.admins or user_id in state.get("admins", [])

    def reply(self, chat_id: int, text: str, buttons: list | None = None) -> None:
        send(self.token, str(chat_id), text, buttons)

    def list_view(self) -> tuple[str, list]:
        if not self.short:
            return "👥 Поки ні за ким не стежу.\n\nНадішли ім'я з таблиці, наприклад <code>Virtanen Matti</code>.", []
        rows = [f"{html.escape(short)} · {html.escape(full)}" for full, short in self.short.items()]
        buttons = [[(f"❌ Прибрати {short}", f"del:{full}")] for full, short in self.short.items()
                   if len(f"del:{full}".encode()) <= 64]
        return "👥 <b>Стежу за:</b>\n" + "\n".join(_tree(rows)), buttons

    def add_person(self, state: dict, text: str) -> tuple[str, list, bool]:
        """(відповідь, кнопки, чи змінився список)."""
        query, _, short = text.partition("=")
        query = " ".join(query.split())
        if not query:
            return HELP_TEXT, [], False
        if not self.table_names:
            self.schedule(date.today())
        match, similar = find_person(self.table_names, query)
        if match is None:
            answer = f"🤷 Не знайшов «{html.escape(query)}» у колонці A таблиці."
            buttons = [[(f"➕ {name}", f"add:{name}")] for name in similar
                       if name not in self.short and len(f"add:{name}".encode()) <= 64]
            if buttons:
                answer += "\n\nМожливо, когось із них?"
            else:
                answer += "\nНапиши ім'я так, як у таблиці, наприклад <code>Virtanen Matti</code>."
            return answer, buttons, False
        if match in self.short:
            new_short = " ".join(short.split())
            if new_short and new_short != self.short[match]:
                self.short[match] = new_short
                state["people"] = dict(self.short)
                save_state(state)
                return (f"✏️ <b>{html.escape(match)}</b> у пості тепер - <b>{html.escape(new_short)}</b>.",
                        [], True)
            return (f"👌 За <b>{html.escape(match)}</b> я вже стежу.\n"
                    f"Інше коротке ім'я: <code>{html.escape(match)} = Нове</code>", [], False)
        first = query.split()[0]
        self.short[match] = " ".join(short.split()) or first[:1].upper() + first[1:]
        state["people"] = dict(self.short)
        save_state(state)
        answer = (f"✅ Тепер стежу за <b>{html.escape(match)}</b> "
                  f"(у пості - <b>{html.escape(self.short[match])}</b>).\n"
                  "За хвилину людина з'явиться у великому пості з графіком, "
                  "а про зміни в її рядку я писатиму в канал.")
        print(f"Додано: {match}")
        return answer, [], True

    def remove_person(self, state: dict, query: str) -> tuple[str, bool]:
        match = next((full for full in self.short if name_key(full) == name_key(query)), None)
        match = match or next((full for full, short in self.short.items() if short.lower() == query.lower()), None)
        if match is None:
            return f"🤷 «{html.escape(query)}» немає в списку. Подивись /list.", False
        del self.short[match]
        state["people"] = dict(self.short)
        state.get("schedule", {}).pop(match, None)
        state.get("colors", {}).pop(match, None)
        save_state(state)
        print(f"Прибрано: {match}")
        return f"🗑 Більше не стежу за <b>{html.escape(match)}</b>.", True

    def handle(self, state: dict, update: dict) -> bool:
        """Одне повідомлення чи натискання кнопки в особистих; True - список людей змінився."""
        if query := update.get("callback_query"):
            return self.handle_button(state, query)
        message = update.get("message") or {}
        if (message.get("chat") or {}).get("type") != "private" or "from" not in message:
            return False
        user, chat = message["from"]["id"], message["chat"]["id"]
        text = (message.get("text") or "").strip()
        command = text.split()[0].split("@")[0].lower() if text.startswith("/") else ""

        if not self.is_admin(state, user):
            if command == "/start" and not self.admins and not state.get("admins"):
                state["admins"] = [user]
                save_state(state)
                print(f"Власник бота: {user}")
                self.reply(chat, "👑 Ти - власник цього бота.\n\n" + HELP_TEXT)
            else:
                self.reply(chat, f"🔒 Цим ботом керує власник.\nТвій Telegram ID: <code>{user}</code>")
            return False

        if command in ("/start", "/help"):
            self.reply(chat, HELP_TEXT)
        elif command == "/list":
            self.reply(chat, *self.list_view())
        elif command == "/remove":
            answer, changed = self.remove_person(state, text.partition(" ")[2].strip())
            self.reply(chat, answer)
            return changed
        elif command:
            self.reply(chat, "Не знаю такої команди.\n\n" + HELP_TEXT)
        elif text:
            answer, buttons, changed = self.add_person(state, text)
            self.reply(chat, answer, buttons)
            return changed
        return False

    def handle_button(self, state: dict, query: dict) -> bool:
        message = query.get("message") or {}
        chat, message_id = (message.get("chat") or {}).get("id"), message.get("message_id")
        action, _, name = (query.get("data") or "").partition(":")
        if not self.is_admin(state, query["from"]["id"]) or chat is None:
            telegram(self.token, "answerCallbackQuery", callback_query_id=query["id"], text="🔒 Лише для власника")
            return False
        changed = False
        if action == "add":
            answer, _, changed = self.add_person(state, name)
            edit(self.token, str(chat), message_id, answer)
        elif action == "del":
            answer, changed = self.remove_person(state, name)
            edit(self.token, str(chat), message_id, *self.list_view())
        else:
            answer = ""
        notice = re.sub(r"<[^>]+>", "", answer)[:200] if answer else None
        telegram(self.token, "answerCallbackQuery", callback_query_id=query["id"], text=notice)
        return changed

    def poll(self, state: dict, timeout: int) -> bool:
        """Чекає повідомлень боту до timeout секунд; True - список людей змінився."""
        updates = telegram(
            self.token, "getUpdates", _timeout=timeout + 15, offset=state.get("update_offset"),
            timeout=timeout, allowed_updates=json.dumps(["message", "callback_query"]),
        )
        changed = False
        for update in updates:
            state["update_offset"] = update["update_id"] + 1
            try:
                changed |= self.handle(state, update)
            except Exception as error:
                print(f"Не вдалося обробити повідомлення: {error}")
        if updates:
            save_state(state)
        return changed

    def set_commands(self) -> None:
        """Меню команд у особистих повідомленнях з ботом."""
        commands = [
            {"command": "list", "description": "За ким стежу (і прибрати)"},
            {"command": "help", "description": "Як додати людину"},
        ]
        try:
            telegram(self.token, "setMyCommands", commands=json.dumps(commands, ensure_ascii=False),
                     scope=json.dumps({"type": "all_private_chats"}))
        except Exception as error:
            print(f"Меню команд не встановилось: {error}")

    def run_forever(self) -> None:
        state = load_state()  # уперше - порожній: графік запам'ятається без оголошень
        if "people" not in state:
            state["people"] = dict(self.short)
            save_state(state)
        print(f"Бот працює: стежу за {', '.join(self.people) or 'нікого'}; "
              f"перевірка що {self.check_every / 60:g} хв, повідомлення на завтра о {self.send_hour}:00.")
        self.set_commands()
        next_tick = 0.0
        while True:
            if time.monotonic() >= next_tick:
                now = datetime.now()
                try:
                    self.tick(now, state)
                except Exception as error:  # немає інтернету, Google чи Telegram не відповів...
                    print(f"{now:%d.%m %H:%M} не вдалося: {error}. Спробую на наступній перевірці.")
                next_tick = time.monotonic() + self.check_every
            wait = int(max(1, min(POLL_SECONDS, next_tick - time.monotonic())))
            try:
                if self.poll(state, wait):
                    next_tick = 0.0  # список людей змінився - одразу оновити пост
            except Exception as error:
                print(f"Не вдалося прочитати повідомлення боту: {error}")
                time.sleep(min(wait, 30))


def main() -> None:
    for stream in (sys.stdout, sys.stderr):
        stream.reconfigure(encoding="utf-8", errors="replace")
    load_env(ENV_FILE)
    env = os.environ
    if "--find-chat" in sys.argv:
        if not env.get("TELEGRAM_TOKEN"):
            sys.exit(f"Не задано TELEGRAM_TOKEN у файлі {ENV_FILE}.")
        find_chat(env["TELEGRAM_TOKEN"])
        return
    needed = ("SHEET_URL",) if "--check" in sys.argv else ("TELEGRAM_TOKEN", "CHAT_ID", "SHEET_URL")
    for key in needed:
        if not env.get(key):
            sys.exit(f"Не задано {key} у файлі {ENV_FILE}. Див. README.md.")

    if "--check" in sys.argv:
        today = date.today()
        env.setdefault("TELEGRAM_TOKEN", "")
        env.setdefault("CHAT_ID", "")
        checker = Bot(env)
        people = checker.people
        schedule = checker.schedule(today)
        print("Вкладки: " + ", ".join(title for title, _ in checker.tabs))
        for person in people:
            days = schedule.get(person)
            if days is None:
                print(f"{person}: НЕ ЗНАЙДЕНО в колонці A")
                continue
            print(f"{person}:")
            for day_text, value in sorted(days.items()):
                print(f"   {_day_label(date.fromisoformat(day_text))}  {value or '—'}")
        return

    bot = Bot(env)
    if "--now" in sys.argv:
        today = date.today()
        send(bot.token, bot.chat_id, tomorrow_message(bot.schedule(today), bot.short, today + timedelta(days=1)),
             [("📊 Таблиця", bot.sheet_link)])
        print("Надіслано.")
        return
    try:
        bot.run_forever()
    except KeyboardInterrupt:
        print("Бот зупинено.")


if __name__ == "__main__":
    main()
