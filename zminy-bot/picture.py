"""Картинка графіка для закріпленого поста - як у Google-таблиці, тими ж кольорами.

Люди в рядках, дні в колонках (Ma Ti Ke ... Su, неділя червона), кожен тиждень
окремим блоком, сьогодні - у синій рамці, внизу легенда кольорів (місця роботи).
Без Pillow (бібліотеки малювання) повертає None - тоді бот лишає текстовий пост.
"""

from __future__ import annotations

import io
from datetime import date, timedelta

WEEKDAYS_FI = ["Ma", "Ti", "Ke", "To", "Pe", "La", "Su"]
FONT_DIRS = ["/usr/share/fonts/truetype/dejavu", "/usr/share/fonts/dejavu", "/Library/Fonts", "C:/Windows/Fonts"]
S = 2  # масштаб: картинка вдвічі більша, щоб на телефоні було чітко

EMPTY = "ffffff"
NO_COLOR = "e8eaed"  # значення є, а кольору з таблиці немає
GRID, HEAD, TEXT, TODAY = "#c7c7c7", "#f1f3f4", "#202124", "#1a73e8"


def _font(bold: bool, size: int):
    from PIL import ImageFont

    name = "DejaVuSans-Bold.ttf" if bold else "DejaVuSans.ttf"
    for folder in FONT_DIRS:
        try:
            return ImageFont.truetype(f"{folder}/{name}", size)
        except OSError:
            continue
    return ImageFont.load_default(size)


def _rgb(color: str) -> tuple[int, int, int]:
    return tuple(int(color[i:i + 2], 16) for i in (0, 2, 4))


def _dark(color: str) -> bool:
    r, g, b = _rgb(color)
    return 0.299 * r + 0.587 * g + 0.114 * b < 150


def weeks_to_show(schedule: dict, people: list[str], today: date, weeks: int) -> list[list[date]]:
    """Тижні від поточного; порожні тижні наприкінці (графік ще не внесли) відкидаються."""
    monday = today - timedelta(days=today.weekday())
    result = [[monday + timedelta(days=7 * w + i) for i in range(7)] for w in range(weeks)]
    while len(result) > 1 and not any(schedule.get(p, {}).get(d.isoformat()) for p in people for d in result[-1]):
        result.pop()
    return result


def draw_board(
    schedule: dict[str, dict[str, str]],
    colors: dict[str, dict[str, str]],
    short: dict[str, str],
    today: date,
    legend: list[tuple[str, str]],
    weeks: int = 3,
    title: str = "Графік змін",
) -> bytes | None:
    """PNG графіка; legend - [(колір "rrggbb" або "", підпис)]."""
    try:
        from PIL import Image, ImageDraw
    except ImportError:
        return None
    people = [p for p in short if p in schedule]
    if not people:
        return None
    blocks = weeks_to_show(schedule, people, today, weeks)

    title_f, bold, font, small = _font(True, 20 * S), _font(True, 15 * S), _font(False, 15 * S), _font(False, 12 * S)
    pad, name_w, head_h, cell_h, gap = 16 * S, 0, 46 * S, 34 * S, 24 * S
    probe = ImageDraw.Draw(Image.new("RGB", (1, 1)))
    name_w = max(probe.textlength(short[p], font=bold) for p in people) + 20 * S
    values = [schedule[p].get(d.isoformat(), "") for p in people for week in blocks for d in week]
    cell_w = max([84 * S] + [probe.textlength(v.strip(), font=font) + 14 * S for v in values])
    block_h = head_h + cell_h * len(people)
    width = int(2 * pad + name_w + 7 * cell_w)
    # Легенда: пункти по рядках, щоб не вилазили за край.
    legend_lines: list[list[tuple[str, str, float]]] = [[]]
    used = 0.0
    for color, label in legend:
        item_w = (28 * S if color else 0) + probe.textlength(label, font=font) + 24 * S
        if legend_lines[-1] and used + item_w > width - 2 * pad:
            legend_lines.append([])
            used = 0.0
        legend_lines[-1].append((color, label, item_w))
        used += item_w
    legend_h = 30 * S * len(legend_lines) if legend else 0
    height = int(60 * S + len(blocks) * (block_h + gap) + legend_h + 8 * S)

    img = Image.new("RGB", (width, height), "#ffffff")
    d = ImageDraw.Draw(img)
    d.text((pad, 18 * S), title, font=title_f, fill=TEXT)
    y = 60 * S
    for week in blocks:
        x0 = pad
        d.rectangle([x0, y, x0 + name_w, y + head_h], fill=HEAD, outline=GRID)
        for i, day in enumerate(week):
            x = x0 + name_w + i * cell_w
            sunday = day.weekday() == 6
            d.rectangle([x, y, x + cell_w, y + head_h], fill="#ff0000" if sunday else HEAD, outline=GRID)
            ink = "#ffffff" if sunday else TEXT
            d.text((x + cell_w / 2, y + 13 * S), WEEKDAYS_FI[day.weekday()], font=small, fill=ink, anchor="mm")
            d.text((x + cell_w / 2, y + 32 * S), f"{day:%d.%m}", font=bold, fill=ink, anchor="mm")
        for j, person in enumerate(people):
            yy = y + head_h + j * cell_h
            d.rectangle([x0, yy, x0 + name_w, yy + cell_h], fill="#ffffff", outline=GRID)
            d.text((x0 + 10 * S, yy + cell_h / 2), short[person], font=bold, fill=TEXT, anchor="lm")
            for i, day in enumerate(week):
                value = schedule[person].get(day.isoformat(), "").strip()
                color = colors.get(person, {}).get(day.isoformat()) or (NO_COLOR if value else EMPTY)
                x = x0 + name_w + i * cell_w
                d.rectangle([x, yy, x + cell_w, yy + cell_h], fill="#" + color, outline=GRID)
                if value:
                    ink = "#ffffff" if _dark(color) else "#000000"
                    d.text((x + cell_w / 2, yy + cell_h / 2), value, font=font, fill=ink, anchor="mm")
        if today in week:
            x = x0 + name_w + week.index(today) * cell_w
            d.rectangle([x, y, x + cell_w, y + block_h], outline=TODAY, width=3 * S)
        y += block_h + gap

    for line in legend_lines if legend else []:
        x = pad
        for color, label, item_w in line:
            if color:
                d.rectangle([x, y + 4 * S, x + 22 * S, y + 22 * S], fill="#" + color, outline=GRID)
            d.text((x + (28 * S if color else 0), y + 13 * S), label, font=font, fill=TEXT, anchor="lm")
            x += item_w
        y += 30 * S

    out = io.BytesIO()
    img.save(out, format="PNG", optimize=True)
    return out.getvalue()
