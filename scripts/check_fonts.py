"""Шрифты PDF: только вложенные шрифты книги, без .notdef."""
from collections import defaultdict
from pathlib import Path
import re
import struct
import fitz
ROOT = Path(__file__).resolve().parents[1]
SUBSET_TAG = re.compile(r"^[A-Z]{6}\+")


def book_font_names(directory=ROOT / 'assets/fonts'):
    """PostScript names (OpenType name ID 6) of the font files of the book."""
    names = set()
    for path in sorted(directory.rglob("*")):
        if path.suffix.lower() not in {".otf", ".ttf"}:
            continue
        data = path.read_bytes()
        for index in range(struct.unpack_from(">H", data, 4)[0]):
            tag, _, table, _ = struct.unpack_from(">4sIII", data, 12 + 16 * index)
            if tag != b"name":
                continue
            _, count, strings = struct.unpack_from(">3H", data, table)
            for record in range(count):
                platform, _, _, name_id, length, offset = struct.unpack_from(
                    ">6H", data, table + 6 + 12 * record
                )
                if name_id == 6:
                    start = table + strings + offset
                    names.add(data[start:start + length].decode(
                        "utf-16-be" if platform in (0, 3) else "latin-1"
                    ))
    if not names:
        raise ValueError(f"No fonts found in {directory}")
    return names


def check_fonts(pdf: Path, label: str, allowed: set[str]):
    """Fail if the PDF has a font outside assets/fonts or a missing glyph."""
    found = defaultdict(dict)  # problem -> {PDF page: text set in the font}
    for page in fitz.open(pdf):
        number, foreign = page.number + 1, {}
        for _, _, kind, name, _, encoding, *_ in page.get_fonts(full=True):
            name = SUBSET_TAG.sub("", name)
            if kind == "Type0":  # BaseFont of a Type0 font is "<font>-<CMap>"
                name = name.removesuffix(f"-{encoding}")
            if name not in allowed:
                foreign[name] = found[f"font {name} is not a book font"]
                foreign[name][number] = ""
        text = ""
        for span in page.get_texttrace():
            chars = "".join(chr(c) if c > 0 else "?" for c, *_ in span["chars"])
            chars = chars.replace("\xad", "-")
            # MuPDF shortens the font names of spans.
            for name, pages in foreign.items():
                if name.startswith(span["font"]):
                    pages[number] += chars
            if any(name.startswith(span["font"]) for name in allowed):
                for index, (_, glyph, *_) in enumerate(span["chars"]):
                    if glyph == 0:
                        context = (text + chars[:index])[-40:]
                        found[f'no book font has the glyph after "{context}"'][
                            number
                        ] = ""
            text += chars
    if found:
        raise ValueError(f"{label}:" + "".join(
            f"\n  {problem}: " + ", ".join(
                f"PDF page {page}" + (f' "{sample[:30]}"' if sample else "")
                for page, sample in list(pages.items())[:8]
            ) + (f" and {len(pages) - 8} more pages" if len(pages) > 8 else "")
            for problem, pages in found.items()
        ))

