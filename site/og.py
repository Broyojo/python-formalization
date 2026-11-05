"""Render docs/og.png, the 1200x630 link-preview image: title, the C/Lean code pair, and the headline numbers.

Uses the same data as site/build.py. Run after build.py: python3 site/og.py
"""

import sys
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont

sys.path.insert(0, str(Path(__file__).resolve().parent))
import build  # noqa: E402

W, H = 1200, 630
BG, TEXT, MUTED, BLUE, PANEL = (255, 255, 255), (22, 24, 29), (100, 107, 117), (63, 111, 152), (246, 247, 249)
SANS = "/System/Library/Fonts/HelveticaNeue.ttc"
MONO = "/System/Library/Fonts/Menlo.ttc"

C_CODE = [
    "static unsigned long",
    "get_len_of_range(long lo, long hi, long step)",
    "{",
    "    if (step > 0 && lo < hi)",
    "        return 1UL + (hi - 1UL - lo) / step;",
    "    else if (step < 0 && lo > hi)",
    "        return 1UL + (lo - 1UL - hi) / (0UL - step);",
    "    else",
    "        return 0UL;",
    "}",
]
LEAN_CODE = [
    "def getLenOfRange (lo hi step : Int) : Int :=",
    "  if step > 0 ∧ lo < hi then",
    "    uadd 1 (usub (usub (toU hi) 1) (toU lo)",
    "           / toU step)",
    "  else if step < 0 ∧ lo > hi then",
    "    uadd 1 (usub (usub (toU lo) 1) (toU hi)",
    "           / usub 0 (toU step))",
    "  else 0",
]


def font(path, size, index=0):
    try:
        return ImageFont.truetype(path, size, index=index)
    except OSError:
        return ImageFont.load_default()


COL = {"kw": (207, 34, 46), "ty": (149, 56, 0), "num": (5, 80, 174), "fn": (130, 80, 223), "op": (207, 34, 46)}


def tokens(line, lang):
    import re as _re
    out, pos = [], 0
    for m in _re.finditer(r"\b\d+(?:UL)?\b|[A-Za-z_][A-Za-z_0-9]*|∧", line):
        if m.start() > pos:
            out.append((line[pos:m.start()], TEXT))
        w = m.group(0)
        kind = ("num" if w[0].isdigit() else "op" if w == "∧" else "kw" if w in build.KEYWORDS[lang]
                else "ty" if w in build.TYPES[lang] else "fn" if w in build.FUNCS[lang] else None)
        out.append((w, COL[kind] if kind else TEXT))
        pos = m.end()
    out.append((line[pos:], TEXT))
    return out


def panel(d, x, y, w, h, label, lines, lang):
    d.rounded_rectangle([x, y, x + w, y + h], radius=14, fill=PANEL)
    d.text((x + 22, y + 18), label, font=font(SANS, 17, 1), fill=MUTED)
    mono = font(MONO, 15)
    for i, line in enumerate(lines):
        cx, cy = x + 22, y + 52 + i * 23
        for text, colour in tokens(line, lang):
            d.text((cx, cy), text, font=mono, fill=colour)
            cx += mono.getlength(text)


def main():
    files = build.coverage()
    reg = build.registry()
    nbugs, _ = build.bugs()
    faithful = sum(c["faithful"] for c in files.values())

    img = Image.new("RGB", (W, H), BG)
    d = ImageDraw.Draw(img)
    x0 = 56
    d.text((x0, 46), "Formalizing CPython", font=font(SANS, 56, 1), fill=TEXT)
    lean_lines = sum(f.read_text().count("\n") for f in (build.ROOT / "lean" / "PyLean").rglob("*.lean"))
    d.text((x0, 116), f"AI agents wrote {lean_lines:,} lines of Lean that copy Python's internals,",
           font=font(SANS, 24), fill=MUTED)
    d.text((x0, 148), "tested every piece against real Python, and found bugs along the way.", font=font(SANS, 24), fill=MUTED)

    top, ph, gap = 204, 312, 20
    pw = (W - 2 * x0 - gap) // 2
    panel(d, x0, top, pw, ph, "CPython  ·  Objects/rangeobject.c", C_CODE, "c")
    panel(d, x0 + pw + gap, top, pw, ph, "Lean copy  ·  RangeSlice/Model.lean", LEAN_CODE, "lean")

    stats = f"{faithful:,} functions checked    ·    {reg['proven']:,} proofs    ·    {nbugs:,} bug reports"
    d.text((x0, top + ph + 30), stats, font=font(SANS, 24, 1), fill=BLUE)
    d.text((W - x0, top + ph + 34), "broyojo.com/python-formalization", font=font(SANS, 18), fill=MUTED, anchor="ra")
    out = build.ROOT / "docs" / "og.png"
    img.save(out, optimize=True)
    print(f"wrote {out.relative_to(build.ROOT)}")


if __name__ == "__main__":
    main()
