"""Render images for the X thread into reports/x_images/ (1600x900, the 16:9 size X shows uncropped).

  post3-crash.png     the dict.setdefault crash, as code with its output
  post4-proofs.png    "could a broken version pass?" table from the write-up
  post5-coverage.png  coverage of each part of CPython, from the same data as the page

Run after site/build.py: python3 site/x_images.py
"""

import collections
import sys
from pathlib import Path

from PIL import Image, ImageDraw

sys.path.insert(0, str(Path(__file__).resolve().parent))
import build  # noqa: E402
from og import BG, BLUE, MONO, MUTED, PANEL, SANS, TEXT, font, tokens  # noqa: E402

W, H = 1600, 900
X0 = 90
OUT = build.ROOT / "reports" / "x_images"
LIGHT_BLUE, GRAY, RED, GREEN = (191, 209, 226), (229, 231, 235), (190, 30, 45), (26, 127, 55)


def canvas(title, subtitle):
    img = Image.new("RGB", (W, H), BG)
    d = ImageDraw.Draw(img)
    d.text((X0, 70), title, font=font(SANS, 64, 1), fill=TEXT)
    d.text((X0, 158), subtitle, font=font(SANS, 30), fill=MUTED)
    d.text((W - X0, H - 60), "broyojo.com/python-formalization", font=font(SANS, 24), fill=MUTED, anchor="ra")
    return img, d


def crash():
    img, d = canvas("A five-line crash in Python 3.15",
                    "Plain Python, no C extensions: dict.setdefault on an instance's __dict__.")
    code = ["class C: pass",
            "a = C(); a.x = 1",
            "b = C(); b.y = 2",
            "class S(str): pass",
            "b.__dict__.setdefault(S('x'), 5)"]
    top, h = 250, 470
    d.rounded_rectangle([X0, top, W - X0, top + h], radius=20, fill=PANEL)
    mono = font(MONO, 34)
    for i, line in enumerate(code):
        x, y = X0 + 44, top + 44 + i * 56
        for text, colour in tokens(line, "c"):
            d.text((x, y), text, font=mono, fill=colour)
            x += mono.getlength(text)
    d.text((X0 + 44, top + 44 + 5 * 56 + 30), "Segmentation fault", font=mono, fill=RED)
    d.text((X0, top + h + 40), "Found by a Lean model of dictobject.c. Reproduces on 3.15.2 and main.",
           font=font(SANS, 28), fill=MUTED)
    img.save(OUT / "post3-crash.png", optimize=True)


def proofs():
    img, d = canvas("Proofs that prove nothing",
                    "Two true statements about one function. Could a broken version pass them?")
    cols = [X0, 760, 1160]
    head = ["Version of the function", "“If it returns, the\nanswer is ≥ 0”",
            "“It always returns\nthe right count”"]
    rows = [("The real one", True, True), ("Always crashes", True, False),
            ("Returns 0 for very large numbers", True, False), ("Off by one when counting down", True, False)]
    y = 260
    for x, h in zip(cols, head):
        d.multiline_text((x, y), h, font=font(SANS, 30, 1), fill=TEXT, spacing=8)
    y += 110
    d.line([X0, y - 20, W - X0, y - 20], fill=GRAY, width=3)
    for name, a, b in rows:
        d.text((cols[0], y), name, font=font(SANS, 34), fill=TEXT)
        for x, ok in ((cols[1], a), (cols[2], b)):
            d.text((x, y), "passes" if ok else "caught", font=font(SANS, 34, 1), fill=RED if ok and name != "The real one" else GREEN)
        y += 78
    d.text((X0, y + 20), "Only statements that catch broken versions count. Review threw out more than half of the early work.",
           font=font(SANS, 28), fill=MUTED)
    img.save(OUT / "post4-proofs.png", optimize=True)


def coverage():
    files = build.coverage()
    area = collections.defaultdict(collections.Counter)
    for f, c in files.items():
        area[f.split("/")[0]].update(c)
    tot = collections.Counter()
    for c in area.values():
        tot.update(c)
    img, d = canvas("How much of CPython is covered",
                    "Copied into Lean, tested against Python, proved, and accepted by an independent review.")
    rows = [("All of CPython", tot)] + [(build.AREA_NAMES[a], area[a]) for a in build.AREA_ORDER]
    y, label_w, bar_x, bar_w = 250, 420, X0 + 430, 880
    for name, c in rows:
        scope = c["rows"] - c["excluded"]
        f1, f2 = c["faithful"] / scope, c["modelled"] / scope
        bold = name == "All of CPython"
        d.text((X0, y), name, font=font(SANS, 32, 1 if bold else 0), fill=TEXT)
        d.rounded_rectangle([bar_x, y + 4, bar_x + bar_w, y + 40], radius=8, fill=GRAY)
        d.rectangle([bar_x, y + 4, bar_x + bar_w * f1, y + 40], fill=BLUE)
        if f2 > 0:
            d.rectangle([bar_x + bar_w * f1, y + 4, bar_x + bar_w * (f1 + f2), y + 40], fill=LIGHT_BLUE)
        d.text((bar_x + bar_w + 24, y), f"{100 * f1:.0f}%", font=font(SANS, 32, 1), fill=TEXT)
        y += 72 if not bold else 92
    lx = X0
    for colour, text in ((BLUE, "accepted"), (LIGHT_BLUE, "written, not yet accepted"), (GRAY, "not started")):
        d.rectangle([lx, y + 22, lx + 26, y + 48], fill=colour)
        d.text((lx + 38, y + 18), text, font=font(SANS, 26), fill=MUTED)
        lx += 60 + font(SANS, 26).getlength(text) + 40
    img.save(OUT / "post5-coverage.png", optimize=True)


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    crash()
    proofs()
    coverage()
    print("wrote", ", ".join(p.name for p in sorted(OUT.glob("*.png"))))


if __name__ == "__main__":
    main()
