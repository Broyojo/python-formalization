"""Render reports/x_images/post1-zoom.mp4: one C/Lean translation, then a slow zoom out to a grid of every
in-scope function, with accepted functions lighting up and a counter. Needs ffmpeg.

  python3 site/x_video.py
"""

import math
import random
import re
import subprocess
import sys
from pathlib import Path

from PIL import Image, ImageDraw

sys.path.insert(0, str(Path(__file__).resolve().parent))
import build  # noqa: E402
from og import BG, BLUE, C_CODE, LEAN_CODE, MONO, MUTED, PANEL, SANS, TEXT, font, tokens  # noqa: E402

W, H, FPS, SECONDS = 1600, 900, 30, 10
OUT = build.ROOT / "reports" / "x_images" / "post1-zoom.mp4"
GRAY, LIGHT = (229, 231, 235), (191, 209, 226)
GAP = 0.08  # fraction of the pitch left between tiles


def code_card(lines_left, lines_right, w, h, label_left, label_right):
    """The hero tile: the C function and its Lean copy side by side."""
    img = Image.new("RGB", (w, h), BG)
    d = ImageDraw.Draw(img)
    pad, gap = int(w * 0.03), int(w * 0.02)
    pw = (w - 2 * pad - gap) // 2
    longest = max(len(l) for l in lines_left + lines_right)
    fs = int(min(w * 0.0185, (pw - 1.6 * pad) / (longest * 0.61)))
    mono = font(MONO, fs)
    body = fs * 2.6 + max(len(lines_left), len(lines_right)) * fs * 1.55 + pad * 1.6
    top = (h - body) / 2
    for k, (label, lines, lang) in enumerate(((label_left, lines_left, "c"), (label_right, lines_right, "lean"))):
        x0 = pad + k * (pw + gap)
        d.rounded_rectangle([x0, top, x0 + pw, top + body], radius=int(w * 0.012), fill=PANEL)
        d.text((x0 + pad * 0.7, top + pad * 0.8), label, font=font(SANS, int(fs * 1.1), 1), fill=MUTED)
        for i, line in enumerate(lines):
            cx, cy = x0 + pad * 0.7, top + pad * 0.8 + fs * 2.6 + i * fs * 1.55
            for text, colour in tokens(line, lang):
                d.text((cx, cy), text, font=mono, fill=colour)
                cx += mono.getlength(text)
    return img


def lean_snippets(n):
    """Short real `def`s from the models, for the other tiles."""
    out = []
    files = sorted((build.ROOT / "lean" / "PyLean").glob("*/Model.lean"))
    random.Random(1).shuffle(files)
    for f in files:
        text = f.read_text(errors="replace")
        for m in re.finditer(r"^def [^\n]{0,70}\n(?:  [^\n]{0,70}\n){4,9}", text, re.M):
            lines = m.group(0).rstrip("\n").splitlines()[:9]
            if all(len(l) <= 70 for l in lines):
                out.append((f.parent.name, lines))
                break
        if len(out) >= n:
            break
    return out


def snippet_card(name, lines, w, h):
    img = Image.new("RGB", (w, h), PANEL)
    d = ImageDraw.Draw(img)
    fs = int(w * 0.03)
    mono = font(MONO, fs)
    d.text((w * 0.05, h * 0.07), f"{name}/Model.lean", font=font(SANS, int(fs * 1.05), 1), fill=MUTED)
    for i, line in enumerate(lines):
        cx, cy = w * 0.05, h * 0.07 + fs * 2.2 + i * fs * 1.5
        for text, colour in tokens(line, "lean"):
            d.text((cx, cy), text, font=mono, fill=colour)
            cx += mono.getlength(text)
    return img


def ease(x):
    x = min(max(x, 0.0), 1.0)
    return x * x * (3 - 2 * x)


def main():
    files = build.coverage()
    tot = {k: sum(c[k] for c in files.values()) for k in ("rows", "excluded", "faithful", "modelled")}
    n_scope = tot["rows"] - tot["excluded"]
    n_ok, n_written = tot["faithful"], tot["modelled"]
    lean_lines = sum(f.read_text().count("\n") for f in (build.ROOT / "lean" / "PyLean").rglob("*.lean"))
    nbugs, _ = build.bugs()

    side = math.ceil(math.sqrt(n_scope))  # square grid of 16:9 tiles is itself 16:9
    hc = hr = side // 2
    hero_i = hr * side + hc
    rng = random.Random(7)
    cells = [i for i in range(side * side) if i != hero_i]
    def dist(i):
        r, c = divmod(i, side)
        return math.hypot(c - hc, (r - hr) * 9 / 16 * 16 / 9) + rng.random() * 9
    cells.sort(key=dist)                          # nearest the hero first, with a ragged edge
    cells = cells[: n_scope - 1]                  # the unused cells of the square are the far corners
    ok_order = cells[: n_ok - 1]                  # lit outward from the hero during the zoom
    written = set(cells[n_ok - 1: n_ok - 1 + n_written])
    exists = set(cells) | {hero_i}
    lit_rank = {c: k for k, c in enumerate(ok_order)}

    hero_w = 1440
    hero = code_card(C_CODE, LEAN_CODE, hero_w, hero_w * 9 // 16,
                     "CPython  ·  Objects/rangeobject.c", "Lean copy  ·  RangeSlice/Model.lean")
    snippets = lean_snippets(24)
    pool = [snippet_card(n, l, 720, 405) for n, l in snippets]
    pending = Image.new("RGB", (720, 405), GRAY)

    P0, P1 = hero_w / (1 - GAP), W / side * 0.98
    t_hold, t_zoom_end, total = 1.5, 7.0, FPS * SECONDS
    ff = subprocess.Popen(["ffmpeg", "-y", "-loglevel", "error", "-f", "rawvideo", "-pix_fmt", "rgb24",
                           "-s", f"{W}x{H}", "-r", str(FPS), "-i", "-", "-c:v", "libx264", "-pix_fmt", "yuv420p",
                           "-crf", "18", "-preset", "slow", "-movflags", "+faststart", str(OUT)],
                          stdin=subprocess.PIPE)
    big = font(SANS, 40, 1)
    small = font(SANS, 28)
    for f in range(total):
        t = f / FPS
        z = ease((t - t_hold) / (t_zoom_end - t_hold))
        P = math.exp(math.log(P0) + (math.log(P1) - math.log(P0)) * z)
        Ph = P * 9 / 16
        lit = 1 + int((n_ok - 1) * ease((t - t_hold - 0.5) / (t_zoom_end - t_hold)))
        frame = Image.new("RGB", (W, H), BG)
        d = ImageDraw.Draw(frame)
        tw, th = max(1, int(P * (1 - GAP))), max(1, int(Ph * (1 - GAP)))
        c0 = max(0, int(hc - (W / 2) / P) - 1)
        c1 = min(side, int(hc + (W / 2) / P) + 2)
        r0 = max(0, int(hr - (H / 2) / Ph) - 1)
        r1 = min(side, int(hr + (H / 2) / Ph) + 2)
        detailed = tw >= 28
        cache = {}
        for r in range(r0, r1):
            y = H / 2 + (r - hr) * Ph - th / 2
            for c in range(c0, c1):
                i = r * side + c
                if i not in exists:
                    continue
                x = W / 2 + (c - hc) * P - tw / 2
                on = i == hero_i or lit_rank.get(i, 1 << 30) < lit
                if detailed:
                    if i == hero_i:
                        key = ("hero",)
                        src = hero
                    elif on:
                        key = ("pool", i % len(pool))
                        src = pool[i % len(pool)]
                    else:
                        key, src = ("pending",), pending
                    if key not in cache:
                        cache[key] = src.resize((tw, th), Image.LANCZOS)
                    frame.paste(cache[key], (int(x), int(y)))
                    if on and i != hero_i:
                        d.rectangle([x, y, x + tw, y + max(2, th * 0.04)], fill=BLUE)
                else:
                    colour = BLUE if on else LIGHT if (i in written and z > 0.98) else GRAY
                    d.rectangle([x, y, x + tw - 1, y + th - 1], fill=colour)
        if t < t_hold + 0.8:
            a0 = 1 - ease((t - t_hold) / 0.8)
            if a0 > 0.3:
                d.text((W / 2, 70), "One CPython function and its Lean copy", font=font(SANS, 38, 1), fill=TEXT,
                       anchor="mm")
        if t >= t_hold:
            alpha = ease((t - t_hold) / 0.6)
            box = Image.new("RGBA", (W, H), (0, 0, 0, 0))
            bd = ImageDraw.Draw(box)
            if t >= t_zoom_end + 0.4:
                alpha *= 1 - ease((t - t_zoom_end - 0.4) / 0.4)
            bd.rounded_rectangle([40, H - 128, 760, H - 22], radius=18, fill=(255, 255, 255, int(235 * alpha)))
            frame.paste(box, (0, 0), box)
            if alpha > 0.4:
                d.text((70, H - 114), f"{lit:,} functions checked", font=big, fill=TEXT)
                d.text((70, H - 66), f"of {n_scope:,} in CPython 3.15.2", font=small, fill=MUTED)
        if t >= t_zoom_end + 0.6:
            alpha = ease((t - t_zoom_end - 0.6) / 0.6)
            box = Image.new("RGBA", (W, H), (0, 0, 0, 0))
            bd = ImageDraw.Draw(box)
            bd.rectangle([0, H - 190, W, H], fill=(255, 255, 255, int(245 * alpha)))
            frame.paste(box, (0, 0), box)
            if alpha > 0.3:
                d.text((70, H - 168), "Formalizing CPython", font=font(SANS, 58, 1), fill=TEXT)
                d.text((70, H - 92), f"{n_ok:,} of {n_scope:,} functions checked  \u00b7  {lean_lines:,} lines of Lean"
                       f"  \u00b7  {nbugs:,} bug reports", font=font(SANS, 32), fill=BLUE)
                d.text((W - 70, H - 150), "broyojo.com/python-formalization", font=font(SANS, 26), fill=MUTED,
                       anchor="ra")
        ff.stdin.write(frame.tobytes())
    ff.stdin.close()
    ff.wait()
    print("wrote", OUT.relative_to(build.ROOT), f"({side}x{side} grid, {n_scope:,} functions, {n_ok:,} lit)")


if __name__ == "__main__":
    main()
