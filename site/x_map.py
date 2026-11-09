"""Render reports/x_images/post1-map.mp4: one C/Lean translation, then a zoom out to a map of CPython.

Each tile is one in-scope function. The six parts of CPython are countries sized by their function counts,
unexplored functions are fog (gray), and functions accepted by review are explored (blue), spreading from a
capital in each country to that part's real coverage. Needs ffmpeg.

  python3 site/x_map.py
"""

import collections
import heapq
import math
import random
import subprocess
import sys
from pathlib import Path

from PIL import Image, ImageDraw

sys.path.insert(0, str(Path(__file__).resolve().parent))
import build  # noqa: E402
from og import BG, BLUE, C_CODE, LEAN_CODE, MUTED, SANS, TEXT, font  # noqa: E402
from x_video import code_card, ease, lean_snippets, snippet_card  # noqa: E402

W, H, FPS, SECONDS = 1600, 900, 30, 11
OUT = build.ROOT / "reports" / "x_images" / "post1-map.mp4"
GAP = 0.1
ASPECT = 9 / 16                      # tile height / width
# Fog colour per country (light, distinct neighbours) and capital position on the continent (0..1).
FOG = {"Lib": (203, 216, 233), "Modules": (238, 222, 194), "Objects": (200, 228, 208),
       "Python": (238, 207, 216), "Parser": (216, 206, 238), "Grammar": (240, 231, 186)}
EDGE = {a: tuple(int(c * 0.86) for c in rgb) for a, rgb in FOG.items()}
SEEDS = {"Lib": (0.27, 0.52), "Modules": (0.66, 0.24), "Objects": (0.63, 0.62),
         "Python": (0.86, 0.50), "Parser": (0.82, 0.83), "Grammar": (0.93, 0.74)}


def noise(x, y):
    """Smooth, deterministic noise for a ragged coastline and borders."""
    return (math.sin(x * 0.11 + 1.3) + math.sin(y * 0.13 + 0.4) + math.sin((x + y) * 0.07 + 2.1)
            + 0.6 * math.sin(x * 0.31 - y * 0.23)) / 3.6


def build_map(counts, rng):
    n = sum(counts.values())
    cols = int(math.sqrt(n / (math.pi / 4) / 0.79 * 1.0)) + 1
    rows = int(cols * 0.79) + 1
    cx, cy = cols / 2, rows / 2
    # Continent: the n cells with the smallest noisy elliptical radius.
    def radius(c, r):
        return math.hypot((c - cx) / cols, (r - cy) / rows) * (1 + 0.16 * noise(c, r))
    cells = sorted(((c, r) for r in range(rows) for c in range(cols)), key=lambda p: radius(*p))[:n]
    land = set(cells)
    # Countries: capacity-constrained growth from each capital, with noisy priorities.
    owner, size = {}, collections.Counter()
    heaps = {}
    for a, (sx, sy) in SEEDS.items():
        seed = min(land, key=lambda p: (p[0] - sx * cols) ** 2 + (p[1] - sy * rows) ** 2)
        heaps[a] = [(0.0, seed)]
    def key(a, p):
        sx, sy = SEEDS[a][0] * cols, SEEDS[a][1] * rows
        return math.hypot(p[0] - sx, (p[1] - sy) * 1.25) * (1 + 0.35 * noise(p[0] * 1.7, p[1] * 1.7)) + rng.random()
    while len(owner) < n:
        open_ = [a for a in heaps if size[a] < counts[a] and heaps[a]]
        if not open_:
            break
        a = min(open_, key=lambda a: size[a] / counts[a])
        while heaps[a]:
            _, p = heapq.heappop(heaps[a])
            if p not in owner:
                owner[p] = a
                size[a] += 1
                for q in ((p[0] + 1, p[1]), (p[0] - 1, p[1]), (p[0], p[1] + 1), (p[0], p[1] - 1)):
                    if q in land and q not in owner:
                        heapq.heappush(heaps[a], (key(a, q), q))
                break
    for p in cells:                      # any enclosed leftovers join a neighbouring country
        if p not in owner:
            for q in ((p[0] + 1, p[1]), (p[0] - 1, p[1]), (p[0], p[1] + 1), (p[0], p[1] - 1)):
                if q in owner:
                    owner[p] = owner[q]
                    break
            else:
                owner[p] = "Lib"
    rebalance(owner, counts, key)
    return cols, rows, owner


def nbrs(p):
    return ((p[0] + 1, p[1]), (p[0] - 1, p[1]), (p[0], p[1] + 1), (p[0], p[1] - 1))


def rebalance(owner, counts, key):
    """Move border cells along a chain of neighbouring countries until every country has its exact size."""
    for _ in range(5000):
        size = collections.Counter(owner.values())
        under = [a for a in counts if size[a] < counts[a]]
        if not under:
            return
        adj = collections.defaultdict(set)
        for p, a in owner.items():
            for q in nbrs(p):
                b = owner.get(q)
                if b and b != a:
                    adj[a].add(b)
        u = under[0]
        prev, queue, goal = {u: None}, [u], None
        while queue:
            a = queue.pop(0)
            if size[a] > counts[a]:
                goal = a
                break
            for b in sorted(adj[a]):
                if b not in prev:
                    prev[b] = a
                    queue.append(b)
        if goal is None:
            return
        b = goal
        while prev[b] is not None:            # move one cell from b into prev[b], back along the path
            a = prev[b]
            cand = [p for p, o in owner.items() if o == b and any(owner.get(q) == a for q in nbrs(p))]
            owner[min(cand, key=lambda p: key(a, p))] = a
            b = a


def main():
    files = build.coverage()
    area = collections.defaultdict(collections.Counter)
    for f, c in files.items():
        area[f.split("/")[0]].update(c)
    counts = {a: area[a]["rows"] - area[a]["excluded"] for a in build.AREA_ORDER}
    explored = {a: area[a]["faithful"] for a in build.AREA_ORDER}
    n_scope, n_ok = sum(counts.values()), sum(explored.values())
    lean_lines = sum(f.read_text().count("\n") for f in (build.ROOT / "lean" / "PyLean").rglob("*.lean"))
    nbugs, _ = build.bugs()
    rng = random.Random(11)
    cols, rows, owner = build_map(counts, rng)

    # Explored tiles: the cells of each country nearest its capital (noisy), in that order.
    by_area = collections.defaultdict(list)
    for p, a in owner.items():
        by_area[a].append(p)
    order = {}
    for a, ps in by_area.items():
        sx, sy = SEEDS[a][0] * cols, SEEDS[a][1] * rows
        ps.sort(key=lambda p: math.hypot(p[0] - sx, (p[1] - sy) * 1.25) * (1 + 0.45 * noise(p[0] * 0.9 + 7, p[1] * 0.9 + 3))
                + rng.random() * 3)
        for k, p in enumerate(ps[: explored[a]]):
            order[p] = (k + 0.5) / explored[a]        # fraction of the country's exploration at which it lights
    hero = min(by_area["Objects"], key=lambda p: (p[0] - SEEDS["Objects"][0] * cols) ** 2
               + (p[1] - SEEDS["Objects"][1] * rows) ** 2)
    order[hero] = 0.0
    border = {p for p, a in owner.items()
              if any(owner.get(q, a) != a for q in nbrs(p)) or any(q not in owner for q in nbrs(p))}
    centroid = {a: (sum(p[0] for p in ps) / len(ps), sum(p[1] for p in ps) / len(ps)) for a, ps in by_area.items()}

    hero_card = code_card(C_CODE, LEAN_CODE, 1440, 810, "CPython  ·  Objects/rangeobject.c",
                          "Lean copy  ·  RangeSlice/Model.lean")
    pool = [snippet_card(n, l, 720, 405) for n, l in lean_snippets(24)]
    fog_img = {(a, e): Image.new("RGB", (720, 405), (EDGE if e else FOG)[a]) for a in FOG for e in (False, True)}

    map_w, map_h = W - 120, H - 230                 # leave room for the bottom bar
    P1 = min(map_w / cols, map_h / (rows * ASPECT))
    P0 = 1260 / (1 - GAP)
    mcx, mcy = cols / 2, rows / 2
    t_hold, t_zoom_end, total = 1.5, 7.5, FPS * SECONDS
    ff = subprocess.Popen(["ffmpeg", "-y", "-loglevel", "error", "-f", "rawvideo", "-pix_fmt", "rgb24",
                           "-s", f"{W}x{H}", "-r", str(FPS), "-i", "-", "-c:v", "libx264", "-pix_fmt", "yuv420p",
                           "-crf", "18", "-preset", "slow", "-movflags", "+faststart", str(OUT)],
                          stdin=subprocess.PIPE)
    big, small = font(SANS, 40, 1), font(SANS, 28)
    label_big, label_small = font(SANS, 30, 1), font(SANS, 24, 1)
    cells = list(owner.items())
    for f in range(total):
        t = f / FPS
        z = ease((t - t_hold) / (t_zoom_end - t_hold))
        P = math.exp(math.log(P0) + (math.log(P1) - math.log(P0)) * z)
        Ph = P * ASPECT
        pan = ease(z * 1.15) ** 1.5                  # stay on the hero early, end on the whole map
        ccx = hero[0] + (mcx - hero[0]) * pan
        ccy = hero[1] + (mcy - hero[1]) * pan
        oy = -95 * pan                               # end slightly above centre, above the bar
        progress = ease((t - t_hold - 0.4) / (t_zoom_end - t_hold + 0.6))
        frame = Image.new("RGB", (W, H), BG)
        d = ImageDraw.Draw(frame)
        tw, th = max(1, int(P * (1 - GAP))), max(1, int(Ph * (1 - GAP)))
        detailed = tw >= 12
        k_blue = ease((64 - tw) / 50)
        hero_bar = ease((700 - tw) / 400)
        cache = {}
        lit = 0
        for p, a in cells:
            on = p in order and order[p] <= progress
            lit += on
            x = W / 2 + (p[0] - ccx) * P - tw / 2
            y = H / 2 + oy + (p[1] - ccy) * Ph - th / 2
            if x > W or y > H or x + tw < 0 or y + th < 0:
                continue
            if detailed:
                if p == hero:
                    key, src = ("hero",), hero_card
                elif on:
                    key, src = ("pool", hash(p) % len(pool)), pool[hash(p) % len(pool)]
                else:
                    key = ("fog", a, p in border)        # border tiles are darker at every zoom level
                    src = fog_img[(a, p in border)]
                if key not in cache:
                    tile = src.resize((tw, th), Image.LANCZOS)
                    if key[0] != "fog" and k_blue > 0:
                        tile = Image.blend(tile, Image.new("RGB", (tw, th), BLUE), k_blue)
                    cache[key] = tile
                frame.paste(cache[key], (int(x), int(y)))
                if on and (p != hero or hero_bar > 0):
                    bar_h = max(2, th * 0.04) * (hero_bar if p == hero else 1)
                    d.rectangle([x, y, x + tw, y + bar_h], fill=BLUE)
            else:
                # Even pixel edges: each tile spans its own pitch, with a uniform 1 px gap while tiles are visible.
                X, Y = x + tw / 2 - P / 2, y + th / 2 - Ph / 2
                g = 1 if P >= 5 else 0
                d.rectangle([round(X), round(Y), round(X + P) - 1 - g, round(Y + Ph) - 1 - (g if Ph >= 4 else 0)],
                            fill=BLUE if on else EDGE[a] if p in border else FOG[a])
        # Country names once the tiles are small.
        la = ease((26 - tw) / 14)
        if la > 0.05:
            for a in build.AREA_ORDER:
                gx, gy = centroid[a]
                x = W / 2 + (gx - ccx) * P
                y = H / 2 + oy + (gy - ccy) * Ph
                name = build.AREA_NAMES[a]
                pct = f"{100 * explored[a] / counts[a]:.0f}% explored"
                fnt, sub = (label_big, label_small) if counts[a] > 1000 else (label_small, font(SANS, 20, 1))
                col = tuple(int(255 - (255 - c) * la) for c in TEXT)
                d.text((x, y - 4), name, font=fnt, fill=col, anchor="md", stroke_width=4, stroke_fill=BG)
                d.text((x, y + 2), pct, font=sub, fill=tuple(int(255 - (255 - c) * la) for c in BLUE), anchor="ma",
                       stroke_width=4, stroke_fill=BG)
        if t < t_hold + 0.8:
            a0 = 1 - ease((t - t_hold) / 0.8)
            if a0 > 0.3:
                d.rectangle([0, 0, W, 88], fill=BG)
                d.text((W / 2, 46), "One CPython function and its Lean copy", font=font(SANS, 38, 1), fill=TEXT,
                       anchor="mm")
        if t >= t_hold and t < t_zoom_end + 0.8:
            alpha = ease((t - t_hold) / 0.6) * (1 - ease((t - t_zoom_end - 0.4) / 0.4))
            if alpha > 0.05:
                box = Image.new("RGBA", (W, H), (0, 0, 0, 0))
                ImageDraw.Draw(box).rounded_rectangle([40, H - 128, 760, H - 22], radius=18,
                                                      fill=(255, 255, 255, int(235 * alpha)))
                frame.paste(box, (0, 0), box)
                if alpha > 0.4:
                    d.text((70, H - 114), f"{lit:,} function{'' if lit == 1 else 's'} checked", font=big, fill=TEXT)
                    d.text((70, H - 66), f"of {n_scope:,} in CPython 3.15.2", font=small, fill=MUTED)
        if t >= t_zoom_end + 0.6:
            alpha = ease((t - t_zoom_end - 0.6) / 0.6)
            box = Image.new("RGBA", (W, H), (0, 0, 0, 0))
            ImageDraw.Draw(box).rectangle([0, H - 170, W, H], fill=(255, 255, 255, int(245 * alpha)))
            frame.paste(box, (0, 0), box)
            if alpha > 0.3:
                d.text((70, H - 152), "Formalizing CPython", font=font(SANS, 54, 1), fill=TEXT)
                d.text((70, H - 80), f"{n_ok:,} of {n_scope:,} functions checked  ·  {lean_lines:,} lines of Lean"
                       f"  ·  {nbugs:,} bug reports", font=font(SANS, 30), fill=BLUE)
                d.text((W - 70, H - 136), "broyojo.com/python-formalization", font=font(SANS, 24), fill=MUTED,
                       anchor="ra")
        ff.stdin.write(frame.tobytes())
    ff.stdin.close()
    ff.wait()
    print("wrote", OUT.relative_to(build.ROOT), f"({cols}x{rows} grid, {n_scope:,} functions, {lit:,} lit)",
          {a: (counts[a], explored[a]) for a in counts})


if __name__ == "__main__":
    main()
