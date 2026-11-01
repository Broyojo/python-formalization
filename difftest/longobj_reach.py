"""How often the longobj_diff.py generator reaches the rare branches of the C kernels.

A passing difftest says nothing about a branch it never took, so this counts operand
shapes, and runs Algorithm D in Python to count the q-hat correction and add-back.
Usage: python3 difftest/longobj_reach.py [--cases N]
"""

import argparse
import random
import sys

sys.set_int_max_str_digits(0)

import longobj_diff as d

B = 1 << 30


def ndigits(x):
    return (abs(x).bit_length() + 29) // 30


def to_digits(x):
    out = []
    while x:
        out.append(x & (B - 1))
        x >>= 30
    return out


def knuth_counts(v, w):
    """Mirror of x_divrem's quotient loop: count corrections and add-backs."""
    ws = to_digits(w)
    shift = 30 - ws[-1].bit_length()
    ws = to_digits(w << shift)
    vs = to_digits(v << shift)
    size_w = len(ws)
    while len(vs) < len(to_digits(v)) + 1:
        vs.append(0)
    if vs[-1] != 0 or vs[-2] >= ws[-1]:
        pass
    else:
        vs.pop()
    wm1, wm2 = ws[-1], ws[-2]
    corrections = addbacks = 0
    for k in range(len(vs) - size_w - 1, -1, -1):
        window = sum(vs[k + i] << (30 * i) for i in range(size_w + 1))
        vv = (vs[k + size_w] << 30) | vs[k + size_w - 1]
        q, r = vv // wm1, vv % wm1
        while wm2 * q > ((r << 30) | vs[k + size_w - 2]):
            q -= 1
            r += wm1
            corrections += 1
            if r >= B:
                break
        rem = window - q * (w << shift)
        if rem < 0:
            addbacks += 1
            rem += w << shift
            q -= 1
        for i in range(size_w + 1):
            vs[k + i] = (rem >> (30 * i)) & (B - 1)
    return corrections, addbacks


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", type=int, default=50000)
    args = ap.parse_args()
    rng = random.Random(1)
    n = dict.fromkeys(["mul", "kara", "square_gt_cutoff", "lopsided", "x_divrem", "corrections",
                       "addbacks", "pylong_divmod", "bin_pow", "win_pow"], 0)
    for _ in range(args.cases):
        c = d.gen_case(rng)
        fn, a, b = c["fn"], c.get("a"), c.get("b")
        if fn == "mul":
            lo, hi = sorted([ndigits(a), ndigits(b)])
            n["mul"] += 1
            if lo > 70:
                n["kara"] += 1
                if 2 * lo <= hi:
                    n["lopsided"] += 1
        elif fn == "square" and ndigits(a) > 140:
            n["square_gt_cutoff"] += 1
        elif fn in ("divmod", "floordiv", "mod") and b and ndigits(b) >= 2 and abs(a) >= abs(b):
            sa, sb = ndigits(a), ndigits(b)
            if fn != "mod" and sb > 300 and sa - sb > 150:
                n["pylong_divmod"] += 1
            else:
                n["x_divrem"] += 1
                co, ad = knuth_counts(abs(a), abs(b))
                n["corrections"] += co
                n["addbacks"] += ad
        elif fn in ("powmod", "pow") and b is not None and b >= 0:
            s = ndigits(b)
            if s > 2:
                n["win_pow"] += 1
            elif s >= 1 and b > 3:
                n["bin_pow"] += 1
    for k, v in n.items():
        print(f"{k:18s} {v}")


if __name__ == "__main__":
    main()
