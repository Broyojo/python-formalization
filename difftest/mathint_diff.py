"""Differential test: Lean model of math's integer functions and the related
int operations vs. the running CPython.

Usage: python3 difftest/mathint_diff.py [--cases N] [--seed S]

Exits non-zero on any mismatch. See difftest/common.py.
"""

import math
import sys

sys.set_int_max_str_digits(0)

import common

P63, P64 = 1 << 63, 1 << 64


def edge_nat(rng, big=True):
    """A non-negative int biased to the boundaries the C code branches on."""
    k = rng.randrange(1, 200 if big else 70)
    base = rng.choice([
        0, 1, 2, 3, 20, 21, 31, 32, 33, 34, 35, 62, 63, 64, 65, 66, 67, 68, 127, 128, 129,
        (1 << 30) - 1, 1 << 30, (1 << 60) - 1, 1 << 60, P63 - 1, P63, P63 + 1,
        P64 - 1, P64, P64 + 1, 1 << k, (1 << k) - 1, (1 << k) + 1,
        rng.randrange(1 << k), rng.randrange(1000), rng.randrange(1 << 64),
        rng.getrandbits(rng.randrange(1, 4000 if big else 70)),
    ])
    if not big and base > (1 << 70):
        base = rng.randrange(1 << 70)
    return base + rng.choice([0, 0, 0, -1, 1, rng.randrange(-3, 4)]) if base > 3 else base


def edge_int(rng, big=True):
    v = edge_nat(rng, big)
    return -v if rng.random() < 0.3 else v


# Limit tables of perm_comb_small: test both sides of every entry.
COMB1 = [0, 0] + [127] * 14 + [116, 105, 97, 91, 86, 82, 78, 76, 74, 72, 71, 70, 69, 68, 68,
                                67, 67, 67, 67]
COMB2 = [0, P64 - 1, 4294967296, 3329022, 102570, 13467, 3612, 1449, 746, 453, 308, 227, 178, 147]
PERM = [0, P64 - 1, 4294967296, 2642246, 65537, 7133, 1627, 568, 259, 142, 88, 61, 45, 36, 30,
        26, 24, 22, 21, 20, 20]


def comb_args(rng, perm):
    r = rng.random()
    if r < 0.35:
        table = PERM if perm else rng.choice([COMB1, COMB2])
        k = rng.randrange(2, len(table) + 2)
        lim = table[k] if k < len(table) else rng.randrange(40, 200)
        lim = min(lim, 1 << 40)
        n = max(0, lim + rng.randrange(-3, 4))
        if not perm and rng.random() < 0.5:
            k = n - k  # exercise k = min(k, n - k)
        return n, k
    if r < 0.55:
        n = rng.randrange(0, 300)
        return n, rng.randrange(-2, n + 3)
    if r < 0.7:
        # huge n with small k, or k near n
        n = rng.choice([P63 - 1, P63, P63 + 1, P64, rng.getrandbits(rng.randrange(1, 200))])
        k = rng.randrange(0, 40)
        if not perm and rng.random() < 0.5:
            k = n - k
        return n, k
    if r < 0.8:
        # OverflowError region: min(k, n - k) > LLONG_MAX, or k > n
        n = rng.choice([P64, P64 + 1, 1 << 65, 1 << 100, P63 - 1, P63])
        k = rng.choice([P63 - 1, P63, P63 + 1, n // 2, n + 1, n - P63, n - P63 + 1, 1 << 70])
        return n, k
    n, k = edge_int(rng, False), edge_int(rng, False)
    if n > 0 and k > 0 and 600 < min(k, max(n - k, 0)) < P63 and n >= k:
        return None  # result too large to compute quickly
    return n, k


def gen_case(rng):
    fn = rng.choice(["isqrt", "isqrt", "comb", "comb", "perm", "perm", "factorial", "gcd",
                     "lcm", "pow", "to_bytes", "to_bytes", "from_bytes", "divmod", "round"])
    c = {"mod": "mathint", "fn": fn}
    if fn == "isqrt":
        if rng.random() < 0.3:
            r = edge_nat(rng)
            n = r * r + rng.choice([-1, 0, 1, 2 * r, 2 * r + 1, rng.randrange(-2, 3)])
        else:
            n = edge_int(rng)
        c["n"] = n
    elif fn in ("comb", "perm"):
        a = comb_args(rng, fn == "perm")
        if a is None:
            return None
        n, k = a
        if n >= 0 and k >= 0 and n >= k and 3000 < min(k, n - k) < P63:
            return None
        if fn == "perm" and n >= 0 and k >= 0 and n >= k and 600 < k < P63:
            return None
        c.update(n=n, k=k)
        if fn == "perm" and rng.random() < 0.1:
            c.update(n=rng.randrange(-3, 400), k=None)
    elif fn == "factorial":
        c["n"] = rng.choice([rng.randrange(-3, 3000), rng.randrange(-3, 40), P63 - 1 + 1, P63,
                             -P63, -P63 - 1, -(1 << 70), 1 << 70, P64])
        if c["n"] == P63 - 1:
            return None
    elif fn in ("gcd", "lcm"):
        m = rng.choice([0, 1, 2, 2, 2, 3, 4, 6])
        common_f = edge_nat(rng) if rng.random() < 0.5 else 1
        args = []
        for _ in range(m):
            v = edge_int(rng) * (common_f if rng.random() < 0.7 else 1)
            if rng.random() < 0.1:
                v = rng.choice([0, 1, -1])
            args.append(v)
        if fn == "lcm" and sum(abs(a).bit_length() for a in args) > 20000:
            return None
        c["args"] = args
    elif fn == "pow":
        m = edge_int(rng, rng.random() < 0.2)
        if rng.random() < 0.1:
            m = rng.choice([0, 1, -1, 2, -2])
        a = edge_int(rng, rng.random() < 0.2)
        if rng.random() < 0.3 and m:
            a = a * abs(m) + rng.choice([1, -1, 0])
        b = rng.choice([-1, -1, -2, -3, -rng.randrange(1, 1000), 0, 1, 2, rng.randrange(100),
                        -edge_nat(rng, False)])
        c.update(a=a, b=b, m=m)
    elif fn == "to_bytes":
        v = edge_int(rng, rng.random() < 0.3)
        nb = (abs(v).bit_length() + 8) // 8
        length = rng.choice([nb, nb - 1, nb + 1, nb - 2, 0, 1, rng.randrange(0, 20), -1,
                             -P63, -P63 - 1, P63, (abs(v).bit_length() + 7) // 8])
        c.update(v=v, length=length, signed=rng.random() < 0.5,
                 byteorder=rng.choice(["big", "little", "big", "little", "mid", "Big"]))
    elif fn == "from_bytes":
        n = rng.choice([0, 1, 2, 3, 4, 7, 8, 9, 15, 16, 17, rng.randrange(0, 60)])
        fill = rng.choice([None, 0, 255, 128, 127])
        bs = [rng.randrange(256) if fill is None or rng.random() < 0.2 else fill for _ in range(n)]
        c.update(bytes=bs, signed=rng.random() < 0.5,
                 byteorder=rng.choice(["big", "little", "big", "little", "mid"]))
    elif fn == "divmod":
        r = rng.random()
        if r < 0.15:
            b = edge_int(rng) | (1 << rng.randrange(9001, 9500))
            a = b * rng.getrandbits(rng.randrange(4500, 7000)) + rng.randrange(-5, 5)
            a, b = (a, b) if rng.random() < 0.5 else (-a, b)
            if rng.random() < 0.5:
                b = -b
        else:
            a, b = edge_int(rng), edge_int(rng)
            if rng.random() < 0.1:
                b = rng.choice([0, 1, -1])
        c.update(a=a, b=b)
    elif fn == "round":
        k = rng.randrange(0, 60)
        x = edge_int(rng, False)
        if rng.random() < 0.4:
            x = (rng.randrange(-1000, 1000) * 2 + 1) * 5 * 10 ** k // 10 if k else x  # ties
        c.update(x=x, nd=rng.choice([None, -k, -k, k, 0, -1]))
    return c


def run_python(c):
    fn = c["fn"]
    if fn == "isqrt":
        return common.py_result(lambda: math.isqrt(c["n"]))
    if fn == "comb":
        return common.py_result(lambda: math.comb(c["n"], c["k"]))
    if fn == "perm":
        return common.py_result(lambda: math.perm(c["n"], c["k"]))
    if fn == "factorial":
        return common.py_result(lambda: math.factorial(c["n"]))
    if fn == "gcd":
        return common.py_result(lambda: math.gcd(*c["args"]))
    if fn == "lcm":
        return common.py_result(lambda: math.lcm(*c["args"]))
    if fn == "pow":
        return common.py_result(lambda: pow(c["a"], c["b"], c["m"]))
    if fn == "to_bytes":
        return common.py_result(lambda: list(c["v"].to_bytes(c["length"], c["byteorder"],
                                                             signed=c["signed"])))
    if fn == "from_bytes":
        return common.py_result(lambda: int.from_bytes(bytes(c["bytes"]), c["byteorder"],
                                                       signed=c["signed"]))
    if fn == "divmod":
        return common.py_result(lambda: list(divmod(c["a"], c["b"])))
    if fn == "round":
        return common.py_result(lambda: round(c["x"]) if c["nd"] is None else round(c["x"], c["nd"]))
    raise ValueError(fn)


if __name__ == "__main__":
    common.main(gen_case, run_python)
