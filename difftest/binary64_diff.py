"""Differential test: exact binary64 model and float code vs. the running CPython.

Usage: python3 difftest/binary64_diff.py [--cases N] [--seed S]

Exits non-zero on any mismatch. See difftest/common.py.

A float travels as its 64-bit pattern (an int), and a NaN result as the string
"nan". Generation is edge-heavy: signed zeros, subnormal boundaries, powers of
two and their neighbours, values next to halfway cases, and random patterns.
"""

import fractions
import math
import random
import struct
import sys

import common


def to_bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def of_bits(b):
    return struct.unpack("<d", struct.pack("<Q", b))[0]


def enc(x):
    return "nan" if x != x else to_bits(x)


SIGN = 1 << 63
PLAIN = [
    0, 1, 2, 3, (1 << 52) - 1, 1 << 52, (1 << 52) + 1, (1 << 53) - 1, 1 << 53,
    0x000fffffffffffff, 0x0010000000000000, 0x0010000000000001, 0x001fffffffffffff,
    0x0020000000000000, 0x3cb0000000000000, 0x3ca0000000000000, 0x3fe0000000000000,
    0x3fefffffffffffff, 0x3ff0000000000000, 0x3ff0000000000001, 0x3ff8000000000000,
    0x4000000000000000, 0x4008000000000000, 0x4330000000000000, 0x4330000000000001,
    0x4340000000000000, 0x4340000000000001, 0x7fe0000000000000, 0x7fefffffffffffff,
    0x7ff0000000000000, 0x7ff8000000000000, 0x7ff0000000000001,
]


def edge_bits(rng):
    k = rng.random()
    if k < 0.25:
        b = rng.choice(PLAIN)
    elif k < 0.4:  # a power of two and its neighbours
        b = (rng.randrange(0, 2047) << 52) + rng.choice([0, 1, 2, (1 << 52) - 1])
    elif k < 0.55:  # subnormals with few or many bits
        b = rng.getrandbits(rng.randrange(1, 53))
    elif k < 0.7:  # small integers and simple fractions
        b = to_bits(float(rng.randrange(-4096, 4096)) / rng.choice([1, 2, 3, 4, 8, 10, 16, 1024]))
    elif k < 0.85:  # near 1, so that sums and products land on halfway cases
        b = (rng.randrange(1000, 1046) << 52) | (rng.getrandbits(rng.randrange(1, 53)) << rng.randrange(0, 40)) & ((1 << 52) - 1)
    else:
        b = rng.getrandbits(64)
    if rng.random() < 0.5:
        b ^= SIGN
    return b


def edge_float(rng):
    return edge_bits(rng)


def halfway_pair(rng):
    """Two floats whose exact sum is a halfway case, or close to one."""
    e = rng.randrange(1, 2000)
    m = rng.getrandbits(52) | 1
    a = (e << 52) | m
    d = 53 + rng.choice([0, 0, 1, -1, 2])
    b = ((max(1, e - d)) << 52) | rng.choice([0, 1, (1 << 52) - 1])
    return a, b


def edge_int(rng):
    k = rng.randrange(1, 70)
    n = rng.choice([
        0, 1, 2, 3, 2 ** 53, 2 ** 53 + 1, 2 ** 53 + 2, 2 ** 53 + 3, 2 ** 54 + 2, 2 ** 54 + 6,
        2 ** 63, 2 ** 64, 2 ** 1024, 2 ** 1024 - 2 ** 970, 2 ** 1024 - 2 ** 970 - 1,
        2 ** 1024 - 2 ** 971, 2 ** 1024 - 2 ** 970 + 1,
        rng.getrandbits(k), rng.getrandbits(1100), (1 << k) + 1, (1 << k) - 1,
    ])
    return -n if rng.random() < 0.5 else n


UNARY = ["sqrt", "floor", "ceil", "trunc", "roundAway", "neg", "abs", "ulp", "frexp"]
BINARY = ["add", "sub", "mul", "div", "fmod", "copysign", "nextafter",
          "eq", "ne", "lt", "le", "gt", "ge"]


def gen_case(rng):
    k = rng.random()
    if k < 0.25:
        fn = rng.choice(UNARY)
        return {"mod": "binary64", "fn": fn, "x": edge_float(rng)}
    if k < 0.75:
        fn = rng.choice(BINARY)
        if fn in ("add", "sub") and rng.random() < 0.4:
            a, b = halfway_pair(rng)
            if rng.random() < 0.5:
                a, b = b, a
            return {"mod": "binary64", "fn": fn, "x": a, "y": b}
        x = edge_float(rng)
        y = x if rng.random() < 0.05 else edge_float(rng)
        return {"mod": "binary64", "fn": fn, "x": x, "y": y}
    if k < 0.85:
        return {"mod": "binary64", "fn": "fma", "x": edge_float(rng), "y": edge_float(rng),
                "z": edge_float(rng)}
    if k < 0.9:
        n = rng.choice([0, 1, -1, 2, -2, 52, 53, -52, -53, 1023, 1024, -1022, -1074, -1075,
                        2098, -2098, 2200, -2200, 2201, -2201, rng.randrange(-2300, 2300)])
        return {"mod": "binary64", "fn": "ldexp", "x": edge_float(rng), "n": n}
    if k < 0.95:
        return {"mod": "binary64", "fn": "ofInt", "n": edge_int(rng)}
    return {"mod": "binary64", "fn": "ratio", "n": edge_int(rng),
            "d": abs(edge_int(rng)) or 1}


def run_python(c):
    fn = c["fn"]
    x = of_bits(c["x"]) if "x" in c else None
    y = of_bits(c["y"]) if "y" in c else None
    if fn == "add":
        return {"ok": enc(x + y)}
    if fn == "sub":
        return {"ok": enc(x - y)}
    if fn == "mul":
        return {"ok": enc(x * y)}
    if fn == "div":
        return {"ok": enc(c_div(x, y))}
    if fn == "fma":
        return {"ok": enc(fma(x, y, of_bits(c["z"])))}
    if fn == "sqrt":
        return {"ok": enc(c_sqrt(x))}
    if fn == "fmod":
        return {"ok": enc(c_fmod(x, y))}
    if fn == "eq":
        return {"ok": x == y}
    if fn == "ne":
        return {"ok": x != y}
    if fn == "lt":
        return {"ok": x < y}
    if fn == "le":
        return {"ok": x <= y}
    if fn == "gt":
        return {"ok": x > y}
    if fn == "ge":
        return {"ok": x >= y}
    if fn == "floor":
        return {"ok": enc(c_floor(x))}
    if fn == "ceil":
        return {"ok": enc(c_ceil(x))}
    if fn == "trunc":
        return {"ok": enc(c_trunc(x))}
    if fn == "roundAway":
        return {"ok": enc(c_round(x))}
    if fn == "neg":
        return {"ok": enc(-x)}
    if fn == "abs":
        return {"ok": enc(abs(x))}
    if fn == "copysign":
        return {"ok": enc(math.copysign(x, y))}
    if fn == "nextafter":
        return {"ok": enc(math.nextafter(x, y))}
    if fn == "ulp":
        return {"ok": enc(math.ulp(x))}
    if fn == "frexp":
        m, e = math.frexp(x)
        return {"ok": [enc(m), e]}
    if fn == "ldexp":
        try:
            return {"ok": enc(math.ldexp(x, c["n"]))}
        except OverflowError:  # math.ldexp raises where C ldexp returns an infinity
            return {"ok": enc(math.copysign(math.inf, x))}
    if fn == "ofInt":
        try:
            return {"ok": enc(float(c["n"]))}
        except OverflowError:  # the model has no overflow check at this layer
            return {"ok": enc(math.inf if c["n"] > 0 else -math.inf)}
    if fn == "ratio":
        return {"ok": enc(ratio_float(c["n"], c["d"]))}
    raise ValueError(fn)


def c_div(x, y):
    """x / y with IEEE semantics; Python raises on y == 0."""
    if y == 0.0:
        if x != x or x == 0.0:
            return math.nan
        s = math.copysign(1.0, x) * math.copysign(1.0, y)
        return math.copysign(math.inf, s)
    return x / y


def fma(x, y, z):
    try:
        return math.fma(x, y, z)
    except ValueError:  # invalid operation: NaN in C
        return math.nan
    except OverflowError:  # a finite overflow: the signed infinity in C
        return exact_inf(fractions.Fraction(x) * fractions.Fraction(y) + fractions.Fraction(z))


def exact_inf(q):
    return math.inf if q > 0 else -math.inf


def c_sqrt(x):
    if x != x:
        return math.nan
    if x < 0:
        return math.nan
    return math.sqrt(x)


def c_fmod(x, y):
    if x != x or y != y or math.isinf(x) or y == 0.0:
        return math.nan
    return math.fmod(x, y)


def c_floor(x):
    if x != x or math.isinf(x) or x == 0.0:
        return x
    r = float(math.floor(x))
    return math.copysign(r, x)


def c_ceil(x):
    if x != x or math.isinf(x) or x == 0.0:
        return x
    r = float(math.ceil(x))
    return math.copysign(r, x)


def c_trunc(x):
    if x != x or math.isinf(x) or x == 0.0:
        return x
    return math.copysign(float(math.trunc(x)), x)


def c_round(x):
    """C round(): halfway cases away from zero, sign kept on a zero result."""
    if x != x or math.isinf(x) or x == 0.0:
        return x
    q = abs(fractions.Fraction(x)) + fractions.Fraction(1, 2)
    return math.copysign(float(math.floor(q)), x)


def ratio_float(n, d):
    try:
        return n / d
    except OverflowError:
        return math.inf if n > 0 else -math.inf


common.main(gen_case, run_python, default_cases=50000)
