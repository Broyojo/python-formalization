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


# ---------------------------------------------------------------------------
# float object layer
# ---------------------------------------------------------------------------

sys.set_int_max_str_digits(0)


def enc_obj(rng, ints=True):
    k = rng.random()
    if not ints or k < 0.6:
        return {"f": edge_float(rng)}
    if k < 0.97:
        return {"i": edge_int(rng)}
    return {"o": "str"}


def py_obj(o):
    if "f" in o:
        return of_bits(o["f"])
    if "i" in o:
        return o["i"]
    return "text"


def enc_any(r):
    if r is NotImplemented:
        return "NotImplemented"
    if isinstance(r, float):
        return enc(r)
    if isinstance(r, tuple):
        return [enc_any(i) for i in r]
    if isinstance(r, complex):
        return "complex"
    return r


BIN_NAMES = {"f_add": "add", "f_sub": "sub", "f_mul": "mul", "f_div": "truediv", "f_rem": "mod",
             "f_floordiv": "floordiv", "f_divmod": "divmod", "f_pow": "pow"}


def bin_call(fn, v, w):
    name = BIN_NAMES[fn]
    if isinstance(v, float):
        return getattr(float, f"__{name}__")(v, w)
    if isinstance(w, float):
        return getattr(float, f"__r{name}__")(w, v)
    return NotImplemented


HEXCH = "0123456789abcdefABCDEF"
SPACE = [" ", "\t", "\n", "\r", "\x0b", "\x0c", ""]


def hex_string(rng):
    k = rng.random()
    if k < 0.3:
        s = of_bits(edge_bits(rng)).hex()
    elif k < 0.5:
        # around the rounding boundary: more digits than a double holds
        n = rng.randrange(1, 20)
        s = "0x" + "".join(rng.choice(["0", "8", "f", "1", rng.choice(HEXCH)]) for _ in range(n))
        s += "." + "".join(rng.choice(["0", "8", "f", "1", rng.choice(HEXCH)])
                           for _ in range(rng.randrange(0, 20)))
        s += "p" + str(rng.choice([0, 1, -1, 1023, 1024, -1022, -1074, -1075, -1076, 2000, -2000,
                                   971, 970, 972, rng.randrange(-1200, 1200)]))
    elif k < 0.75:
        mant = rng.choice(["1", "1.8", "1.fffffffffffff8", "1.fffffffffffff7", "1.fffffffffffff80001",
                           "0.8", "0.0", "0", ".8", "8.", "10000000000000080", "1000000000000008",
                           "1.00000000000008", "1.00000000000018", "1.000000000000080000001",
                           "0.00000000000000000000001", "ffffffffffffffff", "f" * 40, "1" * 30,
                           "00000000000000000000000000000001", "1." + "0" * 60 + "1"])
        s = rng.choice(["", "0x", "0X"]) + mant
        s += rng.choice(["", "p", "P"]) + rng.choice(["0", "+1", "-1", "1023", "1024", "-1022", "-1074",
                                                     "-1075", "-1076", "-1073", "+2000", "-2000",
                                                     "99999999999999999999", "-99999999999999999999",
                                                     "9223372036854775807", "-9223372036854775808",
                                                     "4611686018427387904", "-4611686018427387905",
                                                     "4611686018427387903", "-4611686018427387904"])
    else:
        s = rng.choice(["inf", "-inf", "+INF", "infinity", "Infinity", "-iNfInItY", "nan", "-nan",
                        "+NaN", "NAN", "in", "na", "infin", "", " ", "-", "+", "0x", "0x.", ".",
                        "p1", "0xp1", "1p", "1p+", "1p-", "1e5", "0x1p", "x1", "1.2.3", "--1", "+-1",
                        "1_0", "1 2", "0xg", "1\x00", "\x001", "1\x00 ", "١", "\xa01", "1\xa0"])
    if rng.random() < 0.3:
        s = ("-" if rng.random() < 0.5 else "+") + s
    if rng.random() < 0.3:
        s = rng.choice(SPACE) + s + rng.choice(SPACE)
    if rng.random() < 0.08:
        i = rng.randrange(0, len(s) + 1)
        s = s[:i] + rng.choice(["x", "p", ".", "_", "0", "-", "\x00", " ", "é"]) + s[i:]
    return s


def decimal_string(rng):
    k = rng.random()
    if k < 0.2:
        return repr(of_bits(edge_bits(rng)))
    if k < 0.45:
        # an exact halfway point between two doubles, or just off it
        x = abs(of_bits(edge_bits(rng) & 0x7fffffffffffffff))
        if x != x or math.isinf(x) or x == sys.float_info.max:
            x = 1.0
        q = (fractions.Fraction(x) + fractions.Fraction(math.nextafter(x, math.inf))) / 2
        e = 0
        d = q.denominator
        while d > 1:
            d >>= 1
            e += 1
        n = q.numerator * 5 ** e
        s = str(n)
        p = rng.random()
        if p < 0.4:
            s = s + "0" * rng.randrange(0, 5)
            e += len(s) - len(str(n))
        elif p < 0.6:
            s = s + "0" * rng.randrange(1, 30) + "1"
            e += len(s) - len(str(n))
        elif p < 0.8:
            s = str(n - 1) + "9" * rng.randrange(1, 30)
            e += len(s) - len(str(n))
        cut = rng.randrange(0, len(s) + 1)
        if rng.random() < 0.5:
            return f"{s[:cut] or '0'}.{s[cut:]}e{-e + len(s) - cut}"
        return f"{s}e{-e}"
    if k < 0.7:
        nd = rng.choice([1, 2, 8, 9, 10, 15, 16, 17, 18, 19, 22, 39, 40, 41, 42, 60, 100, 800])
        digs = "".join(rng.choice("0123456789") for _ in range(nd))
        e = rng.choice([0, 1, -1, 22, 23, 37, -22, -23, 308, 309, -308, -323, -324, -325, -340, 300,
                        -300, -256, -240, 400, -400, rng.randrange(-350, 350)])
        cut = rng.randrange(0, nd + 1)
        return digs[:cut] + rng.choice([".", ""]) + digs[cut:] + rng.choice(["e", "E"]) + str(e)
    if k < 0.85:
        return rng.choice(["1e23", "9007199254740993", "8.41e21", "2.2250738585072012e-308",
                           "2.2250738585072011e-308", "1.7976931348623157e308",
                           "1.7976931348623158e308", "1.7976931348623159e308", "4.9e-324",
                           "2.4703282292062328e-324", "2.4703282292062327e-324", "1e400",
                           "-1e400", "1e-400", "-1e-400", "0e400", "0.0e-400", "00000.000", ".0",
                           "0.", ".", "e5", "1e", "1e+", "1e-", "1.e5", ".5e5", "+.5", "-.5e-5",
                           "1e99999999999999", "1e-99999999999999", "0e99999999999999",
                           "1e1100000000", "1e1100000001", "1e4294967296", "1e4294967297",
                           "1e-4294967297", "1e0000000000000000000000000000001"])
    return rng.choice(["inf", "-inf", "+INF", "infinity", "Infinity", "nan", "-nan", "+NaN", "in",
                       "infinit", "infinityx", "nanx", "1_000", "1__0", "_1", "1_", "1_.5", "1._5",
                       "1.5_5", "1e1_0", "1_e5", "1e_5", "١٢٣", "1٢", "１２", "\xa01\xa0", " 1",
                       "1\x00", "\x001", "1\x00_", "é", "1é", "  1  ", "\t1\n", " ", "", "\x0b1",
                       "1 2", "0x10", "١_٢", "1_٢", "\x1f1", "\x851", "1\x7f", "١\x7f"])


def run_float(c):
    fn = c["fn"]
    if fn in BIN_NAMES:
        v, w = py_obj(c["v"]), py_obj(c["w"])
        r = common.py_result(lambda: enc_any(bin_call(fn, v, w)))
        if r.get("msg") == "complex exponentiation":  # complex_pow took over
            return {"ok": "complex"}
        return r
    x = of_bits(c["x"]) if "x" in c else None
    if fn == "f_cmp":
        w = py_obj(c["w"])
        return {"ok": enc_any(getattr(float, f"__{c['op']}__")(x, w))}
    if fn == "f_hash":
        return {"ok": None if x != x else hash(x)}
    if fn == "f_is_integer":
        return {"ok": x.is_integer()}
    if fn == "f_trunc":
        return common.py_result(lambda: math.trunc(x))
    if fn == "f_floor":
        return common.py_result(lambda: math.floor(x))
    if fn == "f_ceil":
        return common.py_result(lambda: math.ceil(x))
    if fn == "f_round0":
        return common.py_result(lambda: round(x))
    if fn == "f_round":
        return common.py_result(lambda: enc(round(x, c["n"])))
    if fn == "f_hex":
        return {"ok": x.hex()}
    if fn == "f_fromhex":
        s = bytes(c["b"]).decode("utf-8")
        return common.py_result(lambda: enc(float.fromhex(s)))
    if fn == "f_ratio":
        return common.py_result(lambda: list(x.as_integer_ratio()))
    if fn in ("pack2", "pack4", "pack8"):
        code = {"pack2": "e", "pack4": "f", "pack8": "d"}[fn]
        e = "<" if c["le"] else ">"
        return common.py_result(lambda: list(struct.pack(e + code, x)))
    if fn in ("unpack2", "unpack4", "unpack8"):
        code = {"unpack2": "e", "unpack4": "f", "unpack8": "d"}[fn]
        e = "<" if c["le"] else ">"
        r = struct.unpack(e + code, bytes(c["b"]))[0]
        return {"ok": to_bits(r)}
    if fn == "repr":
        return {"ok": repr(x)}
    if fn == "fmt":
        code = chr(c["code"])
        if c["z"]:
            return {"ok": format(x, f"z.{c['p']}{code}")}
        if c["dot0"]:
            return {"ok": format(x, f".{c['p']}")}
        return {"ok": ("%" + ("+" if c["sign"] else "") + ("#" if c["alt"] else "")
                       + f".{c['p']}{code}") % x}
    if fn == "parse":
        a = "".join(map(chr, c["cps"])) if "cps" in c else bytes(c["bytes"])
        return common.py_result(lambda: enc(float(a)))
    if fn == "getformat":
        return common.py_result(lambda: float.__getformat__(c["t"]))
    if fn == "asdouble":
        o = py_obj(c["v"])
        return common.py_result(lambda: enc(math.nextafter(o, o)))
    if fn == "info":
        i = sys.float_info
        return {"ok": [to_bits(i.max), i.max_exp, i.max_10_exp, to_bits(i.min), i.min_exp,
                       i.min_10_exp, i.dig, i.mant_dig, to_bits(i.epsilon), i.radix, i.rounds]}
    raise ValueError(fn)


FLOAT_BIN = list(BIN_NAMES)


def int_for_compare(rng, x):
    """Ints close to the float x, so that the 48-bit and 1024-bit branches get hit."""
    v = of_bits(x)
    if v != v or math.isinf(v):
        return edge_int(rng)
    t = int(v)
    k = rng.random()
    if k < 0.4:
        return t + rng.choice([0, 0, 1, -1, 2, -2])
    if k < 0.6:
        return t * 2 + rng.choice([0, 1])
    if k < 0.8:
        return (1 if v >= 0 else -1) * (2 ** rng.choice([47, 48, 49, 52, 53, 54, 1023, 1024, 1025])
                                        + rng.choice([0, 1, -1]))
    return edge_int(rng)


def gen_float_case(rng):
    k = rng.random()
    m = {"mod": "binary64"}
    if k < 0.2:
        fn = rng.choice(FLOAT_BIN)
        v, w = enc_obj(rng), enc_obj(rng)
        if "f" not in v and "f" not in w:
            v = {"f": edge_float(rng)}
        return {**m, "fn": fn, "v": v, "w": w}
    if k < 0.3:
        x = edge_float(rng)
        return {**m, "fn": "f_cmp", "x": x, "w": {"i": int_for_compare(rng, x)} if rng.random() < .8
                else enc_obj(rng), "op": rng.choice(["lt", "le", "eq", "ne", "gt", "ge"])}
    if k < 0.38:
        return {**m, "fn": rng.choice(["f_hash", "f_is_integer", "f_trunc", "f_floor", "f_ceil",
                                       "f_round0", "f_hex", "f_ratio", "repr"]), "x": edge_float(rng)}
    if k < 0.46:
        x = edge_float(rng)
        n = rng.choice([0, 1, 2, -1, 5, 15, 16, 17, 22, 300, 308, 323, 324, -308, -309, -300,
                        2 ** 63, -2 ** 63, 2 ** 70, -2 ** 70, rng.randrange(-330, 330)])
        return {**m, "fn": "f_round", "x": x, "n": n}
    if k < 0.56:
        return {**m, "fn": "f_fromhex", "b": list(hex_string(rng).encode("utf-8"))}
    if k < 0.62:
        fn = rng.choice(["pack2", "pack4", "pack8"])
        x = edge_float(rng)
        if rng.random() < 0.5:
            # values at the edge of the narrower formats
            p = 11 if fn == "pack2" else 24
            e = rng.choice([-25, -24, -15, -14, 15, 16] if fn == "pack2" else
                           [-150, -149, -127, -126, 127, 128])
            v = (1 << p) + rng.choice([0, 1, 2, -1, -2, 3, (1 << p) - 1, rng.randrange(0, 1 << p)])
            x = to_bits(math.ldexp(v, e - p) + rng.choice([0.0, 2.0 ** (e - 40), -2.0 ** (e - 40)]))
        return {**m, "fn": fn, "x": x, "le": rng.random() < .5}
    if k < 0.66:
        n = rng.choice([2, 4, 8])
        b = [rng.getrandbits(8) for _ in range(n)]
        if rng.random() < 0.4:  # force an all-ones exponent for NaNs and infinities
            b[0] |= {2: 0x7c, 4: 0x7f, 8: 0x7f}[n]
            if n > 2:
                b[1] |= {4: 0x80, 8: 0xf0}[n]
        le = rng.random() < .5
        if le:
            b.reverse()
        return {**m, "fn": f"unpack{n}", "b": b, "le": le}
    if k < 0.8:
        code = rng.choice([101, 69, 102, 70, 103, 71])
        p = rng.choice([0, 1, 2, 3, 5, 6, 12, 14, 15, 16, 17, 18, 20, 30, 100, 350, 1100,
                        rng.randrange(0, 40)])
        q = rng.random()
        if rng.random() < 0.5:
            x = edge_float(rng)
        else:
            x = to_bits(rng.choice([1, -1]) * round(rng.random() * 10 ** rng.randrange(-5, 25),
                                                    rng.randrange(0, 5)))
        flags = {"sign": False, "dot0": False, "alt": False, "z": False}
        if q < 0.15:
            flags["alt"] = True
        elif q < 0.3:
            flags["sign"] = True
        elif q < 0.4:
            flags["z"] = True
            code = 102
        elif q < 0.5:
            flags["dot0"] = True
            code = 103
            p = max(p, 1)
        return {**m, "fn": "fmt", "x": x, "code": code, "p": p, **flags}
    if k < 0.97:
        s = decimal_string(rng)
        q = rng.random()
        if q < 0.1:
            s = rng.choice(["-", "+"]) + s
        elif q < 0.2:
            s = rng.choice(SPACE) + s + rng.choice(SPACE)
        elif q < 0.25:
            i = rng.randrange(0, len(s) + 1)
            s = s[:i] + rng.choice(["x", ".", "_", "0", "-", "e", "\x00", " ", "é"]) + s[i:]
        if rng.random() < 0.1:
            return {**m, "fn": "parse", "bytes": list(s.encode("utf-8"))}
        return {**m, "fn": "parse", "cps": [ord(ch) for ch in s]}
    if k < 0.98:
        return {**m, "fn": "getformat", "t": rng.choice(["double", "float", "x", ""])}
    if k < 0.99:
        return {**m, "fn": "info"}
    return {**m, "fn": "asdouble", "v": enc_obj(rng)}


# ---------------------------------------------------------------------------
# complex
# ---------------------------------------------------------------------------

PART = [0, SIGN, 1, 0x3ff0000000000000, 0xbff0000000000000, 0x7ff0000000000000, 0xfff0000000000000,
        0x7ff8000000000000, 0x7fefffffffffffff, 0x4000000000000000, 0x3fe0000000000000]


def part(rng):
    return rng.choice(PART) if rng.random() < 0.5 else edge_float(rng)


def c_operand(rng, real=True):
    k = rng.random()
    if not real or k < 0.7:
        return {"c": [part(rng), part(rng)]}
    if k < 0.9:
        return {"f": part(rng)}
    return {"i": rng.choice([0, 1, -1, 2, 3, 10, 2 ** 53 + 1, -2 ** 70, 10 ** 400])}


def py_c(o):
    if "c" in o:
        return complex(of_bits(o["c"][0]), of_bits(o["c"][1]))
    return py_obj(o)


def enc_c(z):
    return [enc(z.real), enc(z.imag)]


NICE_PARTS = ["0", "1", "-1", "1.5", "-2.5e3", "1e400", "-1e400", "inf", "-inf", "nan", "-nan", "infinity",
              ".5", "5.", "1_0", "1e5", "0.0", "-0.0"]


def complex_string(rng):
    k = rng.random()
    a, b = rng.choice(NICE_PARTS), rng.choice(NICE_PARTS)
    sign = rng.choice(["+", "-"])
    s = rng.choice([a, a + "j", a + sign + b.lstrip("+-") + "j", a + sign + "j", sign + "j", "j", "J",
                    a + "J", "", " ", "(", ")", "()", "(" + a + ")", "(" + a + sign + "j", a + "+", a + "j" + b,
                    "1+2", "1+2i", "++1", "1 + 2j", "1\x00", "1_+2j", "١+٢j", "\xa01j\xa0", "1j\x00"])
    if k < 0.3:
        s = rng.choice(SPACE) + s + rng.choice(SPACE)
    elif k < 0.5:
        s = rng.choice(SPACE) + "(" + rng.choice(SPACE) + s + rng.choice(SPACE) + ")" + rng.choice(SPACE)
    return s


def gen_complex_case(rng):
    m = {"mod": "binary64"}
    k = rng.random()
    if k < 0.5:
        fn = rng.choice(["c_add", "c_sub", "c_mul", "c_div"])
        v, w = c_operand(rng), c_operand(rng)
        if "c" not in v and "c" not in w:
            v = c_operand(rng, real=False)
        return {**m, "fn": fn, "v": v, "w": w}
    if k < 0.65:
        v, w = c_operand(rng), c_operand(rng)
        if "c" not in v and "c" not in w:
            v = c_operand(rng, real=False)
        if rng.random() < 0.7:
            w = {"f": to_bits(float(rng.randrange(-101, 102)))}
            if "c" not in v:
                v = c_operand(rng, real=False)
        return {**m, "fn": "c_pow", "v": v, "w": w}
    if k < 0.8:
        fn = rng.choice(["c_neg", "c_conj", "c_bool", "c_repr", "c_abs"])
        return {**m, "fn": fn, "v": c_operand(rng, real=False)}
    if k < 0.9:
        return {**m, "fn": "c_eq", "v": c_operand(rng, real=False), "w": c_operand(rng),
                "op": rng.choice(["eq", "ne", "lt", "ge"])}
    return {**m, "fn": "c_parse", "cps": [ord(ch) for ch in complex_string(rng)]}


C_BIN = {"c_add": "add", "c_sub": "sub", "c_mul": "mul", "c_div": "truediv", "c_pow": "pow"}


def run_complex(c):
    fn = c["fn"]
    if fn in C_BIN:
        v, w = py_c(c["v"]), py_c(c["w"])
        name = C_BIN[fn]

        def call():
            if isinstance(v, complex):
                return enc_c(getattr(complex, f"__{name}__")(v, w))
            return enc_c(getattr(complex, f"__r{name}__")(w, v))
        return common.py_result(call)
    if fn == "c_parse":
        s = "".join(map(chr, c["cps"]))
        return common.py_result(lambda: enc_c(complex(s)))
    z = py_c(c["v"])
    if fn == "c_neg":
        return {"ok": enc_c(-z)}
    if fn == "c_conj":
        return {"ok": enc_c(z.conjugate())}
    if fn == "c_bool":
        return {"ok": bool(z)}
    if fn == "c_repr":
        return {"ok": repr(z)}
    if fn == "c_abs":
        return common.py_result(lambda: enc(abs(z)))
    if fn == "c_eq":
        r = getattr(complex, f"__{c['op']}__")(z, py_c(c["w"]))
        return {"ok": "NotImplemented" if r is NotImplemented else r}
    raise ValueError(fn)


LOW_LEVEL = set(UNARY + BINARY + ["fma", "ldexp", "ofInt", "ratio"])


def gen_all(rng):
    k = rng.random()
    if k < 0.25:
        return gen_case(rng)
    return gen_float_case(rng) if k < 0.85 else gen_complex_case(rng)


def run_all(c):
    if c["fn"].startswith("c_"):
        return run_complex(c)
    return run_python(c) if c["fn"] in LOW_LEVEL else run_float(c)


common.main(gen_all, run_all, default_cases=50000)
