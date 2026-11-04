"""Differential test: Lean model of decimal vs. the running CPython's two twins.

Usage: python3 difftest/decimal_diff.py [--cases N] [--seed S]

Exits non-zero on any mismatch. See difftest/common.py.

`fn` names ending in `_py` run against `_pydecimal`, `_c` against `_decimal`;
`op` cases carry `"impl": "py" | "c"`. A decimal travels as
["F", neg, "<coeff digits>", exp] | ["I", neg] | ["N", neg, signaling, "<payload>"]
and is rebuilt on the Python side from a tuple (which neither twin limits).
Ints travel as hex(i). Strings and format specs travel as code point lists.
"""

import fractions
import math
import random
import struct
import sys
import warnings

import _decimal as C
import _pydecimal as P

import common

warnings.simplefilter("ignore")

MODS = {"py": P, "c": C}
ROUNDINGS = ["ROUND_UP", "ROUND_DOWN", "ROUND_CEILING", "ROUND_FLOOR", "ROUND_HALF_UP",
             "ROUND_HALF_DOWN", "ROUND_HALF_EVEN", "ROUND_05UP"]
SIGNALS = ["Clamped", "InvalidOperation", "DivisionByZero", "Inexact", "Rounded",
           "Subnormal", "Overflow", "Underflow"]
ND_ZEROS = [0x30, 0x660, 0x6f0, 0x966, 0xff10, 0x1d7ce, 0x104a0, 0x1e950, 0x11de0]  # 0x11de0: Unicode 17
SPACES = [0x20, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x1c, 0x1f, 0x85, 0xa0, 0x1680, 0x2000,
          0x200a, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000]
FOLDS = {"i": ["I", "İ", "ı"], "s": ["S", "ſ"]}


# ---------------------------------------------------------------- encodings

def enc_dec(d):
    t = d.as_tuple()
    digits = "".join(map(str, t.digits))
    if t.exponent == "F":
        return ["I", t.sign == 1]
    if t.exponent in ("n", "N"):
        return ["N", t.sign == 1, t.exponent == "N", digits.lstrip("0") or "0"]
    return ["F", t.sign == 1, digits or "0", t.exponent]


def build(M, j):
    if j[0] == "I":
        return M.Decimal((int(j[1]), (0,), "F"))
    if j[0] == "N":
        p = j[3] if j[3] != "0" else ""
        return M.Decimal((int(j[1]), tuple(map(int, p)), "N" if j[2] else "n"))
    return M.Decimal((int(j[1]), tuple(map(int, j[2])), j[3]))


def hexint(i):
    return ("-" if i < 0 else "") + "0x" + format(abs(i), "x")


def cps(s):
    return [ord(c) for c in s]


def pyval(v):
    if v is None:
        return None
    if isinstance(v, bool):
        return {"b": v}
    if isinstance(v, int):
        return {"i": v}
    return {"s": v}


def unpyval(j):
    if j is None:
        return None
    if "b" in j:
        return j["b"]
    if "i" in j:
        return j["i"]
    return j["s"]


# ---------------------------------------------------------------- generators

def gen_coeff(rng, huge=False):
    k = rng.random()
    if huge and k < 0.05:
        n = rng.choice([4299, 4300, 4301, 4302, 5000, 2200])
        return str(rng.randrange(1, 10)) + "".join(rng.choice("0123456789") for _ in range(n - 1))
    if k < 0.15:
        return rng.choice(["0", "1", "5", "9", "10", "15", "25", "50", "95", "99", "100", "105", "999",
                           "1000", "9999999999999999999999999999", "5000000000000000000000000000",
                           "4999999999999999999999999999", "10000000000000000000000000000"])
    nd = rng.choice([1, 1, 2, 3, 4, 5, 9, 18, 19, 20, 27, 28, 29, 30, 40, 60])
    if rng.random() < 0.3:
        body = rng.choice(["9", "5", "0", "4"]) * nd
        return str(int(rng.choice(["1", "2", "5", "9"]) + body))
    return str(rng.randrange(0, 10 ** nd))


def gen_exp(rng, wide=False):
    choices = [0, 0, 0, -1, -2, 1, 2, -3, 3, -5, 5, -6, -7, -10, 10, -28, -30, 28, rng.randint(-40, 40),
               rng.randint(-12, 12)]
    if wide:
        choices += [rng.randint(-1100, 1100), 999, -999, 1000, -1010, -1020, 999999, -999999,
                    -1000026, 10 ** 18 - 1, -(10 ** 18) + 1, 2 * 10 ** 18, -2 * 10 ** 18]
    return rng.choice(choices)


def gen_dec(rng, huge=False, wide=False, special=0.08):
    if rng.random() < special:
        k = rng.randrange(4)
        neg = rng.random() < 0.5
        if k == 0:
            return ["I", neg]
        p = rng.choice(["0", "0", "1", "12", "123456789", "9" * 30])
        return ["N", neg, k == 1, p]
    return ["F", rng.random() < 0.4, gen_coeff(rng, huge), gen_exp(rng, wide)]


def rand_digit_char(rng, ascii_only=False):
    d = rng.randrange(10)
    if ascii_only or rng.random() < 0.8:
        return chr(0x30 + d)
    return chr(rng.choice(ND_ZEROS) + d)


def rand_word(rng, w):
    out = []
    for ch in w:
        r = rng.random()
        if ch in FOLDS and r < 0.08:
            out.append(rng.choice(FOLDS[ch]))
        elif r < 0.5:
            out.append(ch.upper())
        else:
            out.append(ch)
    return "".join(out)


def gen_numeric_string(rng):
    parts = []
    if rng.random() < 0.3:
        parts.append(rng.choice("+-"))
    k = rng.random()
    if k < 0.12:
        parts.append(rand_word(rng, rng.choice(["inf", "infinity", "infinit", "infinityy", "in"])))
    elif k < 0.24:
        if rng.random() < 0.5:
            parts.append(rand_word(rng, "s"))
        parts.append(rand_word(rng, rng.choice(["nan", "nan", "na"])))
        parts.append("".join(rand_digit_char(rng) for _ in range(rng.choice([0, 0, 1, 2, 5, 30]))))
    else:
        n_int = rng.choice([0, 1, 1, 2, 3, 5, 10, 28, 30])
        if rng.random() < 0.01:
            n_int = rng.choice([4299, 4300, 4301])
        lead0 = rng.choice([0, 0, 0, 1, 2])
        parts.append("0" * lead0 + "".join(rand_digit_char(rng) for _ in range(n_int)))
        if rng.random() < 0.4:
            parts.append(".")
            parts.append("".join(rand_digit_char(rng) for _ in range(rng.choice([0, 1, 2, 3, 7, 30]))))
        if rng.random() < 0.4:
            parts.append(rng.choice("eE"))
            if rng.random() < 0.5:
                parts.append(rng.choice("+-"))
            nd = rng.choice([0, 1, 1, 2, 3, 18, 19, 20])
            if rng.random() < 0.005:
                nd = 4301
            parts.append("".join(rand_digit_char(rng) for _ in range(nd)))
    s = "".join(parts)
    # underscores, junk, whitespace
    if rng.random() < 0.2 and s:
        i = rng.randrange(len(s) + 1)
        s = s[:i] + "_" * rng.choice([1, 1, 2]) + s[i:]
    if rng.random() < 0.05 and s:
        i = rng.randrange(len(s) + 1)
        s = s[:i] + rng.choice(["x", "\x00", ".", "e", "+", "é", " ", " ", "ı", "ſ"]) + s[i:]
    if rng.random() < 0.2:
        s = "".join(chr(rng.choice(SPACES)) for _ in range(rng.randrange(1, 3))) + s
    if rng.random() < 0.2:
        s = s + "".join(chr(rng.choice(SPACES)) for _ in range(rng.randrange(1, 3)))
    return s


def gen_tuple_item_digit(rng):
    k = rng.random()
    if k < 0.85:
        return {"i": rng.randrange(10)}
    if k < 0.9:
        return {"b": rng.random() < 0.5}
    return rng.choice([{"i": 10}, {"i": -1}, {"i": 2 ** 64}, {"s": "1"}, None])


def gen_tuple(rng):
    sign = rng.choice([{"i": 0}, {"i": 1}, {"i": 0}, {"i": 1}, {"b": True}, {"b": False}, {"i": 2},
                       {"i": -1}, {"i": 2 ** 64}, {"s": "0"}, None])
    if rng.random() < 0.05:
        digits = None
    else:
        digits = [gen_tuple_item_digit(rng) if rng.random() < 0.3 else {"i": rng.randrange(10)}
                  for _ in range(rng.choice([0, 1, 1, 2, 3, 5, 20, 30]))]
        if rng.random() < 0.3 and digits:
            digits[0] = {"i": 0}
    exp = rng.choice([{"i": gen_exp(rng, True)}, {"i": gen_exp(rng)}, {"i": gen_exp(rng)},
                      {"s": "F"}, {"s": "n"}, {"s": "N"}, {"s": "x"}, {"b": True}, None,
                      {"i": 2 ** 63}, {"i": -(2 ** 63) - 1}])
    return sign, digits, exp


def gen_spec(rng):
    s = ""
    if rng.random() < 0.3:
        if rng.random() < 0.5:
            s += rng.choice(["x", "*", "0", " ", "é", "{", "\x00", "<", "\n", "1", "_", ",",
                             ".", "\ud800", "\U0001F600", "z"])
        s += rng.choice("<>=^")
    if rng.random() < 0.3:
        s += rng.choice("+- ")
    if rng.random() < 0.15:
        s += "z"
    if rng.random() < 0.15:
        s += "#"
    if rng.random() < 0.2:
        s += "0"
    if rng.random() < 0.4:
        s += rng.choice(["0", "1", "5", "10", "20", "007", "١٠"])
    if rng.random() < 0.3:
        s += rng.choice(",_")
    if rng.random() < 0.4:
        s += "."
        if rng.random() < 0.85:
            s += rng.choice(["0", "1", "2", "5", "28", "٢"])
        if rng.random() < 0.2:
            s += rng.choice(",_")
    if rng.random() < 0.8:
        s += rng.choice("eEfFgG%nN") if rng.random() < 0.95 else rng.choice("dxbs")
    if rng.random() < 0.08:
        i = rng.randrange(len(s) + 1)
        s = s[:i] + rng.choice(["\x00", "\x00junk", "\ud800", "\udfff"]) + s[i:]
    if rng.random() < 0.01:
        s = rng.choice(["00", "0>", "00>5", ".", ",_", "_,", ",,", ".,_", "0,", "+0", "z0", "#0",
                        "\x00", "\x00\x00", "\x00<5", "5\x00", "\x00>10\x00x", "1" * 4301, ".1" + "0" * 4300])
    return s


def gen_ctx(rng):
    return {"prec": rng.choice([1, 2, 3, 5, 9, 16, 28, 30]),
            "rounding": rng.choice(ROUNDINGS),
            "emin": rng.choice([-999999, -999, -30, -5, -1, 0]),
            "emax": rng.choice([999999, 999, 30, 5, 1, 0]),
            "clamp": rng.choice([0, 1]),
            "traps": [t for t in SIGNALS if rng.random() < 0.15]}


# Methods checked generically, name -> how the Python side calls them.
METHODS = {
    "neg": lambda M, a, b, t: -a, "pos": lambda M, a, b, t: +a, "abs": lambda M, a, b, t: abs(a),
    "copy_abs": lambda M, a, b, t: a.copy_abs(), "copy_negate": lambda M, a, b, t: a.copy_negate(),
    "bool": lambda M, a, b, t: bool(a), "adjusted": lambda M, a, b, t: a.adjusted(),
    "is_nan": lambda M, a, b, t: a.is_nan(), "is_qnan": lambda M, a, b, t: a.is_qnan(),
    "is_snan": lambda M, a, b, t: a.is_snan(), "is_infinite": lambda M, a, b, t: a.is_infinite(),
    "is_finite": lambda M, a, b, t: a.is_finite(), "is_signed": lambda M, a, b, t: a.is_signed(),
    "is_zero": lambda M, a, b, t: a.is_zero(), "is_canonical": lambda M, a, b, t: a.is_canonical(),
    "is_normal": lambda M, a, b, t: a.is_normal(), "is_subnormal": lambda M, a, b, t: a.is_subnormal(),
    "number_class": lambda M, a, b, t: a.number_class(), "same_quantum": lambda M, a, b, t: a.same_quantum(b),
    "radix": lambda M, a, b, t: a.radix(), "canonical": lambda M, a, b, t: a.canonical(),
    "conjugate": lambda M, a, b, t: a.conjugate(), "real": lambda M, a, b, t: a.real,
    "imag": lambda M, a, b, t: a.imag,
    "eq": lambda M, a, b, t: a == b, "lt": lambda M, a, b, t: a < b, "le": lambda M, a, b, t: a <= b,
    "gt": lambda M, a, b, t: a > b, "ge": lambda M, a, b, t: a >= b,
    "compare": lambda M, a, b, t: a.compare(b), "compare_signal": lambda M, a, b, t: a.compare_signal(b),
    "compare_total_mag": lambda M, a, b, t: int(a.compare_total_mag(b)),
    "max": lambda M, a, b, t: a.max(b), "min": lambda M, a, b, t: a.min(b),
    "max_mag": lambda M, a, b, t: a.max_mag(b), "min_mag": lambda M, a, b, t: a.min_mag(b),
    "logb": lambda M, a, b, t: a.logb(), "logical_and": lambda M, a, b, t: a.logical_and(b),
    "logical_or": lambda M, a, b, t: a.logical_or(b), "logical_xor": lambda M, a, b, t: a.logical_xor(b),
    "logical_invert": lambda M, a, b, t: a.logical_invert(), "rotate": lambda M, a, b, t: a.rotate(b),
    "shift": lambda M, a, b, t: a.shift(b), "scaleb": lambda M, a, b, t: a.scaleb(b),
    "next_minus": lambda M, a, b, t: a.next_minus(), "next_plus": lambda M, a, b, t: a.next_plus(),
    "next_toward": lambda M, a, b, t: a.next_toward(b), "fma": lambda M, a, b, t: a.fma(b, t),
    "to_eng_string": lambda M, a, b, t: cps(a.to_eng_string()), "repr": lambda M, a, b, t: cps(repr(a)),
    "truediv": lambda M, a, b, t: a / b, "floordiv": lambda M, a, b, t: a // b,
    "mod": lambda M, a, b, t: a % b, "divmod": lambda M, a, b, t: divmod(a, b),
    "remainder_near": lambda M, a, b, t: a.remainder_near(b),
}
LOGICAL = {"logical_and", "logical_or", "logical_xor", "logical_invert"}
SMALL_INT = {"rotate", "shift", "scaleb"}


def gen_method(rng):
    name = rng.choice(list(METHODS))
    impl = rng.choice(["py", "c"])
    a, b, t = gen_dec(rng, wide=True), gen_dec(rng, wide=True), gen_dec(rng, wide=True, special=0.15)
    ctx = gen_ctx(rng)
    if rng.random() < 0.25:
        b = a if rng.random() < 0.5 else (["F", not a[1], a[2], a[3]] if a[0] == "F" else b)
    if name in LOGICAL and rng.random() < 0.9:
        n = rng.choice([1, 2, 3, 5, 9, 30])
        a = ["F", False, str(int("".join(rng.choice("01") for _ in range(n)))), 0]
        b = ["F", False, str(int("".join(rng.choice("01") for _ in range(n)))), 0]
    if name in SMALL_INT and rng.random() < 0.9:
        n = rng.randint(-35, 35)
        b = ["F", n < 0, str(abs(n)), 0]
    return {"mod": "decimal", "fn": "m", "m": name, "impl": impl, "ctx": ctx, "a": a, "b": b, "t": t}


# Context methods: name -> number of operands.
CMETHODS = dict.fromkeys(
    ["add", "subtract", "multiply", "divide", "divide_int", "divmod", "remainder", "compare",
     "compare_signal", "max", "max_mag", "min", "min_mag", "next_toward", "quantize", "remainder_near",
     "rotate", "scaleb", "shift", "compare_total", "compare_total_mag", "copy_sign", "same_quantum",
     "logical_and", "logical_or", "logical_xor"], 2)
CMETHODS.update(dict.fromkeys(
    ["abs", "logb", "logical_invert", "minus", "plus", "next_minus", "next_plus", "normalize",
     "to_integral_exact", "to_integral_value", "number_class", "is_normal", "is_subnormal",
     "to_eng_string", "to_sci_string", "copy_abs", "copy_negate", "copy_decimal", "is_finite",
     "is_infinite", "is_nan", "is_qnan", "is_signed", "is_snan", "is_zero", "canonical",
     "is_canonical"], 1))
CMETHODS["fma"] = 3
CMETHODS["radix"] = 0
ROPS = ["__rsub__", "__rtruediv__", "__rmod__", "__rfloordiv__", "__rdivmod__"]
ALL_SIGNALS = SIGNALS + ["FloatOperation"]
TMPL_DEFAULT = {"prec": "28", "rounding": "ROUND_HALF_EVEN", "Emin": "-999999", "Emax": "999999",
                "capitals": "1", "clamp": "0", "flags": [],
                "traps": ["DivisionByZero", "InvalidOperation", "Overflow"]}
ACTS = ["div00", "conv", "impossible", "invalid", "inexact", "divzero"]
INT_EDGES = [0, 1, -1, 2, 9, 10, 28, 999999, -999999, 2 ** 31 - 1, 2 ** 31, -2 ** 31, -2 ** 31 - 1,
             2 ** 63 - 1, 2 ** 63, -2 ** 63, -2 ** 63 - 1, 2 ** 64, 999999999999999999,
             1000000000000000000, -999999999999999999, -1000000000000000000]


def gen_arg(rng, wide=True):
    k = rng.random()
    if k < 0.70:
        return ["dec", gen_dec(rng, wide=wide)]
    if k < 0.92:
        return ["int", str(rng.choice([0, 1, -1, 2, 7, 10, -10, 123, 10 ** 20, -10 ** 20]))]
    return ["other"]


def gen_cm(rng):
    name = rng.choice(list(CMETHODS))
    a, b, t = gen_arg(rng), gen_arg(rng), gen_arg(rng)
    if name in ("rotate", "shift", "scaleb") and rng.random() < 0.8:
        b = ["int", str(rng.randint(-35, 35))]
    if name.startswith("logical") and rng.random() < 0.9:
        n = rng.choice([1, 2, 3, 5, 9])
        a = ["int", str(int("".join(rng.choice("01") for _ in range(n))))]
        b = ["int", str(int("".join(rng.choice("01") for _ in range(n))))]
    impl = rng.choice(["py", "c"])
    if impl == "py" and rng.random() < 0.05:
        # "Unable to convert %s to Decimal" % () formats the tuple's items (_pydecimal only)
        tup = ["tuple", str(rng.choice([0, 1, 2, 3]))]
        k = rng.choice(["a", "b", "t"])
        a, b, t = (tup if k == "a" else a), (tup if k == "b" else b), (tup if k == "t" else t)
    return {"mod": "decimal", "fn": "cm", "m": name, "impl": impl, "ctx": gen_ctx(rng),
            "a": a, "b": b, "t": t}


def gen_div_band(rng):
    """Both sides of 10**prec, for _is_less_than_pow10a_use_str: at small precisions, and past
    the 4300-digit limit, where its str(q) raises in the band it cannot decide."""
    ctx = gen_ctx(rng)
    ctx.update(emin=-999999, emax=999999)
    if rng.random() < 0.4:
        ctx["prec"] = rng.choice([4299, 4300, 4301, 4302, 5000, 6000, 9000])
        coeff = rng.choice(["1", "2", "5", "9", "99", "101", "999"])
        a = ["F", False, coeff, ctx["prec"] + rng.randrange(-3, 3) - len(coeff) + 1]
    else:
        a = ["F", False, str(max(10 ** ctx["prec"] + rng.randrange(-3, 4), 1)), 0]
    b = ["F", False, "1", 0]
    impl = rng.choice(["py", "c"])
    # The model has no C remainder of its own: past the limit it would apply _pydecimal's.
    names = (["divide_int", "divmod", "remainder", "remainder_near"] if impl == "py" or ctx["prec"] < 4000
             else ["divide_int", "divmod"])
    return {"mod": "decimal", "fn": "cm", "m": rng.choice(names), "impl": impl, "ctx": ctx,
            "a": ["dec", a], "b": ["dec", b], "t": ["dec", b]}


def gen_rop(rng):
    return {"mod": "decimal", "fn": "rop", "m": rng.choice(ROPS), "impl": rng.choice(["py", "c"]),
            "ctx": gen_ctx(rng), "a": gen_dec(rng, wide=True), "b": gen_arg(rng)}


def gen_tmpl(rng):
    t = dict(TMPL_DEFAULT)
    if rng.random() < 0.5:
        t["prec"] = str(rng.choice([1, 9, 28, 100]))
        t["rounding"] = rng.choice(ROUNDINGS)
        t["Emin"] = str(rng.choice([-999999, -30, 0]))
        t["Emax"] = str(rng.choice([999999, 30, 0]))
        t["clamp"] = rng.choice(["0", "1"])
        t["traps"] = [x for x in ALL_SIGNALS if rng.random() < 0.3]
    if rng.random() < 0.4:
        t["capitals"] = rng.choice(["0", "1"])
    if rng.random() < 0.4:
        t["flags"] = [x for x in ALL_SIGNALS if rng.random() < 0.3]
    return t


def gen_int_arg(rng):
    return ["int", str(rng.choice(INT_EDGES))]


def gen_sig_list(rng):
    names = [x for x in ALL_SIGNALS if rng.random() < 0.3]
    if rng.random() < 0.08:
        names.append("other")
    return ["list", names]


def gen_sig_dict(rng):
    keys = list(ALL_SIGNALS)
    r = rng.random()
    if r < 0.1:
        keys.remove(rng.choice(keys))
    elif r < 0.2:
        keys.append("other")
    return ["dict", [[k, rng.random() < 0.3] for k in keys]]


def frozen(v, impl):
    """A signal dict as a frozendict: dict_as_flags takes one since 3.15, `_pydecimal` does not."""
    return ["frozendict" if impl == "c" else "frozendict_py", v[1]]


def gen_attr(rng, name):
    r = rng.random()
    if name in ("prec", "Emin", "Emax", "capitals", "clamp"):
        if r < 0.85:
            return gen_int_arg(rng)
        return rng.choice([["str", "1"], ["obj"]])
    if name == "rounding":
        if r < 0.8:
            return ["str", rng.choice(ROUNDINGS)]
        return rng.choice([["str", "ROUND_NOPE"], ["int", "1"], ["obj"]])
    if name == "_ignored_flags":
        return gen_sig_list(rng)
    if r < 0.6:
        return gen_sig_dict(rng)
    if r < 0.85:
        return gen_sig_list(rng)
    return ["tuple", str(rng.choice([0, 1, 2, 3]))] if r < 0.93 else ["obj"]


def gen_ctxobj(rng):
    impl = rng.choice(["py", "c"])
    k = rng.random()
    if k < 0.3:
        init = {}
        for n in ["prec", "rounding", "Emin", "Emax", "capitals", "clamp", "flags", "traps"]:
            if rng.random() < 0.3:
                init[n] = gen_attr(rng, n)
        for n, v in list(init.items()):
            if n in ("flags", "traps") and v[0] == "dict" and rng.random() < 0.3:
                init[n] = frozen(v, impl)
        return {"mod": "decimal", "fn": "ctxnew", "impl": impl, "tmpl": gen_tmpl(rng), "init": init}
    if k < 0.5:
        name = rng.choice(["prec", "rounding", "Emin", "Emax", "capitals", "clamp", "flags", "traps", "nope",
                           "_ignored_flags"])
        val = gen_attr(rng, name) if name != "nope" else ["int", "1"]
        if name in ("flags", "traps") and val[0] == "list":
            val = gen_sig_dict(rng)
        if val[0] == "dict" and rng.random() < 0.3:
            val = frozen(val, impl)
        return {"mod": "decimal", "fn": "ctxset", "impl": impl, "tmpl": gen_tmpl(rng), "name": name, "val": val}
    if k < 0.55:
        return {"mod": "decimal", "fn": "ctxdel", "impl": impl,
                "name": rng.choice(["prec", "flags", "traps", "nope"])}
    acts = [rng.choice(ACTS) for _ in range(rng.choice([0, 1, 1, 2, 3]))]
    if k < 0.7:
        return {"mod": "decimal", "fn": "ctxrepr", "impl": impl, "acts": acts}
    if k < 0.85:
        return {"mod": "decimal", "fn": "sd", "impl": "c", "acts": acts,
                "acts2": [rng.choice(ACTS) for _ in range(rng.choice([0, 1, 2]))],
                "op": rng.choice(["len", "iter", "get", "set", "clear", "del", "repr", "copy", "eq", "ne"]),
                "key": rng.choice(ALL_SIGNALS + ["other"]), "bound": rng.random() < 0.9,
                "w": rng.choice(["copy", "copy_frozen", "self", "unbound", "other_ctx", "bad_dict",
                                 "bad_frozen", "none"])}
    if k < 0.92:
        bits = rng.choice([0, 32, 64, 128, 160, 256, 512, 544, 33, -32, 1024, 2 ** 31, 2 ** 63])
        arg = ["int", str(bits)]
        if impl == "c":
            # The clinic Py_ssize_t converter of 3.15: __index__ and its refusals.
            arg = rng.choice([arg, arg, ["idx", str(bits)], ["str", "x"], ["obj"]])
        return {"mod": "decimal", "fn": "ieee", "impl": impl, "tmpl": gen_tmpl(rng), "bits": arg}
    kw = []
    for n in rng.sample(["prec", "rounding", "Emin", "Emax", "capitals", "clamp", "flags", "traps", "nope"],
                        rng.choice([0, 1, 1, 2, 3])):
        val = ["null"] if rng.random() < 0.1 else (gen_attr(rng, n) if n != "nope" else ["int", "1"])
        if n in ("flags", "traps") and val[0] == "list":
            val = gen_sig_dict(rng)
        kw.append([n, None if val == ["null"] else val])
    return {"mod": "decimal", "fn": "local", "impl": impl, "tmpl": gen_tmpl(rng), "kw": kw}


OPS = ["add", "sub", "mul", "quantize", "quantize", "tiv", "tie", "roundn", "normalize", "fix"]


MAX_PREC = MAX_EMAX = 999999999999999999
MIN_ETINY = -999999999999999999 - (MAX_PREC - 1)


def in_c_limits(j):
    """The value is representable by _decimal (InCLimits in Basic.lean)."""
    if j[0] == "F":
        n = len(j[2].lstrip("0") or "0")
        return n <= MAX_PREC and j[3] + n - 1 <= MAX_EMAX and j[3] >= MIN_ETINY
    return True



# ---------------------------------------------------------------- conversions and comparisons

FLOAT_EDGES = [0.0, -0.0, 1.0, -1.0, 0.1, 0.5, 1.5, 2.5, -2.5, 1e-300, 5e-324, -5e-324, 1.7976931348623157e308,
               2.0 ** 53, 2.0 ** 63, -2.0 ** 64, 1e22, 1e23, 123.456, float("inf"), float("-inf"),
               float("nan"), -float("nan")]


def fbits(x):
    return str(struct.unpack("<Q", struct.pack("<d", x))[0])


def ffrom(b):
    return struct.unpack("<d", struct.pack("<Q", int(b)))[0]


def gen_float(rng):
    r = rng.random()
    if r < 0.5:
        return fbits(rng.choice(FLOAT_EDGES))
    if r < 0.8:
        return fbits(rng.choice([1, -1]) * rng.random() * 10.0 ** rng.randint(-30, 30))
    return str(rng.getrandbits(64))


def gen_cmparg(rng, a):
    r = rng.random()
    if r < 0.2:
        return ["dec", gen_dec(rng, wide=True)]
    if r < 0.45:
        n = rng.choice([0, 1, -1, 2, 5, 10, -7, 123, 10 ** 20, -10 ** 20, rng.randint(-10 ** 6, 10 ** 6)])
        if a[0] == "F" and len(a[2]) < 40 and -1 < a[3] < 30 and rng.random() < 0.3:
            n = (-1 if a[1] else 1) * int(a[2]) * 10 ** max(a[3], 0)
        return ["rat", str(n), "1"]
    if r < 0.65:
        d = rng.choice([2, 3, 4, 7, 10, 1000, 3 ** 20])
        n = rng.randint(-10 ** 6, 10 ** 6)
        g = math.gcd(n, d)
        return ["rat", str(n // g), str(d // g)]
    if r < 0.85:
        return ["float", gen_float(rng)]
    if r < 0.95:
        im = fbits(rng.choice([0.0, -0.0, 1.0, float("nan")]))
        return ["complex", gen_float(rng), im]
    return ["other"]


def gen_rich(rng):
    a = gen_dec(rng, wide=True, special=0.15)
    ctx = gen_ctx(rng)
    if rng.random() < 0.3:
        ctx["traps"] = ctx["traps"] + ["FloatOperation"]
    return {"mod": "decimal", "fn": "rich", "op": rng.choice(["eq", "lt", "le", "gt", "ge"]),
            "ctx": ctx, "a": a, "b": gen_cmparg(rng, a)}


def gen_new(rng):
    ctx = gen_ctx(rng)
    if rng.random() < 0.3:
        ctx["traps"] = ctx["traps"] + ["FloatOperation"]
    if rng.random() < 0.3:
        ctx["traps"] = [t for t in ctx["traps"] if t != "InvalidOperation"]
    k = rng.choice(["str", "str", "int", "float", "float", "other"])
    c = {"mod": "decimal", "fn": "new_py", "ctx": ctx, "k": k}
    if k == "str":
        c["s"] = cps(gen_numeric_string(rng) if rng.random() < 0.7 else rng.choice(["xyz", "", "1e", "--1", "nan1x", " 1 2"]))
    elif k == "int":
        c["n"] = str(rng.choice([0, 1, -1, 10 ** 30, -12345, rng.randint(-10 ** 9, 10 ** 9)]))
    elif k == "float":
        c["bits"] = gen_float(rng)
    return c


LOG2_10 = math.log2(10)


def gen_pow10(rng):
    r = rng.random()
    if r < 0.05:
        a = rng.choice([2 ** 1024, 2 ** 1024 - 2 ** 970 - 1, 2 ** 1024 - 2 ** 970, 2 ** 1100])
        return {"mod": "decimal", "fn": "pow10", "q": str(rng.choice([0, 1, 10 ** 30])), "a": str(a)}
    a = rng.choice([1, 2, 3, rng.randint(1, 60), rng.randint(1, 3000)])
    if r < 0.5:
        q = 10 ** a + rng.randint(-3, 3)
    elif r < 0.8:
        bl = int(a * LOG2_10) + rng.randint(-2, 2)
        q = (1 << max(bl, 0)) + rng.randint(0, 3)
    else:
        q = rng.getrandbits(rng.randint(0, int(a * 3.4) + 4))
    return {"mod": "decimal", "fn": "pow10", "q": str(max(q, 0)), "a": str(a)}


def build_cmparg(j):
    if j[0] == "dec":
        return build(P, j[1])
    if j[0] == "rat":
        n, d = int(j[1]), int(j[2])
        return n if d == 1 else fractions.Fraction(n, d)
    if j[0] == "float":
        return ffrom(j[1])
    if j[0] == "complex":
        return complex(ffrom(j[1]), ffrom(j[2]))
    return "x"


def run_rich(case):
    ctx = make_ctx(P, case["ctx"])
    a = build(P, case["a"])
    b = build_cmparg(case["b"])
    with P.localcontext(ctx) as cx:
        r = getattr(a, "__%s__" % case["op"])(b)
        flags = sorted(s for s in ALL_SIGNALS if cx.flags[getattr(P, s)])
    return [None if r is NotImplemented else r, flags]


def run_new(case):
    ctx = make_ctx(P, case["ctx"])
    k = case["k"]
    v = {"str": lambda: "".join(map(chr, case["s"])), "int": lambda: int(case["n"]),
         "float": lambda: ffrom(case["bits"]), "other": lambda: object()}[k]()
    d = P.Decimal(v, context=ctx)
    try:
        s = cps(str(d))
    except ValueError:
        s = None
    return [s, sorted(s2 for s2 in ALL_SIGNALS if ctx.flags[getattr(P, s2)])]


def gen_case(rng):
    while True:
        c = gen_case1(rng)
        if c["fn"].endswith("_c") or c.get("impl") == "c":
            vals = [c[k] for k in ("a", "b", "t") if k in c]
            vals = [v[1] if v and v[0] == "dec" else v for v in vals]
            if not all(in_c_limits(v) for v in vals if v and v[0] in ("F", "I", "N")):
                continue
        return c


def gen_case1(rng):
    if rng.random() < 0.04:
        return gen_div_band(rng)
    r0 = rng.random()
    if r0 < 0.05:
        return gen_rich(rng)
    if r0 < 0.07:
        return {"mod": "decimal", "fn": "fromfloat", "bits": gen_float(rng)}
    if r0 < 0.09:
        return gen_new(rng)
    if r0 < 0.11:
        return gen_pow10(rng)
    if rng.random() < 0.01:
        # The clinic `unicode` converter of Decimal.__format__, new in 3.15.
        return {"mod": "decimal", "fn": "fmtarg_c", "arg": rng.choice(["int", "NoneType", "float", "bytes"])}
    r = rng.random()
    if r < 0.25:
        return gen_method(rng)
    if r < 0.40:
        return gen_cm(rng)
    if r < 0.45:
        return gen_rop(rng)
    if r < 0.55:
        return gen_ctxobj(rng)
    k = rng.random()
    if k < 0.18:
        return {"mod": "decimal", "fn": rng.choice(["parse_py", "parse_c"]),
                "s": cps(gen_numeric_string(rng))}
    if k < 0.21:
        return {"mod": "decimal", "fn": rng.choice(["strrt_py", "strrt_c"]),
                "a": gen_dec(rng, huge=True, wide=True, special=0.15)}
    if k < 0.24:
        return {"mod": "decimal", "fn": rng.choice(["str_py", "str_c"]),
                "a": gen_dec(rng, huge=True, wide=True, special=0.15)}
    if k < 0.30:
        s, d, e = gen_tuple(rng)
        return {"mod": "decimal", "fn": rng.choice(["tuple_py", "tuple_c"]), "sign": s, "digits": d, "exp": e}
    if k < 0.33:
        return {"mod": "decimal", "fn": "as_tuple", "impl": rng.choice(["py", "c"]),
                "a": gen_dec(rng, wide=True, special=0.3)}
    if k < 0.37:
        return {"mod": "decimal", "fn": rng.choice(["hash_py", "hash_c"]),
                "a": gen_dec(rng, huge=True, wide=rng.random() < 0.3, special=0.1)}
    if k < 0.43:
        return {"mod": "decimal", "fn": rng.choice(["int_py", "int_c"]),
                "mode": rng.choice(["int", "floor", "ceil", "round"]),
                "a": gen_dec(rng, huge=True, special=0.05)}
    if k < 0.46:
        return {"mod": "decimal", "fn": rng.choice(["ratio_py", "ratio_c"]),
                "a": gen_dec(rng, huge=True, special=0.05)}
    if k < 0.48:
        n = gen_coeff(rng)
        n = int(n) if rng.random() < 0.9 else rng.randrange(10 ** rng.choice([4298, 4299, 4300, 4301]), 10 ** 4302)
        return {"mod": "decimal", "fn": rng.choice(["fromint_py", "fromint_c"]), "n": hex(n)[2:],
                "neg": rng.random() < 0.5}
    if k < 0.58:
        return {"mod": "decimal", "fn": rng.choice(["fmt_py", "fmt_c"]), "spec": cps(gen_spec(rng)),
                "libmpdec": C.__libmpdec_version__.split(".")[0]}
    if k < 0.62:
        return {"mod": "decimal", "fn": rng.choice(["compare_total", "copy_sign"]),
                "impl": rng.choice(["py", "c"]),
                "a": gen_dec(rng, special=0.3), "b": gen_dec(rng, special=0.3)}
    if k < 0.66:
        # quantSpec, the specification the quantize property uses, against _decimal itself.
        return {"mod": "decimal", "fn": "quantspec", "rounding": rng.choice(ROUNDINGS),
                "neg": rng.random() < 0.5, "c": gen_coeff(rng), "e": gen_exp(rng), "qe": gen_exp(rng)}
    if k < 0.68:
        # roundPrec, the specification the multiplication property uses, against _decimal itself.
        return {"mod": "decimal", "fn": "mulspec", "rounding": rng.choice(ROUNDINGS),
                "neg": rng.random() < 0.5, "prec": rng.choice([1, 2, 3, 5, 9, 16, 28]),
                "c1": str(int(gen_coeff(rng)) + 1), "c2": str(int(gen_coeff(rng)) + 1),
                "e1": gen_exp(rng), "e2": gen_exp(rng)}
    impl = rng.choice(["py", "c"])
    op = rng.choice(OPS)
    case = {"mod": "decimal", "fn": "op", "impl": impl, "op": op, "ctx": gen_ctx(rng),
            "a": gen_dec(rng, wide=True), "b": gen_dec(rng, wide=True),
            "n": rng.choice([0, 1, -1, 2, -2, 5, -5, 30, -30, 1000, -1000, 10 ** 6, -10 ** 6])}
    if rng.random() < 0.5:
        case["rounding2"] = rng.choice(ROUNDINGS)
    if op == "quantize" and rng.random() < 0.7:
        case["b"] = ["F", False, "1", rng.randint(-12, 12)]
    if op == "fix" and case["a"][0] == "N":
        case["a"] = ["I", False]
    if impl == "py" and op in ("add", "mul") and rng.random() < 0.03:
        case["a"] = ["F", False, gen_coeff(rng, huge=True), 0]
        case["b"] = ["F", False, gen_coeff(rng, huge=True), 0]
    return case


# ---------------------------------------------------------------- python side

def run_op(M, case):
    c = case["ctx"]
    ctx = M.Context(prec=c["prec"], rounding=getattr(M, c["rounding"]), Emin=c["emin"],
                    Emax=c["emax"], clamp=c["clamp"], traps=[getattr(M, t) for t in c["traps"]],
                    flags=[])
    a, b = build(M, case["a"]), build(M, case["b"])
    r2 = getattr(M, case["rounding2"]) if "rounding2" in case else None
    with M.localcontext(ctx) as cx:
        op = case["op"]
        if op == "add":
            r = cx.add(a, b)
        elif op == "sub":
            r = cx.subtract(a, b)
        elif op == "mul":
            r = cx.multiply(a, b)
        elif op == "quantize":
            r = a.quantize(b, rounding=r2)
        elif op == "tiv":
            r = a.to_integral_value(rounding=r2)
        elif op == "tie":
            r = a.to_integral_exact(rounding=r2)
        elif op == "roundn":
            r = round(a, case["n"])
        elif op == "normalize":
            r = a.normalize()
        elif op == "fix":
            r = cx.create_decimal(a)
        flags = sorted(s for s in SIGNALS if cx.flags[getattr(M, s)])
    return [enc_dec(r), flags]


def enc_val(M, v):
    if isinstance(v, M.Decimal):
        return enc_dec(v)
    if isinstance(v, tuple):
        return [enc_val(M, x) for x in v]
    if v is NotImplemented:
        return None
    if isinstance(v, str) and getattr(enc_val, "str_cps", False):
        return cps(v)
    return v


def make_ctx(M, c):
    return M.Context(prec=c["prec"], rounding=getattr(M, c["rounding"]), Emin=c["emin"],
                     Emax=c["emax"], clamp=c["clamp"], traps=[getattr(M, t) for t in c["traps"]],
                     flags=[])


def build_arg(M, j):
    if j[0] == "dec":
        return build(M, j[1])
    if j[0] == "int":
        return int(j[1])
    if j[0] == "tuple":
        return tuple(range(int(j[1])))
    return "x"


def run_cm(M, case):
    ctx = make_ctx(M, case["ctx"])
    name = case["m"]
    args = [build_arg(M, case[k]) for k in ("a", "b", "t")][:CMETHODS[name]]
    r = getattr(ctx, name)(*args)
    flags = sorted(s for s in SIGNALS if ctx.flags[getattr(M, s)])
    if name in ("to_eng_string", "to_sci_string"):
        r = cps(r)
    return [enc_val(M, r), flags]


def run_rop(M, case):
    ctx = make_ctx(M, case["ctx"])
    a, b = build(M, case["a"]), build_arg(M, case["b"])
    with M.localcontext(ctx) as cx:
        r = getattr(a, case["m"])(b)
        flags = sorted(s for s in SIGNALS if cx.flags[getattr(M, s)])
    return [enc_val(M, r), flags]


def key_obj(M, k):
    return 5 if k == "other" else getattr(M, k)


def ctx_val(M, v):
    if v is None:
        return None
    t = v[0]
    if t == "int":
        return int(v[1])
    if t == "str":
        return v[1]
    if t == "list":
        return [key_obj(M, k) for k in v[1]]
    if t == "dict":
        return {key_obj(M, k): b for k, b in v[1]}
    if t in ("frozendict", "frozendict_py"):
        return frozendict({key_obj(M, k): b for k, b in v[1]})
    if t == "idx":
        return Idx(int(v[1]))
    if t == "tuple":
        return tuple(range(int(v[1])))
    return object()


class Idx:
    def __init__(self, v):
        self.v = v

    def __index__(self):
        return self.v


def enc_ctx(M, c):
    names = lambda d: sorted(k.__name__ for k in ALL_SIG_OBJ[M] if d[k])
    return {"prec": str(c.prec), "rounding": c.rounding, "Emin": str(c.Emin), "Emax": str(c.Emax),
            "capitals": str(c.capitals), "clamp": str(c.clamp), "flags": names(c.flags),
            "traps": names(c.traps)}


ALL_SIG_OBJ = {M: [getattr(M, s) for s in ALL_SIGNALS] for M in (P, C)}


def with_template(M, t, f):
    D = M.DefaultContext
    saved = (D.prec, D.rounding, D.Emin, D.Emax, D.capitals, D.clamp, dict(D.flags), dict(D.traps))
    try:
        D.prec, D.rounding = int(t["prec"]), t["rounding"]
        D.Emin, D.Emax = int(t["Emin"]), int(t["Emax"])
        D.capitals, D.clamp = int(t["capitals"]), int(t["clamp"])
        for s in ALL_SIG_OBJ[M]:
            D.flags[s] = s.__name__ in t["flags"]
            D.traps[s] = s.__name__ in t["traps"]
        return f()
    finally:
        D.prec, D.rounding, D.Emin, D.Emax, D.capitals, D.clamp = saved[:6]
        D.flags, D.traps = saved[6], saved[7]


def do_act(M, ctx, a):
    D = M.Decimal
    if a == "div00":
        ctx.divide(D(0), D(0))
    elif a == "conv":
        ctx.create_decimal("xyz")
    elif a == "impossible":
        ctx.divide_int(D("1E+30"), D(1))
    elif a == "invalid":
        ctx.sqrt(D(-1))
    elif a == "inexact":
        ctx.divide(D(1), D(3))
    elif a == "divzero":
        ctx.divide(D(1), D(0))


def acted(M, acts):
    ctx = M.Context(prec=28, traps=[], flags=[])
    for a in acts:
        do_act(M, ctx, a)
    return ctx


def run_sd(case):
    ctx = acted(C, case["acts"])
    ctx2 = acted(C, case["acts2"])      # kept alive: a SignalDict dies with its context
    sd = ctx.flags if case["bound"] else type(ctx.flags)()
    key = key_obj(C, case["key"])
    op = case["op"]
    if op == "len":
        return len(sd)
    if op == "iter":
        return [k.__name__ for k in sd]
    if op == "get":
        return sd[key]
    if op in ("set", "clear"):
        sd[key] = op == "set"
        return [s.__name__ for s in ctx2.flags if sd[s]]
    if op == "del":
        del sd[key]
        return None
    if op == "repr":
        return repr(sd)
    if op == "copy":
        d = sd.copy()
        return [k.__name__ for k, v in d.items() if v]
    w = case["w"]
    other = {"copy": lambda: sd.copy(), "self": lambda: sd, "unbound": lambda: type(ctx.flags)(),
             "other_ctx": lambda: ctx2.flags, "bad_dict": lambda: {5: True},
             "copy_frozen": lambda: frozendict(ctx.flags.copy()),
             "bad_frozen": lambda: frozendict({5: True}),
             "none": lambda: 7}[w]()
    r = sd.__eq__(other) if op == "eq" else sd.__ne__(other)
    return "NotImplemented" if r is NotImplemented else r


def run_local(M, case):
    t = case["tmpl"]
    base = with_template(M, t, lambda: M.Context())
    def body():
        kw = {k: ctx_val(M, v) for k, v in case["kw"]}
        M.setcontext(base)
        with M.localcontext(**kw) as nc:
            inner = enc_ctx(M, nc)
        return [inner, M.getcontext() is base]
    saved = M.getcontext()
    try:
        return with_template(M, t, body)
    finally:
        M.setcontext(saved)


def run_method(M, case):
    c = case["ctx"]
    ctx = M.Context(prec=c["prec"], rounding=getattr(M, c["rounding"]), Emin=c["emin"],
                    Emax=c["emax"], clamp=c["clamp"], traps=[getattr(M, t) for t in c["traps"]],
                    flags=[])
    a, b, t = build(M, case["a"]), build(M, case["b"]), build(M, case["t"])
    with M.localcontext(ctx) as cx:
        r = METHODS[case["m"]](M, a, b, t)
        flags = sorted(s for s in SIGNALS if cx.flags[getattr(M, s)])
    return [enc_val(M, r), flags]


def run_python(case):
    fn = case["fn"]

    def thunk():
        if fn in ("parse_py", "parse_c"):
            M = P if fn == "parse_py" else C
            return enc_dec(M.Decimal("".join(map(chr, case["s"]))))
        if fn in ("str_py", "str_c"):
            M = P if fn == "str_py" else C
            return cps(str(build(M, case["a"])))
        if fn in ("strrt_py", "strrt_c"):
            M = P if fn == "strrt_py" else C
            return enc_dec(M.Decimal(str(build(M, case["a"]))))
        if fn in ("tuple_py", "tuple_c"):
            M = P if fn == "tuple_py" else C
            digits = case["digits"]
            t = (unpyval(case["sign"]), None if digits is None else tuple(unpyval(x) for x in digits),
                 unpyval(case["exp"]))
            return cps(str(M.Decimal(t)))
        if fn == "as_tuple":
            t = build(MODS[case["impl"]], case["a"]).as_tuple()
            return [pyval(t.sign), [pyval(x) for x in t.digits], pyval(t.exponent)]
        if fn in ("hash_py", "hash_c"):
            d = build(P if fn == "hash_py" else C, case["a"])
            if d.is_qnan():
                return None
            return hash(d)
        if fn in ("int_py", "int_c"):
            d = build(P if fn == "int_py" else C, case["a"])
            f = {"int": int, "floor": math.floor, "ceil": math.ceil, "round": round}[case["mode"]]
            return hexint(f(d))
        if fn in ("ratio_py", "ratio_c"):
            n, d = build(P if fn == "ratio_py" else C, case["a"]).as_integer_ratio()
            return [hexint(n), hexint(d)]
        if fn in ("fromint_py", "fromint_c"):
            M = P if fn == "fromint_py" else C
            n = int(case["n"], 16)
            return enc_dec(M.Decimal(-n if case["neg"] else n))
        if fn in ("fmt_py", "fmt_c"):
            M = P if fn == "fmt_py" else C
            try:
                format(M.Decimal("1.5"), "".join(map(chr, case["spec"])))
                return "ok"
            except UnicodeEncodeError:
                return "UnicodeEncodeError"
            except ValueError:
                return "ValueError"
        if fn == "quantspec":
            d = C.Decimal((int(case["neg"]), tuple(map(int, case["c"])), case["e"]))
            big = C.Context(prec=5000, Emin=-(10 ** 6), Emax=10 ** 6, traps=[])
            r = d.quantize(C.Decimal((0, (1,), case["qe"])), rounding=getattr(C, case["rounding"]), context=big)
            return "".join(map(str, r.as_tuple().digits))
        if fn == "mulspec":
            ctx = C.Context(prec=case["prec"], rounding=getattr(C, case["rounding"]), Emin=-(10 ** 6),
                            Emax=10 ** 6, traps=[])
            a = C.Decimal((int(case["neg"]), tuple(map(int, case["c1"])), case["e1"]))
            b = C.Decimal((0, tuple(map(int, case["c2"])), case["e2"]))
            t = ctx.multiply(a, b).as_tuple()
            return ["".join(map(str, t.digits)), t.exponent]
        if fn == "compare_total":
            M = MODS[case["impl"]]
            return int(build(M, case["a"]).compare_total(build(M, case["b"])))
        if fn == "copy_sign":
            M = MODS[case["impl"]]
            return enc_dec(build(M, case["a"]).copy_sign(build(M, case["b"])))
        if fn == "rich":
            return run_rich(case)
        if fn == "fromfloat":
            return enc_dec(P.Decimal.from_float(ffrom(case["bits"])))
        if fn == "new_py":
            return run_new(case)
        if fn == "pow10":
            v, st = P._is_less_than_pow10a_use_str(int(case["q"]), int(case["a"]))
            return [v, st is not None]
        if fn == "op":
            return run_op(MODS[case["impl"]], case)
        if fn == "m":
            return run_method(MODS[case["impl"]], case)
        if fn == "cm":
            return run_cm(MODS[case["impl"]], case)
        if fn == "rop":
            return run_rop(MODS[case["impl"]], case)
        if fn == "ctxnew":
            M = MODS[case["impl"]]
            init = {k: ctx_val(M, v) for k, v in case["init"].items()}
            return enc_ctx(M, with_template(M, case["tmpl"], lambda: M.Context(**init)))
        if fn == "ctxset":
            M = MODS[case["impl"]]
            c = with_template(M, case["tmpl"], lambda: M.Context(
                prec=int(case["tmpl"]["prec"]), rounding=case["tmpl"]["rounding"],
                Emin=int(case["tmpl"]["Emin"]), Emax=int(case["tmpl"]["Emax"]),
                capitals=int(case["tmpl"]["capitals"]), clamp=int(case["tmpl"]["clamp"]),
                flags=[getattr(M, s) for s in case["tmpl"]["flags"]],
                traps=[getattr(M, s) for s in case["tmpl"]["traps"]]))
            setattr(c, case["name"], ctx_val(M, case["val"]))
            return enc_ctx(M, c)
        if fn == "ctxdel":
            M = MODS[case["impl"]]
            delattr(M.Context(), case["name"])
            return None
        if fn == "ctxrepr":
            M = MODS[case["impl"]]
            return repr(acted(M, case["acts"]))
        if fn == "sd":
            return run_sd(case)
        if fn == "ieee":
            M = MODS[case["impl"]]
            return enc_ctx(M, with_template(M, case["tmpl"], lambda: M.IEEEContext(ctx_val(M, case["bits"]))))
        if fn == "fmtarg_c":
            return C.Decimal(1).__format__({"int": 5, "NoneType": None, "float": 1.5, "bytes": b"f"}[case["arg"]])
        if fn == "local":
            return run_local(MODS[case["impl"]], case)
        raise SystemExit("unknown fn " + fn)

    return common.py_result(thunk)


if __name__ == "__main__":
    sys.set_int_max_str_digits(4300)
    common.main(gen_case, run_python, default_cases=20000)
