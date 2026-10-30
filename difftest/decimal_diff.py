"""Differential test: Lean model of decimal vs. the running CPython's two twins.

Usage: python3 difftest/decimal_diff.py [--cases N] [--seed S]

Exits non-zero on any mismatch. See difftest/common.py.

`fn` names ending in `_py` run against `_pydecimal`, `_c` against `_decimal`;
`op` cases carry `"impl": "py" | "c"`. A decimal travels as
["F", neg, "<coeff digits>", exp] | ["I", neg] | ["N", neg, signaling, "<payload>"]
and is rebuilt on the Python side from a tuple (which neither twin limits).
Ints travel as hex(i). Strings and format specs travel as code point lists.
"""

import math
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
ND_ZEROS = [0x30, 0x660, 0x6f0, 0x966, 0xff10, 0x1d7ce, 0x104a0, 0x1e950]
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


OPS = ["add", "sub", "mul", "quantize", "quantize", "tiv", "tie", "roundn", "normalize", "fix"]


MAX_PREC = MAX_EMAX = 999999999999999999
MIN_ETINY = -999999999999999999 - (MAX_PREC - 1)


def in_c_limits(j):
    """The value is representable by _decimal (InCLimits in Basic.lean)."""
    if j[0] == "F":
        n = len(j[2].lstrip("0") or "0")
        return n <= MAX_PREC and j[3] + n - 1 <= MAX_EMAX and j[3] >= MIN_ETINY
    return True


def gen_case(rng):
    while True:
        c = gen_case1(rng)
        if c["fn"].endswith("_c") or c.get("impl") == "c":
            if not all(in_c_limits(c[k]) for k in ("a", "b") if k in c):
                continue
        return c


def gen_case1(rng):
    k = rng.random()
    if k < 0.18:
        return {"mod": "decimal", "fn": rng.choice(["parse_py", "parse_c"]),
                "s": cps(gen_numeric_string(rng))}
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
        return {"mod": "decimal", "fn": rng.choice(["fmt_py", "fmt_c"]), "spec": cps(gen_spec(rng))}
    if k < 0.62:
        return {"mod": "decimal", "fn": rng.choice(["compare_total", "copy_sign"]),
                "impl": rng.choice(["py", "c"]),
                "a": gen_dec(rng, special=0.3), "b": gen_dec(rng, special=0.3)}
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


def run_python(case):
    fn = case["fn"]

    def thunk():
        if fn in ("parse_py", "parse_c"):
            M = P if fn == "parse_py" else C
            return enc_dec(M.Decimal("".join(map(chr, case["s"]))))
        if fn in ("str_py", "str_c"):
            M = P if fn == "str_py" else C
            return cps(str(build(M, case["a"])))
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
        if fn == "compare_total":
            M = MODS[case["impl"]]
            return int(build(M, case["a"]).compare_total(build(M, case["b"])))
        if fn == "copy_sign":
            M = MODS[case["impl"]]
            return enc_dec(build(M, case["a"]).copy_sign(build(M, case["b"])))
        if fn == "op":
            return run_op(MODS[case["impl"]], case)
        raise SystemExit("unknown fn " + fn)

    return common.py_result(thunk)


if __name__ == "__main__":
    sys.set_int_max_str_digits(4300)
    common.main(gen_case, run_python, default_cases=20000)
