"""Differential test: Lean model of fractions vs. the running CPython.

Usage: python3 difftest/fractions_diff.py [--cases N] [--seed S]

Exits non-zero on any mismatch. See difftest/common.py.

A Fraction travels as [numerator, denominator] and is rebuilt on both sides
with Fraction(n, d). Ints of 1000+ digits travel as {"hex": hex(i)}, since
json cannot print ints past the int string-conversion limit.
"""

import sys
from decimal import Decimal
from fractions import Fraction

import common

P = sys.hash_info.modulus
BIG = 10 ** 1000

FNS_UNARY = ["str", "format", "format", "format", "format", "floor", "ceil", "trunc", "int",
             "round", "round_nd", "hash", "limit", "limit", "is_integer", "ratio", "pow",
             "neg", "abs"]
FNS_BINARY = ["add", "sub", "mul", "truediv", "floordiv", "mod", "divmod",
              "eq", "lt", "le", "gt", "ge"]
FNS_OTHER = ["ctor", "parse", "parse", "parse", "decimal", "dechash"]


def enc(i):
    return {"hex": hex(i)} if abs(i) >= BIG else i


def dec(j):
    return int(j["hex"], 16) if isinstance(j, dict) else j


def edge_int(rng, huge=False):
    k = rng.randrange(1, 40)
    choices = [0, 1, -1, 2, -2, 3, 5, 7, 10, -10, 12, 100, 999, 1000,
               rng.randrange(-20, 21), rng.randrange(-1000, 1001),
               rng.randrange(-10 ** k, 10 ** k), 10 ** k, -(10 ** k), 2 ** k, 10 ** k + 1,
               P, P - 1, P + 1, 2 * P, -P, P * rng.randrange(1, 5), 2 ** 61, 2 ** 63, -2 ** 63,
               2 ** 64, sys.maxsize, rng.randrange(-2 ** 64, 2 ** 64)]
    if huge:
        choices += [10 ** 4299, 10 ** 4300, -10 ** 4300, 10 ** 4299 + 7, 3 ** 9000,
                    10 ** 4300 + 1]
    return rng.choice(choices)


def edge_frac(rng, huge=False):
    n = edge_int(rng, huge and rng.random() < 0.1)
    d = edge_int(rng, huge and rng.random() < 0.1)
    if d == 0:
        d = 1
    if rng.random() < 0.2:
        d = rng.choice([1, 2, 3, 4, 8, 10, 100, 1000, 7, 6])
    return [n, d]


DIGITS = "0123456789"
UDIGITS = "٠٥۳१１９"
WS = [" ", "\t", "\n", "\x0b", "\x0c", "\r", "\x1c", "\x1f", "\x85", "\xa0", " ",
      " ", " ", " ", " ", " ", " ", "　", "​"]


def rand_digits(rng, allow_us=True):
    out = []
    for _ in range(rng.randrange(1, 6)):
        out.append(rng.choice(DIGITS) if rng.random() < 0.9 else rng.choice(UDIGITS))
    s = "".join(out)
    if allow_us and rng.random() < 0.2:
        pos = rng.randrange(0, len(s) + 1)
        s = s[:pos] + rng.choice(["_", "_", "_", "__"]) + s[pos:]
    return s


def rand_ws(rng):
    if rng.random() < 0.6:
        return ""
    return "".join(rng.choice(WS) for _ in range(rng.randrange(1, 3)))


def rand_numstr(rng):
    s = rand_ws(rng) + rng.choice(["", "", "", "+", "-", "-", "--"])
    form = rng.randrange(4)
    if form == 0:
        s += rand_digits(rng) + rand_ws(rng) + rng.choice(["/", "/", "/", "//", ""]) + rand_ws(rng) + rand_digits(rng)
    else:
        s += rng.choice(["", rand_digits(rng)])
        if rng.random() < 0.7:
            s += "." + rng.choice(["", rand_digits(rng)])
        if rng.random() < 0.5:
            s += rng.choice("eE") + rng.choice(["", "+", "-"]) + rng.choice(["", rand_digits(rng)])
    s += rand_ws(rng)
    r = rng.random()
    if r < 0.05:
        s = "".join(rng.choice("0123456789_./eE+- x١") for _ in range(rng.randrange(0, 8)))
    elif r < 0.08:
        k = rng.choice([4299, 4300, 4301])
        pre = rng.choice(["", "-", "0.", "1/", "1e"])
        if pre == "1e":
            k = 4301  # a smaller exponent this long would make 10**exp run forever
        s = pre + "1" * k + rng.choice(["", "/7", ".5", "e2"])
    elif r < 0.1:
        s = rng.choice(["inf", "nan", "1e", ".", "", " ", "_1", "1_", "0x10", "1.2.3", "1/0",
                        "-0/5", "+.5e-3", "1 / 2", "1/2e3", "1.5/2", "١/٣"])
    return s


def rand_spec(rng):
    if rng.random() < 0.35:
        # general (no presentation type)
        s = ""
        if rng.random() < 0.4:
            if rng.random() < 0.5:
                s += rng.choice("*0x <>")
            s += rng.choice("<>=^")
        s += rng.choice(["", "", "+", "-", " "])
        if rng.random() < 0.3:
            s += "#"
        if rng.random() < 0.5:
            s += rng.choice(["0", "5", "12", "25", "00", "05"])
        if rng.random() < 0.3:
            s += rng.choice(",_")
        if rng.random() < 0.05:
            s += rng.choice(["z", "n", "d", "x", ".2"])
        return s
    s = ""
    if rng.random() < 0.4:
        if rng.random() < 0.5:
            s += rng.choice("*0x <>.")
        s += rng.choice("<>=^")
    s += rng.choice(["", "", "+", "-", " "])
    if rng.random() < 0.3:
        s += "z"
    if rng.random() < 0.3:
        s += "#"
    if rng.random() < 0.3:
        s += "0"
    if rng.random() < 0.6:
        s += str(rng.randrange(0, 30))
    if rng.random() < 0.3:
        s += rng.choice(",_")
    if rng.random() < 0.7:
        s += "." + rng.choice(["", str(rng.randrange(0, 25))])
        if rng.random() < 0.15:
            s += rng.choice(",_")
    s += rng.choice("eEfFgG%" if rng.random() < 0.97 else "nxd")
    return s


def gen_case(rng):
    fn = rng.choice(FNS_UNARY + FNS_BINARY + FNS_OTHER)
    c = {"mod": "fractions", "fn": fn}
    if fn == "ctor":
        n, d = edge_int(rng, rng.random() < 0.1), edge_int(rng, rng.random() < 0.1)
        if rng.random() < 0.1:
            d = 0
        c.update(n=enc(n), d=enc(d))
    elif fn == "parse":
        c.update(s=rand_numstr(rng))
    elif fn in ("decimal", "dechash"):
        c.update(neg=rng.random() < 0.5, coeff=abs(edge_int(rng)), exp=rng.randrange(-60, 60))
    elif fn in FNS_UNARY:
        a = edge_frac(rng, huge=fn in ("str", "format", "hash", "limit"))
        c.update(a=[enc(v) for v in a])
        if fn == "format":
            c.update(spec=rand_spec(rng))
        elif fn == "round_nd":
            c.update(nd=rng.randrange(-8, 9))
        elif fn == "limit":
            c.update(m=enc(rng.choice([1, 2, 3, 10, 100, 10 ** 6, rng.randrange(1, 1000), abs(a[1]),
                                       abs(a[1]) - 1, abs(a[1]) + 1, 0, -1, rng.randrange(1, 10 ** 20)])))
        elif fn == "pow":
            a = [rng.randrange(-30, 31), rng.randrange(1, 30)]
            c.update(a=a, e=rng.randrange(-12, 13))
    else:
        a, b = edge_frac(rng), edge_frac(rng)
        if rng.random() < 0.3:
            a[1] = 1
            c.update(aint=True)
        if rng.random() < 0.3 and not c.get("aint"):
            b[1] = 1
            c.update(bint=True)
        if rng.random() < 0.1:
            b[0] = 0
        c.update(a=[enc(v) for v in a], b=[enc(v) for v in b])
    return c


def enc_frac(x):
    return [enc(x.numerator), enc(x.denominator)]


def run_python(c):
    fn = c["fn"]
    try:
        if fn == "ctor":
            v = enc_frac(Fraction(dec(c["n"]), dec(c["d"])))
        elif fn == "parse":
            v = enc_frac(Fraction(c["s"]))
        elif fn in ("decimal", "dechash"):
            digits = tuple(int(ch) for ch in str(c["coeff"]))
            d = Decimal((1 if c["neg"] else 0, digits, c["exp"]))
            v = enc_frac(Fraction(d)) if fn == "decimal" else hash(d)
        else:
            a = Fraction(dec(c["a"][0]), dec(c["a"][1]))
            if c.get("aint"):
                a = int(a)
            if fn == "str":
                v = str(a)
            elif fn == "format":
                v = format(a, c["spec"])
            elif fn == "floor":
                v = enc(a.__floor__())
            elif fn == "ceil":
                v = enc(a.__ceil__())
            elif fn == "trunc":
                v = enc(a.__trunc__())
            elif fn == "int":
                v = enc(int(a))
            elif fn == "round":
                v = enc(round(a))
            elif fn == "round_nd":
                v = enc_frac(round(a, c["nd"]))
            elif fn == "hash":
                v = enc(hash(a))
            elif fn == "limit":
                v = enc_frac(a.limit_denominator(dec(c["m"])))
            elif fn == "is_integer":
                v = a.is_integer()
            elif fn == "ratio":
                v = [enc(t) for t in a.as_integer_ratio()]
            elif fn == "pow":
                v = enc_frac(a ** c["e"])
            elif fn == "neg":
                v = enc_frac(-a)
            elif fn == "abs":
                v = enc_frac(abs(a))
            else:
                b = Fraction(dec(c["b"][0]), dec(c["b"][1]))
                if c.get("bint"):
                    b = int(b)
                if fn == "add":
                    v = enc_frac(a + b)
                elif fn == "sub":
                    v = enc_frac(a - b)
                elif fn == "mul":
                    v = enc_frac(a * b)
                elif fn == "truediv":
                    v = enc_frac(a / b)
                elif fn == "floordiv":
                    v = enc(a // b)
                elif fn == "mod":
                    v = enc_frac(a % b)
                elif fn == "divmod":
                    q, r = divmod(a, b)
                    v = [enc(q), enc_frac(r)]
                elif fn == "eq":
                    v = a == b
                elif fn == "lt":
                    v = a < b
                elif fn == "le":
                    v = a <= b
                elif fn == "gt":
                    v = a > b
                elif fn == "ge":
                    v = a >= b
        return {"ok": v}
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}


if __name__ == "__main__":
    common.main(gen_case, run_python)
