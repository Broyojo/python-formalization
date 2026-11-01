"""Differential test: Lean model of str (Objects/unicodeobject.c and friends)
vs. the running CPython.

Usage: python3 difftest/unicodeobj_diff.py [--cases N] [--seed S]
Set UO_SLICE=object|codec|format|text to run one slice only.

Strings and bytes travel as lists of ints, because JSON and Lean's `String` have
no lone surrogates. A slice registers generators with `@gen(slice, weight)` and
python sides with `@run("fn")`; `ONCE` holds cases emitted once, before the random
ones (the all-code-point table sweeps). Each slice edits its own section only.
"""

import os
import sys

import common

M = sys.maxsize
GENS = []  # (slice, weight, generator)
RUNS = {}  # fn name -> function(case) -> JSON-able result (exceptions are captured)
ONCE = []  # (slice, case)
SLICE = os.environ.get("UO_SLICE")


def gen(slice_name, weight=1):
    def register(f):
        GENS.append((slice_name, weight, f))
        return f
    return register


def run(name):
    def register(f):
        RUNS[name] = f
        return f
    return register


def s_of(cps):
    return "".join(map(chr, cps))


def cps_of(s):
    return [ord(c) for c in s]


# ==== object slice (fn names obj_*) ====

# ==== end object slice ====


# ==== codec slice (fn names codec_*) ====

# ==== end codec slice ====


# ==== format slice (fn names fmt_*) ====

SPEC_CHARS = "<>=^ +-z#0123456789,_.bcdeEfFgGnosxX%$a*\x00\xe9٣€\U0001f600"
INT_TYPES = "bcdoxXn"
FMT_INTS = [0, 1, -1, 2, 9, 10, 99, 100, 255, 256, 999, 1000, 1234567, -1234567, 65, 0x10ffff,
            0x110000, 2 ** 31, 2 ** 63 - 1, 2 ** 63, -2 ** 63, 2 ** 64, 10 ** 20, -10 ** 20,
            10 ** 4299, 10 ** 4300 - 1, 10 ** 4300, -10 ** 4300, 16 ** 40]


def fmt_spec(rng):
    r = rng.random()
    if r < 0.25:
        return "".join(rng.choice(SPEC_CHARS) for _ in range(rng.randint(0, 6)))
    fill = rng.choice(["", "", "*", "0", " ", "\xe9", "\U0001f600", "<", "\x00"])
    align = rng.choice(["", "", "<", ">", "=", "^"]) if fill == "" else rng.choice("<>=^")
    sign = rng.choice(["", "", "+", "-", " "])
    z = rng.choice(["", "", "", "z"])
    alt = rng.choice(["", "", "#"])
    zero = rng.choice(["", "", "0"])
    width = rng.choice(["", "", "1", "5", "12", "30", chr(0x663), "007", str(2 ** 63), "9" * 30])
    group = rng.choice(["", "", "", ",", "_", ",_", "_,"])
    prec = rng.choice(["", "", "", ".", ".3", ".0", ".,", "._", ".3,", ".3_", "._,", ".,_",
                       "." + str(2 ** 31), "." + "9" * 30])
    typ = rng.choice(["", "", "d", "b", "o", "x", "X", "n", "c", "s", "e", "f", "g", "%", "\x00",
                      "q", "\xe9", "€", "dd"])
    return fill + align + sign + z + alt + zero + width + group + prec + typ


@gen("format", 10)
def gen_fmt_int(rng):
    spec = fmt_spec(rng)
    v = rng.choice(FMT_INTS) if rng.random() < 0.7 else rng.randint(-10 ** 6, 10 ** 6)
    name = "int"
    if rng.random() < 0.08:
        v, name = rng.choice([0, 1]), "bool"
    return {"mod": "unicodeobj", "fn": "fmt_int", "v": hex_of(v), "name": name, "spec": cps_of(spec)}


@gen("format", 6)
def gen_fmt_str(rng):
    return {"mod": "unicodeobj", "fn": "fmt_str", "s": cps_of(rng.choice(
        ["", "a", "abc", "hello world", "\xe9t\xe9", "€", "\U0001f600x"])), "spec": cps_of(fmt_spec(rng))}


@gen("format", 2)
def gen_fmt_float(rng):
    return {"mod": "unicodeobj", "fn": rng.choice(["fmt_float", "fmt_complex"]),
            "spec": cps_of(fmt_spec(rng))}


def hex_of(v):
    return ("-" if v < 0 else "") + format(abs(v), "x")


PCT_TYPES = "sradiuoxXc"
PCT_OBJS = [0, 1, -1, 7, 255, -255, 65, 0x10ffff, 0x110000, 2 ** 63, -2 ** 63, 10 ** 30, 10 ** 4300,
            True, False, None, "", "a", "abc", chr(0xe9), chr(0x20ac), chr(0x1f600), "it's"]


def pct_enc(o):
    if o is None:
        return {"t": "none"}
    if isinstance(o, bool):
        return {"t": "bool", "v": o}
    if isinstance(o, int):
        return {"t": "int", "v": hex_of(o)}
    return {"t": "str", "s": cps_of(o)}


def pct_dec(j):
    t = j["t"]
    if t == "none":
        return None
    if t == "bool":
        return j["v"]
    if t == "int":
        s = j["v"]
        return -int(s[1:], 16) if s.startswith("-") else int(s, 16)
    return s_of(j["s"])


def pct_directive(rng):
    flags = "".join(rng.choice("-+ #0") for _ in range(rng.choice([0, 0, 1, 2])))
    width = rng.choice(["", "", "1", "7", "20", "*", "0"])
    prec = rng.choice(["", "", ".", ".0", ".3", ".12", ".*"])
    mod = rng.choice(["", "", "", "h", "l", "L"])
    typ = rng.choice(PCT_TYPES) if rng.random() < 0.9 else rng.choice(["%", "q", chr(0xe9), "", chr(0x1f600)])
    return "%" + flags + width + prec + mod + typ


@gen("format", 8)
def gen_fmt_percent(rng):
    if rng.random() < 0.85:
        fmt = rng.choice(["", "x"]) + "".join(pct_directive(rng) + rng.choice(["", " ", "%%"])
                                              for _ in range(rng.randint(1, 2)))
        count = fmt.count("%") - 2 * fmt.count("%%") + fmt.count("*")
        count = max(0, count + rng.choice([0, 0, 0, 0, 1, -1]))
        items = [rng.choice(PCT_OBJS) if rng.random() < 0.8 else rng.choice([3, -3, 12, 2 ** 31])
                 for _ in range(count)]
        if rng.random() < 0.15 and len(items) == 1:
            args = {"k": "single", "item": pct_enc(items[0])}
        else:
            args = {"k": "tuple", "items": [pct_enc(o) for o in items]}
    else:
        key = rng.choice(["a", "b", "x(y)z", ""])
        fmt = ("%(" + key + rng.choice([")", ")", ")", ""]) + rng.choice(["s", "d", "5r", "x", "c"])
               + rng.choice(["", "%%", " %(a)s"]))
        args = {"k": "dict", "items": [[cps_of(k), pct_enc(rng.choice(PCT_OBJS))]
                                       for k in rng.sample(["a", "b", "x(y)z", ""], rng.randint(0, 3))]}
    return {"mod": "unicodeobj", "fn": "fmt_percent", "fmt": cps_of(fmt), "args": args}


@run("fmt_percent")
def run_fmt_percent(c):
    a = c["args"]
    if a["k"] == "tuple":
        args = tuple(pct_dec(o) for o in a["items"])
    elif a["k"] == "dict":
        args = {s_of(k): pct_dec(v) for k, v in a["items"]}
    else:
        args = pct_dec(a["item"])
    return cps_of(s_of(c["fmt"]) % args)


@run("fmt_int")
def run_fmt_int(c):
    s = c["v"]
    v = -int(s[1:], 16) if s.startswith("-") else int(s, 16)
    if c["name"] == "bool":
        v = bool(v)
    spec = s_of(c["spec"])
    r = format(v, spec)
    return "float" if spec[-1:] in tuple("eEfFgG%") else cps_of(r)


@run("fmt_str")
def run_fmt_str(c):
    return cps_of(format(s_of(c["s"]), s_of(c["spec"])))


@run("fmt_float")
def run_fmt_float(c):
    format(1.5, s_of(c["spec"]))
    return True


@run("fmt_complex")
def run_fmt_complex(c):
    format(1.5 + 2j, s_of(c["spec"]))
    return True

# ==== end format slice ====


# ==== text slice (fn names text_*) ====

import ctypes
import subprocess
import textwrap
import unicodedata

import _sre

TEXT_ALPH = [65, 90, 97, 122, 48, 57, 95, 32, 39, 34, 92, 46, 45, 9, 10, 13, 11, 12, 0x1c, 0x1f,
             0x7f, 0x80, 0x85, 0xa0, 0xaa, 0xad, 0xb5, 0xb7, 0xbd, 0xdf, 0xe9, 0xff, 0x130, 0x131,
             0x149, 0x17f, 0x1c4, 0x1c5, 0x1c6, 0x1f0, 0x2b0, 0x2bc, 0x300, 0x301, 0x345, 0x37a,
             0x390, 0x391, 0x3a3, 0x3c2, 0x3c3, 0x2019, 0x2028, 0x2029, 0x3000, 0x660, 0x663,
             0xbf0, 0x1e9e, 0x1f80, 0x1f88, 0x1fb3, 0x1fb7, 0x2160, 0x2170, 0x2460, 0xfb00,
             0xfb03, 0xd800, 0xdfff, 0xfffe, 0xffff, 0x10000, 0x10400, 0x10428, 0x1d7ce, 0x10ffff]
CASE_OPS = ["upper", "lower", "title", "capitalize", "casefold", "swapcase"]
IS_OPS = ["isascii", "islower", "isupper", "istitle", "isspace", "isalpha", "isalnum",
          "isdecimal", "isdigit", "isnumeric", "isprintable", "isidentifier"]
BYTE_OPS = ["isspace", "isalpha", "isalnum", "isdigit", "isascii", "islower", "isupper",
            "istitle", "lower", "upper", "title", "capitalize", "swapcase"]
SWEEP_BLOCK = 0x1000
SWEEP_PRIME = 2 ** 61 - 1


def text_str(rng, maxlen=8):
    n = rng.choice([0, 1, 1, 2, 3, maxlen, rng.randint(0, maxlen)])
    pool = TEXT_ALPH if rng.random() < 0.7 else rng.sample(TEXT_ALPH, 4)
    if rng.random() < 0.2:
        pool = [c for c in TEXT_ALPH if c < 128]
    return [rng.choice(pool) for _ in range(n)]


def text_item(rng):
    r = rng.random()
    if r < 0.25:
        return {"t": "none"}
    if r < 0.6:
        return {"t": "int", "v": rng.choice([97, 65, 0, 127, 128, 255, 256, 0x10ffff, 0x110000,
                                             -1, 2 ** 31, 2 ** 63, 2 ** 64, -2 ** 63])}
    if r < 0.9:
        return {"t": "str", "s": text_str(rng, 3)}
    if r < 0.95:
        return {"t": "wrong"}
    return {"t": "raise"}


@gen("text", 12)
def gen_text_case(rng):
    return {"mod": "unicodeobj", "fn": "text_case", "op": rng.choice(CASE_OPS), "s": text_str(rng)}


@gen("text", 8)
def gen_text_is(rng):
    return {"mod": "unicodeobj", "fn": "text_is", "op": rng.choice(IS_OPS), "s": text_str(rng)}


@gen("text", 6)
def gen_text_bytes(rng):
    alph = [65, 90, 97, 122, 48, 57, 32, 9, 13, 11, 39, 0, 127, 128, 0xe9, 0xff]
    b = [rng.choice(alph) for _ in range(rng.choice([0, 1, 1, 2, 3, 6]))]
    return {"mod": "unicodeobj", "fn": "text_bytes", "op": rng.choice(BYTE_OPS), "s": b}


@gen("text", 4)
def gen_text_repr(rng):
    return {"mod": "unicodeobj", "fn": "text_repr", "s": text_str(rng)}


@gen("text", 6)
def gen_text_translate(rng):
    s = text_str(rng)
    keys = (s + rng.sample(TEXT_ALPH, 2)) if rng.random() < 0.8 else rng.sample(TEXT_ALPH, 3)
    table = {k: text_item(rng) for k in keys if rng.random() < 0.6}
    fn = "text_translate" if rng.random() < 0.8 else "text_translate_strict"
    return {"mod": "unicodeobj", "fn": fn, "s": s, "table": [[k, v] for k, v in table.items()]}


@gen("text", 3)
def gen_text_maketrans(rng):
    r = rng.random()
    if r < 0.5:
        x = text_str(rng, 5)
        y = text_str(rng, 5)
        if rng.random() < 0.7:
            y = (y + [65] * len(x))[:len(x)]
        z = text_str(rng, 3) if rng.random() < 0.6 else None
        return {"mod": "unicodeobj", "fn": "text_maketrans_str", "x": x, "y": y, "z": z}
    if r < 0.9:
        items = []
        seen = set()
        for _ in range(rng.randrange(4)):
            kr = rng.random()
            k = ({"t": "str", "s": text_str(rng, 2)} if kr < 0.5 else
                 {"t": "int", "v": rng.choice([97, -1, 2 ** 70])} if kr < 0.9 else {"t": "other"})
            if str(k) not in seen:
                seen.add(str(k))
                items.append([k, text_item(rng)])
        return {"mod": "unicodeobj", "fn": "text_maketrans_dict", "x": items}
    return {"mod": "unicodeobj", "fn": "text_maketrans_other", "y": rng.choice([None, [97]])}


DEDENT_LINES = ["", " ", "  ", "\t", " \t", "    ", "a", " a", "  a", "   b", "\ta", " \ta", "  \tb",
                "    c", "  \x0c", "\x0c", "\r", "  \r", "　", "  　x", "  \xe9"]


@gen("text", 2)
def gen_text_dedent(rng):
    lines = [rng.choice(DEDENT_LINES) for _ in range(rng.randint(0, 5))]
    return {"mod": "unicodeobj", "fn": "text_dedent", "s": cps_of("\n".join(lines))}


@gen("text", 0.02)
def gen_text_dedent_c(rng):
    margin = rng.choice([" ", "  ", "    ", "\t", " \t"])
    body = [rng.choice([margin + "x", margin + " y", margin, " ", "", margin + margin, "\x0c",
                        margin[:1], "\r"]) for _ in range(rng.randint(1, 4))]
    text = margin + 's = """' + "\n".join(body) + "\n" + margin + '"""\n' + margin + "print(ascii(s))"
    return {"mod": "unicodeobj", "fn": "text_dedent_c", "s": cps_of(text)}


@gen("text", 1)
def gen_text_transform(rng):
    return {"mod": "unicodeobj", "fn": "text_transform", "s": text_str(rng)}


for _lo in range(0, 0x110000, SWEEP_BLOCK):
    ONCE.append(("text", {"mod": "unicodeobj", "fn": "text_sweep", "lo": _lo, "hi": _lo + SWEEP_BLOCK}))

RAISE = object()


def conv_item(v):
    return {"none": None, "int": v.get("v"), "str": s_of(v.get("s", [])), "raise": RAISE,
            "wrong": 1.5}[v["t"]]


class TextMapping:
    def __init__(self, table):
        self.d = {k: conv_item(v) for k, v in table}

    def __getitem__(self, k):
        v = self.d[k]
        if v is RAISE:
            raise ValueError("boom")
        return v


UPPER_SIMPLE = ctypes.pythonapi._PyUnicode_ToUppercase
TITLE_SIMPLE = ctypes.pythonapi._PyUnicode_ToTitlecase
for _f in (UPPER_SIMPLE, TITLE_SIMPLE):
    _f.restype = ctypes.c_uint
    _f.argtypes = [ctypes.c_uint]
TRANSLATE = ctypes.pythonapi.PyUnicode_Translate
TRANSLATE.restype = ctypes.py_object
TRANSLATE.argtypes = [ctypes.py_object, ctypes.py_object, ctypes.c_char_p]


@run("text_case")
def run_text_case(c):
    return cps_of(getattr(s_of(c["s"]), c["op"])())


@run("text_is")
def run_text_is(c):
    return getattr(s_of(c["s"]), c["op"])()


@run("text_bytes")
def run_text_bytes(c):
    r = getattr(bytes(c["s"]), c["op"])()
    return r if isinstance(r, bool) else list(r)


@run("text_repr")
def run_text_repr(c):
    return cps_of(repr(s_of(c["s"])))


@run("text_translate")
def run_text_translate(c):
    return cps_of(s_of(c["s"]).translate(TextMapping(c["table"])))


@run("text_translate_strict")
def run_text_translate_strict(c):
    return cps_of(TRANSLATE(s_of(c["s"]), TextMapping(c["table"]), None))


def enc_item(v):
    if v is None:
        return ["none"]
    if isinstance(v, int):
        return ["int", v]
    if isinstance(v, str):
        return ["str", cps_of(v)]
    return ["raise"] if v is RAISE else ["wrong"]


def enc_trans(d):
    return [[k, enc_item(v)] for k, v in d.items()]


@run("text_maketrans_str")
def run_text_maketrans_str(c):
    args = [s_of(c["x"]), s_of(c["y"])] + ([s_of(c["z"])] if c["z"] is not None else [])
    return enc_trans(str.maketrans(*args))


@run("text_maketrans_dict")
def run_text_maketrans_dict(c):
    d = {}
    for k, v in c["x"]:
        key = s_of(k["s"]) if k["t"] == "str" else k["v"] if k["t"] == "int" else (1, 2)
        d[key] = conv_item(v)
    return enc_trans(str.maketrans(d))


@run("text_maketrans_other")
def run_text_maketrans_other(c):
    if c["y"] is None:
        str.maketrans(3)
    else:
        str.maketrans(3, s_of(c["y"]))
    return None


@run("text_dedent")
def run_text_dedent(c):
    return cps_of(textwrap.dedent(s_of(c["s"])))


@run("text_dedent_c")
def run_text_dedent_c(c):
    r = subprocess.run([sys.executable, "-c", s_of(c["s"])], capture_output=True, text=True)
    if r.returncode != 0:
        return -1
    return cps_of(eval(r.stdout))


@run("text_transform")
def run_text_transform(c):
    f = ctypes.pythonapi._PyUnicode_TransformDecimalAndSpaceToASCII
    f.restype = ctypes.py_object
    f.argtypes = [ctypes.py_object]
    return cps_of(f(s_of(c["s"])))


def sweep_values(c):
    ch = chr(c)
    upper, lower, title, fold = ch.upper(), ch.lower(), ch.title(), ch.casefold()
    cased = (ch + "a").title()[-1] == "a"
    if cased:
        ignorable = (ch + "Σ").lower()[-1] == "σ"
    else:
        ignorable = ("A" + ch + "Σ").lower()[-1] == "ς"
    return [int(ch.isalpha()), int(ch.isdecimal()), int(ch.isdigit()), int(ch.isnumeric()),
            int(ch.isprintable()), int(ch.islower()), int(ch.isupper()), int(ch.istitle()),
            int(ch.isspace()), int(ch.isidentifier()), int(("a" + ch).isidentifier()),
            int(len(("a" + ch + "b").splitlines()) > 1), int(cased), int(ignorable),
            unicodedata.decimal(ch, -1) + 1, unicodedata.digit(ch, -1) + 1,
            UPPER_SIMPLE(c), _sre.unicode_tolower(c), TITLE_SIMPLE(c),
            len(upper), *map(ord, upper), len(lower), *map(ord, lower), len(title),
            *map(ord, title), len(fold), *map(ord, fold)]


@run("text_sweep")
def run_text_sweep(c):
    h = 0
    for cp in range(c["lo"], c["hi"]):
        for v in sweep_values(cp):
            h = (h * 1000003 + v + 1) % SWEEP_PRIME
    return h

# ==== end text slice ====


active = [(w, f) for s, w, f in GENS if SLICE in (None, s)]
pending = [c for s, c in ONCE if SLICE in (None, s)]
total_weight = sum(w for w, _ in active)


def gen_case(rng):
    if pending:
        return pending.pop()
    r = rng.uniform(0, total_weight)
    for w, f in active:
        r -= w
        if r <= 0:
            return f(rng)
    return active[-1][1](rng)


def run_python(case):
    return common.py_result(lambda: RUNS[case["fn"]](case))


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=20000)
