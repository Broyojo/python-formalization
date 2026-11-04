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
import struct
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

OBJ_ALPH = [0, 65, 97, 127, 128, 233, 255, 256, 0x20ac, 0xd800, 0xffff, 0x10000, 0x1f600, 0x10ffff]


def obj_str(rng, maxlen=7):
    pool = rng.sample(OBJ_ALPH, rng.choice([1, 2, 3, len(OBJ_ALPH)]))
    return [rng.choice(pool) for _ in range(rng.randint(0, maxlen))]


def kind_of(s):
    import ctypes
    f = ctypes.pythonapi.PyUnicode_KIND
    f.restype = ctypes.c_int
    f.argtypes = [ctypes.py_object]
    return [f(s), s.isascii()]


@gen("object", 3)
def gen_obj_concat(rng):
    return {"mod": "unicodeobj", "fn": "obj_concat", "l": obj_str(rng), "r": obj_str(rng)}


@gen("object", 3)
def gen_obj_slice(rng):
    s = obj_str(rng, 12)
    start, stop = rng.randint(-14, 14), rng.randint(-14, 14)
    step = rng.choice([-3, -2, -1, 2, 3, 5])
    sub = s[start:stop:step]
    if not sub:
        return None
    return {"mod": "unicodeobj", "fn": "obj_slice", "s": s, "sub": sub, "start": start,
            "stop": stop, "step": step}


@gen("object", 2)
def gen_obj_repeat(rng):
    n = rng.choice([-1, 0, 1, 2, 3, 7])
    s = obj_str(rng)
    if rng.random() < 0.1 and len(s) >= 2:  # OverflowError; a shorter s would really allocate
        n = sys.maxsize
    return {"mod": "unicodeobj", "fn": "obj_repeat", "s": s, "n": n}


@gen("object", 3)
def gen_obj_compare(rng):
    a = obj_str(rng)
    b = list(a) if rng.random() < 0.3 else obj_str(rng)
    if b and rng.random() < 0.5:
        b[rng.randrange(len(b))] = rng.choice(OBJ_ALPH)
    return {"mod": "unicodeobj", "fn": "obj_compare", "a": a, "b": b}


@run("obj_concat")
def run_obj_concat(c):
    r = s_of(c["l"]) + s_of(c["r"])
    return [cps_of(r), kind_of(r)]


@run("obj_slice")
def run_obj_slice(c):
    r = s_of(c["s"])[c["start"]:c["stop"]:c["step"]]
    assert cps_of(r) == c["sub"]
    return kind_of(r)


@run("obj_repeat")
def run_obj_repeat(c):
    return cps_of(s_of(c["s"]) * c["n"])


@run("obj_compare")
def run_obj_compare(c):
    a, b = s_of(c["a"]), s_of(c["b"])
    return (a > b) - (a < b)

# ==== end object slice ====


# ==== error handler callbacks (fn names codec_cb_*) ====

CB_BYTES = [0, 0x41, 0x7f, 0x80, 0xff, 0x5c, 0x78, 0x75, 0xed, 0xd8, 0xdc, 0xc2, 0xe2, 0x2b, 0x2d, 0xfe]
CB_REPS = ["", "x", "xyz", "\xe9", "\u20ac", "\U0001f600", "\ud800"]
CB_POS = [0, 1, 2, 3, 4, 8, -1, -2, -3, 99, -99, 2 ** 63 - 1, 2 ** 63, -2 ** 63, -2 ** 63 - 1, 2 ** 64]
CB_CODECS = ["utf-8", "utf-16", "utf-32", "ascii", "unicode_escape", "raw_unicode_escape", "utf-7", "charmap"]
CB_TABLE = [cp for cp in (97, 98, 0xfffe, 0x20ac, 0x1f600)]


def cb_bytes(rng):
    b = [rng.choice(CB_BYTES) for _ in range(rng.randint(0, 8))]
    # most cases should reach the handler, so most inputs carry something undecodable
    return b + [rng.choice([0xff, 0xed, 0x5c, 0xfe])] if rng.random() < 0.7 else b


def cb_pos(rng):
    """A position: mostly `end + small`, which makes progress, so the decoder gets to finish."""
    if rng.random() < 0.72:
        return rng.choice([0, 0, 0, 0, 1, 1, 2, -1]), True
    return rng.choice(CB_POS), False


def gen_dec_step(rng):
    r = rng.random()
    if r < 0.08:
        return {"t": "raise"}
    if r < 0.16:
        return {"t": "bad", "form": rng.randint(0, 3)}
    o = rng.random()
    if o < 0.84:
        obj = {"k": "keep"}
    elif o < 0.94:
        obj = {"k": "set", "b": cb_bytes(rng)}
    elif o < 0.97:
        obj = {"k": "wrong"}
    else:
        obj = {"k": "del"}
    pos, rel = cb_pos(rng)
    return {"t": "ret", "rep": cps_of(rng.choice(CB_REPS)), "pos": pos, "rel": rel, "obj": obj}


@gen("codec", 8)
def gen_codec_cb_decode(rng):
    c = {"mod": "unicodeobj", "fn": "codec_cb_decode", "codec": rng.choice(CB_CODECS), "b": cb_bytes(rng),
         "final": rng.random() < 0.7, "bo": rng.choice([-1, 0, 1]), "table": CB_TABLE,
         "script": [gen_dec_step(rng) for _ in range(rng.randint(1, 6))]}
    if rng.random() < 0.03:
        c["missing"] = True
    return c


BAD_RETURNS = ["x", ("x",), (b"x", 1), ("x", 1, 2)]


def dec_handler(script):
    items = list(script)

    def handler(e):
        if not items:
            raise RuntimeError("done")
        r = items.pop(0)
        if r["t"] == "raise":
            raise ValueError("boom")
        if r["t"] == "bad":
            return BAD_RETURNS[r["form"]]
        obj = r["obj"]
        if obj["k"] == "set":
            e.object = bytes(obj["b"])
        elif obj["k"] == "wrong":
            e.object = "text"
        elif obj["k"] == "del":
            del e.object
        return s_of(r["rep"]), r["pos"] + e.end if r["rel"] else r["pos"]
    return handler


@run("codec_cb_decode")
def run_codec_cb_decode(c):
    import codecs
    import warnings
    codecs.register_error("uo_cb", dec_handler(c["script"]))
    errors = "uo_nonesuch" if c.get("missing") else "uo_cb"
    b, final, name = bytes(c["b"]), c["final"], c["codec"]
    if name == "ascii":
        return cps_of(codecs.ascii_decode(b, errors)[0])
    if name == "charmap":
        return cps_of(codecs.charmap_decode(b, errors, s_of(c["table"]))[0])
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        if name == "utf-8":
            s, n = codecs.utf_8_decode(b, errors, final)
        elif name in ("utf-16", "utf-32"):
            width = 2 if name == "utf-16" else 4
            s, n = getattr(codecs, WIDE_DEC[width, c["bo"]])(b, errors, final)
        elif name == "unicode_escape":
            s, n = codecs.unicode_escape_decode(b, errors, final)
        elif name == "raw_unicode_escape":
            s, n = codecs.raw_unicode_escape_decode(b, errors, final)
        else:
            s, n = codecs.utf_7_decode(b, errors, final)
    return cps_of(s) if final else [cps_of(s), n]


CB_CHARS = [0x41, 0x7a, 0x80, 0xe9, 0xff, 0x100, 0x20ac, 0xd800, 0xdbff, 0xdc80, 0xdcff, 0xdfff, 0x1f600]
CB_ENC_REPS = ["", "?", "xy", "\xe9", "\u20ac", "\ud800"]
CB_ENC_BYTES = [b"", b"x", b"xy", b"xyz", b"wxyz", b"\xff"]
CB_ENC_CODECS = ["ascii", "latin-1", "utf-8", "utf-16", "utf-32", "charmap"]


def gen_enc_step(rng):
    r = rng.random()
    if r < 0.07:
        return {"t": "raise"}
    if r < 0.13:
        return {"t": "bad", "form": rng.randint(0, 2)}
    if r < 0.18:
        return {"t": "badrep", "pos": rng.choice([0, 1, 2 ** 64])}
    pos, rel = cb_pos(rng)
    if rng.random() < 0.65:
        return {"t": "str", "rep": cps_of(rng.choice(CB_ENC_REPS)), "pos": pos, "rel": rel}
    return {"t": "bytes", "rep": list(rng.choice(CB_ENC_BYTES)), "pos": pos, "rel": rel}


@gen("codec", 8)
def gen_codec_cb_encode(rng):
    s = [rng.choice(CB_CHARS) for _ in range(rng.randint(0, 6))]
    if rng.random() < 0.7:
        s.insert(rng.randint(0, len(s)), rng.choice([0xd800, 0xdc80, 0xdfff]))
    c = {"mod": "unicodeobj", "fn": "codec_cb_encode", "codec": rng.choice(CB_ENC_CODECS), "s": s,
         "bo": rng.choice([-1, 0, 1]), "map": {"k": "build", "table": [0x41, 0x7a, 0xe9, 0x20ac]},
         "script": [gen_enc_step(rng) for _ in range(rng.randint(1, 6))]}
    if rng.random() < 0.03:
        c["missing"] = True
    return c


ENC_BAD = ["x", ("x",), ("x", 1, 2)]


def enc_handler(script):
    items = list(script)

    def handler(e):
        if not items:
            raise RuntimeError("done")
        r = items.pop(0)
        if r["t"] == "raise":
            raise ValueError("boom")
        if r["t"] == "bad":
            return ENC_BAD[r["form"]]
        if r["t"] == "badrep":
            return 1, r["pos"]
        w = s_of(r["rep"]) if r["t"] == "str" else bytes(r["rep"])
        return w, r["pos"] + e.end if r["rel"] else r["pos"]
    return handler


@run("codec_cb_encode")
def run_codec_cb_encode(c):
    import codecs
    codecs.register_error("uo_cb", enc_handler(c["script"]))
    errors = "uo_nonesuch" if c.get("missing") else "uo_cb"
    s, name = s_of(c["s"]), c["codec"]
    if name == "charmap":
        return list(codecs.charmap_encode(s, errors, codecs.charmap_build(s_of(c["map"]["table"])))[0])
    if name in ("utf-16", "utf-32"):
        name += {-1: "-le", 0: "", 1: "-be"}[c["bo"]]
    return list(s.encode(name, errors))

# ==== end error handler callbacks ====


# ==== str.format (fn names fmt_strformat, fmt_format_map, fmt_parser, fmt_fieldsplit) ====

SF_NAMES = ["", "", "", "0", "0", "1", "2", "9", "a", "a", "b", "\u0663", "\xb2", "-1", "00", "0.real", "0.imag",
            "0.nope", "1.real", "a.real", ".real", "0[0]", "0[1]", "0[a]", "0[9]", "a[0]", "a[a]", "[0]", "0[]", "0.",
            "0..real", "0[0][0]", "0[0].real", "0[0", "0]", "0[0]x", "0[:]", "0[!]", "0[{]", "9" * 25, "0[" + "9" * 25 + "]"]
SF_CONVS = ["", "", "", "", "!r", "!s", "!a", "!x", "!\x00", "!\x01", "!\xe9", "!", "!rx", "!}"]
SF_SPECS = ["", "", "", ":", ":>5", ":<5", ":^7", ":x", ":d", ":.2f", ":e", ":{}", ":{0}", ":{1}", ":{a}", ":{}>3",
            ":>{}", ":{:{}}", ":{0:{1}}", ":{{}}", ":{", ":}", ":{{", ":\x00", ":{}{}"]
SF_CHARS = list("{}{}[]!:.0a1 ") + ["\xe9", "\U0001f600"]


def sf_string(rng):
    if rng.random() < 0.12:
        return "".join(rng.choice(SF_CHARS) for _ in range(rng.randint(0, 9)))
    out = ""
    for _ in range(rng.randint(0, 3)):
        out += rng.choice(["", "", "x", "{{", "}}", "\xe9", " ", "}", "{"] if rng.random() < 0.3 else ["", "x", " "])
        out += "{" + rng.choice(SF_NAMES) + rng.choice(SF_CONVS) + rng.choice(SF_SPECS) + "}"
    return out + rng.choice(["", "", "x", "{{", "}}"])


def sf_clean(rng, positional=True):
    """A string with coherent numbering and a spec most objects take, so rendering is reached."""
    style = rng.choice(["auto", "manual", "named"]) if positional else "named"
    out = rng.choice(["", "x", "{{"])
    for i in range(rng.randint(1, 3)):
        name = {"auto": "", "manual": str(i), "named": "ab"[i % 2]}[style]
        tail = rng.choice(["", "", ".real", "[0]"]) if rng.random() < 0.2 else ""
        conv = rng.choice(["", "", "!r", "!s", "!a"])
        spec = rng.choice(["", "", ":", ":>5", ":<7", ":^9", ":*^6"])
        out += "{" + name + tail + conv + spec + "}" + rng.choice(["", " ", "}}"])
    return out


SF_INTS = [0, 1, -1, 2, 3, 7, 65, 255, 2 ** 63, -2 ** 63, 10 ** 30, 10 ** 4300]


def sf_obj(rng, depth=0):
    r = rng.random()
    if r < 0.3:
        return {"t": "int", "v": hex_of(rng.choice(SF_INTS))}
    if r < 0.36:
        return {"t": "bool", "v": rng.random() < 0.5}
    if r < 0.46:
        return {"t": "float", "v": format(float_bits(rng.choice(FLOATS)), "x")}
    if r < 0.5:
        return {"t": "complex", "re": format(float_bits(rng.choice(FLOATS)), "x"),
                "im": format(float_bits(rng.choice(FLOATS)), "x")}
    if r < 0.72:
        return {"t": "str", "s": cps_of(rng.choice(["", "a", "abc", "it's", "\xe9t\xe9", "\u20ac", ">5", "x", "d",
                                                   "<", "\U0001f600"]))}
    if r < 0.77:
        return {"t": "none"}
    if depth < 2 and r < 0.84:
        return {"t": "tuple", "items": [sf_obj(rng, depth + 1) for _ in range(rng.randint(0, 2))]}
    if depth < 2 and r < 0.9:
        keys = rng.sample(["a", "b", "0"], rng.randint(0, 2))
        return {"t": "dict", "items": [[cps_of(k), sf_obj(rng, depth + 1)] for k in keys]}
    if depth < 2:
        return sf_user(rng, depth)
    return {"t": "int", "v": hex_of(1)}


def sf_resp(rng, depth, text=True):
    if rng.random() < 0.2:
        return {"k": "raise"}
    if text and rng.random() < 0.8:
        return {"k": "ok", "v": {"t": "str", "s": cps_of(rng.choice(["", "u", ">5", "<u>"]))}}
    return {"k": "ok", "v": sf_obj(rng, depth + 1)}


def sf_user(rng, depth):
    attrs = [[cps_of(n), sf_resp(rng, depth, False)] for n in rng.sample(["real", "imag"], rng.randint(0, 2))]
    return {"t": "user", "fmt": sf_resp(rng, depth), "str": sf_resp(rng, depth), "repr": sf_resp(rng, depth),
            "attrs": attrs, "item": sf_resp(rng, depth, False) if rng.random() < 0.6 else None}


def sf_dec(j):
    t = j["t"]
    if t == "int":
        s = j["v"]
        return -int(s[1:], 16) if s.startswith("-") else int(s, 16)
    if t == "bool":
        return j["v"]
    if t == "float":
        return float_of(j["v"])
    if t == "complex":
        return complex(float_of(j["re"]), float_of(j["im"]))
    if t == "str":
        return s_of(j["s"])
    if t == "none":
        return None
    if t == "tuple":
        return tuple(sf_dec(x) for x in j["items"])
    if t == "dict":
        return {s_of(k): sf_dec(v) for k, v in j["items"]}

    def answer(r):
        if r["k"] == "raise":
            raise ValueError("boom")
        return sf_dec(r["v"])
    attrs = {s_of(k): v for k, v in j["attrs"]}

    class U:
        def __format__(self, spec):
            return answer(j["fmt"])

        def __str__(self):
            return answer(j["str"])

        def __repr__(self):
            return answer(j["repr"])

        def __getattr__(self, name):
            if name in attrs:
                return answer(attrs[name])
            raise AttributeError(f"'U' object has no attribute '{name}'")
    # `%T` prints the module and qualified name: keep them what the model calls the class
    U.__qualname__ = "U"
    U.__module__ = "__main__"
    if j["item"] is not None:
        U.__getitem__ = lambda self, k: answer(j["item"])
    return U()


@gen("format", 9)
def gen_fmt_strformat(rng):
    if rng.random() < 0.55:
        return {"mod": "unicodeobj", "fn": "fmt_strformat", "s": cps_of(sf_clean(rng)),
                "args": [sf_obj(rng) for _ in range(3)],
                "kw": [[cps_of(k), sf_obj(rng)] for k in ["a", "b"]]}
    return {"mod": "unicodeobj", "fn": "fmt_strformat", "s": cps_of(sf_string(rng)),
            "args": [sf_obj(rng) for _ in range(rng.randint(0, 3))],
            "kw": [[cps_of(k), sf_obj(rng)] for k in rng.sample(["a", "b"], rng.randint(0, 2))]}


@gen("format", 3)
def gen_fmt_format_map(rng):
    s = sf_clean(rng, False) if rng.random() < 0.55 else sf_string(rng)
    return {"mod": "unicodeobj", "fn": "fmt_format_map", "s": cps_of(s),
            "map": [sf_resp(rng, 1, False) for _ in range(rng.randint(0, 4))]}


@gen("format", 3)
def gen_fmt_parser(rng):
    return {"mod": "unicodeobj", "fn": "fmt_parser", "s": cps_of(sf_string(rng)), "bad": rng.random() < 0.03}


@gen("format", 2)
def gen_fmt_fieldsplit(rng):
    name = rng.choice(SF_NAMES) if rng.random() < 0.7 else "".join(rng.choice(list("0a.[]x")) for _ in range(rng.randint(0, 6)))
    return {"mod": "unicodeobj", "fn": "fmt_fieldsplit", "s": cps_of(name), "bad": rng.random() < 0.03}


@run("fmt_strformat")
def run_fmt_strformat(c):
    return cps_of(s_of(c["s"]).format(*[sf_dec(a) for a in c["args"]],
                                      **{s_of(k): sf_dec(v) for k, v in c["kw"]}))


@run("fmt_format_map")
def run_fmt_format_map(c):
    items = list(c["map"])

    class M:
        def __getitem__(self, key):
            if not items:
                raise KeyError(key)
            r = items.pop(0)
            if r["k"] == "raise":
                raise ValueError("boom")
            return sf_dec(r["v"])
    return cps_of(s_of(c["s"]).format_map(M()))


@run("fmt_parser")
def run_fmt_parser(c):
    import _string
    arg = 1 if c["bad"] else s_of(c["s"])
    return [[cps_of(a), None if b is None else cps_of(b), None if s is None else cps_of(s),
             None if k is None else cps_of(k)] for a, b, s, k in _string.formatter_parser(arg)]


def idx_str(v):
    return {"i": v} if isinstance(v, int) else {"s": cps_of(v)}


@run("fmt_fieldsplit")
def run_fmt_fieldsplit(c):
    import _string
    first, rest = _string.formatter_field_name_split(1 if c["bad"] else s_of(c["s"]))
    return [idx_str(first), [[b, idx_str(v)] for b, v in rest]]


# ==== PyUnicodeWriter (fn name fmt_writer) ====

WR_BYTES = [b"", b"a", b"abc", b"\xc3\xa9", b"\xe2\x82\xac", b"\xf0\x9f\x98\x80", b"\xff", b"a\xff",
            b"\xe2\x82\xac\xff", b"\xc3\xa9\xff", b"\xf0\x9f\x98\x80\xc0", b"\xe2\x82", b"\xed\xa0\x80",
            b"a\x00\xc3\xa9", b"\xc3\xa9\xe2\x82", b"\xed\xa0\x80\xff", b"\xe2\x82\xac\xf0\x9f"]
WR_STRS = ["", "a", "abc", "\xe9", "€", "\U0001f600", "a\xe9", "a€", "\xe9€\U0001f600",
           "\ud800", "a\x00b"]
WR_HANDLERS = ["strict", "strict", "ignore", "replace", "surrogateescape", "backslashreplace",
               "surrogatepass", "xmlcharrefreplace", "namereplace"]


def wr_size(rng, n):
    return rng.choice([-1, n, n, rng.randint(0, n)])


def wop_bytes(rng, key):
    b = rng.choice(WR_BYTES)
    return {"op": key, "s": list(b), "n": wr_size(rng, len(b))}


def gen_wop(rng):
    r = rng.random()
    if r < 0.14:
        return {"op": "char", "c": rng.choice([0, 97, 127, 128, 255, 256, 0x20ac, 0xffff, 0x10000, 0x10ffff,
                                               0x110000, 0xffffffff])}
    if r < 0.26:
        o = {"t": "str", "s": cps_of(rng.choice(WR_STRS))} if rng.random() < 0.6 else sf_obj(rng, 1)
        return {"op": "str", "o": o}
    if r < 0.34:
        return {"op": "repr", "o": sf_obj(rng, 1)} if rng.random() < 0.9 else {"op": "reprnull"}
    if r < 0.4:
        s = rng.choice(["", "x", "ascii", "a\x00b"])
        return {"op": "ascii", "s": cps_of(s), "n": wr_size(rng, len(s))}
    if r < 0.47:
        s = rng.choice(WR_STRS)
        return {"op": "ucs4", "s": cps_of(s), "n": rng.choice([-1, len(s), rng.randint(0, len(s))])}
    if r < 0.54:
        s = cps_of(rng.choice(WR_STRS)) + rng.choice([[], [], [0x110000], [0xffffffff], [65, 0x110000]])
        return {"op": "wide", "s": s, "n": wr_size(rng, len(s))}
    if r < 0.68:
        s = rng.choice(WR_STRS)
        o = {"t": "str", "s": cps_of(s)} if rng.random() < 0.9 else rng.choice([
            {"t": "int", "v": hex_of(1)}, {"t": "none"}])
        if rng.random() < 0.7:
            a = rng.randint(0, len(s))
            return {"op": "sub", "o": o, "a": a, "b": rng.randint(a, len(s))}
        return {"op": "sub", "o": o, "a": rng.randint(-1, len(s) + 1), "b": rng.randint(-1, len(s) + 1)}
    if r < 0.84:
        return wop_bytes(rng, "utf8")
    op = wop_bytes(rng, "decode")
    op["h"] = rng.choice(WR_HANDLERS)
    op["consumed"] = rng.random() < 0.5
    return op


@gen("format", 6)
def gen_fmt_writer(rng):
    n = rng.choice([0, 0, 0, 1, 16, -1])
    ops = [gen_wop(rng) for _ in range(rng.randint(0, 5))]
    if rng.random() < 0.3:
        # The shape of a rollback: something short, a decode failing after wide characters, and
        # at times more text, so that the kind of the result is decided by the failure.
        first = rng.choice([[], [{"op": "char", "c": 97}], [{"op": "ascii", "s": cps_of("ab"), "n": 2}]])
        fail = {"op": "utf8", "s": list(rng.choice([b"\xc3\xa9\xff", b"\xe2\x82\xac\xff",
                                                    b"\xf0\x9f\x98\x80\xff"])), "n": -1}
        rest = rng.choice([[], [{"op": "char", "c": 98}], [{"op": "ascii", "s": cps_of("cd"), "n": -1}]])
        ops = first + [fail] + rest
    return {"mod": "unicodeobj", "fn": "fmt_writer", "n": n, "ops": ops}


def writer_api():
    import ctypes
    api = ctypes.pythonapi
    P, O, N = ctypes.c_void_p, ctypes.py_object, ctypes.c_ssize_t
    for name, args in [("WriteChar", [P, ctypes.c_uint32]), ("WriteStr", [P, O]), ("WriteRepr", [P, O]),
                       ("WriteASCII", [P, ctypes.c_char_p, N]), ("WriteSubstring", [P, O, N, N]),
                       ("WriteUTF8", [P, ctypes.c_char_p, N]), ("WriteUCS4", [P, P, N]),
                       ("WriteWideChar", [P, P, N]),
                       ("DecodeUTF8Stateful", [P, ctypes.c_char_p, N, ctypes.c_char_p, P])]:
        f = getattr(api, "PyUnicodeWriter_" + name)
        f.restype, f.argtypes = ctypes.c_int, args
    api.PyUnicodeWriter_Create.restype, api.PyUnicodeWriter_Create.argtypes = P, [N]
    api.PyUnicodeWriter_Finish.restype, api.PyUnicodeWriter_Finish.argtypes = O, [P]
    null = ctypes.PYFUNCTYPE(ctypes.c_int, P, P)(("PyUnicodeWriter_WriteRepr", api))
    return api, null


def writer_step(api, null, w, op, consumed):
    import ctypes
    k = op["op"]
    if k == "char":
        api.PyUnicodeWriter_WriteChar(w, op["c"])
    elif k == "str":
        api.PyUnicodeWriter_WriteStr(w, sf_dec(op["o"]))
    elif k == "repr":
        api.PyUnicodeWriter_WriteRepr(w, sf_dec(op["o"]))
    elif k == "reprnull":
        null(w, None)
    elif k == "ascii":
        api.PyUnicodeWriter_WriteASCII(w, bytes(op["s"]), op["n"])
    elif k in ("ucs4", "wide"):
        a = (ctypes.c_uint32 * (len(op["s"]) + 1))(*op["s"], 0)
        f = api.PyUnicodeWriter_WriteUCS4 if k == "ucs4" else api.PyUnicodeWriter_WriteWideChar
        f(w, a, op["n"])
    elif k == "sub":
        api.PyUnicodeWriter_WriteSubstring(w, sf_dec(op["o"]), op["a"], op["b"])
    elif k == "utf8":
        api.PyUnicodeWriter_WriteUTF8(w, bytes(op["s"]), op["n"])
    else:
        ref = ctypes.byref(consumed) if op["consumed"] else None
        api.PyUnicodeWriter_DecodeUTF8Stateful(w, bytes(op["s"]), op["n"], op["h"].encode(), ref)


@run("fmt_writer")
def run_fmt_writer(c):
    import ctypes
    api, null = writer_api()
    w = api.PyUnicodeWriter_Create(c["n"])
    trace = []
    for op in c["ops"]:
        consumed = ctypes.c_ssize_t(77 if op.get("consumed") else 0)
        t = common.py_result(lambda: writer_step(api, null, w, op, consumed))
        trace.append([{"ok": None} if "ok" in t else t, consumed.value])
    r = api.PyUnicodeWriter_Finish(w)
    return [trace, cps_of(r), kind_of(r)]

# ==== PyUnicode_FromFormat (fn names fmt_fromformat, fmt_writerformat) ====

FF_INTS = [0, 1, -1, 7, 123, -123, 255, 2 ** 31 - 1, -2 ** 31, 2 ** 31, 2 ** 32 - 1, 2 ** 32, 2 ** 63 - 1,
           -2 ** 63, 2 ** 63, 2 ** 64 - 1]
FF_CT = {"": "int", "l": "long", "ll": "longlong", "z": "ssize", "t": "ssize", "j": "longlong"}
FF_CSTR = [b"", b"a", b"abc", b"abcdefgh", b"\xc3\xa9", b"a\xc3\xa9b", b"\xe2\x82\xac", b"ab\xe2\x82\xac", b"ab\xe2\x82",
           b"\xf0\x9f\x98\x80", b"a\xf0\x9f\x98", b"\xff", b"a\xffb", b"\xc0\x80", b"a\x00b", b"\xed\xa0\x80"]
FF_STRS = ["", "a", "abc", "abcdefgh", "\xe9", "a\xe9b", "€", "ab€", "\U0001f600", "a\U0001f600", "\ud800"]
FF_WIDE = [[], [97], [97, 98, 99], [233], [0x20ac], [97, 0x1f600], [97, 0, 98], [0x110000], [97, 0xffffffff]]
FF_STATIC = ["int", "str", "NoneType", "tuple", "types.GenericAlias"]
FF_HEAP = [("mod", "Q"), ("mod", "A.B"), ("a.b", "Q"), ("builtins", "Q"), ("__main__", "Q"), (None, "Q"),
           ("collections", "deque")]


def ff_tname(rng):
    if rng.random() < 0.4:
        return {"k": "static", "s": cps_of(rng.choice(FF_STATIC))}
    m, q = rng.choice(FF_HEAP)
    return {"k": "heap", "m": None if m is None else cps_of(m), "q": cps_of(q)}


def ff_builtin_obj(rng):
    return rng.choice([{"t": "int", "v": hex_of(1)}, {"t": "none"}, {"t": "str", "s": cps_of("x")},
                       {"t": "tuple", "items": []}])


def ff_directive(rng):
    """A conversion specification and its arguments, in the order va_arg takes them."""
    args = []
    flags = "".join(rng.choice("-0#") for _ in range(rng.choice([0, 0, 0, 1, 1, 2, 3])))
    r = rng.random()
    width = ""
    if r < 0.3:
        width = str(rng.choice([0, 1, 2, 5, 12]))
    elif r < 0.45:
        width = "*"
        args.append({"t": "int", "c": "int", "v": rng.choice([0, 1, 5, 12, -1, -5])})
    r = rng.random()
    prec, starneg = "", False
    if r < 0.25:
        prec = "." + str(rng.choice([0, 1, 2, 3, 7]))
    elif r < 0.32:
        prec = "."
    elif r < 0.5:
        prec = ".*"
        v = rng.choice([0, 1, 2, 3, 7, -1, -3])
        starneg = v < 0
        args.append({"t": "int", "c": "int", "v": v})
    conv = rng.choice("ddiouxXcpsssUVVSRATNq")
    if conv in "diouxX":
        mod = rng.choice(["", "", "l", "ll", "z", "t", "j"])
        args.append({"t": "int", "c": FF_CT[mod], "v": rng.choice(FF_INTS)})
    elif conv == "c":
        mod = rng.choice(["", "", "", "l"])
        args.append({"t": "int", "c": "int", "v": rng.choice([0, 97, 233, 0x20ac, 0x1f600, 0x10ffff, 0x110000, -1])})
    elif conv == "p":
        mod = rng.choice(["", "", "", "l"])
        args.append({"t": "ptr", "v": rng.choice([0, 1, 255, 0x7fff0000])})
    elif conv == "s":
        mod = rng.choice(["", "", "", "l", "ll"])
        if mod == "l":
            args.append({"t": "wstr", "s": rng.choice(FF_WIDE)})
        else:
            args.append({"t": "cstr", "s": list(rng.choice(FF_CSTR))})
    elif conv == "V":
        mod = rng.choice(["", "", "l"])
        if starneg or rng.random() < 0.5:
            args.append({"t": "null"})
        else:
            args.append({"t": "obj", "o": {"t": "str", "s": cps_of(rng.choice(FF_STRS))}})
        if mod == "l":
            args.append({"t": "wstr", "s": rng.choice(FF_WIDE)})
        else:
            args.append({"t": "cstr", "s": list(rng.choice(FF_CSTR))})
    else:
        mod = rng.choice(["", "", "", "", "", "l"])
        if starneg and conv != "q":
            # This is the undefined behaviour: see the record of the precision. Not run here.
            prec = ".0"
            args = [a for a in args[:-1]] if prec and args and args[-1]["v"] < 0 else args
        if conv == "U":
            args.append({"t": "obj", "o": {"t": "str", "s": cps_of(rng.choice(FF_STRS))}})
        elif conv in "SRA":
            args.append({"t": "obj", "o": sf_obj(rng, 1)})
        elif conv == "T":
            args.append({"t": "inst", "n": ff_tname(rng)} if rng.random() < 0.6
                        else {"t": "obj", "o": ff_builtin_obj(rng)})
        elif conv == "N":
            args.append({"t": "type", "n": ff_tname(rng)} if rng.random() < 0.85
                        else {"t": "obj", "o": ff_builtin_obj(rng)})
    return "%" + flags + width + prec + mod + conv, args


def ff_format(rng):
    fmt, args = "", []
    for _ in range(rng.randint(0, 4)):
        r = rng.random()
        if r < 0.3:
            fmt += rng.choice(["a", "abc", " ", "x y"])
        elif r < 0.4:
            fmt += "%%"
        else:
            d, a = ff_directive(rng)
            fmt += d
            args += a
    return fmt, args


@gen("format", 8)
def gen_fmt_fromformat(rng):
    fmt, args = ff_format(rng)
    b = list(fmt.encode())
    r = rng.random()
    if r < 0.02:
        b.append(rng.choice([0xe9, 0x80, 0xff]))
    elif r < 0.04:
        b += [37]
    return {"mod": "unicodeobj", "fn": "fmt_fromformat", "fmt": b, "args": args}


@gen("format", 3)
def gen_fmt_writerformat(rng):
    fmt, args = ff_format(rng)
    if rng.random() < 0.3:
        # A failure after wide characters: gh-158439, by way of Format.
        fmt = rng.choice(["%c%c", "%s%c", "x%c%c"])
        args = [{"t": "int", "c": "int", "v": 0x20ac}] if fmt[-3:] == "c%c" else [
            {"t": "cstr", "s": list(b"\xe2\x82\xac")}]
        args = args + [{"t": "int", "c": "int", "v": 0x110000}]
    pre = [gen_wop(rng) for _ in range(rng.randint(0, 2))]
    post = [gen_wop(rng) for _ in range(rng.randint(0, 2))]
    return {"mod": "unicodeobj", "fn": "fmt_writerformat", "pre": pre, "post": post, "fmt": list(fmt.encode()),
            "args": args}


def str_of(cps):
    return "".join(map(chr, cps))


def ff_type(n):
    if n["k"] == "static":
        import types
        return {"int": int, "str": str, "NoneType": type(None), "tuple": tuple,
                "types.GenericAlias": types.GenericAlias}[str_of(n["s"])]
    if str_of(n["q"]) == "deque":
        import collections
        return collections.deque  # a heap type, with a dotted name
    cls = type("Heap", (), {})
    cls.__qualname__ = str_of(n["q"])
    cls.__module__ = 1 if n["m"] is None else str_of(n["m"])
    return cls


def ff_args(args, keep):
    import ctypes
    ct = {"int": ctypes.c_int, "long": ctypes.c_long, "longlong": ctypes.c_longlong, "ssize": ctypes.c_ssize_t}
    out = []
    for a in args:
        t = a["t"]
        if t == "int":
            out.append(ct[a["c"]](a["v"]))
        elif t == "obj":
            o = sf_dec(a["o"])
            keep.append(o)
            out.append(ctypes.py_object(o))
        elif t == "null":
            out.append(ctypes.c_void_p(None))
        elif t == "cstr":
            b = ctypes.create_string_buffer(bytes(a["s"]))
            keep.append(b)
            out.append(ctypes.cast(b, ctypes.c_void_p))
        elif t == "wstr":
            b = (ctypes.c_uint32 * (len(a["s"]) + 1))(*a["s"], 0)
            keep.append(b)
            out.append(ctypes.cast(b, ctypes.c_void_p))
        elif t == "ptr":
            out.append(ctypes.c_void_p(a["v"]))
        else:
            o = ff_type(a["n"])
            if t != "type":
                import types
                o = types.GenericAlias(list, int) if o is types.GenericAlias else o()
            keep.append(o)
            out.append(ctypes.py_object(o))
    return out


@run("fmt_fromformat")
def run_fmt_fromformat(c):
    import ctypes
    f = ctypes.pythonapi.PyUnicode_FromFormat
    f.restype, f.argtypes = ctypes.py_object, [ctypes.c_char_p]
    keep = []
    r = f(bytes(c["fmt"]), *ff_args(c["args"], keep))
    return [cps_of(r), kind_of(r)]


@run("fmt_writerformat")
def run_fmt_writerformat(c):
    import ctypes
    api, null = writer_api()
    f = api.PyUnicodeWriter_Format
    f.restype, f.argtypes = ctypes.c_int, [ctypes.c_void_p, ctypes.c_char_p]
    w = api.PyUnicodeWriter_Create(0)

    def ops(lst):
        for op in lst:
            consumed = ctypes.c_ssize_t(77)
            common.py_result(lambda: writer_step(api, null, w, op, consumed))

    ops(c["pre"])
    keep = []
    res = common.py_result(lambda: f(w, bytes(c["fmt"]), *ff_args(c["args"], keep)))
    ops(c["post"])
    r = api.PyUnicodeWriter_Finish(w)
    return [{"ok": None} if "ok" in res else res, cps_of(r), kind_of(r)]

# ==== str iterators (fn name fmt_iter) ====

IT_STRS = ["", "a", "ab", "abc", "abcdef", "\xe9", "a\xe9", "\xe9\xff", "€", "a€b", "\U0001f600", "a\U0001f600",
           "\ud800", "\x00", "a\x00b"]
IT_STATES = [0, 1, 2, 3, 5, 100, -1, -5, 2 ** 63 - 1, -2 ** 63, 2 ** 63, -2 ** 63 - 1, 2 ** 70]


def it_state(rng):
    r = rng.random()
    if r < 0.7:
        return {"t": "int", "v": hex_of(rng.choice(IT_STATES))}
    if r < 0.85:
        return {"t": "bool", "v": rng.random() < 0.5}
    return sf_obj(rng, 1)


def it_simple(rng):
    return {"op": "next"} if rng.random() < 0.8 else {
        "op": "setstate", "o": {"t": "int", "v": hex_of(rng.choice([0, 1, 2, 100, -1]))}}


def it_op(rng):
    r = rng.random()
    if r < 0.45:
        return {"op": "next"}
    if r < 0.6:
        return {"op": "len"}
    if r < 0.75:
        return {"op": "setstate", "o": it_state(rng)}
    return {"op": "reduce", "pre": [it_simple(rng) for _ in range(rng.choice([0, 0, 1, 2, 8]))],
            "r": rng.choice(["orig", "orig", "alt", "missing", "raise"])}


@gen("format", 4)
def gen_fmt_iter(rng):
    return {"mod": "unicodeobj", "fn": "fmt_iter", "s": cps_of(rng.choice(IT_STRS)), "exact": rng.random() < 0.8,
            "ops": [it_op(rng) for _ in range(rng.randint(0, 9))]}


class ItSub(str):
    pass


def it_step(it, op):
    if op["op"] == "next":
        next(it, None)
    else:
        try:
            it.__setstate__(sf_dec(op["o"]))
        except Exception:
            pass


def it_reduce(it, op):
    """__reduce__ from a frame whose builtins run the script when `iter` is looked up."""
    alt = lambda *a: None

    class Builtins(dict):
        def __getitem__(self, key):
            for s in op["pre"]:
                it_step(it, s)
            if op["r"] == "raise":
                raise ValueError("hook")
            if op["r"] == "missing":
                raise KeyError(key)
            return iter if op["r"] == "orig" else alt

    glob = {"__builtins__": Builtins(), "it": it}
    exec("r = it.__reduce__()", glob)
    r = glob["r"]
    label = 0 if r[0] is iter else 1 if r[0] is alt else -1
    return [label, cps_of(r[1][0]), r[2] if len(r) > 2 else None]


def it_run(it, op):
    k = op["op"]
    if k == "next":
        x = next(it, None)
        return None if x is None else [cps_of(x), kind_of(x)]
    if k == "len":
        return it.__length_hint__()
    if k == "setstate":
        return common.py_result(lambda: (it.__setstate__(sf_dec(op["o"])), None)[1])
    return common.py_result(lambda: it_reduce(it, op))


@gen("format", 1)
def gen_fmt_unicode_char(rng):
    ch = rng.choice([0, 65, 127, 128, 255, 256, 0x20ac, 0xd800, 0xffff, 0x10000, 0x10ffff, 0x110000, 0x110001,
                     0x7fffffff, 0x80000000, 0xffffffff, rng.randrange(0x110000), rng.randrange(0x110000, 2 ** 32)])
    return {"mod": "unicodeobj", "fn": "fmt_unicode_char", "ch": ch}


@run("fmt_unicode_char")
def run_fmt_unicode_char(c):
    import ctypes
    f = ctypes.pythonapi.PyUnicode_FromKindAndData
    f.restype = ctypes.py_object
    f.argtypes = [ctypes.c_int, ctypes.c_void_p, ctypes.c_ssize_t]
    buf = ctypes.c_uint32(c["ch"])
    r = f(4, ctypes.addressof(buf), 1)
    k = kind_of(r)
    return [cps_of(r), k[0], k[1]]


@run("fmt_iter")
def run_fmt_iter(c):
    s = str_of(c["s"])
    it = iter(s if c["exact"] else ItSub(s))
    return [type(it).__name__, [it_run(it, op) for op in c["ops"]]]

# ==== interning (fn name fmt_intern) ====

KN_STATICS = ["__init__", "__name__", "__dict__"]
KN_SUFFIX = ["", "", "\xe9", "€", "\U0001f600"]
KN_WIDE_USED = set()


def kn_wide(rng):
    """One wide character no case of this run has used: it cannot carry a token."""
    while True:
        c = rng.randrange(0x10000, 0x110000)
        if c not in KN_WIDE_USED:
            KN_WIDE_USED.add(c)
            return chr(c)



@gen("format", 4)
def gen_fmt_intern(rng):
    # The interned dict outlives a case and immortal strings never leave it, so a case uses its own
    # text. Handles are in the order the operations make them.
    token = "k" + format(rng.getrandbits(64), "x")
    texts = [token + rng.choice(KN_SUFFIX) for _ in range(2)] + [token]
    texts += ["€" + token[1:], rng.choice(KN_STATICS), rng.choice(["", "a", "\xe9", "\xff"])]
    wide1 = kn_wide(rng)
    ops, n = [], 0
    for _ in range(rng.randint(1, 10)):
        r = rng.random()
        if n == 0 or r < 0.35:
            ops.append({"op": "new", "s": cps_of(rng.choice(texts))})
        elif r < 0.42:
            ops.append({"op": "new", "s": cps_of(wide1)})
        elif r < 0.5:
            ops.append({"op": "sub", "s": cps_of(rng.choice(texts))})
        elif r < 0.54:
            ops.append({"op": "other"})
        elif r < 0.76:
            ops.append({"op": "mortal", "h": rng.randrange(n)})
        elif r < 0.9:
            ops.append({"op": "immortal", "h": rng.randrange(n)})
        else:
            b = rng.choice([rng.choice(texts).encode("utf-8", "surrogatepass"), b"a", b"", b"\xff", token.encode() + b"\xc3"])
            ops.append({"op": "fromstring", "s": list(b)})
            if b in (b"\xff",) or b.endswith(b"\xc3"):
                n -= 1
        n += 1
    return {"mod": "unicodeobj", "fn": "fmt_intern", "statics": [cps_of(s) for s in KN_STATICS], "ops": ops}


class KnSub(str):
    pass


class KnOther:
    pass


def kn_new(s):
    # A fresh object: join makes one unless there is a singleton.
    return "".join(list(s)) if len(s) != 1 else chr(ord(s))


def kn_inplace(fn, x):
    import ctypes
    api = ctypes.pythonapi
    p = ctypes.py_object(x)
    api.Py_IncRef.argtypes = [ctypes.py_object]
    api.Py_IncRef.restype = None
    api.Py_IncRef(x)  # the call steals one reference; what it leaves in p is never released
    f = getattr(api, fn)
    f.argtypes, f.restype = [ctypes.POINTER(ctypes.py_object)], None
    f(ctypes.byref(p))
    return p.value


@run("fmt_intern")
def run_fmt_intern(c):
    import ctypes
    api = ctypes.pythonapi
    api.PyUnicode_InternFromString.restype = ctypes.py_object
    api.PyUnicode_InternFromString.argtypes = [ctypes.c_char_p]
    hs, rs = [], []
    for op in c["ops"]:
        k = op["op"]
        if k == "new":
            hs.append(kn_new(str_of(op["s"])))
        elif k == "sub":
            hs.append(KnSub(str_of(op["s"])))
        elif k == "other":
            hs.append(KnOther())
        elif k == "mortal":
            hs.append(kn_inplace("PyUnicode_InternInPlace", hs[op["h"]]))
        elif k == "immortal":
            hs.append(kn_inplace("PyUnicode_InternImmortal", hs[op["h"]]))
        else:
            r = common.py_result(lambda: api.PyUnicode_InternFromString(bytes(op["s"])))
            if "ok" in r:
                hs.append(r["ok"])
                rs.append({"ok": None})
            else:
                rs.append(r)
            continue
        rs.append({"ok": None})
    import sys

    def is_interned(x):
        return sys._is_interned(x) if type(x) is str or isinstance(x, str) else False

    def show(x):
        first = next(i for i, y in enumerate(hs) if y is x)
        return [first, is_interned(x), sys._is_immortal(x)]

    return [rs, [show(x) for x in hs]]

# ==== join (fn name fmt_join) ====

JN_STRS = ["", "", "a", "abc", "\xe9", "a\xff", "€", "a€", "\U0001f600", "x\U0001f600y", "\ud800"]
# Type names for `%.80s`, which cuts UTF-8 bytes: 41 'é' (82 bytes), and a cut inside a character.
JN_NAMES = ["int", "Thing", "T" * 100, "\xe9" * 41, "a" + "\xe9" * 40, "\u4e2d" * 27, "ab" + "\U00010000" * 20]


def jn_item(rng, other=0.08):
    r = rng.random()
    if r < other:
        return {"t": "other", "n": rng.choice(JN_NAMES)}
    s = cps_of(rng.choice(JN_STRS))
    return {"t": "sub" if rng.random() < 0.15 else "exact", "s": s}


@gen("format", 4)
def gen_fmt_join(rng):
    r = rng.random()
    sep = {"t": "null"} if r < 0.1 else {"t": "other", "n": rng.choice(["int", "T" * 100] + JN_NAMES[3:])} if r < 0.16 else \
        {"t": "str", "s": cps_of(rng.choice(JN_STRS + [" ", ", "]))}
    n = rng.choice([0, 1, 1, 2, 2, 3, 4, 6])
    bad = rng.choice([0, 0.08, 0.3])
    r = rng.random()
    if r < 0.55:
        seq = {"t": "array", "kind": rng.choice(["list", "tuple"]), "items": [jn_item(rng, bad) for _ in range(n)]}
    elif r < 0.9:
        steps = [jn_item(rng, bad) for _ in range(n)]
        if rng.random() < 0.4:
            steps.insert(rng.randint(0, n), {"exc": rng.choice(["ValueError", "TypeError"])})
        seq = {"t": "iter", "steps": steps}
    else:
        seq = {"t": "getiter", "exc": rng.choice(["ValueError", "TypeError"])}
    return {"mod": "unicodeobj", "fn": "fmt_join", "sep": sep, "seq": seq}


class JnSub(str):
    pass


def jn_obj(x):
    if x["t"] == "exact":
        return kn_new(str_of(x["s"]))
    if x["t"] == "sub":
        return JnSub(str_of(x["s"]))
    return 1 if x["n"] == "int" else type(x["n"], (), {})()


def jn_exc(name):
    return (TypeError if name == "TypeError" else ValueError)("boom")


def jn_seq(q):
    if q["t"] == "array":
        items = [jn_obj(x) for x in q["items"]]
        return (items if q["kind"] == "list" else tuple(items)), items
    if q["t"] == "iter":
        got = []

        def walk():
            for s in q["steps"]:
                if "exc" in s:
                    raise jn_exc(s["exc"])
                got.append(jn_obj(s))
                yield got[-1]
        return walk(), got

    class NoIter:
        def __iter__(self):
            raise jn_exc(q["exc"])
    return NoIter(), None


@run("fmt_join")
def run_fmt_join(c):
    import ctypes
    api = ctypes.pythonapi
    f = api.PyUnicode_Join
    f.restype, f.argtypes = ctypes.py_object, [ctypes.c_void_p, ctypes.py_object]
    q = c["sep"]
    sep = None if q["t"] == "null" else (str_of(q["s"]) if q["t"] == "str" else jn_obj(q))
    seq, items = jn_seq(c["seq"])
    r = f(None if sep is None else id(sep), seq)
    if items is not None and len(items) == 1 and r is items[0]:
        return "itself"
    return [cps_of(r), kind_of(r)]

# ==== UTF-8 through the C entry points, with any handler (codec_utf8_obj, codec_utf8_writer) ====

U8OBJ_BYTES = [0x41, 0x80, 0xa0, 0xbf, 0xc2, 0xc3, 0xc4, 0xdf, 0xe0, 0xe2, 0xed, 0xef, 0xf0, 0xf1, 0xf4, 0xf5, 0xff, 0x82, 0x90]
U8_VALID = ["a", "abc", "\xe9", "\xff", "Ā", "€", "￿", "\U00010000", "\U0001f600", "\U0010ffff"]


def u8_input(rng):
    r = rng.random()
    if r < 0.35:
        return list("".join(rng.choice(U8_VALID) for _ in range(rng.randint(0, 4))).encode())
    if r < 0.5:
        b = "".join(rng.choice(U8_VALID) for _ in range(rng.randint(1, 4))).encode()
        return list(b[:rng.randint(0, len(b))])
    return [rng.choice(U8OBJ_BYTES) for _ in range(rng.randint(0, 7))]


def u8_handler(rng, c):
    r = rng.random()
    if r < 0.45:
        c["handler"] = rng.choice(["ignore", "replace", "surrogateescape", "backslashreplace", "surrogatepass",
                                   "strict", "xmlcharrefreplace", "namereplace"])
    elif r < 0.5:
        c["missing"] = "uo_nonesuch"
    else:
        c["script"] = [gen_dec_step(rng) for _ in range(rng.randint(0, 3))]


@gen("codec", 5)
def gen_codec_utf8_obj(rng):
    c = {"mod": "unicodeobj", "fn": "codec_utf8_obj", "b": u8_input(rng), "consumed": rng.random() < 0.5}
    if rng.random() < 0.4:
        c["null"] = True
    else:
        u8_handler(rng, c)
    return c


@gen("codec", 4)
def gen_codec_utf8_writer(rng):
    c = {"mod": "unicodeobj", "fn": "codec_utf8_writer", "b": u8_input(rng), "consumed": rng.random() < 0.5,
         "pre": cps_of(rng.choice(["", "", "a", "ab", "\xe9", "€", "\U0001f600"]))}
    u8_handler(rng, c)
    return c


def u8_errors(c):
    import codecs
    if "script" in c:
        codecs.register_error("uo_cb8", dec_handler(c["script"]))
        return b"uo_cb8"
    return (c.get("handler") or c.get("missing") or "strict").encode()


@run("codec_utf8_obj")
def run_codec_utf8_obj(c):
    import ctypes
    f = ctypes.pythonapi.PyUnicode_DecodeUTF8Stateful
    f.restype = ctypes.py_object
    f.argtypes = [ctypes.c_char_p, ctypes.c_ssize_t, ctypes.c_char_p, ctypes.c_void_p]
    n = ctypes.c_ssize_t(0)
    b = bytes(c["b"])
    r = f(b, len(b), None if c.get("null") else u8_errors(c), ctypes.addressof(n) if c["consumed"] else None)
    k = kind_of(r)
    return [cps_of(r), k[0], k[1], n.value]


@run("codec_utf8_writer")
def run_codec_utf8_writer(c):
    import ctypes
    api = ctypes.pythonapi
    writer_api()
    f = api.PyUnicodeWriter_DecodeUTF8Stateful
    w = api.PyUnicodeWriter_Create(0)
    pre = str_of(c["pre"])
    if pre:
        api.PyUnicodeWriter_WriteStr(w, pre)
    n = ctypes.c_ssize_t(77 if c["consumed"] else 0)
    b = bytes(c["b"])
    errors = u8_errors(c)
    res = common.py_result(lambda: f(w, b, len(b), errors, ctypes.addressof(n) if c["consumed"] else None))
    r = api.PyUnicodeWriter_Finish(w)
    k = kind_of(r)
    return [{"ok": None} if "ok" in res else res, n.value, cps_of(r), k[0], k[1]]


ESC_PIECES = [b"a", b"abc", b"\\n", b"\\\\", b"\\'", b'\\"', b"\\\n", b"\\a", b"\\b", b"\\f", b"\\t", b"\\r", b"\\v",
              b"\\x41", b"\\xe9", b"\\u20ac", b"\\U0001f600", b"\\101", b"\\0", b"\\12", b"\\377", b"\\400", b"\\777", b"\\4001",
              b"\\q", b"\\8", b"\\9", b"\\ ", b"\\Z", b"\\\xff", b"\\\x80", b"\xff", b"\\", b"\\x", b"\\x4", b"\\xg", b"\\u12",
              b"\\u12g", b"\\U0011", b"\\U00110000", b"\\Uffffffff", b"\\N", b"\\Nq", b"\\N{", b"\\N{}", b"\\N{NOPE}", b"\\N{NOPE"]


def esc_input(rng):
    return list(b"".join(rng.choice(ESC_PIECES) for _ in range(rng.randint(0, 4))))


@gen("codec", 4)
def gen_codec_esc_warn(rng):
    c = {"mod": "unicodeobj", "fn": "codec_esc_warn", "b": esc_input(rng), "final": rng.random() < 0.7,
         "warn": rng.random() < 0.6}
    u8_handler(rng, c)
    return c


@run("codec_esc_warn")
def run_codec_esc_warn(c):
    import codecs
    import warnings
    with warnings.catch_warnings():
        warnings.simplefilter("error" if c["warn"] else "ignore", DeprecationWarning)
        s, n = codecs.unicode_escape_decode(bytes(c["b"]), u8_errors(c).decode(), c["final"])
    return [cps_of(s), n]


@gen("codec", 3)
def gen_codec_esc_internal(rng):
    c = {"mod": "unicodeobj", "fn": "codec_esc_internal", "b": esc_input(rng), "final": rng.random() < 0.7}
    u8_handler(rng, c)
    return c


@run("codec_esc_internal")
def run_codec_esc_internal(c):
    import ctypes
    f = ctypes.pythonapi._PyUnicode_DecodeUnicodeEscapeInternal2
    f.restype = ctypes.py_object
    f.argtypes = [ctypes.c_void_p, ctypes.c_ssize_t, ctypes.c_char_p, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p]
    b = bytes(c["b"])
    buf = ctypes.create_string_buffer(b, len(b) + 1)
    n = ctypes.c_ssize_t(len(b))
    first = ctypes.c_int(7)
    ptr = ctypes.c_void_p(1)
    r = f(ctypes.addressof(buf), len(b), u8_errors(c), None if c["final"] else ctypes.addressof(n),
          ctypes.addressof(first), ctypes.addressof(ptr))
    return [cps_of(r), 0 if c["final"] else n.value, first.value,
            None if ptr.value is None else ptr.value - ctypes.addressof(buf)]


CHUNK_ALPHA = {
    "utf-8": [0x41, 0x80, 0x90, 0x9f, 0xa0, 0xbf, 0xc0, 0xc2, 0xdf, 0xe0, 0xe1, 0xed, 0xef, 0xf0, 0xf1, 0xf4, 0xf5, 0xff],
    "utf-16-le": [0x00, 0x41, 0xd7, 0xd8, 0xdb, 0xdc, 0xdf, 0xe0, 0xff],
    "utf-16-be": [0x00, 0x41, 0xd7, 0xd8, 0xdb, 0xdc, 0xdf, 0xe0, 0xff],
    "utf-32-le": [0x00, 0x01, 0x10, 0x11, 0xd8, 0xdc, 0xff],
    "utf-32-be": [0x00, 0x01, 0x10, 0x11, 0xd8, 0xdc, 0xff],
    "raw_unicode_escape": list(b"\\\\uU0178a\n") + [0xff],
    "unicode_escape": list(b"\\\\\\Nxu U0178{}a\nb") + [0xff],
}


@gen("codec", 5)
def gen_codec_chunks(rng):
    codec = rng.choice(list(CHUNK_ALPHA))
    b = [rng.choice(CHUNK_ALPHA[codec]) for _ in range(rng.randint(0, 9))]
    return {"mod": "unicodeobj", "fn": "codec_chunks", "codec": codec, "b": b, "k": rng.randint(0, len(b) + 1),
            "errors": rng.choice(DEC_HANDLERS)}


@run("codec_chunks")
def run_codec_chunks(c):
    import codecs
    import warnings
    dec = {"utf-8": codecs.utf_8_decode, "utf-16-le": codecs.utf_16_le_decode, "utf-16-be": codecs.utf_16_be_decode,
           "utf-32-le": codecs.utf_32_le_decode, "utf-32-be": codecs.utf_32_be_decode,
           "raw_unicode_escape": codecs.raw_unicode_escape_decode,
           "unicode_escape": codecs.unicode_escape_decode}[c["codec"]]
    b, k, errors = bytes(c["b"]), c["k"], c["errors"]

    def call(x, final):
        try:
            s, n = dec(x, errors, final)
            return cps_of(s), n
        except UnicodeError:
            return None

    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        whole = call(b, True)
        whole = list(whole) if whole else None
        first = call(b[:k], False)
        if first is None:
            return ["first", whole]
        s1, n = first
        second = call(b[n:], True)
        if second is None:
            return ["second", s1, n, whole]
        return ["both", s1, n, second[0], second[1], whole]


@gen("codec", 4)
def gen_codec_ascii_obj(rng):
    b = rng.choice([[], [0x41], [0x80], [0xff], [0x41, 0x42]]) if rng.random() < 0.15 else \
        [rng.choice([0, 0x41, 0x7f, 0x80, 0xe9, 0xff]) for _ in range(rng.randint(0, 9))]
    c = {"mod": "unicodeobj", "fn": "codec_ascii_obj", "b": b}
    u8_handler(rng, c)
    return c


@run("codec_ascii_obj")
def run_codec_ascii_obj(c):
    import ctypes
    f = ctypes.pythonapi.PyUnicode_DecodeASCII
    f.restype = ctypes.py_object
    f.argtypes = [ctypes.c_char_p, ctypes.c_ssize_t, ctypes.c_char_p]
    b = bytes(c["b"])
    r = f(b, len(b), u8_errors(c))
    k = kind_of(r)
    return [cps_of(r), k[0], k[1]]

# ==== end str.format ====


# ==== codec slice (fn names codec_*) ====

U8_BYTES = [0, 0x41, 0x7f, 0x80, 0x8f, 0x90, 0x9f, 0xa0, 0xbf, 0xc0, 0xc1, 0xc2, 0xdf, 0xe0, 0xe1, 0xec,
            0xed, 0xee, 0xef, 0xf0, 0xf1, 0xf3, 0xf4, 0xf5, 0xff]
DEC_HANDLERS = ["strict", "ignore", "replace", "surrogateescape", "backslashreplace", "surrogatepass"]
ENC_HANDLERS = DEC_HANDLERS + ["xmlcharrefreplace", "namereplace"]
ALL_HANDLERS = ENC_HANDLERS
ENC_ALPH = [0, 65, 0x7f, 0x80, 0x7ff, 0x800, 0xd7ff, 0xd800, 0xdbff, 0xdc00, 0xdc7f, 0xdc80, 0xdcff,
            0xdd00, 0xdfff, 0xe000, 0xffff, 0x10000, 0x10ffff]


def u8_bytes(rng):
    b = []
    for _ in range(rng.randint(0, 5)):
        if rng.random() < 0.3:
            b += list(chr(rng.choice([65, 0xe9, 0x20ac, 0xd7ff, 0xe000, 0x1f600, 0x10ffff])).encode())
        else:
            b.append(rng.choice(U8_BYTES))
    return b


@gen("codec", 5)
def gen_codec_decode(rng):
    fn = rng.choice(["codec_utf8_decode", "codec_utf8_stateful"])
    return {"mod": "unicodeobj", "fn": fn, "b": u8_bytes(rng), "errors": rng.choice(ALL_HANDLERS)}


@gen("codec", 3)
def gen_codec_encode(rng):
    s = [rng.choice(ENC_ALPH) for _ in range(rng.randint(0, 5))]
    return {"mod": "unicodeobj", "fn": "codec_utf8_encode", "s": s, "errors": rng.choice(ENC_HANDLERS)}


def wide_bytes(rng, width):
    out = []
    for _ in range(rng.randint(0, 5)):
        r = rng.random()
        if r < 0.15:
            out += [rng.choice([0, 0x41, 0x80, 0xd8, 0xdc, 0xff]) for _ in range(rng.randint(1, width))]
        else:
            c = rng.choice([0, 0x41, 0xe9, 0xd7ff, 0xd800, 0xdbff, 0xdc00, 0xdfff, 0xe000, 0xfeff,
                            0xfffe, 0xffff, 0x10000, 0x10ffff, 0x110000, 0xfffffffe])
            n = c.to_bytes(4, "little")[:width] if width == 2 else c.to_bytes(4, "little")
            out += list(n if rng.random() < 0.5 else n[::-1])
    return out


WIDE_NAMES = {2: "utf-16", 4: "utf-32"}
WIDE_DEC = {(2, 0): "utf_16_decode", (2, -1): "utf_16_le_decode", (2, 1): "utf_16_be_decode",
            (4, 0): "utf_32_decode", (4, -1): "utf_32_le_decode", (4, 1): "utf_32_be_decode"}


@gen("codec", 5)
def gen_codec_wide_decode(rng):
    width = rng.choice([2, 4])
    return {"mod": "unicodeobj", "fn": "codec_wide_decode", "width": width, "bo": rng.choice([-1, 0, 1]),
            "b": wide_bytes(rng, width), "errors": rng.choice(ALL_HANDLERS),
            "final": rng.random() < 0.7}


@gen("codec", 4)
def gen_codec_wide_encode(rng):
    s = [rng.choice(ENC_ALPH) for _ in range(rng.randint(0, 5))]
    return {"mod": "unicodeobj", "fn": "codec_wide_encode", "width": rng.choice([2, 4]),
            "bo": rng.choice([-1, 0, 1]), "s": s, "errors": rng.choice(ALL_HANDLERS)}


@run("codec_wide_decode")
def run_codec_wide_decode(c):
    import codecs
    f = getattr(codecs, WIDE_DEC[c["width"], c["bo"]])
    s, n = f(bytes(c["b"]), c["errors"], c["final"])
    return [cps_of(s), n]


@run("codec_wide_encode")
def run_codec_wide_encode(c):
    suffix = {-1: "-le", 0: "", 1: "-be"}[c["bo"]]
    return list(s_of(c["s"]).encode(WIDE_NAMES[c["width"]] + suffix, c["errors"]))


NAME_LOOKUPS = ["LATIN SMALL LETTER A", "latin small letter a", "SNOWMAN", "BULLET", "NOPE", "",
                "GRINNING FACE", "CJK UNIFIED IDEOGRAPH-4E00", "LF", "HANGUL SYLLABLE GA", "}"]
UCS1_ALPH = [0, 65, 92, 127, 128, 233, 255, 256, 0x2603, 0xd800, 0xdc80, 0xdcff, 0xdd00, 0x1f600,
             0x10ffff]
ESC_BYTES = [65, 92, 92, 92, 39, 34, 98, 102, 116, 110, 114, 118, 97, 10, 48, 52, 55, 56, 120, 117,
             85, 78, 123, 125, 53, 97, 70, 0x80, 0xff, 0]


def esc_bytes(rng):
    r = rng.random()
    if r < 0.4:
        return [rng.choice(ESC_BYTES) for _ in range(rng.randint(0, 10))]
    pieces = [b"\\x41", b"\\u0041", b"\\U00000041", b"\\U0010ffff", b"\\U00110000", b"\\xZ", b"\\u12",
              b"\\U1", b"\\777", b"\\101", b"\\8", b"\\q", b"\\\n", b"\\", b"a", b"\\N", b"\\N{",
              b"\\N{}", b"\\Nx", b"\xff", b"\\\\", b"\\ud800"]
    pieces += [b"\\N{" + n.encode() + b"}" for n in NAME_LOOKUPS]
    return list(b"".join(rng.choice(pieces) for _ in range(rng.randint(0, 4))))


def name_table(b):
    """The names in the case's bytes that CPython's \\N accepts."""
    out = []
    i = 0
    data = bytes(b)
    while True:
        i = data.find(b"\\N{", i)
        if i < 0:
            return out
        j = data.find(b"}", i)
        if j < 0:
            return out
        name = data[i + 3:j]
        try:
            ch = (b"\\N{" + name + b"}").decode("unicode_escape")
            if len(ch) == 1 and name:
                out.append([list(name), ord(ch)])
        except UnicodeDecodeError:
            pass
        i += 3


def char_names(s):
    out = []
    for c in sorted(set(s)):
        n = unicodedata.name(chr(c), None)
        if n:
            out.append([cps_of(n), c])
    return out


@gen("codec", 3)
def gen_codec_ucs1(rng):
    s = [rng.choice(UCS1_ALPH) for _ in range(rng.randint(0, 6))]
    return {"mod": "unicodeobj", "fn": "codec_ucs1_encode", "s": s, "limit": rng.choice([128, 256]),
            "errors": rng.choice(ALL_HANDLERS), "names": char_names(s)}


@gen("codec", 3)
def gen_codec_ascii(rng):
    b = [rng.choice([0, 65, 127, 128, 200, 255]) for _ in range(rng.randint(0, 12))]
    return {"mod": "unicodeobj", "fn": rng.choice(["codec_ascii_decode", "codec_latin1_decode"]), "b": b,
            "errors": rng.choice(ALL_HANDLERS)}


@gen("codec", 4)
def gen_codec_ue(rng):
    b = esc_bytes(rng)
    fn = rng.choice(["codec_ue_decode", "codec_raw_decode"])
    c = {"mod": "unicodeobj", "fn": fn, "b": b, "errors": rng.choice(ALL_HANDLERS),
         "final": rng.random() < 0.7}
    if fn == "codec_ue_decode":
        c["names"] = name_table(b)
    return c


@gen("codec", 2)
def gen_codec_esc_encode(rng):
    s = [rng.choice(UCS1_ALPH + [9, 10, 13, 31, 32, 126]) for _ in range(rng.randint(0, 6))]
    return {"mod": "unicodeobj", "fn": rng.choice(["codec_ue_encode", "codec_raw_encode",
                                                   "codec_utf7_encode"]), "s": s}


U7_PIECES = [b"+", b"-", b"+-", b"a", b" ", b"~", b"\\", b"\xff", b"!", b"\x00", b"+AGE-", b"+AGE", b"+2AA",
             b"+2AA-", b"+2ADcAA-", b"+3AA-", b"+2AAA", b"+A", b"+AA", b"+AAA", b"+AAB", b"+//8-", b"+AGE.",
             b"+2AAAYQ-", b"/", b"+2D3eAA-", b"+AAA+"]


@gen("codec", 4)
def gen_codec_utf7(rng):
    if rng.random() < 0.3:
        s = "".join(chr(rng.choice([65, 43, 45, 32, 0, 126, 233, 0x20ac, 0x1f600, 0xd800, 0xdc00]))
                    for _ in range(rng.randint(0, 5)))
        b = list(s.encode("utf-7"))
    else:
        b = list(b"".join(rng.choice(U7_PIECES) for _ in range(rng.randint(0, 4))))
    return {"mod": "unicodeobj", "fn": "codec_utf7_decode", "b": b, "errors": rng.choice(ALL_HANDLERS),
            "final": rng.random() < 0.7}


@run("codec_ucs1_encode")
def run_codec_ucs1(c):
    return list(s_of(c["s"]).encode("latin-1" if c["limit"] == 256 else "ascii", c["errors"]))


@run("codec_ascii_decode")
def run_codec_ascii(c):
    return cps_of(bytes(c["b"]).decode("ascii", c["errors"]))


@run("codec_latin1_decode")
def run_codec_latin1(c):
    return cps_of(bytes(c["b"]).decode("latin-1", c["errors"]))


@run("codec_ue_decode")
def run_codec_ue_decode(c):
    import codecs
    import warnings
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        s, n = codecs.unicode_escape_decode(bytes(c["b"]), c["errors"], c["final"])
    return [cps_of(s), n]


@run("codec_raw_decode")
def run_codec_raw_decode(c):
    import codecs
    s, n = codecs.raw_unicode_escape_decode(bytes(c["b"]), c["errors"], c["final"])
    return [cps_of(s), n]


@run("codec_ue_encode")
def run_codec_ue_encode(c):
    return list(s_of(c["s"]).encode("unicode_escape"))


@run("codec_raw_encode")
def run_codec_raw_encode(c):
    return list(s_of(c["s"]).encode("raw_unicode_escape"))


@run("codec_utf7_decode")
def run_codec_utf7_decode(c):
    import codecs
    s, n = codecs.utf_7_decode(bytes(c["b"]), c["errors"], c["final"])
    return [cps_of(s), n]


@run("codec_utf7_encode")
def run_codec_utf7_encode(c):
    return list(s_of(c["s"]).encode("utf-7"))


CM_CHARS = [0, 65, 97, 63, 38, 35, 59, 48, 49, 233, 255, 256, 0x20ac, 0xfffe, 0xffff, 0x10000]


def cm_table(rng):
    r = rng.random()
    if r < 0.3:
        n = rng.choice([1, 2, 5, 70, 255, 256, 257])
        return [rng.choice(CM_CHARS) for _ in range(n)]
    base = list(range(256))
    if r < 0.6:
        for _ in range(rng.randint(0, 5)):
            base[rng.randrange(256)] = rng.choice(CM_CHARS)
    elif r < 0.8:
        for _ in range(rng.randint(0, 5)):
            base[rng.randrange(256)] = 0xfffe
    return base


def cm_dec_item(rng):
    r = rng.random()
    if r < 0.5:
        return {"t": "int", "v": rng.choice([65, 233, 0xfffe, 0x20ac, 0x10ffff, 0x110000, -1, 2 ** 70])}
    if r < 0.8:
        return {"t": "str", "s": rng.choice([[], [65], [0xfffe], [0x20ac], [65, 66], [0x1f600]])}
    return {"t": rng.choice(["none", "none", "wrong", "raise"])}


def cm_enc_item(rng):
    r = rng.random()
    if r < 0.6:
        return {"t": "int", "v": rng.choice([0, 63, 65, 255, 256, -1, 2 ** 70])}
    if r < 0.85:
        return {"t": "bytes", "s": rng.choice([[], [65], [65, 66]])}
    return {"t": rng.choice(["none", "wrong", "raise"])}


@gen("codec", 3)
def gen_codec_charmap_decode(rng):
    b = [rng.choice([0, 1, 2, 65, 97, 200, 255]) for _ in range(rng.randint(0, 6))]
    if rng.random() < 0.5:
        m = {"k": "str", "table": cm_table(rng)}
    else:
        m = {"k": "map", "table": [[k, cm_dec_item(rng)] for k in sorted(set(b)) if rng.random() < 0.8]}
    return {"mod": "unicodeobj", "fn": "codec_charmap_decode", "b": b, "map": m,
            "errors": rng.choice(ALL_HANDLERS)}


@gen("codec", 3)
def gen_codec_charmap_encode(rng):
    s = [rng.choice(CM_CHARS + [0xdc80, 0xd800]) for _ in range(rng.randint(0, 5))]
    if rng.random() < 0.5:
        m = {"k": "build", "table": cm_table(rng)}
    else:
        keys = set(s) | {63, 38, 35, 59, 48, 49}
        m = {"k": "map", "table": [[k, cm_enc_item(rng)] for k in sorted(keys) if rng.random() < 0.7]}
    return {"mod": "unicodeobj", "fn": "codec_charmap_encode", "s": s, "map": m,
            "errors": rng.choice(ALL_HANDLERS), "names": char_names(s)}


@gen("codec", 1)
def gen_codec_charmap_build(rng):
    return {"mod": "unicodeobj", "fn": "codec_charmap_build", "table": cm_table(rng)}


class CmMapping:
    def __init__(self, items, conv):
        self.d = {k: conv(v) for k, v in items}

    def __getitem__(self, k):
        v = self.d[k]
        if v is RAISE:
            raise ValueError("boom")
        return v


def cm_dec_conv(v):
    return {"none": None, "int": v.get("v"), "str": s_of(v.get("s", [])), "raise": RAISE, "wrong": 1.5}[v["t"]]


def cm_enc_conv(v):
    return {"none": None, "int": v.get("v"), "bytes": bytes(v.get("s", [])), "raise": RAISE,
            "wrong": 1.5}[v["t"]]


@run("codec_charmap_decode")
def run_codec_charmap_decode(c):
    import codecs
    m = c["map"]
    table = s_of(m["table"]) if m["k"] == "str" else CmMapping(m["table"], cm_dec_conv)
    return cps_of(codecs.charmap_decode(bytes(c["b"]), c["errors"], table)[0])


@run("codec_charmap_encode")
def run_codec_charmap_encode(c):
    import codecs
    m = c["map"]
    table = (codecs.charmap_build(s_of(m["table"])) if m["k"] == "build"
             else CmMapping(m["table"], cm_enc_conv))
    return list(codecs.charmap_encode(s_of(c["s"]), c["errors"], table)[0])


@run("codec_charmap_build")
def run_codec_charmap_build(c):
    import codecs
    m = codecs.charmap_build(s_of(c["table"]))
    return [[k, v] for k, v in m.items()] if isinstance(m, dict) else m.size()


SHORTCUT_NAMES = ["utf8", "utf_8", "utf-8", "UTF8", "UTF-8", "utf16", "utf-16", "UTF_16", "utf32", "utf-32",
                  "ascii", "ASCII", "us-ascii", "US_ASCII", "latin1", "latin-1", "LATIN_1", "iso-8859-1",
                  "ISO8859-1", "iso_8859_1", "utf$8", "-utf8", "utf  8", "us ascii", "iso8859 1"]


@gen("codec", 2)
def gen_codec_dispatch(rng):
    b = [rng.choice([0, 65, 0xc3, 0xa9, 0xff, 0xfe]) for _ in range(rng.randint(1, 4))]
    return {"mod": "unicodeobj", "fn": "codec_dispatch", "name": cps_of(rng.choice(SHORTCUT_NAMES)), "b": b}


@run("codec_dispatch")
def run_codec_dispatch(c):
    return cps_of(bytes(c["b"]).decode(s_of(c["name"])))


@run("codec_utf8_decode")
def run_codec_decode(c):
    return cps_of(bytes(c["b"]).decode("utf-8", c["errors"]))


@run("codec_utf8_stateful")
def run_codec_stateful(c):
    import codecs
    s, n = codecs.utf_8_decode(bytes(c["b"]), c["errors"], False)
    return [cps_of(s), n]


@run("codec_utf8_encode")
def run_codec_encode(c):
    return list(s_of(c["s"]).encode("utf-8", c["errors"]))

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


FLOATS = [0.0, -0.0, 1.0, -1.0, 0.5, 1.5, 2.5, 0.1, 0.125, 9.5, 9.995, 99.5, 100.0, 1234.5, 1234.5678,
          -1234.5678, 1234567.125, 0.0001, 0.00001, 1e15, 1e16, 1e17, 1e21, 1e22, 1e23, 1e100, -1e100,
          1.7976931348623157e308, 5e-324, 2.2250738585072014e-308, float("inf"), float("-inf"),
          float("nan"), -float("nan"), 1 / 3, 2 / 3, 123456789012345678.0, -0.0001, 0.999, 0.9999999]


def float_bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def float_of(s):
    return struct.unpack("<d", struct.pack("<Q", int(s, 16)))[0]


def rand_float(rng):
    r = rng.random()
    if r < 0.55:
        return rng.choice(FLOATS)
    if r < 0.75:
        return rng.randint(-10 ** 9, 10 ** 9) / rng.choice([1, 2, 4, 8, 10, 100, 1000])
    if r < 0.9:
        return struct.unpack("<d", struct.pack("<Q", rng.getrandbits(64)))[0]
    return rng.choice([-1, 1]) * rng.random() * 10.0 ** rng.randint(-30, 30)


def float_spec(rng):
    if rng.random() < 0.15:
        return fmt_spec(rng)
    fill = rng.choice(["", "", "", "*", "0", " ", "\xe9", "\U0001f600", "<", "\x00"])
    align = rng.choice(["", "", "<", ">", "=", "^"]) if fill == "" else rng.choice("<>=^")
    sign = rng.choice(["", "", "+", "-", " "])
    z = rng.choice(["", "", "", "z"])
    alt = rng.choice(["", "", "", "#"])
    zero = rng.choice(["", "", "", "0"])
    width = rng.choice(["", "", "", "1", "5", "8", "12", "20", "30", "40", chr(0x663), "007"])
    group = rng.choice(["", "", "", ",", "_", ",_", "_,"])
    prec = rng.choice(["", "", ".", ".0", ".1", ".2", ".3", ".6", ".10", ".17", ".20", ".50", ".350", ".1100",
                       ".,", "._", ".3,", ".3_", ".7,", ".10_", ".20_", "._,", ".,_", "." + str(2 ** 31),
                       "." + str(2 ** 31 - 1), "." + "9" * 30])
    typ = rng.choice(["", "", "e", "E", "f", "F", "g", "G", "n", "%", "\x00", "r", "q", "d"])
    return fill + align + sign + z + alt + zero + width + group + prec + typ


@gen("format", 7)
def gen_fmt_float(rng):
    return {"mod": "unicodeobj", "fn": "fmt_float", "x": format(float_bits(rand_float(rng)), "x"),
            "spec": cps_of(float_spec(rng) if rng.random() < 0.98 else "")}


@gen("format", 5)
def gen_fmt_complex(rng):
    return {"mod": "unicodeobj", "fn": "fmt_complex", "re": format(float_bits(rand_float(rng)), "x"),
            "im": format(float_bits(rand_float(rng)), "x"),
            "spec": cps_of(float_spec(rng) if rng.random() < 0.97 else "")}


def hex_of(v):
    return ("-" if v < 0 else "") + format(abs(v), "x")


PCT_TYPES = "sradiuoxXceEfFgGeEfFgG"
# A `*` takes its width from these, and the model builds a list of that length, so they stay small
# apart from values that fail the conversion.
PCT_OBJS = [0, 1, -1, 7, 255, -255, 65, 2 ** 63, -2 ** 63, 10 ** 30, 10 ** 4300,
            2 ** 1024 - 2 ** 970, 2 ** 1024 - 2 ** 970 - 1, 2 ** 53 + 1,
            True, False, None, "", "a", "abc", chr(0xe9), chr(0x20ac), chr(0x1f600), "it's",
            0.0, -0.0, 1.5, -1.5, 0.1, 3.7, -3.7, 1e22, 1e300, -1e300, 5e-324, float("inf"),
            float("-inf"), float("nan"), 1234.5678, 2.5, 0.0001, 1e16, -2.5]


def pct_enc(o):
    if o is None:
        return {"t": "none"}
    if isinstance(o, bool):
        return {"t": "bool", "v": o}
    if isinstance(o, int):
        return {"t": "int", "v": hex_of(o)}
    if isinstance(o, float):
        return {"t": "float", "v": format(float_bits(o), "x")}
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
    if t == "float":
        return float_of(j["v"])
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
        items = [rng.choice(PCT_OBJS) if rng.random() < 0.8 else rng.choice([3, -3, 12, 40])
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


PCT_CONV_315 = ["'", '"', "$", "!", "q", "Q", "z", "\xe9", "\u20ac", "\x00", "\x7f", "\x80", "\n", "\u0378",
                "\U0001f600", "\U0001fffe", "\ud800", "%", "*", "-", "(", ")", "5", " "]
PCT_BIG_315 = [2 ** 31 - 1, 2 ** 31, -2 ** 31, -2 ** 31 - 1, 2 ** 63 - 1, 2 ** 63, -2 ** 63, -2 ** 63 + 1, -2 ** 63 - 1,
               2 ** 64, -1, 0, 1, 5, 7]


@gen("format", 3)
def gen_fmt_percent_315(rng):
    """The branches 3.15 added: positions, argument numbers, and keys mixed with no keys."""
    obj = lambda: pct_enc(rng.choice(PCT_OBJS))
    r = rng.randint(0, 8)
    pre = rng.choice(["", "abc", "%d", "%%", "\u20ac"])
    if r == 0:      # a key, then what may not follow one, or the other way round
        fmt = rng.choice(["%(a)s %d", "%(a)s %s", "%d %(a)s", "%s%(a)s", "%(a)*d", "%(a).*d", "%(a)-*d", "%(a)s %*d",
                          "%(a)s%(b)s", "%(a)5.2d", "%(a)", "%(a", "%(", "%(a)%", "%(a))s", "%((a)s", "%(a)d%%"])
        args = {"k": "dict", "items": [[cps_of(k), obj()] for k in rng.sample(["a", "b", "(a)"], rng.randint(0, 3))]}
    elif r == 1:    # a key without a mapping
        fmt = rng.choice(["%(a)s", "x%(a)d", "%d%(a)s"])
        args = rng.choice([{"k": "single", "item": obj()}, {"k": "tuple", "items": [obj()]}, {"k": "tuple", "items": []}])
    elif r == 2:    # a mapping as the one argument
        fmt = rng.choice(["%s", "%r", "%a", "%d", "%x", "%f", "%c", "%5s", "%s %s", "", "x", "%*d", "%.*f", "%%", "%q"])
        args = {"k": "dict", "items": [[cps_of(k), obj()] for k in rng.sample(["a", "b"], rng.randint(0, 2))]}
    elif r == 3:    # `*` with one argument that is not a tuple
        fmt = rng.choice(["%*d", "%.*d", "%-*s", "%*.*f", "%*"])
        args = {"k": "single", "item": obj()}
    elif r == 4:    # bad conversions
        fmt = pre + "%" + rng.choice(["", "-", "5", ".2", "l", "#0"]) + rng.choice(PCT_CONV_315)
        items = [rng.choice(PCT_OBJS) for _ in range(rng.randint(0, 2))]
        args = {"k": "tuple", "items": [pct_enc(o) for o in items]}
    elif r == 5:    # the end of the format
        fmt = pre + rng.choice(["%", "%5", "%.", "%.3", "%-", "%l", "%h", "%L", "%5.", "%*", "%.*", "%5l", "%#0"])
        args = {"k": "tuple", "items": [pct_enc(rng.choice([1, 2.5, "s", None])) for _ in range(rng.randint(0, 2))]}
    elif r == 6:    # sizes
        fmt = rng.choice(["%99999999999999999999d", "%9223372036854775807d", "%9223372036854775808d",
                          "%.99999999999d", "%.2147483648d", "%.2147483647d", "x%99999999999999999999d"])
        args = {"k": "tuple", "items": [pct_enc(7)]}
    elif r == 7:    # the sizes of `*`, and a value for each
        fmt = pre + rng.choice(["%*d", "%*s", "%.*d", "%.*s", "%*.*d", "%-*d", "%0*d"])
        vals = [rng.choice(PCT_BIG_315), rng.choice([0, 1, 5, 7, -1] + PCT_BIG_315), 3, "s"]
        keep = rng.randint(1, 4)
        args = {"k": "tuple", "items": ([pct_enc(3)] if pre == "%d" else []) + [pct_enc(v) for v in vals[:keep]]}
    else:           # the argument number
        fmt = pre + rng.choice(["%d", "%x", "%f", "%c", "%*d", "%s %d", "%s %s %x", "%s"])
        args = {"k": "tuple", "items": [obj() for _ in range(rng.randint(0, 4))]}
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


# Subclasses of str, int, float and complex: the type name shows in the errors (cut to 200 bytes of
# UTF-8), an empty spec goes through str(obj), and float(obj) of an int subclass through __float__.
SUB_NAMES = ["S", "MyNumber", "\xdcn\xefc\xf6d\xe9", "A" * 250, "\xe9" * 150, "a" + "\xe9" * 150,
             "€" * 70, "b" + "\U0001f600" * 60]
SUB_STR = [None, None, {"k": "ok", "s": "S!"}, {"k": "ok", "s": ""}, {"k": "raise"}]
SUB_FLT = [None, None, {"k": "ok", "x": 2.5}, {"k": "ok", "x": -0.0}, {"k": "raise"}, {"k": "int"}]


def sub_enc(o):
    if o is None:
        return None
    if o["k"] == "ok" and "s" in o:
        return {"k": "ok", "s": cps_of(o["s"])}
    if o["k"] == "ok":
        return {"k": "ok", "x": format(float_bits(o["x"]), "x")}
    return o


@gen("format", 4)
def gen_fmt_sub(rng):
    kind = rng.choice(["str", "int", "float", "complex"])
    spec = "" if rng.random() < 0.3 else (fmt_spec(rng) if kind in ("str", "int") else float_spec(rng))
    c = {"mod": "unicodeobj", "spec": cps_of(spec), "tn": rng.choice(SUB_NAMES),
         "str": sub_enc(rng.choice(SUB_STR))}
    if kind == "str":
        c.update(fn="fmt_str", s=cps_of(rng.choice(["", "abc", "\xe9t\xe9", "\U0001f600x"])))
    elif kind == "int":
        v = rng.choice(FMT_INTS) if rng.random() < 0.5 else rng.randint(-10 ** 6, 10 ** 6)
        c.update(fn="fmt_int", v=hex_of(v), name="int", flt=sub_enc(rng.choice(SUB_FLT)))
    elif kind == "float":
        c.update(fn="fmt_float", x=format(float_bits(rand_float(rng)), "x"))
    else:
        c.update(fn="fmt_complex", re=format(float_bits(rand_float(rng)), "x"),
                 im=format(float_bits(rand_float(rng)), "x"))
    return c


def sub_value(c, base, value):
    """`value` as an instance of a subclass of `base` named c['tn'], with the case's __str__ and
    __float__."""
    if "tn" not in c:
        return value
    ns = {}
    st = c.get("str")
    if st is not None:
        if st["k"] == "raise":
            def __str__(self):
                raise ValueError("boom")
        else:
            text = s_of(st["s"])

            def __str__(self):
                return text
        ns["__str__"] = __str__
    fl = c.get("flt")
    if fl is not None:
        if fl["k"] == "raise":
            def __float__(self):
                raise ValueError("boom")
        elif fl["k"] == "int":
            def __float__(self):
                return 1
        else:
            x = float_of(fl["x"])

            def __float__(self):
                return x
        ns["__float__"] = __float__
    return type(c["tn"], (base,), ns)(value)


@run("fmt_int")
def run_fmt_int(c):
    s = c["v"]
    v = -int(s[1:], 16) if s.startswith("-") else int(s, 16)
    if c["name"] == "bool":
        v = bool(v)
    return cps_of(format(sub_value(c, int, v), s_of(c["spec"])))


@run("fmt_str")
def run_fmt_str(c):
    return cps_of(format(sub_value(c, str, s_of(c["s"])), s_of(c["spec"])))


@run("fmt_float")
def run_fmt_float(c):
    return cps_of(format(sub_value(c, float, float_of(c["x"])), s_of(c["spec"])))


@run("fmt_complex")
def run_fmt_complex(c):
    return cps_of(format(sub_value(c, complex, complex(float_of(c["re"]), float_of(c["im"]))),
                         s_of(c["spec"])))

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


@gen("text", 5)
def gen_text_translate_x(rng):
    s = text_str(rng) if rng.random() < 0.5 else [rng.choice([97, 98, 99, 100]) for _ in range(rng.randint(0, 7))]
    if rng.random() < 0.25:
        s = s + [rng.choice([0xe9, 0x20ac, 0x1f600])]
    keys = list(dict.fromkeys(s + rng.sample(TEXT_ALPH, 2)))
    table = [[k, [text_item(rng) for _ in range(rng.randint(1, 3))]] for k in keys if rng.random() < 0.75]
    mode = rng.choice(["ignore", "ignore", "strict", "custom"])
    script = []
    for _ in range(rng.randint(1, 4)):
        r = rng.random()
        if r < 0.1:
            script.append({"t": "raise"})
        elif r < 0.2:
            script.append({"t": "bad", "form": rng.randint(0, 2)})
        else:
            pos, rel = (rng.choice([0, 0, 0, 1, -1]), True) if rng.random() < 0.7 else (rng.choice(CB_POS), False)
            script.append({"t": "ret", "rep": cps_of(rng.choice(["", "x", "\xe9", "\U0001f600"])), "pos": pos, "rel": rel})
    return {"mod": "unicodeobj", "fn": "text_translate_x", "s": s, "table": table, "mode": mode, "script": script}


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
        return {"mod": "unicodeobj", "fn": "text_maketrans_dict", "x": items, "frozen": rng.random() < 0.4}
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


class ScriptMapping:
    """The n-th lookup of a key gets its n-th answer, and the last answer repeats."""

    def __init__(self, table):
        self.d = {k: [conv_item(v) for v in vs] for k, vs in table}
        self.seen = {}

    def __getitem__(self, k):
        vs = self.d[k]
        n = self.seen.get(k, 0)
        self.seen[k] = n + 1
        v = vs[min(n, len(vs) - 1)]
        if v is RAISE:
            raise ValueError("boom")
        return v


def tr_handler(script):
    items = list(script)

    def handler(e):
        if not items:
            raise RuntimeError("done")
        r = items.pop(0)
        if r["t"] == "raise":
            raise ValueError("boom")
        if r["t"] == "bad":
            return ["x", ("x",), (b"x", 1)][r["form"]]
        return s_of(r["rep"]), r["pos"] + e.end if r["rel"] else r["pos"]
    return handler


@run("text_translate_x")
def run_text_translate_x(c):
    import codecs
    s, m = s_of(c["s"]), ScriptMapping(c["table"])
    if c["mode"] == "ignore":
        return cps_of(s.translate(m))
    if c["mode"] == "strict":
        return cps_of(TRANSLATE(s, m, None))
    codecs.register_error("uo_tr", tr_handler(c["script"]))
    return cps_of(TRANSLATE(s, m, b"uo_tr"))


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
    return enc_trans(str.maketrans(frozendict(d) if c.get("frozen") else d))


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


# ==== str method slice (fn names meth_*) ====

import operator

ME_ALPH = [0x20, 0x9, 0xa, 0xd, 0x1c, 0x1f, 0x85, 0xa0, 0x1680, 0x2028, 0x3000, 0x200b, 0x41, 0x61,
           0x62, 0x78, 0x2d, 0x2b, 0x30, 0x31, 0x7f, 0xe9, 0xff, 0x100, 0x141, 0x3a3, 0x20ac, 0xd800,
           0xffff, 0x10000, 0x10041, 0x1f600, 0x10ffff]
ME_INTS = [0, 1, -1, 2, 3, 4, 5, 7, 8, 9, 10, -2, -3, -5, -9, -10, 2 ** 30 - 1, 2 ** 30, -2 ** 30,
           -2 ** 30 - 1, M, M + 1, -M - 1, -M - 2, 2 ** 64, -2 ** 64, 10 ** 30]
ME_OTHER = {"float": 2.5, "list": [], "bytes": b"a", "dict": {}}


class MeIdx:
    """An object whose __index__ answers an int, raises, or returns a non-int."""

    def __init__(self, mode, v=0):
        self.mode, self.v = mode, v

    def __index__(self):
        if self.mode == "ok":
            return self.v
        if self.mode == "raise":
            raise ValueError("boom")
        return "x"


def me_str(rng, maxlen=8):
    k = rng.random()
    if k < 0.3:
        pool = [c for c in ME_ALPH if c < 128]
    elif k < 0.5:
        pool = [c for c in ME_ALPH if c < 256]
    elif k < 0.7:
        pool = [c for c in ME_ALPH if c < 65536]
    else:
        pool = ME_ALPH
    return [rng.choice(pool) for _ in range(rng.randint(0, maxlen))]


def me_int(rng, n=8):
    r = rng.random()
    if r < 0.5:
        return rng.randint(-n - 2, n + 2)
    return rng.choice(ME_INTS)


def me_index_arg(rng, n=8):
    """An argument meant as an index: mostly an int, sometimes another object."""
    r = rng.random()
    if r < 0.75:
        return {"t": "int", "v": me_int(rng, n)}
    if r < 0.85:
        mode = rng.choice(["ok", "ok", "raise", "bad"])
        v = me_int(rng, n)
        obj = MeIdx(mode, v)
        try:
            res = {"ok": operator.index(obj)}
        except Exception as e:
            res = {"exc": type(e).__name__, "msg": str(e)}
        return {"t": "index", "tp": "MeIdx", "r": res, "mode": mode, "v": v}
    if r < 0.9:
        return {"t": "none"}
    if r < 0.95:
        return {"t": "str", "s": me_str(rng, 2)}
    return {"t": "other", "tp": rng.choice(list(ME_OTHER))}


def me_obj(a):
    t = a["t"]
    if t == "int":
        return a["v"]
    if t == "str":
        return s_of(a["s"])
    if t == "none":
        return None
    if t == "tuple":
        return tuple(me_obj(x) for x in a["items"])
    if t == "index":
        return MeIdx(a["mode"], a["v"])
    return ME_OTHER[a["tp"]]


@gen("meth", 6)
def gen_meth_strip(rng):
    s = me_str(rng)
    r = rng.random()
    if r < 0.3:
        chars = {"t": "none"}
    elif r < 0.85:
        pool = s + ME_ALPH if s and rng.random() < 0.6 else ME_ALPH
        chars = {"t": "str", "s": [rng.choice(pool) for _ in range(rng.randint(0, 4))]}
    else:
        chars = rng.choice([{"t": "int", "v": 1}, {"t": "other", "tp": "bytes"},
                            {"t": "other", "tp": "list"}])
    return {"mod": "unicodeobj", "fn": "meth_strip", "s": s, "chars": chars,
            "op": rng.choice(["strip", "lstrip", "rstrip"])}


@run("meth_strip")
def run_meth_strip(c):
    return cps_of(getattr(s_of(c["s"]), c["op"])(me_obj(c["chars"])))


_ME_FINDCHAR = ctypes.pythonapi.PyUnicode_FindChar
_ME_FINDCHAR.argtypes = [ctypes.py_object, ctypes.c_uint32, ctypes.c_ssize_t, ctypes.c_ssize_t,
                         ctypes.c_int]
_ME_FINDCHAR.restype = ctypes.c_ssize_t
_ME_SUBSTRING = ctypes.pythonapi.PyUnicode_Substring
_ME_SUBSTRING.argtypes = [ctypes.py_object, ctypes.c_ssize_t, ctypes.c_ssize_t]
_ME_SUBSTRING.restype = ctypes.py_object
ME_SSIZE = [0, 1, -1, 2, 3, 5, 8, 9, -2, -5, -9, M, -M - 1, M - 1]


def me_ssize(rng):
    return rng.randint(-10, 10) if rng.random() < 0.6 else rng.choice(ME_SSIZE)


@gen("meth", 3)
def gen_meth_findchar(rng):
    s = me_str(rng)
    pool = s + ME_ALPH + [0x10041, 0x1ff41, 0xffff0041, 0xffffffff, 0x110000]
    return {"mod": "unicodeobj", "fn": "meth_findchar", "s": s, "ch": rng.choice(pool),
            "start": me_ssize(rng), "end": me_ssize(rng), "dir": rng.choice([1, -1, 1, -1, 0, 2])}


@run("meth_findchar")
def run_meth_findchar(c):
    return _ME_FINDCHAR(s_of(c["s"]), c["ch"], c["start"], c["end"], c["dir"])


@gen("meth", 2)
def gen_meth_substring(rng):
    return {"mod": "unicodeobj", "fn": "meth_substring", "s": me_str(rng), "start": me_ssize(rng),
            "end": me_ssize(rng)}


@run("meth_substring")
def run_meth_substring(c):
    return cps_of(_ME_SUBSTRING(s_of(c["s"]), c["start"], c["end"]))


@gen("meth", 5)
def gen_meth_pad(rng):
    s = me_str(rng, 6)
    if s and rng.random() < 0.3:
        s[0] = rng.choice([0x2b, 0x2d])
    op = rng.choice(["center", "ljust", "rjust", "zfill"])
    c = {"mod": "unicodeobj", "fn": "meth_pad", "op": op, "s": s,
         "width": me_index_arg(rng, len(s) + 4)}
    if op != "zfill" and rng.random() < 0.6:
        r = rng.random()
        if r < 0.8:
            c["fill"] = {"t": "str", "s": [rng.choice(ME_ALPH)]}
        elif r < 0.9:
            c["fill"] = {"t": "str", "s": me_str(rng, 3)}
        else:
            c["fill"] = rng.choice([{"t": "int", "v": 32}, {"t": "none"}, {"t": "other", "tp": "bytes"}])
    return c


@run("meth_pad")
def run_meth_pad(c):
    s = s_of(c["s"])
    args = [me_obj(c["width"])] + ([me_obj(c["fill"])] if "fill" in c else [])
    return cps_of(getattr(s, c["op"])(*args))


def me_affix(rng, s):
    """A str argument that often is a prefix, suffix or middle piece of s."""
    r = rng.random()
    if s and r < 0.6:
        i = rng.randint(0, len(s))
        j = rng.randint(i, len(s))
        piece = s[i:j]
        if rng.random() < 0.2 and piece:
            piece = piece[:-1] + [rng.choice(ME_ALPH)]
        return piece
    return me_str(rng, 3)


@gen("meth", 5)
def gen_meth_startswith(rng):
    s = me_str(rng)
    r = rng.random()
    if r < 0.6:
        sub = {"t": "str", "s": me_affix(rng, s)}
    elif r < 0.9:
        items = [{"t": "str", "s": me_affix(rng, s)} for _ in range(rng.randint(0, 3))]
        if rng.random() < 0.3:
            items.insert(rng.randint(0, len(items)), rng.choice(
                [{"t": "int", "v": 1}, {"t": "none"}, {"t": "other", "tp": "bytes"}]))
        sub = {"t": "tuple", "items": items}
    else:
        sub = rng.choice([{"t": "int", "v": 1}, {"t": "none"}, {"t": "other", "tp": "list"}])
    c = {"mod": "unicodeobj", "fn": "meth_startswith", "op": rng.choice(["startswith", "endswith"]),
         "s": s, "sub": sub}
    if rng.random() < 0.6:
        c["start"] = me_index_arg(rng, len(s) + 2)
        if rng.random() < 0.6:
            c["end"] = me_index_arg(rng, len(s) + 2)
    return c


@run("meth_startswith")
def run_meth_startswith(c):
    args = [me_obj(c["sub"])]
    if "start" in c:
        args.append(me_obj(c["start"]))
        if "end" in c:
            args.append(me_obj(c["end"]))
    return getattr(s_of(c["s"]), c["op"])(*args)


@gen("meth", 3)
def gen_meth_removeaffix(rng):
    s = me_str(rng)
    if rng.random() < 0.9:
        affix = {"t": "str", "s": me_affix(rng, s)}
    else:
        affix = rng.choice([{"t": "int", "v": 1}, {"t": "none"}, {"t": "other", "tp": "bytes"}])
    return {"mod": "unicodeobj", "fn": "meth_removeaffix", "s": s, "affix": affix,
            "op": rng.choice(["removeprefix", "removesuffix"])}


@run("meth_removeaffix")
def run_meth_removeaffix(c):
    return cps_of(getattr(s_of(c["s"]), c["op"])(me_obj(c["affix"])))


_ME_TAILMATCH = ctypes.pythonapi.PyUnicode_Tailmatch
_ME_TAILMATCH.argtypes = [ctypes.py_object, ctypes.py_object, ctypes.c_ssize_t, ctypes.c_ssize_t,
                          ctypes.c_int]
_ME_TAILMATCH.restype = ctypes.c_ssize_t


@gen("meth", 3)
def gen_meth_tailmatch(rng):
    s = me_str(rng)
    a = {"t": "str", "s": s} if rng.random() < 0.95 else {"t": "int", "v": 3}
    b = {"t": "str", "s": me_affix(rng, s)} if rng.random() < 0.95 else {"t": "none"}
    return {"mod": "unicodeobj", "fn": "meth_tailmatch", "str": a, "sub": b,
            "start": me_ssize(rng), "end": me_ssize(rng), "dir": rng.choice([1, -1, 0, 2])}


@run("meth_tailmatch")
def run_meth_tailmatch(c):
    return _ME_TAILMATCH(me_obj(c["str"]), me_obj(c["sub"]), c["start"], c["end"], c["dir"])


@gen("meth", 5)
def gen_meth_slice(rng):
    s = me_str(rng)
    form = rng.choice(["binary", "binary", "subscript", "index"])
    c = {"mod": "unicodeobj", "fn": "meth_slice", "form": form, "s": s,
         "a": me_index_arg(rng, len(s) + 2)}
    if form != "index":
        c["b"] = me_index_arg(rng, len(s) + 2)
    if form == "subscript":
        c["c"] = {"t": "none"} if rng.random() < 0.3 else me_index_arg(rng, 3)
    return c


def me_binary_slice(s, a, b):
    return s[a:b]  # BINARY_SLICE, which runs _PyUnicode_BinarySlice for an exact str


@run("meth_slice")
def run_meth_slice(c):
    s = s_of(c["s"])
    a = me_obj(c["a"])
    if c["form"] == "binary":
        return cps_of(me_binary_slice(s, a, me_obj(c["b"])))
    if c["form"] == "subscript":
        return cps_of(s[slice(a, me_obj(c["b"]), me_obj(c["c"]))])
    return cps_of(s[a])


@gen("meth", 4)
def gen_meth_partition(rng):
    s = me_str(rng)
    r = rng.random()
    if r < 0.85:
        sep = {"t": "str", "s": me_affix(rng, s)}
    elif r < 0.92:
        sep = {"t": "str", "s": s + me_str(rng, 2)}
    else:
        sep = rng.choice([{"t": "int", "v": 1}, {"t": "none"}, {"t": "other", "tp": "bytes"}])
    return {"mod": "unicodeobj", "fn": "meth_partition", "s": s, "sep": sep,
            "op": rng.choice(["partition", "rpartition"])}


@run("meth_partition")
def run_meth_partition(c):
    return [cps_of(x) for x in getattr(s_of(c["s"]), c["op"])(me_obj(c["sep"]))]


def me_width_value(a):
    if a["t"] == "int":
        return a["v"]
    if a["t"] == "index" and "ok" in a["r"]:
        return a["r"]["ok"]
    return 0

# ==== end str method slice ====


# ==== Python/codecs.c and Modules/_codecsmodule.c (fn names codecs_*) ====

def _ucn_getname():
    """`ucnhash_capi->getname(c, buf, 256, with_alias_and_seq)`, the function namereplace
    calls, reached through the capsule unicodedata exports."""
    import ctypes
    get_ptr = ctypes.pythonapi.PyCapsule_GetPointer
    get_ptr.restype = ctypes.c_void_p
    get_ptr.argtypes = [ctypes.py_object, ctypes.c_char_p]
    ptr = get_ptr(unicodedata._ucnhash_CAPI, b"unicodedata._ucnhash_CAPI")
    proto = ctypes.CFUNCTYPE(ctypes.c_int, ctypes.c_uint32, ctypes.c_char_p, ctypes.c_int, ctypes.c_int)
    fn = proto(ctypes.c_void_p.from_address(ptr).value)
    buf = ctypes.create_string_buffer(256)

    def getname(c, flag=1):
        return buf.value.decode("ascii") if fn(c, buf, 256, flag) else None
    return getname


CAPI_GETNAME = _ucn_getname()


def capi_names(cps):
    return [[c, None if CAPI_GETNAME(c) is None else cps_of(CAPI_GETNAME(c))] for c in sorted(set(cps))]


class SubEnc(UnicodeEncodeError):
    pass


class SubDec(UnicodeDecodeError):
    pass


class SubTr(UnicodeTranslateError):
    pass


class SubVal(ValueError):
    pass


class MroDropEnc(type):
    """A metaclass whose MRO keeps UnicodeEncodeError but drops its bases."""
    def mro(cls):
        return [cls, UnicodeEncodeError, object]


class MroDropDec(type):
    def mro(cls):
        return [cls, UnicodeDecodeError, BaseException, object]


class MroEnc(UnicodeEncodeError, metaclass=MroDropEnc):
    pass


class MroEncSub(MroEnc):
    """tp_base MroEnc has no BaseException in its MRO, so this class lacks the exception flag."""
    pass


class MroDec(UnicodeDecodeError, metaclass=MroDropDec):
    pass


class CheckRaises(type):
    """A metaclass `__subclasscheck__` that raises: `_PyErr_SetObject` asks it before raising."""
    def __subclasscheck__(cls, sub):
        raise RuntimeError("subclasscheck")


class CheckFalse(type):
    def __subclasscheck__(cls, sub):
        return False


class CheckTrue(type):
    def __subclasscheck__(cls, sub):
        return True


ChkRaiseEnc = CheckRaises("ChkRaiseEnc", (UnicodeEncodeError,), {})
ChkRaiseDec = CheckRaises("ChkRaiseDec", (UnicodeDecodeError,), {})
ChkFalseEnc = CheckFalse("ChkFalseEnc", (UnicodeEncodeError,), {})
ChkFalseDec = CheckFalse("ChkFalseDec", (UnicodeDecodeError,), {})
ChkTrueEnc = CheckTrue("ChkTrueEnc", (UnicodeEncodeError,), {})
ChkTrueDec = CheckTrue("ChkTrueDec", (UnicodeDecodeError,), {})


def ch_subcheck(cls):
    """What `issubclass(cls, cls)` does, as the model's oracle sees it."""
    m = type(cls)
    if m is CheckRaises:
        return {"t": "raise"}
    if m is CheckFalse:
        return {"t": "false"}
    return {"t": "true"}


def fqn(t):
    """`PyType_GetFullyQualifiedName`, which `%T` prints: no module for builtins and __main__."""
    return t.__qualname__ if t.__module__ in ("builtins", "__main__") else f"{t.__module__}.{t.__qualname__}"


CH_KINDS = {
    "enc": UnicodeEncodeError, "dec": UnicodeDecodeError, "tr": UnicodeTranslateError,
    "subenc": SubEnc, "subdec": SubDec, "subtr": SubTr,
    "uerr": UnicodeError, "value": ValueError, "subval": SubVal, "int": int, "strobj": str,
    "mroenc": MroEnc, "mroencsub": MroEncSub, "mrodec": MroDec,
    "chkraiseenc": ChkRaiseEnc, "chkraisedec": ChkRaiseDec, "chkfalseenc": ChkFalseEnc,
    "chkfalsedec": ChkFalseDec, "chktrueenc": ChkTrueEnc, "chktruedec": ChkTrueDec,
}
CH_HANDLERS = ["strict", "ignore", "replace", "xmlcharrefreplace", "backslashreplace", "namereplace",
               "surrogatepass", "surrogateescape"]
CH_CHARS = [0x0, 0x9, 0x26, 0x41, 0x5c, 0x7a, 0x7f, 0x80, 0xe9, 0xff, 0x100, 0x3400, 0x4e00, 0xac00,
            0x20ac, 0xd7ff, 0xd800, 0xdbff, 0xdc00, 0xdc7f, 0xdc80, 0xdcff, 0xdd00, 0xdfff, 0xe000,
            0xfffd, 0xffff, 0x10000, 0x1f600, 0xe0100, 0xf0000, 0xf0001, 0xf00ff, 0xf01d8, 0xf0200,
            0xf0300, 0xf03a0, 0x10ffff, 9999, 99999, 999999]
CH_BYTES = [0x00, 0x41, 0x5c, 0x7f, 0x80, 0x9f, 0xa0, 0xb0, 0xbf, 0xc0, 0xd8, 0xdc, 0xdf, 0xe0, 0xed,
            0xef, 0xff]
CH_SURR = [0xd800, 0xdbff, 0xdc00, 0xdc80, 0xdcff, 0xdfff]
CH_ENCODINGS = ["utf-8", "UTF8", "utf_8", "utf8", "Utf-8", "cp65001", "CP65001", "utf-16", "utf-16-le",
                "UTF-16BE", "utf_16_le", "utf16le", "utf16-be", "utf-16-", "utf-16-l", "utf-16-lex",
                "utf-16-xe", "utf-32", "utf-32-be", "utf32LE", "utf_32-le", "utf-32-", "utf", "u", "",
                "utf-8\x00junk", "utf-16\x00be", "utf-8-sig", "utf-7", "ascii", "latin-1", "utf-\ud800",
                "\ud800", "utf-16-\xe9e", "\xfctf-8", "utf--8", "utf-1", "utf-3", "utf-16-be\x00",
                "utf-32le", "utf-32_BE"]


def ch_rand_enc(rng):
    if rng.random() < 0.8:
        return cps_of(rng.choice(CH_ENCODINGS))
    return cps_of("".join(rng.choice("utfUTF-_81632lebLEB\x00\xe9") for _ in range(rng.randint(0, 9))))


def ch_surr_bytes(rng):
    """A surrogate as one of the five encodings writes it, or a near miss."""
    c = rng.choice(CH_SURR + [0xd7ff, 0xe000, 0x41])
    form = rng.choice(["utf-8", "utf-16-le", "utf-16-be", "utf-32-le", "utf-32-be"])
    b = list(chr(c).encode(form, "surrogatepass"))
    if rng.random() < 0.15 and b:
        b[rng.randrange(len(b))] ^= rng.choice([0x01, 0x40, 0x80])
    return b


def ch_str(rng):
    pool = rng.sample(CH_CHARS, rng.choice([1, 2, 4, len(CH_CHARS)]))
    return [rng.choice(pool) for _ in range(rng.randint(0, 7))]


def ch_bytes(rng):
    out = []
    for _ in range(rng.randint(0, 4)):
        out += ch_surr_bytes(rng) if rng.random() < 0.4 else [rng.choice(CH_BYTES)]
    return out


def ch_slot(rng, want):
    r = rng.random()
    if r < 0.82:
        k = want
    elif r < 0.9:
        k = "bytes" if want == "str" else "str"
    else:
        k = rng.choice(["null", "none", "int"])
    if k == "str":
        return {"k": "str", "v": ch_str(rng)}
    if k == "bytes":
        return {"k": "bytes", "v": ch_bytes(rng)}
    return {"k": k}


def ch_pos(rng, n):
    r = rng.random()
    if r < 0.7:
        return rng.randint(-2, n + 2)
    return rng.choice([-2 ** 63, -2 ** 63 + 1, -5, -1, 0, 1, n - 1, n, n + 1, 2 ** 62, 2 ** 63 - 2,
                       2 ** 63 - 1])


@gen("codecs", 10)
def gen_codecs_handler(rng):
    kind = rng.choices(list(CH_KINDS), weights=[6, 6, 3, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])[0]
    cls = CH_KINDS[kind]
    obj_type = "bytes" if issubclass(cls, UnicodeDecodeError) else "str"
    c = {"mod": "unicodeobj", "fn": "codecs_handler", "h": rng.choice(CH_HANDLERS), "kind": kind,
         "cls": fqn(cls), "tp": fqn(cls), "mro": [fqn(t) for t in cls.__mro__],
         "flag": bool(cls.__flags__ & (1 << 30)), "repr": repr(cls), "subcheck": ch_subcheck(cls)}
    if obj_type == "str" and rng.random() < 0.5:
        enc = {"k": "str", "v": ch_rand_enc(rng)}
    else:
        enc = {"k": "str", "v": ch_rand_enc(rng)} if rng.random() < 0.85 else \
            ch_slot(rng, rng.choice(["bytes", "null", "none"]))
    obj = ch_slot(rng, obj_type)
    if obj_type == "bytes" and obj["k"] == "bytes" and rng.random() < 0.5:
        # one surrogate in a chosen encoding, so surrogatepass has something to find
        obj = {"k": "bytes", "v": [rng.choice(CH_BYTES) for _ in range(rng.randint(0, 2))] + ch_surr_bytes(rng)
               + [rng.choice(CH_BYTES) for _ in range(rng.randint(0, 2))]}
    if obj_type == "str" and obj["k"] == "str" and rng.random() < 0.4:
        obj["v"] = obj["v"] + [rng.choice(CH_SURR) for _ in range(rng.randint(1, 3))]
    start = None
    if c["h"] == "surrogatepass" and obj_type == "bytes" and rng.random() < 0.6:
        # a surrogate at start, in the encoding the exception names
        form = rng.choice(["utf-8", "utf-16-le", "utf-16-be", "utf-32-le", "utf-32-be"])
        pre = [rng.choice(CH_BYTES) for _ in range(rng.randint(0, 2))]
        b = list(chr(rng.choice(CH_SURR + [0xe000])).encode(form, "surrogatepass"))
        obj = {"k": "bytes", "v": pre + b + [rng.choice(CH_BYTES) for _ in range(rng.randint(0, 2))]}
        names = {"utf-8": ["utf-8", "UTF8", "cp65001"], "utf-16-le": ["utf-16", "utf_16_LE", "utf16le"],
                 "utf-16-be": ["utf-16-be", "UTF16BE"], "utf-32-le": ["utf-32", "utf-32le"],
                 "utf-32-be": ["utf-32-be", "Utf_32_bE"]}[form]
        enc = {"k": "str", "v": cps_of(rng.choice(names))}
        start = len(pre)
    if c["h"] == "surrogateescape" and obj_type == "str" and rng.random() < 0.4:
        obj = {"k": "str", "v": [rng.randint(0xdc78, 0xdd02) for _ in range(rng.randint(0, 5))]}
    if c["h"] == "surrogatepass" and obj_type == "str" and rng.random() < 0.4:
        obj = {"k": "str", "v": [rng.choice(CH_SURR + [0xe000]) for _ in range(rng.randint(0, 5))]}
        enc = {"k": "str", "v": cps_of(rng.choice(CH_ENCODINGS[:22]))}
    n = len(obj.get("v", []))
    c.update({"encoding": enc, "object": obj, "start": ch_pos(rng, n) if start is None else start,
              "end": ch_pos(rng, n)})
    c["names"] = capi_names(obj["v"]) if obj["k"] == "str" else []
    return c


def ch_set(e, attr, slot):
    k = slot["k"]
    if k == "null":
        delattr(e, attr)
    elif k == "str":
        setattr(e, attr, s_of(slot["v"]))
    elif k == "bytes":
        setattr(e, attr, bytes(slot["v"]))
    elif k == "none":
        setattr(e, attr, None)
    else:
        setattr(e, attr, 5)


def ch_build(c):
    cls = CH_KINDS[c["kind"]]
    if issubclass(cls, UnicodeEncodeError):
        e = cls("ascii", "x", 0, 1, "r")
    elif issubclass(cls, UnicodeDecodeError):
        e = cls("ascii", b"x", 0, 1, "r")
    elif issubclass(cls, UnicodeTranslateError):
        e = cls("x", 0, 1, "r")
    elif cls is int:
        return 5
    elif cls is str:
        return "abc"
    else:
        return cls("x")
    ch_set(e, "encoding", c["encoding"])
    ch_set(e, "object", c["object"])
    e.start = c["start"]
    e.end = c["end"]
    return e


@run("codecs_handler")
def run_codecs_handler(c):
    import codecs
    e = ch_build(c)
    h = codecs.lookup_error(c["h"])
    try:
        rep, pos = h(e)
    except:  # noqa: E722 -- a class with a custom mro() may be no Exception
        x = sys.exc_info()[1]
        if x is e:
            return {"raised": "self"}
        if any("Normalization failed" in n for n in getattr(x, "__notes__", [])):
            return {"raised": "normalize"}
        return {"raised": type(x).__name__, "msg": str(x)}
    if isinstance(rep, str):
        return {"rep": ["str", cps_of(rep)], "pos": pos}
    return {"rep": ["bytes", list(rep)], "pos": pos}


@gen("codecs", 2)
def gen_codecs_ucs1_encode(rng):
    s = ch_str(rng)
    return {"mod": "unicodeobj", "fn": "codecs_ucs1_encode", "s": s, "limit": rng.choice([128, 256]),
            "h": rng.choice(CH_HANDLERS), "names": capi_names(s)}


@run("codecs_ucs1_encode")
def run_codecs_ucs1_encode(c):
    return list(s_of(c["s"]).encode("ascii" if c["limit"] == 128 else "latin-1", c["h"]))


# -- the registry: search functions, lookup, encode/decode, the C API, error handlers --

REG_NAMES = ["", "a", "B c", "x-Y_z", "\xc9t\xe9", "a b-C", "Q", "longname" * 30, "€€" * 120]


def reg_names(rng, tag):
    """A few names under the case's tag, so no other case's cache entries interfere."""
    out = []
    for _ in range(rng.randint(1, 3)):
        n = tag + rng.choice(REG_NAMES)
        if rng.random() < 0.3:
            n = n.upper()
        out.append(n)
    return out


def reg_norm(name):
    """normalizestring, for the generator only: which normalized name a rule answers."""
    return "".join("-" if ch == " " else (ch.lower() if ch.isascii() else ch) for ch in name)


def reg_ret(rng, ninfo):
    r = rng.random()
    if r < 0.35 and ninfo:
        return {"t": "info", "i": rng.randrange(ninfo)}
    if r < 0.7:
        return {"t": "none"}
    if r < 0.85:
        return {"t": "bad", "form": rng.randrange(4)}
    return {"t": "raise"}


def reg_ops(rng, nfuncs):
    if rng.random() < 0.8:
        return []
    return [{"t": rng.choice(["reg", "unreg", "unreg"]), "f": rng.randrange(nfuncs)} for _ in range(rng.randint(1, 3))]


def reg_coder(rng):
    r = rng.random()
    if r < 0.45:
        return {"t": "nargs"}
    if r < 0.75:
        v = rng.choice([{"k": "bytes", "v": [120, 255]}, {"k": "str", "v": [233]}, {"k": "bytearray", "v": [1]},
                        {"k": "int", "v": 7}])
        return {"t": "pair", "v": v}
    if r < 0.88:
        return {"t": "bad", "form": rng.randrange(3)}
    return {"t": "raise"}


@gen("codecs", 6)
def gen_codecs_registry(rng):
    tag = "uoc" + "".join(rng.choice("abcdefghij") for _ in range(10))
    names = reg_names(rng, tag) + [tag + "nope"]
    ncoders = rng.randint(1, 4)
    coders = [reg_coder(rng) for _ in range(ncoders)]
    ninfo = rng.randint(0, 3)
    infos = []
    for _ in range(ninfo):
        kind = rng.choice(["ci", "ci", "ci", "tuple", "sub"])
        info = {"kind": kind, "items": [rng.randrange(ncoders) for _ in range(4)]}
        if kind == "ci":
            info["ie"] = rng.choice([None, rng.randrange(ncoders)])
            info["id"] = rng.choice([None, rng.randrange(ncoders)])
            info["text"] = rng.choice([None, None, True, False, False, "raise"])
        infos.append(info)
    nfuncs = rng.randint(1, 3)
    funcs = []
    for _ in range(nfuncs):
        rules = [[cps_of(reg_norm(n)), reg_ret(rng, ninfo), reg_ops(rng, nfuncs)]
                 for n in rng.sample(names, rng.randint(0, len(names)))]
        funcs.append({"rules": rules, "default": {"t": "none"} if rng.random() < 0.8 else reg_ret(rng, ninfo),
                      "dops": reg_ops(rng, nfuncs)})
    steps = []
    for f in range(nfuncs):
        if rng.random() < 0.85:
            steps.append({"t": "register", "f": f})
    for _ in range(rng.randint(1, 7)):
        r = rng.random()
        name = cps_of(rng.choice(names))
        if r < 0.25:
            steps.append({"t": "lookup", "name": name})
        elif r < 0.35:
            steps.append({"t": rng.choice(["register", "unregister"]), "f": rng.randrange(nfuncs)})
        elif r < 0.38:
            steps.append({"t": "register", "bad": True})
        elif r < 0.55:
            steps.append({"t": rng.choice(["encode", "decode"]), "name": name,
                          "errors": rng.choice([None, cps_of("strict"), cps_of("uoc\xe9")])})
        elif r < 0.68:
            steps.append({"t": rng.choice(["strencode", "bytesdecode"]), "name": name,
                          "errors": rng.choice([None, cps_of("strict")])})
        elif r < 0.73:
            steps.append({"t": "known", "name": name})
        elif r < 0.79:
            steps.append({"t": "pyget", "which": rng.choice(["encoder", "decoder", "incenc", "incdec", "reader",
                                                             "writer"]),
                          "name": name, "errors": rng.choice([None, cps_of("strict")])})
        elif r < 0.85:
            steps.append({"t": "capi", "which": rng.choice(["Encoder", "Decoder", "IncrementalEncoder",
                                                            "IncrementalDecoder", "StreamReader", "StreamWriter"]),
                          "name": name, "errors": rng.choice([None, cps_of("strict")])})
        else:
            en = rng.choice(["strict", "ignore", tag, tag + "h", "\xe9" * 250 + tag])
            steps.append({"t": rng.choice(["regerr", "lookuperr", "unregerr"]), "name": en,
                          "h": rng.choice([0, 1, "bad"])})
    return {"mod": "unicodeobj", "fn": "codecs_registry", "tag": tag, "coders": coders, "infos": infos,
            "funcs": funcs, "steps": steps}


class RegBadBool:
    def __bool__(self):
        raise ValueError("bad bool")


class RegTupleSub(tuple):
    pass


def reg_val(v):
    k = v["k"]
    return {"bytes": lambda: bytes(v["v"]), "str": lambda: s_of(v["v"]), "bytearray": lambda: bytearray(v["v"]),
            "int": lambda: v["v"]}[k]()


@run("codecs_registry")
def run_codecs_registry(c):
    import codecs
    import ctypes
    import _codecs
    import warnings
    ids = []  # (object, id): the identities the model knows

    def make_coder(spec):
        def coder(*args):
            t = spec["t"]
            if t == "nargs":
                return len(args)
            if t == "pair":
                return (reg_val(spec["v"]), 0)
            if t == "bad":
                return ["x", (1,), (1, 2, 3)][spec["form"]]
            raise ValueError("boom")
        return coder
    coders = [make_coder(s) for s in c["coders"]]
    for i, f in enumerate(coders):
        ids.append((f, 200 + i))
    infos = []
    for i, info in enumerate(c["infos"]):
        items = [coders[j] for j in info["items"]]
        if info["kind"] == "ci":
            text = info["text"]
            kw = {} if text is None else {"_is_text_encoding": RegBadBool() if text == "raise" else text}
            obj = codecs.CodecInfo(*items, incrementalencoder=None if info["ie"] is None else coders[info["ie"]],
                                   incrementaldecoder=None if info["id"] is None else coders[info["id"]],
                                   name=c["tag"], **kw)
        elif info["kind"] == "tuple":
            obj = tuple(items)
        else:
            obj = RegTupleSub(items)
        infos.append(obj)
        ids.append((obj, 100 + i))
    funcs = []
    live = [True]
    nreg = [0]  # registrations made, so the cleanup can undo every one

    def reg(f):
        codecs.register(f)
        nreg[0] += 1

    def run_ops(ops):
        for op in ops:
            (reg if op["t"] == "reg" else codecs.unregister)(funcs[op["f"]])

    def ret(r):
        t = r["t"]
        if t == "none":
            return None
        if t == "info":
            return infos[r["i"]]
        if t == "bad":
            return [(1, 2, 3), (1, 2, 3, 4, 5), [1, 2, 3, 4], "x"][r["form"]]
        raise ValueError("search failed")

    def make_search(spec):
        def search(name):
            if not live[0]:
                return None
            for rn, r, ops in spec["rules"]:
                if name == s_of(rn):
                    run_ops(ops)
                    return ret(r)
            run_ops(spec["dops"])
            return ret(spec["default"])
        return search
    for i, spec in enumerate(c["funcs"]):
        funcs.append(make_search(spec))
        ids.append((funcs[-1], 1 + i))
    handlers = [lambda e: ("", e.end), lambda e: ("?", e.end)]
    for i, h in enumerate(handlers):
        ids.append((h, 300 + i))

    def enc(v):
        for o, i in ids:
            if v is o:
                return {"id": i}
        if v is None:
            return {"none": 1}
        if isinstance(v, bool):
            return {"int": int(v)}
        if isinstance(v, int):
            return {"int": v}
        if type(v) is str:
            return {"str": cps_of(v)}
        if type(v) is bytes:
            return {"bytes": list(v)}
        if type(v) is bytearray:
            return {"bytearray": list(v)}
        return {"other": type(v).__name__}

    def opt(x):
        return None if x is None else s_of(x)

    api = ctypes.pythonapi
    out = []
    saved = {n: codecs.lookup_error(n) for n in ("strict", "ignore")}
    # a clean cache: unregistering a registered function clears it
    probe = lambda name: None
    codecs.register(probe)
    codecs.unregister(probe)
    try:
        for st in c["steps"]:
            t = st["t"]
            try:
                if t == "register":
                    r = codecs.register(5) if st.get("bad") else reg(funcs[st["f"]])
                elif t == "unregister":
                    r = codecs.unregister(funcs[st["f"]])
                elif t == "lookup":
                    r = codecs.lookup(s_of(st["name"]))
                elif t in ("encode", "decode"):
                    f = codecs.encode if t == "encode" else codecs.decode
                    args = {"encoding": s_of(st["name"])}
                    if st["errors"] is not None:
                        args["errors"] = s_of(st["errors"])
                    r = f("abc", **args)
                elif t in ("strencode", "bytesdecode"):
                    with warnings.catch_warnings():
                        warnings.simplefilter("ignore")
                        if t == "strencode":
                            r = "abc".encode(s_of(st["name"]), *([] if st["errors"] is None else [s_of(st["errors"])]))
                        else:
                            r = b"abc".decode(s_of(st["name"]), *([] if st["errors"] is None else [s_of(st["errors"])]))
                elif t == "known":
                    fn = api.PyCodec_KnownEncoding
                    fn.restype, fn.argtypes = ctypes.c_int, [ctypes.c_char_p]
                    r = fn(s_of(st["name"]).encode())
                elif t == "capi":
                    w = st["which"]
                    fn = getattr(api, "PyCodec_" + w)
                    fn.restype = ctypes.py_object
                    name = s_of(st["name"]).encode()
                    err = None if st["errors"] is None else s_of(st["errors"]).encode()
                    if w in ("Encoder", "Decoder"):
                        fn.argtypes = [ctypes.c_char_p]
                        r = fn(name)
                    elif w.startswith("Incremental"):
                        fn.argtypes = [ctypes.c_char_p, ctypes.c_char_p]
                        r = fn(name, err)
                    else:
                        fn.argtypes = [ctypes.c_char_p, ctypes.py_object, ctypes.c_char_p]
                        r = fn(name, b"stream", err)
                elif t == "pyget":
                    w, name = st["which"], s_of(st["name"])
                    eargs = [] if st["errors"] is None else [s_of(st["errors"])]
                    if w == "encoder":
                        r = codecs.getencoder(name)
                    elif w == "decoder":
                        r = codecs.getdecoder(name)
                    elif w in ("incenc", "incdec"):
                        f = (codecs.getincrementalencoder if w == "incenc" else codecs.getincrementaldecoder)(name)
                        r = f(*eargs)
                    else:
                        f = (codecs.getreader if w == "reader" else codecs.getwriter)(name)
                        r = f(b"stream", *eargs)
                elif t == "regerr":
                    r = codecs.register_error(st["name"], 5 if st["h"] == "bad" else handlers[st["h"]])
                elif t == "lookuperr":
                    r = codecs.lookup_error(st["name"])
                else:
                    r = _codecs._unregister_error(st["name"])
                out.append({"ok": enc(r)})
            except Exception as x:
                out.append({"exc": type(x).__name__, "msg": str(x) if not isinstance(x, AttributeError) else "~",
                            "notes": getattr(x, "__notes__", [])})
    finally:
        live[0] = False
        for f in funcs:
            for _ in range(nreg[0]):
                codecs.unregister(f)
        for name in (c["tag"], c["tag"] + "h", "\xe9" * 250 + c["tag"]):
            _codecs._unregister_error(name)
        for n, h in saved.items():
            codecs.register_error(n, h)
    return out

@gen("codecs", 2)
def gen_codecs_normalize(rng):
    pool = list("aZ09._- ;#\x00") + ["\xe9", "\u20ac", "\ud800", "\U0001f600", "\x7f", "\t"]
    s = "".join(rng.choice(pool) for _ in range(rng.randint(0, 9)))
    return {"mod": "unicodeobj", "fn": "codecs_normalize", "s": cps_of(s)}


@run("codecs_normalize")
def run_codecs_normalize(c):
    import _codecs
    return cps_of(_codecs._normalize_encoding(s_of(c["s"])))


@gen("codecs", 2)
def gen_codecs_escape(rng):
    if rng.random() < 0.5:
        b = [rng.randrange(256) for _ in range(rng.randint(0, 8))]
    else:
        b = list(b"".join(rng.choice([b"\\", b"\\x4", b"\\x41", b"\\n", b"\\'", b"a", b"\\7", b"\\777", b"\\q",
                                       b"\\", b"\\xzz", b"\xff"]) for _ in range(rng.randint(0, 5))))
    return {"mod": "unicodeobj", "fn": "codecs_escape", "b": b, "enc": rng.random() < 0.5,
            "errors": rng.choice([None, "strict", "ignore", "replace", "bogus"])}


@run("codecs_escape")
def run_codecs_escape(c):
    import codecs
    import warnings
    if c["enc"]:
        r, n = codecs.escape_encode(bytes(c["b"]))
    else:
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            r, n = codecs.escape_decode(bytes(c["b"]), c["errors"])
    return [list(r), n]

# ==== end codecs.c ====


# The size cap. The model builds its output as a list, so a case that asks for a huge result
# (a large width, a large repeat) can take hundreds of GB in pydiff, where CPython would raise
# MemoryError at once. Every generated case passes through size_ok, and one that could
# produce more than SIZE_CAP characters is dropped. Numbers above sys.maxsize stay in: they fail
# the conversion to Py_ssize_t, which is the behaviour being tested.
SIZE_CAP = 1 << 20


def number_ok(v):
    return abs(v) <= SIZE_CAP or abs(v) > sys.maxsize


def digit_runs(s):
    """The values of the runs of decimal digits in s, with whether a '.' precedes each."""
    runs, cur, dotted = [], "", False
    for i, ch in enumerate(s + " "):
        if unicodedata.decimal(ch, None) is not None:
            if not cur:
                dotted = i > 0 and s[i - 1] == "."
            cur += ch
        elif cur:
            runs.append((int(cur), dotted))
            cur = ""
    return runs


def size_ok(c):
    fn = c["fn"]
    if fn == "meth_pad":
        # Above the cap only widths PyUnicode_New refuses at once (>= sys.maxsize) stay in.
        v = me_width_value(c["width"])
        return v <= SIZE_CAP or v >= sys.maxsize
    if fn == "obj_repeat":
        n, length = c["n"], len(c["s"])
        return n <= 0 or length * n <= SIZE_CAP or (length > 0 and length * n > sys.maxsize)
    if fn in ("fmt_int", "fmt_str", "fmt_float", "fmt_complex"):
        # A precision pads a float, or an int given a float type, with zeros. Above INT_MAX it
        # is an error, which is the behaviour being tested.
        return all(number_ok(v) if not dotted else (v <= SIZE_CAP or v > 2 ** 31 - 1)
                   for v, dotted in digit_runs(s_of(c["spec"])))
    if fn == "fmt_percent":
        fmt = s_of(c["fmt"])
        # A precision above INT_MAX is refused, and so is one %d cannot pad: nothing gets built.
        if not all(number_ok(v) if not dotted else
                   v <= SIZE_CAP or v > 2 ** 31 - 1 or (v == 2 ** 31 - 1 and fmt.endswith("d"))
                   for v, dotted in digit_runs(fmt)):
            return False
        items = c["args"].get("items", [c["args"].get("item")])
        ints = [pct_dec(o) for o in items if c["args"]["k"] == "tuple" and o["t"] == "int"]
        only_prec = fmt.count("*") == fmt.count(".*")
        return "*" not in fmt or all(number_ok(v) or (only_prec and abs(v) >= 2 ** 31) for v in ints)
    return True


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
            c = f(rng)
            break
    else:
        c = active[-1][1](rng)
    return c if c is None or size_ok(c) else None


def run_python(case):
    return common.py_result(lambda: RUNS[case["fn"]](case))


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=20000)
