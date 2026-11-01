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
    return cps_of(format(v, s_of(c["spec"])))


@run("fmt_str")
def run_fmt_str(c):
    return cps_of(format(s_of(c["s"]), s_of(c["spec"])))


@run("fmt_float")
def run_fmt_float(c):
    return cps_of(format(float_of(c["x"]), s_of(c["spec"])))


@run("fmt_complex")
def run_fmt_complex(c):
    return cps_of(format(complex(float_of(c["re"]), float_of(c["im"])), s_of(c["spec"])))

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
        if not all(number_ok(v) for v, _ in digit_runs(fmt)):
            return False
        items = c["args"].get("items", [c["args"].get("item")])
        ints = [pct_dec(o) for o in items if c["args"]["k"] == "tuple" and o["t"] == "int"]
        return "*" not in fmt or all(number_ok(v) for v in ints)
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
