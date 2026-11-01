"""Differential test: Lean model of json (C and pure-Python twins) vs. the running CPython.

Usage: python3 difftest/json_diff.py [--cases N] [--seed S]

`..._c` cases run the C accelerator (`_json`): `json.JSONDecoder` with the C
scanner, `json.dumps` with `c_make_encoder`. `..._py` cases run the pure-Python
module from `import_fresh_module('json', blocked=['_json'])`. Decoding uses
`parse_float` and `parse_constant` hooks that record the matched text, except in
the `api_*` cases, which call `json.loads` as is and compare a `float` result
only as being a float (`float()` is not modelled). The other cases call
`json.dumps`, `dump`, `load`, `detect_encoding`, `JSONDecodeError`, `iterencode`,
`scanstring`, `encode_basestring(_ascii)`, the C `make_encoder` and `make_scanner`
directly, and `json.tool.main` with patched streams. Exits non-zero on any
mismatch. See difftest/common.py.
"""

import io
import json
import json.tool
import math
import random
import struct
import sys
import types
import warnings

from test.support.import_helper import import_fresh_module

import common

with warnings.catch_warnings():
    warnings.simplefilter("ignore")
    pyjson = import_fresh_module("json", blocked=["_json"])
assert pyjson.decoder.scanstring is pyjson.decoder.py_scanstring
assert pyjson.scanner.make_scanner is pyjson.scanner.py_make_scanner
assert pyjson.encoder.c_make_encoder is None
assert json.scanner.make_scanner is not json.scanner.py_make_scanner

IMPL = {"py": pyjson, "c": json}


class Hook:
    __slots__ = ("kind", "t")

    def __init__(self, kind, t):
        self.kind, self.t = kind, t


class Pairs:
    __slots__ = ("ps",)

    def __init__(self, ps):
        self.ps = ps


def cps(s):
    return [ord(ch) for ch in s]


def conv(v):
    if v is None or v is True or v is False:
        return v
    if type(v) is float:
        return {"float": 1}
    if type(v) is int:
        return {"int": str(v)}
    if type(v) is str:
        return {"s": cps(v)}
    if type(v) is Hook:
        return {"hook": v.kind, "t": cps(v.t)}
    if type(v) is list:
        return [conv(x) for x in v]
    if type(v) is Pairs:
        return {"obj": [[cps(k), conv(x)] for k, x in v.ps]}
    if type(v) is dict:
        return {"obj": [[cps(k), conv(x)] for k, x in v.items()]}
    raise AssertionError(type(v))


# ---------------------------------------------------------------- generation

STR_CH = ["a", "Z", "0", " ", "é", "€", "\U0001d11e", "\ud834", "\udd1e", "\udbff", "\udc00",
          "\x00", "\x01", "\x1f", "\x7f", "\x80", "\t", "\n", "\r", "\b", "\f", '"', "\\", "/",
          "'", " ", "￿", "\U0010ffff", "\x0b"]
ESCAPES = ['\\"', "\\\\", "\\/", "\\b", "\\f", "\\n", "\\r", "\\t", "\\u0041", "\\u00e9", "\\u20AC",
           "\\ud834\\udd1e", "\\uD834\\uDD1E", "\\ud834", "\\udd1e", "\\udd1e\\ud834", "\\ud834\\u0041",
           "\\ud834\\ud834", "\\ud834\\u12", "\\ud834\\uzzzz", "\\ud834\\", "\\u12", "\\uXYZW", "\\u",
           "\\x", "\\'", "\\a", "\\U0001", "\\é", "\\\x01", "\\ ", "\\0", "\\u00", "\\u+123", "\\u 123",
           "\\u١٢٣٤", "\\uDBFF\\uDFFF", "\\udc00", "\\ud800\\udc00"]
NUMS = ["0", "-0", "1", "-1", "12", "007", "01", "-01", "1.5", "1.", ".5", "-.5", "1e5", "1E+5", "1e-5",
        "1e", "1e+", "1e-", "1.5e3", "0e0", "-", "--1", "+1", "1.e5", "123456789012345678901234567890",
        "0x10", "1_0", "١", "1.5.5", "1ee5", "2e308", "NaN", "Infinity", "-Infinity", "nan", "inf",
        "-NaN", "Infinityx", "-Inf", "NaNa"]
TOKENS = ["{", "}", "[", "]", ",", ":", '"', " ", "\t", "\n", "\r", "\x0b", "\xa0", "null", "true",
          "false", "nul", "tru", "fals", "nulls", "\\", "\x00", "x"] + NUMS


def rand_text(rng, n):
    out = []
    for _ in range(n):
        r = rng.random()
        if r < 0.55:
            out.append(rng.choice(STR_CH))
        else:
            out.append(rng.choice(ESCAPES))
    return "".join(out)


def big_int_text(rng):
    k = rng.choice([4299, 4300, 4301, 4302, 5000])
    return rng.choice(["", "-"]) + "1" + "0" * (k - 1)


def rand_ws(rng):
    if rng.random() < 0.6:
        return ""
    return "".join(rng.choice([" ", "\t", "\n", "\r", "\n\n", "  "]) for _ in range(rng.randint(1, 3)))


def rand_doc(rng, depth=0):
    """Mostly valid JSON text."""
    k = rng.random()
    if depth > 4 or k < 0.45:
        r = rng.random()
        if r < 0.3:
            return '"' + rand_text(rng, rng.randint(0, 5)) + '"'
        if r < 0.55:
            return rng.choice(NUMS[:12] + ["123", "-45", "9" * 30, "0", "6.02e23", "NaN", "Infinity", "-Infinity"])
        if r < 0.58:
            return big_int_text(rng)
        return rng.choice(["null", "true", "false", "[]", "{}"])
    w = lambda: rand_ws(rng)
    if k < 0.75:
        items = [rand_doc(rng, depth + 1) for _ in range(rng.randint(0, 4))]
        return "[" + w() + (w() + "," + w()).join(items) + w() + "]"
    keys = ['"' + rand_text(rng, rng.randint(0, 3)) + '"' for _ in range(rng.randint(0, 4))]
    if keys and rng.random() < 0.3:
        keys.append(rng.choice(keys))  # duplicate key
    items = [k_ + w() + ":" + w() + rand_doc(rng, depth + 1) for k_ in keys]
    return "{" + w() + ("," + w()).join(items) + w() + "}"


def mutate(rng, s):
    s = list(s)
    for _ in range(rng.randint(1, 3)):
        op, i = rng.random(), rng.randrange(len(s) + 1)
        tok = rng.choice(TOKENS + STR_CH)
        if op < 0.35 and s:
            del s[min(i, len(s) - 1)]
        elif op < 0.7:
            s.insert(i, tok)
        elif s:
            s[min(i, len(s) - 1)] = tok
    return "".join(s)


def gen_doc(rng):
    r = rng.random()
    if r < 0.12:
        return "".join(rng.choice(TOKENS + STR_CH + ESCAPES) for _ in range(rng.randint(0, 8)))
    if r < 0.2:
        return '"' + rand_text(rng, rng.randint(0, 6)) + rng.choice(['"', "", '"x', '" ', "\\"])
    if r < 0.25:
        d = rng.randint(1, 25)
        return "[" * d + rng.choice(["1", "", "{}", '{"a":1}']) + "]" * rng.choice([d, d - 1, 0])
    s = rand_ws(rng) + rand_doc(rng) + rand_ws(rng)
    if rng.random() < 0.4:
        s = mutate(rng, s)
    if rng.random() < 0.1:
        s += rng.choice(["x", " 1", "]", "}", ",", "\x00", "null"])
    return s


def gen_idx(rng, s):
    n = len(s)
    return rng.choice([0, 0, 1, n, n - 1, n + 1, -1, -2, -n, -n - 1, rng.randint(-n - 2, n + 2),
                       rng.randint(-n - 2, n + 2), 2**63 - 1, 2**63, -2**63, -2**63 - 1, 2**64, -2**100])


# encoder values

KEY_STRS = ["", "a", "b", "é", "\ud834", "\U0001d11e", '"', "\\", "\x00", "\n", "aa", "B", "true", "1"]
FLOATS = [0.0, -0.0, 1.0, -1.5, 0.1, 1e22, 1e16, 1e-5, 1.7976931348623157e308, 5e-324, 2.5, 1e300,
          math.inf, -math.inf, math.nan, -math.nan]


def fbits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


class Obj:
    """An object `default()` is called on."""

    def __init__(self, n, ret):
        self.n, self.ret = n, ret


OBJS = {}


def new_obj(rng, depth, ancestors):
    n = len(OBJS)
    o = Obj(n, None)
    OBJS[n] = o
    r = rng.random()
    if r < 0.15:
        o.ret = BOOM
    elif r < 0.25:
        o.ret = [o]  # default() returns a container holding the object itself
    elif r < 0.35 and n:
        o.ret = OBJS[rng.randrange(n)]
    else:
        o.ret = rand_val(rng, depth + 1, [])
    return o


BOOM = object()


def rand_key(rng):
    r = rng.random()
    if r < 0.6:
        return rng.choice(KEY_STRS) if rng.random() < 0.7 else rand_text(rng, 2)
    if r < 0.75:
        return rng.choice([0, 1, -1, 2, 10**20, -(10**20), 7])
    if r < 0.82:
        return rng.choice([True, False])
    if r < 0.86:
        return None
    if r < 0.9:
        return 10 ** 4300 * rng.choice([1, -1])
    if r < 0.95:
        return rng.choice(FLOATS[:-2])  # NaN keys make `sorted` order-dependent
    return (rng.randint(-2, 2),)


def rand_val(rng, depth, ancestors):
    k = rng.random()
    if ancestors and k < 0.03:
        return ancestors[rng.randrange(len(ancestors))]
    if depth > 3 or k < 0.5:
        r = rng.random()
        if r < 0.3:
            return "".join(rng.choice(STR_CH) for _ in range(rng.randint(0, 5)))
        if r < 0.55:
            return rng.choice([0, 1, -1, 2**63, -2**63, 2**64, 10**30, 123, -7])
        if r < 0.57:
            return 10 ** rng.choice([4299, 4300]) * rng.choice([1, -1])
        if r < 0.6:
            return b"x"
        if r < 0.72:
            return rng.choice(FLOATS)
        if r < 0.76 and depth < 3:
            return new_obj(rng, depth, ancestors)
        return rng.choice([None, True, False])
    if k < 0.75:
        lst = []
        for _ in range(rng.randint(0, 4)):
            lst.append(rand_val(rng, depth + 1, ancestors + [lst]))
        return lst
    d = {}
    for _ in range(rng.randint(0, 4)):
        d[rand_key(rng)] = rand_val(rng, depth + 1, ancestors + [d])
    return d


def istr(n):
    old = sys.get_int_max_str_digits()
    sys.set_int_max_str_digits(0)
    try:
        return str(n)
    finally:
        sys.set_int_max_str_digits(old)


def enc_key(k):
    if k is None:
        return None
    if k is True or k is False:
        return {"b": k}
    if type(k) is int:
        return {"i": istr(k)}
    if type(k) is str:
        return {"s": cps(k)}
    if type(k) is tuple:
        return {"t": str(k[0])}
    if type(k) is float:
        return {"f": str(fbits(k)), "r": cps(repr(k))}
    raise AssertionError(k)


def enc_val(v, ancestors):
    for i, a in enumerate(reversed(ancestors)):
        if v is a:
            return {"back": i}
    if v is None or v is True or v is False:
        return v
    if type(v) is int:
        return {"i": istr(v)}
    if type(v) is str:
        return {"s": cps(v)}
    if type(v) is float:
        return {"f": str(fbits(v)), "r": cps(repr(v))}
    if type(v) is bytes:
        return {"other": 10**6, "t": "bytes"}
    if type(v) is Obj:
        return {"other": v.n, "t": "Obj"}
    if type(v) is list:
        return {"l": [enc_val(x, ancestors + [v]) for x in v]}
    if type(v) is dict:
        return {"d": [[enc_key(k), enc_val(x, ancestors + [v])] for k, x in v.items()]}
    raise AssertionError(type(v))


INT_MAX_STR = sys.get_int_max_str_digits()
if INT_MAX_STR != 4300:
    sys.set_int_max_str_digits(4300)

VALUES = {}  # case id -> Python object (cycles cannot travel as JSON)


def objs_of(v, seen=None):
    """The `Obj`s reachable from `v`, through `default()` too."""
    seen = {} if seen is None else seen
    visited = set()

    def go(x):
        if id(x) in visited:
            return
        visited.add(id(x))
        if type(x) is Obj:
            seen[x.n] = x
            if x.ret is not BOOM:
                go(x.ret)
        elif type(x) is list:
            for y in x:
                go(y)
        elif type(x) is dict:
            for y in x.values():
                go(y)

    go(v)
    return seen


def dflt_table(v):
    out = []
    for n, o in objs_of(v).items():
        out.append([n, None if o.ret is BOOM else {"v": enc_val(o.ret, [])}])
    return out


def py_default(o):
    if type(o) is Obj:
        if o.ret is BOOM:
            raise ValueError("boom")
        return o.ret
    raise TypeError(f"Object of type {type(o).__name__} is not JSON serializable")


def has_cycle(v):
    """Is a repeat possible on some path (`back`, or an `Obj` under itself)?"""

    def go(x, path):
        if id(x) in path:
            return True
        if type(x) is Obj:
            return x.ret is not BOOM and go(x.ret, path | {id(x)})
        if type(x) is list:
            return any(go(y, path | {id(x)}) for y in x)
        if type(x) is dict:
            return any(go(y, path | {id(x)}) for y in x.values())
        return False

    return go(v, frozenset())


def enc_opts(rng):
    v = rand_val(rng, 0, [])
    indent = rng.choice([None, None, 0, 2, -1, "\t", "", " \n", "--"])
    seps = rng.choice([None, None, (",", ":"), (" , ", " : "), ("\n,", ":\t"), (";", "=")])
    kw = dict(ensure_ascii=rng.random() < 0.5, check_circular=rng.random() < 0.7, allow_nan=rng.random() < 0.7,
              sort_keys=rng.random() < 0.4, skipkeys=rng.random() < 0.4, indent=indent, separators=seps)
    if not kw["check_circular"] and has_cycle(v):
        # A cycle without check_circular recurses until RecursionError; with an
        # indent the C encoder's indent cache grows quadratically on the way
        # (bugs/json-indent-recursion-memory.yaml), so keep those cases compact.
        indent = kw["indent"] = None
    return v, kw


def base_case(fn, v, kw, use_default=True):
    indent = kw["indent"]
    seps = kw["separators"]
    eff_indent = None if indent is None else (" " * indent if type(indent) is int else indent)
    if seps is None:
        seps = (", ", ": ") if indent is None else (",", ": ")
    key = len(VALUES)
    VALUES[key] = (v, kw)
    return {"mod": "json", "fn": fn, "v": enc_val(v, []), "key": key, "dflt": dflt_table(v) if use_default else [],
            "ensure_ascii": kw["ensure_ascii"], "check_circular": kw["check_circular"],
            "allow_nan": kw["allow_nan"], "sort_keys": kw["sort_keys"], "skipkeys": kw["skipkeys"],
            "indent": None if eff_indent is None else cps(eff_indent),
            "item_sep": cps(seps[0]), "key_sep": cps(seps[1])}


def api_args(rng, v, kw):
    """`json.dumps`/`dump` keyword arguments, often at their defaults."""
    a = {}
    for k, dv in [("skipkeys", False), ("ensure_ascii", True), ("check_circular", True), ("allow_nan", True),
                  ("sort_keys", False)]:
        a[k] = kw[k] if rng.random() < 0.4 else dv
    a["indent"] = kw["indent"] if rng.random() < 0.4 else None
    a["separators"] = kw["separators"] if rng.random() < 0.4 else None
    if not a["check_circular"] and has_cycle(v):
        a["indent"] = None
    return a


def indent_json(i):
    return None if i is None else {"i": str(i)} if type(i) is int else {"s": cps(i)}


def bytes_doc(rng):
    r = rng.random()
    if r < 0.25:
        return bytes(rng.choice([0, 0, 1, 34, 123, 0x7f, 0x80, 0xbf, 0xc0, 0xc2, 0xe0, 0xed, 0xef, 0xbb, 0xf0, 0xf4,
                                 0xf5, 0xfe, 0xff]) for _ in range(rng.randint(0, 9)))
    s = gen_doc(rng)
    enc = rng.choice(["utf-8", "utf-8-sig", "utf-16", "utf-16-le", "utf-16-be", "utf-32", "utf-32-le", "utf-32-be"])
    b = s.encode(enc, "surrogatepass")
    if rng.random() < 0.2 and b:
        i = rng.randrange(len(b))
        b = b[:i] + rng.choice([b"", b"\x00", b"\xff", b"\xd8", b"\xdc"]) + b[i + 1:]
    return b


def load_arg(rng):
    r = rng.random()
    if r < 0.55:
        s = gen_doc(rng)
        if rng.random() < 0.05:
            s = "﻿" + s
        return {"s": cps(s)}
    if r < 0.93:
        return {"b": list(bytes_doc(rng))}
    return {"other": rng.choice(["int", "NoneType", "list", "float"])}


def gen_scan_arg(rng):
    if rng.random() < 0.05:
        return {"other": rng.choice(["int", "bytes", "NoneType"])}, ""
    s = gen_doc(rng)
    return {"s": cps(s)}, s


def tool_text(rng):
    r = rng.random()
    if r < 0.5:
        return "\n".join(gen_doc(rng) for _ in range(rng.randint(0, 3))) + rng.choice(["", "\n"])
    return json.dumps(rand_val_json(rng, 0), ensure_ascii=rng.random() < 0.5)


def rand_val_json(rng, depth):
    k = rng.random()
    if depth > 2 or k < 0.5:
        return rng.choice([None, True, False, 0, 1.5, "a\ud834", "é", -1, "x"])
    if k < 0.75:
        return [rand_val_json(rng, depth + 1) for _ in range(rng.randint(0, 3))]
    return {rng.choice(["a", "b", "c", "é"]): rand_val_json(rng, depth + 1) for _ in range(rng.randint(0, 3))}


def float_table(text):
    """`[text, bits, repr]` for every float and constant the text mentions."""
    seen = {}

    def rec(t):
        if t not in seen:
            seen[t] = float(t)
        return 0

    for piece in (text.splitlines() or [text]) + [text]:
        try:
            json.loads(piece, parse_float=rec, parse_constant=rec)
        except Exception:
            pass
    return [[cps(t), str(fbits(x)), cps(repr(x))] for t, x in seen.items()]


CTX_ATTRS = ["strict", "object_hook", "object_pairs_hook", "parse_float", "parse_int", "parse_constant"]


def gen_case(rng):
    impl = rng.choice(["py", "c"])
    r = rng.random()
    if r < 0.32:
        s = gen_doc(rng)
        c = {"mod": "json", "s": cps(s), "strict": rng.random() < 0.7,
             "ohook": rng.choice([0, 0, 1, 2, 3]), "phook": rng.choice([0, 0, 0, 1, 2, 3]),
             "pint": rng.choice([0, 0, 0, 1, 2, 3]), "pfloat": rng.choice([0, 0, 0, 2, 3]),
             "pconst": rng.choice([0, 0, 0, 2, 3])}
        if rng.random() < 0.7:
            c["fn"] = f"loads_{impl}"
        else:
            c["fn"] = f"raw_{impl}"
            c["idx"] = str(gen_idx(rng, s))
        return c
    if r < 0.52:
        v, kw = enc_opts(rng)
        return base_case(f"dumps_{impl}", v, kw)
    if r < 0.62:
        v, kw = enc_opts(rng)
        a = api_args(rng, v, kw)
        has_default = rng.random() < 0.5
        bad = rng.random() < 0.03
        c = {"mod": "json", "fn": f"api_dumps_{impl}", "v": enc_val(v, []), "dflt": dflt_table(v) if has_default else [],
             "has_default": int(has_default), "kw": ["frob"] if bad else []}
        c.update(skipkeys=a["skipkeys"], ensure_ascii=a["ensure_ascii"], check_circular=a["check_circular"],
                 allow_nan=a["allow_nan"], sort_keys=a["sort_keys"], indent=indent_json(a["indent"]),
                 seps=None if a["separators"] is None else [cps(a["separators"][0]), cps(a["separators"][1])])
        key = len(VALUES)
        VALUES[key] = (v, a)
        c["key"] = key
        return c
    if r < 0.70:
        v, kw = enc_opts(rng)
        if has_cycle(v) and not kw["check_circular"]:
            kw["check_circular"] = True  # the chunks before RecursionError depend on the limit
        if rng.random() < 0.5:
            return base_case("iter", v, kw)
        a = api_args(rng, v, kw)
        has_default = rng.random() < 0.5
        c = {"mod": "json", "fn": "api_dump", "v": enc_val(v, []), "dflt": dflt_table(v) if has_default else [],
             "has_default": int(has_default), "kw": [], "fail": rng.choice([-1, -1, 0, 1, 3])}
        c.update(skipkeys=a["skipkeys"], ensure_ascii=a["ensure_ascii"], check_circular=a["check_circular"],
                 allow_nan=a["allow_nan"], sort_keys=a["sort_keys"], indent=indent_json(a["indent"]),
                 seps=None if a["separators"] is None else [cps(a["separators"][0]), cps(a["separators"][1])])
        key = len(VALUES)
        VALUES[key] = (v, a)
        c["key"] = key
        return c
    if r < 0.80:
        c = {"mod": "json", "fn": rng.choice([f"api_loads_{impl}", "api_load"]), "arg": load_arg(rng),
             "ohook": rng.choice([0, 0, 0, 1, 2]), "phook": rng.choice([0, 0, 0, 1, 2]),
             "pfloat": rng.choice([0, 0, 0, 1, 2, 4]), "pint": rng.choice([0, 0, 0, 1, 2, 4]),
             "pconst": rng.choice([0, 0, 0, 1, 2, 4]), "strict": rng.choice([None, None, True, False]),
             "kw": ["frob"] if rng.random() < 0.03 else [], "read_fail": int(rng.random() < 0.05)}
        return c
    if r < 0.84:
        b = bytes_doc(rng)
        return {"mod": "json", "fn": rng.choice(["detect", "decode"]), "b": list(b)}
    if r < 0.87:
        doc = rand_text(rng, rng.randint(0, 6)) + rng.choice(["", "\n", "a\nb\n\nc"])
        n = len(doc)
        pos = rng.choice([0, 1, n, n - 1, n + 1, -1, -2, -n, -n - 1, rng.randint(-n - 2, n + 2)])
        return {"mod": "json", "fn": "jde", "msg": rng.choice(["m", "Expecting value", ""]), "doc": cps(doc), "pos": str(pos)}
    if r < 0.91:
        x, s = gen_scan_arg(rng)
        strict = rng.random() < 0.7
        if rng.random() < 0.5:
            s = '"' + rand_text(rng, rng.randint(0, 5)) + rng.choice(['"', "", '"x'])
            x = {"s": cps(s)}
        n = len(s)
        e = rng.choice([1, 1, 1, 0, n, n - 1, n + 1, -1, 2**63 - 1, 2**63, -2**63 - 1, rng.randint(0, n + 1)])
        if impl == "py":
            return {"mod": "json", "fn": "scanstr_py", "s": cps(s), "end": str(e), "strict": strict}
        return {"mod": "json", "fn": "scanstr_c", "x": x, "end": str(e), "strict": strict}
    if r < 0.93:
        ascii_ = rng.random() < 0.5
        s = rand_text(rng, rng.randint(0, 6))
        if impl == "py" or rng.random() < 0.9:
            return {"mod": "json", "fn": f"encstr_{impl}", "ascii": ascii_, "s": cps(s), "x": {"s": cps(s)}}
        return {"mod": "json", "fn": "encstr_c", "ascii": ascii_, "x": {"other": rng.choice(["int", "bytes"])}}
    if r < 0.95:
        x, s = gen_scan_arg(rng)
        return {"mod": "json", "fn": "scan_once", "x": x, "idx": str(gen_idx(rng, s)), "strict": rng.random() < 0.7,
                "pfloat": 0, "pconst": 0}
    if r < 0.96:
        attrs = [a for a in CTX_ATTRS if rng.random() < 0.9]
        return {"mod": "json", "fn": "scanner_new", "tp": "Ctx", "attrs": attrs, "strict_mode": rng.choice([0, 1, 2])}
    if r < 0.98:
        v, kw = enc_opts(rng)
        c = base_case("make_enc", v, kw)
        c["markers"] = rng.choice([0, 1, 1, 1, 2]) if kw["check_circular"] else 0
        if has_cycle(v):
            c["markers"] = 1 if kw["check_circular"] else 0
            c["indent"] = c["indent"] if kw["check_circular"] else None
        c["encoder"] = rng.choice([0, 1, 2, 3, 4])
        c["level"] = str(rng.choice([0, 0, 1, 3, 2**63, -2**63 - 1]))
        c["key_sep"] = {"s": c["key_sep"]} if rng.random() < 0.95 else {"other": "int"}
        c["item_sep"] = {"s": c["item_sep"]} if rng.random() < 0.95 else {"other": "int"}
        return c
    if r < 0.99:
        s = rng.choice([gen_doc(rng), tool_text(rng), rand_text(rng, 5)])
        return {"mod": "json", "fn": "colorize", "s": cps(s)}
    s = tool_text(rng)
    indent = rng.choice([4, 4, 0, 2, -1, "\t", None])
    return {"mod": "json", "fn": "tool", "s": cps(s), "sort_keys": rng.random() < 0.3,
            "ensure_ascii": rng.random() < 0.6, "json_lines": rng.random() < 0.4, "compact": rng.random() < 0.2,
            "indent": indent, "color": int(rng.random() < 0.3), "strict_out": rng.random() < 0.5,
            "floats": float_table(s)}


class Theme:
    reset = "</>"

    def __getitem__(self, c):
        return {"definition": "<K>", "string": "<S>", "number": "<N>", "keyword": "<W>"}[c]


class Sink(io.BytesIO):
    def close(self):
        pass


class Stream(io.StringIO):
    def close(self):
        pass


class Fp:
    def __init__(self, x=None, fail=-1):
        self.x, self.fail, self.chunks = x, fail, []

    def read(self):
        if self.fail == -2:
            raise OSError("no read")
        return self.x

    def write(self, c):
        if len(self.chunks) == self.fail:
            raise ValueError("write")
        self.chunks.append(c)


def run_tool(c):
    text = "".join(map(chr, c["s"]))
    argv = ["json.tool"]
    if c["sort_keys"]:
        argv.append("--sort-keys")
    if not c["ensure_ascii"]:
        argv.append("--no-ensure-ascii")
    if c["json_lines"]:
        argv.append("--json-lines")
    if c["compact"]:
        argv.append("--compact")
    elif c["indent"] is None:
        argv.append("--no-indent")
    elif c["indent"] == "\t":
        argv.append("--tab")
    else:
        argv.append(f"--indent={c['indent']}")
    old = sys.argv, sys.stdin, sys.stdout, json.tool.can_colorize, json.tool.get_theme
    out = Sink() if c["strict_out"] else Stream()
    stream = io.TextIOWrapper(out, encoding="utf-8", newline="\n") if c["strict_out"] else out
    if c["strict_out"]:
        stream.close = lambda: io.TextIOWrapper.flush(stream)
    sys.argv, sys.stdin, sys.stdout = argv, io.StringIO(text), stream
    json.tool.can_colorize = lambda file: bool(c["color"])
    json.tool.get_theme = lambda tty_file: types.SimpleNamespace(syntax=Theme())
    exc = msg = None
    try:
        json.tool.main()
    except SystemExit as e:
        exc, msg = "SystemExit", str(e.code)
        if "codec can't encode" in msg:
            msg = "~surrogate"
    finally:
        sys.argv, sys.stdin, sys.stdout, json.tool.can_colorize, json.tool.get_theme = old
    if c["strict_out"]:
        stream.flush()
        return {"ok": {"out": cps(out.getvalue().decode("utf-8")), "exc": exc, "msg": msg}}
    return {"ok": {"out": cps(out.getvalue()), "exc": exc, "msg": msg}}


def py_hook(m, tag):
    def rec(t):
        return [tag, t]

    def bad(t):
        raise ValueError("hook")

    def stop(t):
        raise StopIteration(3)

    class Falsy:
        def __call__(self, t):
            return t

        def __bool__(self):
            return False

    return {0: None, 1: rec, 2: bad, 3: stop, 4: Falsy()}[m]


def obj_hook(m, wrap):
    def bad(x):
        raise ValueError("hook")

    def stop(x):
        raise StopIteration(3)

    return {0: None, 1: wrap, 2: bad, 3: stop}[m]


def text_hook(m, kind, nonempty):
    def rec(t):
        return Hook(kind, t)

    def bad(t):
        raise ValueError("hook")

    def stop(t):
        raise StopIteration(3)

    return {0: rec if nonempty else None, 1: rec, 2: bad, 3: stop}[m]


def dec_of(m, c):
    return m.JSONDecoder(strict=c["strict"], parse_float=text_hook(c.get("pfloat", 0), "float", True),
                         parse_constant=text_hook(c.get("pconst", 0), "const", True),
                         parse_int=text_hook(c.get("pint", 0), "int", False),
                         object_hook=obj_hook(c.get("ohook", 0), lambda d: ["H", d]),
                         object_pairs_hook=obj_hook(c.get("phook", 0), Pairs))


def decode_arg(c):
    a = c["arg"]
    if "s" in a:
        return "".join(map(chr, a["s"]))
    if "b" in a:
        return bytes(a["b"])
    return {"int": 1, "NoneType": None, "list": [], "float": 1.5}[a["other"]]


def load_kw(c):
    kw = dict(object_hook=obj_hook(c["ohook"], lambda d: ["H", d]), object_pairs_hook=obj_hook(c["phook"], Pairs),
              parse_float=py_hook(c["pfloat"], "F"), parse_int=py_hook(c["pint"], "I"),
              parse_constant=py_hook(c["pconst"], "C"))
    if c["strict"] is not None:
        kw["strict"] = c["strict"]
    if c["kw"]:
        kw[c["kw"][0]] = 1
    return kw


def yield_result(chunks, exc):
    return {"ok": {"chunks": [cps(x) for x in chunks], "exc": exc}}


def str_arg(x):
    return "".join(map(chr, x["s"])) if "s" in x else {"int": 1, "bytes": b"", "NoneType": None}[x["other"]]


def run_python(c):
    fn = c["fn"]
    base, impl = fn.rsplit("_", 1) if "_" in fn else (fn, "c")
    m = IMPL.get(impl, json)
    try:
        if base in ("loads", "raw"):
            s = "".join(map(chr, c["s"]))
            dec = dec_of(m, c)
            if base == "loads":
                return {"ok": conv(dec.decode(s))}
            v, end = dec.raw_decode(s, int(c["idx"]))
            return {"ok": [conv(v), str(end)]}
        if fn == "scanstr_py":
            v, end = pyjson.decoder.py_scanstring("".join(map(chr, c["s"])), int(c["end"]), c["strict"])
            return {"ok": [cps(v), str(end)]}
        if fn == "scanstr_c":
            v, end = json.decoder.c_scanstring(str_arg(c["x"]), int(c["end"]), c["strict"])
            return {"ok": [cps(v), str(end)]}
        if fn == "encstr_py":
            f = pyjson.encoder.py_encode_basestring_ascii if c["ascii"] else pyjson.encoder.py_encode_basestring
            return {"ok": cps(f("".join(map(chr, c["s"]))))}
        if fn == "encstr_c":
            f = json.encoder.c_encode_basestring_ascii if c["ascii"] else json.encoder.c_encode_basestring
            return {"ok": cps(f(str_arg(c["x"])))}
        if base == "dumps":
            v, kw = VALUES[c["key"]]
            return {"ok": cps(m.dumps(v, default=py_default, **kw))}
        if base == "api_dumps":
            v, a = VALUES[c["key"]]
            a = dict(a)
            if c["has_default"]:
                a["default"] = py_default
            if c["kw"]:
                a[c["kw"][0]] = 1
            return {"ok": cps(m.dumps(v, **a))}
        if fn == "api_dump":
            v, a = VALUES[c["key"]]
            a = dict(a)
            if c["has_default"]:
                a["default"] = py_default
            fp = Fp(fail=c["fail"])
            try:
                json.dump(v, fp, **a)
                return yield_result(fp.chunks, None)
            except Exception as e:
                return yield_result(fp.chunks, type(e).__name__)
        if fn == "iter":
            v, kw = VALUES[c["key"]]
            chunks = []
            try:
                for x in json.JSONEncoder(default=py_default, **kw).iterencode(v):
                    chunks.append(x)
                return yield_result(chunks, None)
            except Exception as e:
                return yield_result(chunks, type(e).__name__)
        if base == "api_loads":
            return {"ok": conv(m.loads(decode_arg(c), **load_kw(c)))}
        if fn == "api_load":
            return {"ok": conv(json.load(Fp(decode_arg(c), -2 if c["read_fail"] else -1), **load_kw(c)))}
        if fn == "detect":
            return {"ok": json.detect_encoding(bytes(c["b"]))}
        if fn == "decode":
            b = bytes(c["b"])
            return {"ok": cps(b.decode(json.detect_encoding(b), "surrogatepass"))}
        if fn == "jde":
            doc = "".join(map(chr, c["doc"]))
            e = json.JSONDecodeError(c["msg"], doc, int(c["pos"]))
            cls, args = e.__reduce__()
            assert cls is json.JSONDecodeError
            return {"ok": [str(e), str(e.lineno), str(e.colno), [args[0], cps(args[1]), str(args[2])]]}
        if fn == "scan_once":
            v, end = dec_of(json, c).scan_once(str_arg(c["x"]), int(c["idx"]))
            return {"ok": [conv(v), str(end)]}
        if fn == "scanner_new":
            class Bad:
                def __bool__(self):
                    raise ValueError("boom")

            ns = {a: None for a in c["attrs"]}
            if "strict" in ns:
                ns["strict"] = {0: True, 1: False, 2: Bad()}[c["strict_mode"]]
            Ctx = type("Ctx", (), ns)
            return {"ok": bool(json.scanner.c_make_scanner(Ctx()).strict)}
        if fn == "make_enc":
            v = VALUES[c["key"]][0]
            markers = {0: None, 1: {}, 2: []}[c["markers"]]

            def custom(s):
                return "<" + s + ">"

            def nonstr(s):
                return 1

            def boom(s):
                raise ValueError("boom")

            enc = {0: json.encoder.c_encode_basestring_ascii, 1: json.encoder.c_encode_basestring,
                   2: custom, 3: nonstr, 4: boom}[c["encoder"]]
            ks = str_arg(c["key_sep"]) if "s" in c["key_sep"] else 1
            its = str_arg(c["item_sep"]) if "s" in c["item_sep"] else 1
            indent = None if c["indent"] is None else "".join(map(chr, c["indent"]))
            e = json.encoder.c_make_encoder(markers, py_default, enc, indent, ks, its, c["sort_keys"], c["skipkeys"],
                                            c["allow_nan"])
            return {"ok": [cps(x) for x in e(v, int(c["level"]))]}
        if fn == "colorize":
            return {"ok": cps(json.tool._colorize_json("".join(map(chr, c["s"])), Theme()))}
        if fn == "tool":
            return run_tool(c)
        raise AssertionError(fn)
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=50000)
