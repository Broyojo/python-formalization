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
directly, and `json.tool.main` with patched streams. Decoders also run with an
`array_hook`; encoders get `frozendict`s, and `str` subclasses whose `__str__`
would show if a writer called it. Exits non-zero on any mismatch. See
difftest/common.py.
"""

import datetime
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


class StrSub(str):
    """Encoded by its characters: `write_escaped_*` must not call `str()` (gh-148241)."""

    def __str__(self):
        return "WRONG"


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
PLAIN_CH = ["a", "Z", "0", " ", "~", "é", "€", "\U0001d11e", "\x7f"]  # needs no escape, or only with ensure_ascii


def maybe_sub(rng, s):
    return StrSub(s) if rng.random() < 0.15 else s


def enc_text(rng):
    ch = PLAIN_CH if rng.random() < 0.4 else STR_CH
    return "".join(rng.choice(ch) for _ in range(rng.randint(0, 5)))
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
        return maybe_sub(rng, rng.choice(KEY_STRS) if rng.random() < 0.7 else rand_text(rng, 2))
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
            return maybe_sub(rng, enc_text(rng))
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
    if rng.random() < 0.3 and not has_cycle(d):
        return frozendict(d)
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
    if isinstance(k, str):
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
    if isinstance(v, str):
        return {"s": cps(v)}
    if type(v) is float:
        return {"f": str(fbits(v)), "r": cps(repr(v))}
    if type(v) is bytes:
        return {"other": 10**6, "t": "bytes"}
    if type(v) is Obj:
        return {"other": v.n, "t": "Obj"}
    if type(v) is list:
        return {"l": [enc_val(x, ancestors + [v]) for x in v]}
    if type(v) in (dict, frozendict):
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
        elif type(x) in (dict, frozendict):
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
        if type(x) in (dict, frozendict):
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


LONG_TYPE = "L" * 60  # `_PyArg_BadArgument` prints 50 bytes of the type name
# `%.50s` and `%.80s` cut UTF-8 bytes, dropping a character the cut splits.
LONG_TYPES = [LONG_TYPE, "\u00e9" * 41, "a" + "\u00e9" * 30, "\u4e2d" * 30, "ab" + "\U00010000" * 20]


def gen_scan_arg(rng):
    if rng.random() < 0.05:
        return {"other": rng.choice(["int", "bytes", "NoneType", *LONG_TYPES])}, ""
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


CTX_ATTRS = ["strict", "object_hook", "object_pairs_hook", "array_hook", "parse_float", "parse_int", "parse_constant"]


# ---------------------------------------------------------------- recursion limits and the full encoder
# (lean/PyLean/JsonMod/DecRec.lean, EncFull.lean)

def frame_depth():
    """The depth of the caller's frame."""
    f = sys._getframe(1)
    n = 0
    while f is not None:
        n += 1
        f = f.f_back
    return n


def rec_doc(rng):
    """Nested arrays and objects around a leaf, some with escapes (frames of py_scanstring and
    _decode_uXXXX), some invalid."""
    leaf = rng.choice(['1', '"a"', '"\\u0041"', '"\\ud834\\udd1e"', '{"\\u0041": 1}', '[]', '{}', 'null', '"x', '1.5', 'NaN'])
    s = leaf
    for _ in range(rng.randint(0, 40)):
        r = rng.random()
        bad = rng.random() < 0.03
        if r < 0.6:
            s = "[" + s + (rng.choice(["", ","]) if bad else rng.choice(["]", "]", ", 2]"]))
        else:
            s = '{"k' + rng.choice(["", "\\u0042"]) + '": ' + s + (rng.choice(["", "]"]) if bad else rng.choice(["}", ', "z": 0}']))
    return s


def tjson(name, qualname=None, module="builtins", tp_name=None, heap=False):
    return {"name": name, "qualname": qualname or name, "module": module, "tpName": tp_name or name, "heap": heap}


T_LIST, T_TUPLE, T_DICT, T_FDICT = tjson("list"), tjson("tuple"), tjson("dict"), tjson("frozendict")


class LSub(list):
    """A list subclass: `bool()` and iteration are given."""

    def __len__(self):
        return 1 if self._truth else 0

    def __iter__(self):
        yield from list(self._yields)
        if self._stop is not None:
            raise ValueError(self._stop)


class LSubM(LSub):
    pass


LSubM.__module__, LSubM.__qualname__ = "mymod", "Outer.LSubM"


class DSub(dict):
    """A dict subclass: stored entries, `bool()` and `items()` are given."""

    def __len__(self):
        return 1 if self._truth else 0

    def items(self):
        if self._head == 1:
            raise ValueError("items")
        if self._head == 2:
            return 5
        return self._gen()

    def _gen(self):
        for sh, k, v in self._items:
            yield (k, v) if sh == 0 else ([k, v] if sh == 1 else (k, v, 0))
        if self._stop is not None:
            raise ValueError(self._stop)


class XObj:
    def __init__(self, n):
        self.n, self.ret = n, BOOM


class XObjM(XObj):
    pass


XObjM.__module__, XObjM.__qualname__ = "mymod", "Outer.XObjM"

TYPES = {LSub: tjson("LSub", module="__main__", heap=True), LSubM: tjson("LSubM", "Outer.LSubM", "mymod", heap=True),
         DSub: tjson("DSub", module="__main__", heap=True), XObj: tjson("XObj", module="__main__", heap=True),
         XObjM: tjson("XObjM", "Outer.XObjM", "mymod", heap=True)}

XKEY_STRS = ["", "a", "b", "'", '"', "\\", "\n", "k'q", 'k"q', "true", "1"]
XOBJS = {}


class XGen:
    def __init__(self, rng):
        self.rng, self.sub, self.cyc = rng, False, False

    def key(self):
        rng = self.rng
        r = rng.random()
        if r < 0.55:
            s = rng.choice(XKEY_STRS)
            return s, {"s": cps(s)}
        if r < 0.7:
            n = rng.choice([0, 1, -1, 7, 10**20, 10**4300])
            return n, {"i": istr(n)}
        if r < 0.77:
            b = rng.random() < 0.5
            return b, {"b": b}
        if r < 0.81:
            return None, None
        if r < 0.9:
            x = rng.choice([0.0, -1.5, 1e22, math.inf, -math.inf])
            return x, {"f": str(fbits(x)), "r": cps(repr(x))}
        k = rng.randint(1, 3)
        # (a `decimal.Decimal` key would compare with int and float keys under sort_keys, which the
        # model's sort does not do; its message is that of a date key)
        o, t = rng.choice([((k,), tjson("tuple")),
                           (datetime.date(2000, 1, k), tjson("date", module="datetime", tp_name="datetime.date"))])
        return o, {"o": t, "ord": str(k)}

    def leaf(self, depth):
        rng = self.rng
        r = rng.random()
        if r < 0.25:
            s = "".join(rng.choice(["a", "\n", '"', "\\", "é", "\U0001d11e", "\x01", " "]) for _ in range(rng.randint(0, 3)))
            return (StrSub(s) if rng.random() < 0.2 else s), {"s": cps(s)}
        if r < 0.45:
            n = rng.choice([0, 1, -1, 2**63, 10**4300])
            return n, {"i": istr(n)}
        if r < 0.55:
            x = rng.choice([0.0, -1.5, 1e22, math.inf, math.nan])
            return x, {"f": str(fbits(x)), "r": cps(repr(x))}
        if r < 0.65:
            o = rng.choice([None, True, False])
            return o, o
        if r < 0.72:
            o, t = rng.choice([(set(), tjson("set")), (b"x", tjson("bytes"))])
            return o, {"other": 10**6, "t": t}
        if depth < 4:
            n = len(XOBJS)
            o = (XObjM if rng.random() < 0.3 else XObj)(n)
            XOBJS[n] = o
            q = rng.random()
            if q < 0.25:
                o.ret = BOOM
            elif q < 0.4:
                o.ret = [o]
                XJSON[id(o.ret)] = {"l": [{"other": n, "t": TYPES[type(o)]}], "t": T_LIST}
                self.cyc = True
            else:
                o.ret = self.val(depth + 1, [], allow_sub=False)[0]
            return o, {"other": n, "t": TYPES[type(o)]}
        return None, None

    def val(self, depth, anc, allow_sub=True):
        """`anc`: (object, mutable) for the enclosing containers, innermost last."""
        rng = self.rng
        k = rng.random()
        targets = [i for i, (_, mut) in enumerate(reversed(anc)) if mut]
        if targets and k < 0.05:
            self.cyc = True
            i = rng.choice(targets)
            return anc[-1 - i][0], {"back": i}
        if depth > 3 or k < 0.45:
            return self.leaf(depth)
        r = rng.random()
        n = rng.randint(0, 3)
        if r < 0.3:
            lst = []
            items = [self.val(depth + 1, anc + [(lst, True)], allow_sub) for _ in range(n)]
            lst.extend(o for o, _ in items)
            return lst, {"l": [j for _, j in items], "t": T_LIST}
        if r < 0.4:
            items = [self.val(depth + 1, anc + [(None, False)], allow_sub) for _ in range(n)]
            return tuple(o for o, _ in items), {"l": [j for _, j in items], "t": T_TUPLE}
        if r < 0.65:
            d = {}
            pairs = []
            for _ in range(n):
                ko, kj = self.key()
                vo, vj = self.val(depth + 1, anc + [(d, True)], allow_sub)
                if ko in d:
                    continue
                d[ko] = vo
                pairs.append([kj, vj])
            return d, {"d": pairs, "t": T_DICT}
        if r < 0.75 or not allow_sub:
            d = {}
            pairs = []
            for _ in range(n):
                ko, kj = self.key()
                vo, vj = self.val(depth + 1, anc + [(None, False)], allow_sub)
                if ko in d:
                    continue
                d[ko] = vo
                pairs.append([kj, vj])
            return frozendict(d), {"d": pairs, "t": T_FDICT}
        self.sub = True
        stop = rng.choice([None, None, "it"])
        truth = rng.random() < 0.7
        if r < 0.87:
            cls = LSubM if rng.random() < 0.3 else LSub
            lst = cls()
            lst._truth, lst._stop = truth, stop
            items = [self.val(depth + 1, anc + [(lst, True)], allow_sub) for _ in range(n)]
            lst._yields = [o for o, _ in items]
            return lst, {"l": [j for _, j in items], "t": TYPES[cls], "sub": {"truth": truth, "stop": stop}}
        d = DSub()
        stored = rng.randint(0, 2)
        for i in range(stored):
            dict.__setitem__(d, f"s{i}", i)
        d._truth, d._stop, d._head = truth, stop, rng.choice([0, 0, 0, 0, 1, 2])
        its = []
        js = []
        for _ in range(n):
            sh = rng.choice([0, 0, 0, 1, 2])
            ko, kj = self.key()
            vo, vj = self.val(depth + 1, anc + [(d, True)], allow_sub)
            its.append((sh, ko, vo))
            js.append([sh, kj, vj])
        d._items = its
        return d, {"d": js, "t": TYPES[DSub],
                   "sub": {"used": stored, "truth": truth, "head": d._head, "stop": stop}}


def xdefault(o):
    if isinstance(o, XObj):
        if o.ret is BOOM:
            raise ValueError("boom")
        return o.ret
    raise TypeError(f"Object of type {type(o).__name__} is not JSON serializable")


def xdflt_table(v):
    out = []
    seen = set()

    def go(x):
        if id(x) in seen:
            return
        seen.add(id(x))
        if isinstance(x, XObj):
            out.append([x.n, None if x.ret is BOOM else {"v": XJSON[id(x.ret)]}])
            if x.ret is not BOOM:
                go(x.ret)
        elif isinstance(x, LSub):
            for y in x._yields:
                go(y)
        elif isinstance(x, DSub):
            for _, _, y in x._items:
                go(y)
        elif isinstance(x, (list, tuple)):
            for y in x:
                go(y)
        elif isinstance(x, (dict, frozendict)):
            for y in x.values():
                go(y)

    go(v)
    return out


XJSON = {}  # id(default result) -> its JSON
XVALUES = {}


def sep_json(rng, s):
    m = rng.choice([0, 0, 0, 1, 2])
    return m, {"s": cps(s), "sub": m}


class SepX(str):
    def __str__(self):
        return "X"


class SepR(str):
    def __str__(self):
        raise ValueError("sep")


def gen_x_case(rng, impl):
    if rng.random() < 0.3:
        s = rec_doc(rng)
        c = {"mod": "json", "fn": f"loads_rec_{impl}", "s": cps(s), "strict": rng.random() < 0.8}
        c["budget"] = rng.randint(0, 90) if impl == "py" else 100000
        return c
    g = XGen(rng)
    XJSON.clear()
    orig_val = g.val

    def val(depth, anc, allow_sub=True):
        o, j = orig_val(depth, anc, allow_sub)
        XJSON[id(o)] = j
        return o, j

    g.val = val
    v, vj = g.val(0, [])
    indent = rng.choice([None, None, None, "  ", "\t"])
    item, key = rng.choice([(", ", ": "), (",", ":"), (";", "=")])
    if indent is not None and rng.random() < 0.5:
        item = ","
    im, ij = sep_json(rng, item)
    km, kj = sep_json(rng, key)
    kw = dict(ensure_ascii=rng.random() < 0.5, check_circular=rng.random() < 0.7, allow_nan=rng.random() < 0.7,
              sort_keys=rng.random() < 0.3 and not g.sub, skipkeys=rng.random() < 0.4, indent=indent)
    if g.cyc and (impl == "c" or g.sub):
        kw["check_circular"] = True  # without it C recurses until its stack runs out
    seps = ({0: str, 1: SepX, 2: SepR}[im](item), {0: str, 1: SepX, 2: SepR}[km](key))
    if impl == "py":
        # the methods of the subclasses take frames the model does not count
        if g.sub:
            budget = 10000
        elif g.cyc and not kw["check_circular"]:
            budget = rng.randint(0, 60)
        else:
            budget = rng.choice([rng.randint(0, 30), 10000])
    else:
        budget = 100000
    key_ = len(XVALUES)
    XVALUES[key_] = (v, kw, seps)
    c = {"mod": "json", "fn": f"dumpsx_{impl}", "v": vj, "dflt": xdflt_table(v), "key": key_, "budget": budget,
         "indent": None if indent is None else cps(indent), "item_sep": ij, "key_sep": kj}
    c.update({k: kw[k] for k in ("ensure_ascii", "check_circular", "allow_nan", "sort_keys", "skipkeys")})
    return c


def xexc(e, impl):
    msg = str(e)
    if (type(e) is RecursionError and impl == "c") or msg.startswith("'<' not supported"):
        msg = "~"
    return {"exc": type(e).__name__, "msg": msg, "notes": list(getattr(e, "__notes__", []))}


def run_x(c, impl):
    if c["fn"].startswith("loads_rec"):
        s = "".join(map(chr, c["s"]))
        if impl == "c":
            return {"ok": conv(json.JSONDecoder(strict=c["strict"]).decode(s))}
        dec = pyjson.JSONDecoder(strict=c["strict"])
        d = frame_depth()
        # decode at d + 1, raw_decode at d + 2: `budget` frames are left when it calls scan_once
        old = sys.getrecursionlimit()
        sys.setrecursionlimit(d + 2 + c["budget"])
        try:
            r = dec.decode(s)
        finally:
            sys.setrecursionlimit(old)
        return {"ok": conv(r)}
    v, kw, seps = XVALUES[c["key"]]
    try:
        if impl == "c":
            return {"ok": {"text": cps(json.JSONEncoder(default=xdefault, separators=seps, **kw).encode(v))}}
        e = pyjson.JSONEncoder(default=xdefault, separators=seps, **kw)
        d = frame_depth()
        # encode at d + 1: `budget` frames are left there
        old = sys.getrecursionlimit()
        sys.setrecursionlimit(d + 1 + c["budget"])
        try:
            r = e.encode(v)
        finally:
            sys.setrecursionlimit(old)
        return {"ok": {"text": cps(r)}}
    except Exception as ex:
        return {"ok": xexc(ex, impl)}


def gen_case(rng):
    impl = rng.choice(["py", "c"])
    if rng.random() < 0.25:
        return gen_x_case(rng, impl)
    r = rng.random()
    if r < 0.32:
        s = gen_doc(rng)
        c = {"mod": "json", "s": cps(s), "strict": rng.random() < 0.7,
             "ohook": rng.choice([0, 0, 1, 2, 3]), "phook": rng.choice([0, 0, 0, 1, 2, 3]),
             "pint": rng.choice([0, 0, 0, 1, 2, 3]), "pfloat": rng.choice([0, 0, 0, 2, 3]),
             "pconst": rng.choice([0, 0, 0, 2, 3]), "ahook": rng.choice([0, 0, 1, 1, 2, 3])}
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
             "ahook": rng.choice([0, 0, 0, 1, 2, 3]),
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
            x = {"s": cps(s), "sub": rng.random() < 0.2}
        n = len(s)
        e = rng.choice([1, 1, 1, 0, n, n - 1, n + 1, -1, 2**63 - 1, 2**63, -2**63 - 1, rng.randint(0, n + 1)])
        if impl == "py":
            return {"mod": "json", "fn": "scanstr_py", "s": cps(s), "end": str(e), "strict": strict}
        return {"mod": "json", "fn": "scanstr_c", "x": x, "end": str(e), "strict": strict}
    if r < 0.93:
        ascii_ = rng.random() < 0.5
        s = rand_text(rng, rng.randint(0, 6)) if rng.random() < 0.6 else enc_text(rng)
        if impl == "py" or rng.random() < 0.9:
            return {"mod": "json", "fn": f"encstr_{impl}", "ascii": ascii_, "s": cps(s),
                    "x": {"s": cps(s), "sub": rng.random() < 0.3}}
        return {"mod": "json", "fn": "encstr_c", "ascii": ascii_,
                "x": {"other": rng.choice(["int", "bytes", "NoneType", *LONG_TYPES])}}
    if r < 0.95:
        x, s = gen_scan_arg(rng)
        return {"mod": "json", "fn": "scan_once", "x": x, "idx": str(gen_idx(rng, s)), "strict": rng.random() < 0.7,
                "pfloat": 0, "pconst": 0, "ahook": rng.choice([0, 0, 1, 2, 3])}
    if r < 0.96:
        attrs = [a for a in CTX_ATTRS if rng.random() < 0.9]
        raising = [a for a in CTX_ATTRS if rng.random() < 0.1]
        return {"mod": "json", "fn": "scanner_new", "tp": "Ctx", "attrs": attrs, "raising": raising,
                "strict_mode": rng.choice([0, 1, 2])}
    if r < 0.98:
        v, kw = enc_opts(rng)
        c = base_case("make_enc", v, kw)
        c["markers"] = rng.choice([0, 1, 1, 1, 2]) if kw["check_circular"] else 0
        if has_cycle(v):
            c["markers"] = 1 if kw["check_circular"] else 0
            c["indent"] = c["indent"] if kw["check_circular"] else None
        c["encoder"] = rng.choice([0, 1, 2, 3, 4, 5])
        c["level"] = str(rng.choice([0, 0, 1, 3, 2**63, -2**63 - 1]))
        # A non-str separator: `converterr` cuts its type name to 50 bytes with snprintf.
        c["key_sep"] = {"s": c["key_sep"]} if rng.random() < 0.95 else {"other": rng.choice(["int", *LONG_TYPES])}
        c["item_sep"] = {"s": c["item_sep"]} if rng.random() < 0.95 else {"other": rng.choice(["int", *LONG_TYPES])}
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
                         object_pairs_hook=obj_hook(c.get("phook", 0), Pairs),
                         array_hook=obj_hook(c.get("ahook", 0), lambda x: ["A", x]))


def decode_arg(c):
    a = c["arg"]
    if "s" in a:
        return "".join(map(chr, a["s"]))
    if "b" in a:
        return bytes(a["b"])
    return {"int": 1, "NoneType": None, "list": [], "float": 1.5}[a["other"]]


def load_kw(c):
    kw = dict(object_hook=obj_hook(c["ohook"], lambda d: ["H", d]), object_pairs_hook=obj_hook(c["phook"], Pairs),
              array_hook=obj_hook(c["ahook"], lambda x: ["A", x]),
              parse_float=py_hook(c["pfloat"], "F"), parse_int=py_hook(c["pint"], "I"),
              parse_constant=py_hook(c["pconst"], "C"))
    if c["strict"] is not None:
        kw["strict"] = c["strict"]
    if c["kw"]:
        kw[c["kw"][0]] = 1
    return kw


def yield_result(chunks, exc):
    return {"ok": {"chunks": [cps(x) for x in chunks], "exc": exc}}


LONG_OBJS = {t: type(t, (), {})() for t in LONG_TYPES}


def str_arg(x):
    if "s" in x:
        s = "".join(map(chr, x["s"]))
        return StrSub(s) if x.get("sub") else s
    return {"int": 1, "bytes": b"", "NoneType": None, **LONG_OBJS}[x["other"]]


def run_python(c):
    fn = c["fn"]
    base, impl = fn.rsplit("_", 1) if "_" in fn else (fn, "c")
    m = IMPL.get(impl, json)
    try:
        if base in ("loads_rec", "dumpsx"):
            return run_x(c, impl)
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

            def raiser(a):
                def get(self):
                    raise ValueError(a)
                return property(get)

            ns = {a: None for a in c["attrs"]}
            if "strict" in ns:
                ns["strict"] = {0: True, 1: False, 2: Bad()}[c["strict_mode"]]
            for a in c.get("raising", []):
                ns[a] = raiser(a)
            Ctx = type("Ctx", (), ns)
            return {"ok": bool(json.scanner.c_make_scanner(Ctx()).strict)}
        if fn == "make_enc":
            v = VALUES[c["key"]][0]
            markers = {0: None, 1: {}, 2: []}[c["markers"]]

            def custom(s):
                return "<" + s + ">"

            def nonstr(s):
                return 1

            def nonstr_long(s):
                return LONG_OBJS["\u00e9" * 41]

            def boom(s):
                raise ValueError("boom")

            enc = {0: json.encoder.c_encode_basestring_ascii, 1: json.encoder.c_encode_basestring,
                   2: custom, 3: nonstr, 4: boom, 5: nonstr_long}[c["encoder"]]
            ks = str_arg(c["key_sep"])
            its = str_arg(c["item_sep"])
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
