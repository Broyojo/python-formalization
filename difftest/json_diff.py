"""Differential test: Lean model of json (C and pure-Python twins) vs. the running CPython.

Usage: python3 difftest/json_diff.py [--cases N] [--seed S]

`..._c` cases run the C accelerator (`_json`): `json.JSONDecoder` with the C
scanner, `json.dumps` with `c_make_encoder`. `..._py` cases run the pure-Python
module from `import_fresh_module('json', blocked=['_json'])`. Decoding always
uses `parse_float` and `parse_constant` hooks that record the matched text
(floats are out of scope); `parse_int` is `int` or such a hook, and
`object_pairs_hook` is unset or records the pairs. Exits non-zero on any
mismatch. See difftest/common.py.
"""

import json
import sys
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


def rand_key(rng):
    r = rng.random()
    if r < 0.6:
        return rng.choice(KEY_STRS) if rng.random() < 0.7 else rand_text(rng, 2)
    if r < 0.75:
        return rng.choice([0, 1, -1, 2, 10**20, -(10**20), 7])
    if r < 0.82:
        return rng.choice([True, False])
    if r < 0.88:
        return None
    if r < 0.93:
        return 10 ** 4300 * rng.choice([1, -1])
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
    if type(v) is bytes:
        return {"other": 0}
    if type(v) is list:
        return {"l": [enc_val(x, ancestors + [v]) for x in v]}
    if type(v) is dict:
        return {"d": [[enc_key(k), enc_val(x, ancestors + [v])] for k, x in v.items()]}
    raise AssertionError(type(v))


INT_MAX_STR = sys.get_int_max_str_digits()
if INT_MAX_STR != 4300:
    sys.set_int_max_str_digits(4300)

VALUES = {}  # case id -> Python object (cycles cannot travel as JSON)


def gen_case(rng):
    impl = rng.choice(["py", "c"])
    r = rng.random()
    if r < 0.6:
        s = gen_doc(rng)
        c = {"mod": "json", "s": cps(s), "strict": rng.random() < 0.7,
             "pairs": rng.random() < 0.4, "inthook": rng.random() < 0.2}
        if rng.random() < 0.7:
            c["fn"] = f"loads_{impl}"
        else:
            c["fn"] = f"raw_{impl}"
            c["idx"] = str(gen_idx(rng, s))
        return c
    v = rand_val(rng, 0, [])
    indent = rng.choice([None, None, 0, 2, -1, "\t", "", " \n", "--"])
    seps = rng.choice([None, None, (",", ":"), (" , ", " : "), ("\n,", ":\t"), (";", "=")])
    kw = dict(ensure_ascii=rng.random() < 0.5, check_circular=rng.random() < 0.7,
              sort_keys=rng.random() < 0.4, skipkeys=rng.random() < 0.4, indent=indent, separators=seps)
    if not kw["check_circular"] and '"back"' in json.dumps(enc_val(v, [])):
        # A cycle without check_circular recurses until RecursionError; with an
        # indent the C encoder's indent cache grows quadratically on the way
        # (gigabytes before the C stack limit), so keep those cases compact.
        indent = kw["indent"] = None
    eff_indent = None if indent is None else (" " * indent if type(indent) is int else indent)
    if seps is None:
        seps = (", ", ": ") if indent is None else (",", ": ")
    key = len(VALUES)
    VALUES[key] = (v, kw)
    return {"mod": "json", "fn": f"dumps_{impl}", "v": enc_val(v, []), "key": key,
            "ensure_ascii": kw["ensure_ascii"], "check_circular": kw["check_circular"],
            "sort_keys": kw["sort_keys"], "skipkeys": kw["skipkeys"],
            "indent": None if eff_indent is None else cps(eff_indent),
            "item_sep": cps(seps[0]), "key_sep": cps(seps[1])}


def run_python(c):
    fn = c["fn"]
    base, impl = fn.rsplit("_", 1)
    m = IMPL[impl]
    try:
        if base in ("loads", "raw"):
            s = "".join(map(chr, c["s"]))
            dec = m.JSONDecoder(strict=c["strict"], parse_float=lambda t: Hook("float", t),
                                parse_constant=lambda t: Hook("const", t),
                                parse_int=(lambda t: Hook("int", t)) if c["inthook"] else None,
                                object_pairs_hook=Pairs if c["pairs"] else None)
            if base == "loads":
                return {"ok": conv(dec.decode(s))}
            v, end = dec.raw_decode(s, int(c["idx"]))
            return {"ok": [conv(v), str(end)]}
        v, kw = VALUES[c["key"]]
        return {"ok": cps(m.dumps(v, **kw))}
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=50000)
