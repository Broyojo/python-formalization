"""Differential test: Lean model of the str/bytes/bytearray search, split and
pad methods vs. the running CPython.

Usage: python3 difftest/strsearch_diff.py [--cases N] [--seed S]

A case is {"mod": "strsearch", "fn": <method>, "ty": "str"|"bytes"|"bytearray",
"s": [code points or byte values], ...arguments}. Exits non-zero on any
mismatch. See difftest/common.py.
"""

import sys

import common

M = sys.maxsize
STR_ALPH = [97, 98, 97, 98, 32, 9, 10, 13, 11, 12, 0x1c, 0x1f, 43, 45, 48, 0, 0x85, 0xa0, 0xe9,
            0xff, 0x100, 0x2028, 0x3000, 0xffff, 0x10000, 0x10ffff]
BYTE_ALPH = [97, 98, 97, 98, 32, 9, 10, 13, 11, 12, 0x1c, 0x1f, 43, 45, 48, 0, 0x85, 0xa0, 0xe9, 0xff]
FNS = ["find", "rfind", "index", "rindex", "count", "startswith", "endswith", "replace",
       "split", "rsplit", "partition", "rpartition", "expandtabs", "zfill", "center", "ljust",
       "rjust", "removeprefix", "removesuffix", "strip", "lstrip", "rstrip", "splitlines"]
SEARCH = {"find", "rfind", "index", "rindex", "count", "startswith", "endswith", "replace",
          "split", "rsplit", "partition", "rpartition"}


def rand_seq(rng, alph, n):
    k = rng.choice([1, 2, 3, len(alph)])
    sub = rng.sample(alph, min(k, len(alph)))
    return [rng.choice(sub) for _ in range(n)]


def periodic(rng, alph, n):
    per = rand_seq(rng, alph[:4] if rng.random() < 0.7 else alph, rng.randint(1, 7))
    s = (per * (n // len(per) + 1))[:n]
    for _ in range(rng.randrange(4)):
        if s:
            s[rng.randrange(len(s))] = rng.choice(alph)
    return s


def gen_s(rng, alph, fn):
    if fn in SEARCH and rng.random() < 0.08:
        # Long haystacks reach the two-way / adaptive / horspool paths of FASTSEARCH.
        return periodic(rng, alph, rng.randint(2500, 6000))
    n = rng.choice([0, 1, 2, 3, 5, 8, rng.randint(0, 40)])
    return periodic(rng, alph, n) if rng.random() < 0.5 else rand_seq(rng, alph, n)


def gen_sub(rng, alph, s):
    if len(s) >= 2500:
        m = rng.choice([1, 2, 5, 6, 99, 100, 150, 400, 900])
    else:
        m = rng.choice([0, 1, 1, 2, 2, 3, 4, rng.randint(0, 10)])
    if s and m <= len(s) and rng.random() < 0.6:
        i = rng.randrange(len(s) - m + 1)
        sub = s[i:i + m]
        if sub and rng.random() < 0.3:
            sub[rng.randrange(len(sub))] = rng.choice(alph)
        return sub
    return rand_seq(rng, alph, m)


def edge_index(rng, n):
    return rng.choice([None, None, 0, 1, -1, 2, -2, 3, -3, n, n + 1, n - 1, -n, -n - 1, n + 5,
                       M, -M, -M - 1, 2 ** 63, -2 ** 63 - 1, 2 ** 64, 2 ** 100, -2 ** 100,
                       rng.randint(-n - 3, n + 3)])


def edge_count(rng):
    return rng.choice([-1, -1, -2, 0, 1, 2, 3, 5, M, -M - 1, M + 1, -M - 2, 2 ** 64])


def edge_width(rng, n):
    return rng.choice([-1, 0, n - 1, n, n + 1, n + 2, n + 3, n + 8, -M - 1, M + 1, -M - 2,
                       -2 ** 100, rng.randint(-3, n + 20)])


def gen_case(rng):
    fn = rng.choice(FNS)
    ty = rng.choice(["str", "str", "bytes", "bytearray"])
    alph = STR_ALPH if ty == "str" else BYTE_ALPH
    s = gen_s(rng, alph, fn)
    n = len(s)
    c = {"mod": "strsearch", "fn": fn, "ty": ty, "s": s}
    if fn in ("find", "rfind", "index", "rindex", "count"):
        if ty != "str" and rng.random() < 0.15:
            c["subint"] = rng.choice([97, 98, 0, 255, 256, -1, M, M + 1, -M - 2, rng.choice(alph)])
        else:
            c["sub"] = gen_sub(rng, alph, s)
        if rng.random() < 0.7:
            c["start"] = edge_index(rng, n)
            if rng.random() < 0.7:
                c["end"] = edge_index(rng, n)
    elif fn in ("startswith", "endswith"):
        if rng.random() < 0.2:
            c["tuple"] = [gen_sub(rng, alph, s) for _ in range(rng.randrange(4))]
        else:
            c["prefix"] = gen_sub(rng, alph, s)
        if rng.random() < 0.7:
            c["start"] = edge_index(rng, n)
            if rng.random() < 0.7:
                c["end"] = edge_index(rng, n)
    elif fn == "replace":
        c["old"] = gen_sub(rng, alph, s)
        c["new"] = gen_sub(rng, alph, s) if rng.random() < 0.7 else rand_seq(rng, alph, rng.randrange(4))
        if rng.random() < 0.6:
            c["count"] = edge_count(rng)
    elif fn in ("split", "rsplit"):
        c["sep"] = None if rng.random() < 0.4 else gen_sub(rng, alph, s)
        if rng.random() < 0.6:
            c["maxsplit"] = edge_count(rng)
    elif fn in ("partition", "rpartition"):
        c["sep"] = gen_sub(rng, alph, s)
    elif fn == "expandtabs":
        if rng.random() < 0.3:
            s[:] = [rng.choice([9, 9, 10, 13, 97]) for _ in range(rng.randrange(12))]
        big = [2 ** 31 - 1, 2 ** 31, -2 ** 31, -2 ** 31 - 1, M]
        if 9 in s:
            big = [2 ** 31, -2 ** 31, -2 ** 31 - 1, M, 1000]
        if rng.random() < 0.85:
            c["tabsize"] = rng.choice([-5, -1, 0, 1, 2, 3, 4, 8, rng.randint(-3, 12)] + big)
    elif fn == "zfill":
        if rng.random() < 0.5:
            s[:0] = [rng.choice([43, 45, 48, 97])]
        c["width"] = edge_width(rng, len(s))
    elif fn in ("center", "ljust", "rjust"):
        c["width"] = edge_width(rng, n)
        if rng.random() < 0.5:
            c["fill"] = rng.choice(alph)
    elif fn in ("removeprefix", "removesuffix"):
        c["p"] = gen_sub(rng, alph, s)
    elif fn in ("strip", "lstrip", "rstrip"):
        c["chars"] = None if rng.random() < 0.5 else rand_seq(rng, alph, rng.randrange(4))
    elif fn == "splitlines":
        c["keepends"] = rng.random() < 0.5
    return c


def mk(ty, seq):
    if ty == "str":
        return "".join(map(chr, seq))
    return bytes(seq) if ty == "bytes" else bytearray(seq)


def enc(v):
    if isinstance(v, str):
        return [ord(ch) for ch in v]
    if isinstance(v, (bytes, bytearray)):
        return list(v)
    if isinstance(v, (list, tuple)):
        return [enc(x) for x in v]
    return v


def run_python(c):
    ty = c["ty"]
    s = mk(ty, c["s"])
    # Arguments other than the receiver are `bytes` for bytes/bytearray receivers.
    arg = (lambda q: mk("str", q)) if ty == "str" else (lambda q: bytes(q))
    fn = c["fn"]

    def call():
        if fn in ("find", "rfind", "index", "rindex", "count"):
            sub = c["subint"] if "subint" in c else arg(c["sub"])
            extra = [c[k] for k in ("start", "end") if k in c]
            return getattr(s, fn)(sub, *extra)
        if fn in ("startswith", "endswith"):
            p = tuple(arg(x) for x in c["tuple"]) if "tuple" in c else arg(c["prefix"])
            extra = [c[k] for k in ("start", "end") if k in c]
            return getattr(s, fn)(p, *extra)
        if fn == "replace":
            extra = [c["count"]] if "count" in c else []
            return s.replace(arg(c["old"]), arg(c["new"]), *extra)
        if fn in ("split", "rsplit"):
            sep = None if c["sep"] is None else arg(c["sep"])
            kw = {"maxsplit": c["maxsplit"]} if "maxsplit" in c else {}
            return getattr(s, fn)(sep, **kw)
        if fn in ("partition", "rpartition"):
            return getattr(s, fn)(arg(c["sep"]))
        if fn == "expandtabs":
            return s.expandtabs(c["tabsize"]) if "tabsize" in c else s.expandtabs()
        if fn == "zfill":
            return s.zfill(c["width"])
        if fn in ("center", "ljust", "rjust"):
            extra = [arg([c["fill"]])] if "fill" in c else []
            return getattr(s, fn)(c["width"], *extra)
        if fn in ("removeprefix", "removesuffix"):
            return getattr(s, fn)(arg(c["p"]))
        if fn in ("strip", "lstrip", "rstrip"):
            ch = None if c["chars"] is None else arg(c["chars"])
            return getattr(s, fn)(ch)
        if fn == "splitlines":
            return s.splitlines(c["keepends"])
        raise AssertionError(fn)

    r = common.py_result(call)
    if "ok" in r:
        r["ok"] = enc(r["ok"])
    return r


if __name__ == "__main__":
    common.main(gen_case, run_python)
