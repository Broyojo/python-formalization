"""Differential test: Lean model of tuple, list, bytes, bytearray and memoryview
vs. the running CPython.

Usage: python3 difftest/bytesobj_diff.py [--cases N] [--seed S] [--family F]

Each family below supplies `gen_<family>(rng)` and `run_<family>(case)`. Cases
carry "mod": "bytesobj" and a `fn` starting with the family prefix.
"""

import sys

import common


def choose_family():
    """`--family seq|bytes|mem` restricts the run; the option is removed from argv."""
    if "--family" not in sys.argv:
        return None
    i = sys.argv.index("--family")
    family = sys.argv[i + 1]
    del sys.argv[i:i + 2]
    return family


# ===== family seq: tuple and list =====================================


def gen_seq(rng):
    return None


def run_seq(case):
    raise NotImplementedError(case["fn"])


# ===== end of family seq ==============================================


# ===== family bytes: bytes and bytearray ==============================
#
# Objects travel as tagged lists (see lean/PyLean/BytesObj/Bytes/Diff.lean, `decObj`).
# `b_build` makes the real object. Requests between 2**31 and 2**47 bytes are never
# generated: below that memory is available, above it malloc fails on LP64.

import codecs
import warnings


class BIdx:
    def __init__(self, v):
        self.v = v

    def __index__(self):
        return self.v


class BDun:
    def __init__(self, r):
        self.r = r

    def __bytes__(self):
        return self.r


def b_bflt(x):
    import math
    if math.isnan(x):
        return ["float", False, 2, 0, 1, repr(x), x.hex()]
    neg = math.copysign(1.0, x) < 0
    if math.isinf(x):
        return ["float", neg, 1, 0, 1, repr(x), x.hex()]
    n, d = abs(x).as_integer_ratio()
    return ["float", neg, 0, n, d, repr(x), x.hex()]


def b_build(o):
    t = o[0]
    if t == "none":
        return None
    if t in ("bool", "int"):
        return o[1]
    if t == "pow":
        return o[1] ** o[2]
    if t == "float":
        return float.fromhex(o[6])
    if t == "str":
        return "".join(map(chr, o[1]))
    if t == "bytes":
        return bytes(o[1])
    if t == "bytearray":
        return bytearray(o[1])
    if t == "memview":
        return memoryview(bytes(o[1] + o[2]))[:len(o[1])]
    if t == "list":
        return [b_build(x) for x in o[1]]
    if t == "tuple":
        return tuple(b_build(x) for x in o[1])
    if t == "iter":
        return (b_build(x) for x in o[1])
    if t == "dict":
        return {bytes(k): b_build(v) for k, v in o[1]}
    if t == "index":
        return BIdx(o[1])
    if t == "dunder":
        return BDun(b_build(o[1]))
    if t == "plain":
        return object()
    raise ValueError(t)


def b_benc(v):
    if isinstance(v, bytes):
        return ["B", list(v)]
    if isinstance(v, bytearray):
        return ["A", list(v)]
    if isinstance(v, str):
        return ["S", [ord(c) for c in v]]
    if isinstance(v, (list, tuple)):
        return [b_benc(x) for x in v]
    return v


B_EDGE_INT = [0, 1, -1, 2, -2, 255, 256, -256, 127, 128, sys.maxsize, -sys.maxsize, -sys.maxsize - 1,
             2 ** 63, -2 ** 63 - 1, 2 ** 64, 2 ** 31, -2 ** 31, 2 ** 31 - 1, 10 ** 30, -10 ** 30]


def b_rbytes(rng, n=None):
    n = rng.choice([0, 0, 1, 1, 2, 3, 4, 5, 8, 12, 20]) if n is None else n
    pool = rng.choice([list(range(256)), [32, 9, 10, 13, 12, 11], list(b"aAbBzZ09 _'\"\\"),
                       list(b"abcABC"), [0, 1, 127, 128, 255], list(b"0123456789abcdefABCDEF ")])
    return [rng.choice(pool) for _ in range(n)]


def b_rint(rng):
    return rng.choice(B_EDGE_INT) if rng.random() < 0.5 else rng.randint(-20, 300)


def b_robj(rng, depth=2):
    r = rng.random()
    if r < 0.25:
        return ["int", b_rint(rng)]
    if r < 0.45:
        return ["bytes", b_rbytes(rng)]
    if r < 0.55:
        return ["bytearray", b_rbytes(rng)]
    if r < 0.62:
        return ["str", rng.choice([[], [97], [97, 98], [233], [0x263a], [0x1f600], [39], [39, 34], [10, 92]])]
    if r < 0.69:
        s = b_rbytes(rng)
        return ["memview", s, b_rbytes(rng, 2) + [0]]
    if r < 0.74:
        return ["bool", rng.random() < 0.5]
    if r < 0.79:
        return ["none"]
    if r < 0.84:
        return ["index", b_rint(rng)]
    if r < 0.88:
        return ["dunder", rng.choice([["bytes", b_rbytes(rng)], ["int", 1]])]
    if r < 0.93:
        return b_bflt(rng.choice([0.0, -0.0, 1.0, -1.5, 3.14159, 1e300, 1e-300, 5e-324, 1e22, 1e21, 0.1,
                                123456789.125, 0.5, 2.5, 1e16, float("inf"), float("-inf"), float("nan"),
                                99999.5, 0.0001, 0.00001, 1.7976931348623157e308]))
    if depth > 0:
        k = rng.choice(["list", "tuple", "iter"])
        return [k, [b_robj(rng, depth - 1) for _ in range(rng.randint(0, 3))]]
    return ["plain"]


def b_rbyteobjs(rng):
    return [["int", rng.choice([0, 1, 97, 255, 256, -1, 2 ** 63, 300])] if rng.random() < 0.1
            else ["int", rng.randint(0, 255)] for _ in range(rng.randint(0, 6))]


def b_rfmt(rng):
    """Format strings with every parser path; returns (format bytes, args object)."""
    parts, args = [], []
    for _ in range(rng.randint(0, 4)):
        if rng.random() < 0.3:
            parts.append(bytes(rng.choice([b"x", b"ab", b"%%", b" ", b"\xff", b"\x00", b"%", b"%("])))
            continue
        sp = b"%"
        if rng.random() < 0.1:
            sp += b"(" + rng.choice([b"a", b"b", b"(x)", b""]) + b")"
        for f in rng.sample([b"-", b"+", b" ", b"#", b"0"], rng.choice([0, 0, 1, 1, 2, 3])):
            sp += f
        wk = rng.random()
        if wk < 0.3:
            sp += str(rng.choice([1, 2, 3, 5, 8, 10, 20, 0])).encode()
        elif wk < 0.33:
            sp += str(rng.choice([2 ** 63 - 1, 2 ** 63, 10 ** 30, 2 ** 63 - 2])).encode()
        elif wk < 0.45:
            sp += b"*"
            args.append(["int", rng.choice([0, 1, 5, 8, -1, -5, -8, 12, 2 ** 63, -2 ** 63, -2 ** 63 + 1, 2 ** 63 - 1,
                                            2 ** 63 - 30, 2 ** 47, 2 ** 48 - 1])])
        pk = rng.random()
        if pk < 0.25:
            sp += b"." + str(rng.choice([0, 1, 2, 3, 6, 10, 17, 20])).encode()
        elif pk < 0.28:
            sp += b"." + str(rng.choice([2 ** 31 - 1, 2 ** 31, 2 ** 31 - 3, 10 ** 20])).encode()
            parts.append(sp + rng.choice([b"d", b"x", b"s", b"a"]))
            args.append(rng.choice([["int", 5], ["bytes", [97]]]))
            continue
        elif pk < 0.35:
            sp += b".*"
            args.append(["int", rng.choice([0, 1, 5, -1, -7, 2 ** 31, -2 ** 31 - 1, 2 ** 40])])
        elif pk < 0.38:
            sp += b"."
        if rng.random() < 0.07:
            sp += rng.choice([b"h", b"l", b"L"])
        conv = rng.choice([b"d", b"i", b"u", b"o", b"x", b"X", b"e", b"E", b"f", b"F", b"g", b"G",
                           b"s", b"b", b"a", b"r", b"c", b"%", b"z", b"\xe9", b"\x00", b""])
        sp += conv
        parts.append(sp)
        if conv in (b"d", b"i", b"u", b"o", b"x", b"X"):
            args.append(rng.choice([["int", b_rint(rng)], ["pow", 10, 4400], ["pow", 10, 4299], ["pow", 10, 4300], ["pow", 2, 15000],
                                    ["bool", True], ["index", b_rint(rng)], b_robj(rng, 1)]))
        elif conv in (b"e", b"E", b"f", b"F", b"g", b"G"):
            args.append(rng.choice([b_bflt(rng.choice([0.0, 1.5, -2.25, 1e100, 1e-5, 123456.789, 0.1, float("inf"), float("nan")])),
                                    ["int", b_rint(rng)], ["pow", 2, 1024], ["pow", 2, 1023], ["index", 7], b_robj(rng, 1)]))
        elif conv == b"c":
            args.append(rng.choice([["int", rng.randint(-1, 300)], ["bytes", b_rbytes(rng, rng.choice([0, 1, 1, 2]))],
                                    ["bytearray", b_rbytes(rng, rng.choice([0, 1, 1, 2]))], ["index", rng.randint(0, 300)],
                                    ["int", 2 ** 70], ["str", [97]], b_bflt(1.5), ["none"]]))
        elif conv in (b"a", b"r"):
            args.append(rng.choice([b_robj_ascii(rng), ["pow", 10, 4400]]))
        else:
            args.append(b_robj(rng, 1) if rng.random() < 0.4 else ["bytes", b_rbytes(rng)])
    fmt = b"".join(parts)
    r = rng.random()
    if r < 0.6:
        a = ["tuple", args]
    elif r < 0.8 and len(args) == 1:
        a = args[0]
    elif r < 0.9:
        a = ["dict", [[list(b"a"), args[0] if args else ["int", 1]], [list(b"(x)"), ["bytes", list(b"k")]],
                      [[], ["int", 3]]]]
    elif r < 0.95:
        a = ["list", args]
    else:
        a = ["tuple", args + [["int", 1]]]
    return list(fmt), a


def b_robj_ascii(rng, depth=2):
    """Objects whose repr has no address."""
    r = rng.random()
    if r < 0.2:
        return ["int", b_rint(rng)]
    if r < 0.4:
        return ["bytes", b_rbytes(rng)]
    if r < 0.5:
        return ["bytearray", b_rbytes(rng)]
    if r < 0.7:
        return ["str", rng.choice([[], [97], [233], [0x263a], [0x1f600], [39], [39, 34], [34], [10, 92, 9, 13, 127, 1]])]
    if r < 0.8:
        return rng.choice([["none"], ["bool", True], ["bool", False], b_bflt(1.5), b_bflt(float("inf"))])
    if depth > 0:
        return [rng.choice(["list", "tuple"]), [b_robj_ascii(rng, depth - 1) for _ in range(rng.randint(0, 3))]]
    return ["none"]


def b_noaddr(o):
    """`%a` of a misaligned argument: objects whose repr has an address are out of scope."""
    t = o[0]
    if t in ("memview", "plain", "iter", "index", "dunder"):
        return ["int", 1]
    if t in ("list", "tuple"):
        return [t, [b_noaddr(x) for x in o[1]]]
    if t == "dict":
        return [t, [[k, b_noaddr(v)] for k, v in o[1]]]
    return o


def b_rsub(rng, s):
    r = rng.random()
    if r < 0.4 and s:
        i = rng.randint(0, len(s) - 1)
        return ["bytes", s[i:i + rng.randint(0, 3)]]
    if r < 0.6:
        return ["int", s[0] if s and rng.random() < 0.5 else b_rint(rng)]
    return b_robj(rng, 1)


def b_ropt(rng, s):
    if rng.random() < 0.5:
        return None
    return rng.choice([0, 1, -1, len(s), -len(s), len(s) + 1, -len(s) - 1, 2, sys.maxsize, -sys.maxsize - 1,
                       2 ** 64, -2 ** 64, 10 ** 30])


def b_rslice(rng, n):
    def part():
        if rng.random() < 0.3:
            return None
        return rng.choice([0, 1, -1, 2, -2, n, -n, n + 1, -n - 1, 3, 2 ** 63, -2 ** 63 - 1, sys.maxsize, -sys.maxsize - 1])
    st = rng.choice([None, 1, 1, 2, -1, -2, 3, 5, -3, sys.maxsize, -sys.maxsize - 1, 2 ** 64, -2 ** 64, 0])
    return [part(), part(), st]


BCOMMON_M = ["isspace", "isalpha", "isalnum", "isdigit", "islower", "isupper", "istitle", "isascii",
            "lower", "upper", "title", "capitalize", "swapcase"]
BSEARCH_M = ["find", "rfind", "index", "rindex", "count"]


def b_rtable(rng):
    r = rng.random()
    if r < 0.3:
        return ["none"]
    if r < 0.8:
        t = list(range(256))
        for _ in range(rng.randint(0, 5)):
            t[rng.randint(0, 255)] = rng.randint(0, 255)
        return [rng.choice(["bytes", "bytearray"]), t]
    return rng.choice([["bytes", b_rbytes(rng)], ["str", [97]], ["int", 1]])


def b_rhex_input(rng):
    alpha = rng.choice([list(b"0123456789abcdefABCDEF"), list(b"0123456789abcdefABCDEF   \t\n\r\x0b\x0c"),
                        list(b"01 g"), list(range(128))])
    s = [rng.choice(alpha) for _ in range(rng.randint(0, 10))]
    k = rng.random()
    if k < 0.35:
        return ["str", s]
    if k < 0.45:
        return ["str", s + [rng.choice([128, 255, 256, 0x263a])] + s[:2]]
    if k < 0.65:
        return ["bytes", s]
    if k < 0.8:
        return ["bytearray", s]
    if k < 0.95:
        # keep the memory after the view from containing a hex digit or a space
        return ["memview", s, [rng.choice([0, 0x7f, 0xff, 0x67])]]
    return b_robj(rng, 1)


def gen_bytes(rng):
    ty = rng.choice(["bytes", "bytes", "bytearray"])
    s = b_rbytes(rng)
    r = rng.random()
    c = {"mod": "bytesobj", "s": s}
    if r < 0.14:
        c["fn"] = ty + "." + rng.choice(BCOMMON_M)
    elif r < 0.30:
        c["fn"] = ty + "." + rng.choice(BSEARCH_M)
        c["sub"] = b_rsub(rng, s)
        c["start"], c["end"] = b_ropt(rng, s), b_ropt(rng, s)
    elif r < 0.33:
        c["fn"] = ty + ".contains"
        c["sub"] = b_rsub(rng, s)
    elif r < 0.37:
        c["fn"] = ty + "." + rng.choice(["startswith", "endswith"])
        sub = b_rsub(rng, s)
        if rng.random() < 0.3:
            sub = ["tuple", [b_rsub(rng, s) for _ in range(rng.randint(0, 3))]]
        c["sub"] = sub
        c["start"], c["end"] = b_ropt(rng, s), b_ropt(rng, s)
    elif r < 0.42:
        c["fn"] = ty + ".hex"
        c["sep"] = rng.choice([None, None, ["str", [58]], ["bytes", [32]], ["str", [255]], ["bytes", [200]],
                               ["str", [0x263a]], ["str", []], ["str", [97, 98]], ["bytearray", [58]], ["int", 5],
                               ["list", [["int", 1]]]])
        c["n"] = rng.choice([None, 1, 2, 3, -1, -2, -3, 0, 100, -100, 2 ** 31, -2 ** 31, -2 ** 31 - 1, 2 ** 31 - 1])
    elif r < 0.46:
        c["fn"] = ty + ".fromhex"
        c["x"] = b_rhex_input(rng)
    elif r < 0.60:
        c["fn"] = ty + ".mod"
        fmt, arg = b_rfmt(rng)
        c["s"], c["arg"] = fmt, (b_noaddr(arg) if 97 in fmt or 114 in fmt else arg)
    elif r < 0.63:
        c["fn"] = ty + ".repr"
    elif r < 0.64:
        c["fn"] = ty + ".bufinfo"
    elif r < 0.68:
        c["fn"] = ty + ".new"
        c["x"] = rng.choice([b_robj(rng, 2), ["list", b_rbyteobjs(rng)], ["tuple", b_rbyteobjs(rng)],
                             ["iter", b_rbyteobjs(rng)], ["int", rng.choice([0, 1, 5, -1, sys.maxsize, sys.maxsize - 32,
                                                                           sys.maxsize - 33, 2 ** 47, 2 ** 63])], None,
                             ["str", [97, 233]]])
        if c["x"] is None or rng.random() < 0.3:
            c["enc"] = rng.choice([None, "latin-1", "ascii"])
            c["err"] = rng.choice([None, "strict"])
        if c["x"] is not None and c["x"][0] in ("int", "index") and 2000 < c["x"][1] < 2 ** 47:
            c["x"] = [c["x"][0], c["x"][1] % 1000]
    elif r < 0.72:
        c["fn"] = ty + ".join"
        c["it"] = rng.choice([["list", [["bytes", b_rbytes(rng)] for _ in range(rng.randint(0, 4))]],
                              ["tuple", [["bytearray", b_rbytes(rng)] for _ in range(rng.randint(0, 4))]],
                              ["iter", [b_robj(rng, 0) for _ in range(rng.randint(0, 3))]], b_robj(rng, 1)])
    elif r < 0.75:
        c["fn"] = ty + ".translate"
        c["table"] = b_rtable(rng)
        c["delete"] = rng.choice([None, None, ["bytes", b_rbytes(rng)], ["bytearray", b_rbytes(rng)], ["str", [97]], ["int", 1]])
    elif r < 0.78:
        c["fn"] = ty + "." + rng.choice(["removeprefix", "removesuffix"])
        c["arg"] = rng.choice([["bytes", s[:rng.randint(0, 3)]], ["bytes", s[-2:]], ["bytearray", s[:1]], b_robj(rng, 0)])
    elif r < 0.81:
        c["fn"] = ty + "." + rng.choice(["strip", "lstrip", "rstrip"])
        c["chars"] = rng.choice([None, None, ["bytes", b_rbytes(rng)], ["bytes", []], ["memview", s[:1], [0]], ["str", [97]]])
    elif r < 0.84:
        c["fn"] = ty + ".rich"
        c["other"] = rng.choice([["bytes", s], ["bytes", s + [1]], ["bytes", s[:-1]], ["bytes", b_rbytes(rng)],
                                 ["bytearray", s], ["memview", s, [0]], b_robj(rng, 0)])
        c["op"] = rng.choice(["lt", "le", "eq", "ne", "gt", "ge"])
    elif r < 0.86 and ty == "bytes":
        c["fn"] = "bytes.mul"
        c["n"] = rng.choice([0, 1, 2, 3, -1, sys.maxsize, sys.maxsize // 2, sys.maxsize // 2 + 1, 2 ** 63, -2 ** 64, 2 ** 47])
    elif r < 0.88 and ty == "bytes":
        c["fn"] = "bytes." + rng.choice(["getitem", "getitem", "getslice"])
        c["i"] = rng.choice([0, 1, -1, len(s), -len(s), len(s) - 1, -len(s) - 1, 2 ** 63, -2 ** 63 - 1, sys.maxsize])
        c["sl"] = b_rslice(rng, len(s))
    elif r < 0.90 and ty == "bytes":
        c["fn"] = "bytes.escape"
        pool = list(b"\\\\\\xnrtbfva'\"0123456789abcdefgABCDEF\n?")
        c["s"] = [rng.choice(pool) for _ in range(rng.randint(0, 10))]
        c["err"] = rng.choice([None, "strict", "replace", "ignore", "bogus"])
    elif r < 0.92 and ty == "bytes":
        c["fn"] = "bytes.iter"
        ops = []
        for _ in range(rng.randint(1, 8)):
            k = rng.random()
            if k < 0.5:
                ops.append(["next"])
            elif k < 0.7:
                ops.append(["len"])
            elif k < 0.85:
                ops.append(["reduce"])
            else:
                ops.append(["setstate", rng.choice([0, 1, -1, -5, len(s), len(s) + 3, 2 ** 63, -2 ** 63 - 1])])
        c["ops"] = ops
    elif r < 0.93 and ty == "bytes":
        c["fn"] = "bytes.maketrans"
        n = rng.randint(0, 4)
        c["a"] = ["bytes", b_rbytes(rng, n)]
        c["b"] = rng.choice([["bytes", b_rbytes(rng, n)], ["bytearray", b_rbytes(rng, n)], ["bytes", b_rbytes(rng, n + 1)], ["str", [97]]])
    elif r < 0.95 and ty == "bytes":
        c["fn"] = "bytes." + rng.choice(["size", "asstring", "asstringandsize", "pyconcat", "pyjoin"])
        c["x"] = rng.choice([["bytes", b_rbytes(rng)], ["bytes", [97, 0, 98]], ["bytes", []], ["str", [97]], ["int", 1],
                             ["bytearray", [1]], ["none"]])
        c["wantlen"] = rng.random() < 0.5
        c["it"] = ["list", [["bytes", b_rbytes(rng)] for _ in range(rng.randint(0, 3))]]
    elif r < 0.96 and ty == "bytes":
        c["fn"] = "bytes.fromformat"
        conv = [(b"%d", "i"), (b"%i", "i"), (b"%u", "i"), (b"%ld", "l"), (b"%lu", "l"), (b"%zd", "l"), (b"%zu", "l"),
                (b"%x", "i"), (b"%c", "c"), (b"%s", "s"), (b"%.3s", "s"), (b"%.0s", "s"), (b"%5d", "i"), (b"%%", ""),
                (b"%-5s", "s"), (b"%p", "p")]
        fmt, args = b"", []
        for _ in range(rng.randint(0, 4)):
            f, k = rng.choice(conv)
            fmt += rng.choice([b"", b"x", b"ab "]) + f
            if k in ("i", "l"):
                args.append(["i", rng.choice([0, 1, -1, 2 ** 31 - 1, -2 ** 31, 12345])])
            elif k == "c":
                args.append(["i", rng.choice([0, 65, 255, 256, -1])])
            elif k == "s":
                args.append(["s", [rng.randint(97, 122) for _ in range(rng.randint(0, 6))]])
            elif k == "p":
                args.append(["p", rng.randint(1, 2 ** 40)])
        c["s"] = list(fmt + rng.choice([b"", b"", b"%", b"%q", b"%l"]))
        c["args"] = args
    elif r < 0.97 and ty == "bytes":
        c["fn"] = "bytes.privfind"
        c["n"] = rng.choice([s[:rng.randint(0, 3)], s[-2:], b_rbytes(rng, 2)])
        c["off"] = rng.randint(0, 5)
    elif ty == "bytearray" and r < 0.86:
        c["fn"] = "bytearray.reduce"
        c["proto"] = rng.choice([0, 1, 2, 3, 4, 5])
    elif ty == "bytearray" and r < 0.89:
        c["fn"] = "bytearray.initfail"
        k = rng.randint(1, 6)
        items = [["int", rng.randint(0, 255)] for _ in range(k)]
        items[rng.randint(0, k - 1)] = ["int", rng.choice([256, 1000, -1, 2 ** 70])]
        c["items"] = items
    elif ty == "bytearray" and r < 0.91:
        c["fn"] = "bytearray.evilextend"
        c["s"] = [97] * rng.randint(1, 40)
        c["v"] = b_rbytes(rng)
    else:
        c["fn"] = "bytearray.ops"
        c["ops"] = [b_rbaop(rng) for _ in range(rng.randint(1, 8))]
    return c


def b_rbaop(rng):
    r = rng.random()
    n = 8

    def bo():
        return rng.choice([["int", rng.randint(0, 255)], ["int", rng.randint(0, 255)], ["int", 256], ["int", -1], ["int", 2 ** 70],
                           ["index", 5], ["bool", True], ["str", [97]], ["none"], b_bflt(1.0)])

    def src():
        return rng.choice([["bytes", b_rbytes(rng)], ["bytes", b_rbytes(rng)], ["bytes", []], ["bytearray", b_rbytes(rng)],
                           ["list", b_rbyteobjs(rng)], ["iter", b_rbyteobjs(rng)], ["tuple", b_rbyteobjs(rng)], ["int", 3], ["str", [97]],
                           ["str", []], ["none"], ["memview", b_rbytes(rng), [0]]])

    def idx():
        return rng.choice([0, 1, -1, 2, -2, 5, -5, 40, -40, 2 ** 63, -2 ** 63 - 1, sys.maxsize, -sys.maxsize - 1])

    if r < 0.05:
        return {"m": rng.choice(["iterstart", "iternext", "iternext", "iternext"])}
    if r < 0.12:
        return {"m": "append", "x": bo()}
    if r < 0.20:
        return {"m": "insert", "i": idx(), "x": bo()}
    if r < 0.28:
        return {"m": "pop", "i": rng.choice([None, None, idx()])}
    if r < 0.33:
        return {"m": "remove", "x": rng.choice([["int", rng.randint(0, 255)], ["int", 97], bo()])}
    if r < 0.36:
        return {"m": "clear"}
    if r < 0.38:
        return {"m": "reverse"}
    if r < 0.44:
        return {"m": "extend", "x": src()}
    if r < 0.50:
        return {"m": "resize", "n": rng.choice([0, 1, 2, 5, 9, 10, 16, 32, 33, 100, 200, -1, 2 ** 63, 2 ** 47])}
    if r < 0.55:
        return {"m": "setitem", "i": idx(), "x": bo()}
    if r < 0.59:
        return {"m": "delitem", "i": idx()}
    if r < 0.72:
        return {"m": "setslice", "sl": b_rslice(rng, n), "x": src()}
    if r < 0.74:
        return {"m": "setslice_self", "sl": b_rslice(rng, n)}
    if r < 0.80:
        return {"m": "delslice", "sl": b_rslice(rng, n)}
    if r < 0.83:
        return {"m": "iconcat", "x": src()}
    if r < 0.86:
        return {"m": "imul", "n": rng.choice([0, 1, 2, 3, -1, 2 ** 63, sys.maxsize])}
    if r < 0.90:
        return {"m": rng.choice(["export", "export", "release"])}
    if r < 0.92:
        return {"m": rng.choice(["getitem", "getslice"]), "i": idx(), "sl": b_rslice(rng, n)}
    if r < 0.94:
        return {"m": rng.choice(["copy", "sizeof"])}
    if r < 0.95:
        return {"m": "mul", "n": rng.choice([0, 1, 2, -1, sys.maxsize, 2 ** 63])}
    if r < 0.96:
        return {"m": "concat", "x": src()}
    if r < 0.98:
        return {"m": "init", "x": rng.choice([None, ["bytes", b_rbytes(rng)], ["int", 5], ["int", 0], ["int", -1], ["str", [97]],
                                              ["list", [["int", rng.randint(0, 255)] for _ in range(rng.randint(0, 4))]],
                                              ["tuple", [["int", 1], ["index", 2]]], ["iter", b_rbyteobjs(rng)], ["none"]]),
                "enc": rng.choice([None, None, "latin-1"]), "err": rng.choice([None, None, "strict"])}
    return {"m": "itersetstate", "n": rng.choice([0, 1, 3, -1, -5, 100, 2 ** 63])}


def b_ba_step(b, views, op, tmp):
    m = op["m"]
    if m == "append":
        return b.append(b_build(op["x"]))
    if m == "insert":
        return b.insert(op["i"], b_build(op["x"]))
    if m == "pop":
        return b.pop() if op.get("i") is None else b.pop(op["i"])
    if m == "remove":
        return b.remove(b_build(op["x"]))
    if m == "clear":
        return b.clear()
    if m == "reverse":
        return b.reverse()
    if m == "extend":
        return b.extend(b_build(op["x"]))
    if m == "resize":
        return b.resize(op["n"])
    if m == "setitem":
        b[op["i"]] = b_build(op["x"])
        return None
    if m == "delitem":
        del b[op["i"]]
        return None
    if m == "setslice":
        b[slice(*op["sl"])] = b_build(op["x"])
        return None
    if m == "setslice_self":
        b[slice(*op["sl"])] = b
        return None
    if m == "delslice":
        del b[slice(*op["sl"])]
        return None
    if m == "iconcat":
        tmp[0] = b
        tmp[0] += b_build(op["x"])
        return None
    if m == "imul":
        tmp[0] = b
        tmp[0] *= op["n"]
        return None
    if m == "export":
        views.append(memoryview(b))
        return None
    if m == "release":
        if views:
            views.pop().release()
        return None
    if m == "copy":
        c = b.copy()
        return [list(c), c.__alloc__()]
    if m == "getitem":
        return b[op["i"]]
    if m == "getslice":
        return ["A", list(b[slice(*op["sl"])])]
    if m == "mul":
        c = b * op["n"]
        return [list(c), c.__alloc__()]
    if m == "concat":
        c = b + b_build(op["x"])
        return [list(c), c.__alloc__()]
    if m == "init":
        args = []
        kw = {}
        if op.get("x") is not None:
            args.append(b_build(op["x"]))
        if op.get("enc") is not None:
            kw["encoding"] = op["enc"]
        if op.get("err") is not None:
            kw["errors"] = op["err"]
        return b.__init__(*args, **kw)
    if m == "sizeof":
        return b.__sizeof__()
    if m == "itersetstate":
        it = iter(b)
        it.__setstate__(op["n"])
        red = it.__reduce__()
        red = red[2] if len(red) == 3 else "empty"
        h = it.__length_hint__()
        return [red, h, next(it, "stop")]
    raise ValueError(m)


def b_run_ba_ops(c):
    b = bytearray(bytes(c["s"]))
    views = []
    out = []
    tmp = [None]
    it = iter(b)
    for op in c["ops"]:
        if op["m"] == "iterstart":
            it = iter(b)
            r = {"ok": None}
        elif op["m"] == "iternext":
            v = next(it, "stop")
            r = {"ok": [v, it.__length_hint__()]}
        else:
            r = common.py_result(lambda: b_ba_step(b, views, op, tmp))
        out.append([r, [list(b), b.__alloc__()]])
    for v in views:
        v.release()
    return {"ok": out}


class BClearingBuffer:
    def __init__(self, target, data):
        self.target, self.data = target, data

    def __buffer__(self, flags):
        self.target.clear()
        return memoryview(self.data)


BCFMT = None


def b_capi():
    global BCFMT
    if BCFMT is None:
        import ctypes
        BCFMT = ctypes
        api = ctypes.pythonapi
        api.PyBytes_Size.restype = ctypes.c_ssize_t
        api.PyBytes_Size.argtypes = [ctypes.py_object]
        api.PyBytes_AsString.restype = ctypes.c_void_p
        api.PyBytes_AsString.argtypes = [ctypes.py_object]
        api.PyBytes_AsStringAndSize.restype = ctypes.c_int
        api.PyBytes_FromFormat.restype = ctypes.py_object
    return BCFMT


def b_run_capi(c, m):
    ct = b_capi()
    api = ct.pythonapi
    if m == "size":
        return api.PyBytes_Size(b_build(c["x"]))
    if m == "asstring":
        o = b_build(c["x"])
        p = api.PyBytes_AsString(o)
        return b_benc(ct.string_at(p, len(o)))
    if m == "asstringandsize":
        o = b_build(c["x"])
        buf = ct.c_void_p()
        n = ct.c_ssize_t()
        api.PyBytes_AsStringAndSize.argtypes = [ct.py_object, ct.POINTER(ct.c_void_p), ct.c_void_p]
        rc = api.PyBytes_AsStringAndSize(o, ct.byref(buf), ct.addressof(n) if c["wantlen"] else None)
        assert rc == 0
        return b_benc(ct.string_at(buf, len(o)))
    if m == "pyconcat":
        s = bytes(c["s"])
        o = b_build(c["x"])
        # keep a second reference, so that this is the shared branch
        p = ct.py_object(s)
        # PyBytes_Concat releases the reference in *pv; give it one of its own
        api.Py_IncRef.argtypes = [ct.py_object]
        api.Py_IncRef.restype = None
        api.Py_IncRef(s)
        api.PyBytes_Concat.argtypes = [ct.POINTER(ct.py_object), ct.py_object]
        api.PyBytes_Concat.restype = None
        api.PyBytes_Concat(ct.byref(p), o)
        return b_benc(p.value)
    if m == "pyjoin":
        api.PyBytes_Join.restype = ct.py_object
        api.PyBytes_Join.argtypes = [ct.py_object, ct.py_object]
        return b_benc(api.PyBytes_Join(b_build(c["x"]), b_build(c["it"])))
    if m == "fromformat":
        args = []
        for a in c["args"]:
            if a[0] == "i":
                args.append(ct.c_long(a[1]))
            elif a[0] == "s":
                args.append(ct.c_char_p(bytes(a[1])))
            else:
                args.append(ct.c_void_p(a[1]))
        return b_benc(api.PyBytes_FromFormat(ct.c_char_p(bytes(c["s"])), *args))
    raise ValueError(m)


def run_bytes(case):
    c = case
    ty, m = c["fn"].split(".")
    mk = bytes if ty == "bytes" else bytearray

    def go():
        s = mk(bytes(c["s"]))
        if m in BCOMMON_M:
            return b_benc(getattr(s, m)())
        if m in BSEARCH_M + ["startswith", "endswith"]:
            args = [b_build(c["sub"])]
            if c["start"] is not None or c["end"] is not None:
                args += [c["start"], c["end"]]
            return getattr(s, m)(*args)
        if m == "contains":
            return b_build(c["sub"]) in s
        if m == "hex":
            a = []
            if c.get("sep") is not None:
                a.append(b_build(c["sep"]))
                if c.get("n") is not None:
                    a.append(c["n"])
            elif c.get("n") is not None:
                return b_benc(s.hex(bytes_per_sep=c["n"]))
            return b_benc(s.hex(*a))
        if m == "fromhex":
            return b_benc(mk.fromhex(b_build(c["x"])))
        if m == "mod":
            return b_benc(s % b_build(c["arg"]))
        if m == "repr":
            return b_benc(repr(s))
        if m == "bufinfo":
            v = memoryview(s)
            res = [list(v), v.readonly]
            v.release()
            return res
        if m == "new":
            a = [] if c.get("x") is None else [b_build(c["x"])]
            kw = {}
            if c.get("enc") is not None:
                kw["encoding"] = c["enc"]
            if c.get("err") is not None:
                kw["errors"] = c["err"]
            return b_benc(mk(*a, **kw))
        if m == "join":
            return b_benc(s.join(b_build(c["it"])))
        if m == "translate":
            if c.get("delete") is None:
                return b_benc(s.translate(b_build(c["table"])))
            return b_benc(s.translate(b_build(c["table"]), b_build(c["delete"])))
        if m in ("removeprefix", "removesuffix"):
            return b_benc(getattr(s, m)(b_build(c["arg"])))
        if m in ("strip", "lstrip", "rstrip"):
            if c.get("chars") is None:
                return b_benc(getattr(s, m)())
            return b_benc(getattr(s, m)(b_build(c["chars"])))
        if m == "rich":
            r = getattr(s, "__" + c["op"] + "__")(b_build(c["other"]))
            return "NotImplemented" if r is NotImplemented else r
        if m == "mul":
            return b_benc(s * c["n"])
        if m == "getitem":
            return s[c["i"]]
        if m == "getslice":
            return b_benc(s[slice(*c["sl"])])
        if m == "escape":
            with warnings.catch_warnings(record=True) as w:
                warnings.simplefilter("always")
                if c.get("err") is None:
                    r, n = codecs.escape_decode(s)
                else:
                    r, n = codecs.escape_decode(s, c["err"])
            return [b_benc(r), n, str(w[0].message) if w else None]
        if m == "iter":
            it = iter(s)
            out = []
            for op in c["ops"]:
                if op[0] == "next":
                    out.append(next(it, "stop"))
                elif op[0] == "len":
                    out.append(it.__length_hint__())
                elif op[0] == "reduce":
                    r = it.__reduce__()
                    out.append([b_benc(r[1][0]), r[2]] if len(r) == 3 else "empty")
                else:
                    try:
                        it.__setstate__(op[1])
                        out.append("ok")
                    except Exception as e:
                        out.append({"exc": type(e).__name__, "msg": str(e)})
            return out
        if m == "maketrans":
            return b_benc(bytes.maketrans(b_build(c["a"]), b_build(c["b"])))
        if m == "reduce":
            r = s.__reduce_ex__(c["proto"])
            assert r[0] is bytearray and r[2] is None
            return b_benc(r[1])
        if m == "initfail":
            b = bytearray()
            items = [b_build(x) for x in c["items"]]
            e = None
            try:
                b.__init__(items)
            except Exception as ex:
                e = type(ex).__name__
            k = next((i for i, x in enumerate(items) if not 0 <= x < 256), len(items))
            return [len(b), list(b[:k]), e]
        if m == "evilextend":
            b = bytearray(bytes(c["s"]))
            b.extend(BClearingBuffer(b, bytes(c["v"])))
            return [len(b), list(b[len(c["s"]):])]
        if m == "privfind":
            import mmap
            hay, needle = bytes(c["s"]), bytes(c["n"])
            off = c["off"]
            if not hay or not needle:
                return off if not needle else -1
            mm = mmap.mmap(-1, len(hay))
            mm.write(hay)
            # _PyBytes_Find via mmap.find; the offset of the result is relative to 0
            r = mm.find(needle, 0)
            mm.close()
            return r + off if r >= 0 else -1
        if m in ("size", "asstring", "asstringandsize", "pyconcat", "pyjoin", "fromformat"):
            return b_run_capi(c, m)
        raise ValueError(m)

    if m == "ops":
        return b_run_ba_ops(c)
    return common.py_result(go)


# ===== end of family bytes ============================================


# ===== family mem: memoryview =========================================


def gen_mem(rng):
    return None


def run_mem(case):
    raise NotImplementedError(case["fn"])


# ===== end of family mem ==============================================


FAMILIES = {"seq": (gen_seq, run_seq), "bytes": (gen_bytes, run_bytes), "mem": (gen_mem, run_mem)}
PREFIXES = {"tuple": "seq", "list": "seq", "bytes": "bytes", "bytearray": "bytes", "mem": "mem"}


def main():
    only = choose_family()
    names = [only] if only else list(FAMILIES)

    def gen_case(rng):
        return FAMILIES[rng.choice(names)][0](rng)

    def run_python(case):
        return FAMILIES[PREFIXES[case["fn"].split(".")[0]]][1](case)

    common.main(gen_case, run_python)


if __name__ == "__main__":
    main()
