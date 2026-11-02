"""Differential test: Lean model of math's integer functions and the related
int operations vs. the running CPython.

Usage: python3 difftest/mathint_diff.py [--cases N] [--seed S]

Exits non-zero on any mismatch. See difftest/common.py.
"""

import math
import sys

sys.set_int_max_str_digits(0)

import common

P63, P64 = 1 << 63, 1 << 64

FIB = [0, 1]
while len(FIB) < 1500:
    FIB.append(FIB[-1] + FIB[-2])


def edge_nat(rng, big=True):
    """A non-negative int biased to the boundaries the C code branches on."""
    k = rng.randrange(1, 200 if big else 70)
    base = rng.choice([
        0, 1, 2, 3, 20, 21, 31, 32, 33, 34, 35, 62, 63, 64, 65, 66, 67, 68, 127, 128, 129,
        (1 << 30) - 1, 1 << 30, (1 << 60) - 1, 1 << 60, P63 - 1, P63, P63 + 1,
        P64 - 1, P64, P64 + 1, 1 << k, (1 << k) - 1, (1 << k) + 1,
        rng.randrange(1 << k), rng.randrange(1000), rng.randrange(1 << 64),
        rng.getrandbits(rng.randrange(1, 4000 if big else 70)),
    ])
    if not big and base > (1 << 70):
        base = rng.randrange(1 << 70)
    return base + rng.choice([0, 0, 0, -1, 1, rng.randrange(-3, 4)]) if base > 3 else base


def edge_int(rng, big=True):
    v = edge_nat(rng, big)
    return -v if rng.random() < 0.3 else v


# Limit tables of perm_comb_small: test both sides of every entry.
COMB1 = [0, 0] + [127] * 14 + [116, 105, 97, 91, 86, 82, 78, 76, 74, 72, 71, 70, 69, 68, 68,
                                67, 67, 67, 67]
COMB2 = [0, P64 - 1, 4294967296, 3329022, 102570, 13467, 3612, 1449, 746, 453, 308, 227, 178, 147]
PERM = [0, P64 - 1, 4294967296, 2642246, 65537, 7133, 1627, 568, 259, 142, 88, 61, 45, 36, 30,
        26, 24, 22, 21, 20, 20]


def comb_args(rng, perm):
    r = rng.random()
    if r < 0.35:
        table = PERM if perm else rng.choice([COMB1, COMB2])
        k = rng.randrange(2, len(table) + 2)
        lim = table[k] if k < len(table) else rng.randrange(40, 200)
        lim = min(lim, 1 << 40)
        n = max(0, lim + rng.randrange(-3, 4))
        if not perm and rng.random() < 0.5:
            k = n - k  # exercise k = min(k, n - k)
        return n, k
    if r < 0.55:
        n = rng.randrange(0, 300)
        return n, rng.randrange(-2, n + 3)
    if r < 0.7:
        # huge n with small k, or k near n
        n = rng.choice([P63 - 1, P63, P63 + 1, P64, rng.getrandbits(rng.randrange(1, 200))])
        k = rng.randrange(0, 40)
        if not perm and rng.random() < 0.5:
            k = n - k
        return n, k
    if r < 0.8:
        # OverflowError region: min(k, n - k) > LLONG_MAX, or k > n
        n = rng.choice([P64, P64 + 1, 1 << 65, 1 << 100, P63 - 1, P63])
        k = rng.choice([P63 - 1, P63, P63 + 1, n // 2, n + 1, n - P63, n - P63 + 1, 1 << 70])
        return n, k
    n, k = edge_int(rng, False), edge_int(rng, False)
    if n > 0 and k > 0 and 600 < min(k, max(n - k, 0)) < P63 and n >= k:
        return None  # result too large to compute quickly
    return n, k


class Idx:
    """An argument that is an int only through __index__, off the exact-int fast paths."""

    def __init__(self, v):
        self.v = v

    def __index__(self):
        return self.v


class BytesSub(bytes):
    """A bytes subclass: 3.15 takes the buffer route and never calls __bytes__."""

    def __bytes__(self):
        return b"\x7f\x7f"


class BytearraySub(bytearray):
    def __bytes__(self):
        return b"\x7f\x7f"


class HasDunder:
    def __init__(self, bs):
        self.bs = bs

    def __bytes__(self):
        return bytes(self.bs)


class DunderRaises:
    def __bytes__(self):
        raise KeyError("from __bytes__")


class DunderBad:
    def __bytes__(self):
        return 5


class BufferRaises:
    def __buffer__(self, flags):
        raise KeyError("from __buffer__")


class BufferAndDunder:
    """Both protocols: the buffer wins in 3.15."""

    def __init__(self, bs):
        self.bs = bs

    def __buffer__(self, flags):
        return memoryview(bytes(self.bs))

    def __bytes__(self):
        return b"\x7f\x7f"


class IntSub(int):
    pass


class IntSubRaises(int):
    def __new__(cls, *args):
        raise KeyError("from __new__")


def released():
    m = memoryview(b"ab")
    m.release()
    return m


# kind -> route, failure a case states, and how run_python builds the object
OBJ_ROUTES = {
    "bytes": "exact", "bytes_sub": "buffer", "bytearray": "buffer", "bytearray_sub": "buffer",
    "memoryview": "buffer", "buffer_and_dunder": "buffer", "strided": "buffer",
    "released": "buffer", "buffer_raises": "buffer", "list": "other", "tuple": "other",
    "iter": "other", "dunder": "other", "dunder_raises": "other", "dunder_bad": "other",
    "str": "other", "int": "other", "none": "other", "float": "other", "list_big": "other",
}
OBJ_FAIL = {
    "strided": ("BufferError", "memoryview: underlying buffer is not C-contiguous"),
    "released": ("ValueError", "operation forbidden on released memoryview object"),
    "buffer_raises": ("KeyError", "'from __buffer__'"),
    "dunder_raises": ("KeyError", "'from __bytes__'"),
    "dunder_bad": ("TypeError", "~__bytes__ must return bytes"),
    "str": ("TypeError", "cannot convert 'str' object to bytes"),
    "int": ("TypeError", "cannot convert 'int' object to bytes"),
    "none": ("TypeError", "cannot convert 'NoneType' object to bytes"),
    "float": ("TypeError", "cannot convert 'float' object to bytes"),
    "list_big": ("ValueError", "bytes must be in range(0, 256)"),
}


def build_obj(kind, bs):
    return {
        "bytes": lambda: bytes(bs), "bytes_sub": lambda: BytesSub(bs),
        "bytearray": lambda: bytearray(bs), "bytearray_sub": lambda: BytearraySub(bs),
        "memoryview": lambda: memoryview(bytes(bs)),
        "buffer_and_dunder": lambda: BufferAndDunder(bs),
        "strided": lambda: memoryview(b"abcd")[::2], "released": released,
        "buffer_raises": BufferRaises, "list": lambda: list(bs), "tuple": lambda: tuple(bs),
        "iter": lambda: iter(bs), "dunder": lambda: HasDunder(bs), "dunder_raises": DunderRaises,
        "dunder_bad": DunderBad, "str": lambda: "ab", "int": lambda: 5, "none": lambda: None,
        "float": lambda: 1.5, "list_big": lambda: [1, 300],
    }[kind]()


def gen_case(rng):
    fn = rng.choice(["isqrt", "isqrt", "comb", "comb", "perm", "perm", "factorial", "gcd",
                     "lcm", "pow", "to_bytes", "to_bytes", "from_bytes", "from_bytes_obj",
                     "divmod", "round"])
    c = {"mod": "mathint", "fn": fn}
    # math re-exports the objects of math.integer; reach them both ways, and off the
    # exact-int fast paths through __index__.
    if fn in ("isqrt", "comb", "perm", "factorial", "gcd", "lcm"):
        c.update(ns=rng.choice(["math", "math.integer"]), index=rng.random() < 0.15)
    if fn == "isqrt":
        if rng.random() < 0.3:
            r = edge_nat(rng)
            n = r * r + rng.choice([-1, 0, 1, 2 * r, 2 * r + 1, rng.randrange(-2, 3)])
        else:
            n = edge_int(rng)
        c["n"] = n
    elif fn in ("comb", "perm"):
        a = comb_args(rng, fn == "perm")
        if a is None:
            return None
        n, k = a
        if n >= 0 and k >= 0 and n >= k and 3000 < min(k, n - k) < P63:
            return None
        if fn == "perm" and n >= 0 and k >= 0 and n >= k and 600 < k < P63:
            return None
        c.update(n=n, k=k)
        if fn == "perm" and rng.random() < 0.1:
            c.update(n=rng.randrange(-3, 400), k=None)
    elif fn == "factorial":
        c["n"] = rng.choice([rng.randrange(-3, 3000), rng.randrange(-3, 40), P63 - 1 + 1, P63,
                             -P63, -P63 - 1, -(1 << 70), 1 << 70, P64])
        if c["n"] == P63 - 1:
            return None
    elif fn in ("gcd", "lcm"):
        m = rng.choice([0, 1, 2, 2, 2, 3, 4, 6])
        common_f = edge_nat(rng) if rng.random() < 0.5 else 1
        args = []
        for _ in range(m):
            v = edge_int(rng) * (common_f if rng.random() < 0.7 else 1)
            if rng.random() < 0.1:
                v = rng.choice([0, 1, -1])
            args.append(v)
        if m >= 2 and rng.random() < 0.15:
            # consecutive Fibonacci numbers: the longest runs of Lehmer's inner loop
            k = rng.randrange(40, len(FIB) - 1)
            g = rng.choice([1, 1, edge_nat(rng, False) or 1])
            args[0], args[1] = FIB[k + 1] * g, FIB[k] * g
        if fn == "lcm" and sum(abs(a).bit_length() for a in args) > 20000:
            return None
        c["args"] = args
    elif fn == "pow":
        m = edge_int(rng, rng.random() < 0.2)
        if rng.random() < 0.1:
            m = rng.choice([0, 1, -1, 2, -2])
        a = edge_int(rng, rng.random() < 0.2)
        if rng.random() < 0.3 and m:
            a = a * abs(m) + rng.choice([1, -1, 0])
        b = rng.choice([-1, -1, -2, -3, -rng.randrange(1, 1000), 0, 1, 2, rng.randrange(100),
                        -edge_nat(rng, False)])
        c.update(a=a, b=b, m=m)
    elif fn == "to_bytes":
        v = edge_int(rng, rng.random() < 0.3)
        nb = (abs(v).bit_length() + 8) // 8
        length = rng.choice([nb, nb - 1, nb + 1, nb - 2, 0, 1, rng.randrange(0, 20), -1,
                             -P63, -P63 - 1, P63, (abs(v).bit_length() + 7) // 8,
                             P63 - 1, P63 - 2, P63 - 33, 255, 256, 257])  # the writer's 256-byte buffer
        c.update(v=v, length=length, signed=rng.random() < 0.5,
                 byteorder=rng.choice(["big", "little", "big", "little", "mid", "Big"]),
                 index=rng.random() < 0.15)
        # The clinic defaults: length=1, byteorder='big', signed=False.
        r = rng.random()
        if r < 0.1:
            c.update(length=1, byteorder="big", signed=False, omit=3)
        elif r < 0.2:
            c.update(byteorder="big", signed=False, omit=2)
        elif r < 0.3:
            c.update(signed=False, omit=1)
    elif fn == "from_bytes":
        n = rng.choice([0, 1, 2, 3, 4, 7, 8, 9, 15, 16, 17, rng.randrange(0, 60)])
        fill = rng.choice([None, 0, 255, 128, 127])
        bs = [rng.randrange(256) if fill is None or rng.random() < 0.2 else fill for _ in range(n)]
        c.update(bytes=bs, signed=rng.random() < 0.5,
                 byteorder=rng.choice(["big", "little", "big", "little", "mid"]))
    elif fn == "from_bytes_obj":
        n = rng.choice([0, 1, 2, 3, 4, 7, 8, 9, 15, 16, rng.randrange(0, 40)])
        fill = rng.choice([None, 0, 255, 128])
        bs = [rng.randrange(256) if fill is None or rng.random() < 0.2 else fill for _ in range(n)]
        kind = rng.choice(list(OBJ_ROUTES))
        c.update(kind=kind, route=OBJ_ROUTES[kind], bytes=bs, signed=rng.random() < 0.5,
                 byteorder=rng.choice(["big", "little", "big", "little", "big", "little", "mid"]))
        if kind in OBJ_FAIL:
            exc, msg = OBJ_FAIL[kind]
            c["fail"] = {"exc": exc, "msg": msg}
        cls = rng.choice(["int", "int", "sub", "sub_raises"])
        c["cls"] = cls
        if cls == "sub_raises":
            c["ctor_fail"] = {"exc": "KeyError", "msg": "'from __new__'"}
    elif fn == "divmod":
        r = rng.random()
        if r < 0.15:
            b = edge_int(rng) | (1 << rng.randrange(9001, 9500))
            a = b * rng.getrandbits(rng.randrange(4500, 7000)) + rng.randrange(-5, 5)
            a, b = (a, b) if rng.random() < 0.5 else (-a, b)
            if rng.random() < 0.5:
                b = -b
        else:
            a, b = edge_int(rng), edge_int(rng)
            if rng.random() < 0.1:
                b = rng.choice([0, 1, -1])
        c.update(a=a, b=b)
    elif fn == "round":
        k = rng.randrange(0, 60)
        x = edge_int(rng, False)
        if rng.random() < 0.4:
            x = (rng.randrange(-1000, 1000) * 2 + 1) * 5 * 10 ** k // 10 if k else x  # ties
        c.update(x=x, nd=rng.choice([None, -k, -k, k, 0, -1]))
    return c


def run_python(c):
    fn = c["fn"]
    ns = math.integer if c.get("ns") == "math.integer" else math
    arg = (lambda x: x) if not c.get("index") or c.get("ns") is None else Idx
    if fn == "isqrt":
        return common.py_result(lambda: ns.isqrt(arg(c["n"])))
    if fn == "comb":
        return common.py_result(lambda: ns.comb(arg(c["n"]), arg(c["k"])))
    if fn == "perm":
        return common.py_result(lambda: ns.perm(arg(c["n"]), c["k"] if c["k"] is None else arg(c["k"])))
    if fn == "factorial":
        return common.py_result(lambda: ns.factorial(arg(c["n"])))
    if fn == "gcd":
        return common.py_result(lambda: ns.gcd(*map(arg, c["args"])))
    if fn == "lcm":
        return common.py_result(lambda: ns.lcm(*map(arg, c["args"])))
    if fn == "pow":
        return common.py_result(lambda: pow(c["a"], c["b"], c["m"]))
    if fn == "to_bytes":
        length = Idx(c["length"]) if c["index"] else c["length"]
        omit = c.get("omit", 0)
        if omit == 3:
            return common.py_result(lambda: list(c["v"].to_bytes()))
        if omit == 2:
            return common.py_result(lambda: list(c["v"].to_bytes(length)))
        if omit == 1:
            return common.py_result(lambda: list(c["v"].to_bytes(length, c["byteorder"])))
        return common.py_result(lambda: list(c["v"].to_bytes(length, c["byteorder"],
                                                             signed=c["signed"])))
    if fn == "from_bytes":
        return common.py_result(lambda: int.from_bytes(bytes(c["bytes"]), c["byteorder"],
                                                       signed=c["signed"]))
    if fn == "from_bytes_obj":
        cls = {"int": int, "sub": IntSub, "sub_raises": IntSubRaises}[c["cls"]]
        obj = build_obj(c["kind"], c["bytes"])
        return common.py_result(lambda: int(cls.from_bytes(obj, c["byteorder"], signed=c["signed"])))
    if fn == "divmod":
        return common.py_result(lambda: list(divmod(c["a"], c["b"])))
    if fn == "round":
        return common.py_result(lambda: round(c["x"]) if c["nd"] is None else round(c["x"], c["nd"]))
    raise ValueError(fn)


if __name__ == "__main__":
    for name in ("comb", "factorial", "gcd", "isqrt", "lcm", "perm"):
        assert getattr(math, name) is getattr(math.integer, name), name
    common.main(gen_case, run_python)
