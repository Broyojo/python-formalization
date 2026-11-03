"""Differential test: Lean model of list, array.array, collections.deque,
defaultdict, _count_elements and _tuplegetter vs. the running CPython.

Usage: python3 difftest/sequences_diff.py [--cases N] [--seed S]

A case builds one object and applies a random sequence of operations; after
every operation it records the result (value or exception and message) and the
object's state. The state of a deque includes the number of 64-slot blocks in use
and that of an array the `allocated` count, both read from `__sizeof__()`, and
whether `ob_item` is NULL (from `buffer_info()`), so the block arithmetic and the
over-allocation are checked, not only the contents. Exceptions compare exactly
(class and message), except where the model's message starts with `~`.

Deque elements include objects whose `__eq__` raises (`B`) or mutates the deque
under test (`M<k>`), which reach the exception and mutation checks of the search
loops. Array items are compared through `tobytes()`, floats and the parts of complex
numbers as bit patterns.

One state is not deterministic: `ins1` on an `e` array can raise after growing the array
(bugs/sequences-array-e-ins1-overflow-keeps-slot.yaml), which leaves the new last item
uninitialised. The harness stores 0.0 there, the model's value for such a slot, right after
the failing call and only for that slot; the length, `allocated`, the exception and the
slots that were shifted are still compared.

Results that would need gigabytes of memory are never requested: repeat counts are
steered to small values unless the C code's explicit overflow check rejects them
(MemoryError) or a small `maxlen` bounds the result.
"""

import array as array_mod
import collections
import ctypes
import copy
import io
import operator
import struct
import sys
import warnings
from array import array
from collections import defaultdict, deque

import common

warnings.simplefilter("ignore", DeprecationWarning)

M = sys.maxsize
BIG = 10 ** 5           # largest result the generator lets CPython allocate
TYPECODES = array_mod.typecodes
INT_RANGE = {"b": (-128, 127), "B": (0, 255), "h": (-2 ** 15, 2 ** 15 - 1), "H": (0, 2 ** 16 - 1),
             "i": (-2 ** 31, 2 ** 31 - 1), "I": (0, 2 ** 32 - 1), "l": (-2 ** 63, 2 ** 63 - 1),
             "L": (0, 2 ** 64 - 1), "q": (-2 ** 63, 2 ** 63 - 1), "Q": (0, 2 ** 64 - 1)}
ITEMSIZE = {tc: array(tc).itemsize for tc in TYPECODES}
BLOCK = 64 * 8 + 16
DEQUE_BASE = {}
OPS = {"lt": operator.lt, "le": operator.le, "eq": operator.eq, "ne": operator.ne,
       "gt": operator.gt, "ge": operator.ge}

sq_get = ctypes.pythonapi.PySequence_GetItem
sq_get.argtypes, sq_get.restype = [ctypes.py_object, ctypes.c_ssize_t], ctypes.py_object
sq_set = ctypes.pythonapi.PySequence_SetItem
sq_set.argtypes, sq_set.restype = [ctypes.py_object, ctypes.c_ssize_t, ctypes.py_object], ctypes.c_int
sq_del = ctypes.pythonapi.PySequence_DelItem
sq_del.argtypes, sq_del.restype = [ctypes.py_object, ctypes.c_ssize_t], ctypes.c_int


class D(deque):
    pass


class A(array):
    pass


class DD(defaultdict):
    pass


def blocks(d):
    t = type(d)
    if t not in DEQUE_BASE:
        DEQUE_BASE[t] = t().__sizeof__() - BLOCK
    return (d.__sizeof__() - DEQUE_BASE[t]) // BLOCK


# ---------------------------------------------------------------- deque elements

TARGET = [None]


class Bomb:
    __hash__ = None

    def __eq__(self, other):
        raise ValueError("boom")

    def __repr__(self):
        return "B"


class Mut:
    def __init__(self, k):
        self.k = k

    def __eq__(self, other):
        d = TARGET[0]
        if self.k == 0:
            d.append(0)
        elif self.k == 1:
            d.clear()
        elif self.k == 2:
            if d:
                d[0] = 7
        elif self.k == 3:
            d.rotate(1)
        else:
            d.append(0)
            return True
        return False

    __hash__ = None

    def __repr__(self):
        return "M%d" % self.k


BOMB = Bomb()
MUTS = [Mut(k) for k in range(5)]


def to_el(j):
    if isinstance(j, str):
        return BOMB if j == "B" else MUTS[int(j[1:])]
    return j


def from_el(x):
    return repr(x) if isinstance(x, (Bomb, Mut)) else x


# ---------------------------------------------------------------- array values

class Idx:
    __module__ = "builtins"     # so that %T and tp_name print the same name

    def __init__(self, n):
        self.n = n

    def __index__(self):
        return self.n


class ABomb:
    def __eq__(self, other):
        raise ValueError("boom")

    __hash__ = None


def to_float(bits):
    return struct.unpack("<d", bits.to_bytes(8, "little"))[0]


def float_bits(x):
    return int.from_bytes(struct.pack("<d", x), "little")


_CLS = {}


def user_cls(name, base, ns):
    """A class whose `%T` and `tp_name` both print `name`."""
    key = (name, base, tuple(sorted(ns)))
    ns = dict(ns, __module__="builtins")
    return type(name, (base,), ns)


def ret_obj(r):
    """What a user `__float__`/`__index__`/`__complex__` returns, or raises."""
    if "f" in r:
        return to_float(r["f"])
    if "fs" in r:
        return user_cls(r["fs"][0], float, {})(to_float(r["fs"][1]))
    if "i" in r:
        return r["i"]
    if "is" in r:
        return user_cls(r["is"][0], int, {})(r["is"][1])
    if "c" in r:
        return complex(to_float(r["c"][0]), to_float(r["c"][1]))
    if "cs" in r:
        return user_cls(r["cs"][0], complex, {})(complex(to_float(r["cs"][1]), to_float(r["cs"][2])))
    if "o" in r:
        return user_cls(r["o"], object, {})()
    raise ValueError(r["r"])


def user_val(j):
    ns = {}
    for key, meth in (("fl", "__float__"), ("ix", "__index__"), ("cx", "__complex__")):
        r = j.get(key)
        if r is not None:
            ns[meth] = (lambda r: lambda self: ret_obj(r))(r)
    b = j.get("b")
    if b is None:
        return user_cls(j["u"], object, ns)()
    if "f" in b:
        return user_cls(j["u"], float, ns)(to_float(b["f"]))
    if "c" in b:
        return user_cls(j["u"], complex, ns)(complex(to_float(b["c"][0]), to_float(b["c"][1])))
    return user_cls(j["u"], int, ns)(b["i"])


def werr_in(x):
    """Whether a value (or nested list) asks for DeprecationWarning to be an error."""
    if isinstance(x, dict):
        return x.get("werr", False) or any(werr_in(v) for v in x.values())
    if isinstance(x, list):
        return any(werr_in(v) for v in x)
    return False


def to_val(j):
    if isinstance(j, dict):
        if "u" in j:
            return user_val(j)
        if "f" in j:
            return to_float(j["f"])
        if "c" in j:
            return complex(to_float(j["c"][0]), to_float(j["c"][1]))
        if "s" in j:
            return "".join(map(chr, j["s"]))
        o = j["o"]
        if o == "Idx":
            return Idx(j["i"])
        if o == "Bomb":
            return ABomb()
        return {"NoneType": None, "list": [], "tuple": ()}[o]
    return j


def from_val(x):
    if isinstance(x, float):
        return {"f": float_bits(x)}
    if isinstance(x, complex):
        return {"c": [float_bits(x.real), float_bits(x.imag)]}
    if isinstance(x, str):
        return {"s": [ord(c) for c in x]}
    return x


# ---------------------------------------------------------------- generators

def edge_index(rng, n):
    """Indices around 0, +-n and every Py_ssize_t / size_t boundary."""
    return rng.choice([0, 1, -1, 2, -2, n, -n, n - 1, -n - 1, n + 1, -n + 1,
                       rng.randint(-n - 3, n + 3), rng.randint(-n - 3, n + 3),
                       M, -M, -M - 1, M + 1, -M - 2, 2 ** 64, -2 ** 64, 2 ** 64 - 1,
                       2 ** 62, -2 ** 62, 10 ** 30, -10 ** 30, 64, -64, 65, 128])


def de_elem(rng):
    r = rng.random()
    if r < 0.9:
        return rng.randint(0, 5)
    if r < 0.95:
        return "B"
    return "M%d" % rng.randrange(5)


def de_items(rng, k):
    p = rng.choice([0, 0, 1])
    return [de_elem(rng) if p else rng.randint(0, 5) for _ in range(k)]


def rand_len(rng, kind):
    if kind == "deque" and rng.random() < 0.4:
        return rng.choice([31, 32, 33, 62, 63, 64, 65, 66, 95, 96, 127, 128, 129, 130, 200])
    return rng.choice([0, 0, 1, 1, 2, 3, 4, 5, 6, 7, 8, 10, 13, 16, 17, 18, 24, rng.randrange(40)])


def rand_slice(rng, n):
    part = lambda: rng.choice([None, None, edge_index(rng, n), rng.randint(-n - 2, n + 2)])
    step = rng.choice([None, None, 1, -1, 2, -2, 3, -3, 5, edge_index(rng, n) or 1])
    if rng.random() < 0.02:
        step = 0
    return [part(), part(), step]


def slice_len(n, s):
    try:
        return len(range(*slice(*s).indices(n)))
    except ValueError:
        return 0


def repeat_factor(rng, size, maxlen, itemsize=None, inplace=True):
    """A factor that is either small, or large enough that CPython's explicit
    overflow check fires, or bounded by a small maxlen. Returns None to skip."""
    n = rng.choice([-2, -1, 0, 1, 2, 3, 2, 3, -M - 1, -2 ** 64, M, M + 1, 2 ** 62, 2 ** 61,
                    2 ** 64, M // max(size, 1), M // max(size, 1) + 1, 10 ** 30, -10 ** 30])
    if not (-M - 1 <= n <= M):
        return n            # OverflowError in the conversion
    if n <= 1 or size == 0:
        return n
    if itemsize is not None:
        nbytes = size * itemsize
        if (inplace and nbytes * n > M) or (not inplace and (n > M // size or size * n > M // itemsize)):
            return n
        return n if size * n <= BIG else None
    if size > 1 and size * n > M:
        return n
    if maxlen is not None and maxlen <= BIG:
        return n
    return n if size * n <= BIG else None


def gen_deque_op(rng, d):
    n = len(d)
    maxlen = d.maxlen
    x = de_elem(rng)
    op = rng.choice(["append", "appendleft", "pop", "popleft", "extend", "extendleft", "extend_self",
                     "extendleft_self", "iadd", "iadd_self", "rotate", "rotate", "rotate", "reverse",
                     "copy", "add", "add_self", "add_bad", "clear", "init", "init_self", "index", "index",
                     "insert", "count", "remove", "contains", "getitem", "setitem", "delitem", "imul", "mul",
                     "extend_raise", "extendleft_raise", "extend_stop", "extend_bad", "extendleft_bad",
                     "iadd_bad", "len", "maxlen", "repr", "repr_nested", "reduce", "cmp", "cmp_self",
                     "it_new", "it_new", "it_make", "it_next", "it_next", "it_next", "it_len", "it_reduce"])
    if op in ("append", "appendleft", "count", "remove", "contains"):
        return [op, x]
    if op in ("pop", "popleft", "extend_self", "extendleft_self", "iadd_self", "reverse", "copy",
              "add_self", "add_bad", "clear", "extend_bad", "extendleft_bad", "iadd_bad", "len", "maxlen",
              "repr", "reduce"):
        return [op]
    if op == "repr_nested":
        return [op] if type(d) is deque else None
    if op == "insert":
        return [op, edge_index(rng, n), x]
    if op == "index":
        k = rng.choice([1, 2, 2, 3, 3])
        return [op, x] + [edge_index(rng, n) for _ in range(k - 1)]
    if op in ("getitem", "delitem"):
        return [op, edge_index(rng, n)]
    if op == "setitem":
        return [op, edge_index(rng, n), x]
    if op in ("extend", "extendleft", "iadd", "init", "extend_raise", "extendleft_raise", "extend_stop"):
        xs = de_items(rng, rng.choice([0, 1, 2, 3, 5, 64, 70]))
        if op == "init":
            ml = rng.choice([None, None, 0, 1, 3, 10, -1, M + 1, "x"])
            return [op, xs] + ([] if ml is None else [ml])
        return [op, xs]
    if op == "init_self":
        ml = rng.choice([None, 2])
        return [op] + ([] if ml is None else [ml])
    if op == "rotate":
        if rng.random() < 0.1:
            return [op]
        return [op, rng.choice([edge_index(rng, n), rng.randint(-3 * n - 3, 3 * n + 3), rng.randint(-70, 70), 0])]
    if op in ("imul", "mul"):
        f = repeat_factor(rng, n, maxlen)
        return None if f is None else [op, f]
    if op == "add":
        k = rng.choice([0, 1, 2, 3, 70])
        return [op, de_items(rng, k), rng.choice([None, None, k, k + 2])]
    if op in ("cmp", "cmp_self"):
        if any(isinstance(e, Mut) for e in d):
            return None
        o = rng.choice(list(OPS))
        if op == "cmp_self":
            return [op, o]
        k = rng.choice([n, n, n, 0, 1, n + 1, max(n - 1, 0)])
        xs = [from_el(e) for e in list(d)[:k]] + [rng.randint(0, 5) for _ in range(k - n)]
        if xs and rng.random() < 0.5:
            xs[rng.randrange(len(xs))] = rng.randint(0, 5)
        return [op, o, xs]
    if op == "it_new":
        return [op, rng.random() < 0.5]
    if op == "it_make":
        return [op, rng.random() < 0.5, edge_index(rng, n)]
    if op in ("it_next", "it_len", "it_reduce"):
        return [op, rng.randrange(4)]
    raise AssertionError(op)


def gen_list_op(rng, l):
    n = len(l)
    x = rng.randint(0, 5)
    op = rng.choice(["append", "insert", "pop", "index", "index", "count", "remove", "getitem", "setitem",
                     "delitem", "imul", "mul", "setslice", "setslice", "setslice_self", "delslice", "delslice",
                     "extend", "init", "init_self"])
    if op in ("append", "count", "remove"):
        return [op, x]
    if op == "pop":
        return [op] if rng.random() < 0.3 else [op, edge_index(rng, n)]
    if op == "insert":
        return [op, edge_index(rng, n), x]
    if op == "index":
        return [op, x] + [edge_index(rng, n) for _ in range(rng.choice([0, 1, 1, 2, 2]))]
    if op in ("getitem", "delitem"):
        return [op, edge_index(rng, n)]
    if op == "setitem":
        return [op, edge_index(rng, n), x]
    if op in ("extend", "init"):
        return [op, [rng.randint(0, 5) for _ in range(rng.choice([0, 1, 2, 3, 5, 64]))]]
    if op == "init_self":
        return [op]
    if op in ("imul", "mul"):
        f = repeat_factor(rng, n, None)
        return None if f is None else [op, f]
    s = rand_slice(rng, n)
    if op == "setslice":
        L = slice_len(n, s)
        return [op, s, [rng.randint(0, 5) for _ in range(rng.choice([L, L, L, 0, L + 1, max(L - 1, 0), 2]))]]
    return [op, s]


def fbits(rng):
    return rng.choice([0, 1 << 63, 0x3ff0000000000000, 0xbff8000000000000, 0x7ff0000000000000,
                       0xfff0000000000000, 0x7ff8000000000000, 0x7ff8000000000001, 1, (1 << 52) - 1,
                       1 << 52, 0x47efffffe0000000, 0x47efffffffffffff, 0x47f0000000000000,
                       0x36a0000000000000, 0x3690000000000000, 0x3810000000000000, 0x380fffffffffffff,
                       0x36b0000000000001, rng.getrandbits(64), rng.getrandbits(64)
                       & 0x800fffffffffffff | (rng.randrange(860, 1160) << 52)])


def half_bits(rng):
    """The binary64 pattern of a value `PyFloat_Pack2` takes."""
    h = rng.choice([0, 0x8000, 1, 0x8001, 0x3ff, 0x400, 0x401, 0x7bff, 0xfbff, 0x7c00, 0xfc00, 0x7e00,
                    0x7c01, 0x7e01, 0xfe00, rng.getrandbits(16), rng.getrandbits(16)])
    return float_bits(struct.unpack("<e", h.to_bytes(2, "little"))[0])


def half_edge(rng):
    """Doubles around every branch of `PyFloat_Pack2`."""
    return float_bits(rng.choice([65504.0, 65505.0, 65519.0, 65519.999, 65520.0, 65536.0, 1e5, 1e6, 1e38,
                                  -65504.0, -65520.0, -1e5, 2.0 ** -14, 2.0 ** -15, 2.0 ** -24, 2.0 ** -25,
                                  2.0 ** -26, 1.5 * 2.0 ** -25, 3.0 * 2.0 ** -25, 3.0 * 2.0 ** -26,
                                  (2.0 ** 10 - 0.5) * 2.0 ** -24, 1.0 + 2.0 ** -11, 1.0 + 3 * 2.0 ** -11,
                                  1.0 + 2.0 ** -10 + 2.0 ** -11, 2.0 - 2.0 ** -11, 2.0 ** -14 - 2.0 ** -25,
                                  1e-300, 5e-324, -5e-324, rng.uniform(-70000.0, 70000.0),
                                  rng.uniform(-1.0, 1.0), rng.uniform(-1e-4, 1e-4)]))


def half_round_edge(rng):
    """Doubles near ties of binary16 and binary32, so that the float step of e_setitem
    rounds differently from a direct rounding, and near the boundaries of each format."""
    k = rng.randint(-24, 15)
    m = rng.randint(1024, 2047)
    base = m * 2.0 ** (k - 10)
    half_ulp16 = 2.0 ** (k - 11)
    x = base + half_ulp16 + rng.choice([0.0, 2.0 ** (k - 40), -2.0 ** (k - 40), 2.0 ** (k - 35), 2.0 ** (k - 36),
                                        -2.0 ** (k - 36), 2.0 ** (k - 24), 2.0 ** (k - 25), 2.0 ** (k - 26)])
    return float_bits(rng.choice([x, -x, 65519.998046875, 65519.99804687499, 65519.99609375, 65520.0,
                                  3.4028235677973366e38, 3.4028235677973362e38, 3.402823669209385e38,
                                  float.fromhex("0x1.ffffffp+127"), float.fromhex("0x1.fffffefffffffp+127"),
                                  float.fromhex("0x1.ffffff0000001p+127"), 1e300, -1e300]))


def good_val(rng, tc):
    """A value that fits typecode tc."""
    if tc == "e":
        return {"f": half_bits(rng)}
    if tc in ("Zf", "Zd"):
        return rng.choice([{"c": [fbits(rng), fbits(rng)]}, {"c": [fbits(rng), fbits(rng)]},
                           {"c": [fbits(rng), 0]}, {"f": fbits(rng)}, 1, rng.randint(-5, 5)])
    if tc in INT_RANGE:
        lo, hi = INT_RANGE[tc]
        return rng.choice([lo, hi, lo + 1, hi - 1, 0, 1, 2, 3, max(lo, 0) + 5, rng.randint(lo, hi)])
    if tc in "uw":
        return {"s": [rng.choice([97, 98, 99, 0, 0xe9, 0x20ac, 0xfeff, 0xd800, 0xdfff, 0x10000, 0x10ffff])]}
    return {"f": fbits(rng)}


def any_val(rng, tc):
    r = rng.random()
    if r < 0.6:
        return good_val(rng, tc)
    if r < 0.8:
        return rng.choice([128, -129, 256, -1, 2 ** 15, 2 ** 16, -2 ** 15 - 1, 2 ** 31, -2 ** 31 - 1, 2 ** 32,
                           2 ** 63, -2 ** 63 - 1, 2 ** 64, -2 ** 64, 2 ** 70, 2 ** 53 + 1, 3 ** 40, 2 ** 1024,
                           2 ** 1024 - 2 ** 970, 2 ** 1024 - 2 ** 971])
    if tc == "e" and r < 0.9:
        return {"f": half_edge(rng)}
    return rng.choice([{"f": fbits(rng)}, {"s": []}, {"s": [97]}, {"s": [97, 98]}, {"o": "NoneType"},
                       {"o": "Idx", "i": 5}, {"o": "Idx", "i": 2 ** 70}, {"o": "list"},
                       {"c": [fbits(rng), fbits(rng)]}])


def gen_ret(rng, kind, werr):
    """A result of a user method; `kind` is the method's natural result type."""
    r = rng.random()
    if r < 0.35:
        return {"f": fbits(rng)} if kind == "f" else ({"i": rng.choice([0, 1, -1, 5, 2 ** 64, 2 ** 1024, -2 ** 63])}
                                                       if kind == "i" else {"c": [fbits(rng), fbits(rng)]})
    if r < 0.5:
        if kind == "f":
            return {"fs": ["FS", fbits(rng), werr]}
        if kind == "i":
            return {"is": ["IS", rng.choice([3, 2 ** 70]), werr]}
        return {"cs": ["CS", fbits(rng), fbits(rng), werr]}
    if r < 0.7:
        return {"r": "meth"}
    return rng.choice([{"o": "O"}, {"f": fbits(rng)}, {"i": 7}, {"c": [fbits(rng), 0]}, {"fs": ["FS", fbits(rng), werr]},
                       {"is": ["IS", 4, werr]}, {"cs": ["CS", fbits(rng), 0, werr]}])


def user_obj(rng, werr):
    """An instance of a user class: its base, and which of __float__, __index__ and
    __complex__ it defines, with what they give."""
    j = {"u": rng.choice(["U", "V"]), "werr": werr}
    b = rng.random()
    if b < 0.15:
        j["b"] = {"f": fbits(rng)}
    elif b < 0.3:
        j["b"] = {"c": [fbits(rng), fbits(rng)]}
    elif b < 0.4:
        j["b"] = {"i": rng.choice([0, 3, 2 ** 64, 2 ** 1100])}
    for key, kind in (("fl", "f"), ("ix", "i"), ("cx", "c")):
        if rng.random() < 0.5:
            j[key] = gen_ret(rng, kind, werr)
    return j


def store_val(rng, tc):
    """A value to store, with more of what 3.15 changed: values `PyFloat_Pack2` refuses after
    `ins1` has grown the array, and `__index__` objects for `II_setitem`, `LL_setitem` and
    `QQ_setitem`, which now hold a reference to the object across the call."""
    if tc == "e" and rng.random() < 0.3:
        return {"f": half_edge(rng)}
    if tc in ("I", "L", "Q") and rng.random() < 0.2:
        lo, hi = INT_RANGE[tc]
        return {"o": "Idx", "i": rng.choice([lo, hi, lo - 1, hi + 1, 2 ** 64, -2 ** 64, 5])}
    if rng.random() < (0.35 if tc in ("e", "f", "d", "Zf", "Zd") else 0.08):
        return user_obj(rng, rng.random() < 0.3)
    if tc == "e" and rng.random() < 0.3:
        return {"f": half_round_edge(rng)}
    return any_val(rng, tc)


def gen_array_op(rng, a):
    tc = a.typecode
    n = len(a)
    op = rng.choice(["append", "insert", "pop", "index", "index", "count", "contains", "remove", "getitem",
                     "sqitem", "setitem", "delitem", "sqsetitem", "sqdelitem", "getslice", "setslice", "setslice",
                     "setslice_other", "setslice_self", "setslice_bad", "delslice", "delslice", "imul", "mul",
                     "add", "add_other", "add_bad", "iadd", "iadd_bad", "iadd_self", "extend", "extend_raise",
                     "extend_bad", "extend_arr", "extend_arr_other", "extend_self", "fromlist", "fromlist_bad",
                     "tolist", "frombytes", "frombytes_wide", "tobytes", "fromfile", "fromfile_notbytes",
                     "fromfile_raise", "tofile", "fromunicode", "tounicode", "byteswap", "reverse", "clear",
                     "copy", "buffer_info", "typecode", "itemsize", "len", "reduce_ex", "repr", "mv_open",
                     "mv_close", "cmp", "cmp_other", "cmp_bad", "it_new", "it_new", "it_next", "it_next", "it_reduce",
                     "it_setstate"])
    def good(k):
        return [good_val(rng, tc) for _ in range(k)]
    if op == "append":
        return [op, store_val(rng, tc)]
    if op in ("count", "contains", "remove", "index"):
        v = rng.choice([good_val(rng, tc), any_val(rng, tc), {"o": "Bomb"}])
        if n and rng.random() < 0.5:
            try:
                v = from_val(a[rng.randrange(n)])
            except ValueError:
                pass
        if op == "index":
            return [op, v] + [edge_index(rng, n) for _ in range(rng.choice([0, 1, 2]))]
        return [op, v]
    if op == "insert":
        return [op, edge_index(rng, n), store_val(rng, tc)]
    if op == "pop":
        return [op] if rng.random() < 0.3 else [op, edge_index(rng, n)]
    if op == "getitem" or op == "delitem":
        return [op, edge_index(rng, n)]
    if op in ("sqitem", "sqdelitem", "sqsetitem") and type(a) is not array:
        return None             # a subclass reaches __getitem__ through slot_sq_item
    if op in ("sqitem", "sqdelitem"):
        return [op, rng.randint(-n - 2, n + 2)]
    if op == "setitem":
        return [op, edge_index(rng, n), store_val(rng, tc)]
    if op == "sqsetitem":
        return [op, rng.randint(-n - 2, n + 2), store_val(rng, tc)]
    if op == "getslice" or op == "delslice" or op == "setslice_self" or op == "setslice_bad":
        return [op, rand_slice(rng, n)]
    if op in ("setslice", "setslice_other"):
        s = rand_slice(rng, n)
        L = slice_len(n, s)
        k = rng.choice([L, L, L, 0, L + 1, max(L - 1, 0), 2])
        if op == "setslice":
            return ["setslice", s, tc, good(k)]
        tc2 = rng.choice([t for t in "bBhHiIlLqQ" if t != tc])
        return ["setslice", s, tc2, [good_val(rng, tc2) for _ in range(k)]]
    if op in ("imul", "mul"):
        f = repeat_factor(rng, n, None, ITEMSIZE[tc], op == "imul")
        return None if f is None else [op, f]
    if op in ("add", "iadd", "extend_arr"):
        return [op, tc, good(rng.choice([0, 1, 2, 5]))]
    if op in ("add_other", "extend_arr_other"):
        tc2 = rng.choice([t for t in "bBhHiIlLqQ" if t != tc])
        return [op[:-6], tc2, [good_val(rng, tc2) for _ in range(rng.choice([0, 1, 2]))]]
    if op in ("add_bad", "iadd_bad", "iadd_self", "extend_bad", "extend_self", "fromlist_bad", "tolist",
              "tobytes", "tounicode", "byteswap", "reverse", "clear", "copy", "buffer_info",
              "typecode", "itemsize", "len", "repr", "mv_open", "mv_close", "it_new"):
        return [op]
    if op in ("extend", "extend_raise", "fromlist"):
        return [op, [rng.choice([good_val(rng, tc), good_val(rng, tc), any_val(rng, tc)])
                     for _ in range(rng.choice([0, 1, 2, 3, 5, 20]))]]
    if op in ("frombytes", "frombytes_wide"):
        k = rng.choice([0, 1, 2, 3, 4, 5, 7, 8, 16, 24]) * rng.choice([1, ITEMSIZE[tc]])
        return [op, [rng.choice([0, 1, 255, 0x80, rng.randrange(256)]) for _ in range(k)]]
    if op == "fromfile":
        k = rng.choice([0, 1, 2, 3, 8, 16])
        nbytes = k * rng.choice([1, ITEMSIZE[tc]]) + rng.choice([0, 0, 0, 1, ITEMSIZE[tc] - 1])
        cnt = rng.choice([0, 1, 2, 3, 8, -1, M, M + 1, M // ITEMSIZE[tc], M // ITEMSIZE[tc] + 1, k, k + 1,
                          {"o": "Idx", "i": rng.choice([1, 2, -1, 2 ** 64])}, {"o": "NoneType"}, {"f": fbits(rng)},
                          user_obj(rng, False)])
        if rng.random() < 0.4:
            return ["fromfile_mut", [rng.randrange(256) for _ in range(nbytes)], cnt, rng.randrange(4)]
        return [op, [rng.randrange(256) for _ in range(nbytes)], cnt]
    if op in ("fromfile_notbytes", "fromfile_raise"):
        return [op, rng.choice([0, 1, 2, -1, {"o": "NoneType"}])]
    if op == "tofile":
        return [op, rng.randrange(3), rng.randrange(2)]
    if op == "cmp_bad":
        return [op, rng.choice(list(OPS))]
    if op == "fromunicode":
        cs = [rng.choice([97, 98, 0xe9, 0xfeff, 0xd800, 0x10ffff, 0]) for _ in range(rng.choice([0, 1, 2, 3]))]
        if tc == "w" and not cs and a.buffer_info()[0] == 0:
            return None         # bugs/sequences-array-w-fromunicode-empty-systemerror.yaml: the
                                # exception escapes at a later, unrelated call
        return [op, cs]
    if op == "reduce_ex":
        return [op, rng.choice([0, 1, 2, 3, 4, 5, -1, 2 ** 63, {"s": [97]}])]
    if op in ("cmp", "cmp_other"):
        o = rng.choice(list(OPS))
        k = rng.choice([n, n, n, 0, 1, n + 1, max(n - 1, 0)])
        if op == "cmp_other":
            tc2 = rng.choice(TYPECODES)
            return ["cmp", o, tc2, [good_val(rng, tc2) for _ in range(k)]]
        try:
            vs = [from_val(v) for v in list(a)[:k]] + good(max(k - n, 0))
        except ValueError:
            vs = good(k)
        if vs and rng.random() < 0.5:
            vs[rng.randrange(len(vs))] = good_val(rng, tc)
        return ["cmp", o, tc, vs]
    if op == "it_next":
        return [op, rng.randrange(3)]
    if op == "it_reduce":
        return [op, rng.randrange(3)]
    if op == "it_setstate":
        return [op, rng.randrange(3), rng.choice([0, 1, -1, n, n + 1, 2 ** 63, -2 ** 64, rng.randint(-2, n + 2)])]
    raise AssertionError(op)


def make(c):
    kind = c["fn"]
    if kind == "list":
        return list(c["init"])
    if kind == "array":
        return (A if c["tname"] == "A" else array)(c["tc"], [to_val(v) for v in c["init"]])
    return (D if c["tname"] == "D" else deque)([to_el(e) for e in c["init"]], c["maxlen"])


def gen_array_new(rng):
    tc = rng.choice(list(TYPECODES) * 3 + ["x", "", "ab", 5, None, "Z", "ZZ", "Zdd", "dZ", "Zf ", "a\0", "\0",
                                           "Zf\0", "\udc80", "\udc80\0", "\u00e9", "\U00010000"])
    good = tc if tc in TYPECODES else "i"
    typecode = {"s": [ord(c) for c in tc]} if isinstance(tc, str) else ({"o": "NoneType"} if tc is None else tc)
    k = rng.choice(["none", "list", "list", "tuple", "bytes", "bytearray", "str", "iter", "iter_raise", "bad", "array"])
    n = rng.choice([0, 1, 2, 3, 8])
    init = {"kind": k}
    if k in ("list", "tuple", "iter", "iter_raise"):
        init["v"] = [rng.choice([good_val(rng, good), good_val(rng, good), any_val(rng, good)]) for _ in range(n)]
    elif k in ("bytes", "bytearray"):
        init["v"] = [rng.randrange(256) for _ in range(n * rng.choice([1, ITEMSIZE[good]]))]
    elif k == "str":
        init["v"] = [rng.choice([97, 0xe9, 0xfeff, 0xd800, 0x10ffff]) for _ in range(n)]
    elif k == "array":
        tc2 = rng.choice([good, good, rng.choice(TYPECODES)])
        init["tc"] = tc2
        init["v"] = [good_val(rng, tc2) for _ in range(n)]
    return {"mod": "sequences", "fn": "array_new", "typecode": typecode, "init": init,
            "tname": rng.choice(["array", "array", "A"])}


def gen_reconstruct(rng):
    mformat = rng.choice(list(range(28)) * 2 + [-1, 22, 28, 100])
    tc = rng.choice(list(TYPECODES) * 2 + ["x", "", "Z", "Zdd", "a\0", "\udc80", 5, None])
    size = {0: 1, 1: 1, 2: 2, 3: 2, 4: 2, 5: 2, 6: 4, 7: 4, 8: 4, 9: 4, 10: 8, 11: 8, 12: 8, 13: 8, 14: 4,
            15: 4, 16: 8, 17: 8, 18: 2, 19: 2, 20: 4, 21: 4, 22: 8, 23: 8, 24: 16, 25: 16, 26: 2, 27: 2}.get(mformat, 1)
    n = rng.choice([0, 1, 2, 3, 4, 5, 8])
    items = [rng.randrange(256) for _ in range(n * size + rng.choice([0, 0, 0, 1]))]
    if mformat in (14, 15, 16, 17, 22, 23, 24, 25, 26, 27) and rng.random() < 0.7:
        # NaNs, infinities and subnormals, in the byte order of the format, into an array
        # that can hold what the format decodes to
        if rng.random() < 0.8:
            tc = rng.choice(["e", "f", "d", "Zf", "Zd"])
        big = mformat % 2 == 1
        part = {14: 4, 15: 4, 16: 8, 17: 8, 22: 4, 23: 4, 24: 8, 25: 8, 26: 2, 27: 2}[mformat]
        out = []
        for _ in range(len(items) // part):
            pat = rng.choice({2: [0x7c00, 0xfc00, 0x7c01, 0x7dff, 0x7e00, 0x7fff, 0xfc01, 1, 0x3ff, 0x400],
                              4: [0x7f800000, 0xff800000, 0x7f800001, 0x7fbfffff, 0x7fc00000, 0x7fffffff,
                                  0xff800001, 1, 0x7fffff, 0x800000],
                              8: [0x7ff0000000000000, 0xfff0000000000000, 0x7ff0000000000001, 0x7ff7ffffffffffff,
                                  0x7ff8000000000000, 0xfff0000000000001, 1, 2 ** 52 - 1]}[part]
                             + [rng.getrandbits(8 * part)])
            out += pat.to_bytes(part, "big" if big else "little")
        items = out + items[len(out):]
    if mformat in (18, 19, 20, 21) and rng.random() < 0.8:
        s = "".join(rng.choice("abé€\U00010000\U0010ffff") for _ in range(n))
        enc = {18: "utf-16-le", 19: "utf-16-be", 20: "utf-32-le", 21: "utf-32-be"}[mformat]
        items = list(s.encode(enc))
        tc = rng.choice("uw" * 3 + "b")
    typecode = {"s": [ord(c) for c in tc]} if isinstance(tc, str) else ({"o": "NoneType"} if tc is None else tc)
    return {"mod": "sequences", "fn": "reconstruct", "typecode": typecode, "mformat": mformat, "items": items,
            "tname": rng.choice(["array", "A"])}


def gen_defdict(rng):
    def items():
        return [[rng.randint(0, 5), rng.randint(0, 9)] for _ in range(rng.choice([0, 1, 2, 3]))]
    ops = []
    for _ in range(rng.randint(1, 6)):
        op = rng.choice(["getitem", "getitem", "missing", "copy", "reduce", "repr", "repr_nested", "or_dict",
                         "ror_dict", "or_dd", "or_bad", "init", "init_toomany", "set", "or_frozen",
                         "ror_frozen"])
        if op in ("getitem", "missing"):
            ops.append([op, rng.choice([1, rng.randint(0, 7)])])
        elif op in ("copy", "reduce", "repr", "or_bad", "repr_nested"):
            ops.append([op])
        elif op in ("or_dict", "ror_dict", "or_frozen", "ror_frozen"):
            ops.append([op, items()])
        elif op == "or_dd":
            ops.append([op, items(), rng.choice(["null", "none", "F0"])])
        elif op == "init":
            f = rng.choice(["absent", "none", "F0", "F1", "bad"])
            ops.append([op, f, [] if f == "absent" else items()])
        elif op == "init_toomany":
            ops.append([op, rng.choice(["none", "F0"])])
        else:
            ops.append([op, rng.randint(0, 5), rng.randint(0, 9)])
    return {"mod": "sequences", "fn": "defdict", "init": items(),
            "factory": rng.choice(["null", "none", "F0", "F1", "F2", "F3"]),
            "tname": rng.choice(["defaultdict", "DD"]), "ops": ops}


def gen_count(rng):
    key = lambda: rng.choice([0, 1, 2, 3, "U"] if rng.random() < 0.3 else [0, 1, 2, 3])
    val = lambda: rng.choice([0, 1, 2, -1, "S"] if rng.random() < 0.3 else [0, 1, 2, -1])
    init = [[k, val()] for k in {rng.randint(0, 3) for _ in range(rng.randint(0, 3))}]
    return {"mod": "sequences", "fn": "count", "mapping": rng.choice(["dict", "slow"]), "init": init,
            "keys": [key() for _ in range(rng.choice([0, 1, 2, 3, 5, 8]))],
            "raises": rng.random() < 0.2, "bad": rng.random() < 0.05}


def gen_tuplegetter(rng):
    n = rng.randint(0, 4)
    return {"mod": "sequences", "fn": "tuplegetter", "index": edge_index(rng, n), "doc": rng.randint(0, 5),
            "tuple": [rng.randint(0, 5) for _ in range(n)]}


def gen_tofile(rng):
    tc = rng.choice(TYPECODES)
    blocks = rng.choice([1, 2, 3])
    nbytes = rng.choice([65536 * blocks, 65536 * blocks - ITEMSIZE[tc], 65536 * (blocks - 1) + ITEMSIZE[tc],
                         65536 * blocks + 7 * ITEMSIZE[tc]])
    return {"mod": "sequences", "fn": "array_tofile", "tc": tc, "n": max(nbytes // ITEMSIZE[tc], 1),
            "mode": rng.randrange(3), "k": rng.randrange(3)}


def run_tofile(c):
    a = array(c["tc"])
    n = c["n"] * a.itemsize
    a.frombytes(bytes((k * 7 + 3) % 256 for k in range(n)))
    f = BlockFile(a, c["mode"], c["k"])
    try:
        a.tofile(f)
        r = {"ok": None}
    except Exception as e:
        r = {"exc": type(e).__name__, "msg": str(e)}
    return {"ok": [r, f.chunks, len(a)]}


def gen_case(rng):
    kind = rng.choice(["list", "array", "array", "array", "deque", "deque", "deque", "array_new", "reconstruct",
                       "defdict", "count", "tuplegetter"] + (["array_tofile"] if rng.random() < 0.03 else []))
    if kind == "array_tofile":
        return gen_tofile(rng)
    if kind == "array_new":
        return gen_array_new(rng)
    if kind == "reconstruct":
        return gen_reconstruct(rng)
    if kind == "defdict":
        return gen_defdict(rng)
    if kind == "count":
        return gen_count(rng)
    if kind == "tuplegetter":
        return gen_tuplegetter(rng)
    n = rand_len(rng, kind)
    c = {"mod": "sequences", "fn": kind}
    if kind == "array":
        tc = rng.choice(TYPECODES)
        c["tc"] = tc
        c["tname"] = rng.choice(["array", "array", "A"])
        init = [good_val(rng, tc) for _ in range(n)]
        if rng.random() < 0.03:
            init.append(any_val(rng, tc))
    elif kind == "deque":
        c["tname"] = rng.choice(["deque", "deque", "deque", "D"])
        c["maxlen"] = rng.choice([None, None, None, 0, 1, 2, 3, 5, 64, 65, n, n + 1, n + 3, 2 ** 31,
                                  2 ** 31 + 5, 2 ** 32, 2 ** 32 + 2, 2 ** 33, 2 ** 40])
        init = de_items(rng, n)
    else:
        init = [rng.randint(0, 5) for _ in range(n)]
    c["init"] = init
    try:
        obj = make(c)
    except Exception:
        c["ops"] = []
        return c
    TARGET[0] = obj
    extra = {"its": [], "views": []}
    ops = []
    gen = {"list": gen_list_op, "array": gen_array_op, "deque": gen_deque_op}[kind]
    for _ in range(rng.randint(1, 10)):
        op = gen(rng, obj)
        if op is None:
            continue
        if op[0] == "mv_close" and not extra["views"]:
            continue
        if op[0].startswith("it_") and op[0] not in ("it_new", "it_make") and op[1] >= len(extra["its"]):
            continue
        ops.append(op)
        if werr_in(op):
            with warnings.catch_warnings():
                warnings.simplefilter("error", DeprecationWarning)
                py_res(lambda: run_op(obj, op, kind, c, extra))
        else:
            py_res(lambda: run_op(obj, op, kind, c, extra))
        if len(obj) > 3000:
            break
    for v in extra["views"]:
        v.release()
    c["ops"] = ops
    return c


def py_res(thunk):
    try:
        v = thunk()
        return {"ok": v}
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}


def deque_j(d):
    return [[from_el(e) for e in d], d.maxlen, blocks(d)]


def arr_j(a):
    base = type(a)(a.typecode).__sizeof__()
    return [list(a.tobytes()), (a.__sizeof__() - base) // a.itemsize, a.buffer_info()[0] != 0]


def arr_repr(a):
    r = repr(a)
    name, tc = type(a).__name__, a.typecode
    if len(a) == 0:
        return r
    if tc in "uw":
        s = a.tounicode()
        assert r == f"{name}('{tc}', {s!r})"
        return f"{name}('{tc}', <str {[ord(c) for c in s]}>)"
    if tc in ("e", "f", "d"):
        xs = list(a)
        assert r == f"{name}('{tc}', {xs!r})"
        body = ", ".join("<float %d>" % from_val(x)["f"] for x in xs)
        return f"{name}('{tc}', [{body}])"
    if tc in ("Zf", "Zd"):
        xs = list(a)
        assert r == f"{name}('{tc}', {xs!r})"
        body = ", ".join("<complex <float %d> <float %d>>" % tuple(from_val(x)["c"]) for x in xs)
        return f"{name}('{tc}', [{body}])"
    return r


class RaisingIter:
    """An iterator yielding xs, then raising exc (StopIteration or another)."""

    def __init__(self, xs, exc):
        self.it = iter(xs)
        self.exc = exc

    def __iter__(self):
        return self

    def __next__(self):
        for x in self.it:
            return x
        raise self.exc


class NotBytesFile:
    def read(self, n):
        return "x"


class RaisingFile:
    def read(self, n):
        raise ValueError("read")


class ChunkFile:
    """A scripted `write`: mode 1 raises at call k, mode 2 appends a zero item each call."""

    def __init__(self, a, mode, k):
        self.a, self.mode, self.k = a, mode, k
        self.chunks = []

    def write(self, b):
        self.chunks.append(list(b))
        if self.mode == 1 and len(self.chunks) - 1 == self.k:
            raise ValueError("write")
        if self.mode == 2:
            self.a.frombytes(bytes(self.a.itemsize))


class BlockFile(ChunkFile):
    def write(self, b):
        n = len(self.chunks)
        self.chunks.append([len(b), sum(x * (i + 1) for i, x in enumerate(b)) % 1000000007])
        if self.mode == 1 and n == self.k:
            raise ValueError("write")
        if self.mode == 2:
            self.a.frombytes(bytes(self.a.itemsize))


class MutFile:
    """A scripted `read`: before returning data[:n], k = 1 appends a zero item, k = 2 clears
    the array, k = 3 opens a memoryview of it that stays open."""

    def __init__(self, a, data, k, extra):
        self.a, self.f, self.k, self.extra = a, io.BytesIO(data), k, extra

    def read(self, n):
        if self.k == 1:
            self.a.frombytes(bytes(self.a.itemsize))
        elif self.k == 2:
            self.a.clear()
        elif self.k == 3:
            self.extra["views"].append(memoryview(self.a))
        return self.f.read(n)


def run_deque_op(d, op, extra):
    name, args = op[0], op[1:]
    its = extra["its"]
    if name in ("append", "appendleft"):
        return getattr(d, name)(to_el(args[0]))
    if name in ("pop", "popleft"):
        return from_el(getattr(d, name)())
    if name in ("extend", "extendleft"):
        return getattr(d, name)([to_el(e) for e in args[0]])
    if name == "iadd":
        d.__iadd__([to_el(e) for e in args[0]])
        return None
    if name in ("extend_raise", "extendleft_raise"):
        return getattr(d, name[:-6])(RaisingIter([to_el(e) for e in args[0]], ValueError("iter")))
    if name == "extend_stop":
        return d.extend(RaisingIter([to_el(e) for e in args[0]], StopIteration()))
    if name in ("extend_bad", "extendleft_bad"):
        return getattr(d, name[:-4])(5)
    if name == "iadd_bad":
        d.__iadd__(5)
        return None
    if name in ("extend_self", "extendleft_self"):
        return getattr(d, name[:-5])(d)
    if name == "iadd_self":
        d.__iadd__(d)
        return None
    if name == "rotate":
        return d.rotate(*args)
    if name == "index":
        return d.index(to_el(args[0]), *args[1:])
    if name == "insert":
        return d.insert(args[0], to_el(args[1]))
    if name in ("remove", "count"):
        return getattr(d, name)(to_el(args[0]))
    if name == "contains":
        return to_el(args[0]) in d
    if name == "reverse":
        return d.reverse()
    if name == "getitem":
        return from_el(d[args[0]])
    if name == "setitem":
        d[args[0]] = to_el(args[1])
        return None
    if name == "delitem":
        del d[args[0]]
        return None
    if name == "copy":
        return deque_j(d.copy())
    if name == "imul":
        d.__imul__(args[0])
        return None
    if name == "mul":
        return deque_j(d * args[0])
    if name == "add":
        return deque_j(d + deque([to_el(e) for e in args[0]], args[1]))
    if name == "add_self":
        return deque_j(d + d)
    if name == "add_bad":
        return deque_j(d + [1])
    if name == "clear":
        return d.clear()
    if name == "init":
        d.__init__([to_el(e) for e in args[0]], *args[1:])
        return None
    if name == "init_self":
        d.__init__(d, *args)
        return None
    if name == "len":
        return len(d)
    if name == "maxlen":
        return d.maxlen
    if name == "repr":
        return repr(d)
    if name == "repr_nested":
        c = d.copy()
        c.append(c)
        return repr(c)
    if name == "reduce":
        r = d.__reduce__()
        return [r[1][1] if r[1] else None, [from_el(e) for e in r[3]]]
    if name == "cmp":
        return OPS[args[0]](d, deque([to_el(e) for e in args[1]]))
    if name == "cmp_self":
        return OPS[args[0]](d, d)
    if name == "it_new":
        its.append(reversed(d) if args[0] else iter(d))
        return None
    if name == "it_make":
        its.append((type(reversed(deque())) if args[0] else type(iter(deque())))(d, args[1]))
        return None
    if name == "it_next":
        x = next(its[args[0]], its)
        return "STOP" if x is its else from_el(x)
    if name == "it_len":
        return its[args[0]].__length_hint__()
    if name == "it_reduce":
        return its[args[0]].__reduce__()[1][1]
    raise AssertionError(name)


E_PACK_ERROR = "float too large to pack with e format"


def scrub_slot(a, exc, last):
    """After `ins1` failed in `e_setitem`, the new last slot is uninitialised memory when
    `last` says it was the insertion point: store the model's value there."""
    if a.typecode == "e" and last and str(exc) == E_PACK_ERROR:
        a[len(a) - 1] = 0.0


def ins_at_end(a, i):
    """Whether `ins1(a, i, v)` writes the slot past the old end."""
    n = len(a)
    return i >= n or (n == 0 and i < 0)


def run_array_op(a, op, c, extra):
    name, args = op[0], op[1:]
    its = extra["its"]
    if name == "append":
        try:
            return a.append(to_val(args[0]))
        except OverflowError as e:
            scrub_slot(a, e, True)
            raise
    if name == "insert":
        end = ins_at_end(a, args[0])
        try:
            return a.insert(args[0], to_val(args[1]))
        except OverflowError as e:
            scrub_slot(a, e, end)
            raise
    if name == "pop":
        return from_val(a.pop(*args))
    if name == "index":
        return a.index(to_val(args[0]), *args[1:])
    if name == "count":
        return a.count(to_val(args[0]))
    if name == "contains":
        return to_val(args[0]) in a
    if name == "remove":
        return a.remove(to_val(args[0]))
    if name == "getitem":
        return from_val(a[args[0]])
    if name == "sqitem":
        return from_val(sq_get(a, args[0]))
    if name == "setitem":
        a[args[0]] = to_val(args[1])
        return None
    if name == "delitem":
        del a[args[0]]
        return None
    if name == "sqsetitem":
        sq_set(a, args[0], to_val(args[1]))
        return None
    if name == "sqdelitem":
        sq_del(a, args[0])
        return None
    if name == "getslice":
        return arr_j(a[slice(*args[0])])
    if name == "setslice":
        a[slice(*args[0])] = array(args[1], [to_val(v) for v in args[2]])
        return None
    if name == "setslice_self":
        a[slice(*args[0])] = a
        return None
    if name == "setslice_bad":
        a[slice(*args[0])] = [1]
        return None
    if name == "delslice":
        del a[slice(*args[0])]
        return None
    if name == "imul":
        a.__imul__(args[0])
        return None
    if name == "mul":
        return arr_j(a * args[0])
    if name == "add":
        return arr_j(a + array(args[0], [to_val(v) for v in args[1]]))
    if name == "add_bad":
        return arr_j(a + [1])
    if name == "iadd":
        a.__iadd__(array(args[0], [to_val(v) for v in args[1]]))
        return None
    if name == "iadd_bad":
        a.__iadd__([1])
        return None
    if name == "iadd_self":
        a.__iadd__(a)
        return None
    if name == "extend":
        try:
            return a.extend([to_val(v) for v in args[0]])
        except OverflowError as e:
            scrub_slot(a, e, True)
            raise
    if name == "extend_raise":
        try:
            return a.extend(RaisingIter([to_val(v) for v in args[0]], ValueError("iter")))
        except OverflowError as e:
            scrub_slot(a, e, True)
            raise
    if name == "extend_bad":
        return a.extend(5)
    if name == "extend_arr":
        return a.extend(array(args[0], [to_val(v) for v in args[1]]))
    if name == "extend_self":
        return a.extend(a)
    if name == "fromlist":
        return a.fromlist([to_val(v) for v in args[0]])
    if name == "fromlist_bad":
        return a.fromlist(())
    if name == "tolist":
        return [from_val(v) for v in a.tolist()]
    if name == "frombytes":
        return a.frombytes(bytes(args[0]))
    if name == "frombytes_wide":
        return a.frombytes(memoryview(array("h", [0])).cast("B").cast("h") if False else _wide(args[0]))
    if name == "tobytes":
        return list(a.tobytes())
    if name == "fromfile":
        return a.fromfile(io.BytesIO(bytes(args[0])), to_val(args[1]))
    if name == "fromfile_mut":
        return a.fromfile(MutFile(a, bytes(args[0]), args[2], extra), to_val(args[1]))
    if name == "fromfile_notbytes":
        return a.fromfile(NotBytesFile(), to_val(args[0]))
    if name == "fromfile_raise":
        return a.fromfile(RaisingFile(), to_val(args[0]))
    if name == "tofile":
        f = ChunkFile(a, args[0], args[1])
        try:
            a.tofile(f)
            return [{"ok": None}, f.chunks]
        except Exception as e:
            return [{"exc": type(e).__name__, "msg": str(e)}, f.chunks]
    if name == "cmp_bad":
        r = getattr(a, "__%s__" % args[0])([1])
        return "NotImplemented" if r is NotImplemented else r
    if name == "fromunicode":
        return a.fromunicode("".join(map(chr, args[0])))
    if name == "tounicode":
        return [ord(c) for c in a.tounicode()]
    if name == "byteswap":
        return a.byteswap()
    if name == "reverse":
        return a.reverse()
    if name == "clear":
        return a.clear()
    if name == "copy":
        return arr_j(a.__copy__())
    if name == "buffer_info":
        addr, k = a.buffer_info()
        return [addr != 0, k]
    if name == "typecode":
        return a.typecode
    if name == "itemsize":
        return a.itemsize
    if name == "len":
        return len(a)
    if name == "reduce_ex":
        r = a.__reduce_ex__(to_val(args[0]))
        if r[0] is type(a):
            return [r[0].__name__, r[1][0], [from_val(v) for v in r[1][1]]]
        return [r[1][0].__name__, r[1][1], r[1][2], list(r[1][3])]
    if name == "repr":
        return repr(a)
    if name == "mv_open":
        m = memoryview(a)
        extra["views"].append(m)
        return [m.format, m.itemsize, m.shape[0], m.nbytes]
    if name == "mv_close":
        extra["views"].pop().release()
        return None
    if name == "cmp":
        return OPS[args[0]](a, array(args[1], [to_val(v) for v in args[2]]))
    if name == "it_new":
        its.append(iter(a))
        return None
    if name == "it_next":
        x = next(its[args[0]], its)
        return "STOP" if x is its else from_val(x)
    if name == "it_reduce":
        r = its[args[0]].__reduce__()
        return r[2] if len(r) == 3 else None
    if name == "it_setstate":
        return its[args[0]].__setstate__(args[1])
    raise AssertionError(name)


def _wide(bs):
    """A buffer with itemsize 2, holding len(bs) // 2 items."""
    k = len(bs) // 2 * 2
    return memoryview(bytes(bs[:k])).cast("H")


def run_list_op(l, op):
    name, args = op[0], op[1:]
    if name == "append":
        return l.append(args[0])
    if name in ("insert", "index", "count", "remove"):
        return getattr(l, name)(*args)
    if name == "pop":
        return l.pop(*args)
    if name == "getitem":
        return l[args[0]]
    if name == "setitem":
        l[args[0]] = args[1]
        return None
    if name == "delitem":
        del l[args[0]]
        return None
    if name == "setslice":
        l[slice(*args[0])] = args[1]
        return None
    if name == "setslice_self":
        l[slice(*args[0])] = l
        return None
    if name == "delslice":
        del l[slice(*args[0])]
        return None
    if name == "imul":
        l.__imul__(args[0])
        return None
    if name == "mul":
        return l * args[0]
    if name == "init":
        return l.__init__(*args)
    if name == "init_self":
        return l.__init__(l)
    if name == "extend":
        return l.extend(args[0])
    raise AssertionError(name)


def run_op(obj, op, kind, c, extra):
    if kind == "list":
        return run_list_op(obj, op)
    if kind == "deque":
        return run_deque_op(obj, op, extra)
    return run_array_op(obj, op, c, extra)


class Fac:
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return self.name

    def __call__(self):
        d = FACT_TARGET[0]
        if self.name == "F1":
            raise ValueError("fac")
        if self.name == "F2":
            d[100] = 7
            return 1
        if self.name == "F3":
            d[1] = 5
            return 1
        return 0


FACT_TARGET = [None]


class NestRepr:
    def __repr__(self):
        return repr(FACT_TARGET[0])

    def __call__(self):
        return 0


def fac_of(name):
    return {"null": None, "none": None}.get(name, Fac(name)) if name in ("null", "none") else Fac(name)


def dd_j(x):
    return [type(x).__name__, [list(kv) for kv in x.items()], repr(x)]


def run_defdict(c):
    cls = DD if c["tname"] == "DD" else defaultdict
    if c["factory"] == "null":
        dd = cls()
    else:
        dd = cls(fac_of(c["factory"]))
    dd.update(dict(c["init"]))
    FACT_TARGET[0] = dd
    out = []
    for op in c["ops"]:
        r = py_res(lambda: run_dd_op(dd, op))
        out.append([r, [[list(kv) for kv in dd.items()]]])
    return {"ok": out}


def run_dd_op(dd, op):
    name, args = op[0], op[1:]
    if name == "getitem":
        return dd[args[0]]
    if name == "missing":
        return dd.__missing__(args[0])
    if name == "copy":
        return dd_j(dd.copy())
    if name == "reduce":
        r = dd.__reduce__()
        return [repr(r[1][0]) if r[1] else None, [list(kv) for kv in r[4]]]
    if name == "repr":
        return repr(dd)
    if name == "repr_nested":
        f = dd.default_factory
        dd.default_factory = NestRepr()
        try:
            return repr(dd)
        finally:
            dd.default_factory = f
    if name == "or_dict":
        return dd_j(dd | dict(args[0]))
    if name == "ror_dict":
        return dd_j(dict(args[0]) | dd)
    if name == "or_dd":
        o = defaultdict() if args[1] == "null" else defaultdict(fac_of(args[1]))
        o.update(dict(args[0]))
        return dd_j(dd | o)
    if name == "or_frozen":
        return dd_j(dd | frozendict(args[0]))
    if name == "ror_frozen":
        # `frozendict | dd` is frozendict_or's: this slot is reached only by name
        return dd_j(dd.__ror__(frozendict(args[0])))
    if name == "or_bad":
        return "NI" if dd.__or__(5) is NotImplemented else None
    if name == "init":
        if args[0] == "absent":
            return dd.__init__()
        if args[0] == "bad":
            return dd.__init__(5, dict(args[1]))
        return dd.__init__(fac_of(args[0]), dict(args[1]))
    if name == "init_toomany":
        return dd.__init__(fac_of(args[0]), {}, {})
    if name == "set":
        dd[args[0]] = args[1]
        return None
    raise AssertionError(name)


class SlowDict(dict):
    def __setitem__(self, k, v):
        dict.__setitem__(self, k, v)


def run_count(c):
    k_ = lambda k: [] if k == "U" else k
    v_ = lambda v: "x" if v == "S" else v
    m = (dict if c["mapping"] == "dict" else SlowDict)((k, v_(v)) for k, v in c["init"])
    keys = [k_(k) for k in c["keys"]]
    src = 5 if c["bad"] else (RaisingIter(keys, ValueError("iter")) if c["raises"] else keys)
    r = py_res(lambda: collections._count_elements(m, src))
    items = [[k, "S" if v == "x" else v] for k, v in m.items()]
    return {"ok": [r, items]}


def run_tuplegetter(c):
    try:
        g = collections._tuplegetter(c["index"], c["doc"])
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}
    t = tuple(c["tuple"])

    def get(obj, cls):
        r = g.__get__(obj, cls)
        return "SELF" if r is g else r

    def set_():
        g.__set__(t, 1)

    def del_():
        g.__delete__(t)
    return {"ok": [py_res(lambda: get(t, tuple)), py_res(lambda: get(None, tuple)), py_res(lambda: get(None, tuple)),
                   py_res(lambda: get(5, int)), py_res(set_), py_res(del_), list(g.__reduce__()[1]), repr(g)]}


def run_array_new(c):
    cls = A if c["tname"] == "A" else array
    i = c["init"]
    k = i["kind"]
    tc = to_val(c["typecode"])
    if k == "none":
        return py_res(lambda: arr_j(cls(tc)))
    if k == "array":
        initial = array(i["tc"], [to_val(v) for v in i["v"]])
    elif k == "bad":
        initial = 5
    else:
        v = [to_val(x) for x in i["v"]] if k in ("list", "tuple", "iter", "iter_raise") else i["v"]
        initial = {"list": lambda: v, "tuple": lambda: tuple(v), "bytes": lambda: bytes(v),
                   "bytearray": lambda: bytearray(v), "str": lambda: "".join(map(chr, v)),
                   "iter": lambda: iter(v), "iter_raise": lambda: RaisingIter(v, ValueError("iter"))}[k]()
    return py_res(lambda: arr_j(cls(tc, initial)))


def run_reconstruct(c):
    cls = A if c["tname"] == "A" else array

    def go():
        a = array_mod._array_reconstructor(cls, to_val(c["typecode"]), c["mformat"], bytes(c["items"]))
        return [a.typecode, list(a.tobytes())]
    return py_res(go)


def run_python(c):
    kind = c["fn"]
    if kind == "defdict":
        return run_defdict(c)
    if kind == "count":
        return run_count(c)
    if kind == "tuplegetter":
        return run_tuplegetter(c)
    if kind == "array_new":
        return run_array_new(c)
    if kind == "reconstruct":
        return run_reconstruct(c)
    if kind == "array_tofile":
        return run_tofile(c)
    try:
        obj = make(c)
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}
    TARGET[0] = obj
    extra = {"its": [], "views": []}
    out = []
    for op in c["ops"]:
        if werr_in(op):
            with warnings.catch_warnings():
                warnings.simplefilter("error", DeprecationWarning)
                r = py_res(lambda: run_op(obj, op, kind, c, extra))
        else:
            r = py_res(lambda: run_op(obj, op, kind, c, extra))
        if kind == "deque":
            st = [[from_el(e) for e in obj], blocks(obj)]
        elif kind == "array":
            st = arr_j(obj)
        else:
            st = list(obj)
        out.append([r, st])
    for v in extra["views"]:
        v.release()
    return {"ok": out}


def agree(py, lean):
    """Equality, except that an exception whose model message starts with `~`
    compares by class only, at any depth."""
    if isinstance(py, dict) and isinstance(lean, dict):
        if "exc" in py and "exc" in lean:
            return py["exc"] == lean["exc"] and (lean["msg"].startswith("~") or py["msg"] == lean["msg"])
        return py.keys() == lean.keys() and all(agree(py[k], lean[k]) for k in py)
    if isinstance(py, (list, tuple)) and isinstance(lean, (list, tuple)):
        return len(py) == len(lean) and all(agree(a, b) for a, b in zip(py, lean))
    return py == lean


if __name__ == "__main__":
    common.agree = agree
    common.main(gen_case, run_python)
