"""Differential test: Lean model of dict, set, frozenset, OrderedDict vs. the running CPython.

Usage: python3 difftest/dictset_diff.py [--cases N] [--seed S]

A case is a scenario: a pool of objects (ints, floats, strs, str subclasses, objects with a
chosen hash, objects whose __eq__ raises or mutates the container, unhashable objects) and a
list of operations on three dict slots, three set slots and four iterator slots. After every
operation the test compares the result and, for every container, the exact element order and
__sizeof__, which pins down table size, entry kind (unicode or general), and for sets the slot
of every element. Each object carries its hash and equality class, computed here, so the model
needs no model of str or float hashing.

Slots 0 and 1 keep their object; slot 2 receives results, so iterators stay valid.
"""

import importlib.util
import itertools
import contextlib
import ctypes
import json
import os
import resource
import sys
from collections import OrderedDict

import _testcapi as tc
import _testlimitedcapi as tl

import common


def kwf(**kw):
    """`f(**a, **b)` is DICT_MERGE, which is `_PyDict_MergeUniq`: override 2 with a dupkey."""
    return kw


class Refuses:
    def __get__(self, obj, tp=None):
        raise ValueError("look")


def with_missing(base, how, v):
    """A subclass of `base`, by what looking up and calling `__missing__` does."""
    if how == 0:
        return type("M", (base,), {})

    def missing(self, k):
        if how == 2:
            raise ValueError("miss")
        return v
    return type("M", (base,), {"__missing__": Refuses() if how == 3 else missing})


class S(str):
    """Not PyUnicode_CheckExact: forces the generic paths of the lookup."""


class K:
    __slots__ = ("c", "h", "u")

    def __init__(self, c, h, u):
        self.c, self.h, self.u = c, h, u

    def __hash__(self):
        return self.h

    def __eq__(self, o):
        if isinstance(o, (KRaise, KEvil)):
            return NotImplemented
        return type(o) is K and o.c == self.c

    def __repr__(self):
        return f"K({self.u})"


class KRaise(K):
    __slots__ = ()
    __hash__ = K.__hash__

    def __eq__(self, o):
        raise ValueError("eq")


TARGET = [None]
POOL = [None]


def evil_act(t, n):
    """1 clears, 2 pops an item, 10 + i pops an item and stores its value under pool object i,
    which keeps the number of items, so `orig_size` in dict_dict_merge cannot see it."""
    if n == 0:
        return
    if n == 1:
        t.clear()
    elif n == 2:
        try:
            t.popitem() if isinstance(t, dict) else t.pop()
        except KeyError:
            pass
    else:
        try:
            v = t.popitem()[1]
        except KeyError:
            return
        t[POOL[0][n - 10]] = v


class KEvil(K):
    __slots__ = ("act", "rs")
    __hash__ = K.__hash__

    def __init__(self, c, h, u, act, rs=False):
        super().__init__(c, h, u)
        self.act = act
        self.rs = rs

    def __eq__(self, o):
        evil_act(TARGET[0], self.act)
        if self.rs:
            raise ValueError("eq")
        return False


class HRaise:
    __slots__ = ("u",)

    def __init__(self, u):
        self.u = u

    def __hash__(self):
        raise ValueError("hash")

    def __repr__(self):
        return f"H({self.u})"


class Mapping:
    def __init__(self, ks, pairs):
        self.ks, self.pairs = ks, pairs

    def keys(self):
        return list(self.ks)

    def __getitem__(self, k):
        for a, b in self.pairs:
            if a is k:
                return b
        raise KeyError(k)


class HookMapping(Mapping):
    """`__getitem__` of `hook` does `act` to the receiver; `keys()` may raise."""

    def __init__(self, ks, pairs, hook, act, recv, kr):
        super().__init__(ks, pairs)
        self.hook, self.act, self.recv, self.kr = hook, act, recv, kr

    def keys(self):
        if self.kr:
            raise ValueError("keys")
        return super().keys()

    def __getitem__(self, k):
        if k is self.hook:
            evil_act(self.recv, self.act)
        return super().__getitem__(k)


class AttrRaises:
    """`hasattr(self, 'keys')` raises something other than AttributeError."""

    def __getattr__(self, name):
        raise ValueError("hasattr")


class DictSub(dict):
    """Keeps dict's tp_iter, so dict_merge takes the fast path."""


class ItemsOnly:
    """No keys(): `items` matters to odict's C update, iteration to the pure-Python one."""

    def __init__(self, its, it):
        self.its, self.it = its, it

    def items(self):
        return list(self.its)

    def __iter__(self):
        return iter(self.it)


def load_py_ordereddict():
    """The pure-Python OrderedDict, with `_collections` hidden from the module."""
    import collections
    saved = sys.modules.get("_collections")
    sys.modules["_collections"] = None
    try:
        spec = importlib.util.spec_from_file_location(
            "py_collections", collections.__file__,
            submodule_search_locations=collections.__path__)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
    finally:
        sys.modules["_collections"] = saved
    return mod.OrderedDict


PyOrderedDict = load_py_ordereddict()
assert PyOrderedDict is not OrderedDict and "popitem" in PyOrderedDict.__dict__


# hash(nan) depends on the object's address, so a scenario must not rebuild them.
NANS = [float("nan"), float("nan")]


def build(spec):
    kind, p = spec["py"]
    u = spec["u"]
    if kind == "int":
        return p
    if kind == "bool":
        return bool(p)
    if kind == "float":
        return float(p)
    if kind == "nan":
        return NANS[p]
    if kind == "str":
        # setattr() interns the name, and the key in __dict__ must be the pool object.
        return sys.intern(p)
    if kind == "strsub":
        return S(p)
    if kind == "K":
        return K(p[0], p[1], u)
    if kind == "Kr":
        return KRaise(p[0], p[1], u)
    if kind == "Kev":
        return KEvil(p[0], p[1], u, p[2], len(p) > 3 and p[3])
    if kind == "list":
        return [u]
    if kind == "hraise":
        return HRaise(u)
    if kind == "fz":
        return frozenset(p)
    if kind == "st":
        return set(p)
    raise ValueError(kind)


class Pool:
    def __init__(self):
        self.specs = []
        self.cls = {}

    def _cls(self, key):
        return self.cls.setdefault(key, len(self.cls))

    def add(self, kind, p, ckey=None, hk=0, r=False, a=0, fs=None):
        u = len(self.specs)
        ckey = ckey if ckey is not None else ("u", u)
        spec = {"py": [kind, p], "u": u, "c": self._cls(ckey), "hk": hk, "r": r, "a": a, "fs": fs}
        o = build(spec)
        try:
            spec["h"] = hash(o)
        except TypeError:
            spec["h"] = 0
            spec["hk"] = 1
        except ValueError:
            spec["h"] = 0
            spec["hk"] = 2
        spec["s"] = type(o) is str
        spec["sl"] = isinstance(o, str)
        spec["rep"] = repr(o)
        spec["t"] = type(o).__name__
        spec["nan"] = kind == "nan"
        self.specs.append(spec)
        return u


def edge_hashes(rng):
    return rng.choice([0, 1, 2, 8, 16, 32, -1, -2, 2 ** 61 - 1, 2 ** 61, 2 ** 63 - 1, -2 ** 63,
                       rng.randint(0, 7), rng.randint(0, 7) * 8, rng.randint(0, 7) << 32,
                       rng.getrandbits(62)])


def int_pool(pool, rng, n, spread):
    seen = set()
    while len(seen) < n:
        v = rng.choice([rng.randint(0, spread), rng.randint(-spread, spread),
                        rng.randint(0, spread) * 8, rng.randint(0, 40) << rng.randint(0, 40),
                        2 ** rng.randint(0, 80), -1, -2, 2 ** 61 - 1, 2 ** 61, 2 ** 63, -2 ** 63,
                        sys.maxsize])
        if v not in seen:
            seen.add(v)
            pool.add("int", v, ("num", v))


def str_pool(pool, rng, n):
    for i in range(n):
        pool.add("str", "s" + str(i), ("str", i))


def mixed_pool(pool, rng):
    int_pool(pool, rng, rng.randint(2, 8), 16)
    str_pool(pool, rng, rng.randint(2, 5))
    if rng.random() < 0.5:
        pool.add("strsub", "s0", ("str", 0))
    if rng.random() < 0.5:
        pool.add("float", 1.0, ("num", 1))
        pool.add("bool", 1, ("num", 1))
    if rng.random() < 0.5:
        pool.add("nan", 0)
        pool.add("nan", 1)
    h = edge_hashes(rng)
    for i in range(rng.randint(0, 5)):
        pool.add("K", [i % 3, h], ("K", i % 3, h))
    if rng.random() < 0.3:
        pool.add("list", 0)
    if rng.random() < 0.2:
        pool.add("hraise", 0)
    if rng.random() < 0.2:
        pool.add("Kr", [99, h], r=True)
    if rng.random() < 0.2:
        pool.add("fz", [1, 2], ("fs", 12))
        pool.add("st", [1, 2], ("fs", 12), fs=hash(frozenset([1, 2])))


def dict_op(rng, n):
    k = lambda: rng.randrange(n)
    d = rng.choice([0, 0, 0, 1])
    o = rng.random()
    if o < 0.30:
        return ["set", d, k(), k()]
    if o < 0.40:
        return ["del", d, k()]
    if o < 0.47:
        return [rng.choice(["get", "in"]), d, k()]
    if o < 0.52:
        return ["getd", d, k(), k()]
    if o < 0.58:
        return ["sdef", d, k(), k()]
    if o < 0.62:
        return ["pop", d, k()]
    if o < 0.65:
        return ["popd", d, k(), k()]
    if o < 0.71:
        return ["popitem", d]
    if o < 0.73:
        return ["clear", d]
    if o < 0.76:
        return [rng.choice(["len", "keys", "values", "items", "repr"]), d]
    return None


def upd_arg(rng, n, hooks=True):
    """`hooks`: the callbacks may act on the receiver, which `dict(arg)` does not expose."""
    k = lambda: rng.randrange(n)
    o = rng.random()
    if o < 0.35:
        return ["d", rng.randrange(3)]
    if o < 0.45:
        return ["sub", rng.randrange(2)]
    if o < 0.75:
        items = []
        for _ in range(rng.randint(0, 6)):
            r = rng.random()
            if r < 0.9:
                items.append(["p", k(), k()])
            elif r < 0.95:
                items.append(["b"])
            else:
                items.append(["l", rng.choice([0, 1, 3])])
        return ["p", items, rng.random() < 0.1]
    if o < 0.95:
        ks = [k() for _ in range(rng.randint(0, 6))]
        pairs = [[x, k()] for x in ks if rng.random() < 0.9]
        if rng.random() < 0.3 and ks:
            act = rng.choice([0, 1, 2]) if hooks else 0
            return ["mr", ks, pairs, rng.choice(ks), act, rng.random() < 0.15]
        return ["m", ks, pairs]
    if o < 0.97:
        items = [["p", k(), k()] for _ in range(rng.randint(0, 6))]
        return ["pr", items, rng.randint(0, 6), rng.choice([1, 2]) if hooks else 0, rng.random() < 0.2]
    if o < 0.98:
        return ["hr"]
    return ["n"]


def dict_op2(rng, n, specs):
    k = lambda: rng.randrange(n)
    d = rng.choice([0, 0, 1])
    o = rng.random()
    if o < 0.30:
        strs = [s["u"] for s in specs if s["s"]]
        kw = []
        if strs and rng.random() < 0.3:
            ks = rng.sample(strs, min(len(strs), rng.randint(1, 3)))
            kw = [[x, k()] for x in ks]
        return ["upd", d, upd_arg(rng, n), kw]
    if o < 0.40:
        return ["ior", d, upd_arg(rng, n)]
    if o < 0.50:
        return ["or", d, rng.randrange(3)]
    if o < 0.65:
        return ["copy", rng.randrange(3)]
    if o < 0.75:
        return ["eq", d, rng.randrange(3), rng.random() < 0.3]
    if o < 0.85:
        src = rng.choice([["d", rng.randrange(3)], ["s", rng.randrange(3)],
                          ["l", [k() for _ in range(rng.randint(0, 7))]],
                          ["g", [k() for _ in range(rng.randint(0, 3))]], ["n"]])
        return ["fromkeys", 0, src, k()]
    if o < 0.93:
        return ["fromitems", 0, [[k(), k()] for _ in range(rng.randint(0, 14))]]
    return ["dict", 0, upd_arg(rng, n, False)]


def fz_op(rng, n, specs):
    """A frozendict into slot 2, and what can only be asked of one. Slot 2 is an argument of many
    other operations, which is what reaches the `PyAnyDict_Check` tests."""
    k = lambda: rng.randrange(n)
    o = rng.random()
    if o < 0.30:
        strs = [s["u"] for s in specs if s["s"]]
        kw = []
        if strs and rng.random() < 0.3:
            kw = [[x, k()] for x in rng.sample(strs, min(len(strs), rng.randint(1, 3)))]
        return ["fz", upd_arg(rng, n, False), kw]
    if o < 0.34:
        return ["fz0"]
    if o < 0.36:
        return ["fz2", upd_arg(rng, n, False)]
    if o < 0.46:
        return ["f_or", rng.randrange(3)]
    if o < 0.54:
        return ["f_hash"]
    if o < 0.60:
        return ["repr", 2]
    if o < 0.66:
        src = rng.choice([["d", rng.randrange(3)], ["s", rng.randrange(3)],
                          ["l", [k() for _ in range(rng.randint(0, 7))]],
                          ["g", [k() for _ in range(rng.randint(0, 3))]], ["n"]])
        return ["f_fromkeys", src, k()]
    if o < 0.74:
        return ["f_it", rng.choice("kvi"), rng.random() < 0.5]
    if o < 0.84:
        return [rng.choice(["get", "in"]), 2, k()]
    if o < 0.89:
        return ["getd", 2, k(), k()]
    if o < 0.93:
        return [rng.choice(["len", "keys", "values", "items"]), 2]
    if o < 0.96:
        return ["copy", 2]
    if o < 0.98:
        return ["eq", 2, rng.randrange(3), rng.random() < 0.3]
    return ["m_get", rng.random() < 0.5, rng.randrange(3), k(), rng.randrange(4), k()]


def capi_arg(rng, n):
    k = lambda: rng.randrange(n)
    o = rng.random()
    if o < 0.6:
        return ["d", rng.randrange(3)]
    if o < 0.9:
        ks = [k() for _ in range(rng.randint(0, 6))]
        return ["m", ks, [[x, k()] for x in ks if rng.random() < 0.9]]
    return ["n"]


def capi_op(rng, n, specs):
    """The entry points Python code cannot reach, on a dict, a frozendict or a list."""
    k = lambda: rng.randrange(n)
    t = rng.choice([0, 0, 1, 2, 2, -1])
    o = rng.random()
    if o < 0.20:
        return ["c_set", t, k(), k()]
    if o < 0.27:
        return ["c_del", t, k()]
    if o < 0.33:
        return ["c_in", t, k()]
    if o < 0.41:
        return ["c_get", t, k()]
    if o < 0.46:
        return ["c_gete", t, k()]
    if o < 0.51:
        return ["c_getr", t, k()]
    if o < 0.56:
        return ["c_pop", t, k()]
    if o < 0.62:
        return [rng.choice(["c_sdef", "c_sdefr"]), t, k(), k()]
    if o < 0.72:
        return ["c_merge", t, capi_arg(rng, n), rng.choice([0, 1, 2])]
    if o < 0.78:
        items = [pair_item(rng, n) for _ in range(rng.randint(0, 5))]
        return ["c_seq2", t, items, rng.random() < 0.5]
    if o < 0.80:
        return ["c_clear", t]
    if o < 0.83:
        return ["c_copy", t]
    if o < 0.87:
        return [rng.choice(["c_size", "c_keys", "c_values", "c_items"]), t]
    if o < 0.92:
        return ["c_kw", rng.randrange(3), rng.randrange(3)]
    s = rng.choice([0, 0, 1, 2, -1])
    return rng.choice([["c_sin", s, k()], ["c_sdisc", s, k()], ["c_sadd", s, k()], ["c_spop", s],
                       ["c_ssize", s], ["c_sclear", s]])


def set_arg(rng, n):
    k = lambda: rng.randrange(n)
    o = rng.random()
    if o < 0.4:
        return ["s", rng.randrange(3)]
    if o < 0.55:
        return ["d", rng.randrange(3)]
    if o < 0.85:
        return ["l", [k() for _ in range(rng.randint(0, 8))]]
    if o < 0.95:
        return ["g", [k() for _ in range(rng.randint(0, 4))]]
    return ["n"]


def set_op(rng, n):
    k = lambda: rng.randrange(n)
    s = rng.choice([0, 0, 1])
    o = rng.random()
    if o < 0.32:
        return ["sadd", s, k()]
    if o < 0.40:
        return ["sdisc", s, k()]
    if o < 0.46:
        return ["srem", s, k()]
    if o < 0.48:
        return ["sin", rng.randrange(3), k()]
    if o < 0.50:
        return ["fin", rng.randrange(3), k()]
    if o < 0.56:
        return ["spop", s]
    if o < 0.58:
        return ["sclear", s]
    if o < 0.62:
        return [rng.choice(["slen", "srepr", "shash"]), rng.randrange(3)]
    args = [set_arg(rng, n) for _ in range(rng.randint(0, 3))]
    name = rng.choice(["supd", "sunion", "sinter", "sdiff", "sinterupd", "sdiffupd"])
    if o < 0.78:
        return [name, s, args]
    if o < 0.84:
        return [rng.choice(["ssym", "ssymupd", "sdisj", "ssubset", "ssuper"]), s, set_arg(rng, n)]
    if o < 0.90:
        return [rng.choice(["sor", "sand", "ssub", "sxor", "sior", "siand", "sisub", "sixor"]),
                s, rng.randrange(3)]
    if o < 0.95:
        return ["scmp", s, rng.randrange(3), rng.choice(["lt", "le", "eq", "ne", "gt", "ge"])]
    if o < 0.97:
        return ["scopy", s]
    a = rng.choice([x for x in [set_arg(rng, n)] if x[0] != "s" or x[1] != s] or [["n"]])
    return [rng.choice(["sinit", "snew", "fnew"]), s, a]


def view_arg(rng, n, sets=True):
    o = rng.random()
    if o < 0.5:
        return ["v", rng.choice("ki"), rng.randrange(3)]
    if o < 0.8:
        return ["s", rng.randrange(3)]
    return ["l", [rng.randrange(n) if rng.random() < 0.6
                  else [rng.randrange(n), rng.randrange(n)] for _ in range(rng.randint(0, 6))]]


def view_op(rng, n):
    v = ["v", rng.choice("ki"), rng.randrange(3)]
    o = rng.random()
    if o < 0.5:
        return [rng.choice(["v_sub", "v_or", "v_xor", "v_and"]), v, view_arg(rng, n)]
    if o < 0.65:
        a = view_arg(rng, n)
        if a[0] == "l":
            a = ["s", 0]
        return ["v_cmp", v, a, rng.choice(["lt", "le", "eq", "ne", "gt", "ge"])]
    if o < 0.8:
        return ["v_disj", v, view_arg(rng, n), False]
    if o < 0.9:
        return ["v_in", v, rng.randrange(n)]
    if o < 0.97:
        return ["v_intup", v, rng.randrange(n), rng.randrange(n)]
    return ["v_len", v]


def iter_op(rng, n):
    i = rng.randrange(4)
    o = rng.random()
    if o < 0.25:
        return ["it_new", i, rng.randrange(2), rng.choice("kvi"), rng.random() < 0.5]
    if o < 0.32:
        return ["sit_new", i, rng.randrange(2)]
    if o < 0.75:
        return ["it_next", i]
    if o < 0.85:
        return ["it_hint", i]
    if o < 0.93:
        return ["it_list", i]
    return ["it_reduce", i]


def gen_dict(rng):
    pool = Pool()
    mode = rng.random()
    if mode < 0.2:
        int_pool(pool, rng, rng.randint(8, 40), 64)
    elif mode < 0.4:
        str_pool(pool, rng, rng.randint(4, 30))
    else:
        mixed_pool(pool, rng)
    n = len(pool.specs)
    ops = []
    for _ in range(rng.randint(5, 60)):
        op = dict_op(rng, n)
        if op is None:
            op = dict_op2(rng, n, pool.specs)
        ops.append(op)
    return pool, ops


def gen_frozen(rng):
    pool = Pool()
    mode = rng.random()
    if mode < 0.3:
        int_pool(pool, rng, rng.randint(4, 24), 64)
    elif mode < 0.5:
        str_pool(pool, rng, rng.randint(4, 16))
    else:
        mixed_pool(pool, rng)
    n = len(pool.specs)
    ops = []
    for _ in range(rng.randint(2, 10)):
        ops.append(["set", rng.randrange(2), rng.randrange(n), rng.randrange(n)])
    for _ in range(rng.randint(5, 40)):
        r = rng.random()
        if r < 0.5:
            ops.append(fz_op(rng, n, pool.specs))
        elif r < 0.7:
            ops.append(dict_op(rng, n) or dict_op2(rng, n, pool.specs))
        elif r < 0.85:
            ops.append(view_op(rng, n))
        else:
            ops.append(set_op(rng, n))
    return pool, ops


def gen_capi(rng):
    pool = Pool()
    mode = rng.random()
    if mode < 0.2:
        int_pool(pool, rng, rng.randint(4, 24), 64)
    elif mode < 0.45:
        str_pool(pool, rng, rng.randint(4, 16))
    else:
        mixed_pool(pool, rng)
    n = len(pool.specs)
    ops = []
    for _ in range(rng.randint(2, 10)):
        ops.append(["set", rng.randrange(2), rng.randrange(n), rng.randrange(n)])
    for _ in range(rng.randint(1, 6)):
        ops.append(["sadd", rng.randrange(2), rng.randrange(n)])
    for _ in range(rng.randint(5, 40)):
        r = rng.random()
        if r < 0.75:
            ops.append(capi_op(rng, n, pool.specs))
        elif r < 0.9:
            ops.append(fz_op(rng, n, pool.specs))
        else:
            ops.append(["fnew", 0, ["s", rng.randrange(2)]])
    return pool, ops


def gen_growth(rng):
    pool = Pool()
    if rng.random() < 0.5:
        for i in range(rng.randint(30, 400)):
            pool.add("int", i, ("num", i))
    else:
        str_pool(pool, rng, rng.randint(30, 300))
    n = len(pool.specs)
    ops = []
    if rng.random() < 0.5:
        ops.append(["fromitems", 0, [[i, i] for i in range(min(n, 14))]])
        ops.append(["upd", 0, ["d", 2], []])
    for i in range(n):
        ops.append(["set", 0, i, i])
        if rng.random() < 0.3:
            ops.append(["del", 0, rng.randrange(n)])
        if rng.random() < 0.05:
            ops.append(["popitem", 0])
        if rng.random() < 0.02:
            ops.append(["copy", 0])
        if rng.random() < 0.02:
            ops.append(["upd", 1, ["d", 0], []])
    return pool, ops


def gen_set(rng):
    pool = Pool()
    if rng.random() < 0.3:
        int_pool(pool, rng, rng.randint(8, 60), 256)
    else:
        mixed_pool(pool, rng)
    n = len(pool.specs)
    return pool, [set_op(rng, n) if rng.random() < 0.9 else dict_op(rng, n) or ["set", 0, 0, 0]
                  for _ in range(rng.randint(5, 60))]


def gen_set_growth(rng):
    pool = Pool()
    scale = rng.choice([1, 8, 2 ** 20])
    for i in range(rng.randint(20, 600)):
        pool.add("int", i * scale + 1, ("num", i))
    n = len(pool.specs)
    ops = []
    for i in range(n):
        ops.append(["sadd", 0, i])
        r = rng.random()
        if r < 0.3:
            ops.append(["sdisc", 0, rng.randrange(n)])
        elif r < 0.33:
            ops.append(["spop", 0])
        elif r < 0.35:
            ops.append(["scopy", 0])
        elif r < 0.37:
            ops.append(["supd", 1, [["s", 0]]])
        elif r < 0.39:
            ops.append(["sdiffupd", 0, [["s", 1]]])
    return pool, ops


def gen_views(rng):
    pool = Pool()
    mixed_pool(pool, rng)
    n = len(pool.specs)
    ops = []
    for _ in range(rng.randint(3, 12)):
        ops.append(["set", rng.randrange(2), rng.randrange(n), rng.randrange(n)])
    for _ in range(rng.randint(2, 8)):
        ops.append(["sadd", rng.randrange(2), rng.randrange(n)])
    for _ in range(rng.randint(5, 30)):
        ops.append(view_op(rng, n))
    return pool, ops


def gen_iters(rng):
    pool = Pool()
    int_pool(pool, rng, rng.randint(6, 16), 32)
    n = len(pool.specs)
    ops = []
    for _ in range(rng.randint(3, 12)):
        ops.append(["set", rng.randrange(2), rng.randrange(n), rng.randrange(n)])
    for _ in range(rng.randint(2, 8)):
        ops.append(["sadd", rng.randrange(2), rng.randrange(n)])
    live = set()
    for _ in range(rng.randint(10, 60)):
        r = rng.random()
        if r < 0.55:
            op = iter_op(rng, n)
            if op[0] in ("it_new", "sit_new"):
                live.add(op[1])
            elif op[1] not in live:
                continue
            ops.append(op)
        elif r < 0.7:
            ops.append(["set", rng.randrange(2), rng.randrange(n), rng.randrange(n)])
        elif r < 0.85:
            ops.append(["del", rng.randrange(2), rng.randrange(n)])
        elif r < 0.9:
            ops.append(["popitem", rng.randrange(2)])
        else:
            ops.append([rng.choice(["sadd", "sdisc"]), rng.randrange(2), rng.randrange(n)])
    return pool, ops


def gen_evil(rng):
    pool = Pool()
    h = rng.choice([0, 1, 8, 16])
    for i in range(rng.randint(2, 8)):
        pool.add("K", [i, h if rng.random() < 0.7 else i], ("K", i))
    act = rng.choice([1, 2])
    for i in range(rng.randint(1, 2)):
        pool.add("Kev", [100 + i, h, act], a=act)
    int_pool(pool, rng, 3, 8)
    n = len(pool.specs)
    if rng.random() < 0.5:
        target = "d"
        ops = []
        for _ in range(rng.randint(4, 30)):
            k = rng.randrange(n)
            ops.append(rng.choice([["set", 0, k, k], ["set", 0, k, k], ["get", 0, k], ["in", 0, k],
                                   ["del", 0, k], ["getd", 0, k, 0], ["sdef", 0, k, k],
                                   ["popd", 0, k, 0]]))
    else:
        target = "s"
        ops = []
        for _ in range(rng.randint(4, 30)):
            k = rng.randrange(n)
            ops.append(rng.choice([["sadd", 0, k], ["sadd", 0, k], ["sin", 0, k], ["sdisc", 0, k],
                                   ["srem", 0, k]]))
    return pool, ops, target


def gen_merge(rng):
    """`dict_dict_merge` with a key whose `__eq__` changes the source or the receiver: a pool of
    keys sharing a hash, so that inserting one into the receiver compares it with another."""
    pool = Pool()
    h = rng.choice([0, 1, 8, 16])
    for i in range(rng.randint(2, 7)):
        pool.add("K", [i, h if rng.random() < 0.8 else i], ("K", i))
    fresh = pool.add("K", [50, 1000 + rng.randrange(1000)], ("K", 50))
    target = rng.choice(["d0", "d1", "d1", "d1"])
    act = rng.choice([1, 2, 2, 10 + fresh]) if target == "d1" else rng.choice([1, 2, 10 + fresh])
    rs = rng.random() < 0.2
    for i in range(rng.randint(1, 3)):
        pool.add("Kev", [100 + i, h, act, rs], ("Kev", i), a=act, r=rs)
    int_pool(pool, rng, 3, 8)
    n = len(pool.specs)
    ops = []
    for _ in range(rng.randint(2, 12)):
        ops.append(["set", rng.randrange(2), rng.randrange(n), rng.randrange(n)])
    for _ in range(rng.randint(1, 6)):
        r = rng.random()
        k = rng.randrange(n)
        if r < 0.5:
            ops.append(["upd", 0, ["d", 1], []])
        elif r < 0.65:
            ops.append(["ior", 0, ["d", 1]])
        elif r < 0.85:
            ops.append(["set", rng.randrange(2), k, k])
        elif r < 0.95:
            ops.append(["del", rng.randrange(2), k])
        else:
            ops.append(["popitem", rng.randrange(2)])
    return pool, ops, target


def pair_item(rng, n):
    r = rng.random()
    if r < 0.9:
        return ["p", rng.randrange(n), rng.randrange(n)]
    if r < 0.95:
        return ["b"]
    return ["l", rng.choice([0, 1, 3])]


def od_arg(rng, n, twin=False):
    """`twin`: the C OrderedDict, whose update has a test for an exact frozendict."""
    k = lambda: rng.randrange(n)
    r = rng.random()
    if r < 0.3:
        return ["fd" if twin and rng.random() < 0.3 else "d", rng.randrange(2)]
    if r < 0.55:
        ks = [k() for _ in range(rng.randint(0, 6))]
        return ["m", ks, [[x, k()] for x in ks if rng.random() < 0.9]]
    if r < 0.8:
        return ["p", [pair_item(rng, n) for _ in range(rng.randint(0, 6))], rng.random() < 0.1]
    if r < 0.95:
        return ["it", [pair_item(rng, n) for _ in range(rng.randint(0, 3))],
                [pair_item(rng, n) for _ in range(rng.randint(0, 3))]]
    return ["n"]


def od_ops(rng, n, p, specs):
    """One OrderedDict operation; `p` is the prefix, `o_` for C and `p_` for pure Python."""
    k = lambda: rng.randrange(n)
    i = rng.choice([0, 0, 1])
    r = rng.random()
    if r < 0.30:
        return [p + "set", i, k(), k()]
    if r < 0.38:
        return [p + "del", i, k()]
    if r < 0.42:
        return [p + rng.choice(["get", "in"]), i, k()]
    if r < 0.47:
        return [p + "pop", i, k()]
    if r < 0.51:
        return [p + "popd", i, k(), k()]
    if r < 0.58:
        return [p + "popitem", i, rng.random() < 0.5]
    if r < 0.64:
        return [p + "sdef", i, k(), k()]
    if r < 0.74:
        return [p + "mte", i, k(), rng.random() < 0.5]
    if r < 0.76:
        return [p + "clear", i]
    if r < 0.80:
        return [p + "copy", i]
    if r < 0.87:
        strs = [s["u"] for s in specs if s["s"]]
        kw = []
        if strs and rng.random() < 0.3:
            kw = [[x, k()] for x in rng.sample(strs, min(len(strs), 2))]
        return [p + "upd", i, od_arg(rng, n, p == "o_"), kw]
    if r < 0.90:
        return [p + "ior", i, od_arg(rng, n, p == "o_")]
    if r < 0.92:
        return [p + "or", i, ["fd" if p == "o_" and rng.random() < 0.3 else "d", rng.randrange(2)]]
    if r < 0.96:
        return [p + "eq", i, rng.randrange(3), rng.random() < 0.3]
    return [p + "fromkeys", 0, [k() for _ in range(rng.randint(0, 6))], k()]


def od_pool(rng):
    pool = Pool()
    r = rng.random()
    if r < 0.3:
        int_pool(pool, rng, rng.randint(4, 24), 32)
    elif r < 0.5:
        str_pool(pool, rng, rng.randint(4, 12))
    else:
        mixed_pool(pool, rng)
    return pool


def gen_odict(rng):
    pool = od_pool(rng)
    n = len(pool.specs)
    ops = []
    raw = rng.random() < 0.25
    live = set()
    for _ in range(rng.randint(5, 40)):
        r = rng.random()
        if r < 0.12:
            x = rng.randrange(2)
            ops.append(["set", x, rng.randrange(n), rng.randrange(n)])
        elif r < 0.17:
            it = rng.randrange(4)
            live.add(it)
            ops.append(["o_itnew", it, rng.randrange(2), rng.choice("kvi"), rng.random() < 0.5])
        elif r < 0.27 and live:
            ops.append(["o_itnext", rng.choice(sorted(live)), None])
        elif r < 0.30:
            if not raw:
                ops.append(["o_repr", rng.randrange(3)])
        elif r < 0.34:
            ops.append(["o_eqd", rng.randrange(2), rng.randrange(2), rng.random() < 0.3,
                        rng.random() < 0.3])
        elif raw and r < 0.45:
            i = rng.randrange(2)
            ops.append(rng.choice([["r_set", i, rng.randrange(n), rng.randrange(n)],
                                   ["r_del", i, rng.randrange(n)], ["r_popitem", i],
                                   ["r_pop", i, rng.randrange(n)], ["r_clear", i]]))
        else:
            ops.append(od_ops(rng, n, "o_", pool.specs))
    # An iterator is tied to the slot it was made from.
    slots = {}
    fixed = []
    for op in ops:
        if op[0] == "o_itnew":
            slots[op[1]] = op[2]
        if op[0] == "o_itnext":
            op = ["o_itnext", op[1], slots[op[1]]]
        fixed.append(op)
    return pool, fixed


def gen_pyod(rng):
    pool = od_pool(rng)
    n = len(pool.specs)
    ops = []
    live = set()
    for _ in range(rng.randint(5, 40)):
        r = rng.random()
        if r < 0.1:
            ops.append(["set", rng.randrange(2), rng.randrange(n), rng.randrange(n)])
        elif r < 0.15:
            it = rng.randrange(4)
            kind = rng.choice("kvi")
            if rng.random() < 0.5:
                # Reversed generators walk weak proxies, which die with their link when the
                # list changes (ReferenceError). The model has no reference counts, so a
                # reversed generator here only runs while nothing is mutated.
                live.discard(it)
                ops.append(["p_itnew", it, rng.randrange(2), kind, True])
                ops.extend(["p_itnext", it] for _ in range(rng.randint(1, 8)))
            else:
                live.add(it)
                ops.append(["p_itnew", it, rng.randrange(2), kind, False])
        elif r < 0.27 and live:
            ops.append(["p_itnext", rng.choice(sorted(live))])
        else:
            ops.append(od_ops(rng, n, "p_", pool.specs))
    return pool, ops


def gen_instances(rng):
    pool = Pool()
    names = []
    for i in range(rng.randint(2, rng.choice([6, 12, 40]))):
        names.append(pool.add("str", "a" + str(i), ("str", i)))
    subs = []
    if rng.random() < 0.6:
        subs.append(pool.add("strsub", "a0", ("str", 0)))
        subs.append(pool.add("strsub", "a1", ("str", 1)))
    int_pool(pool, rng, 4, 16)
    n = len(pool.specs)
    v = lambda: rng.randrange(n)
    nm = lambda: rng.choice(names) if not subs or rng.random() < 0.9 else rng.choice(subs)
    ops = [["i_new", 0]]
    if rng.random() < 0.7:
        ops.append(["i_new", 1])
    made = {o[1] for o in ops}
    for _ in range(rng.randint(5, 50)):
        i = rng.choice(sorted(made))
        r = rng.random()
        if r < 0.40:
            ops.append(["i_set", i, nm(), v()])
        elif r < 0.50:
            ops.append(["i_del", i, nm()])
        elif r < 0.55:
            ops.append(["i_get", i, nm()])
        elif r < 0.60:
            ops.append(["i_dict", i])
        elif r < 0.63:
            ops.append(["i_deldict", i])
        elif r < 0.66:
            ops.append(["i_setdict", i, [[rng.choice(names), v()] for _ in range(rng.randint(0, 3))]])
        elif r < 0.70:
            ops.append(["i_copy", i])
        elif r < 0.72 and len(made) < 3:
            x = len(made)
            made.add(x)
            ops.append(["i_new", x])
        else:
            k = nm() if rng.random() < 0.8 else v()
            ops.append(["i_d", i, rng.choice([
                ["set", k, v()], ["set", k, v()], ["del", k], ["get", k], ["in", k], ["getd", k, v()],
                ["sdef", k, v()], ["sdef", k, v()], ["pop", k], ["popd", k, v()], ["popitem"],
                ["clear"], ["len"], ["keys"], ["items"], ["repr"]])])
    return pool, ops, names


def gen_case(rng):
    r = rng.random()
    target = None
    case = None
    if r < 0.15:
        pool, ops = gen_dict(rng)
    elif r < 0.18:
        pool, ops = gen_frozen(rng)
    elif r < 0.20:
        pool, ops = gen_capi(rng)
    elif r < 0.23:
        pool, ops = gen_growth(rng)
        case = {"every": 32}
    elif r < 0.41:
        pool, ops = gen_set(rng)
    elif r < 0.44:
        pool, ops = gen_set_growth(rng)
        case = {"every": 32}
    elif r < 0.53:
        pool, ops = gen_views(rng)
    elif r < 0.63:
        pool, ops = gen_iters(rng)
    elif r < 0.66:
        pool, ops, target = gen_evil(rng)
    elif r < 0.72:
        pool, ops, target = gen_merge(rng)
    elif r < 0.81:
        pool, ops = gen_odict(rng)
        case = {"fn": "odict", "fork": True}
    elif r < 0.89:
        pool, ops = gen_pyod(rng)
        case = {"fn": "pyod"}
    else:
        pool, ops, names = gen_instances(rng)
        case = {"fn": "instances", "fork": True, "names": names}
    c = {"mod": "dictset", "fn": "scenario", "pool": pool.specs, "ops": ops, "target": target}
    c.update(case or {})
    return c


class Runner:
    def __init__(self, case):
        self.pool = [build(s) for s in case["pool"]]
        self.uid = {id(o): s["u"] for o, s in zip(self.pool, case["pool"])}
        self.ds = [{}, {}, {}]
        self.ss = [set(), set(), set()]
        self.its = [None] * 4
        self.fn = case["fn"]
        self.limit = len(self.pool) + 2
        self.ods = [OrderedDict(), OrderedDict(), OrderedDict()] if self.fn == "odict" else []
        self.pods = [PyOrderedDict(), PyOrderedDict(), PyOrderedDict()] if self.fn == "pyod" else []
        self.oits = [None] * 4
        self.gens = [None] * 4
        self.names = [self.pool[i] for i in case.get("names", [])]
        self.C = type("C", (), {})
        self.objs = [None] * 3 if self.fn == "instances" else []
        self.touched = [False] * 3
        self.unr = []
        POOL[0] = self.pool
        t = case.get("target")
        if t in ("d", "d0"):
            TARGET[0] = self.ds[0]
        elif t == "d1":
            TARGET[0] = self.ds[1]
        elif t == "s":
            TARGET[0] = self.ss[0]

    def E(self, x):
        if isinstance(x, tuple):
            return [self.E(a) for a in x]
        return self.uid[id(x)]

    def Es(self, l):
        return [self.E(x) for x in l]

    def O(self, j):
        if isinstance(j, list):
            return tuple(self.O(x) for x in j)
        return self.pool[j]

    def enc1(self, thunk):
        return common.py_result(thunk)

    @contextlib.contextmanager
    def noting(self):
        """Keep the note on an exception, which `str(e)` does not show."""
        try:
            yield
        except Exception as e:
            notes = getattr(e, "__notes__", None)
            self.note = notes[-1] if notes else None
            raise

    def run_op(self, op):
        self.note = None
        res = common.py_result(lambda: self.step(op))
        if res.get("exc") == "SystemError":
            # The message has the C file and line; this is the form the model gives.
            res["msg"] = "~" + res["msg"].split(": ", 1)[1]
        if self.note is not None:
            res["note"] = self.note
        return res

    def digest(self):
        base = [[[self.Es(d.keys()), self.Es(d.values()), d.__sizeof__()] for d in self.ds],
                [[self.Es(s), s.__sizeof__()] for s in self.ss]]
        ods = []
        for od in self.ods:
            size = od.__sizeof__()
            ks = self.Es(dict.keys(od))
            # Bounded: after dict.popitem(od) iteration can cycle for ever (see
            # bugs/dictset-odict-stale-fast-nodes.yaml), growing a list until memory runs out.
            ods.append([size, ks, self.enc1(lambda: self.Es(itertools.islice(od, self.limit)))])
        pods = [[self.Es(dict.keys(o)), self.Es(dict.values(o)), self.Es(list(o))]
                for o in self.pods]
        insts = []
        for o, t in zip(self.objs, self.touched):
            if o is None:
                insts.append(None)
                continue
            attrs = []
            for nm in self.names:
                v = getattr(o, nm, None)
                attrs.append(None if v is None else self.E(v))
            if t:
                d = o.__dict__
                insts.append([attrs, [self.Es(d.keys()), self.Es(d.values()), d.__sizeof__()]])
            else:
                insts.append([attrs, None])
        return [base, ods, pods, insts]

    def od_arg(self, a):
        t = a[0]
        if t == "d":
            return self.ds[a[1]]
        if t == "fd":
            return frozendict(self.ds[a[1]])
        if t == "m":
            return Mapping([self.O(x) for x in a[1]], [(self.O(p[0]), self.O(p[1])) for p in a[2]])
        if t == "p":
            items = [self.seq2(x) for x in a[1]]
            if a[2]:
                def gen():
                    yield from items
                    raise ValueError("stop")
                return gen()
            return items
        if t == "it":
            return ItemsOnly([self.seq2(x) for x in a[1]], [self.seq2(x) for x in a[2]])
        return 5

    def step_od(self, op, ods, Cls):
        name = op[0][2:]
        P = self.pool
        od = ods[op[1]] if isinstance(op[1], int) and op[1] < len(ods) else None
        if name == "set":
            od[P[op[2]]] = P[op[3]]
        elif name == "del":
            del od[P[op[2]]]
        elif name == "get":
            return self.E(od[P[op[2]]])
        elif name == "in":
            return P[op[2]] in od
        elif name == "pop":
            return self.E(od.pop(P[op[2]]))
        elif name == "popd":
            return self.E(od.pop(P[op[2]], P[op[3]]))
        elif name == "popitem":
            return self.E(od.popitem(op[2]))
        elif name == "sdef":
            return self.E(od.setdefault(P[op[2]], P[op[3]]))
        elif name == "mte":
            od.move_to_end(P[op[2]], op[3])
        elif name == "clear":
            od.clear()
        elif name == "copy":
            ods[2] = od.copy()
        elif name == "upd":
            od.update(self.od_arg(op[2]), **{P[a]: P[b] for a, b in op[3]})
        elif name == "ior":
            ods[op[1]] |= self.od_arg(op[2])
        elif name == "or":
            ods[2] = od | self.od_arg(op[2])
        elif name == "eq":
            return (od != ods[op[2]]) if op[3] else (od == ods[op[2]])
        elif name == "eqd":
            o = frozendict(self.ds[op[2]]) if len(op) > 4 and op[4] else self.ds[op[2]]
            return (od != o) if op[3] else (od == o)
        elif name == "fromkeys":
            ods[2] = Cls.fromkeys([P[x] for x in op[2]], P[op[3]])
        elif name == "repr":
            return repr(od)
        else:
            raise ValueError(op)
        return None

    def view_of(self, od, kind):
        return {"k": od.keys, "v": od.values, "i": od.items}[kind]()

    def step_odx(self, op):
        name = op[0]
        P = self.pool
        if name == "o_itnew":
            v = self.view_of(self.ods[op[2]], op[3])
            self.oits[op[1]] = reversed(v) if op[4] else iter(v)
            return None
        if name == "o_itnext":
            return self.E(next(self.oits[op[1]]))
        if name == "p_itnew":
            v = self.view_of(self.pods[op[2]], op[3])
            self.gens[op[1]] = reversed(v) if op[4] else iter(v)
            return None
        if name == "p_itnext":
            return self.E(next(self.gens[op[1]]))
        if name == "r_set":
            dict.__setitem__(self.ods[op[1]], P[op[2]], P[op[3]])
            return None
        if name == "r_del":
            dict.__delitem__(self.ods[op[1]], P[op[2]])
            return None
        if name == "r_popitem":
            return self.E(dict.popitem(self.ods[op[1]]))
        if name == "r_pop":
            return self.E(dict.pop(self.ods[op[1]], P[op[2]]))
        if name == "r_clear":
            dict.clear(self.ods[op[1]])
            return None
        if name[:2] == "o_":
            return self.step_od(op, self.ods, OrderedDict)
        return self.step_od(op, self.pods, PyOrderedDict)

    def step_inst(self, op):
        name = op[0]
        P = self.pool
        n = op[1]
        o = self.objs[n]
        if name == "i_new":
            self.objs[n] = self.C()
            self.touched[n] = False
        elif name == "i_set":
            setattr(o, P[op[2]], P[op[3]])
        elif name == "i_del":
            delattr(o, P[op[2]])
        elif name == "i_get":
            return self.E(getattr(o, P[op[2]]))
        elif name == "i_dict":
            o.__dict__
            self.touched[n] = True
        elif name == "i_deldict":
            del o.__dict__
            self.touched[n] = False
        elif name == "i_setdict":
            o.__dict__ = {P[a]: P[b] for a, b in op[2]}
            self.touched[n] = True
        elif name == "i_copy":
            self.ds[2] = o.__dict__.copy()
            self.touched[n] = True
        elif name == "i_d":
            self.touched[n] = True
            keep = self.ds[2]
            self.ds[2] = o.__dict__
            try:
                return self.step([op[2][0], 2] + op[2][1:])
            finally:
                self.ds[2] = keep
        return None

    def set_arg(self, a):
        t = a[0]
        if t == "s":
            return self.ss[a[1]]
        if t == "d":
            return self.ds[a[1]]
        if t == "l":
            return [self.O(x) for x in a[1]]
        if t == "g":
            items = [self.O(x) for x in a[1]]

            def gen():
                yield from items
                raise ValueError("stop")
            return gen()
        return 5

    def seq2(self, it):
        t = it[0]
        if t == "p":
            return (self.O(it[1]), self.O(it[2]))
        if t == "b":
            return 7
        return [self.pool[0]] * it[1]

    def upd_arg(self, a, recv=None):
        t = a[0]
        if t == "d":
            return self.ds[a[1]]
        if t == "sub":
            return DictSub(self.ds[a[1]]) if False else self.sub(a[1])
        if t == "p":
            items = [self.seq2(x) for x in a[1]]
            if a[2]:
                def gen():
                    yield from items
                    raise ValueError("stop")
                return gen()
            return items
        if t == "m":
            return Mapping([self.O(x) for x in a[1]], [(self.O(p[0]), self.O(p[1])) for p in a[2]])
        if t == "mr":
            return HookMapping([self.O(x) for x in a[1]], [(self.O(p[0]), self.O(p[1])) for p in a[2]],
                               self.O(a[3]), a[4], recv, a[5])
        if t == "pr":
            items = [self.seq2(x) for x in a[1]]

            def hooked():
                for i, x in enumerate(items):
                    if i == a[2]:
                        evil_act(recv, a[3])
                    yield x
                if a[4]:
                    raise ValueError("stop")
            return hooked()
        if t == "hr":
            return AttrRaises()
        return 5

    def sub(self, slot):
        """A dict subclass with the same table: copied through the fast path of dict_merge."""
        s = DictSub()
        dict.update(s, self.ds[slot])
        return s

    def view(self, a):
        d = self.ds[a[2]]
        return d.keys() if a[1] == "k" else d.items()

    def view_arg(self, a):
        if a[0] == "v":
            return self.view(a)
        if a[0] == "s":
            return self.ss[a[1]]
        return self.set_arg(a)

    def c_target(self, t, slots):
        return slots[t] if t >= 0 else []

    def step_capi(self, op):
        name = op[0]
        P = self.pool
        t = op[1]
        d = self.c_target(t, self.ds)
        s = self.c_target(t, self.ss)
        E0 = lambda r: None if r is KeyError else self.E(r)
        if name == "c_set":
            tl.dict_setitem(d, P[op[2]], P[op[3]])
        elif name == "c_del":
            tl.dict_delitem(d, P[op[2]])
        elif name == "c_in":
            return bool(tl.dict_contains(d, P[op[2]]))
        elif name == "c_get":
            got = []
            old = sys.unraisablehook
            sys.unraisablehook = lambda u: got.append(u.exc_value)
            try:
                r = tl.dict_getitem(d, P[op[2]])
            finally:
                sys.unraisablehook = old
            e = got[0] if got else None
            return [E0(r), [type(e).__name__, str(e)] if e is not None else None]
        elif name == "c_gete":
            return E0(tl.dict_getitemwitherror(d, P[op[2]]))
        elif name == "c_getr":
            return E0(tc.dict_getitemref(d, P[op[2]]))
        elif name == "c_pop":
            r = tc.dict_pop(d, P[op[2]])
            return [r[0], self.E(r[1]) if r[0] else None]
        elif name == "c_sdef":
            # `_testcapi.dict_setdefault` returns the borrowed reference of PyDict_SetDefault as if it
            # were its own, so each call would take one reference from the value.
            r = tc.dict_setdefault(d, P[op[2]], P[op[3]])
            ctypes.pythonapi.Py_IncRef(ctypes.py_object(r))
            return self.E(r)
        elif name == "c_sdefr":
            return self.E(tc.dict_setdefaultref(d, P[op[2]], P[op[3]]))
        elif name == "c_merge":
            a = op[2]
            b = None if a[0] == "n" else self.ds[a[1]] if a[0] == "d" else self.upd_arg(a)
            tl.dict_merge(d, b, op[3])
        elif name == "c_seq2":
            tl.dict_mergefromseq2(d, [self.seq2(x) for x in op[2]], int(op[3]))
        elif name == "c_clear":
            tl.dict_clear(d)
        elif name == "c_copy":
            self.ds[2] = tl.dict_copy(d)
        elif name == "c_size":
            return tl.dict_size(d)
        elif name == "c_keys":
            return self.Es(tl.dict_keys(d))
        elif name == "c_values":
            return self.Es(tl.dict_values(d))
        elif name == "c_items":
            return [self.E(x) for x in tl.dict_items(d)]
        elif name == "c_kw":
            try:
                return ["ok", self.Es(kwf(**d, **self.ds[op[2]]))]
            except TypeError as e:
                m = str(e)
                if "multiple values" in m:
                    return ["dup", m.split("keyword argument ")[1]]
                raise
        elif name == "c_sin":
            return bool(tl.set_contains(s, P[op[2]]))
        elif name == "c_sdisc":
            return bool(tl.set_discard(s, P[op[2]]))
        elif name == "c_sadd":
            tl.set_add(s, P[op[2]])
        elif name == "c_spop":
            return self.E(tl.set_pop(s))
        elif name == "c_ssize":
            return tl.set_size(s)
        elif name == "c_sclear":
            tl.set_clear(s)
        else:
            raise ValueError(name)
        return None

    def step_fz(self, op):
        name = op[0]
        P = self.pool
        ds, ss = self.ds, self.ss
        if name == "fz":
            ds[2] = frozendict(self.upd_arg(op[1]), **{P[a]: P[b] for a, b in op[2]})
        elif name == "fz0":
            ds[2] = frozendict()
        elif name == "fz2":
            a = self.upd_arg(op[1])
            ds[2] = frozendict(a, a)
        elif name == "f_or":
            ds[2] = ds[2] | ds[op[1]]
        elif name == "f_hash":
            return hash(ds[2])
        elif name == "f_fromkeys":
            t = op[1]
            src = ds[t[1]] if t[0] == "d" else ss[t[1]] if t[0] == "s" else self.set_arg(t)
            ds[2] = frozendict.fromkeys(src, P[op[2]])
        elif name == "f_it":
            d = ds[2]
            view = {"k": d.keys, "v": d.values, "i": d.items}[op[1]]()
            return [self.E(x) for x in (reversed(view) if op[2] else iter(view))]
        elif name == "m_get":
            cls = with_missing(frozendict if op[1] else dict, op[4], P[op[5]])
            return self.E(cls(ds[op[2]])[P[op[3]]])
        else:
            raise ValueError(name)
        return None

    def step(self, op):
        name = op[0]
        P = self.pool
        ds, ss = self.ds, self.ss
        if name[:2] == "c_":
            return self.step_capi(op)
        if name[:2] == "f_" or name[:2] == "fz" or name == "m_get":
            return self.step_fz(op)
        if name[:2] in ("o_", "p_", "r_"):
            return self.step_odx(op)
        if name[:2] == "i_":
            return self.step_inst(op)
        if name == "set":
            ds[op[1]][P[op[2]]] = P[op[3]]
            return None
        if name == "get":
            return self.E(ds[op[1]][P[op[2]]])
        if name == "del":
            del ds[op[1]][P[op[2]]]
            return None
        if name == "in":
            return P[op[2]] in ds[op[1]]
        if name == "getd":
            return self.E(ds[op[1]].get(P[op[2]], P[op[3]]))
        if name == "sdef":
            return self.E(ds[op[1]].setdefault(P[op[2]], P[op[3]]))
        if name == "pop":
            return self.E(ds[op[1]].pop(P[op[2]]))
        if name == "popd":
            return self.E(ds[op[1]].pop(P[op[2]], P[op[3]]))
        if name == "popitem":
            return self.E(ds[op[1]].popitem())
        if name == "clear":
            ds[op[1]].clear()
            return None
        if name == "len":
            return len(ds[op[1]])
        if name == "keys":
            return self.Es(ds[op[1]].keys())
        if name == "values":
            return self.Es(ds[op[1]].values())
        if name == "items":
            return [self.E(x) for x in ds[op[1]].items()]
        if name == "repr":
            return repr(ds[op[1]])
        if name == "upd":
            kw = {P[a]: P[b] for a, b in op[3]}
            with self.noting():
                ds[op[1]].update(self.upd_arg(op[2], ds[op[1]]), **kw)
            return None
        if name == "ior":
            d = ds[op[1]]
            with self.noting():
                d |= self.upd_arg(op[2], d)
            return None
        if name == "or":
            ds[2] = ds[op[1]] | ds[op[2]]
            return None
        if name == "copy":
            ds[2] = ds[op[1]].copy()
            return None
        if name == "eq":
            return (ds[op[1]] != ds[op[2]]) if op[3] else (ds[op[1]] == ds[op[2]])
        if name == "fromkeys":
            t = op[2]
            src = ds[t[1]] if t[0] == "d" else ss[t[1]] if t[0] == "s" else self.set_arg(t)
            ds[2] = dict.fromkeys(src, P[op[3]])
            return None
        if name == "fromitems":
            names = {}
            parts = []
            for i, (a, b) in enumerate(op[2]):
                names[f"k{i}"] = P[a]
                names[f"v{i}"] = P[b]
                parts.append(f"k{i}: v{i}")
            ds[2] = eval("{" + ", ".join(parts) + "}", names)
            return None
        if name == "dict":
            with self.noting():
                ds[2] = dict(self.upd_arg(op[2]))
            return None
        if name == "it_new":
            d = ds[op[2]]
            view = {"k": d.keys, "v": d.values, "i": d.items}[op[3]]()
            self.its[op[1]] = (op[3], reversed(view) if op[4] else iter(view))
            return None
        if name == "sit_new":
            self.its[op[1]] = ("k", iter(ss[op[2]]))
            return None
        if name == "it_next":
            return self.E(next(self.its[op[1]][1]))
        if name == "it_hint":
            return self.its[op[1]][1].__length_hint__()
        if name == "it_list":
            return self.Es(list(self.its[op[1]][1]))
        if name == "it_reduce":
            return self.Es(self.its[op[1]][1].__reduce__()[1][0])
        return self.step_set(op)

    def step_set(self, op):
        name = op[0]
        P = self.pool
        ss = self.ss
        s = ss[op[1]] if name[0] == "s" and name != "sit_new" or name == "fin" else None
        args = lambda: [self.set_arg(a) for a in op[2]]
        if name == "sadd":
            s.add(P[op[2]])
        elif name == "srem":
            s.remove(P[op[2]])
        elif name == "sdisc":
            s.discard(P[op[2]])
        elif name == "sin":
            return P[op[2]] in s
        elif name == "fin":
            return type(s).__contains__(s, P[op[2]])
        elif name == "spop":
            return self.E(s.pop())
        elif name == "sclear":
            s.clear()
        elif name == "slen":
            return len(s)
        elif name == "srepr":
            return repr(s)
        elif name == "shash":
            return hash(frozenset(s))
        elif name == "supd":
            s.update(*args())
        elif name == "sunion":
            ss[2] = s.union(*args())
        elif name == "sinter":
            ss[2] = s.intersection(*args())
        elif name == "sdiff":
            ss[2] = s.difference(*args())
        elif name == "ssym":
            ss[2] = s.symmetric_difference(self.set_arg(op[2]))
        elif name == "scopy":
            ss[2] = s.copy()
        elif name == "sinterupd":
            s.intersection_update(*args())
        elif name == "sdiffupd":
            s.difference_update(*args())
        elif name == "ssymupd":
            s.symmetric_difference_update(self.set_arg(op[2]))
        elif name == "sdisj":
            return s.isdisjoint(self.set_arg(op[2]))
        elif name == "ssubset":
            return s.issubset(self.set_arg(op[2]))
        elif name == "ssuper":
            return s.issuperset(self.set_arg(op[2]))
        elif name == "scmp":
            o = ss[op[2]]
            return {"lt": lambda: s < o, "le": lambda: s <= o, "eq": lambda: s == o,
                    "ne": lambda: s != o, "gt": lambda: s > o, "ge": lambda: s >= o}[op[3]]()
        elif name == "sor":
            ss[2] = s | ss[op[2]]
        elif name == "sand":
            ss[2] = s & ss[op[2]]
        elif name == "ssub":
            ss[2] = s - ss[op[2]]
        elif name == "sxor":
            ss[2] = s ^ ss[op[2]]
        elif name == "sior":
            s |= ss[op[2]]
        elif name == "siand":
            s &= ss[op[2]]
        elif name == "sisub":
            s -= ss[op[2]]
        elif name == "sixor":
            s ^= ss[op[2]]
        elif name == "sinit":
            s.__init__(self.set_arg(op[2]))
        elif name == "snew":
            ss[2] = set(self.set_arg(op[2]))
        elif name == "fnew":
            ss[2] = frozenset(self.set_arg(op[2]))
        else:
            return self.step_view(op)
        return None

    def step_view(self, op):
        name = op[0]
        v = self.view(op[1])
        if name == "v_sub":
            self.ss[2] = v - self.view_arg(op[2])
        elif name == "v_or":
            self.ss[2] = v | self.view_arg(op[2])
        elif name == "v_xor":
            self.ss[2] = v ^ self.view_arg(op[2])
        elif name == "v_and":
            self.ss[2] = v & self.view_arg(op[2])
        elif name == "v_cmp":
            o = self.view_arg(op[2])
            return {"lt": lambda: v < o, "le": lambda: v <= o, "eq": lambda: v == o,
                    "ne": lambda: v != o, "gt": lambda: v > o, "ge": lambda: v >= o}[op[3]]()
        elif name == "v_disj":
            return v.isdisjoint(self.view_arg(op[2]))
        elif name == "v_in":
            return self.pool[op[2]] in v
        elif name == "v_intup":
            return (self.pool[op[2]], self.pool[op[3]]) in v
        elif name == "v_len":
            return len(v)
        else:
            raise ValueError(name)
        return None


def run_forked(case):
    """The scenario in a child, so that a crash the model predicts can be observed."""
    rd, wr = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(rd)
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        resource.setrlimit(resource.RLIMIT_CPU, (20, 25))
        resource.setrlimit(resource.RLIMIT_AS, (2 ** 31, 2 ** 31))
        # A child must never return into the parent's loop, whatever goes wrong here.
        try:
            with os.fdopen(wr, "w") as f:
                r = Runner(case)
                for op in case["ops"]:
                    res = r.run_op(op)
                    f.write(json.dumps([res, r.digest()]) + "\n")
                    f.flush()
        except BaseException as e:
            print("child failed:", repr(e), file=sys.stderr)
            os._exit(3)
        os._exit(0)
    os.close(wr)
    with os.fdopen(rd) as f:
        data = f.read()
    _, status = os.waitpid(pid, 0)
    out = [json.loads(line) for line in data.splitlines()]
    if os.WIFSIGNALED(status):
        out.append([{"exc": "<crash>", "msg": ""}, None])
    return {"ok": out}


def run_python(case):
    if case.get("fork"):
        return run_forked(case)
    r = Runner(case)
    out = []
    every = case.get("every", 1)
    last = len(case["ops"]) - 1
    for i, op in enumerate(case["ops"]):
        res = r.run_op(op)
        out.append([res, r.digest() if i % every == 0 or i == last else None])
    return {"ok": out}


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=2000)
