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

import json
import random
import sys

import common


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


class KEvil(K):
    __slots__ = ("act",)
    __hash__ = K.__hash__

    def __init__(self, c, h, u, act):
        super().__init__(c, h, u)
        self.act = act

    def __eq__(self, o):
        t = TARGET[0]
        if self.act == 1:
            t.clear()
        else:
            try:
                t.popitem() if isinstance(t, dict) else t.pop()
            except KeyError:
                pass
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


class DictSub(dict):
    """Keeps dict's tp_iter, so dict_merge takes the fast path."""


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
        return p
    if kind == "strsub":
        return S(p)
    if kind == "K":
        return K(p[0], p[1], u)
    if kind == "Kr":
        return KRaise(p[0], p[1], u)
    if kind == "Kev":
        return KEvil(p[0], p[1], u, p[2])
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


def upd_arg(rng, n):
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
        return ["m", ks, pairs]
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
    return ["dict", 0, upd_arg(rng, n)]


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
    if o < 0.50:
        return ["sin", rng.randrange(3), k()]
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


def gen_case(rng):
    r = rng.random()
    target = None
    if r < 0.30:
        pool, ops = gen_dict(rng)
    elif r < 0.33:
        pool, ops = gen_growth(rng)
    elif r < 0.60:
        pool, ops = gen_set(rng)
    elif r < 0.63:
        pool, ops = gen_set_growth(rng)
    elif r < 0.78:
        pool, ops = gen_views(rng)
    elif r < 0.93:
        pool, ops = gen_iters(rng)
    else:
        pool, ops, target = gen_evil(rng)
    return {"mod": "dictset", "fn": "scenario", "pool": pool.specs, "ops": ops, "target": target}


class Runner:
    def __init__(self, case):
        self.pool = [build(s) for s in case["pool"]]
        self.uid = {id(o): s["u"] for o, s in zip(self.pool, case["pool"])}
        self.ds = [{}, {}, {}]
        self.ss = [set(), set(), set()]
        self.its = [None] * 4
        t = case.get("target")
        if t == "d":
            TARGET[0] = self.ds[0]
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

    def digest(self):
        return [[[self.Es(d.keys()), self.Es(d.values()), d.__sizeof__()] for d in self.ds],
                [[self.Es(s), s.__sizeof__()] for s in self.ss]]

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

    def upd_arg(self, a):
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

    def step(self, op):
        name = op[0]
        P = self.pool
        ds, ss = self.ds, self.ss
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
            ds[op[1]].update(self.upd_arg(op[2]), **kw)
            return None
        if name == "ior":
            d = ds[op[1]]
            d |= self.upd_arg(op[2])
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
        s = ss[op[1]] if name[0] == "s" and name != "sit_new" else None
        args = lambda: [self.set_arg(a) for a in op[2]]
        if name == "sadd":
            s.add(P[op[2]])
        elif name == "srem":
            s.remove(P[op[2]])
        elif name == "sdisc":
            s.discard(P[op[2]])
        elif name == "sin":
            return P[op[2]] in s
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


def run_python(case):
    r = Runner(case)
    out = []
    for op in case["ops"]:
        out.append([common.py_result(lambda: r.step(op)), r.digest()])
    return {"ok": out}


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=2000)
