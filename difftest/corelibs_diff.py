"""Differential test for CoreLibs: Lean model vs the running CPython.

One section per area. `CORELIBS_AREA=coll,rand` restricts the run to those areas;
the default is every area that has a generator:
  scripts/r env CORELIBS_AREA=coll python3 difftest/corelibs_diff.py --cases 50000 --seed 1
"""

import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import main, py_result  # noqa: E402

# ====== BEGIN AREA coll (Lib/collections/__init__.py (everything except OrderedDict)) ======
# Everything for this area stays between these two markers; prefix top-level names with coll_.
import collections as coll_collections  # noqa: E402
import collections.abc as coll_abc  # noqa: E402
import copy as coll_copy  # noqa: E402

coll_KEYS = ["a", "b", "c", "d", "e", "f"]
coll_EDGE = [0, 0, 1, -1, 2, -2, 3, 5, -5, 2**31, -2**31, 2**63 - 1, -2**63, 2**63, 2**64, -2**64]


def coll_int(rng):
    return rng.choice(coll_EDGE) if rng.random() < 0.3 else rng.randint(-4, 6)


def coll_items(rng, small=False):
    keys = rng.sample(coll_KEYS, rng.randint(0, len(coll_KEYS)))
    return [[k, rng.randint(-3, 5) if small else coll_int(rng)] for k in keys]


def coll_xs(rng, unhashable=False):
    xs = [rng.choice(coll_KEYS) for _ in range(rng.randint(0, 10))]
    if unhashable and xs and rng.random() < 0.1:
        xs.insert(rng.randrange(len(xs) + 1), "#L")
    return xs


def coll_src(rng, case):
    case["src"] = rng.choice(["none", "mapping", "iter"])
    if case["src"] == "mapping":
        case["items"] = coll_items(rng)
        case["mty"] = rng.choice(["dict", "dict", "mapping", "bad_items"])
    elif case["src"] == "iter":
        case["xs"] = coll_xs(rng, unhashable=True)
        case["fail"] = rng.random() < 0.2
    case["kw"] = coll_items(rng) if rng.random() < 0.3 else []


def coll_gen_ctr(rng):
    op = rng.choice(["new", "update", "update", "subtract", "count_py", "count_c", "count_c", "most_common",
                     "most_common", "elements", "copy", "reduce", "delitem", "getitem", "repr", "fromkeys",
                     "keep_positive", "pos", "neg", "add", "sub", "or", "and", "xor", "xor", "eq", "ne", "le",
                     "lt", "ge", "gt", "iadd", "isub", "ior", "iand", "ixor", "ixor"])
    case = {"fn": "coll.ctr", "op": op, "a": coll_items(rng)}
    if op in ("new", "update", "subtract"):
        coll_src(rng, case)
    if op in ("count_py", "count_c"):
        case["xs"] = coll_xs(rng, unhashable=True)
        case["fail"] = rng.random() < 0.2
        case["inst"] = rng.random() < 0.3
        case["slow"] = rng.random() < 0.3
    if op == "fromkeys":
        case["xs"] = coll_xs(rng)
    if op in ("delitem", "getitem"):
        case["e"] = rng.choice(coll_KEYS + ["#L"])
    if op == "most_common":
        case["n"] = rng.choice([None, None, 0, 1, 2, 3, 4, 5, 6, 7, 100, -1, -2, 2**63, -2**63])
    if op == "elements":
        case["a"] = coll_items(rng, small=True)
        if rng.random() < 0.1:
            case["a"].insert(rng.randrange(len(case["a"]) + 1),
                             ["z", rng.choice([2**63, -2**63 - 1, 2**64])])
    if op in ("add", "sub", "or", "and", "xor", "eq", "ne", "le", "lt", "ge", "gt"):
        r = rng.random()
        if r < 0.9:
            # bias towards equal/ordered pairs so that the comparisons are not all false
            case["b"] = coll_items(rng)
            if r < 0.3:
                d = dict(map(tuple, case["a"]))
                d.update({k: v + rng.randint(0, 1) for k, v in d.items()})
                case["b"] = [[k, v] for k, v in d.items()]
                rng.shuffle(case["b"])
            elif r < 0.45:
                case["b"] = [list(p) for p in case["a"] if p[1] != 0]
                rng.shuffle(case["b"])
    if op in ("iadd", "isub", "ior", "iand", "ixor"):
        case["bty"] = rng.choice(["Counter", "Counter", "Counter", "dict", "int"])
        case["b"] = coll_items(rng)
    return case


def coll_ctr(items, cls=None):
    c = (cls or coll_collections.Counter)()
    for k, v in items:
        dict.__setitem__(c, k, v)
    return c


def coll_enc(d):
    return [[k, v] for k, v in d.items()]


def coll_el(x):
    return [1] if x == "#L" else x


def coll_iter(xs, fail):
    for x in xs:
        yield coll_el(x)
    if fail:
        raise ValueError("boom")


class coll_Map(coll_abc.Mapping):
    """A Mapping that is not a dict: dict.update reads keys() and [] (bad: items() raises)."""
    def __init__(self, d, bad):
        self._d = d
        self._bad = bad

    def __getitem__(self, k):
        return self._d[k]

    def __iter__(self):
        return iter(self._d)

    def __len__(self):
        return len(self._d)

    def items(self):
        if self._bad:
            raise RuntimeError("items")
        return self._d.items()


def coll_src_arg(case):
    if case["src"] == "none":
        return None
    if case["src"] == "mapping":
        d = dict(map(tuple, case["items"]))
        mty = case.get("mty", "dict")
        return d if mty == "dict" else coll_Map(d, mty == "bad_items")
    return coll_iter(case["xs"], case.get("fail", False))


def coll_ipy_count(mapping, iterable):
    'Lib/collections/__init__.py:540-544, verbatim.'
    mapping_get = mapping.get
    for elem in iterable:
        mapping[elem] = mapping_get(elem, 0) + 1


class coll_SlowCounter(coll_collections.Counter):
    """Overrides `get`, which sends the C `_count_elements` down its slow path."""
    def get(self, *args):
        return super().get(*args)


def coll_out(thunk, state):
    """A mutating call: the state it leaves and the exception, as `[state, exc]`."""
    try:
        thunk()
        exc = None
    except Exception as e:
        exc = [type(e).__name__, str(e)]
    return [coll_enc(state), exc]


def coll_run_ctr(case):
    op = case["op"]
    a = coll_ctr(case["a"])
    Counter = coll_collections.Counter

    def body():
        if op == "new":
            return coll_enc(Counter(coll_src_arg(case), **dict(map(tuple, case["kw"]))))
        if op == "update":
            return coll_out(lambda: a.update(coll_src_arg(case), **dict(map(tuple, case["kw"]))), a)
        if op == "subtract":
            return coll_out(lambda: a.subtract(coll_src_arg(case), **dict(map(tuple, case["kw"]))), a)
        if op in ("count_py", "count_c"):
            m = coll_ctr(case["a"], coll_SlowCounter if case["slow"] else None)
            if case["inst"]:
                m.get = lambda k, d: dict.get(m, k, d) + 10
            f = coll_ipy_count if op == "count_py" else coll_collections._count_elements
            return coll_out(lambda: f(m, coll_iter(case["xs"], case["fail"])), m)
        if op == "most_common":
            r = a.most_common(case["n"]) if case["n"] is not None else a.most_common()
            return [list(p) for p in r]
        if op == "elements":
            out = []

            def drain():
                for x in a.elements():
                    out.append(x)
            r = coll_out(drain, {})
            return [out, r[1]]
        if op == "copy":
            c = a.copy()
            return [type(c).__name__, c is not a, coll_enc(c)]
        if op == "reduce":
            cls, args = a.__reduce__()
            assert len(args) == 1
            return [cls.__name__, type(args[0]).__name__, coll_enc(args[0])]
        if op == "delitem":
            del a[coll_el(case["e"])]
            return coll_enc(a)
        if op == "getitem":
            return a[coll_el(case["e"])]
        if op == "repr":
            return repr(a)
        if op == "fromkeys":
            return coll_enc(Counter.fromkeys(case["xs"]))
        if op == "keep_positive":
            return coll_out(a._keep_positive, a)
        if op == "pos":
            return coll_enc(+a)
        if op == "neg":
            return coll_enc(-a)
        if op in ("add", "sub", "or", "and", "xor"):
            b = coll_ctr(case["b"]) if "b" in case else 5
            r = {"add": lambda: a + b, "sub": lambda: a - b, "or": lambda: a | b,
                 "and": lambda: a & b, "xor": lambda: a ^ b}[op]()
            return coll_enc(r)
        if op in ("eq", "ne", "le", "lt", "ge", "gt"):
            b = coll_ctr(case["b"]) if "b" in case else 5
            return {"eq": lambda: a == b, "ne": lambda: a != b, "le": lambda: a <= b,
                    "lt": lambda: a < b, "ge": lambda: a >= b, "gt": lambda: a > b}[op]()
        if op in ("iadd", "isub", "ior", "iand", "ixor"):
            ty = case["bty"]
            b = coll_ctr(case["b"]) if ty == "Counter" else (
                dict(map(tuple, case["b"])) if ty == "dict" else 5)
            f = {"iadd": Counter.__iadd__, "isub": Counter.__isub__, "ior": Counter.__ior__,
                 "iand": Counter.__iand__, "ixor": Counter.__ixor__}[op]
            return coll_out(lambda: f(a, b), a)
        raise AssertionError(op)
    return py_result(body)


class coll_CMMiss(coll_collections.ChainMap):
    def __missing__(self, key):
        return -1


class coll_UDPlain(coll_collections.UserDict):
    pass


class coll_UDMiss(coll_collections.UserDict):
    def __missing__(self, key):
        return -1


class coll_DictMiss(dict):
    def __missing__(self, key):
        return -1


class coll_UDRaise(coll_collections.UserDict):
    def __copy__(self):
        raise RuntimeError("nocopy")


class coll_UDRaiseMiss(coll_collections.UserDict):
    def __missing__(self, key):
        raise ValueError("miss")


def coll_pairs(case):
    for k, v in case["o"]:
        yield (k, v)
    if case.get("bad"):
        yield (1,)
    if case.get("fail"):
        raise ValueError("boom")


def coll_gen_pairs(items):
    for k, v in items:
        yield (k, v)
    raise ValueError("boom")


coll_UD_CLASSES = [coll_collections.UserDict, coll_UDPlain, coll_UDMiss]


def coll_d(items):
    return dict(map(tuple, items))


coll_CM_ODD_KEYS = ["a\\b", "it's", "q\"'x", "\t"]


def coll_gen_cm(rng):
    op = rng.choice(["new", "getitem", "get", "len", "iter", "contains", "bool", "repr", "repr_self",
                     "getitem_dd", "contains_dd", "fromkeys", "copy", "new_child", "parents", "setitem",
                     "delitem", "popitem", "pop", "clear", "ior", "ior", "or", "ror", "ror_bad"])
    n = rng.choice([0, 1, 1, 2, 2, 3, 4])
    keys = coll_KEYS + (coll_CM_ODD_KEYS if op in ("getitem", "delitem", "pop") else [])
    case = {"fn": "coll.cm", "op": op, "k": rng.choice(keys),
            "maps": [coll_items(rng, small=True) if rng.random() < 0.8 else [] for _ in range(n)]}
    if rng.random() < 0.4:
        case["d"] = rng.randint(-3, 3)
    if op in ("get", "getitem") and rng.random() < 0.5:
        case["sub"] = 1
    if op == "fromkeys":
        case["xs"] = coll_xs(rng)
        case["fail"] = rng.random() < 0.2
    if op in ("or", "ror", "new_child", "ior"):
        if rng.random() < 0.8:
            case["o"] = coll_items(rng, small=True)
    if op == "new_child":
        case["kw"] = coll_items(rng, small=True) if rng.random() < 0.5 else []
    if op == "ior":
        case["gen"] = rng.random() < 0.3
    return case


def coll_enc_cm(c):
    return [coll_enc(m) for m in c.maps]


class coll_BadMap(coll_abc.Mapping):
    """A Mapping whose [] raises, so dict(other) fails."""
    def __getitem__(self, k):
        raise LookupError("gi")

    def __iter__(self):
        return iter(["x"])

    def __len__(self):
        return 1


def coll_copy_bits(r, c):
    return [r is not c, r.maps[0] is not c.maps[0],
            len(r.maps) == len(c.maps) and all(x is y for x, y in zip(r.maps[1:], c.maps[1:])),
            coll_enc_cm(r)]


def coll_run_cm(case):
    op = case["op"]
    ChainMap = coll_collections.ChainMap
    cls = coll_CMMiss if case.get("sub") == 1 else ChainMap
    maps = [coll_d(m) for m in case["maps"]]
    c = cls(*maps)
    c.maps = maps
    k = case.get("k")
    d = case.get("d")

    def body():
        if op == "new":
            return coll_enc_cm(ChainMap(*maps))
        if op == "getitem":
            return c[k]
        if op in ("getitem_dd", "contains_dd"):
            if maps:
                c.maps = [coll_collections.defaultdict(int, maps[0])] + maps[1:]
            return c[k] if op == "getitem_dd" else (k in c)
        if op == "get":
            return c.get(k, d) if d is not None else c.get(k)
        if op == "len":
            return len(c)
        if op == "iter":
            return list(c)
        if op == "contains":
            return k in c
        if op == "bool":
            return bool(c)
        if op == "repr":
            return repr(c)
        if op == "repr_self":
            c.maps.append(c)
            return repr(c)
        if op == "fromkeys":
            return coll_enc_cm(ChainMap.fromkeys(coll_iter(case["xs"], case["fail"]), 0 if d is None else d))
        if op == "copy":
            return coll_copy_bits(c.copy(), c)
        if op == "new_child":
            m = coll_d(case["o"]) if "o" in case else None
            return coll_enc_cm(c.new_child(m, **coll_d(case["kw"])))
        if op == "parents":
            return coll_enc_cm(c.parents)
        if op == "setitem":
            c[k] = 0 if d is None else d
            return coll_enc_cm(c)
        if op == "delitem":
            del c[k]
            return coll_enc_cm(c)
        if op == "popitem":
            r = c.popitem()
            return [list(r), coll_enc_cm(c)]
        if op == "pop":
            r = c.pop(k, d) if d is not None else c.pop(k)
            return [r, coll_enc_cm(c)]
        if op == "clear":
            c.clear()
            return coll_enc_cm(c)
        if op == "ior":
            m0 = c.maps[0] if c.maps else None
            if "o" not in case:
                other = 5
            elif case.get("gen"):
                other = coll_gen_pairs(case["o"])
            else:
                other = coll_d(case["o"])
            try:
                r = c
                r |= other
                bits, exc = [r is c, r.maps[0] is m0], None
            except Exception as e:
                bits, exc = None, [type(e).__name__, str(e)]
            return [bits, coll_enc_cm(c), exc]
        if op == "ror_bad":
            return coll_enc_cm(ChainMap.__ror__(c, coll_BadMap()))
        if op == "or":
            return coll_copy_bits(c | (coll_d(case["o"]) if "o" in case else 5), c)
        if op == "ror":
            return coll_enc_cm((coll_d(case["o"]) if "o" in case else 5) | c)
        raise AssertionError(op)
    return py_result(body)


def coll_gen_ud(rng):
    op = rng.choice(["new", "len", "getitem", "setitem", "delitem", "iter", "contains", "get",
                     "repr", "or", "ror", "ior", "copy", "copy_dunder", "fromkeys", "pop",
                     "popitem", "setdefault", "clear", "items_contains", "reversed",
                     "dict_reversed", "dict_getitem",
                     "dict_pop", "dict_popitem", "dict_setdefault", "dict_items_contains",
                     "new_p", "getitem_p", "repr_self", "ior_p", "ior_p", "copy_p", "copy_p", "fromkeys_p"])
    case = {"fn": "coll.ud", "op": op, "a": coll_items(rng, small=True),
            "sub": rng.choice([0, 1, 2]), "k": rng.choice(coll_KEYS)}
    if op == "new_p":
        case["o"] = coll_items(rng, small=True)
        case["kw"] = coll_items(rng, small=True) if rng.random() < 0.5 else []
        case["bad"] = rng.random() < 0.2
        case["fail"] = rng.random() < 0.2
    if op == "ior_p":
        case["oty"] = rng.choice(["user", "dict", "gen", "int"])
        case["o"] = coll_items(rng, small=True)
    if op == "copy_p":
        case["raise"] = rng.random() < 0.3
    if op == "fromkeys_p":
        case["xs"] = coll_xs(rng)
        case["fail"] = rng.random() < 0.2
    if rng.random() < 0.5:
        case["d"] = rng.randint(-3, 3)
    if op in ("items_contains", "dict_items_contains") and rng.random() < 0.5:
        case["d"] = -1
    if op == "new":
        case["kw"] = coll_items(rng, small=True) if rng.random() < 0.5 else []
        if rng.random() < 0.7:
            case["o"] = coll_items(rng, small=True)
    if op in ("or", "ror"):
        case["oty"] = rng.choice(["user", "dict", "frozen", "int"])
        case["o"] = coll_items(rng, small=True)
    if op == "ior":
        case["o"] = coll_items(rng, small=True)
    if op == "fromkeys":
        case["xs"] = coll_xs(rng)
    return case


def coll_enc_ud(u):
    return [type(u).__name__, coll_enc(u.data)]


def coll_run_ud(case):
    op = case["op"]
    cls = coll_UD_CLASSES[case["sub"]]
    u = cls()
    u.data = coll_d(case["a"])
    k = case["k"]
    d = case.get("d")
    plain = (coll_DictMiss if case["sub"] == 2 else dict)(coll_d(case["a"]))

    def other():
        ty = case["oty"]
        if ty == "user":
            return coll_collections.UserDict(coll_d(case["o"]))
        if ty == "frozen":
            return frozendict(coll_d(case["o"]))
        return coll_d(case["o"]) if ty == "dict" else 5

    def body():
        if op == "new":
            src = coll_d(case["o"]) if "o" in case else None
            return coll_enc_ud(cls(src, **coll_d(case["kw"])))
        if op == "len":
            return len(u)
        if op == "getitem":
            return u[k]
        if op == "setitem":
            u[k] = 0 if d is None else d
            return coll_enc_ud(u)
        if op == "delitem":
            del u[k]
            return coll_enc_ud(u)
        if op == "iter":
            return list(u)
        if op == "contains":
            return k in u
        if op == "get":
            return u.get(k, d) if d is not None else u.get(k)
        if op == "repr":
            return repr(u)
        if op == "or":
            return coll_enc_ud(u | other())
        if op == "ror":
            if case["oty"] == "user":
                return coll_enc_ud(coll_collections.UserDict.__ror__(u, other()))
            return coll_enc_ud(other() | u)
        if op == "ior":
            r = u
            r |= coll_d(case["o"])
            return coll_enc_ud(r)
        if op == "copy":
            return coll_enc_ud(u.copy())
        if op == "copy_dunder":
            return coll_enc_ud(coll_copy.copy(u))
        if op == "fromkeys":
            return coll_enc_ud(cls.fromkeys(case["xs"], 0 if d is None else d))
        if op == "pop":
            r = u.pop(k, d) if d is not None else u.pop(k)
            return [r, coll_enc_ud(u)]
        if op == "popitem":
            r = u.popitem()
            return [list(r), coll_enc_ud(u)]
        if op == "setdefault":
            r = u.setdefault(k, 0 if d is None else d)
            return [r, coll_enc_ud(u)]
        if op == "clear":
            u.clear()
            return coll_enc_ud(u)
        if op == "items_contains":
            return (k, 0 if d is None else d) in u.items()
        if op == "reversed":
            return list(reversed(u))
        if op == "dict_reversed":
            return list(reversed(plain))
        if op == "dict_getitem":
            return plain[k]
        if op == "dict_pop":
            r = plain.pop(k, d) if d is not None else plain.pop(k)
            return [r, coll_enc(plain)]
        if op == "dict_popitem":
            r = plain.popitem()
            return [list(r), coll_enc(plain)]
        if op == "dict_setdefault":
            r = plain.setdefault(k, 0 if d is None else d)
            return [r, coll_enc(plain)]
        if op == "dict_items_contains":
            return (k, 0 if d is None else d) in plain.items()
        if op == "new_p":
            return coll_enc(cls(coll_pairs(case), **coll_d(case["kw"])).data)
        if op == "getitem_p":
            v = coll_UDRaiseMiss()
            v.data = coll_d(case["a"])
            return v[k]
        if op == "repr_self":
            u[k] = u
            return repr(u)
        if op == "ior_p":
            ty = case["oty"]
            o = {"user": lambda: coll_collections.UserDict(coll_d(case["o"])), "dict": lambda: coll_d(case["o"]),
                 "gen": lambda: coll_gen_pairs(case["o"]), "int": lambda: 5}[ty]()
            try:
                r = u
                r |= o
                assert r is u
                exc = None
            except Exception as e:
                exc = [type(e).__name__, str(e)]
            return [coll_enc_ud(u), exc]
        if op == "copy_p":
            v = (coll_UDRaise if case["raise"] else cls)()
            v.data = coll_d(case["a"])
            v.extra = 5
            try:
                c = v.copy()
                res = {"ok": [type(c).__name__, c is not v, c.data is not v.data, coll_enc(c.data),
                              len(vars(c)) - 1]}
            except Exception as e:
                res = {"exc": type(e).__name__, "msg": str(e)}
            return [coll_enc(v.data), res]
        if op == "fromkeys_p":
            return coll_enc_ud(cls.fromkeys(coll_iter(case["xs"], case["fail"]), 0 if d is None else d))
        raise AssertionError(op)
    return py_result(body)


class coll_ULPlain(coll_collections.UserList):
    pass


class coll_USPlain(coll_collections.UserString):
    pass


coll_IDX = [0, 1, 2, -1, -2, 3, 5, -5, 7, -7, 2**31, 2**63 - 1, -2**63, 2**63, -2**63 - 1, 2**64]


def coll_ints(rng):
    return [rng.randint(-2, 4) for _ in range(rng.randint(0, 7))]


def coll_slice_args(rng, case, names=("st", "sp", "se")):
    for name in names:
        if rng.random() < 0.6:
            v = rng.choice(coll_IDX)
            if name == names[-1] and v == 0 and rng.random() < 0.9:
                v = 1
            case[name] = v


def coll_slice_of(case, names=("st", "sp", "se")):
    return slice(*(case.get(n) for n in names))


def coll_int_gen(xs, fail):
    yield from xs
    if fail:
        raise ValueError("boom")


class coll_RevList(list):
    """A list subclass whose __iter__ yields the items reversed."""
    def __iter__(self):
        return iter(list.__reversed__(self))


def coll_gen_ul(rng):
    op = rng.choice(["new", "repr", "lt", "le", "eq", "gt", "ge", "contains", "len", "getitem",
                     "getslice", "setitem", "setslice", "delitem", "delslice", "add", "radd",
                     "iadd", "mul", "imul", "copy", "copy_dunder", "append", "insert", "pop",
                     "remove", "clear", "count", "index", "reverse", "sort", "extend",
                     "gen_iadd", "gen_extend", "gen_add", "gen_radd", "gen_list_iadd", "init_sub"])
    case = {"fn": "coll.ul", "op": op, "sub": rng.choice([0, 1]), "a": coll_ints(rng)}
    if op.startswith("gen_") or op == "init_sub":
        case["o"] = coll_ints(rng)
        case["fail"] = rng.random() < 0.5
    if op in ("contains", "setitem", "append", "insert", "remove", "count", "index"):
        case["x"] = rng.randint(-2, 5)
    if op in ("getitem", "setitem", "delitem", "insert", "mul", "imul"):
        case["i"] = rng.choice(coll_IDX)
    if op in ("mul", "imul"):
        case["i"] = rng.choice([0, 1, 2, 3, -1, -2**63, 2**63, 2**62, 2**63 - 1])
        if rng.random() < 0.3:
            case["a"] = []
        # a one-item list times a huge count is a real allocation attempt in both sides
        if len(case["a"]) == 1 and case["i"] in (2**62, 2**63 - 1):
            case["i"] = 2
    if op == "pop" and rng.random() < 0.6:
        case["i"] = rng.choice(coll_IDX)
    if op in ("getslice", "setslice", "delslice"):
        coll_slice_args(rng, case)
    if op == "index":
        coll_slice_args(rng, case, ("st", "sp"))
    if op == "sort":
        case["r"] = rng.random() < 0.5
    if op == "setslice":
        case["o"] = coll_ints(rng)
    if op in ("new", "lt", "le", "eq", "gt", "ge", "add", "radd", "iadd", "extend"):
        if op != "new" or rng.random() < 0.8:
            case["oty"] = rng.choice(["user", "list", "tuple", "int"])
            case["o"] = coll_ints(rng)
            if rng.random() < 0.3:
                case["o"] = list(case["a"])
    return case


def coll_enc_ul(u):
    return [type(u).__name__, list(u.data)]


def coll_opnd(case):
    ty = case["oty"]
    if ty == "user":
        return coll_collections.UserList(case["o"])
    if ty == "list":
        return list(case["o"])
    return tuple(case["o"]) if ty == "tuple" else 5


def coll_run_ul(case):
    op = case["op"]
    cls = coll_ULPlain if case["sub"] else coll_collections.UserList
    u = cls(case["a"])
    x = case.get("x", 0)
    i = case.get("i", 0)

    def body():
        if op == "new":
            return coll_enc_ul(cls(coll_opnd(case)) if "oty" in case else cls())
        if op == "repr":
            return repr(u)
        if op in ("lt", "le", "eq", "gt", "ge"):
            o = coll_opnd(case)
            return {"lt": lambda: u < o, "le": lambda: u <= o, "eq": lambda: u == o,
                    "gt": lambda: u > o, "ge": lambda: u >= o}[op]()
        if op == "contains":
            return x in u
        if op == "len":
            return len(u)
        if op == "getitem":
            return u[i]
        if op == "getslice":
            return coll_enc_ul(u[coll_slice_of(case)])
        if op == "setitem":
            u[i] = x
            return coll_enc_ul(u)
        if op == "setslice":
            u[coll_slice_of(case)] = case["o"]
            return coll_enc_ul(u)
        if op == "delitem":
            del u[i]
            return coll_enc_ul(u)
        if op == "delslice":
            del u[coll_slice_of(case)]
            return coll_enc_ul(u)
        if op == "add":
            return coll_enc_ul(u + coll_opnd(case))
        if op == "radd":
            o = coll_opnd(case)
            return coll_enc_ul(u.__radd__(o))
        if op == "iadd":
            r = u
            r += coll_opnd(case)
            return coll_enc_ul(r)
        if op == "mul":
            return coll_enc_ul(u * i)
        if op == "imul":
            r = u
            r *= i
            return coll_enc_ul(r)
        if op == "copy":
            return coll_enc_ul(u.copy())
        if op == "copy_dunder":
            return coll_enc_ul(coll_copy.copy(u))
        if op == "append":
            u.append(x)
            return coll_enc_ul(u)
        if op == "insert":
            u.insert(i, x)
            return coll_enc_ul(u)
        if op == "pop":
            r = u.pop(i) if "i" in case else u.pop()
            return [r, coll_enc_ul(u)]
        if op == "remove":
            u.remove(x)
            return coll_enc_ul(u)
        if op == "clear":
            u.clear()
            return coll_enc_ul(u)
        if op == "count":
            return u.count(x)
        if op == "index":
            return u.index(x, *[v for v in (case.get("st", 0), case.get("sp", 2**63 - 1))])
        if op == "reverse":
            u.reverse()
            return coll_enc_ul(u)
        if op == "sort":
            u.sort(reverse=case["r"])
            return coll_enc_ul(u)
        if op == "extend":
            u.extend(coll_opnd(case))
            return coll_enc_ul(u)
        if op in ("gen_iadd", "gen_extend", "gen_list_iadd"):
            it = coll_int_gen(case["o"], case["fail"])
            tgt = list(u.data) if op == "gen_list_iadd" else u
            try:
                if op == "gen_extend":
                    tgt.extend(it)
                else:
                    tgt += it
                exc = None
            except Exception as e:
                exc = [type(e).__name__, str(e)]
            return [list(tgt) if op == "gen_list_iadd" else coll_enc_ul(u), exc]
        if op == "gen_add":
            return coll_enc_ul(u + coll_int_gen(case["o"], case["fail"]))
        if op == "gen_radd":
            return coll_enc_ul(u.__radd__(coll_int_gen(case["o"], case["fail"])))
        if op == "init_sub":
            return coll_enc_ul(type(u)(coll_RevList(case["o"])))
        raise AssertionError(op)
    return py_result(body)


coll_ALPHA = "abAB12 -_\t\n"
coll_UNI = [233, 0x2003, 0x3000, 0x85, 0x2028, 0x1f600, 0xff21]
coll_NUMS = ["12", " 7 ", "-3", "+4", "abc", "", "1_0", "1__0", "_1", "5"]


def coll_cps(rng, ascii_only=True, n=8):
    out = [ord(rng.choice(coll_ALPHA)) for _ in range(rng.randint(0, n))]
    if not ascii_only and rng.random() < 0.3:
        out[rng.randint(0, len(out)):0] = [rng.choice(coll_UNI)]
    return out


def coll_sarg(rng, s=None):
    r = rng.random()
    if s is None:
        s = coll_cps(rng, n=3)
    if r < 0.45:
        return {"k": "str", "s": s}
    if r < 0.85:
        return {"k": "user", "s": s}
    return {"k": "int", "s": [53]}


def coll_arg_of(a):
    if a is None:
        return None
    if a["k"] == "int":
        return 5
    t = "".join(map(chr, a["s"]))
    return coll_collections.UserString(t) if a["k"] == "user" else t


def coll_gen_us(rng):
    case_ops = ["capitalize", "casefold", "lower", "upper", "swapcase", "title"]
    pred_ops = ["isalpha", "isalnum", "isascii", "isdecimal", "isdigit", "isidentifier", "islower",
                "isnumeric", "isprintable", "isspace", "istitle", "isupper"]
    op = rng.choice(case_ops + pred_ops + [
        "new", "str", "getnewargs", "add", "radd", "rmod", "replace_kw", "str_replace_kw",
        "dformat", "encode_none", "eq", "lt", "le", "gt", "ge", "center", "ljust", "rjust", "zfill",
        "expandtabs", "count", "find", "rfind", "index", "rindex", "startswith", "endswith",
        "removeprefix", "removesuffix", "partition", "rpartition", "replace", "split", "rsplit",
        "splitlines", "strip", "lstrip", "rstrip", "join", "contains", "mul", "getitem", "getslice",
        "format", "format_map", "mod", "translate", "encode", "len", "hash", "repr", "toInt",
        "toFloat", "toComplex"] * 2)
    ascii_only = op not in ("count", "find", "rfind", "index", "rindex", "partition", "rpartition",
                            "split", "rsplit", "splitlines", "strip", "lstrip", "rstrip",
                            "replace", "len", "getitem", "getslice", "startswith", "endswith")
    s = coll_cps(rng, ascii_only)
    case = {"fn": "coll.us", "op": op, "sub": rng.choice([0, 1]), "s": s,
            "plain": rng.random() < 0.15}
    sub = s[rng.randint(0, len(s)):][:rng.randint(0, 3)] if rng.random() < 0.6 else None
    if op in ("new", "add", "radd", "eq", "lt", "le", "gt", "ge", "count", "find", "rfind",
              "index", "rindex", "removeprefix", "removesuffix", "partition", "rpartition",
              "contains", "startswith", "endswith", "replace", "replace_kw", "str_replace_kw"):
        case["a"] = coll_sarg(rng, sub)
    if op in ("replace", "replace_kw", "str_replace_kw"):
        case["b"] = coll_sarg(rng)
        if rng.random() < 0.6:
            case["w"] = rng.choice([-1, 0, 1, 2])
    if op in ("replace_kw", "str_replace_kw"):
        case["kw"] = rng.choice(["count", "maxsplit", "n"])
        case["w"] = rng.choice([0, 1, 2])
    if op in ("startswith", "endswith") and rng.random() < 0.3:
        case["tup"] = [coll_cps(rng, n=2) for _ in range(rng.randint(0, 3))]
    if op in ("count", "find", "rfind", "index", "rindex", "startswith", "endswith"):
        coll_slice_args(rng, case, ("st", "en"))
    if op in ("split", "rsplit", "strip", "lstrip", "rstrip") and rng.random() < 0.7:
        a = coll_sarg(rng, sub)
        if op in ("split", "rsplit") and rng.random() < 0.1:
            a["s"] = []
        case["a"] = a
    if op in ("split", "rsplit"):
        case["w"] = rng.choice([-1, -1, 0, 1, 2, 2**63 - 1])
    if op in ("center", "ljust", "rjust", "zfill", "expandtabs", "mul", "getitem"):
        case["w"] = rng.choice([0, 1, 2, 3, 5, 9, 12, -1, -2])
    if op == "mul" and rng.random() < 0.2 and len(s) != 1:
        case["w"] = rng.choice([2**62, 2**63 - 1, 2**63, -2**63 - 1])
    if op == "getitem" and rng.random() < 0.2:
        case["w"] = rng.choice(coll_IDX)
    if op in ("center", "ljust", "rjust") and rng.random() < 0.6:
        case["fill"] = coll_sarg(rng, coll_cps(rng, n=2))
    if op == "splitlines":
        case["keep"] = rng.random() < 0.5
    if op == "join":
        case["items"] = [coll_sarg(rng) if rng.random() < 0.4 else {"k": "str", "s": coll_cps(rng, n=3)}
                         for _ in range(rng.randint(0, 4))]
    if op == "getslice":
        coll_slice_args(rng, case, ("st", "en", "se"))
    if op == "format":
        case["s"] = list(map(ord, rng.choice(["x", "{}", "{}{}", "{0}", "{1}", "", "{a}", "{0}{a}"])))
        case["args"] = coll_ints(rng)[:2]
        case["kw"] = [["a", rng.randint(0, 9)]] if rng.random() < 0.5 else []
    if op == "format_map":
        case["s"] = list(map(ord, rng.choice(["x", "{a}", "{b}", ""])))
        case["m"] = [["a", rng.randint(0, 9)]]
        case["miss"] = rng.random() < 0.4
    if op == "mod":
        case["mk"] = rng.choice(["tuple", "single", "mapping", "user"])
        if case["mk"] == "mapping":
            case["s"] = list(map(ord, rng.choice(["x", "%(a)s", "%(a)d", "%%", "%(b)s"])))
            case["m"] = [["a", rng.randint(0, 9)]]
        elif case["mk"] == "user":
            case["s"] = list(map(ord, rng.choice(["x", "%s", "x%sy"])))
            case["us"] = coll_cps(rng, n=3)
        else:
            case["s"] = list(map(ord, rng.choice(["x", "%d", "%s%d", "%%", "", "%d%%"])))
            case["args"] = coll_ints(rng)[:2]
            case["v"] = rng.randint(-5, 5)
    if op == "rmod":
        case["t"] = list(map(ord, rng.choice(["5", "%s", "x%sy", "%s%s"])))
    if op == "translate":
        case["tk"] = rng.choice(["dict", "dict", "list", "bad"])
        if case["tk"] == "list":
            case["t"] = [[i, rng.choice([None, 120, "yz", i])] for i in range(rng.randint(0, 100))]
        else:
            case["t"] = [[ord(rng.choice(coll_ALPHA)), rng.choice([None, 120, "yz", ""])]
                         for _ in range(rng.randint(0, 3))]
            case["t"] = list({p[0]: p for p in case["t"]}.values())
        case["n"] = rng.choice([1, 1, 1, 1, 0, 2])
    if op == "encode":
        case["enc"] = rng.choice(["utf-8", "ascii", "nope"])
        case["err"] = rng.choice(["strict", "ignore"])
    if op == "dformat":
        case["spec"] = rng.choice(["", ">5", "s"])
    if op in ("toInt", "toFloat", "toComplex"):
        case["s"] = list(map(ord, rng.choice(coll_NUMS)))
    return case


def coll_enc_us(r):
    if isinstance(r, coll_collections.UserString):
        return {"us": [type(r).__name__, list(map(ord, r.data))]}
    if isinstance(r, bool) or isinstance(r, int):
        return r
    if isinstance(r, str):
        return {"str": list(map(ord, r))}
    if isinstance(r, bytes):
        return {"bytes": list(r)}
    if isinstance(r, list):
        return {"strs": [list(map(ord, x)) for x in r]}
    if isinstance(r, tuple):
        return {"tup": [list(map(ord, x)) for x in r]}
    raise AssertionError(type(r))


class coll_FMiss(dict):
    def __missing__(self, key):
        return -1


class coll_BadTable:
    def __getitem__(self, k):
        raise ValueError("t")


def coll_run_us(case):
    op = case["op"]
    t = "".join(map(chr, case["s"]))
    plain = case.get("plain") and op not in ("new", "str", "getnewargs", "add", "radd", "rmod",
                                             "replace_kw", "str_replace_kw", "dformat",
                                             "encode_none")
    u = t if plain else (coll_USPlain if case["sub"] else coll_collections.UserString)(t)
    a = coll_arg_of(case.get("a"))
    w = case.get("w")
    fill = coll_arg_of(case.get("fill"))
    st, en = case.get("st"), case.get("en")
    pad = () if "fill" not in case else (fill,)

    def se():
        # defaults when absent; None is accepted and means the same
        return (0 if st is None else st, 2**63 - 1 if en is None else en)

    def affix():
        if "tup" in case:
            return tuple("".join(map(chr, p)) for p in case["tup"])
        return a

    def body():
        if op == "new":
            return coll_enc_us(type(u)(a))
        if op == "str":
            return coll_enc_us(str(u))
        if op == "getnewargs":
            return coll_enc_us(u.__getnewargs__()[0])
        if op == "add":
            return coll_enc_us(u + a)
        if op == "radd":
            return coll_enc_us(u.__radd__(a))
        if op == "rmod":
            return coll_enc_us(5 % u if case["t"] == [53] else u.__rmod__("".join(map(chr, case["t"]))))
        if op == "replace_kw":
            return coll_enc_us(u.replace(a, coll_arg_of(case["b"]), **{case["kw"]: w}))
        if op == "str_replace_kw":
            return coll_enc_us(t.replace(a, coll_arg_of(case["b"]), **{case["kw"]: w}))
        if op == "dformat":
            return coll_enc_us(format(u, case["spec"]))
        if op == "encode_none":
            return coll_enc_us(u.encode(None, None))
        if op in ("eq", "lt", "le", "gt", "ge"):
            return {"eq": lambda: u == a, "lt": lambda: u < a, "le": lambda: u <= a,
                    "gt": lambda: u > a, "ge": lambda: u >= a}[op]()
        if op in ("capitalize", "casefold", "lower", "upper", "swapcase", "title", "isalpha",
                  "isalnum", "isascii", "isdecimal", "isdigit", "isidentifier", "islower",
                  "isnumeric", "isprintable", "isspace", "istitle", "isupper"):
            return coll_enc_us(getattr(u, op)())
        if op in ("center", "ljust", "rjust"):
            return coll_enc_us(getattr(u, op)(w, *pad))
        if op in ("zfill", "expandtabs"):
            return coll_enc_us(getattr(u, op)(w))
        if op in ("count", "find", "rfind", "index", "rindex"):
            return coll_enc_us(getattr(u, op)(a, *se()))
        if op in ("startswith", "endswith"):
            return coll_enc_us(getattr(u, op)(affix(), *se()))
        if op in ("removeprefix", "removesuffix", "partition", "rpartition"):
            return coll_enc_us(getattr(u, op)(a))
        if op == "replace":
            return coll_enc_us(u.replace(a, coll_arg_of(case["b"]), -1 if w is None else w))
        if op in ("split", "rsplit"):
            return coll_enc_us(getattr(u, op)(a, w))
        if op == "splitlines":
            return coll_enc_us(u.splitlines(case["keep"]))
        if op in ("strip", "lstrip", "rstrip"):
            return coll_enc_us(getattr(u, op)(a))
        if op == "join":
            return coll_enc_us(u.join([coll_arg_of(x) for x in case["items"]]))
        if op == "contains":
            return a in u
        if op == "mul":
            return coll_enc_us(u * w)
        if op == "getitem":
            return coll_enc_us(u[w])
        if op == "getslice":
            return coll_enc_us(u[slice(st, en, case.get("se"))])
        if op == "format":
            return coll_enc_us(u.format(*case["args"], **coll_d(case["kw"])))
        if op == "format_map":
            m = (coll_FMiss if case["miss"] else dict)(coll_d(case["m"]))
            return coll_enc_us(u.format_map(m))
        if op == "mod":
            mk = case["mk"]
            if mk == "tuple":
                return coll_enc_us(u % tuple(case["args"]))
            if mk == "single":
                return coll_enc_us(u % case["v"])
            if mk == "mapping":
                return coll_enc_us(u % coll_d(case["m"]))
            return coll_enc_us(u % coll_collections.UserString("".join(map(chr, case["us"]))))
        if op == "translate":
            tk = case["tk"]
            if tk == "list":
                table = [v for _, v in case["t"]]
            elif tk == "bad":
                table = coll_BadTable()
            else:
                table = coll_d(case["t"])
            return coll_enc_us(u.translate(*([table] * case["n"])))
        if op == "encode":
            return coll_enc_us(u.encode(case["enc"], case["err"]))
        if op == "len":
            return len(u)
        if op == "hash":
            return 0 if hash(u) == hash(t) else 1
        if op == "repr":
            return {"text": repr(u)}
        if op == "toInt":
            return int(u)
        if op == "toFloat":
            return {"text": repr(float(u))}
        if op == "toComplex":
            return {"text": repr(complex(u))}
        raise AssertionError(op)
    r = py_result(body)
    return r


coll_NT_NAMES = ["a", "b", "x", "y", "z", "count", "index", "match", "type", "self", "_a", "__b",
                 "_0", "_1", "class", "def", "None", "True", "1x", "a b", "", "a-b", "a_b",
                 "ﬁ", "fi", "a＿b", "\U0001d41d\U0001d41e\U0001d41f",
                 "\U0001d40d\U0001d428\U0001d427\U0001d41e", "\U0001d41a"]
coll_NT_GOOD = ["a", "b", "x", "y", "z", "count", "match", "self", "c1", "a_b"]
coll_NT_TYPES = ["T", "Point", "_T", "ﬁ", "class", "1x", "", "a b", "None"]
coll_NT_FSTRS = ["a b", "a,b", "a, b c", "  ", "", "a\tb\nc", "x,,y", "a a", "a,_b"]


def coll_gen_nt(rng):
    op = rng.choice(["create", "create", "call", "make", "replace", "repr", "asdict", "getnewargs",
                     "getattr", "roundtrip"])
    case = {"fn": "coll.nt", "op": op, "rename": rng.random() < 0.4}
    case["typename"] = "T" if op != "create" or rng.random() < 0.7 else rng.choice(coll_NT_TYPES)
    pool = coll_NT_NAMES if rng.random() < 0.5 else coll_NT_GOOD
    if rng.random() < 0.15:
        case["fstr"] = rng.choice(coll_NT_FSTRS)
        names = case["fstr"].replace(",", " ").split()
    else:
        names = [rng.choice(pool) for _ in range(rng.randint(0, 5))]
        if rng.random() < 0.6:
            names = list(dict.fromkeys(names))
        case["fields"] = names
    if rng.random() < 0.4:
        case["defaults"] = [rng.randint(0, 9) for _ in range(rng.randint(0, len(names) + 1))]
    n = len(names)
    if op == "call":
        case["vals"] = [rng.randint(0, 9) for _ in range(rng.randint(0, n + 1))]
        case["kw"] = [[rng.choice(names + ["q"]), rng.randint(0, 9)]
                      for _ in range(rng.randint(0, 2))]
        case["kw"] = [[k, v] for k, v in dict(case["kw"]).items()]
    else:
        case["vals"] = [rng.randint(0, 9) for _ in range(n)]
    if op == "make" and rng.random() < 0.3:
        case["vals"].append(1)
    if op == "replace":
        case["kw"] = [[rng.choice(names + ["q", "r"]), rng.randint(0, 9)]
                      for _ in range(rng.randint(0, 2))]
        case["kw"] = [[k, v] for k, v in dict(case["kw"]).items()]
    if op == "getattr":
        case["name"] = rng.choice(names + ["nope"])
    return case


def coll_run_nt(case):
    op = case["op"]
    fields = case.get("fstr", case.get("fields"))
    defaults = case.get("defaults")

    def body():
        T = coll_collections.namedtuple(case["typename"], fields, rename=case["rename"],
                                        defaults=defaults, module="m")
        assert T.__match_args__ == T._fields
        if op == "create":
            d = T.__new__.__defaults__
            return {"typename": T.__name__, "fields": list(T._fields),
                    "args": list(T.__new__.__code__.co_varnames[1:]),
                    "defaults": list(d) if d else [],
                    "fd": [[k, v] for k, v in T._field_defaults.items()], "doc": T.__doc__,
                    "newdoc": T.__new__.__doc__}
        vals = case["vals"]
        if op == "call":
            return list(T(*vals, **coll_d(case["kw"])))
        if op == "make":
            return list(T._make(vals))
        p = T._make(vals)
        if op == "replace":
            return list(p._replace(**coll_d(case["kw"])))
        if op == "repr":
            return repr(p)
        if op == "asdict":
            return coll_enc(p._asdict())
        if op == "getnewargs":
            return list(p.__getnewargs__())
        if op == "getattr":
            return getattr(p, case["name"])
        if op == "roundtrip":
            return list(T(**p._asdict()))
        raise AssertionError(op)
    return py_result(body)


coll_GENS = [coll_gen_ctr, coll_gen_cm, coll_gen_ud, coll_gen_ul, coll_gen_us, coll_gen_nt]
coll_RUNS = {"coll.ctr": coll_run_ctr, "coll.cm": coll_run_cm, "coll.ud": coll_run_ud,
             "coll.ul": coll_run_ul, "coll.us": coll_run_us, "coll.nt": coll_run_nt}


def coll_gen(rng):
    return rng.choice(coll_GENS)(rng)


def coll_run(case):
    return coll_RUNS[case["fn"]](case)
# ====== END AREA coll ======

# ====== BEGIN AREA collabc (Lib/_collections_abc.py, Lib/collections/abc.py) ======
# Everything for this area stays between these two markers; prefix top-level names with collabc_.
import _collections_abc as collabc_A  # noqa: E402
from _collections_abc import _check_methods as collabc_check_methods  # noqa: E402

collabc_VALS = [0, 1, 2, 3, -1, 5, 7, 2**64, -2**63]


class collabc_E:
    """An int element whose __eq__ raises for the poisoned value, on the left."""
    bad = None
    __slots__ = ("v",)

    def __init__(self, v):
        self.v = v

    def __eq__(self, o):
        if self.v == collabc_E.bad:
            raise ValueError("bad")
        return self.v == (o.v if isinstance(o, collabc_E) else o)

    def __hash__(self):
        return hash(self.v)


class collabc_Seq(collabc_A.Sequence):
    def __init__(self, xs, fail, badlen=False):
        self.xs, self.fail, self.badlen = xs, fail, badlen

    def __getitem__(self, i):
        if i == self.fail:
            raise ValueError("fail")
        return self.xs[i]

    def __len__(self):
        if self.badlen:
            raise ValueError("len")
        return len(self.xs)


collabc_LENEXC = {"TypeError": TypeError, "ValueError": ValueError}


class collabc_MSeq(collabc_A.MutableSequence):
    def __init__(self, xs, fail, lenexc=None):
        self.xs, self.fail, self.lenexc = list(xs), fail, lenexc

    def __getitem__(self, i):
        if i == self.fail:
            raise ValueError("fail")
        return self.xs[i]

    def __setitem__(self, i, v):
        self.xs[i] = v

    def __delitem__(self, i):
        del self.xs[i]

    def __len__(self):
        if self.lenexc:
            raise collabc_LENEXC[self.lenexc]("len")
        return len(self.xs)

    def insert(self, i, v):
        self.xs.insert(i, v)


def collabc_tail(xs):
    """An iterator that raises after its items."""
    yield from xs
    raise ValueError("itail")


class collabc_Set(collabc_A.MutableSet):
    bad = None
    uh = None
    itail = False

    def __init__(self, it=()):
        self.xs = []
        for x in it:
            if collabc_Set.uh is not None and x == collabc_Set.uh:
                raise TypeError("unhashable")
            if x not in self.xs:
                self.xs.append(x)

    def __contains__(self, x):
        if x == collabc_Set.bad:
            raise ValueError("bad")
        return x in self.xs

    def __iter__(self):
        return collabc_tail(list(self.xs)) if self.itail else iter(list(self.xs))

    def __len__(self):
        if getattr(self, "badlen", False):
            raise ValueError("len")
        return len(self.xs)

    def add(self, x):
        if x not in self.xs:
            self.xs.append(x)

    def discard(self, x):
        if x in self.xs:
            self.xs.remove(x)

    __hash__ = None


class collabc_GI:
    """Iterable through __getitem__ only: not an Iterable to the ABC."""

    def __init__(self, xs, tail):
        self.xs, self.tail = xs, tail

    def __getitem__(self, i):
        if i < len(self.xs):
            return self.xs[i]
        if self.tail:
            raise ValueError("itail")
        raise IndexError


class collabc_R:
    """Not iterable, with a reflected subtraction that gives a set."""

    def __init__(self, xs):
        self.xs = xs

    def __rsub__(self, o):
        s = collabc_Set()
        s.xs = list(self.xs)
        return s


class collabc_Map(collabc_A.MutableMapping):
    itail = False

    def __init__(self, items, fail, failkey=False):
        self.d, self.fail, self.failkey = dict(items), fail, failkey

    def __getitem__(self, k):
        if k == self.fail:
            if self.failkey:
                raise KeyError(k)
            raise ValueError("fail")
        return self.d[k]

    def __setitem__(self, k, v):
        self.d[k] = v

    def __delitem__(self, k):
        del self.d[k]

    def __iter__(self):
        return collabc_tail(list(self.d)) if self.itail else iter(list(self.d))

    def __len__(self):
        return len(self.d)


class collabc_MapO(collabc_Map):
    """A mapping whose own __contains__ differs from Mapping.__contains__."""

    def __contains__(self, k):
        return k % 2 == 0


class collabc_KeysLike:
    def __init__(self, pairs, fail, tail):
        self.d, self.fail, self.tail = dict(pairs), fail, tail

    def keys(self):
        return collabc_tail(list(self.d)) if self.tail else iter(list(self.d))

    def __getitem__(self, k):
        if k == self.fail:
            raise ValueError("fail")
        return self.d[k]


class collabc_BadAttr:
    def __getattr__(self, n):
        raise ValueError("ga")


class collabc_HSet(collabc_A.Set):
    """A Set that reports the given hashes, for Set._hash; None is an unhashable element."""

    def __init__(self, hashes, badlen=False):
        self.hs = [[0] if h is None else collabc_H(h) for h in hashes]
        self.badlen = badlen

    def __contains__(self, x):
        return x in self.hs

    def __iter__(self):
        return iter(self.hs)

    def __len__(self):
        if self.badlen:
            raise ValueError("len")
        return len(self.hs)


class collabc_H:
    def __init__(self, h):
        self.h = h

    def __hash__(self):
        return self.h


class collabc_Scripted:
    """Play a script of steps: each resumption consumes one."""

    def __init__(self, script):
        self.script = list(script)

    def step(self):
        if not self.script:
            return None
        k, v = self.script.pop(0)
        if k == "y":
            return v
        if k == "r":
            raise self.stop(v)
        if k == "exit":
            raise GeneratorExit
        raise ValueError(str(v))


def collabc_scripted(base, stop_exc, async_=False):
    class G(base):
        def __init__(self, script):
            self.s = collabc_Scripted(script)
            self.s.stop = stop_exc

        if async_:
            async def asend(self, v):
                if not self.s.script:
                    raise StopAsyncIteration(0)
                return self.s.step()

            async def athrow(self, typ, val=None, tb=None):
                if not self.s.script:
                    raise typ
                return self.s.step()

            def __aiter__(self):
                return self
        else:
            def send(self, v):
                if not self.s.script:
                    raise stop_exc(0)
                return self.s.step()

            def throw(self, typ, val=None, tb=None):
                if not self.s.script:
                    raise typ
                return self.s.step()

            def __await__(self):
                return iter(())
    return G


collabc_GenC = collabc_scripted(collabc_A.Generator, StopIteration)
collabc_CoroC = collabc_scripted(collabc_A.Coroutine, StopIteration)
collabc_AGenC = collabc_scripted(collabc_A.AsyncGenerator, StopAsyncIteration, async_=True)


def collabc_bytestring():
    """`ByteString` with the warning of the module's `__getattr__` out of the way: only the first read in a process gives it."""
    import warnings
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        return collabc_A.ByteString


def collabc_drive(coro):
    """Run a coroutine that never suspends."""
    try:
        coro.send(None)
    except StopIteration as e:
        return e.value
    raise RuntimeError("suspended")


collabc_HOOKS = ["Hashable", "Awaitable", "Coroutine", "AsyncIterable", "AsyncIterator",
                 "AsyncGenerator", "Iterable", "Iterator", "Reversible", "Generator", "Sized",
                 "Container", "Collection", "Buffer", "Callable"]
collabc_METHODS = ["__hash__", "__await__", "send", "throw", "close", "__aiter__", "__anext__",
                   "asend", "athrow", "aclose", "__iter__", "__next__", "__reversed__", "__len__",
                   "__contains__", "__buffer__", "__call__", "__eq__", "other"]
collabc_STUBS = {
    "Awaitable.__await__": lambda: len(list(collabc_A.Awaitable.__await__(None))),
    "Iterable.__iter__": lambda: len(list(collabc_A.Iterable.__iter__(None))),
    "Reversible.__reversed__": lambda: len(list(collabc_A.Reversible.__reversed__(None))),
    "Iterator.__next__": lambda: collabc_A.Iterator.__next__(None),
    "Generator.send": lambda: collabc_A.Generator.send(None, 1),
    "Coroutine.send": lambda: collabc_A.Coroutine.send(None, 1),
    "AsyncIterable.__aiter__": lambda: collabc_A.AsyncIterable.__aiter__(None),
    "Buffer.__buffer__": lambda: collabc_A.Buffer.__buffer__(None, 0),
    "MutableSet.add": lambda: collabc_A.MutableSet.add(None, 1),
    "MutableSet.discard": lambda: collabc_A.MutableSet.discard(None, 1),
    "Mapping.__getitem__": lambda: collabc_A.Mapping.__getitem__(None, 1),
    "MutableMapping.__setitem__": lambda: collabc_A.MutableMapping.__setitem__(None, 1, 2),
    "MutableMapping.__delitem__": lambda: collabc_A.MutableMapping.__delitem__(None, 1),
    "Sequence.__getitem__": lambda: collabc_A.Sequence.__getitem__(None, 1),
    "MutableSequence.__setitem__": lambda: collabc_A.MutableSequence.__setitem__(None, 1, 2),
    "MutableSequence.__delitem__": lambda: collabc_A.MutableSequence.__delitem__(None, 1),
    "MutableSequence.insert": lambda: collabc_A.MutableSequence.insert(None, 1, 2),
}


def collabc_rand_class(rng):
    C = object
    for depth in range(rng.randrange(0, 4)):
        d = {}
        for m in rng.sample(collabc_METHODS, rng.randrange(0, 6)):
            d[m] = None if rng.random() < 0.25 else (lambda self: 0)
        C = type(f"C{depth}", (C,), d)
    return C


def collabc_full_class(rng, x):
    """A class defining exactly the methods of hook `x`, or all but one, so that True answers are frequent."""
    ms = list(collabc_A.__dict__[x].__subclasshook__.__func__.__code__.co_consts)
    ms = [m for m in ms if isinstance(m, str) and m.startswith(("_", "s", "t", "c", "a")) and m != x]
    if ms and rng.random() < .4:
        ms.remove(rng.choice(ms))
    d = {m: (None if rng.random() < .1 else (lambda self: 0)) for m in ms}
    return type("F", (object,), d)


def collabc_mro(C):
    return [[[k, v is None] for k, v in B.__dict__.items() if isinstance(k, str)]
            for B in C.__mro__]


def collabc_list(rng, n=7):
    return [rng.choice(collabc_VALS) if rng.random() < 0.3 else rng.randrange(-3, 6)
            for _ in range(rng.randrange(0, n))]


def collabc_uniq(xs):
    return list(dict.fromkeys(xs))


def collabc_opt(rng, xs):
    return None if rng.random() < 0.7 or not xs else rng.choice(xs)


collabc_ASYNC_STUBS = {
    "AsyncIterator.__anext__": lambda: collabc_A.AsyncIterator.__anext__(None),
    "AsyncGenerator.asend": lambda: collabc_A.AsyncGenerator.asend(None, 1),
}


def collabc_stub(name):
    if name in collabc_ASYNC_STUBS:
        c = py_result(collabc_ASYNC_STUBS[name])
        if "exc" in c:
            return {"callexc": c}
        return py_result(lambda: collabc_drive(c["ok"]))
    return py_result(collabc_STUBS[name])


class collabc_BadRepr(dict):
    def __repr__(self):
        raise ValueError("repr")


class collabc_NotStr(dict):
    def __repr__(self):
        return 5


collabc_TOBJ = [{"k": "cls", "n": "ValueError"}, {"k": "cls", "n": "KeyError"}, {"k": "cls_ude"},
                {"k": "cls_bad"}, {"k": "inst", "n": "ValueError"}, {"k": "func"}, {"k": "wtb"},
                {"k": "other"}]
collabc_CITEMS = ["int", "str", "bool", ["int"], {"t": ["int", "str"]}, "...", "~P"]


def collabc_gen(rng):
    r = rng.randrange(0, 25)
    xs = collabc_list(rng)
    idx = rng.choice(list(range(-len(xs) - 2, len(xs) + 3)) + [0, 1, -1])
    fail = None if rng.random() < 0.7 else rng.randrange(-2, len(xs) + 2)
    bad = None if rng.random() < 0.8 or not xs else rng.choice(xs)
    v = rng.choice(xs) if xs and rng.random() < 0.6 else rng.randrange(-3, 6)
    if r == 0:
        return {"fn": "collabc.check_methods", "mro": collabc_mro(collabc_rand_class(rng)),
                "methods": rng.sample(collabc_METHODS, rng.randrange(0, 4))}
    if r == 1:
        x = rng.choice(collabc_HOOKS)
        C = collabc_full_class(rng, x) if rng.random() < .5 else collabc_rand_class(rng)
        return {"fn": "collabc.hook", "mro": collabc_mro(C),
                "x": x, "cls": x if rng.random() < .7 else rng.choice(collabc_HOOKS)}
    if r == 2:
        if rng.random() < .5:
            return {"fn": "collabc.stub", "name": rng.choice(list(collabc_STUBS) + list(collabc_ASYNC_STUBS))}
        k = rng.randrange(0, 4)
        if k == 0:
            return {"fn": "collabc.list_remove", "xs": xs, "v": v, "bad": bad}
        act = rng.choice(["ignore", "always", "error"])
        if k == 1:
            return {"fn": "collabc.bytestring_new", "act": act,
                    "name": rng.choice(["ByteString", "Other", "bytestring"])}
        if k == 2:
            return {"fn": "collabc.bytestring_check", "answer": rng.random() < .5, "act": act}
        if rng.random() < .5:
            ys = [None if rng.random() < .15 else x for x in xs]
            return {"fn": "collabc.from_iterable", "kind": rng.choice(["set", "keys", "items"]), "xs": ys,
                    "tail": rng.random() < .2, "uh": collabc_opt(rng, xs)}
        return {"fn": "collabc.view_repr", "cls": rng.choice(["KeysView", "ItemsView", "ValuesView"]),
                "kind": rng.choice(["ok", "raise", "notstr"])}
    if r == 3:
        return {"fn": "collabc.throw", "typ": rng.choice(collabc_TOBJ),
                "val": None if rng.random() < .5 else rng.choice(collabc_TOBJ),
                "tb": rng.choice(["none", "tb", "bad"])}
    if r in (4, 5):
        script = [rng.choice([["y", 1], ["r", 7], ["exit", 0], ["e", 3]])
                  for _ in range(rng.randrange(0, 3))]
        if r == 4:
            return {"fn": "collabc.gen_close", "script": script,
                    "kind": rng.choice(["gen", "coro", "agen"])}
        return {"fn": rng.choice(["collabc.gen_next", "collabc.agen_next", "collabc.builtin_close",
                                  "collabc.builtin_aclose"]),
                "script": script[:1], "kind": rng.choice(["gen", "coro"])}
    if r == 6:
        if rng.random() < .35:
            a, b = rng.choice(["int", "str"]), rng.choice(["bool", "float"])
            shape = rng.choice(["tv", "param", "listlist", "pseq"])
            new = {"tv": [a, "int", b], "param": [{"t": [a, b]}, "int"], "listlist": [[a], [b]],
                   "pseq": [{"t": [a]}, [b]]}[shape]
            return {"fn": "collabc.callable_getitem", "shape": shape, "a": a, "b": b, "new": new}
        k = rng.randrange(0, 8)
        items = [rng.choice(collabc_CITEMS[:5]) for _ in range(rng.randrange(0, 4))]
        a = [items, {"t": items}, "...", "~P", "C", "int", "notpair",
             [rng.choice([["int"], ["int", "str"], "~P", "..."])]][k]
        return {"fn": "collabc.callable_new", "a": a, "r": rng.choice(["float", "...", ["int"]])}
    if r == 7:
        return {"fn": "collabc.seq_iter", "xs": xs, "fail": fail}
    if r == 8:
        return {"fn": "collabc.seq_reversed", "xs": xs, "fail": fail, "badlen": rng.random() < .15}
    if r in (9, 10):
        return {"fn": "collabc." + ("seq_contains" if r == 9 else "seq_count"), "xs": xs,
                "fail": fail, "bad": bad, "v": v}
    if r == 11:
        n = len(xs)
        start = rng.choice([0, 1, -1, n, -n, n + 1, -n - 1, n // 2, -2**70, 2**70])
        stop = rng.choice([None, 0, 1, -1, n, -n, n + 1, -n - 1, n // 2, -2**70, 2**70])
        return {"fn": rng.choice(["collabc.seq_index", "collabc.list_index"]), "xs": xs,
                "fail": fail, "bad": bad, "v": v, "start": start, "stop": stop,
                "badlen": rng.random() < .15}
    if r == 12:
        return {"fn": "collabc.mseq_append", "xs": xs, "v": v,
                "lenexc": None if rng.random() < .8 else rng.choice(["TypeError", "ValueError"])}
    if r == 13:
        return {"fn": "collabc.mseq_pop", "xs": xs, "i": idx, "fail": fail}
    if r == 14:
        return {"fn": rng.choice(["collabc.mseq_clear", "collabc.mseq_reverse"]), "xs": xs,
                "fail": fail}
    if r == 15:
        return {"fn": "collabc.mseq_extend", "xs": xs, "fail": fail,
                "vs": None if rng.random() < .3 else collabc_list(rng, 4),
                "vtail": rng.random() < .2, "iadd": rng.random() < .3,
                "lenexc": None if rng.random() < .7 else rng.choice(["TypeError", "ValueError"])}
    if r == 16:
        if rng.random() < .3:
            return {"fn": "collabc.module_getattr", "name": rng.choice(["ByteString", "ByteString", "Other"]),
                    "act": rng.choice(["ignore", "always", "error"])}
        return {"fn": "collabc.mseq_remove", "xs": xs, "v": v, "fail": fail, "bad": bad}
    a, b = collabc_uniq(xs), collabc_list(rng)
    kind = rng.choice(["set", "iter", "gi", "other", "rsub"])
    if kind in ("set", "rsub"):
        b = collabc_uniq(b)
    uh = None if rng.random() < .75 or not (a or b) else rng.choice(a + b)
    if r == 17:
        return {"fn": "collabc.set_cmp", "op": rng.choice(["le", "lt", "ge", "gt", "eq"]), "xs": a,
                "other": b, "okind": kind, "bad": bad, "badlen": rng.random() < .1, **collabc_tails(rng)}
    if r == 18:
        return {"fn": "collabc.set_op", "op": rng.choice(["and", "or", "sub", "rsub", "xor"]),
                "xs": a, "other": b, "okind": kind, "bad": bad, "uh": uh, **collabc_tails(rng)}
    if r == 19:
        return {"fn": "collabc.set_isdisjoint", "xs": a, "other": b, "okind": kind, "bad": bad,
                **collabc_tails(rng)}
    if r == 20:
        hs = rng.sample([0, 1, -1, -2, 2**61 - 1, -2**63, 2**63 - 1, 5, 2**32, 123456789, -77,
                         rng.randrange(-2**63, 2**63)], rng.randrange(0, 8))
        if rng.random() < .5:
            if hs and rng.random() < .3:
                hs[rng.randrange(len(hs))] = None
            return {"fn": "collabc.set_hash", "hashes": hs, "badlen": rng.random() < .1}
        return {"fn": "collabc.frozenset_hash", "hashes": [h for h in hs if h != -1],
                "nulls": rng.randrange(0, 9), "dummies": rng.randrange(0, 3)}
    if r == 21:
        return {"fn": "collabc.mset_op", "op": rng.choice(["ior", "iand", "ixor", "isub", "clear",
                                                           "remove", "pop"]),
                "xs": a, "other": b, "okind": kind, "bad": bad, "uh": uh, "v": v,
                "selfit": rng.random() < .2, **collabc_tails(rng)}
    d = [[k, rng.randrange(-2, 4)] for k in collabc_uniq(xs)]
    k = rng.choice(xs) if xs and rng.random() < .6 else rng.randrange(-3, 6)
    failk = None if rng.random() < .75 else rng.randrange(-3, 6)
    if r == 22:
        d2 = d if rng.random() < .5 else [[k2, rng.randrange(-2, 4)] for k2 in collabc_uniq(collabc_list(rng))]
        return {"fn": "collabc.map_op", "op": rng.choice(["get", "contains", "items", "values",
                                                          "valuecontains", "keyscontain",
                                                          "itemcontains", "eq"]),
                "d": d, "d2": d2, "k": k, "default": 99, "fail": failk, "failkey": rng.random() < .3,
                "bad": bad, "v": rng.randrange(-2, 4), "ovr": rng.random() < .3,
                "ikind": rng.choice(["tuple", "list", "short", "empty", "long", "dict3", "str3", "iter3",
                                     "sublist3", "gen2t", "gen1t", "none"]),
                "who": rng.choice(["abc", "dict"]), **collabc_tails(rng)}
    other = [[rng.randrange(-3, 6), rng.randrange(-2, 4)] for _ in range(rng.randrange(0, 4))]
    op = rng.choice(["pop", "popd", "popitem", "clear", "setdefault", "update_map", "update_keys",
                     "update_pairs", "update_hasattr"])
    if op in ("update_map", "update_keys"):
        other = [[k2, v2] for k2, v2 in dict(map(tuple, other)).items()]
    items = [rng.choice([p, p, "short", "long", "none", "str3", "empty"]) for p in other]
    return {"fn": "collabc.mmap_op", "op": op, "d": d, "k": k, "default": 99, "fail": failk,
            "ofail": None if rng.random() < .7 else rng.randrange(-3, 6),
            "kw": [], "other": other, "items": items, **collabc_tails(rng)}


def collabc_tails(rng):
    return {"selftail": rng.random() < .2, "otail": rng.random() < .2}


def collabc_self(cls, *args, tail):
    s = cls(*args)
    s.itail = tail
    return s


def collabc_operand(case):
    k = case["okind"]
    if k == "set":
        return collabc_self(collabc_Set, case["other"], tail=case["otail"])
    if k == "iter":
        return collabc_tail(case["other"]) if case["otail"] else iter(case["other"])
    if k == "gi":
        return collabc_GI(case["other"], case["otail"])
    if k == "rsub":
        return collabc_R(case["other"])
    return 5


def collabc_ret(v):
    return "NotImplemented" if v is NotImplemented else {"val": v}


def collabc_setret(v):
    return "NotImplemented" if v is NotImplemented else {"val": list(v.xs)}


def collabc_run_gen(cls, script, f):
    g = cls(script)
    r = py_result(lambda: f(g))
    return {"ok": {"r": r, "left": len(g.s.script)}}


def collabc_run(case):
    fn = case["fn"].split(".")[1]
    bad = case.get("bad")
    fail = case.get("fail")
    collabc_E.bad = bad
    collabc_Set.bad = bad
    collabc_Set.uh = None
    if fn == "check_methods":
        return {"ok": collabc_ret(collabc_check_methods(collabc_fake(case["mro"]),
                                                        *case["methods"]))}
    if fn == "hook":
        cls = getattr(collabc_A, case["cls"])
        hook = getattr(collabc_A, case["x"]).__dict__["__subclasshook__"].__func__
        return collabc_hook(cls, hook, case["mro"])
    if fn == "stub":
        return collabc_stub(case["name"])
    if fn == "agen_next":
        return collabc_agen_next([tuple(s) for s in case["script"]])
    if fn == "from_iterable":
        return collabc_from_iterable(case)
    if fn == "throw":
        return collabc_throw(case)
    if fn == "gen_close":
        script = [tuple(s) for s in case["script"]]
        if case["kind"] == "gen":
            return collabc_run_gen(collabc_GenC, script, lambda g: g.close())
        if case["kind"] == "coro":
            return collabc_run_gen(collabc_CoroC, script, lambda g: g.close())
        return collabc_run_gen(collabc_AGenC, script, lambda g: collabc_drive(g.aclose()))
    if fn == "builtin_close":
        return collabc_builtin_close([tuple(s) for s in case["script"]], case["kind"])
    if fn == "builtin_aclose":
        return collabc_builtin_aclose([tuple(s) for s in case["script"]])
    if fn == "callable_getitem":
        return collabc_getitem(case)
    if fn == "gen_next":
        return collabc_gen_next([tuple(s) for s in case["script"]])
    if fn == "callable_new":
        return collabc_callable(case)
    xs = [collabc_E(x) for x in case.get("xs", [])]
    raw = case.get("xs", [])
    if fn == "seq_iter":
        s = collabc_Seq(raw, fail)
        return py_result(lambda: list(iter(s)))
    if fn == "seq_reversed":
        s = collabc_Seq(raw, fail, case["badlen"])
        return py_result(lambda: list(reversed(s)))
    if fn == "seq_contains":
        s = collabc_Seq(xs, fail)
        return py_result(lambda: collabc_E(case["v"]) in s)
    if fn == "seq_count":
        s = collabc_Seq(xs, fail)
        return py_result(lambda: s.count(collabc_E(case["v"])))
    if fn == "seq_index":
        s = collabc_Seq(xs, fail, case["badlen"])
        return py_result(lambda: s.index(collabc_E(case["v"]), case["start"], case["stop"]))
    if fn == "list_index":
        def f():
            stop = case["stop"] if case["stop"] is not None else sys.maxsize
            try:
                return raw.index(case["v"], case["start"], stop)
            except ValueError:
                return None
        return collabc_plain(f)
    if fn == "mseq_append":
        s = collabc_MSeq(raw, None, case["lenexc"])
        return py_result(lambda: (s.append(case["v"]), s.xs)[1])
    if fn == "mseq_pop":
        s = collabc_MSeq(raw, fail)
        return py_result(lambda: [s.pop(case["i"]), s.xs])
    if fn == "mseq_clear":
        s = collabc_MSeq(raw, fail)
        return py_result(lambda: (s.clear(), s.xs)[1])
    if fn == "mseq_reverse":
        s = collabc_MSeq(raw, fail)
        return py_result(lambda: (s.reverse(), s.xs)[1])
    if fn == "mseq_extend":
        s = collabc_MSeq(raw, fail, case["lenexc"])
        vs = case["vs"]
        vals = s if vs is None else (collabc_tail(vs) if case["vtail"] else iter(vs))
        if case["iadd"]:
            return py_result(lambda: s.__iadd__(vals).xs)
        return py_result(lambda: (s.extend(vals), s.xs)[1])
    if fn == "mseq_remove":
        s = collabc_MSeq(xs, fail)

        def f():
            s.remove(collabc_E(case["v"]))
            return [e.v for e in s.xs]
        return py_result(f)
    if fn == "list_remove":
        ys = list(xs)

        def f():
            try:
                ys.remove(collabc_E(case["v"]))
            except ValueError as e:
                if str(e) != "list.remove(x): x not in list":
                    raise
                return None
            return [e.v for e in ys]
        return py_result(f)
    if fn == "module_getattr":
        import warnings
        g, B = vars(collabc_A), collabc_bytestring()
        del g["ByteString"]
        with warnings.catch_warnings(record=True) as w:
            warnings.simplefilter(case["act"])
            r = py_result(lambda: None if getattr(collabc_A, case["name"]) is B else "other")
        loaded = "ByteString" in g
        g["ByteString"] = B
        return {"ok": [[[x.category.__name__, str(x.message)] for x in w], loaded, r]}
    if fn in ("bytestring_new", "bytestring_check"):
        import warnings
        B = collabc_bytestring()
        with warnings.catch_warnings(record=True) as w:
            warnings.simplefilter(case["act"])
            if fn == "bytestring_new":
                r = py_result(lambda: (type(B)(case["name"], (), {}), None)[1])
            else:
                r = py_result(lambda: isinstance(b"" if case["answer"] else 1, B))
        return {"ok": [[[x.category.__name__, str(x.message)] for x in w], r]}
    if fn == "view_repr":
        cls = getattr(collabc_A, case["cls"])
        m = {"ok": dict, "raise": collabc_BadRepr, "notstr": collabc_NotStr}[case["kind"]]({1: 2})
        return py_result(lambda: repr(cls(m)))
    if fn == "set_cmp":
        s = collabc_self(collabc_Set, raw, tail=case["selftail"])
        s.badlen = case["badlen"]
        o = collabc_operand(case)
        m = {"le": s.__le__, "lt": s.__lt__, "ge": s.__ge__, "gt": s.__gt__, "eq": s.__eq__}
        return py_result(lambda: collabc_ret(m[case["op"]](o)))
    if fn == "set_op":
        s = collabc_self(collabc_Set, raw, tail=case["selftail"])
        o = collabc_operand(case)
        collabc_Set.uh = case["uh"]
        m = {"and": s.__and__, "or": s.__or__, "sub": s.__sub__, "rsub": s.__rsub__,
             "xor": s.__xor__}
        return py_result(lambda: collabc_setret(m[case["op"]](o)))
    if fn == "set_isdisjoint":
        s = collabc_self(collabc_Set, raw, tail=case["selftail"])
        o = collabc_operand(case)
        return py_result(lambda: s.isdisjoint(o))
    if fn == "set_hash":
        return py_result(lambda: collabc_A.Set._hash(collabc_HSet(case["hashes"], case["badlen"])))
    if fn == "frozenset_hash":
        return collabc_plain(lambda: hash(frozenset(collabc_H(h) for h in case["hashes"])))
    if fn == "mset_op":
        return collabc_mset(case, raw)
    if fn == "map_op":
        return collabc_map(case)
    if fn == "mmap_op":
        return collabc_mmap(case)
    raise ValueError(fn)


class collabc_Mro:
    def __init__(self, mro):
        self.__mro__ = mro


class collabc_DictHolder:
    def __init__(self, d):
        self.__dict__ = d


def collabc_fake(mro):
    # `_check_methods` reads C.__mro__ and B.__dict__ only.
    return collabc_Mro([collabc_DictHolder({k: (None if n else 1) for k, n in d}) for d in mro])


def collabc_hook(cls, hook, mro):
    return {"ok": collabc_ret(hook(cls, collabc_fake(mro)))}


def collabc_plain(f):
    return {"ok": f()}


class collabc_X(Exception):
    def __new__(cls):
        return 5


class collabc_W:
    def with_traceback(self, tb):
        return KeyError("w")


def collabc_tobj(a):
    if a is None:
        return None
    k = a["k"]
    if k == "cls":
        return {"ValueError": ValueError, "KeyError": KeyError}[a["n"]]
    if k == "cls_ude":
        return UnicodeDecodeError
    if k == "cls_bad":
        return collabc_X
    if k == "inst":
        return {"ValueError": ValueError, "KeyError": KeyError}[a["n"]]("x")
    if k == "func":
        return lambda: KeyError("k")
    if k == "wtb":
        return collabc_W()
    return 5


def collabc_throw(case):
    tb = None
    if case["tb"] == "tb":
        try:
            raise ValueError
        except ValueError as e:
            tb = e.__traceback__
    elif case["tb"] == "bad":
        tb = 5
    try:
        collabc_A.Generator.throw(None, collabc_tobj(case["typ"]), collabc_tobj(case["val"]), tb)
    except (ValueError, KeyError) as e:
        return {"ok": {"raised": type(e).__name__,
                       "tb": e.__traceback__.tb_next.tb_next is not None}}
    except (TypeError, AttributeError) as e:
        return {"exc": type(e).__name__, "msg": str(e)}


def collabc_gen_next(script):
    g = collabc_GenC(script)
    try:
        r = {"y": next(g)}
    except StopIteration as e:
        r = {"r": e.value}
    except GeneratorExit as e:
        r = {"exc": "GeneratorExit", "msg": str(e)}
    except ValueError as e:
        r = {"exc": "ValueError", "msg": str(e)}
    return {"ok": {"r": r, "left": len(g.s.script)}}


def collabc_agen_next(script):
    g = collabc_AGenC(script)
    try:
        r = {"y": collabc_drive(g.__anext__())}
    except StopAsyncIteration as e:
        r = {"r": e.args[0] if e.args else None}
    except GeneratorExit as e:
        r = {"exc": "GeneratorExit", "msg": str(e)}
    except ValueError as e:
        r = {"exc": "ValueError", "msg": str(e)}
    return {"ok": {"r": r, "left": len(g.s.script)}}


def collabc_from_iterable(case):
    elems = [[0] if x is None else x for x in case["xs"]]
    it = collabc_tail(elems) if case["tail"] else iter(elems)
    if case["kind"] == "set":
        collabc_Set.uh = case["uh"]
        return py_result(lambda: collabc_Set._from_iterable(
            collabc_tail([x for x in case["xs"] if x is not None]) if case["tail"]
            else iter([x for x in case["xs"] if x is not None])).xs)
    cls = collabc_A.KeysView if case["kind"] == "keys" else collabc_A.ItemsView
    return py_result(lambda: sorted(cls._from_iterable(it)))


def collabc_real(step):
    k, v = step
    try:
        yield 0
    except GeneratorExit:
        if k == "y":
            yield v
        if k == "r":
            return v
        if k == "exit":
            raise
        raise ValueError(str(v))


class collabc_Aw:
    def __await__(self):
        yield 0


async def collabc_creal(step):
    k, v = step
    try:
        await collabc_Aw()
    except GeneratorExit:
        if k == "y":
            await collabc_Aw()
        if k == "r":
            return v
        if k == "exit":
            raise
        raise ValueError(str(v))


async def collabc_areal(step):
    k, v = step
    try:
        yield 0
    except GeneratorExit:
        if k == "y":
            yield v
        if k == "r":
            return
        if k == "exit":
            raise
        raise ValueError(str(v))


def collabc_builtin_close(script, kind):
    step = script[0] if script else ("exit", 0)
    if kind == "coro":
        g = collabc_creal(step)
        g.send(None)
    else:
        g = collabc_real(step)
        next(g)
    return {"ok": {"r": py_result(g.close), "left": 0}}


def collabc_builtin_aclose(script):
    g = collabc_areal(script[0] if script else ("exit", 0))
    collabc_drive(g.asend(None))
    return {"ok": {"r": py_result(lambda: collabc_drive(g.aclose())), "left": 0}}


def collabc_carg(a, P, C):
    if a == "...":
        return Ellipsis
    if a == "~P":
        return P
    if a == "C":
        return C
    if isinstance(a, list):
        return [collabc_carg(x, P, C) for x in a]
    if isinstance(a, dict):
        return tuple(collabc_carg(x, P, C) for x in a["t"])
    return {"int": int, "str": str, "bool": bool, "float": float}[a]


def collabc_cenc(x, P, C):
    if x is Ellipsis:
        return "..."
    if x is P:
        return "~P"
    if x is C:
        return "C"
    if isinstance(x, list):
        return [collabc_cenc(y, P, C) for y in x]
    if isinstance(x, tuple):
        return {"t": [collabc_cenc(y, P, C) for y in x]}
    return x.__name__


def collabc_callable(case):
    import typing
    P = typing.ParamSpec("P")
    C = typing.Concatenate[int, P]
    a = case["a"]
    item = (int, str, float) if a == "notpair" else (collabc_carg(a, P, C), collabc_carg(case["r"], P, C))

    def f():
        x = collabc_A._CallableGenericAlias(collabc_A.Callable, item)
        enc = lambda t: [collabc_cenc(y, P, C) for y in t]  # noqa: E731
        red = x.__reduce__()[1][1]
        return {"args": enc(x.__args__), "repr": py_result(lambda: repr(x)), "reduce": {"ok": enc(red)},
                "rt": py_result(lambda: enc(collabc_A._CallableGenericAlias(collabc_A.Callable, red).__args__))}
    return py_result(f)


def collabc_getitem(case):
    import typing
    names = {"int": int, "str": str, "bool": bool, "float": float}
    a, b = names[case["a"]], names[case["b"]]
    T, S = typing.TypeVar("T"), typing.TypeVar("S")
    P = typing.ParamSpec("P")
    shape = case["shape"]
    if shape == "tv":
        x = collabc_A.Callable[[T, int], S][a, b]
    elif shape == "param":
        x = collabc_A.Callable[P, int][[a, b]]
    elif shape == "listlist":
        x = collabc_A.Callable[[T], S][[a], [b]]
    else:
        x = collabc_A.Callable[P, T][[a], [b]]
    assert type(x) is collabc_A._CallableGenericAlias
    return {"ok": [collabc_cenc(t, P, None) for t in x.__args__]}


def collabc_mset(case, raw):
    s = collabc_self(collabc_Set, raw, tail=case["selftail"])
    fresh = collabc_operand(case)
    o = s if case["selfit"] else fresh
    collabc_Set.uh = case["uh"]
    op = case["op"]

    def f():
        if op == "ior":
            s.__ior__(fresh)
        elif op == "iand":
            s.__iand__(fresh)
        elif op == "ixor":
            s.__ixor__(o)
        elif op == "isub":
            s.__isub__(o)
        elif op == "clear":
            s.clear()
        elif op == "remove":
            s.remove(case["v"])
        else:
            s.pop()
        return s.xs
    return py_result(f)


def collabc_item(case):
    k, v = case["k"], case["v"]

    def gen(n):
        yield k
        if n == 2:
            yield v
        raise ValueError("itail")

    class LS(list):
        pass
    return {"tuple": lambda: (k, v), "list": lambda: [k, v], "short": lambda: (1,), "empty": lambda: (),
            "long": lambda: (1, 2, 3), "dict3": lambda: {1: 2, 3: 4, 5: 6}, "str3": lambda: "abc",
            "iter3": lambda: iter([1, 2, 3]), "sublist3": lambda: LS([1, 2, 3]), "gen2t": lambda: gen(2),
            "gen1t": lambda: gen(1), "none": lambda: 5}[case["ikind"]]()


def collabc_map(case):
    cls = collabc_MapO if case["ovr"] else collabc_Map
    m = collabc_self(cls, case["d"], case["fail"], case["failkey"], tail=case["selftail"])
    op, k = case["op"], case["k"]
    E = collabc_E
    if op == "get":
        return py_result(lambda: m.get(k, case["default"]))
    if op == "contains":
        return py_result(lambda: collabc_A.Mapping.__contains__(m, k))
    if op == "items":
        return py_result(lambda: [list(p) for p in m.items()])
    if op == "values":
        return py_result(lambda: list(m.values()))
    if op == "valuecontains":
        m2 = collabc_self(cls, [(a, E(b)) for a, b in case["d"]], case["fail"], case["failkey"],
                          tail=case["selftail"])
        return py_result(lambda: E(k) in m2.values())
    if op == "keyscontain":
        return py_result(lambda: k in m.keys())
    if op == "eq":
        o = collabc_self(collabc_Map, case["d2"], None, tail=case["otail"])
        return py_result(lambda: collabc_ret(m.__eq__(o)))
    item = collabc_item(case)
    if case["who"] == "abc":
        return py_result(lambda: item in m.items())
    return py_result(lambda: item in dict(case["d"]).items())


def collabc_pairitem(p):
    if isinstance(p, list):
        return tuple(p)
    return {"short": (1,), "long": (1, 2, 3), "none": 5, "str3": "abc", "empty": ()}[p]


def collabc_mmap(case):
    m = collabc_self(collabc_Map, case["d"], case["fail"], tail=case["selftail"])
    op, k = case["op"], case["k"]
    items = lambda: [list(p) for p in m.d.items()]  # noqa: E731
    if op == "pop":
        return py_result(lambda: [m.pop(k), items()])
    if op == "popd":
        return py_result(lambda: [m.pop(k, case["default"]), items()])
    if op == "popitem":
        return py_result(lambda: [list(m.popitem()), items()])
    if op == "clear":
        return py_result(lambda: (m.clear(), items())[1])
    if op == "setdefault":
        return py_result(lambda: [m.setdefault(k, case["default"]), items()])
    if op == "update_map":
        other = collabc_self(collabc_Map, [tuple(p) for p in case["other"]], case["ofail"], tail=case["otail"])
        return py_result(lambda: (m.update(other), items())[1])
    if op == "update_keys":
        other = collabc_KeysLike([tuple(p) for p in case["other"]], case["ofail"], case["otail"])
        return py_result(lambda: (m.update(other), items())[1])
    if op == "update_hasattr":
        return py_result(lambda: (m.update(collabc_BadAttr()), items())[1])
    its = [collabc_pairitem(p) for p in case["items"]]
    it = collabc_tail(its) if case["otail"] else iter(its)
    return py_result(lambda: (m.update(it), items())[1])
# ====== END AREA collabc ======

# ====== BEGIN AREA functools (Lib/functools.py, Modules/_functoolsmodule.c) ======
# Everything for this area stays between these two markers; prefix top-level names with functools_.
import abc as functools_abc  # noqa: E402
import operator as functools_operator  # noqa: E402
import warnings as functools_warnings  # noqa: E402
from test.support import import_helper as functools_ih  # noqa: E402

import gc as functools_gc  # noqa: E402
functools_C = functools_ih.import_fresh_module("functools", fresh=["_functools"])
functools_P = functools_ih.import_fresh_module("functools", blocked=["_functools"])


def functools_mod(case):
    return functools_C if case.get("twin") == "c" else functools_P


def functools_tilde(r, needle):
    """A message that embeds an object or a CPython-generated signature is a wildcard."""
    if "exc" in r and needle in r["msg"]:
        r["msg"] = "~" + r["msg"]
    return r


def functools_iter(case):
    def gen():
        yield from case["xs"]
        if case["itfail"]:
            raise ValueError("it")
    if case.get("iterraise") and not case["noniter"]:
        exc = {"TypeError": TypeError, "ValueError": ValueError}[case["iterraise"]]

        class Raises:
            def __iter__(self):
                raise exc("mine")
        return Raises()
    return 5 if case["noniter"] else gen()


def functools_build(m, s):
    if s["kind"] == "base":
        i = s["id"]
        return lambda *a, **k: [i, list(a), [[x, y] for x, y in k.items()]]
    if s["kind"] == "noncallable":
        return 5
    PH = m.Placeholder
    args = [PH if a == "PH" else a for a in s["args"]]
    kw = {k: (PH if v == "PH" else v) for k, v in s["kw"]}
    cls = m.partial
    if s["override"] is not None:
        o = s["override"]

        class S(m.partial):
            _o = o

            def __call__(self, *a, **k):
                return [o, list(a), [[x, y] for x, y in k.items()]]
        cls = S
    inner = functools_build(m, s["func"])
    p = cls(inner, *args, **kw)
    if s["dict"]:
        p.x = 1
    return p


def functools_fid_safe(f, m):
    if isinstance(f, m.partial):
        o = getattr(type(f), "_o", None)
        return {"partial": o}
    return f()[0]


def functools_obj(m, p, more, morekw):
    PH = m.Placeholder
    return {"func": functools_fid_safe(p.func, m),
            "args": ["PH" if a is PH else a for a in p.args],
            "kw": [[k, v] for k, v in p.keywords.items()],
            "call": py_result(lambda: p(*more, **dict(morekw)))}


def functools_run_fast(m, case):
    PH = m.Placeholder

    def conv(xs):
        return [PH if x == "PH" else x for x in xs]
    raw, items = tuple(conv(case["raw"])), conv(case["items"])

    class T(tuple):
        def __iter__(self):
            return iter(items)

    def f(*a):
        return [-1 if x is PH else x for x in a]
    p = m.partial(f)
    p.__setstate__((f, T(raw), {}, None))
    more = case["more"]
    # plain calls: the interpreter passes PY_VECTORCALL_ARGUMENTS_OFFSET, which `p(*more)` does not
    if len(more) == 0:
        return p()
    if len(more) == 1:
        return p(more[0])
    if len(more) == 2:
        return p(more[0], more[1])
    return p(more[0], more[1], more[2])


def functools_run_kwhook(m, case):
    def f(**k):
        return [[str(x), y] for x, y in k.items()]
    stored = case["stored"]
    p = m.partial(f, **dict(stored))
    first = stored[0][0]
    # `p(**kw)` merges `kw` into a new dict first, which compares colliding keys too: only the stored key itself, which
    # no key of the call is, means that this is the lookup at Modules/_functoolsmodule.c:467
    stored_key = next(iter(p.keywords))

    class S(str):
        def __hash__(self):
            return hash(first)

        def __eq__(self, other):
            if other is stored_key and self.c is not None:
                c, self.c = self.c, None
                if c["hook"] == "raise":
                    raise ValueError("eq")
                if c["hook"] == "swap" and len(p.keywords) >= 2:
                    del p.keywords[next(reversed(p.keywords))]
                for i in range(c["n"]):
                    p.keywords[c["k"] + "z%d" % i] = 0
            return False
        __ne__ = None

    kw = {}
    for c in case["call"]:
        key = "".join(list(c["k"]))
        if c["hook"] != "none":
            key = S(key)
            key.c = c
        kw[key] = c["v"]
    return p(**kw)


def functools_run_partial(case):
    m = functools_mod(case)

    def go():
        p = functools_build(m, case["spec"])
        if not isinstance(p, m.partial):
            return "notpartial"
        return functools_obj(m, p, case["more"], case["morekw"])
    return py_result(go)


def functools_run_reduce(case):
    m = functools_mod(case)

    def go():
        p = functools_build(m, case["spec"])
        cls, ctor, state = p.__reduce__()
        q = cls(*ctor)
        q.__setstate__(state)
        return functools_obj(m, q, case["more"], [])
    return py_result(go)


def functools_spec(rng, depth):
    if depth == 0 or rng.random() < .3:
        return {"kind": "base", "id": rng.randrange(1, 4)}
    n = rng.randrange(0, 4)
    args = [("PH" if rng.random() < .35 else rng.randrange(-3, 9)) for _ in range(n)]
    kw = [[k, rng.randrange(0, 5)] for k in rng.sample(["a", "b"], rng.randrange(0, 3))]
    if rng.random() < .03 and kw:
        kw[0][1] = "PH"
    return {"kind": "partial", "func": functools_spec(rng, depth - 1), "args": args, "kw": kw,
            "override": rng.choice([None, None, None, None, 77]), "dict": rng.random() < .15}


def functools_pspec(rng):
    spec = functools_spec(rng, 3)
    if spec["kind"] == "base":
        spec = {"kind": "partial", "func": spec, "args": [], "kw": [], "override": None,
                "dict": False}
    spec["override"] = None
    return spec


functools_V = [(0, 0), (1, 0), (2, 0), (1, 1), (1, 2), (2, 2), (3, 0)]  # (value, type)


def functools_val(p):
    n, t = p
    return [n, float(n), str(n)][t]


def functools_lru_call(rng):
    args = [list(rng.choice(functools_V)) for _ in range(rng.randrange(0, 3))]
    kw = [[k, list(rng.choice(functools_V))] for k in rng.sample(["x", "y"], rng.randrange(0, 2))]
    return {"args": args, "kw": kw}


class functools_hookmeta(functools_abc.ABCMeta):
    pass


def functools_worlds(rng):
    """A random hierarchy: real classes, with virtual registrations applied later."""
    classes = [object]
    n = rng.randrange(2, 7)
    for i in range(1, n):
        k = rng.randrange(0, 3)
        bases = tuple(rng.sample(classes[1:], min(k, len(classes) - 1))) or (object,)
        abstract = rng.random() < .5
        try:
            if abstract or any(isinstance(b, functools_abc.ABCMeta) for b in bases):
                c = functools_abc.ABCMeta(f"C{i}", bases, {})
            else:
                c = type(f"C{i}", bases, {})
        except TypeError:
            continue
        classes.append(c)
    if rng.random() < .25 and len(classes) > 2:
        victim = rng.choice(classes[1:])

        def hook(cls, sub, v=victim):
            if sub is v:
                raise ValueError("hook")
            return NotImplemented
        classes.append(functools_abc.ABCMeta("H", (), {"__subclasshook__": classmethod(hook)}))
    return classes


def functools_issub(a, b):
    try:
        return issubclass(a, b)
    except ValueError:
        return True


def functools_vreg(abc_cls, c):
    try:
        abc_cls.register(c)
    except (ValueError, RuntimeError):
        pass


def functools_world_json(classes):
    idx = {c: i for i, c in enumerate(classes)}

    def members(cs):
        return [idx[c] for c in cs if c in idx]
    issub, bad = [], []
    for i, c in enumerate(classes):
        row = []
        for j, b in enumerate(classes):
            try:
                if issubclass(c, b):
                    row.append(j)
            except ValueError:
                bad.append([i, j])
        issub.append(row)
    pseudo_alias, pseudo_type = len(classes), len(classes) + 1
    return {"n": len(classes), "bad": bad,
            "bases": [members(c.__bases__) for c in classes] + [[], []],
            "mro": [members(c.__mro__) for c in classes] + [[], []],
            "subclasses": [members(c.__subclasses__()) if c is not object else []
                           for c in classes] + [[], []],
            "issub": issub + [[], []], "alias": [pseudo_alias], "notype": [pseudo_type],
            "abc": [i for i, c in enumerate(classes) if hasattr(c, "__abstractmethods__")]}


functools_HIER = {}
functools_ALIAS = list[int]
functools_NOTYPE = object()
functools_STEP = [["ret", 1], ["ret", 2], ["raise"]]


def functools_script(rng, n, calls):
    """`calls` is how many inner calls one script may make. The first may be the key itself, for
    re-entrancy, and a later one only a higher key, so that the recursion stays shallow."""
    out = []
    for _ in range(n):
        s = []
        if calls:
            k = len(out)
            for i in range(rng.randrange(0, calls + 1)):
                if i == 0:
                    s.append(["call", rng.randrange(k, n)])
                elif k + 1 < n:
                    s.append(["call", rng.randrange(k + 1, n)])
        else:
            if rng.random() < .1:
                s.append(["clear"])
        s.append(rng.choice([["ret", rng.randrange(0, 9)], ["ret", rng.randrange(0, 9)], ["raise"]]))
        out.append(s)
    return out


functools_SOURCES = [
    ("def g(x: int): pass", [["x", {"cls": 1}]]),
    ("def g(x: int | str): pass", [["x", {"union": [1, 2]}]]),
    ("def g(x: list[int]): pass", [["x", "other"]]),
    ("def g(x: 'Undefined'): pass", [["x", "fw"]]),
    ("def g(x: int | list[int]): pass", [["x", {"union": [1, None]}]]),
    ("def g(x) -> int: pass", [["return", {"cls": 1}]]),
    ("def g(x, y: str): pass", [["y", {"cls": 2}]]),
    ("def g(*, y: str): pass", [["y", {"cls": 2}]]),
    ("def g(x): pass", None),
]


def functools_gen_kwhook(rng):
    """Stored keywords, and call keywords whose `__eq__` may rewrite `p.keywords` inside `PyDict_Contains`, Modules/_functoolsmodule.c:467.
    `functools_kw_crashes` leaves out what the corelibs-partial-vectorcall-stale-kw-count finding turns into a crash."""
    stored = [[n, rng.randrange(0, 9)] for n in rng.sample(["ka", "kb", "kc"], rng.randrange(1, 4))]
    names = {n for n, _ in stored}
    call = []
    for i in range(rng.randrange(0, 5)):
        hook = rng.choice(["none", "none", "add", "swap", "raise"])
        name = "n%d" % i if hook != "none" or rng.random() < .5 else rng.choice(sorted(names))
        if any(c["k"] == name for c in call):
            name = "n%d" % i
        call.append({"k": name, "v": rng.randrange(0, 9), "hook": hook, "n": rng.randrange(0, 3)})
    if functools_kw_crashes(stored, call):
        for c in call:
            if c["hook"] in ("add", "swap"):
                c["hook"] = "none"
    return {"fn": "functools.partial_kwhook", "twin": "c", "stored": stored, "call": call}


def functools_kw_crashes(stored, call):
    d = [n for n, _ in stored]
    merged, tail = None, 0
    for c in call:
        if c["hook"] == "raise":
            return False
        adds = [c["k"] + "z%d" % i for i in range(c["n"])]
        if c["hook"] == "add":
            d = d + adds
        elif c["hook"] == "swap":
            d = (d[:-1] if len(d) >= 2 else d) + adds
        if c["k"] in d:
            merged = list(d) if merged is None else merged
        else:
            tail += 1
    n = len(merged if merged is not None else d)
    return n > len(stored) + tail or n < len(stored)


def functools_gen(rng):
    if rng.random() < .12:
        return functools_lru_ptr(rng, rng.choice(["c", "py"]))
    r = rng.randrange(0, 27)
    twin = rng.choice(["c", "py"])
    if r == 0:
        xs = [rng.randrange(-3, 6) for _ in range(rng.randrange(0, 5))]
        return {"fn": "functools.reduce", "twin": twin, "xs": xs,
                "noniter": rng.random() < .1, "itfail": rng.random() < .2,
                "iterraise": rng.choice([None, None, None, None, "TypeError", "ValueError"]),
                "initial": rng.choice([None, 0, 7]), "kind": rng.choice(["add", "sub"]),
                "bad": rng.choice([None, None, 2])}
    if r == 1:
        return {"fn": "functools.reduce_wrapper", "werror": rng.random() < .3,
                "names": rng.sample(["function", "sequence", "initial"], rng.randrange(0, 4))}
    if r == 2:
        ops = ["__lt__", "__le__", "__gt__", "__ge__"]
        roots = rng.sample(ops, rng.randrange(0, 3))
        return {"fn": "functools.total_ordering", "roots": roots, "inherit": rng.random() < .3,
                "op": rng.choice(ops), "foreign": rng.random() < .15, "rootbad": rng.random() < .08,
                "res": rng.choice([0, 1, 2, 9]), "eq": rng.choice([0, 1, 3, 9]),
                "ne": rng.choice([0, 1, 4]),
                "setfail": rng.choice([None, None, None, rng.choice(ops)])}
    if r == 3:
        return {"fn": "functools.cmp_key", "twin": twin, "x": rng.randrange(0, 4),
                "other": rng.randrange(0, 4), "otherkind": rng.choice(["key", "key", "key", "duck", "plain"]),
                "op": rng.choice(["lt", "le", "eq", "ne", "gt", "ge"]),
                "bad": rng.choice([None, None, 1]), "res": rng.choice(["int", "int", "obj", "boom"])}
    if r == 4:
        pos = [1] * rng.randrange(0, 3)
        return {"fn": "functools.key_new", "twin": twin, "pos": pos,
                "kw": rng.choice([[], [], [["obj", 2]], [["x", 2]]])}
    if r in (5, 6, 7):
        return {"fn": "functools.partial", "twin": twin, "spec": functools_pspec(rng),
                "more": [rng.randrange(0, 9) for _ in range(rng.randrange(0, 4))],
                "morekw": [["b", 9]] if rng.random() < .3 else []}
    if r == 8:
        return {"fn": "functools.partial_reduce", "twin": twin, "spec": functools_pspec(rng),
                "more": [rng.randrange(0, 9) for _ in range(rng.randrange(0, 4))]}
    if r == 9:
        return {"fn": "functools.descr_get", "twin": twin, "spec": functools_pspec(rng),
                "obj": rng.choice([None, 3]),
                "more": [rng.randrange(0, 5) for _ in range(rng.randrange(0, 3))]}
    if r in (10, 11):
        return functools_setstate_case(rng, twin)
    if r == 12:
        n = rng.randrange(0, 4)
        return {"fn": "functools.partial_repr", "twin": twin, "funcbad": rng.random() < .2,
                "args": [rng.choice(["PH", 1, 2, -1, -2]) for _ in range(n - 1)] + [1] * (n > 0),
                "kw": rng.choice([[], [["a", 1]], [["a", 1], ["b", -1]], [["c", -2]]])}
    if r == 13:
        return {"fn": "functools.placeholder", "twin": twin, "name": rng.choice(["X", "Sub"]),
                "nargs": rng.choice([0, 0, 1])}
    if r in (14, 15):
        n = rng.randrange(0, 3)
        args = [("PH" if i < n - 1 and rng.random() < .5 else 7) for i in range(n)]
        if rng.random() < .05 and args:
            args[-1] = "PH"
        k = rng.randrange(0, 3)
        nest = [("PH" if i < k - 1 and rng.random() < .5 else 8) for i in range(k)]
        return {"fn": "functools.pm_get", "twin": twin,
                "kind": rng.choice(["fn", "fn", "classm", "staticm", "obj", "partial", "custom"]),
                "id": rng.randrange(1, 4), "args": args, "nest": nest,
                "kw": rng.choice([[], [["a", 1]]]), "morekw": rng.choice([[], [["b", 2]]]),
                "abstract": rng.choice(["none", "none", "true", "raise"]),
                "instance": rng.random() < .6,
                "get": rng.choice(["new", "self", "raise"]), "self": rng.choice(["none", "attr", "raise"]),
                "more": [rng.randrange(0, 5) for _ in range(rng.randrange(0, 4))]}
    if r == 16:
        def u(d):
            k = rng.choice(["leaf", "leaf", "part", "pm", "method", "bad"]) if d else "leaf"
            if k == "leaf":
                return {"k": "leaf", "id": rng.randrange(1, 4)}
            if k == "bad":
                return {"k": "bad"}
            return {"k": k, "f": u(d - 1)}
        return {"fn": "functools.unwrap", "obj": u(5)}
    if r == 17:
        return {"fn": "functools.make_key", "typed": False, **functools_lru_call(rng)}
    if r in (18, 19, 20):
        return functools_lru_case(rng, twin)
    if r == 21:
        k = rng.choice(["int", "int", "none", "callable", "other"])
        usable = k == "callable" or rng.random() < .85
        return {"fn": "functools.lru_dec", "twin": twin, "kind": k, "typedbool": rng.random() < .7,
                "n": rng.choice([-2**70, -1, 0, 1, 5, 2**63 - 1]), "callable": usable,
                "fail": usable and rng.random() < .1, "viacache": rng.random() < .15}
    if r == 22:
        seqs = [rng.sample(range(5), rng.randrange(0, 4)) for _ in range(rng.randrange(0, 4))]
        return {"fn": "functools.c3_merge", "seqs": seqs}
    if r == 23:
        classes = functools_worlds(rng)
        key = len(functools_HIER)
        for c in classes[1:]:
            if rng.random() < .3:
                targets = [t for t in classes[1:] if isinstance(t, functools_abc.ABCMeta)
                           and t.__name__ != "H" and not functools_issub(t, c)]
                if targets:
                    functools_vreg(rng.choice(targets), c)
        functools_HIER[key] = classes
        i = rng.randrange(len(classes))
        types = rng.sample(range(len(classes)), rng.randrange(0, len(classes) + 1))
        which = rng.choice(["c3_mro", "compose_mro", "find_impl"])
        if which == "find_impl" and 0 not in types:
            types.append(0)
        w = functools_world_json(classes)
        if rng.random() < .3 and which != "c3_mro":
            types.append(len(classes) + rng.randrange(0, 2))
        extra = {"abcs": [t for t in types if t in w["abc"]]} if which == "c3_mro" else {}
        return {"fn": "functools." + which, "key": key, "cls": i, "types": types, **w, **extra}
    if r == 24:
        return functools_dispatch_case(rng)
    if r == 25:
        return functools_register_case(rng)
    k = rng.randrange(0, 21)
    if k == 13:
        if rng.random() < .7:
            return functools_lru_ptr(rng, twin_pick(rng))
        if rng.random() < .5:
            return {"fn": "functools.lru_evict", "twin": twin_pick(rng), "arm": rng.random() < .7}
        return {"fn": "functools.key_hash", "twin": twin_pick(rng)}
    if k == 14:
        return {"fn": "functools.key_isinstance", "twin": twin_pick(rng)}
    if k == 15:
        return {"fn": "functools.partial_duck", "twin": twin_pick(rng),
                "pargs": [rng.randrange(0, 5) for _ in range(rng.randrange(0, 3))],
                "args": [rng.randrange(5, 9) for _ in range(rng.randrange(0, 3))]}
    if k == 16:
        vals = rng.sample([1, 2, 3, 4], rng.randrange(0, 4))
        return {"fn": "functools.repr_mut", "twin": twin_pick(rng), "vals": vals,
                "mut": rng.choice(vals + [None])}
    if k == 17:
        return {"fn": "functools.repr_read", "bad": rng.choice(["__module__", "__qualname__"])}
    if k == 18:
        return {"fn": "functools.pm_new_fail", "which": rng.choice(["get", "repr", "none"])}
    if k == 19:
        return functools_gen_kwhook(rng)
    if k == 20:
        # one stored argument after `__setstate__`, which a `phcount` from another tuple does not describe
        raw, items = rng.choice([[["PH", 1], [1]], [[1], ["PH"]], [[1], [5]], [[2], [3]]])
        return {"fn": "functools.partial_fast", "twin": "c", "raw": raw, "items": items,
                "more": [10, 11, 12][:rng.randrange(0, 4)]}
    if k == 9:
        return {"fn": "functools.make_key_meta", "n": rng.randrange(1, 3), "typed": rng.random() < .3,
                "bad": rng.random() < .5}
    if k == 10:
        return {"fn": "functools.lru_stacked", "twin": rng.choice(["c", "py"]), "m1": rng.randrange(0, 9),
                "m2": rng.randrange(0, 9), "t1": rng.random() < .5, "t2": rng.random() < .5}
    if k == 11:
        return {"fn": "functools.wraps_ph", "which": rng.choice(["wrapped", "assigned", "updated", "none"])}
    if k == 12:
        return {"fn": "functools.update_wrapper_fn", "attr": rng.choice(["a", "b"]), "entry": rng.choice(["x", "y"])}
    if k == 0:
        names = ["a", "b", "c"]
        return {"fn": "functools.update_wrapper", "viawraps": rng.random() < .3,
                "wrapper": functools_wrapper_spec(rng),
                "wrapped": {"attrs": [[k2, 10 + i] for i, k2 in enumerate(rng.sample(names, 2))],
                            "bad": rng.choice([None, None, None, "b"]),
                            "dictkind": rng.choice(["dict", "dict", "dict", "none", "bad"]),
                            "dict": rng.sample([["y", 5], ["z", 6], ["a", 7], ["__wrapped__", 8]], 2)},
                "assigned": rng.sample(names, rng.randrange(0, 4)),
                "updated": rng.choice([["__dict__"], ["__dict__"], [], ["missing"]])}
    if k == 1:
        return {"fn": "functools.cached_get", "name": rng.choice(["p", "p", None]),
                "func": rng.choice(["ok", "mutate", "raise", "writeraise"]),
                "dict": rng.choice(["rw", "rw", "rw", "none", "class", "frozen", "dictraises", "getfails",
                                    "setfails"]),
                "items": rng.choice([[], [["p", 1]], [["q", 1]]])}
    if k == 2:
        return {"fn": "functools.cached_init",
                "tbl": [["__doc__", rng.choice(["d", None, "RAISE"])],
                        ["__module__", rng.choice(["m", None, "RAISE"])]]}
    if k == 3:
        return {"fn": "functools.set_name", "attr": rng.choice([None, "a", "b"]), "name": "a"}
    if k in (4, 5):
        return functools_sdm_case(rng)
    if k == 6:
        return {"fn": "functools.sd_noarg", "tbl": [["__name__", rng.choice(["f", None, "RAISE"])]]}
    if k == 7:
        return {"fn": "functools.key_sig"}
    return {"fn": "functools.lru_misc", "q": "functools_mod"}


def functools_wrapper_spec(rng):
    hasdict = rng.random() < .85
    return {"dict": [["a", 1], ["y", 2]][:rng.randrange(0, 3)] if hasdict else [], "hasdict": hasdict,
            "setfail": rng.choice([None, None, None, "a", "__wrapped__"])}


def twin_pick(rng):
    return rng.choice(["c", "py"])


def functools_hashres(f):
    r = py_result(f)
    if "exc" in r:
        r["msg"] = "~unhashable type"
    return r


def functools_id(i):
    def f():
        return i
    return f


def functools_setstate_case(rng, twin):
    shape = rng.choice(["four"] * 8 + ["nottuple", "size"])
    state = {"shape": shape, "n": rng.choice([0, 3, 5])}
    raw = [("PH" if rng.random() < .35 else i) for i in range(rng.randrange(0, 4))]
    it = [("PH" if rng.random() < .3 else 10 + i) for i in range(rng.randrange(2, 5))]
    argkind = rng.choice(["tuple", "tuple", "tuple", "sub", "sub", "other"])
    state.update({"callable": rng.random() < .9, "raw": raw, "iter": it, "argkind": argkind,
                  "iterbad": rng.random() < .1, "kw": rng.choice(["none", "dict", "sub", "subbad", "other"]),
                  "iter2": None, "truth": rng.choice(["std", "std", "std", "no", "raise"]),
                  "lenv": rng.choice(["std", "std", "std", "raise"]),
                  "kwitems": rng.choice([[], [["a", 1]]]), "ns": rng.choice(["none", "dict", "other"]),
                  "nsitems": rng.choice([[], [["x", 1]]])})
    if argkind == "sub" and rng.random() < .3 and twin == "py":
        state["iter2"] = [("PH" if rng.random() < .3 else 20 + i) for i in range(rng.randrange(2, 4))]
    if argkind != "sub":
        state["iter"] = raw
    ph_raw = sum(1 for a in raw[:-1] if a == "PH")
    ph_it = sum(1 for a in state["iter"] if a == "PH")
    pyok = sum(1 for a in state["iter"] if a == "PH") == 0 or argkind != "sub"
    # a call of a C partial whose count differs from the slots of its tuple can read or write out of bounds:
    # the finding corelibs-partial-setstate-phcount, reproduced in its own process, not in this one. The
    # tuple must not hold one element either, where the fast path takes over.
    more = [rng.randrange(0, 9) for _ in range(rng.randrange(0, 4))]
    safe = argkind != "sub" or (twin == "py" and pyok and state["iter2"] is None and state["truth"] == "std") or \
        (twin == "c" and len(state["iter"]) >= 2 and
         (ph_it == ph_raw or (ph_it < ph_raw and len(more) <= ph_raw)))
    return {"fn": "functools.setstate", "twin": twin, "state": state, "more": more, "call": safe}


def functools_lru_ptr(rng, twin):
    """Two keys collide, so a dict operation on one of them with the other in the dict runs one `__eq__`, and the
    countdown set by `arm` picks which. The hook may call the wrapper, clear it, or raise."""
    n = rng.randrange(3, 8)
    pair = rng.sample(range(n), 2)
    ops = []
    for _ in range(rng.randrange(2, 16)):
        x = rng.random()
        if x < .05:
            ops.append("clear")
        elif x < .22:
            ops.append(["arm", rng.randrange(1, 6)])
        else:
            ops.append(rng.choice(pair) if rng.random() < .5 else rng.randrange(n))
    hook = [(["clear"] if rng.random() < .15 else ["call", rng.choice(pair) if rng.random() < .6 else rng.randrange(n)])
            for _ in range(rng.randrange(0, 3))]
    hook.append(rng.choice([["ret", 0], ["ret", 0], ["ret", 0], ["raise"]]))
    return {"fn": "functools.lru_ptr", "twin": twin, "maxsize": rng.randrange(1, 5), "ops": ops, "pair": pair,
            "hook": hook, "script": [[st for st in steps if st[0] != "call" or st[1] > k]
                                     for k, steps in enumerate(functools_script(rng, n, 1))],
            "hashes": [hash((1000 if k in pair else k,)) & (2 ** 64 - 1) for k in range(n)]}


def functools_lru_case(rng, twin):
    maxsize = rng.choice([None, 0, 1, 2, 3, 4])
    n = rng.randrange(2, 5)
    ops = ["clear" if rng.random() < .05 else rng.randrange(n) for _ in range(rng.randrange(0, 14))]
    stage = {k: rng.choice([None, None, None, "hash", "getk", "getk", "recheckk", "insertk", "insertk"])
             for k in range(n)}
    pick = lambda name: [k for k in range(n) if stage[k] == name]
    return {"fn": "functools.lru", "twin": twin, "maxsize": maxsize, "ops": ops,
            "scripta": functools_script(rng, n, 1 if maxsize in (0, 1) else 2),
            "scriptb": functools_script(rng, n, 0),
            "hash": pick("hash"), "getk": pick("getk"), "recheckk": pick("recheckk"),
            "insertk": pick("insertk")}


def functools_register_case(rng):
    k = rng.randrange(0, 4)
    if k == 0:
        return {"fn": "functools.register", "withfunc": rng.random() < .5,
                "first": {"k": "val", "v": rng.choice([{"cls": 1}, {"union": [1, 2]}, {"union": [1, None]},
                                                       "other"])}}
    src, hints = rng.choice(functools_SOURCES)
    return {"fn": "functools.register", "withfunc": rng.random() < .1,
            "first": {"k": "func", "hints": hints, "src": src}}


def functools_sdm_case(rng):
    if rng.random() < .3:
        # a real function underneath, so `_dispatch_arg_index`, Lib/functools.py:1066, can be 1
        return {"fn": "functools.sdm", "tbl": [["__qualname__", "A.f"], ["__name__", "f"], ["__module__", "m"], ["__doc__", "d"]],
                "callable": True, "hasget": True, "absbad": False, "isfunc": True, "reprbad": False,
                "kind": rng.choice(["fn", "classm", "staticm", "obj", "partial"]),
                "id": rng.randrange(1, 4), "obj": rng.choice([None, None, 501]), "what": "call", "name": "foo",
                "more": rng.choice([[], [1], [1, 2], [1, 2, 3]]), "register": rng.random() < .5,
                "badclass": rng.random() < .1}
    tbl = [["__qualname__", rng.choice(["A.f", None, "RAISE", "FMT"])],
           ["__name__", rng.choice(["f", None, None, "RAISE", "FMT"])],
           ["__module__", rng.choice(["m", None, "RAISE"])],
           ["__doc__", rng.choice(["d", None])], ["__annotations__", rng.choice([None, 7])]]
    return {"fn": "functools.sdm", "tbl": tbl, "callable": rng.random() < .8,
            "hasget": rng.choice([True, True, True, False, False, "raise"]), "reprbad": rng.random() < .3,
            "absbad": rng.random() < .2, "isfunc": False, "kind": rng.choice(["fn", "classm", "staticm", "obj", "partial"]),
            "id": rng.randrange(1, 4), "obj": rng.choice([None, 501, -1]),
            "what": rng.choice(["repr", "getrepr", "getattr", "call", "call", "abstract", "wrapped"]),
            "name": rng.choice(["__name__", "__qualname__", "__annotations__", "__isabstractmethod__", "foo", "__wrapped2__"]),
            "more": rng.choice([[], [1], [1, 2]]), "register": rng.random() < .5, "badclass": rng.random() < .1}


def functools_dispatch_case(rng):
    classes = functools_worlds(rng)
    m = rng.choice([functools_P])

    def f(x):
        return 1000
    d = m.singledispatch(f)
    worlds, ops, out = [], [], []

    def snap():
        worlds.append(functools_world_json(classes))
        return len(worlds) - 1

    w = snap()
    for step in range(rng.randrange(1, 8)):
        a = rng.randrange(0, 4)
        tok = functools_abc.get_cache_token()
        c = rng.randrange(1, len(classes)) if len(classes) > 1 else 0
        if a == 0 and len(classes) > 1:
            impl = 2000 + step
            cc = rng.random() < .3 and len(classes) > 2
            if cc:
                pick = rng.sample(range(1, len(classes)), 2)
                u = classes[pick[0]] | classes[pick[1]]
                d.register(u, lambda x, impl=impl: impl)
                ops.append({"op": "regu", "cs": pick, "impl": impl, "w": w, "token": tok})
            else:
                d.register(classes[c], lambda x, impl=impl: impl)
                ops.append({"op": "reg", "c": c, "impl": impl, "w": w, "token": tok})
        elif a == 1:
            targets = [t for t in classes[1:] if isinstance(t, functools_abc.ABCMeta)
                       and t.__name__ != "H" and not functools_issub(t, classes[c])]
            if targets and classes[c] is not object:
                functools_vreg(rng.choice(targets), classes[c])
                w = snap()
        else:
            cls = classes[rng.randrange(0, len(classes))]
            ops.append({"op": "disp", "c": classes.index(cls), "w": w, "token": tok})
            try:
                impl = d.dispatch(cls)
                out.append({"ok": impl(None)})
            except RuntimeError as e:
                msg = str(e)
                out.append({"exc": "RuntimeError",
                            "msg": "~Ambiguous dispatch" if msg.startswith("Ambiguous") else msg})
            except ValueError as e:
                out.append({"exc": "ValueError", "msg": str(e)})
    return {"fn": "functools.dispatch", "worlds": worlds, "ops": ops, "expect": out}


class functools_FmtStr(str):
    """A name that `update_wrapper` keeps, whose `__format__` raises."""

    def __format__(self, spec):
        raise ValueError("format")


class functools_reader:
    """An object whose attribute reads follow a table: a value, `None` for AttributeError, or RAISE."""

    def __init__(self, tbl, callable_=True):
        object.__setattr__(self, "_tbl", dict(tbl))

    def __getattribute__(self, k):
        t = object.__getattribute__(self, "_tbl")
        if k in t:
            v = t[k]
            if v == "RAISE":
                raise ValueError("read")
            if v is None:
                raise AttributeError(k)
            return functools_FmtStr(v) if v == "FMT" else v
        if k in ("__class__", "__call__", "__get__", "__wrapped__"):
            return object.__getattribute__(self, k)
        raise AttributeError(k)


def functools_reader_cls(callable_, hasget):
    body = {}
    if callable_:
        body["__call__"] = lambda self, *a: 0
    if hasget == "raise":
        body["__get__"] = property(lambda self: (_ for _ in ()).throw(ValueError("hasattr")))
    elif hasget:
        body["__get__"] = lambda self, o, t=None: self
    return type("R", (functools_reader,), body)


def functools_run(case):
    fn = case["fn"].split(".")[1]
    m = functools_mod(case)
    if fn == "reduce":
        bad, kind = case["bad"], case["kind"]

        def f(a, b):
            if b == bad:
                raise ValueError("f")
            return a + b if kind == "add" else a - b
        it = functools_iter(case)
        args = (f, it) if case["initial"] is None else (f, it, case["initial"])
        return py_result(lambda: m.reduce(*args))
    if fn == "lru_ptr":
        return functools_lru_ptr_run(case, m)
    if fn == "lru_evict":
        armed = [False]

        class Kk:
            def __init__(self, n, h):
                self.n, self.h = n, h

            def __hash__(self):
                return self.h

            def __eq__(self, o):
                if armed[0]:
                    raise ValueError("eq")
                return self is o
        a, b, d = Kk(1, 0), Kk(2, 0), Kk(3, 1)

        def user(k):
            if k is d and case["arm"]:
                armed[0] = True
            return k.n * 10
        f = m.lru_cache(maxsize=2)(user)
        out = []
        for key in (a, b, a, d, b):
            try:
                out.append(f(key))
            except ValueError:
                out.append("ValueError")
            armed[0] = False
        i = f.cache_info()
        return {"ok": [out, [i.hits, i.misses, i.currsize]]}
    if fn == "key_hash":
        K = m.cmp_to_key(lambda a, b: 0)
        return py_result(lambda: hash(K(1))) if False else functools_hashres(lambda: hash(K(1)))
    if fn == "key_isinstance":
        K = m.cmp_to_key(lambda a, b: 0)

        def go():
            return isinstance(K(1), K)
        r = py_result(go)
        if "exc" in r:
            r["msg"] = "~isinstance() arg 2 must be a type"
        return r
    if fn == "partial_kwhook":
        return py_result(lambda: functools_run_kwhook(m, case))
    if fn == "partial_fast":
        return py_result(lambda: functools_run_fast(m, case))
    if fn == "partial_duck":
        P = m.partial
        inner = functools_id(1)
        pa = tuple(case["pargs"])

        class Fake:
            func = staticmethod(inner)
            args = pa
            keywords = {}
            _phcount = 0
            _merger = None
            __class__ = property(lambda s: P)

            def __call__(self):
                return 0
        fake = Fake()

        def go():
            p = P(fake, *case["args"])
            return [1 if p.func is inner else 9 if p.func is fake else -1, list(p.args)]
        return py_result(go)
    if fn == "repr_mut":
        P = m.partial
        hold = []

        class V:
            def __init__(self, v):
                self.v = v

            def __repr__(self):
                if self.v == case["mut"] and hold:
                    hold[0].keywords["zz"] = 0
                    hold.clear()
                return str(self.v)

        class F:
            def __repr__(self):
                return "f"

            def __call__(self):
                return 0
        p = P(F(), **{"k%d" % v: V(v) for v in case["vals"]})
        hold.append(p)
        return py_result(lambda: repr(p))
    if fn == "repr_read":
        bad = case["bad"]

        class Meta(type):
            def __getattribute__(cls, name):
                if name == bad:
                    raise ValueError("read")
                if name in ("__module__", "__qualname__"):
                    return name
                return super().__getattribute__(name)

        class S(functools_P.partial, metaclass=Meta):
            pass

        class F:
            def __repr__(self):
                return "f"

            def __call__(self):
                return 0
        return py_result(lambda: repr(S(F())))
    if fn == "pm_new_fail":
        w = case["which"]

        class Obj:
            def __getattr__(self, n):
                if n == "__get__" and w == "get":
                    raise ValueError("get")
                raise AttributeError(n)

            def __repr__(self):
                if w == "repr":
                    raise ValueError("repr")
                return "obj"

        def go():
            functools_P.partialmethod(Obj())
            return "pm"
        r = py_result(go)
        if r.get("exc") == "TypeError":
            r["msg"] = "~the first argument must be a callable or a descriptor"
        return r
    if fn == "make_key_meta":
        class M(type):
            def __eq__(self, o):
                return self is o

        class K(metaclass=M if case["bad"] else type):
            __hash__ = object.__hash__

        def go():
            functools_P._make_key(tuple(K() for _ in range(case["n"])), {}, case["typed"])
            return "key"
        r = py_result(go)
        if "exc" in r:
            r["msg"] = "~unhashable type"
        return r
    if fn == "lru_stacked":
        mod = functools_C if case["twin"] == "c" else functools_P
        inner = mod.lru_cache(maxsize=case["m1"], typed=case["t1"])(lambda x: x)
        outer = mod.lru_cache(maxsize=case["m2"], typed=case["t2"])(inner)
        p = outer.cache_parameters()
        return {"ok": [[p["maxsize"], p["typed"]],
                       1 if outer.cache_info is inner.cache_info or "cache_info" in outer.__dict__ else 2]}
    if fn == "wraps_ph":
        w = case["which"]
        ph = functools_P.Placeholder
        kw = {"assigned": (), "updated": ()}
        target = "x"
        if w == "wrapped":
            target = ph
        elif w != "none":
            kw[w] = ph

        def go():
            functools_P.wraps(target, **kw)
            return "partial"
        return py_result(go)
    if fn == "update_wrapper_fn":
        attr, entry = case["attr"], case["entry"]

        class Wd:
            __name__ = property(lambda self: attr)

        o = Wd()
        o.__dict__["__name__"] = entry

        def w():
            pass
        functools_P.update_wrapper(w, o)
        return {"ok": [w.__name__, w.__dict__.get("__name__")]}
    if fn == "reduce_wrapper":
        vals = {"function": lambda a, b: 1, "sequence": [1, 2], "initial": 0}
        kw = {k: vals[k] for k in case["names"]}
        kw2 = dict(kw)
        if "initial" in kw2 and "function" in kw2 and "sequence" in kw2:
            kw2["sequence"] = [1]
        with functools_warnings.catch_warnings(record=True) as w:
            functools_warnings.simplefilter("error" if case["werror"] else "always")
            r = py_result(lambda: functools_P.reduce(**kw2))
        if r.get("exc") == "TypeError":
            r["msg"] = "~reduce() missing"
        return {"ok": [r, str(w[0].message) if w else (r["msg"] if r.get("exc") == "DeprecationWarning" else None)]}
    if fn == "total_ordering":
        return functools_total(case)
    if fn == "cmp_key":
        return functools_cmp(case, m)
    if fn == "key_new":
        K = m.cmp_to_key(lambda a, b: 0)
        r = py_result(lambda: K(*case["pos"], **dict(case["kw"])).obj)
        return functools_tilde(functools_tilde(functools_tilde(r, "argument"), "keyword"), "missing")
    if fn == "partial":
        return functools_run_partial(case)
    if fn == "partial_reduce":
        return functools_run_reduce(case)
    if fn == "descr_get":
        def go():
            q = functools_build(m, case["spec"])
            return q.__get__(case["obj"], int)(*case["more"])
        return functools_tilde(py_result(go), "object is not callable")
    if fn == "setstate":
        return functools_setstate(case, m)
    if fn == "partial_repr":
        return functools_repr(case, m)
    if fn == "placeholder":
        return functools_placeholder(case, m)
    if fn == "pm_get":
        return functools_pm(case, m)
    if fn == "unwrap":
        return functools_unwrap(case)
    if fn == "make_key":
        args = tuple(functools_val(p) for p in case["args"])
        kw = {k: functools_val(v) for k, v in case["kw"]}
        k = functools_P._make_key(args, kw, False)
        return {"ok": k if isinstance(k, int) else ("tuple" if not isinstance(k, str) else int(k))}
    if fn == "lru":
        return functools_lru(case, m)
    if fn == "lru_dec":
        return functools_lru_dec(case, m)
    if fn == "c3_merge":
        return py_result(lambda: functools_P._c3_merge([list(s) for s in case["seqs"]]))
    if fn in ("c3_mro", "compose_mro", "find_impl"):
        cs = list(functools_HIER[case["key"]]) + [functools_ALIAS, functools_NOTYPE]
        idx = {c: i for i, c in enumerate(cs)}
        cls = cs[case["cls"]]
        if fn == "c3_mro":
            return py_result(lambda: [idx[c] for c in functools_P._c3_mro(
                cls, [cs[a] for a in case["abcs"]])])
        if fn == "compose_mro":
            return py_result(lambda: [idx[c] for c in functools_P._compose_mro(
                cls, [cs[a] for a in case["types"]])])
        reg = {cs[t]: t + 1000 for t in case["types"]}
        return functools_tilde(py_result(lambda: functools_P._find_impl(cls, reg)), "Ambiguous dispatch")
    if fn == "dispatch":
        return {"ok": case["expect"]}
    if fn == "register":
        return functools_register(case)
    if fn == "sd_noarg":
        tbl = dict(case["tbl"])

        def go():
            cls = functools_reader_cls(True, False)
            return functools_P.singledispatch(cls(tbl))()
        return functools_tilde(py_result(go), "\0")
    if fn == "update_wrapper":
        return functools_update_wrapper(case)
    if fn == "cached_get":
        return functools_cached(case)
    if fn == "cached_init":
        return py_result(lambda: (functools_P.cached_property(functools_reader(case["tbl"]))).attrname) \
            if True else None
    if fn == "set_name":
        cp = functools_P.cached_property(lambda s: 1)
        cp.attrname = case["attr"]

        def go():
            cp.__set_name__(object, case["name"])
            return cp.attrname
        return functools_tilde(py_result(go), "Cannot assign the same")
    if fn == "sdm":
        return functools_sdm(case)
    if fn == "key_sig":
        return {"ok": functools_C.cmp_to_key(max).__text_signature__}
    if fn == "lru_misc":
        import copy
        wr = functools_C.lru_cache(functools_mod)
        assert copy.copy(wr) is wr and copy.deepcopy(wr) is wr
        assert wr.__get__(None, int) is wr and type(wr.__get__(1, int)).__name__ == "method"
        return {"ok": [wr.__reduce__()]}
    raise ValueError(fn)


def functools_norm(v, cls=None, obj=None):
    if isinstance(v, bool):
        return 101 if v else 100
    if isinstance(v, functools_R):
        return v.v
    return v


class functools_R:
    """A comparison result that is not a bool."""

    def __init__(self, v):
        self.v = v

    def __bool__(self):
        if self.v == 9:
            raise ValueError("bool")
        return self.v != 0


def functools_total(case):
    foreign, rootbad = case["foreign"], case["rootbad"]
    res, eqv, nev = case["res"], case["eq"], case["ne"]

    def root(s, o):
        if rootbad:
            raise ValueError("root")
        return NotImplemented if foreign else functools_R(res)
    body = {"__eq__": lambda s, o: functools_R(eqv), "__ne__": lambda s, o: functools_R(nev),
            "__hash__": None}
    for r in case["roots"]:
        body[r] = root
    setfail = case["setfail"]

    class Meta(type):
        def __setattr__(cls, k, v):
            if k == setfail:
                raise ValueError("set")
            super().__setattr__(k, v)
    if case["inherit"]:
        base = Meta("B", (), body)
        cls = Meta("T", (base,), {})
    else:
        cls = Meta("T", (), body)

    def go():
        c = functools_P.total_ordering(cls)
        v = getattr(c, case["op"])(c(), c())
        return "NotImplemented" if v is NotImplemented else {"val": functools_norm(v)}
    r = py_result(go)
    return r


class functools_cmpres(int):
    pass


def functools_cmp(case, m):
    bad, kind = case["bad"], case["res"]

    class Res:
        def __init__(self, v):
            self.v = v

        def __lt__(self, o):
            return self.w("lt", self.v < o)

        def __le__(self, o):
            return self.w("le", self.v <= o)

        def __eq__(self, o):
            return self.w("eq", self.v == o)

        def __ne__(self, o):
            return self.w("ne", self.v != o)

        def __gt__(self, o):
            return self.w("gt", self.v > o)

        def __ge__(self, o):
            return self.w("ge", self.v >= o)

        def w(self, op, b):
            if kind == "boom":
                raise ValueError("cmp0")
            if op == "ne":
                return 7
            return 1 if b else 0

    def cmp(a, b):
        if a == bad:
            raise ValueError("cmp")
        return a - b if kind == "int" else Res(a - b)
    K = m.cmp_to_key(cmp)
    x = K(case["x"])

    class Duck:
        obj = case["other"]
    ok = case["otherkind"]
    o = K(case["other"]) if ok == "key" else (Duck() if ok == "duck" else 5)
    op = getattr(functools_operator, case["op"])

    def go():
        v = op(x, o)
        if isinstance(v, bool):
            return 101 if v else 100
        return v
    r = py_result(go)
    if r.get("exc") == "AttributeError":
        r["msg"] = "~object has no attribute 'obj'"
    return r


def functools_repr(case, m):
    PH = m.Placeholder

    class V:
        def __init__(self, v):
            self.v = v

        def __repr__(self):
            if self.v == -1:
                raise ValueError("arg")
            return str(self.v)

    class F:
        def __call__(self):
            return 0

        def __repr__(self):
            if case["funcbad"]:
                raise ValueError("func")
            return "F"
    p = m.partial(F())
    conv = lambda a: PH if a == "PH" else (p if a == -2 else V(a))
    args = tuple(conv(a) for a in case["args"])
    kw = {k: conv(v) for k, v in case["kw"]}
    p.__setstate__((p.func, args, kw, None))
    return py_result(lambda: repr(p))


def functools_ph_new(m, a, nargs):
    r = py_result(lambda: m._PlaceholderType(*[1] * nargs) is a)
    if "exc" in r and "positional argument" in r["msg"]:
        r["msg"] = "~takes 1 positional argument"
    return r


def functools_placeholder(case, m):
    a = m._PlaceholderType()
    b = m.Placeholder

    def sub():
        type(m._PlaceholderType)(case["name"], (m._PlaceholderType,), {})
    return {"ok": [a is b, repr(a), a.__reduce__(), py_result(sub),
                   functools_ph_new(m, a, case["nargs"])]}


class functools_targets:
    pass


def functools_pm(case, m):
    P = m.Placeholder
    args = [P if a == "PH" else a for a in case["args"]]
    nest = [P if a == "PH" else a for a in case["nest"]]
    i = case["id"]
    holder = {}

    def norm(a):
        if isinstance(a, holder["A"]):
            return 501
        if a is holder["A"]:
            return 502
        return a

    def target(*a, **k):
        return [i, [norm(x) for x in a], [[x, y] for x, y in k.items()]]
    kind = case["kind"]
    ab = case["abstract"]

    class Abs:
        """A plain callable with the `__isabstractmethod__` the case asks for."""

        def __call__(self, *a, **k):
            return target(*a, **k)

        @property
        def __isabstractmethod__(self):
            if ab == "raise":
                raise ValueError("abs")
            if ab == "true":
                return True
            raise AttributeError("__isabstractmethod__")

    class Func(Abs):
        def __get__(self, obj, cls=None):
            if obj is None:
                return self
            return functools_operator_bound(self, obj)

    def wrapf(x):
        return x

    def bound(f, o):
        class Mt(Abs):
            __self__ = o

            def __call__(self, *a, **k):
                return f(o, *a, **k)
        return Mt()
    functools_operator_bound = bound
    if kind == "fn":
        func = Func()
    elif kind == "classm":
        class Cm(Abs):
            __call__ = None

            def __get__(self, obj, cls=None):
                return bound(target, cls)
        func = Cm()
        if True:
            del_call = None
    elif kind == "staticm":
        class Sm(Abs):
            def __get__(self, obj, cls=None):
                return target
        func = Sm()
    elif kind == "obj":
        func = Abs()
    elif kind == "partial":
        class Pa(Abs):
            def __get__(self, obj, cls=None):
                return self if obj is None else bound(target, obj)
        func = Pa()
    else:
        ge, se = case["get"], case["self"]

        class Cu(Abs):
            def __get__(self, obj, cls=None):
                if ge == "raise":
                    raise ValueError("get")
                if ge == "self":
                    return self

                class New:
                    def __call__(self2, *a, **k):
                        return [i + 100, [norm(x) for x in a], [[x, y] for x, y in k.items()]]

                    @property
                    def __self__(self2):
                        if se == "raise":
                            raise ValueError("self")
                        if se == "attr":
                            return 700
                        raise AttributeError("__self__")
                return New()
        func = Cu()

    def go():
        pm = m.partialmethod(func, *args, **dict(case["kw"]))
        if nest:
            pm = m.partialmethod(pm, *nest)

        class A:
            h = pm
        holder["A"] = A
        got = pm.__get__(A() if case["instance"] else None, A)
        return got(*case["more"], **dict(case["morekw"]))
    r = py_result(go)
    if "exc" in r and "cls_or_self" in r["msg"]:
        r["msg"] = "~_method() missing 1 required positional argument: 'cls_or_self'"
    if "exc" in r and "object is not callable" in r["msg"]:
        r["msg"] = "~object is not callable"
    if "exc" in r and "must be a callable" in r["msg"]:
        r["msg"] = "~the first argument must be a callable or a descriptor"
    return r


def functools_unwrap(case):
    P = functools_P

    def mk(u):
        k = u["k"]
        if k == "leaf":
            def f():
                return u["id"]
            return f
        if k == "bad":
            class Bad:
                @property
                def __partialmethod__(self):
                    raise ValueError("read")
            return Bad()
        inner = mk(u["f"])
        if k == "part":
            o = object.__new__(P.partial)
            o.func = inner
            return o
        if k == "pm":
            o = object.__new__(P.partialmethod)
            o.func = inner
            return o

        class Met:
            pass
        o = Met()
        o.__partialmethod__ = inner
        return o

    def go():
        r = P._unwrap_partialmethod(mk(case["obj"]))
        return r() if type(r).__name__ == "function" else "method"
    return py_result(go)


def functools_setstate(case, m):
    PH = m.Placeholder
    st = case["state"]
    conv = lambda l: tuple(PH if a == "PH" else a for a in l)
    if st["shape"] == "nottuple":
        state = [1]
    elif st["shape"] == "size":
        state = (1,) * st["n"]
    else:
        fn = (lambda *a, **k: [1, list(a), [[x, y] for x, y in k.items()]]) if st["callable"] else 5
        ak = st["argkind"]
        if ak == "tuple":
            a = conv(st["raw"])
        elif ak == "sub":
            it, itbad = conv(st["iter"]), st["iterbad"]
            it2 = conv(st["iter2"]) if st["iter2"] is not None else None
            truth, lenv = st["truth"], st["lenv"]
            calls = []

            class T(tuple):
                def __iter__(self):
                    if itbad and not calls:
                        raise ValueError("iter")
                    calls.append(1)
                    return iter(it2 if it2 is not None and len(calls) > 1 else it)

                def __bool__(self):
                    if truth == "raise":
                        raise ValueError("truth")
                    return False if truth == "no" else tuple.__len__(self) != 0

                def __len__(self):
                    if lenv == "raise":
                        raise ValueError("len")
                    return tuple.__len__(self)
            a = T(conv(st["raw"]))
        else:
            a = list(conv(st["raw"]))
        ki = dict(st["kwitems"])
        kk = st["kw"]
        if kk == "none":
            kw = None
        elif kk == "dict":
            kw = ki
        elif kk == "sub":
            class D(dict):
                pass
            kw = D(ki)
        elif kk == "subbad":
            class D2(dict):
                def keys(self):
                    raise ValueError("conv")

                def __iter__(self):
                    raise ValueError("conv")
            kw = D2(ki)
        else:
            kw = 5
        ns = None if st["ns"] == "none" else (dict(st["nsitems"]) if st["ns"] == "dict" else 5)
        state = (fn, a, kw, ns)
    p = m.partial(lambda: 0)

    def go():
        p.__setstate__(state)
        _, _, rs = p.__reduce__()
        red = [["PH" if a is PH else a for a in rs[1]],
               [[k, v] for k, v in rs[2].items()] if rs[2] is not None else None,
               [[k, v] for k, v in rs[3].items()] if rs[3] is not None else None]
        if case["call"]:
            return [red, py_result(lambda: p(*case["more"]))]
        return [red, None]
    return py_result(go)


class functools_key:
    """A key whose hash is shared, so every lookup compares; `__eq__` raises when poisoned."""
    poison = None   # set of keys armed now, with the remaining compares

    def __init__(self, n, stage):
        self.n, self.stage = n, stage
        self.count = None

    def __hash__(self):
        if self.stage == "hash":
            raise TypeError("unhashable")
        return 0

    def __eq__(self, other):
        for k in (self, other):
            if k.count is not None:
                k.count -= 1
                if k.count <= 0:
                    k.count = None
                    raise ValueError("eq")
        return self.n == other.n


def functools_lru_ptr_run(case, m):
    box = {"left": None}

    def run(steps):
        for s in steps:
            if s[0] == "ret":
                return s[1]
            if s[0] == "raise":
                raise ValueError("f")
            if s[0] == "clear":
                box["w"].cache_clear()
            if s[0] == "call":
                try:
                    box["w"](keys[s[1]])
                except Exception:
                    pass
        return 0

    class Key:
        def __init__(self, n):
            self.n = n

        def __hash__(self):
            return 1000 if self.n in case["pair"] else self.n

        def __eq__(self, other):
            if box["left"] is not None:
                box["left"] -= 1
                if box["left"] == 0:
                    box["left"] = None
                    run(case["hook"])
            return self.n == other.n

    n = len(case["script"])
    keys = [Key(i) for i in range(n)]

    def user(key):
        return run(case["script"][key.n])
    box["w"] = w = m.lru_cache(maxsize=case["maxsize"])(user)
    out = []
    # bugs/corelibs-lru-evicted-hit-gc-hang.yaml: a case can leave the list with a cycle, and then the collector hangs on
    # this wrapper, so it stays off until `cache_clear` has cut the list
    gc_was_on = functools_gc.isenabled()
    functools_gc.disable()
    try:
        for op in case["ops"]:
            if op == "clear":
                w.cache_clear()
                continue
            if isinstance(op, list):
                box["left"] = op[1]
                continue
            r = py_result(lambda: w(keys[op]))
            i = w.cache_info()
            out.append([r.get("ok") if "ok" in r else r["exc"], i.hits, i.misses, i.currsize])
    finally:
        box["left"] = None
        w.cache_clear()
        if gc_was_on:
            functools_gc.enable()
    return {"ok": out}


def functools_lru(case, m):
    maxsize = case["maxsize"]
    box = {}
    current = []

    def run(steps):
        for s in steps:
            if s[0] == "ret":
                return s[1]
            if s[0] == "raise":
                raise ValueError("f")
            if s[0] == "clear":
                box["w"].cache_clear()
            if s[0] == "call":
                try:
                    call(s[1])
                except Exception:
                    pass
        return 0

    def f(key):
        if key.stage == "get":
            key.count = None
        mi = box["w"].cache_info().misses
        steps = case["scripta"][key.n] if mi % 2 == 1 else case["scriptb"][key.n]
        r = run(steps)
        size = box["w"].cache_info().currsize
        if key.stage == "recheck":
            key.count = 1
        elif key.stage == "insert" and maxsize is not None and size + 1 < maxsize + 0:
            key.count = size + 1
        return r

    def stage(n):
        for name, l in (("hash", "hash"), ("get", "getk"), ("recheck", "recheckk"), ("insert", "insertk")):
            if n in case[l]:
                return name
        return None

    def call(n):
        st = stage(n)
        if maxsize is None and st in ("recheck", "insert"):
            st = None
        if maxsize == 0:
            st = None
        key = functools_key(n, st)
        if st == "get":
            key.count = 1
        try:
            return box["w"](key)
        finally:
            key.count = None
    box["w"] = w = m.lru_cache(maxsize=maxsize)(f)
    out = []
    for op in case["ops"]:
        if op == "clear":
            w.cache_clear()
            continue
        r = py_result(lambda: call(op))
        if r.get("exc") == "TypeError":
            r["msg"] = "~unhashable"
        if r.get("exc") == "KeyError":
            r["msg"] = "~key"
        out.append(r)
    i = w.cache_info()
    return {"ok": [out, [i.hits, i.misses, i.maxsize, i.currsize]]}


def functools_lru_dec(case, m):
    k = case["kind"]
    fail = case["fail"]

    class F:
        def __call__(self):
            return 0

        @property
        def __module__(self):
            raise ValueError("read")
    user = (F() if fail else (lambda: 0)) if case["callable"] else 5
    arg = {"int": case["n"], "none": None, "callable": user, "other": 1.5}[k]
    typed = case["typedbool"]
    if k == "callable":
        typed = False if case["typedbool"] else 1

    def go():
        if case["viacache"]:
            w = m.cache(user)
        else:
            w = m.lru_cache(arg, typed)
            if k != "callable":
                w = w(user)
        p = w.cache_parameters()
        i = p["maxsize"]
        mode = "infinite" if i is None else "uncached" if i == 0 else int(i)
        return [mode, i, p["typed"]]
    return functools_tilde(py_result(go), "\0")


def functools_register(case):
    d = functools_P.singledispatch(lambda x: 1000)
    first = case["first"]
    table = {1: int, 2: str}
    funcarg = (lambda x: 7) if case["withfunc"] else None

    def val(v):
        if v == "other":
            return 5
        if "cls" in v:
            return table[v["cls"]]
        args = [table[a] if a is not None else list[int] for a in v["union"]]
        return args[0] | args[1]

    def go():
        if first["k"] == "val":
            r = d.register(val(first["v"]), funcarg)
        else:
            ns = {}
            exec(first["src"], ns)
            r = d.register(ns["g"], funcarg)
        keys = sorted({object: 0, int: 1, str: 2}[k] for k in d.registry)
        kind = "decorator" if getattr(r, "__name__", "") == "<lambda>" and funcarg is None \
            and first["k"] == "val" else "func"
        return [kind, keys]
    r = py_result(go)
    if "exc" in r and r["exc"] == "TypeError":
        msg = r["msg"]
        if "Use either" in msg:
            r["msg"] = "~Invalid first argument to `register()`: Use either `@register(some_class)`"
        elif "is not a class or union type" in msg:
            r["msg"] = "~Invalid first argument to `register()`. is not a class or union type."
        elif "not all arguments" in msg:
            r["msg"] = "~Invalid annotation: not all arguments are classes."
        elif "unresolved forward" in msg:
            r["msg"] = "~Invalid annotation: is an unresolved forward reference."
        elif "is not a class" in msg:
            r["msg"] = "~Invalid annotation: is not a class."
    return r


def functools_update_wrapper(case):
    wr, wd = case["wrapper"], case["wrapped"]
    setfail = wr["setfail"]

    class Base:
        __slots__ = ()

        def __setattr__(self, k, v):
            if k == setfail:
                raise ValueError("set")
            object.__setattr__(self, k, v)

    class WithDict(Base):
        pass

    class Slots(Base):
        __slots__ = ("a", "b", "c", "y", "__wrapped__")

    if wr["hasdict"]:
        wrapper = WithDict()
        for k, v in wr["dict"]:
            wrapper.__dict__[k] = v
    else:
        wrapper = Slots()
    attrs, bad, dk, dd = dict(wd["attrs"]), wd["bad"], wd["dictkind"], dict(wd["dict"])

    class W:
        def __getattribute__(self, k):
            if k == bad:
                raise ValueError("read")
            if k in attrs:
                return attrs[k]
            if k == "__dict__":
                if dk == "bad":
                    raise ValueError("dict")
                if dk == "none":
                    raise AttributeError(k)
                return dd
            if k == "__class__":
                return W
            raise AttributeError(k)
    wrapped = W()

    def go():
        if case["viawraps"]:
            r = functools_P.wraps(wrapped, tuple(case["assigned"]), tuple(case["updated"]))(wrapper)
        else:
            r = functools_P.update_wrapper(wrapper, wrapped, tuple(case["assigned"]), tuple(case["updated"]))
        fix = lambda v: 7 if v is wrapped else v
        if wr["hasdict"]:
            return [sorted([k, fix(v)] for k, v in r.__dict__.items()), []]
        slots = [[n, fix(getattr(r, n))] for n in Slots.__slots__ if hasattr(r, n)]
        return [[], sorted(slots)]
    res = py_result(go)
    if res.get("exc") == "AttributeError":
        res["msg"] = "~object has no attribute"
    return res


def functools_cached(case):
    class Plain:
        pass
    name, mode, dk, items = case["name"], case["func"], case["dict"], case["items"]

    class Custom:
        __slots__ = ("store",)

        def __init__(self, store):
            self.store = store

        @property
        def __dict__(self):
            if dk == "dictraises":
                raise ValueError("dict")
            return self.store

    class GetFails(dict):
        def get(self, *a):
            raise ValueError("get")

    class SetFails(dict):
        def __setitem__(self, k, v):
            raise ValueError("set")

    def func(self):
        d = self.__dict__
        if mode == "raise":
            raise ValueError("f")
        if mode == "writeraise":
            dict.__setitem__(d, "extra", 3)
            raise ValueError("f")
        if mode == "mutate":
            dict.__setitem__(d, "extra", 3)
            dict.__setitem__(d, name or "p", 9)
        return 5
    cp = functools_P.cached_property(func)
    cp.attrname = name
    if dk == "class":
        inst = None
    elif dk == "none":
        inst = type("S", (), {"__slots__": ()})()
    elif dk == "frozen":
        inst = functools_frozen(dict(items))
    elif dk == "dictraises":
        inst = Custom({})
    elif dk == "getfails":
        inst = Custom(GetFails(items))
    elif dk == "setfails":
        inst = Custom(SetFails(items))
    else:
        inst = Plain()
        inst.__dict__.update(items)

    def state():
        if dk in ("class", "none", "dictraises"):
            return None
        return sorted([k, x] for k, x in inst.__dict__.items())

    def go():
        v = cp.__get__(inst, Plain)
        if v is cp:
            return "self"
        return [v, state()]
    r = py_result(go)
    if "exc" in r and "No '__dict__'" in r["msg"]:
        r["msg"] = "~No '__dict__' attribute on instance"
    if "exc" in r and "does not support item assignment" in r["msg"]:
        r["msg"] = "~The '__dict__' attribute does not support item assignment"
    return {"ok": {"r": r, "d": state()}}


class functools_FrozenDict(dict):
    def __setitem__(self, k, v):
        raise TypeError("frozen")


class functools_frozen:
    __slots__ = ("__dict__",)

    def __init__(self, d):
        object.__setattr__(self, "__dict__", d)
        self.__class__ = functools_frozen
        functools_frozen_store[id(self)] = functools_FrozenDict(d)

    def __getattribute__(self, k):
        if k == "__dict__":
            return functools_frozen_store[id(self)]
        return object.__getattribute__(self, k)


functools_frozen_store = {}


def functools_sdm(case):
    i = case["id"]
    tbl = dict(case["tbl"])
    if case["absbad"]:
        tbl["__isabstractmethod__"] = "RAISE"
    cls = functools_reader_cls(case["callable"], case["hasget"])
    if case["reprbad"]:
        def bad_repr(self):
            raise ValueError("repr")
        cls.__repr__ = bad_repr
    if case["isfunc"]:
        def f(*a, **k):
            raise AssertionError("the dispatcher has its own implementation")
        f.__qualname__, f.__name__, f.__module__, f.__doc__ = tbl["__qualname__"], tbl["__name__"], tbl["__module__"], tbl["__doc__"]
    else:
        f = cls(tbl)
    what = case["what"]
    obj = case["obj"]

    class Obj:
        def __repr__(self):
            if obj == -1:
                raise ValueError("objrepr")
            return str(obj)

    class A:
        pass
    inst = None if obj is None else Obj()

    def norm(a):
        if a is inst:
            return obj
        if a is A:
            return 502
        return a

    def target(*a, **k):
        return [i, [norm(x) for x in a], []]
    kind = case["kind"]
    if kind == "fn":
        impl = target
    elif kind == "classm":
        impl = classmethod(target)
    elif kind == "staticm":
        impl = staticmethod(target)
    elif kind == "obj":
        class C:
            def __call__(self, *a, **k):
                return target(*a, **k)
        impl = C()
    else:
        impl = functools_P.partial(target)

    def go():
        s = functools_P.singledispatchmethod(f)
        # `impl` is what `object` dispatches to in the model too
        s.dispatcher.registry  # read only
        base = None
        s.dispatcher.register(object, impl)
        if what == "repr":
            return repr(s)
        if what == "abstract":
            return s.__isabstractmethod__ is not False and bool(s.__isabstractmethod__)
        g = s.__get__(inst, A)
        if what == "getrepr":
            return repr(g)
        if what == "getattr":
            try:
                v = g.__getattr__(case["name"])
            except AttributeError:
                return None
            return v
        if what == "wrapped":
            return g.__wrapped__ is f
        if case["register"]:
            g.register(int, impl)
        if case["badclass"]:
            class Bad:
                @property
                def __class__(self):
                    raise ValueError("cls")
            return g(*[Bad() for _ in case["more"]])
        return g(*case["more"])
    r = py_result(go)
    if "exc" in r and "is not callable or a descriptor" in r["msg"]:
        r["msg"] = "~is not callable or a descriptor"
    if "exc" in r and "has no attribute '__get__'" in r["msg"]:
        r["msg"] = "~object has no attribute '__get__'"
    return r
# ====== END AREA functools ======

# ====== BEGIN AREA operator (Lib/operator.py, Modules/_operator.c, Lib/copy.py, Lib/abc.py) ======
# Everything for this area stays between these two markers; prefix top-level names with operator_.
import abc as operator_abc  # noqa: E402
import collections as operator_collections  # noqa: E402
import copy as operator_copy  # noqa: E402
import copyreg as operator_copyreg  # noqa: E402

class operator_FalsyReductor:
    """A dispatch_table entry that is callable but false; it reduces to a string, so `copy` returns `x`."""

    def __bool__(self):
        return False

    def __call__(self, o):
        return "name"


operator_registered = []        # classes put in copyreg.dispatch_table by one case, taken out after it
import types as operator_types  # noqa: E402
import _operator as operator_C  # noqa: E402
from test.support import import_helper as operator_ih  # noqa: E402

operator_P = operator_ih.import_fresh_module("operator", blocked=["_operator"])
operator_BIN = {"add": "+", "sub": "-", "mul": "*", "matmul": "@", "floordiv": "//",
                "truediv": "/", "mod": "%", "lshift": "<<", "rshift": ">>", "and_": "&",
                "xor": "^", "or_": "|", "pow": "**"}
operator_DUNDER = {k: k.rstrip("_") for k in operator_BIN}
operator_INAME = {"and_": "iand", "or_": "ior"}


def operator_mod(case):
    return operator_C if case.get("twin") == "c" else operator_P


def operator_slot(kind, tag):
    if kind == "val":
        return lambda *a: tag
    if kind == "ni":
        return lambda *a: NotImplemented
    if kind == "raise":
        def f(*a):
            raise ValueError("slot")
        return f
    return None


def operator_pair(case, name):
    d = operator_DUNDER[name]
    A = type("A", (), {k: v for k, v in [(f"__{d}__", operator_slot(case["l"], 1))] if v})
    r = {k: v for k, v in [(f"__r{d}__", operator_slot(case["r"], 2))] if v}
    B = type("B", (A,) if case["sub"] else (), r)
    return A, B


def operator_gen(rng):
    r = rng.randrange(0, 24)
    twin = rng.choice(["c", "py"])
    if r in (0, 1):
        name = rng.choice(list(operator_BIN))
        kinds = ["none", "val", "ni", "raise"]
        l, rr = rng.choice(kinds), rng.choice(kinds)
        sub = rng.random() < .3
        case = {"twin": twin, "name": name, "sym": operator_BIN[name], "l": l, "r": rr, "sub": sub}
        if r == 0:
            return {"fn": "operator.binop", **case}
        return {"fn": "operator.iop", **case, "i": rng.choice(kinds)}
    if r in (2, 3):
        kinds = ["list", "tuple", "int", "i", "idx", "plain"]
        return {"fn": "operator.seqop", "twin": twin, "name": rng.choice(["add", "mul", "iadd", "imul"]),
                "kv": rng.choice(kinds), "kw": rng.choice(kinds),
                "a": rng.randrange(0, 3), "b": rng.choice([0, 1, 2, -1])}
    if r == 4:
        same = rng.random() < .2
        kinds = ["val", "ni", "raise", "none"]
        return {"fn": "operator.cmp", "twin": twin, "op": rng.choice(["lt", "le", "eq", "ne", "gt", "ge"]),
                "l": rng.choice(kinds), "r": rng.choice(kinds), "sub": not same and rng.random() < .3,
                "same": same}
    if r == 5:
        return {"fn": "operator.truth", "twin": twin, "name": rng.choice(["truth", "not_"]),
                "k": rng.choice(["true", "false", "none", "booltrue", "boolfalse", "boolraise", "badbool",
                                 "nonebool", "len", "lenraise", "plain"]),
                "n": rng.choice([0, 1, 5, -1, 2**63, -2**63 - 1])}
    if r == 6:
        return {"fn": "operator.unary", "twin": twin, "name": rng.choice(["neg", "pos", "inv", "abs"]),
                "has": rng.choice(["val", "raise", "none"])}
    if r == 7:
        return {"fn": "operator.index", "twin": twin, "isint": rng.random() < .15,
                "slot": rng.choice(["none", "exact", "exact", "other", "raise"]),
                "inst": rng.choice(["none", "none", "none", "exact"]), "n": rng.choice([0, 1, -1, 2**70])}
    if r == 8:
        name = rng.choice(["getitem", "setitem", "delitem"])
        objs = ["deque", "user", "userraise", "int"]
        objs += ["cls", "cg", "cgraise"] if name == "getitem" else ["tuple"]
        return {"fn": "operator." + name, "twin": twin, "o": rng.choice(objs),
                "k": rng.choice(["int", "int", "idx", "bad", "str"]),
                "n": rng.choice([0, 1, 2, 3, -1, -3, -4, 2**63, -2**63 - 1])}
    if r == 9:
        kinds = ["list", "tuple", "dict", "seqadd", "radd", "plain", "int", "gar"]
        return {"fn": "operator.concat", "twin": twin, "a": rng.choice(kinds), "b": rng.choice(kinds),
                "inplace": rng.random() < .4}
    if r in (10, 11):
        xs = [rng.randrange(0, 4) for _ in range(rng.randrange(0, 6))]
        return {"fn": "operator.search", "name": rng.choice(["countOf", "indexOf", "contains"]), "twin": twin,
                "xs": xs, "b": rng.randrange(0, 4), "bad": rng.choice([None, None, None, 1]),
                "itfail": rng.random() < .2, "notiter": rng.choice(["no", "no", "no", "no", "type", "value"]),
                "slot": rng.choice(["none", "none", "true", "raise"])}
    if r == 12:
        return {"fn": "operator.length_hint", "twin": twin,
                "len": rng.choice([None, None, 3, 0, "raise"]),
                "hint": rng.choice([None, 0, 2, -1, "ni", "typeerror", "raise", "str", "true"]),
                "desc": rng.choice(["func", "func", "func", "static", "prop", "propraise", "descraise", "descattr", "meta"]),
                "dkind": rng.choice(["int", "int", "int", "bool", "other"]), "d": rng.choice([0, 7, -1])}
    if r == 13:
        xs = [rng.randrange(0, 9) for _ in range(rng.randrange(0, 5))]
        return {"fn": "operator.itemgetter", "twin": twin, "xs": xs, "obj": rng.choice(["tuple", "sub", "list"]),
                "items": [rng.choice([0, 1, 2, -1, -6, 5, 2**63, -2**63 - 1])
                          for _ in range(rng.randrange(1, 4))]}
    if r == 14:
        k = rng.randrange(0, 2)
        if k == 0:
            return {"fn": "operator.getter_repr", "twin": twin,
                    "items": [rng.choice([1, 2, -9]) for _ in range(rng.randrange(1, 4))]}
        return {"fn": "operator.arity", "twin": twin, "cls": rng.choice(["itemgetter", "attrgetter", "methodcaller"]),
                "call": rng.random() < .6, "nargs": rng.choice([0, 1, 1, 2]), "nkw": rng.choice([0, 0, 1])}
    if r == 15:
        names = ["a", "b.c", "x", "a.x", "", "a.", ".b", "a..b", 5, ["x", "real"]]
        return {"fn": "operator.attrgetter" if rng.random() < .3 else "operator.attr_call", "twin": twin,
                "attrs": [rng.choice(names[:-1]) for _ in range(rng.randrange(1, 3))]}
    if r == 16:
        k = rng.randrange(0, 5)
        if k == 0:
            return {"fn": "operator.mc_new", "twin": twin, "name": rng.choice([None, "BAD", "m"])}
        args = [rng.randrange(0, 5) for _ in range(rng.randrange(0, 9))]
        kw = [[n, rng.randrange(0, 5)] for n in rng.sample(["p", "q", "r"], rng.randrange(0, 3))]
        if k in (1, 2):
            return {"fn": "operator.mc_call", "twin": twin, "args": args, "kw": kw,
                    "bad": rng.choice(["no", "no", "getattr", "call"])}
        if k == 3:
            if rng.random() < .3 and args:
                args[0] = -9
            return {"fn": "operator.mc_repr", "twin": twin, "args": args, "kw": kw}
        return {"fn": "operator.mc_reduce", "twin": twin, "args": args, "kw": kw}
    if r == 17:
        def arg():
            k = rng.choice(["str", "str", "strsub", "bytes", "bytes", "int", "noncontig"])
            return {"k": k, "ascii": rng.random() < .8,
                    "data": [rng.randrange(97, 100) for _ in range(rng.randrange(0, 4))]}
        a = arg()
        return {"fn": "operator.digest", "a": a, "b": dict(a) if rng.random() < .3 else arg()}
    if r in (18, 19):
        return operator_graph(rng)
    if r == 20:
        return rng.choice([
            {"fn": "operator.call_op", "twin": twin, "args": [0] * rng.randrange(0, 3), "bad": rng.random() < .3,
             "kw": rng.random() < .3},
            {"fn": "operator.replace", "has": rng.choice(["ok", "raise", "none", "null"]),
             "obj": rng.randrange(-3, 4),
             "changes": [[k, rng.randrange(-5, 6)] for k in rng.sample(["a", "b", "c"], rng.randrange(0, 4))]}])
    if r == 21:
        names = ["f", "g", "h"]
        table = [[n, rng.choice(["abs", "no"])] for n in names]
        return {"fn": "operator.abstract", "update": rng.random() < .5,
                "parents": [rng.sample(names, rng.randrange(0, 3)) for _ in range(rng.randrange(1, 3))],
                "table": table, "own": [[n, rng.choice(["abs", "no", "no"])]
                                        for n in rng.sample(["u", "v"], rng.randrange(0, 2))]}
    return operator_abc_case(rng)


def operator_spec(rng, n):
    size = rng.choice([2, 3, 3, 4, 5, 5, 1, 6])
    kind = rng.choice(["inst", "inst", "list", "dict"])
    # a state for a list or a dict `y` meets `y.__dict__`, which neither has
    return {"rv": "tuple", "size": size, "ctorfail": rng.random() < .1, "kind": kind,
            "args": [rng.randrange(0, n) for _ in range(rng.randrange(0, 3))] if kind == "inst" else [],
            "state": rng.randrange(0, n) if (kind == "inst" or rng.random() < .3) and size >= 3 and rng.random() < .5
            else None,
            "listiter": [rng.randrange(0, n)] if size >= 4 and rng.random() < .4 else None,
            "listfail": rng.random() < .2, "dictfail": rng.random() < .2,
            "dictiter": None, "setstate": rng.choice(["no", "no", "ok", "raise"]) if kind == "inst" else "no"}


def operator_state(rng, cells, ok):
    """A state for the default step of `_reconstruct` (no `__setstate__`), Lib/copy.py:258-266, built from new cells
    after the graph: a mapping or a sequence of pairs for `__dict__.update`, good or bad elements, a `(state,
    slotstate)` tuple whose slot keys are `str` or not, or something `update` cannot take. Returns its cell."""
    def add(c):
        cells.append(c)
        return len(cells) - 1

    def key():
        return add({"k": "str", "s": rng.choice(["a", "b", "f0"])}) if rng.random() < .85 else rng.choice(ok)

    def mapping(kind):
        # distinct keys, as a real dict has: `str` names, and at most one atom
        items = []
        for name in rng.sample(["a", "b", "f0"], rng.randrange(0, 3)):
            items += [add({"k": "str", "s": name}), rng.choice(ok)]
        if rng.random() < .2:
            items += [rng.choice(ok), rng.choice(ok)]
        return add({"k": kind, "items": items})

    def element():
        r = rng.random()
        if r < .55:
            return add({"k": rng.choice(["tuple", "list"]), "items": [key(), rng.choice(ok)]})
        if r < .7:
            return add({"k": "tuple", "items": [rng.choice(ok) for _ in range(rng.choice([1, 3]))]})
        if r < .8:
            return add({"k": "str", "s": rng.choice(["xy", "z", ""])})
        if r < .9:
            return mapping("dict")
        return rng.choice(ok)

    nones = [j for j in ok if cells[j]["n"] == 0]
    r = rng.random()
    if r < .3:
        return mapping(rng.choice(["dict", "dict", "fdict"]))
    if r < .55:
        return add({"k": rng.choice(["list", "tuple"]), "items": [element() for _ in range(rng.randrange(0, 3))]})
    if r < .85:
        first = mapping("dict") if rng.random() < .6 or not nones else rng.choice(nones)
        if rng.random() < .8:
            slot = mapping("dict")          # a frozendict is built after the tuples
        else:
            slot = rng.choice([mapping("dict"), add({"k": "list", "items": []}), rng.choice(nones or ok)])
        return add({"k": "tuple", "items": [first, slot]})
    if r < .95:
        return add({"k": "str", "s": rng.choice(["", "ab"])})
    return rng.choice(ok)


def operator_merge_graph(rng):
    """Dict stores that meet an equal key, which the general graphs reach only rarely: `memo` sends a dict key to an
    atom that may equal the other key (Lib/copy.py:201), or a reduce value's `dictiter` repeats a key's value
    (:279-281 and :283-284). `y[k] = v` then keeps one item, in the first key's place, with the last value."""
    cells = [{"k": "atom", "n": rng.randrange(0, 3)} for _ in range(3)]            # 0, 1, 2
    cells.append({"k": "hooked", "copier": "no", "tag": "3", "rv": "absent",       # 3: the key `memo` answers for
                  "deepcopier": rng.choice(["raise", "no"])})
    cells.append({"k": "hooked", "copier": "no", "tag": "4", "deepcopier": "no", "rv": "tuple", "size": 5,
                  "ctorfail": False, "kind": "dict", "args": [], "state": None, "listiter": None, "setstate": "no",
                  "dictiter": [[rng.randrange(0, 3), rng.randrange(0, 6)] for _ in range(rng.randrange(1, 4))]})
    items = [3, rng.randrange(0, 6), rng.randrange(0, 3), rng.randrange(0, 6)]
    if rng.random() < .5:
        items = items[2:] + items[:2]
    cells.append({"k": "dict", "items": items})                                     # 5
    root = rng.choice([4, 5, 5])
    return {"fn": "operator.deepcopy", "cells": cells, "root": root, "shallow": root == 4 and rng.random() < .3,
            "memo": [[3, rng.randrange(0, 3)]] if rng.random() < .8 else []}


def operator_state_graph(rng):
    """`_reconstruct`'s state step, `__setstate__`, `listiter` and `dictiter` (Lib/copy.py:252-284), which the general
    graphs reach rarely: one hooked object whose reduce value has the items, with a state that is `None`, an atom, or
    one built by `operator_state`, and iterators that may raise after their items."""
    cells = [{"k": "atom", "n": v} for v in (0, rng.randrange(1, 4), rng.randrange(0, 4))]     # cell 0 is `None`
    ok = [0, 1, 2]
    kind = rng.choice(["inst", "inst", "list", "dict"])
    size = rng.choice([3, 4, 5, 5])
    hooked = {"k": "hooked", "copier": "no", "tag": "3", "deepcopier": "no", "rv": "tuple", "size": size,
              "ctorfail": False, "kind": kind,
              "args": [rng.choice(ok) for _ in range(rng.randrange(0, 2))] if kind == "inst" else [],
              "state": None, "listiter": None, "dictiter": None,
              "setstate": rng.choice(["no", "no", "ok", "raise"]) if kind == "inst" else "no",
              "listfail": rng.random() < .3, "dictfail": rng.random() < .3,
              "via": rng.choice(["ex", "ex", "plain"]),
              "table": rng.choice([True, "falsy"]) if rng.random() < .3 else False}
    if rng.random() < .15:                     # no reduce value at all, or a false reductor
        hooked.update({"rv": "absent", "via": rng.choice(["ex", "falsy", "falsyex"]), "table": False})
    cells.append(hooked)                                                                       # cell 3
    r = rng.random()
    hooked["state"] = 0 if r < .2 else rng.choice(ok) if r < .3 else operator_state(rng, cells, ok)
    if size >= 4 and rng.random() < .6:
        hooked["listiter"] = [rng.choice(ok) for _ in range(rng.randrange(0, 3))]
    if size >= 5 and rng.random() < .6:
        hooked["dictiter"] = [[rng.choice(ok), rng.choice(ok)] for _ in range(rng.randrange(0, 3))]
    return {"fn": "operator.deepcopy", "cells": cells, "root": 3, "shallow": rng.random() < .4, "memo": []}


def operator_graph(rng):
    if rng.random() < .15:
        return operator_merge_graph(rng)
    if rng.random() < .2:
        return operator_state_graph(rng)
    n = rng.randrange(1, 7)
    cells = []
    for i in range(n):
        k = rng.choice(["atom", "atom", "list", "tuple", "dict", "fdict", "inst", "method", "cls", "meta", "hooked"])
        if k == "atom":
            cells.append({"k": k, "n": rng.randrange(0, 4)})
        elif k == "list":
            cells.append({"k": k, "items": [rng.randrange(0, n) for _ in range(rng.randrange(0, 3))]})
        elif k == "tuple":
            low = [j for j in range(i) if cells[j]["k"] != "tuple"] + list(range(i + 1, n))
            cells.append({"k": k, "items": rng.sample(low, min(len(low), rng.randrange(0, 3)))})
        elif k in ("dict", "fdict"):
            atoms = list({cells[j]["n"]: j for j in range(i) if cells[j]["k"] == "atom"}.values())
            items = []
            for key in rng.sample(atoms, min(len(atoms), 2)):
                items += [key, rng.randrange(0, n)]
            cells.append({"k": k, "items": items})
        elif k == "inst":
            # an attribute `f0` hides the class's method of that name from `getattr`, so from `copy` of a method
            cells.append({"k": k, "attrs": [[a, rng.randrange(0, n)]
                                            for a in rng.sample(["a", "b", "f0", "f1"], rng.randrange(0, 3))]})
        elif k == "method":
            # `f1` is no class's attribute, and its `__self__` may be anything but `None`
            cells.append({"k": k, "self": rng.randrange(0, n), "fn": rng.choice([0, 0, 1])})
        elif k in ("cls", "meta"):
            cells.append({"k": k})
        else:
            c = {"k": k, "copier": rng.choice(["no", "no", "ok", "raise"]), "tag": str(i),
                 "deepcopier": rng.choice(["no", "no", "ok", "raise"])}
            rv = rng.choice(["absent", "str", "raise", "tuple", "tuple", "tuple"])
            if rv == "tuple":
                c.update(operator_spec(rng, n))
            else:
                c.update({"rv": rv})
            # where the reduce value comes from: __reduce_ex__, __reduce__ behind __reduce_ex__ = None, a
            # copyreg.dispatch_table entry, or (with none) a false reductor
            c["via"] = rng.choice(["ex", "ex", "plain"] if rv != "absent" else ["ex", "falsy", "falsyex"])
            c["table"] = rng.choice([True, "falsy"]) if rv != "absent" and rng.random() < .25 else False
            cells.append(c)
    for i, c in enumerate(cells):
        if c["k"] == "method":
            ok = [j for j in range(n) if cells[j]["k"] == "inst" or c["fn"] == 1 and (
                cells[j]["k"] == "list" or cells[j]["k"] == "atom" and cells[j]["n"] != 0)]
            if ok:
                c["self"] = rng.choice(ok)
            else:
                cells[i] = {"k": "atom", "n": 0}
    for i, c in enumerate(cells):
        if c["k"] == "tuple":
            c["items"] = [j for j in c["items"] if cells[j]["k"] not in ("tuple", "method", "fdict")]
            # `()` is a singleton in CPython; the model's cells are distinct objects
            if not c["items"]:
                cells[i] = {"k": "atom", "n": 0}
    # a `frozendict` is built after the tuples, so its values are anything but another `frozendict` or a method
    for c in cells:
        if c["k"] == "fdict":
            it = c["items"]
            for v in range(1, len(it), 2):
                if cells[it[v]]["k"] in ("fdict", "method"):
                    it[v] = it[v - 1]
    # a method's self or a tuple item that loops through a hook has no answer to copy, so a hook's own
    # references go only to plain data
    for c in cells:
        if c["k"] == "hooked" and c["rv"] == "tuple":
            plain = [j for j in range(n) if cells[j]["k"] == "atom"] or [None]
            ok = [j for j in plain if j is not None]
            if not ok:
                c.update({"args": [], "state": None, "listiter": None})
                continue
            c["args"] = [rng.choice(ok) for _ in c["args"]]
            if c["state"] is not None:
                if c["setstate"] in ("ok", "raise"):
                    # `__setstate__` stores what it gets, so the state may lead back to the object itself
                    # through a list, which is the reason `memo[id(x)] = y` comes first in `_reconstruct`; the
                    # state may be `None` (the atom 0), and then `__setstate__` is not called, :252
                    c["state"] = rng.randrange(0, n)
                else:
                    c["state"] = operator_state(rng, cells, ok) if rng.random() < .8 else rng.choice(ok)
            if c["listiter"] is not None:
                c["listiter"] = [rng.randrange(0, n) if c["kind"] == "list" else rng.choice(ok)]
            distinct = list({cells[j]["n"]: j for j in ok}.values())
            if c["kind"] == "dict" and c["size"] >= 5 and rng.random() < .6:
                # sometimes keys of one value (two equal atoms, or one atom twice): `y[key] = value` makes one item
                keys = ([rng.choice(ok) for _ in range(2)] if rng.random() < .3
                        else rng.sample(distinct, min(len(distinct), 2)))
                c["dictiter"] = [[key, rng.randrange(0, n)] for key in keys]
    # a key whose `__deepcopy__` raises: which exception comes out says which of the key and the value was copied
    # first; when `memo` answers for the key instead, its copy can equal another key, and the two items merge
    raising = [j for j in range(n) if cells[j]["k"] == "hooked" and cells[j]["deepcopier"] == "raise"]
    for c in cells:
        if c["k"] == "dict" and raising and rng.random() < .5:
            c["items"] = [rng.choice(raising), rng.randrange(0, n)] + c["items"]
    memo = []
    if rng.random() < .3:
        for _ in range(2):
            a = rng.randrange(0, n)
            if cells[a]["k"] != "atom":
                memo.append([a, rng.randrange(0, n)])
    return {"fn": "operator.deepcopy", "cells": cells, "root": rng.randrange(0, n),
            "shallow": rng.random() < .3, "memo": memo}


def operator_f1(self):
    """A function no class here defines: `getattr(self, "f1")`, which `copy` of its method runs, fails."""
    return 1


operator_f1.__name__ = "f1"      # the model's `methName 1`


class operator_Atom(int):
    """An atom keeps its identity through both copies, like the model's atoms."""

    def __deepcopy__(self, memo):
        return self

    def __copy__(self):
        return self


class operator_Inst:
    def __init__(self, *args):
        for i, a in enumerate(args):
            setattr(self, f"k{i}", a)

    def f0(self):
        return 0


class operator_InstS(operator_Inst):
    def __setstate__(self, st):
        if type(self).fail:
            raise ValueError("setstate")
        self.__dict__["__state__"] = st


class operator_InstOk(operator_InstS):
    fail = False


class operator_InstBad(operator_InstS):
    fail = True


def operator_ctor(spec):
    def f(*args):
        if spec["ctorfail"]:
            raise ValueError("ctor")
        if spec["kind"] == "list":
            return []
        if spec["kind"] == "dict":
            return {}
        c = {"ok": operator_InstOk, "raise": operator_InstBad}.get(spec["setstate"], operator_Inst)
        return c(*args)
    return f


def operator_hooked(spec, objs):
    body = {}
    if spec["copier"] == "ok":
        body["__copy__"] = lambda s: operator_Atom(1)
    elif spec["copier"] == "raise":
        def cf(s):
            raise ValueError("copier" + spec["tag"])
        body["__copy__"] = cf
    if spec["deepcopier"] == "ok":
        body["__deepcopy__"] = lambda s, memo: operator_Atom(1)
    elif spec["deepcopier"] == "raise":
        def df(s, memo):
            raise ValueError("deepcopier" + spec["tag"])
        body["__deepcopy__"] = df
    rv = spec["rv"]

    def reduce_ex(s, proto):
        if rv == "str":
            return "name"
        if rv == "raise":
            raise ValueError("reduce")
        def it(xs, which):
            yield from xs
            if spec.get(which + "fail"):
                raise ValueError(which + "iter" + spec["tag"])
        t = [operator_ctor(spec), tuple(objs[j] for j in spec["args"]),
             objs[spec["state"]] if spec["state"] is not None else None,
             it([objs[j] for j in spec["listiter"]], "list") if spec["listiter"] is not None else None,
             it([(objs[a], objs[b]) for a, b in spec["dictiter"]], "dict") if spec["dictiter"] is not None else None,
             None]
        return tuple(t[:spec["size"]])
    # how it reduces, Lib/copy.py:84-96 and :139-152: a copyreg.dispatch_table entry, which must win over the
    # `__reduce_ex__` that then raises; `__reduce_ex__ = None` and the value from `__reduce__`; or a false reductor
    via = spec.get("via", "ex")
    falsy_table = spec.get("table") == "falsy" and rv != "absent"
    table = spec.get("table") is True and rv != "absent"
    if rv == "absent":
        body["__reduce_ex__"] = 0 if via == "falsyex" else None
        body["__reduce__"] = 0 if via == "falsy" else None
    elif table:
        def shadowed(s, proto):
            raise ValueError("shadowed")
        body["__reduce_ex__"] = shadowed
        body["__reduce__"] = None
    elif falsy_table:
        body["__reduce_ex__"] = reduce_ex
        body["__reduce__"] = None
    elif via == "plain":
        body["__reduce_ex__"] = None
        body["__reduce__"] = lambda s: reduce_ex(s, None)
    else:
        body["__reduce_ex__"] = reduce_ex
        body["__reduce__"] = None
    cls = type("Hooked", (), body)
    if table:
        operator_copyreg.dispatch_table[cls] = lambda o: reduce_ex(o, None)
        operator_registered.append(cls)
    elif falsy_table:
        # copy calls a false entry (`is not None`, Lib/copy.py:85), deepcopy skips it (`if reductor:`, :140)
        operator_copyreg.dispatch_table[cls] = operator_FalsyReductor()
        operator_registered.append(cls)
    return cls()


def operator_build_graph(cells):
    objs = {}
    for i, c in enumerate(cells):
        k = c["k"]
        if k == "atom":
            objs[i] = None if c["n"] == 0 else operator_Atom(c["n"])      # the atom 0 is `None`
        elif k == "str":
            objs[i] = c["s"]
        elif k == "list":
            objs[i] = []
        elif k == "dict":
            objs[i] = {}
        elif k == "inst":
            objs[i] = operator_Inst()
        elif k == "cls":
            objs[i] = operator_Empty
        elif k == "meta":
            objs[i] = operator_Meta("MetaCls", (), {})      # one object per cell, as `memo` keys on identity
        elif k == "hooked":
            objs[i] = operator_hooked(c, objs)
    for i, c in enumerate(cells):
        if c["k"] == "tuple":
            objs[i] = tuple(objs[j] for j in c["items"])
    for i, c in enumerate(cells):
        if c["k"] == "fdict":
            it = c["items"]
            objs[i] = frozendict({objs[a]: objs[b] for a, b in zip(it[::2], it[1::2])})
    for i, c in enumerate(cells):
        if c["k"] == "method":
            objs[i] = (objs[c["self"]].f0 if c.get("fn", 0) == 0
                       else operator_types.MethodType(operator_f1, objs[c["self"]]))
    for i, c in enumerate(cells):
        k = c["k"]
        if k == "list":
            objs[i].extend(objs[j] for j in c["items"])
        elif k == "dict":
            it = c["items"]
            for a, b in zip(it[::2], it[1::2]):
                objs[i][objs[a]] = objs[b]
        elif k == "inst":
            for a, j in c["attrs"]:
                setattr(objs[i], a, objs[j])
    return objs


def operator_render(o, seen):
    if o is None:
        return ["atom", 0]
    if isinstance(o, operator_Atom):
        return ["atom", int(o)]
    if isinstance(o, str):
        return ["str", o]
    if o is operator_Empty:
        return ["cls"]
    if isinstance(o, operator_Meta):
        return ["meta"]
    if type(o).__name__ == "Hooked":
        return ["hooked"]
    for i, s in enumerate(seen):
        if s is o:
            return ["ref", i]
    seen.append(o)
    if isinstance(o, list):
        return ["list", [operator_render(x, seen) for x in o]]
    if isinstance(o, tuple):
        return ["tuple", [operator_render(x, seen) for x in o]]
    if isinstance(o, operator_types.MethodType):
        return ["method", o.__func__.__name__, [operator_render(o.__self__, seen)]]
    if isinstance(o, operator_Inst):
        # the `__dict__` in insertion order, a key that is not a `str` rendered as an object, before its value
        out = []
        for k, v in o.__dict__.items():
            kj = k if isinstance(k, str) else operator_render(k, seen)
            out.append([kj, operator_render(v, seen)])
        return ["inst", out]
    out = []
    for k, v in o.items():
        out.append(operator_render(k, seen))
        out.append(operator_render(v, seen))
    return ["fdict" if isinstance(o, frozendict) else "dict", out]


class operator_hook_table:
    current = {}


def operator_abc_case(rng):
    n = rng.randrange(2, 5)
    table = {}

    def hook(cls, sub):
        v = table.get((cls._i, sub._i))
        if v == "raise":
            raise ValueError("hook")
        if v == "other":
            return 5
        return {"true": True, "false": False}.get(v, NotImplemented)
    classes = []
    for i in range(n + 2):
        bases = ()
        if i and i < n and rng.random() < .5:
            bases = (rng.choice(classes),)
        if i >= n:
            c = type(f"P{i}", (), {"_i": i})
        else:
            c = operator_abc.ABCMeta(f"C{i}", bases, {"_i": i, "__subclasshook__": classmethod(hook)})
        classes.append(c)
    for _ in range(rng.randrange(0, 3)):
        table[(rng.randrange(n), rng.randrange(n + 2))] = rng.choice(["true", "false", "other", "raise"])
    hooks = [[a, b, v] for (a, b), v in table.items()]
    idx = {c: i for i, c in enumerate(classes)}
    W = {"n": n, "mro": [[idx[m] for m in c.__mro__ if m in idx] for c in classes],
         "subs": [[idx[s] for s in c.__subclasses__() if s in idx] for c in classes]}
    ops = []
    for _ in range(rng.randrange(1, 7)):
        # a hook that lies can hide a cycle from `register`, and the check then recurses without end
        names = ["check", "check", "isinst", "isinst_noclass"] + ([] if hooks else ["reg"])
        ops.append({"op": rng.choice(names), "cls": rng.randrange(n), "sub": rng.randrange(n + 2),
                    "attr": rng.random() < .7})
    key = len(operator_HIER)
    operator_HIER[key] = classes
    return {"fn": "operator.abc", "key": key, "hooks": hooks, "ops": ops, **W}


operator_HIER = {}


def operator_run(case):
    fn = case["fn"].split(".")[1]
    m = operator_mod(case)
    if fn == "binop":
        A, B = operator_pair(case, case["name"])
        return py_result(lambda: getattr(m, case["name"])(A(), B()))
    if fn == "iop":
        A, B = operator_pair(case, case["name"])
        s = operator_slot(case["i"], 3)
        if s:
            setattr(A, f"__i{operator_DUNDER[case['name']]}__", s)
        name = operator_INAME.get(case["name"], "i" + case["name"])
        return operator_binmsg(py_result(lambda: getattr(m, name)(A(), B())))
    if fn == "seqop":
        return operator_seqop(case, m)
    if fn == "cmp":
        return operator_cmp(case, m)
    if fn == "truth":
        return operator_truth(case, m)
    if fn == "unary":
        name = case["name"]
        d = {"neg": "neg", "pos": "pos", "inv": "invert", "abs": "abs"}[name]
        s = {"val": lambda self: 4}.get(case["has"])
        if case["has"] == "raise":
            def s(self):
                raise ValueError("slot")
        cls = type("A", (), {f"__{d}__": s} if s else {})
        return py_result(lambda: getattr(m, name)(cls()))
    if fn == "index":
        return operator_index(case, m)
    if fn in ("getitem", "setitem", "delitem"):
        return operator_subscript(case, m, fn)
    if fn == "concat":
        return operator_concat(case, m)
    if fn == "search":
        return operator_search(case, m)
    if fn == "length_hint":
        return operator_hint(case, m)
    if fn == "itemgetter":
        items = case["items"]
        ob = {"tuple": tuple, "sub": type("T", (tuple,), {}), "list": list}[case["obj"]](case["xs"])

        def go():
            v = m.itemgetter(*items)(ob)
            return ["many", list(v)] if len(items) > 1 else ["one", v]
        return py_result(go)
    if fn == "getter_repr":
        class It:
            def __init__(self, v):
                self.v = v

            def __repr__(self):
                if self.v == -9:
                    raise ValueError("repr")
                return str(self.v)
        return py_result(lambda: repr(m.itemgetter(*[It(i) for i in case["items"]])))
    if fn == "arity":
        return operator_arity(case, m)
    if fn in ("attrgetter", "attr_call"):
        return operator_attr(case, m, fn)
    if fn == "mc_new":
        n = case["name"]

        def go():
            if n is None:
                m.methodcaller()
            return m.methodcaller(5 if n == "BAD" else n).__reduce__()[1][0]
        r = py_result(go)
        if "exc" in r and "missing 1 required" in r["msg"]:
            r["msg"] = "~" + r["msg"]
        return r
    if fn == "mc_call":
        bad = case["bad"]

        class O:
            def __getattr__(self, n):
                if bad == "getattr":
                    raise ValueError("getattr")

                def call(*a, **k):
                    if bad == "call":
                        raise ValueError("call")
                    return [list(a), [[x, y] for x, y in k.items()]]
                return call
        return py_result(lambda: m.methodcaller("m", *case["args"], **dict(case["kw"]))(O()))
    if fn == "mc_repr":
        class It:
            def __init__(self, v):
                self.v = v

            def __repr__(self):
                if self.v == -9:
                    raise ValueError("repr")
                return str(self.v)
        args = [It(a) for a in case["args"]]
        kw = {k: It(v) for k, v in case["kw"]}
        return py_result(lambda: repr(m.methodcaller("m", *args, **kw)))
    if fn == "mc_reduce":
        f = m.methodcaller("m", *case["args"], **dict(case["kw"]))
        r = f.__reduce__()
        if not case["kw"]:
            return {"ok": ["plain", list(r[1][1:])]}
        return {"ok": ["partial", [[k, v] for k, v in r[0].keywords.items()], list(r[1])]}
    if fn == "digest":
        def conv(a):
            if a["k"] in ("str", "strsub"):
                s = "".join(map(chr, a["data"])) + ("" if a["ascii"] else "é")
                return operator_DigestS(s) if a["k"] == "strsub" else s
            if a["k"] == "bytes":
                return bytes(a["data"])
            if a["k"] == "noncontig":
                # PyObject_GetBuffer(PyBUF_SIMPLE) refuses a strided view
                return memoryview(bytes(range(4)))[::2]
            return 5
        r = py_result(lambda: operator_C._compare_digest(conv(case["a"]), conv(case["b"])))
        if "exc" in r and "bytes-like" in r["msg"]:
            r["msg"] = "~" + r["msg"]
        return r
    if fn == "deepcopy":
        return operator_deep(case)
    if fn == "call_op":
        def target(*a, **k):
            if case["bad"]:
                raise ValueError("call")
            return len(a) + len(k)
        args = [target] + [0] * (len(case["args"]) - 1) if case["args"] else []
        kw = {"k": 1} if case["kw"] else {}
        return py_result(lambda: m.call(*args, **kw))
    if fn == "replace":
        h = case["has"]

        def rep(s, **k):
            if h == "raise":
                raise ValueError("replace")
            return s.v * 1000 + 10 * len(k) + sum(k.values())
        body = {"ok": {"__replace__": rep}, "raise": {"__replace__": rep}, "null": {"__replace__": None}}.get(h, {})
        cls = type("X", (), body)
        obj = cls()
        obj.v = case["obj"]
        return py_result(lambda: operator_copy.replace(obj, **dict(case["changes"])))
    if fn == "abstract":
        return operator_abstract(case)
    if fn == "abc":
        return operator_abc_run(case)
    raise ValueError(fn)


class operator_Meta(type):
    pass


class operator_Empty:
    pass


def operator_binmsg(r):
    return r


def operator_seqop(case, m):
    class I(int):
        pass

    class Idx:
        def __index__(self):
            return 2

    class Plain:
        pass

    def mk(k, n):
        return {"list": lambda: [0] * n, "tuple": lambda: (0,) * n, "int": lambda: n, "i": lambda: I(n),
                "idx": Idx, "plain": Plain}[k]()
    a, b = mk(case["kv"], case["a"]), mk(case["kw"], case["b"]) if case["b"] >= 0 or case["kw"] in ("int", "i") \
        else mk(case["kw"], 0)

    def norm(x):
        if isinstance(x, list):
            return ["list", len(x)]
        if isinstance(x, tuple):
            return ["tuple", len(x)]
        if isinstance(x, int):
            return ["int", int(x)]
        return [{Idx: "idx", Plain: "plain"}[type(x)], 0]
    return py_result(lambda: norm(getattr(m, case["name"])(a, b)))


def operator_cmp(case, m):
    op = case["op"]
    refl = {"lt": "gt", "le": "ge", "gt": "lt", "ge": "le", "eq": "eq", "ne": "ne"}[op]

    def mk(kind, val):
        if kind == "val":
            return lambda s, o: val
        if kind == "raise":
            def f(s, o):
                raise ValueError("slot")
            return f
        return lambda s, o: NotImplemented
    ab = {"__hash__": None}
    if case["l"] != "none":
        ab[f"__{op}__"] = mk(case["l"], 1)
    br = {"__hash__": None}
    if case["r"] != "none":
        br[f"__{refl}__"] = mk(case["r"], 2)
    A = type("A", (), ab)
    B = type("B", (A,) if case["sub"] else (), br)

    def go():
        a = A()
        v = getattr(m, op)(a, a if case["same"] else B())
        return 101 if v is True else 100 if v is False else v
    return py_result(go)


def operator_truth(case, m):
    k, n = case["k"], case["n"]
    o = {"true": True, "false": False, "none": None}.get(k, 0)
    if k not in ("true", "false", "none"):
        body = {}
        if k == "booltrue":
            body["__bool__"] = lambda s: True
        elif k == "boolfalse":
            body["__bool__"] = lambda s: False
        elif k == "boolraise":
            def f(s):
                raise ValueError("bool")
            body["__bool__"] = f
        elif k == "badbool":
            body["__bool__"] = lambda s: 1
        elif k == "nonebool":
            body["__bool__"] = None
        elif k == "len":
            body["__len__"] = lambda s: n
        elif k == "lenraise":
            def g(s):
                raise ValueError("len")
            body["__len__"] = g
        o = type("T", (), body)()
    return py_result(lambda: getattr(m, case["name"])(o))


def operator_index(case, m):
    n = case["n"]

    def mk(k, v):
        def f(*a):
            if k == "exact":
                return v
            if k == "other":
                return "x"
            raise ValueError("index")
        return f
    if case["isint"]:
        if case["slot"] != "none":
            # an int subclass overriding __index__: Python's a.__index__() runs it, C answers PyLong_Check first
            o = type("I", (int,), {"__index__": mk(case["slot"], n + 2)})(n)
        else:
            o = operator_IntO(n)
    else:
        body = {"__slots__": ()} if False else {}
        if case["slot"] != "none":
            body["__index__"] = mk(case["slot"], n)
        o = type("O", (), body)()
    if case["inst"] != "none" and not case["isint"]:
        o.__index__ = mk(case["inst"], n + 1)
    elif case["inst"] != "none":
        return {"ok": ["int", n]} if case.get("twin") == "c" else {"ok": ["int", n + 1]}

    def go():
        v = m.index(o)
        return ["int", v] if isinstance(v, int) else ["other", type(v).__name__]
    return py_result(go)


class operator_IntO(int):
    pass


def operator_subscript(case, m, fn):
    o, k, n = case["o"], case["k"], case["n"]

    class Idx:
        def __index__(self):
            return 3

    class Bad:
        def __index__(self):
            raise ValueError("index")
    key = {"int": n, "idx": Idx(), "bad": Bad(), "str": "s"}[k]

    class U:
        def __getitem__(self, k):
            if o == "userraise":
                raise ValueError("get")
            return 7

        def __setitem__(self, k, v):
            if o == "userraise":
                raise ValueError("set")

        def __delitem__(self, k):
            if o == "userraise":
                raise ValueError("set")

    class C:
        pass

    def cgi(cls, item):
        if o == "cgraise":
            raise ValueError("cg")
        return 9
    obj = {"deque": lambda: operator_collections.deque([0, 1, 2]), "user": U, "userraise": U,
           "int": lambda: 5, "tuple": lambda: (1,), "cls": lambda: C,
           "cg": lambda: type("D", (), {"__class_getitem__": classmethod(cgi)}),
           "cgraise": lambda: type("D", (), {"__class_getitem__": classmethod(cgi)})}[o]()
    if fn == "setitem":
        return py_result(lambda: m.setitem(obj, key, 0))
    if fn == "delitem":
        return py_result(lambda: m.delitem(obj, key))
    return py_result(lambda: m.getitem(obj, key))


def operator_concat(case, m):
    class SeqAdd:
        def __getitem__(self, i):
            raise IndexError

        def __add__(self, o):
            return self

    class RAdd:
        def __getitem__(self, i):
            raise IndexError

        def __radd__(self, o):
            return self

    class Plain:
        def __add__(self, o):
            return self

    class GAR:
        # hasattr(a, '__getitem__') passes this ValueError on
        def __getattr__(self, name):
            raise ValueError("getattr")
    mk = {"list": list, "tuple": tuple, "dict": dict, "seqadd": SeqAdd, "radd": RAdd, "plain": Plain,
          "int": lambda: 5, "gar": GAR}
    names = {list: "list", tuple: "tuple", SeqAdd: "seqadd", RAdd: "radd", Plain: "plain"}
    a, b = mk[case["a"]](), mk[case["b"]]()
    f = m.iconcat if case["inplace"] else m.concat
    return py_result(lambda: names[type(f(a, b))])


def operator_search(case, m):
    bad, name = case["bad"], case["name"]

    class E:
        def __init__(self, v):
            self.v = v

        def __eq__(self, o):
            if self.v == bad:
                raise ValueError("eq")
            return self.v == o

    def gen():
        yield from (E(x) for x in case["xs"])
        if case["itfail"]:
            raise ValueError("it")
    ni = case["notiter"]
    if ni == "type":
        src = 5
    elif ni == "value":
        def it(s):
            raise ValueError("iter")
        src = type("I", (), {"__iter__": it})()
    else:
        src = gen()
    if name == "contains" and case["slot"] != "none":
        sl = case["slot"]

        def cf(s, o):
            if sl == "raise":
                raise ValueError("contains")
            return True
        src = type("C", (), {"__contains__": cf})()
    f = getattr(m, name)
    r = py_result(lambda: f(src, case["b"]))
    if "exc" in r and r["exc"] == "TypeError" and case.get("twin") == "py" and name != "contains":
        r["msg"] = "'int' object is not iterable"
    return r


# a str subclass whose tp_name is 'S', for the type names _compare_digest prints
operator_DigestS = type("S", (str,), {})


def operator_hint(case, m):
    ln, hint = case["len"], case["hint"]
    body = {}
    if ln == "raise":
        def f(s):
            raise ValueError("len")
        body["__len__"] = f
    elif ln is not None:
        body["__len__"] = lambda s: ln
    if hint is not None:
        def h(s):
            if hint == "typeerror":
                raise TypeError("hint")
            if hint == "raise":
                raise ValueError("hint")
            return {"ni": NotImplemented, "str": "x", "true": True}.get(hint, hint)
        desc = case.get("desc", "func")
        meta = None
        if desc in ("descraise", "descattr"):
            class D:
                # with an instance (C's lookup) the function; with none (Python's type(obj) lookup) an error
                def __get__(self, inst, owner):
                    if inst is None:
                        raise (ValueError if desc == "descraise" else AttributeError)("get")
                    return lambda: h(inst)
            body["__length_hint__"] = D()
        elif desc == "meta":
            # only Python's type(obj).__length_hint__ sees the metaclass
            meta = type("M", (type,), {"__length_hint__": lambda cls, o: h(o)})
        elif desc == "static":
            # C calls it with no argument; Python's call with obj is a TypeError
            body["__length_hint__"] = staticmethod(lambda: h(None))
        elif desc == "prop":
            # C's lookup runs the getter on obj and calls what it returns; Python calls the property object
            body["__length_hint__"] = property(lambda s: (lambda: h(s)))
        elif desc == "propraise":
            def g(s):
                raise TypeError("get")
            body["__length_hint__"] = property(g)
        else:
            body["__length_hint__"] = h
    else:
        meta = None
    obj = (meta or type)("O", (), body)()
    d = {"int": case["d"], "bool": bool(case["d"])}.get(case["dkind"], "x")
    return py_result(lambda: m.length_hint(obj, d))


def operator_arity(case, m):
    name, nargs, nkw = case["cls"], case["nargs"], case["nkw"]
    C = getattr(m, name)
    kw = {"x": 1} if nkw else {}
    arg0 = "a"

    class O:
        a = 1

        def __getitem__(self, i):
            return 1

        def a2(self):
            return 1
    if case["call"]:
        f = C("a")
        if name == "methodcaller":
            O.a = lambda s: None

        def go():
            f(*[O()] * nargs, **kw)
            return None
    else:
        def go():
            if name == "methodcaller" and case.get("twin") == "c":
                return None
            C(*[arg0] * nargs, **kw)
            return None
    r = py_result(go)
    if case.get("twin") == "c" and name == "methodcaller" and not case["call"]:
        return {"ok": None}
    if case.get("twin") == "py" and "exc" in r:
        r["msg"] = "~" + r["msg"]
    return r


def operator_attr(case, m, fn):
    class N:
        def __init__(self, path):
            self.path = path

        def __getattr__(self, n):
            if n in ("", "x"):
                raise AttributeError("no attribute")
            return N(self.path + "." + n)
    attrs = case["attrs"]

    def run():
        g = m.attrgetter(*attrs)
        v = g(N("o"))
        o = ["many", [x.path for x in v]] if isinstance(v, tuple) else ["one", v.path]
        if fn == "attr_call":
            return o
        return [o, list(g.__reduce__()[1])]

    def rdone():
        g = m.attrgetter(*attrs)
        try:
            v = g(N("o"))
            o = ["many", [x.path for x in v]] if isinstance(v, tuple) else ["one", v.path]
        except AttributeError:
            o = ["one", "fail"]
        return [o, list(g.__reduce__()[1])]
    r = py_result(run if fn == "attr_call" else rdone)
    if r.get("exc") == "AttributeError":
        r["msg"] = "~no attribute"
    return r


def operator_deep(case):
    objs = operator_build_graph(case["cells"])
    x = objs[case["root"]]
    memo = {}
    for a, b in case["memo"]:
        memo[id(objs[a])] = objs[b]

    def go():
        y = operator_copy.copy(x) if case["shallow"] else operator_copy.deepcopy(x, memo)
        seen = []
        out = operator_render(y, seen)
        keep = memo.get(id(memo)) if not case["shallow"] else None
        # memo[id(memo)], the list _keep_alive fills (Lib/copy.py:226-240), rendered after the copy
        return [out, y is x, None if keep is None else [operator_render(k, seen) for k in keep]]
    try:
        r = py_result(go)
    finally:
        for c in operator_registered:
            del operator_copyreg.dispatch_table[c]
        operator_registered.clear()
    if "exc" in r:
        if r["exc"] == "TypeError" and "_reconstruct" in r["msg"]:
            r["msg"] = "~_reconstruct()"
        if r["exc"] == "Error":
            r["msg"] = "~" + r["msg"]
        if r["exc"] == "AttributeError":
            r["msg"] = "~" + r["msg"]
    return r


def operator_abstract(case):
    table = dict(case["table"])
    own = dict(case["own"])

    def val(k):
        def f():
            return 0
        if k == "abs":
            f.__isabstractmethod__ = True
        return f
    bases = []
    for i, p in enumerate(case["parents"]):
        ns = {n: val("abs") for n in p}
        bases.append(operator_abc.ABCMeta(f"P{i}", (), ns))
    names = {n for p in case["parents"] for n in p}
    body = {**{n: val(table[n]) for n in names}, **{n: val(k) for n, k in own.items()}}
    if case["update"]:
        c = operator_abc.ABCMeta("C", tuple(bases), {})
        for n, f in body.items():
            setattr(c, n, f)
        operator_abc.update_abstractmethods(c)
        return {"ok": sorted(c.__abstractmethods__)}
    c = operator_abc.ABCMeta("C", tuple(bases), body)
    return {"ok": sorted(c.__abstractmethods__)}


def operator_abc_run(case):
    cs = operator_HIER[case["key"]]
    out = []
    for op in case["ops"]:
        a, b = cs[op["cls"]], cs[op["sub"]]
        if op["op"] == "reg":
            r = py_result(lambda: cs.index(a.register(b)))
        elif op["op"] == "isinst":
            inst = object.__new__(b)
            r = py_result(lambda: type(a).__instancecheck__(a, inst))
        elif op["op"] == "isinst_noclass":
            inst = object.__new__(b)
            err = AttributeError if op["attr"] else ValueError

            def getattribute(self, name, err=err):
                if name == "__class__":
                    raise err("no")
                return object.__getattribute__(self, name)
            b.__getattribute__ = getattribute
            try:
                r = py_result(lambda: type(a).__instancecheck__(a, inst))
            finally:
                del b.__getattribute__
        else:
            r = py_result(lambda: issubclass(b, a))
        out.append(r)
    return {"ok": out}
# ====== END AREA operator ======

# ====== BEGIN AREA enumdc (Lib/enum.py, Lib/dataclasses.py) ======
# Everything for this area stays between these two markers; prefix top-level names with enumdc_.
import collections as enumdc_collections  # noqa: E402
import dataclasses as enumdc_dc  # noqa: E402
import enum as enumdc_enum  # noqa: E402
import sys as enumdc_sys  # noqa: E402
import types as enumdc_types  # noqa: E402

enumdc_DEFS = [[["A", 1], ["B", 2], ["C", 4]], [["A", 1], ["C", 4]], [["A", 1], ["B", 2], ["AB", 3]],
               [["A", 1], ["AB", 3]], [["A", 1], ["X", 6]], [["B", 2], ["A", 1]],
               [["Z", 0], ["A", 1], ["B", 2]], [["A", 1], ["B", 2], ["X", 8]],
               [["C", 4], ["A", 1], ["B", 2]]]
enumdc_BOUND = {"strict": enumdc_enum.STRICT, "conform": enumdc_enum.CONFORM,
                "eject": enumdc_enum.EJECT, "keep": enumdc_enum.KEEP}


def enumdc_cls(case):
    return enumdc_enum.Flag("F", [tuple(m) for m in case["members"]],
                            boundary=enumdc_BOUND[case["boundary"]])


def enumdc_out(x, F):
    if isinstance(x, F):
        return ["flag", x.value, x.name]
    return ["plain", x]


enumdc_OBJ = [object(), object(), object()]
enumdc_WORDS = ["A", "B", "C", "D", "name", "AB", "a", "Zed"]


def enumdc_gatom(rng):
    r = rng.randrange(0, 8)
    if r <= 3:
        return ["int", rng.choice([0, 1, 1, 2, 2, 3, 5, -1, 10, 2**63])]
    if r == 4:
        return ["str", rng.choice(["x", "y", "", "1"])]
    if r == 5:
        return ["obj", rng.randrange(0, 3)]
    return ["list", rng.randrange(0, 3)]


def enumdc_gval(rng, mode):
    """A class body value: `mode` 0 has auto and tuples of ints, so that `sorted` is exact; 1 has any tuple."""
    r = rng.randrange(0, 14)
    if r <= 4:
        return enumdc_gatom(rng)
    if r <= 7:
        if mode == 1:
            return enumdc_gatom(rng)
        return ["auto", rng.choice([None, None, None, 7, 1])]
    if r == 8:
        if mode == 0:
            return ["tup", [["int", rng.randrange(0, 4)] for _ in range(rng.randrange(0, 3))]]
        return ["tup", [enumdc_gatom(rng) for _ in range(rng.randrange(0, 3))]]
    if r == 9:
        if mode == 1:
            return ["tup", [enumdc_gatom(rng) for _ in range(rng.randrange(0, 3))]]
        return ["tup", [["auto", None]] + [rng.choice([["auto", None], ["auto", 4], ["int", 1], ["str", "s"]])
                                           for _ in range(rng.randrange(0, 3))]]
    if r == 10:
        v = enumdc_gval(rng, mode)
        while v[0] in ("member", "nonmember"):
            v = enumdc_gval(rng, mode)
        return ["member", v]
    if r == 11:
        return ["nonmember", enumdc_gatom(rng)]
    if r == 12:
        return ["descr", rng.randrange(0, 2)]
    return ["inner", rng.randrange(0, 2)]


def enumdc_gorder(rng, keys):
    l = list(keys)
    rng.shuffle(l)
    l = l[:rng.randrange(0, len(l) + 2)] + rng.choice([[], [], ["Q"]])
    if rng.random() < .5:
        return ["str", rng.choice([" ", ",", ", "]).join(l)]
    return ["names", l]


def enumdc_gbody(rng, kind):
    mode = rng.randrange(0, 2)
    body = []
    keys = ["A", "B", "C", "D"]
    if rng.random() < .1:
        body.append(["_generate_next_value_",
                     ["gen", rng.choice([["enum"], ["flag"], ["const", ["int", 7]],
                                         ["raises", "ValueError", "boom"]] if kind == "flag" else
                                        [["enum"], ["flag"], ["strEnum"], ["const", ["int", 7]],
                                         ["const", ["str", "k"]], ["raises", "ValueError", "boom"]])]])
    if rng.random() < .08:
        body.append(["_ignore_", rng.choice([["str", "A B"], ["str", "C,D"], ["names", ["B"]], ["names", []],
                                             ["int", 1]])])
    for _ in range(rng.randrange(0, 6)):
        k = rng.randrange(0, 40)
        if k < 28:
            key = rng.choice(keys)
        else:
            key = rng.choice(["name", "mro", "", "_C__x", "_C__x__", "_foo_", "_repr_x_", "__foo__", "_repr_y_",
                              "_ignore_", "_generate_next_value_", "X"])
        if kind == "flag":
            if key == "_generate_next_value_" or key == "_ignore_":
                v = ["names", ["B"]] if key == "_ignore_" else ["gen", ["flag"]]
            elif rng.random() < .3:
                v = ["auto", None]
            else:
                v = ["int", rng.choice([0, 1, 2, 3, 4, 5, 6, 8])]
        elif kind == "strEnum":
            r = rng.randrange(0, 7)
            if key == "_generate_next_value_" or key == "_ignore_":
                v = ["names", ["B"]] if key == "_ignore_" else ["gen", ["strEnum"]]
            elif r <= 2:
                v = ["str", rng.choice(["x", "y", "", "x"])]
            elif r == 3:
                v = ["auto", None]
            elif r == 4:
                v = enumdc_gatom(rng)
            else:
                v = ["tup", [rng.choice([["str", "a"], ["int", 1]]) for _ in range(rng.randrange(0, 6))]]
        elif key == "_generate_next_value_":
            v = ["gen", ["enum"]]
        elif key == "_ignore_":
            v = ["names", ["D"]]
        else:
            v = enumdc_gval(rng, mode)
        if key == "name" and v[0] == "nonmember" and v[1][0] == "list":
            v = ["nonmember", ["int", 1]]
        body.append([key, v])
    if rng.random() < .25:
        names = [b[0] for b in body if b[0] in keys]
        k = "_order_" if rng.random() < .8 else "__order__"
        body.append([k, enumdc_gorder(rng, names)])
    return body


def enumdc_gop(rng, kind, body):
    names = [b[0] for b in body] + ["A", "B", "Q"]
    r = rng.randrange(0, 15)
    if kind == "flag" and r in (1, 2, 3, 4, 7):
        r = 0
    if r == 0:
        return ["summary"]
    if r <= 2:
        a = rng.choice([b[1] for b in body if b[1][0] in ("int", "str", "obj", "list")] or [["int", 1]])
        more = [] if rng.random() < .8 else [enumdc_gatom(rng) for _ in range(rng.randrange(1, 3))]
        miss = rng.choice([["none"], ["none"], ["member", rng.choice(names)], ["other"],
                           ["raises", "KeyError", "m"], ["raises", "ValueError", "m"]])
        return ["call", rng.choice([a, enumdc_gatom(rng)]), more, miss]
    if r == 3:
        return ["contains", rng.choice([b[1] for b in body if b[1][0] in ("int", "str", "obj", "list", "tup")
                                        and all(x[0] != "auto" for x in (b[1][1] if b[1][0] == "tup" else []))]
                                       or [["int", 1]])]
    if r == 4:
        return ["contains", enumdc_gatom(rng)]
    if r == 5:
        return ["callself", rng.choice(names)]
    if r == 6:
        return ["getitem", rng.choice(names)]
    if r == 7:
        return ["iter"]
    if r == 8:
        return ["setattr", rng.choice(names)]
    if r == 9:
        return ["delattr", rng.choice(names + ["_repr_x_", "X"])]
    if r == 10:
        return ["alias", rng.choice(names), rng.choice(names + ["W", "P"])]
    if r == 11:
        return ["valias", rng.choice(names), enumdc_gatom(rng)]
    if r == 12:
        return ["valias_call", rng.choice(names), enumdc_gatom(rng)]
    return ["unique"]


def enumdc_gclass(rng):
    kind = rng.choice(["plain", "plain", "plain", "plain", "flag", "strEnum"])
    body = enumdc_gbody(rng, kind)
    return {"fn": "enumdc.ec_class", "kind": kind, "body": body, "op": enumdc_gop(rng, kind, body)}


def enumdc_gverify(rng):
    kind = rng.choice(["plain", "flag"])
    body = []
    for key in rng.sample(["A", "B", "C", "D", "E", "F"], rng.randrange(0, 6)):
        if rng.random() < .25:
            v = ["auto", None]
        elif kind == "flag":
            v = ["int", rng.choice([1, 2, 3, 4, 5, 6, 7, 8, 12, 16])]
        else:
            v = ["int", rng.choice([-2, -1, 0, 1, 2, 3, 4, 5, 6])]
        body.append([key, v])
    return {"fn": "enumdc.ec_class", "kind": kind, "body": body,
            "op": ["verify", [rng.choice(["unique", "continuous", "named"]) for _ in range(rng.randrange(0, 4))]]}


def enumdc_gupdate(rng):
    items = []
    for _ in range(rng.randrange(0, 4)):
        items.append([rng.choice(["A", "B", "AB", "CD", "_x_", "_order_", "ABC"]),
                      rng.choice([["int", 1], ["auto", None], ["auto", 3], ["descr", 0], ["str", "s"],
                                  ["nonmember", ["int", 2]]])])
    more = [[rng.choice(["E", "F"]), rng.choice([["int", 2], ["auto", None]])]
            for _ in range(rng.randrange(0, 2))]
    mapping = rng.random() < .7
    if mapping:
        items = [[k, v] for k, v in dict((k, v) for k, v in items).items()]
    return {"fn": "enumdc.ec_update", "cls": rng.choice(["C", None]), "gen": rng.random() < .5, "members": items,
            "more": more, "mapping": mapping}


def enumdc_gcreate(rng):
    kind = rng.choice(["plain", "plain", "flag", "strEnum"])
    words = rng.sample(enumdc_WORDS, rng.randrange(0, 5))
    if rng.random() < .15:
        words = words + words[:1]
    r = rng.randrange(0, 3)
    if r == 0:
        names = ["text", rng.choice([" ", ",", ", ", "  "]).join(words)]
    elif r == 1:
        names = ["seq", words]
    else:
        names = ["pairs", [[w, ["int", rng.randrange(0, 4)] if kind != "strEnum" else ["str", "v"]] for w in words]]
    return {"fn": "enumdc.ec_create", "kind": kind, "start": rng.choice([1, 1, 0, 5]), "names": names}


def enumdc_gflag(rng):
    mixin = rng.random() < .5
    op = rng.choice(["or", "and", "xor", "in", "invert", "bool", "class_in", "class_in"])
    other = rng.choice([["same", rng.randrange(0, 8)], ["same", rng.randrange(0, 8)],
                        ["mixin", rng.randrange(-9, 20)], ["other", 0], ["none", 0]])
    if op == "class_in":
        other = rng.choice([["same", rng.randrange(-20, 40)], ["same", rng.randrange(-20, 40)], ["other", 0]])
    if mixin and other[0] == "none":
        other = ["other", 0]
    return {"fn": "enumdc.ec_flag", "members": rng.choice(enumdc_DEFS),
            "boundary": rng.choice(["strict", "conform", "eject", "keep"]), "mixin": mixin, "op": op,
            "v": rng.randrange(0, 8), "self_none": not mixin and rng.random() < .1, "other": other}


def enumdc_gfield(rng, name, kind, plain_default=True):
    f = {"name": name, "kind": kind, "default": None, "unhash": False, "factory": None, "init": rng.random() < .85,
         "repr": rng.random() < .8, "hash": rng.choice([None, None, True, False]), "compare": rng.random() < .8,
         "kw": rng.choice([None, None, True, False])}
    r = rng.randrange(0, 8)
    if r <= 2:
        f["default"] = rng.randrange(0, 5)
    elif r == 3 and plain_default:
        f["factory"] = rng.randrange(5, 9)
    elif r == 4 and rng.random() < .3:
        f["default"] = rng.randrange(0, 5)
        f["unhash"] = True
    return f


def enumdc_gbase(rng):
    fields = []
    for name in rng.sample(["a", "b", "c", "d"], rng.randrange(0, 3)):
        kind = rng.choice(["plain", "plain", "plain", "classvar", "initvar"])
        f = enumdc_gfield(rng, name, kind, kind == "plain")
        f["unhash"] = f["unhash"] and kind != "plain"
        f["kw"] = None if kind == "classvar" else bool(f["kw"])
        f["init"] = True if kind == "classvar" else f["init"]
        fields.append(f)
    # A base must be a valid dataclass: no default before a field without one.
    seen = False
    for f in fields:
        if f["kind"] == "classvar" or f["kw"] or not f["init"]:
            continue
        if f["default"] is not None or f["factory"] is not None:
            seen = True
        elif seen:
            f["default"] = 1
    return {"fields": fields, "frozen": rng.random() < .3}


def enumdc_gdc(rng):
    params = {"init": rng.random() < .9, "repr": rng.random() < .9, "eq": rng.random() < .85, "order": rng.random() < .15,
              "unsafe_hash": rng.random() < .15, "frozen": rng.random() < .2, "match_args": rng.random() < .85,
              "kw_only": rng.random() < .15, "slots": rng.random() < .07, "weakref_slot": rng.random() < .03}
    if rng.random() < .7:
        params["weakref_slot"] = False
    bases = [enumdc_gbase(rng) for _ in range(rng.choice([0, 0, 0, 1, 1, 2]))]
    frozen = rng.random()
    if frozen < .85 and bases:
        v = bases[0]["frozen"]
        for b in bases:
            b["frozen"] = v
        params["frozen"] = v
    anns = []
    for name in rng.sample(["a", "b", "c", "e", "f"], rng.randrange(0, 5)):
        kind = rng.choice(["plain", "plain", "plain", "plain", "classvar", "initvar"])
        r = rng.randrange(0, 5)
        if r <= 1:
            attr = ["missing"]
        elif r == 2:
            attr = ["value", rng.randrange(0, 5), rng.random() < .1]
        else:
            attr = ["field", enumdc_gfield(rng, name, kind)]
            if rng.random() < .9 and kind != "plain":
                attr[1]["factory"] = None
            if rng.random() < .9 and kind == "classvar":
                attr[1]["kw"] = None
        anns.append({"name": name, "kind": kind, "attr": attr})
    if rng.random() < .15:
        anns.insert(rng.randrange(0, len(anns) + 1), {"name": "_", "kind": "kw", "attr": ["missing"]})
    if rng.random() < .03:
        anns.insert(rng.randrange(0, len(anns) + 1), {"name": "__", "kind": "kw", "attr": ["missing"]})
    defined = [n for n in ["__repr__", "__eq__", "__lt__", "__setattr__", "__init__", "__match_args__"]
               if rng.random() < .06]
    names = []
    for b in bases:
        names += [f["name"] for f in b["fields"]]
    names += [a["name"] for a in anns if a["kind"] != "kw"]
    names = list(dict.fromkeys(names))
    r = rng.randrange(0, 6)
    if r <= 1:
        op = ["info"]
    else:
        params["init"] = True
        defined = [n for n in defined if n not in ("__init__", "__setattr__")]
        args = [rng.randrange(10, 20) for _ in range(rng.randrange(0, len(names) + 2))]
        kw = [[n, rng.randrange(20, 30)] for n in rng.sample(names, rng.randrange(0, len(names) + 1))]
        if rng.random() < .1:
            kw.append(["zz", 1])
        if r <= 3:
            args = args[:rng.randrange(0, len(args) + 1)]
            if rng.random() < .5:
                args, kw = [], [[n, rng.randrange(20, 30)] for n in names]
            op = ["init", args, kw]
        else:
            ch = [[n, rng.randrange(30, 40)] for n in rng.sample(names, rng.randrange(0, len(names) + 1))]
            if rng.random() < .7:
                args, kw = [], [[n, rng.randrange(20, 30)] for n in names]
            op = ["replace", args, kw, ch]
    return {"fn": "enumdc.dc_class", "params": params, "bases": bases, "anns": anns,
            "stray": "s" if rng.random() < .02 else None, "hash": rng.choice([None, None, None, None, False, True]),
            "defined": defined, "has_slots": op[0] == "info" and rng.random() < .1, "post": rng.random() < .2, "op": op}


def enumdc_gdcmro(rng):
    # Bases that share the names c and d, often with init=False and no default, and an own c that may be a field(init=False)
    # without a default: reading such a field on the instance falls through the MRO to the next class attribute, which a
    # ClassVar, an InitVar or a field of a later base left (Lib/dataclasses.py:628-632, 1085-1102).
    case = enumdc_gdc(rng)
    fz = case["params"]["frozen"]
    bases = []
    for _ in range(rng.randrange(1, 4)):
        fields = []
        for name in ["c", "d"][:rng.randrange(1, 3)]:
            kind = rng.choice(["plain", "plain", "classvar", "initvar"])
            f = enumdc_gfield(rng, name, kind, kind == "plain" and rng.random() < .3)
            f["unhash"] = False
            f["kw"] = None if kind == "classvar" else bool(f["kw"])
            f["init"] = True if kind == "classvar" else rng.random() < .4
            if f["factory"] is None and rng.random() < .4:
                f["default"] = None
            fields.append(f)
        if rng.random() < .4:
            fields[0].update({"kind": "plain", "init": False, "default": None, "factory": None, "kw": False})
        seen = False
        for f in fields:
            if f["kind"] == "classvar" or f["kw"] or not f["init"]:
                continue
            if f["default"] is not None or f["factory"] is not None:
                seen = True
            elif seen:
                f["default"] = 1
        bases.append({"fields": fields, "frozen": fz})
    anns = [a for a in case["anns"] if a["name"] != "c"]
    r = rng.random()
    if r < .35:
        own = enumdc_gfield(rng, "c", "plain", False)
        own.update({"init": False, "default": None, "factory": None, "unhash": False})
        anns.insert(rng.randrange(0, len(anns) + 1), {"name": "c", "kind": "plain", "attr": ["field", own]})
    elif r < .5:
        anns.insert(rng.randrange(0, len(anns) + 1), {"name": "c", "kind": "plain", "attr": ["missing"]})
    elif r < .6:
        anns.insert(rng.randrange(0, len(anns) + 1), {"name": "c", "kind": "plain", "attr": ["value", rng.randrange(0, 5), False]})
    merged = {}
    for b in bases:
        for f in b["fields"]:
            merged[f["name"]] = f["kind"] != "classvar" and f["init"]
    for a in anns:
        if a["kind"] != "kw":
            merged[a["name"]] = a["kind"] != "classvar" and (a["attr"][0] != "field" or a["attr"][1]["init"])
    names = list(merged)
    p = case["params"]
    defined = case["defined"]
    if rng.random() < .2:
        op = ["info"]
    else:
        p["init"] = True
        defined = [n for n in defined if n not in ("__init__", "__setattr__")]
        kw = [[n, rng.randrange(20, 30)] for n in names if (merged[n] and rng.random() < .85) or rng.random() < .05]
        if rng.random() < .6:
            op = ["init", [], kw]
        else:
            op = ["replace", [], kw, [[n, rng.randrange(30, 40)] for n in names if rng.random() < .2]]
    case.update({"bases": bases, "anns": anns, "defined": defined, "op": op,
                 "has_slots": op[0] == "info" and case["has_slots"]})
    return case


def enumdc_gdv(rng, depth):
    r = rng.randrange(0, 15 if depth > 0 else 4)
    if r == 0:
        return ["atom", rng.randrange(-3, 4)]
    if r == 1:
        return ["str", rng.choice(["x", "y", ""])]
    if r == 2:
        return ["copied", rng.randrange(0, 3)]
    if r == 3:
        return ["unhash", rng.randrange(0, 3)]
    items = lambda: [enumdc_gdv(rng, depth - 1) for _ in range(rng.randrange(0, 3))]
    if r in (4, 5):
        return ["list", items()]
    if r == 6:
        return ["tuple", items()]
    if r == 7:
        return ["named", items()]
    if r == 8:
        return ["listSub", items()]
    if r == 9:
        return ["tupleSub", items()]
    if r in (10, 11):
        return enumdc_ginst(rng, depth - 1)
    keys = {}
    for _ in range(rng.randrange(0, 3)):
        k = rng.choice([["atom", rng.randrange(0, 3)], ["str", "k"], ["copied", 1],
                        ["tuple", [["atom", rng.randrange(0, 2)]]],
                        ["inst", ["p"], [["atom", rng.randrange(0, 2)]]]])
        keys[str(k)] = k
    ks = list(keys.values())
    kind = ["dict", "dictSub", "defaultDict", "counter"][r - 12 if r <= 14 else 0]
    if rng.random() < .25:
        kind = "counter"
    elif rng.random() < .25:
        kind = "frozenDict"
    if kind == "counter":
        return [kind, ks, [["atom", rng.randrange(1, 3)] for _ in ks]]
    return [kind, ks, [enumdc_gdv(rng, depth - 1) for _ in ks]]


def enumdc_ginst(rng, depth):
    names = rng.sample(["p", "q", "r"], rng.randrange(0, 4))
    return ["inst", names, [enumdc_gdv(rng, depth) for _ in names]]


enumdc_ANNOTATIONS = ["", "  ", "[a]", ".a", "1", "a", "a.b", "a.b.c", "a.b.c.d", "a.x", "x", "x.y", " a . b [int]", "a\n.\tb",
                      "a.", "a..b", "a.b[int].c", "bad", "bad.x", "a.bad", "boom", "boom.x", "a.b -> c", "a b"]


def enumdc_gmisc(rng):
    r = rng.randrange(0, 9)
    if r == 7:
        return {"fn": "enumdc.dc_annotation", "s": rng.choice(enumdc_ANNOTATIONS)}
    if r == 8:
        return {"fn": "enumdc.dc_doc", "name": rng.choice(["C", "Point"]), "setfail": rng.random() < .15,
                "sig": rng.choice(["typeerror", "valueerror", "keyerror", "()", "(x: int) -> None", "(a, b) -> None -> None",
                                   "(x: 'int -> None') -> None"])}
    if r == 0:
        fs = [enumdc_gfield(rng, n, "plain") for n in rng.sample(["a", "b", "c", "d"], rng.randrange(0, 5))]
        return {"fn": "enumdc.dc_hash", "fields": fs}
    if r == 1:
        n = rng.randrange(0, 4)
        return {"fn": "enumdc.dc_eq", "terms": [rng.choice(["t", "t", "f", "raise"]) for _ in range(n)],
                "same": rng.random() < .1, "same_class": rng.random() < .85}
    if r == 2:
        n = rng.randrange(0, 4)
        a = [rng.randrange(0, 3) for _ in range(n)]
        return {"fn": "enumdc.dc_order", "a": a, "b": [rng.choice([x, rng.randrange(0, 3)]) for x in a],
                "op": rng.choice(["lt", "le", "gt", "ge"]), "same_class": rng.random() < .9}
    if r == 3:
        names = rng.sample(["a", "b", "c"], rng.randrange(0, 4))
        return {"fn": "enumdc.dc_frozen", "fields": names, "name": rng.choice(["a", "b", "z"]),
                "exact": rng.random() < .5, "del": rng.random() < .5}
    if r == 4:
        items = []
        for _ in range(rng.randrange(0, 4)):
            s = rng.choice(["a", "b", "a", "x1", "_y", "1a", "a-b", "", "class", "def", "None", "match", "type"])
            items.append(rng.choice([["name", s], ["named", s], ["name", s], ["named", s], ["notStr"], ["bad"]]))
        return {"fn": "enumdc.dc_make", "items": items}
    if r == 5:
        return {"fn": "enumdc.dc_asdict", "v": enumdc_ginst(rng, 3), "fact": rng.choice(["dict", "dictLike", "list"])}
    return {"fn": "enumdc.dc_astuple", "v": enumdc_ginst(rng, 3), "fact": rng.choice(["tuple", "list"])}


def enumdc_gen(rng):
    r0 = rng.randrange(0, 40)
    if r0 >= 33:
        return enumdc_gmisc(rng)
    if r0 >= 25:
        if r0 <= 26 and rng.random() < .6:
            return enumdc_gdcmro(rng)
        return enumdc_gdc(rng)
    if r0 <= 8:
        return enumdc_gclass(rng)
    if r0 == 9:
        return enumdc_gverify(rng)
    if r0 == 10:
        return enumdc_gupdate(rng)
    if r0 == 11:
        return enumdc_gcreate(rng)
    if r0 == 12:
        return {"fn": "enumdc.ec_scan",
                "bases": [rng.choice(["absent", "prop", "descr", "plain"]) for _ in range(rng.randrange(0, 5))]}
    if r0 == 13:
        return {"fn": "enumdc.ec_progress"} if rng.random() < .5 else {"fn": "enumdc.ec_verify_other"}
    if r0 <= 17:
        return enumdc_gflag(rng)
    r = rng.randrange(0, 12)
    if r <= 5:
        v = rng.randrange(-12, 20)
        w = rng.randrange(0, 16)
        base = {"members": rng.choice(enumdc_DEFS),
                "boundary": rng.choice(["strict", "conform", "eject", "keep"]), "v": v, "w": w}
        return {"fn": "enumdc." + ["flag_call", "flag_call", "flag_or", "flag_and", "flag_xor",
                                   "flag_invert"][r], **base}
    if r == 6:
        return {"fn": "enumdc.flag_iter", "members": rng.choice(enumdc_DEFS),
                "boundary": rng.choice(["strict", "conform", "keep"]), "v": rng.randrange(0, 16)}
    if r == 7:
        return {"fn": "enumdc.names", "s": rng.choice(["__a__", "_a_", "__", "___", "____", "_____",
                                                       "__a_", "_a__", "a", "", "_", "__ab__",
                                                       "_F__x", "_F__x__", "_F__x_", "_F__"])}
    if r == 8:
        n = rng.randrange(0, 40)
        return {"fn": "enumdc.bits", "n": n, "last": [rng.randrange(1, 9) for _ in range(rng.randrange(1, 4))],
                "count": rng.randrange(0, 3)}
    if r == 9:
        return {"fn": "enumdc.hash_action", "u": rng.random() < .5, "e": rng.random() < .5,
                "f": rng.random() < .5, "h": rng.random() < .5}
    fs = []
    for name in rng.sample(["a", "b", "c", "d"], rng.randrange(0, 5)):
        fs.append({"name": name, "default": rng.random() < .4, "init": rng.random() < .8,
                   "kw": rng.random() < .3})
    if r == 10:
        return {"fn": "enumdc.dc_init", "fields": fs}
    keep = [f for f in fs if f["init"]]
    return {"fn": "enumdc.dc_replace", "fields": fs,
            "changes": [f["name"] for f in rng.sample(fs, rng.randrange(0, len(fs) + 1))]}


def enumdc_make(fs):
    spec = []
    for f in fs:
        kw = {"init": f["init"], "kw_only": f["kw"]}
        if f["default"]:
            kw["default"] = 0
        spec.append((f["name"], int, enumdc_dc.field(**kw)))
    return enumdc_dc.make_dataclass("D", spec)


def enumdc_hash(case):
    u, e, f, h = case["u"], case["e"], case["f"], case["h"]
    ns = {"__hash__": (lambda s: 5)} if h else {}
    C = type("C", (), {"__annotations__": {"x": int}, **ns})
    try:
        D = enumdc_dc.dataclass(unsafe_hash=u, eq=e, frozen=f)(C)
    except TypeError:
        return {"ok": "exception"}
    v = D.__dict__.get("__hash__", "absent")
    if h:
        if v is ns["__hash__"]:
            return {"ok": "none"}
        return {"ok": "add"}
    if "__hash__" not in C.__dict__ or v == "absent":
        return {"ok": "none"}
    if v is None:
        return {"ok": "setNone" if e else "none"}
    return {"ok": "add"}


class enumdc_Descr:
    def __init__(self, i):
        self.i = i

    def __get__(self, obj, owner=None):
        return self


def enumdc_dec(v, cls="C"):
    k = v[0]
    if k == "int" or k == "str":
        return v[1]
    if k == "obj":
        return enumdc_OBJ[v[1]]
    if k == "list":
        return [v[1]]
    if k == "auto":
        return enumdc_enum.auto() if v[1] is None else enumdc_enum.auto(v[1])
    if k == "tup":
        return tuple(enumdc_dec(x, cls) for x in v[1])
    if k == "member":
        return enumdc_enum.member(enumdc_dec(v[1], cls))
    if k == "nonmember":
        return enumdc_enum.nonmember(enumdc_dec(v[1], cls))
    if k == "descr":
        return enumdc_Descr(v[1])
    if k == "inner":
        return type("Inner", (), {"__qualname__": str(cls) + ".Inner", "i": v[1]})
    if k == "names":
        return list(v[1])
    if k == "gen":
        g = v[1]
        if g[0] == "enum":
            return enumdc_enum.Enum._generate_next_value_
        if g[0] == "flag":
            return enumdc_enum.Flag._generate_next_value_
        if g[0] == "strEnum":
            return enumdc_enum.StrEnum._generate_next_value_
        if g[0] == "const":
            return lambda *a: enumdc_dec(g[1])

        def raiser(*a):
            raise {"ValueError": ValueError}[g[1]](g[2])
        return raiser
    raise ValueError(k)


def enumdc_enc(x):
    if isinstance(x, bool):
        raise ValueError(x)
    if isinstance(x, int):
        return ["int", x]
    if isinstance(x, str):
        return ["str", x]
    if isinstance(x, tuple):
        return ["tup", [enumdc_enc(i) for i in x]]
    if isinstance(x, list):
        if x and all(isinstance(i, int) for i in x):
            return ["list", x[0]]
        return ["names", list(x)]
    if isinstance(x, enumdc_Descr):
        return ["descr", x.i]
    if isinstance(x, (enumdc_enum.nonmember, enumdc_enum.member)):
        return None
    if isinstance(x, enumdc_enum.auto):
        return ["auto"]
    if isinstance(x, type) and hasattr(x, "i"):
        return ["inner", x.i]
    if x in enumdc_OBJ:
        return ["obj", enumdc_OBJ.index(x)]
    if callable(x) or isinstance(x, staticmethod):
        return ["gen"]
    raise ValueError(x)


def enumdc_summary(C):
    flag = issubclass(C, enumdc_enum.Flag)
    return [list(C._member_names_),
            [[n, m._name_, enumdc_enc(m._value_)] for n, m in C._member_map_.items()],
            [[enumdc_enc(k), m._name_] for k, m in C._value2member_map_.items()],
            [enumdc_enc(v) for v in C._hashable_values_], [enumdc_enc(v) for v in C._unhashable_values_],
            [[k if isinstance(k, str) else "?", [enumdc_enc(x) for x in l]]
             for k, l in C._unhashable_values_map_.items()],
            [C._flag_mask_, C._singles_mask_, C._all_bits_] if flag else None]


enumdc_BASE = {"plain": enumdc_enum.Enum, "flag": enumdc_enum.Flag, "strEnum": enumdc_enum.StrEnum}


def enumdc_build(case):
    base = enumdc_BASE[case["kind"]]
    op = case["op"]
    ns = enumdc_enum.EnumType.__prepare__("C", (base,))
    if op[0] == "call":
        miss = op[3]

        def _missing_(cls, value):
            if miss[0] == "none":
                return None
            if miss[0] == "other":
                return 42
            if miss[0] == "member":
                return cls[miss[1]]
            raise {"KeyError": KeyError, "ValueError": ValueError}[miss[1]](miss[2])
        ns["_missing_"] = classmethod(_missing_)
    for k, v in case["body"]:
        ns[k] = enumdc_dec(v)
    return enumdc_enum.EnumType("C", (base,), ns)


def enumdc_class(case):
    op = case["op"]
    k = op[0]

    def go():
        C = enumdc_build(case)
        if k == "summary":
            return enumdc_summary(C)
        if k == "call":
            if op[2] and not C._member_map_:
                return "functional"
            return C(enumdc_dec(op[1]), *[enumdc_dec(x) for x in op[2]])._name_
        if k == "callself":
            return C(C[op[1]])._name_
        if k == "contains":
            return enumdc_dec(op[1]) in C
        if k == "getitem":
            return C[op[1]]._name_
        if k == "iter":
            return [[m._name_ for m in C], [m._name_ for m in reversed(C)], len(C)]
        if k == "setattr":
            setattr(C, op[1], 1)
            return None
        if k == "delattr":
            delattr(C, op[1])
            return None
        if k == "alias":
            C[op[1]]._add_alias_(op[2])
            return enumdc_summary(C)
        if k == "valias":
            C[op[1]]._add_value_alias_(enumdc_dec(op[2]))
            return enumdc_summary(C)
        if k == "valias_call":
            C[op[1]]._add_value_alias_(enumdc_dec(op[2]))
            return C(enumdc_dec(op[2]))._name_
        if k == "unique":
            enumdc_enum.unique(C)
            return None
        checks = [{"unique": enumdc_enum.UNIQUE, "continuous": enumdc_enum.CONTINUOUS,
                   "named": enumdc_enum.NAMED_FLAGS}[k] for k in op[1]]
        enumdc_enum.verify(*checks)(C)
        return None
    return py_result(go)


def enumdc_update(case):
    def go():
        d = enumdc_enum.EnumDict(case["cls"])
        if case["gen"]:
            d._generate_next_value = enumdc_enum.Enum._generate_next_value_
        items = [(k, enumdc_dec(v, case["cls"])) for k, v in case["members"]]
        more = {k: enumdc_dec(v, case["cls"]) for k, v in case["more"]}
        d.update(dict(items) if case["mapping"] else items, **more)
        return [[[k, enumdc_enc(v)] for k, v in d.items()], d.member_names,
                [enumdc_enc(v) for v in d._last_values]]
    return py_result(go)


def enumdc_create(case):
    def go():
        base = enumdc_BASE[case["kind"]]
        kind, v = case["names"]
        names = [(k, enumdc_dec(x)) for k, x in v] if kind == "pairs" else v
        return enumdc_summary(base("C", names, start=case["start"]))
    return py_result(go)


def enumdc_scan(case):
    def go():
        mix = []
        for b in case["bases"]:
            ns = {"prop": {"P": enumdc_enum.property(lambda s: 1)}, "descr": {"P": enumdc_Descr(0)}, "plain": {"P": 5},
                  "absent": {}}[b]
            mix.append(type("M", (), ns))
        bases = tuple(mix) + (enumdc_enum.Enum,)
        ns = enumdc_enum.EnumType.__prepare__("E", bases)
        ns["A"] = 1
        E = enumdc_enum.EnumType("E", bases, ns)
        E.A._add_alias_("P")
        d = E.__dict__["P"]
        if isinstance(d, enumdc_enum.property):
            return [True, d._attr_type, E.__mro__[1:].index(d._cls_type)]
        return [False]
    return py_result(go)


def enumdc_new_in_progress():
    class E(enumdc_enum.Enum):
        def __new__(cls, v):
            return super().__new__(cls, v)
        A = 1
    return E.A._name_


def enumdc_flag(case):
    base = enumdc_enum.IntFlag if case["mixin"] else enumdc_enum.Flag
    members = [tuple(m) for m in case["members"]]
    F = base("F", members + [("NONE", None)] if case["self_none"] or case["other"][0] == "none" else members,
             boundary=enumdc_BOUND[case["boundary"]])
    op = case["op"]
    okind, ov = case["other"]

    def go():
        if op == "class_in":
            return (ov if okind != "other" else "x") in F
        self = F.NONE if case["self_none"] else F(case["v"])
        if not isinstance(self, F):
            return "skip"
        if op in ("or", "and", "xor", "in"):
            if okind == "other":
                other = "x"
            elif okind == "mixin":
                other = ov
            elif okind == "none":
                other = F.NONE
            else:
                other = F(ov)
                if not isinstance(other, F):
                    return "skip"
            if op == "in":
                if case["self_none"]:
                    return "skip"
                return F.__contains__(self, other)
            r = {"or": F.__or__, "and": F.__and__, "xor": F.__xor__}[op](self, other)
            if r is NotImplemented:
                return "NotImplemented"
            return enumdc_out(r, F)
        if op == "invert":
            a = ~self
            return [enumdc_out(a, F), (~self) is a]
        if case["self_none"]:
            return "skip"
        return bool(self)
    return py_result(go)


def enumdc_fld(f):
    kw = {"init": f["init"], "repr": f["repr"], "hash": f["hash"], "compare": f["compare"]}
    if f["kw"] is not None:
        kw["kw_only"] = f["kw"]
    if f["default"] is not None:
        kw["default"] = [f["default"]] if f["unhash"] else f["default"]
    if f["factory"] is not None:
        v = f["factory"]
        kw["default_factory"] = lambda: v
    return enumdc_dc.field(**kw)


def enumdc_ann(kind):
    import typing
    return {"plain": int, "classvar": typing.ClassVar[int], "initvar": enumdc_dc.InitVar[int],
            "kw": enumdc_dc.KW_ONLY}[kind]


def enumdc_user(*a, **k):
    return None


enumdc_user.user = True


def enumdc_mkbase(b):
    ns = {"__annotations__": {f["name"]: enumdc_ann(f["kind"]) for f in b["fields"]}}
    for f in b["fields"]:
        ns[f["name"]] = enumdc_fld(f)
    return enumdc_dc.dataclass(frozen=b["frozen"])(type("B", (), ns))


def enumdc_plain(x):
    return x[0] if isinstance(x, list) else x


def enumdc_obj(C, o, seen):
    post = seen.get("post")
    return [[enumdc_plain(getattr(o, f.name, "unset")) for f in enumdc_dc.fields(C)],
            None if post is None else [enumdc_plain(x) for x in post]]


def enumdc_dcclass(case):
    op = case["op"]
    p = case["params"]
    seen = {}

    def go():
        bases = tuple(enumdc_mkbase(b) for b in reversed(case["bases"]))
        anns = {}
        ns = {}
        for a in case["anns"]:
            anns[a["name"]] = enumdc_ann(a["kind"])
            at = a["attr"]
            if at[0] == "value":
                ns[a["name"]] = [at[1]] if at[2] else at[1]
            elif at[0] == "field":
                ns[a["name"]] = enumdc_fld(at[1])
        ns["__annotations__"] = anns
        if case["stray"]:
            ns[case["stray"]] = enumdc_dc.field()
        for n in case["defined"]:
            ns[n] = () if n == "__match_args__" else enumdc_user
        if case["hash"] is True:
            ns["__hash__"] = enumdc_user
        elif case["hash"] is False:
            ns["__hash__"] = None
        if case["has_slots"]:
            ns["__slots__"] = ()
        if case["post"]:
            def __post_init__(self, *a):
                seen["post"] = list(a)
            ns["__post_init__"] = __post_init__
        C = enumdc_dc.dataclass(**p)(type("C", bases, ns))
        if op[0] == "info":
            sig = []
            kwl = []
            if p["init"] or "__init__" in case["defined"]:
                pass
            fl = list(C.__dataclass_fields__.values())
            kinds = {enumdc_dc._FIELD: "plain", enumdc_dc._FIELD_CLASSVAR: "classVar",
                     enumdc_dc._FIELD_INITVAR: "initVar"}
            has = lambda f: f.default is not enumdc_dc.MISSING or f.default_factory is not enumdc_dc.MISSING
            all_ = [f for f in fl if f._field_type is not enumdc_dc._FIELD_CLASSVAR]
            std, kwo = enumdc_dc._fields_in_init_order(all_)
            hash_ = C.__dict__.get("__hash__", "absent")
            state = hash_ if hash_ == "absent" else ("None" if hash_ is None else
                                                     ("user" if hash_ is enumdc_user else "gen"))
            names = ["__init__", "__repr__", "__eq__", "__lt__", "__le__", "__gt__", "__ge__", "__setattr__",
                     "__delattr__"]
            gen = [n for n in names if n in C.__dict__ and C.__dict__[n] is not enumdc_user]
            return [[[f.name, "PyLean.CoreLibs.EnumDC.FKind." + kinds[f._field_type],
                      None if f.kw_only is enumdc_dc.MISSING else f.kw_only,
                      None if f.default is enumdc_dc.MISSING else enumdc_plain(f.default),
                      f.default_factory is not enumdc_dc.MISSING] for f in fl],
                    [[f.name, has(f)] for f in std], [[f.name, has(f)] for f in kwo],
                    None if "__match_args__" in case["defined"] or not p["match_args"]
                    else list(C.__match_args__), state, gen]
        o = C(*op[1], **dict(op[2]))
        if op[0] == "init":
            return enumdc_obj(C, o, seen)
        return enumdc_obj(C, enumdc_dc.replace(o, **dict(op[3])), seen)
    return py_result(go)


class enumdc_Cp:
    def __init__(self, n):
        self.n = n

    def __eq__(self, o):
        return isinstance(o, enumdc_Cp) and self.n == o.n

    def __hash__(self):
        return hash(("cp", self.n))


class enumdc_L(list):
    pass


class enumdc_T(tuple):
    pass


class enumdc_D(dict):
    pass


enumdc_INST = {}
enumdc_NT = {}


def enumdc_dv(v):
    k = v[0]
    if k == "atom" or k == "str":
        return v[1]
    if k == "copied":
        return enumdc_Cp(v[1])
    if k == "unhash":
        return {v[1]}
    if k in ("list", "tuple", "named", "listSub", "tupleSub"):
        l = [enumdc_dv(x) for x in v[1]]
        if k == "list":
            return l
        if k == "tuple":
            return tuple(l)
        if k == "listSub":
            return enumdc_L(l)
        if k == "tupleSub":
            return enumdc_T(l)
        n = len(l)
        if n not in enumdc_NT:
            enumdc_NT[n] = enumdc_collections.namedtuple("N", ["f%d" % i for i in range(n)])
        return enumdc_NT[n](*l)
    if k == "inst":
        key = tuple(v[1])
        if key not in enumdc_INST:
            enumdc_INST[key] = enumdc_dc.make_dataclass("I", list(key), frozen=True)
        return enumdc_INST[key](*[enumdc_dv(x) for x in v[2]])
    pairs = [(enumdc_dv(a), enumdc_dv(b)) for a, b in zip(v[1], v[2])]
    if k == "dict":
        return dict(pairs)
    if k == "dictSub":
        return enumdc_D(pairs)
    if k == "frozenDict":
        return frozendict(pairs)
    if k == "defaultDict":
        return enumdc_collections.defaultdict(int, pairs)
    return enumdc_collections.Counter(dict(pairs))


def enumdc_dvenc(x):
    enc = enumdc_dvenc
    if isinstance(x, int):
        return ["atom", x]
    if isinstance(x, str):
        return ["str", x]
    if isinstance(x, enumdc_Cp):
        return ["copied", x.n]
    if isinstance(x, set):
        return ["unhash", next(iter(x))]
    if isinstance(x, enumdc_L):
        return ["listSub", [enc(i) for i in x]]
    if isinstance(x, list):
        return ["list", [enc(i) for i in x]]
    if isinstance(x, enumdc_T):
        return ["tupleSub", [enc(i) for i in x]]
    if isinstance(x, tuple) and hasattr(x, "_fields"):
        return ["named", [enc(i) for i in x]]
    if isinstance(x, tuple):
        return ["tuple", [enc(i) for i in x]]
    name = ("counter" if isinstance(x, enumdc_collections.Counter) else
            "defaultDict" if isinstance(x, enumdc_collections.defaultdict) else
            "dictSub" if isinstance(x, enumdc_D) else
            "frozenDict" if isinstance(x, frozendict) else "dict")
    return [name, [enc(k) for k in x.keys()], [enc(v) for v in x.values()]]


class enumdc_Boom(BaseException):
    pass


class enumdc_Node:
    def __init__(self, **kw):
        self.__dict__.update(kw)


class enumdc_Bad:
    def __getattr__(self, name):
        raise ValueError("get")


class enumdc_BoomAttr:
    def __getattr__(self, name):
        raise enumdc_Boom("get")


enumdc_LEAF = enumdc_Node(tag="a.b.c")
enumdc_MID = enumdc_Node(tag="a.b", c=enumdc_LEAF)
enumdc_TOP = enumdc_Node(tag="a", b=enumdc_MID)
enumdc_ANNMOD = enumdc_types.ModuleType("enumdc_annmod")
enumdc_ANNMOD.a, enumdc_ANNMOD.bad, enumdc_ANNMOD.boom = enumdc_TOP, enumdc_Bad(), enumdc_BoomAttr()
enumdc_sys.modules["enumdc_annmod"] = enumdc_ANNMOD


def enumdc_annotation(case):
    class K:
        pass
    K.__module__ = "enumdc_annmod"
    try:
        r = enumdc_dc._get_type_from_annotation(case["s"], K)
    except enumdc_Boom as e:
        return {"exc": "Boom", "msg": str(e)}
    tag = {id(enumdc_ANNMOD.bad): "bad", id(enumdc_ANNMOD.boom): "boom"}.get(id(r))
    return {"ok": None if r is None else (tag or r.tag)}


def enumdc_doc(case):
    import inspect
    name, sig = case["name"], case["sig"]

    class Meta(type):
        def __setattr__(cls, k, v):
            if case["setfail"]:
                raise AttributeError("set")
            type.__setattr__(cls, k, v)
    K = Meta(name, (), {})

    def signature(c, annotation_format=None):
        if sig == "typeerror":
            raise TypeError("sig")
        if sig == "valueerror":
            raise ValueError("sig")
        if sig == "keyerror":
            raise KeyError("sig")
        return sig
    saved = inspect.signature
    inspect.signature = signature
    try:
        return py_result(lambda: enumdc_dc._auto_docstring.__get__(None, K))
    finally:
        inspect.signature = saved


def enumdc_dcmisc(case, fn):
    if fn == "dc_annotation":
        return enumdc_annotation(case)
    if fn == "dc_doc":
        return enumdc_doc(case)

    def go():
        if fn == "dc_hash":
            fs = case["fields"]
            for f in fs:
                f["default"] = None
                f["factory"] = None
                f["unhash"] = False
            ns = {"__annotations__": {f["name"]: int for f in fs}}
            C = enumdc_dc.make_dataclass("H", [(f["name"], int, enumdc_dc.field(hash=f["hash"], compare=f["compare"]))
                                               for f in fs], unsafe_hash=True)
            vals = {f["name"]: 1000 + i for i, f in enumerate(fs)}
            h = hash(C(*vals.values()))
            names = [f["name"] for f in fs]
            for m in range(2 ** len(names)):
                sub = [n for i, n in enumerate(names) if m >> i & 1]
                if hash(tuple(vals[n] for n in sub)) == h:
                    return sub
            return "none"
        if fn == "dc_eq":
            terms = case["terms"]

            class E:
                def __init__(self, t):
                    self.t = t

                def __eq__(self, o):
                    if self.t == "raise":
                        raise ValueError("eq")
                    return 1 if self.t == "t" else 0
            names = ["f%d" % i for i in range(len(terms))]
            C = enumdc_dc.make_dataclass("Q", names)
            a = C(*[E(t) for t in terms])
            if case["same"]:
                return int(C.__eq__(a, a))
            b = C(*[E(t) for t in terms]) if case["same_class"] else 3
            r = C.__eq__(a, b)
            return "NotImplemented" if r is NotImplemented else int(r)
        if fn == "dc_order":
            names = ["f%d" % i for i in range(len(case["a"]))]
            C = enumdc_dc.make_dataclass("O", names, order=True)
            a = C(*case["a"])
            b = C(*case["b"]) if case["same_class"] else 3
            r = getattr(C, "__%s__" % case["op"])(a, b)
            return "NotImplemented" if r is NotImplemented else r
        if fn == "dc_frozen":
            C = enumdc_dc.make_dataclass("F", case["fields"], frozen=True)
            G = C if case["exact"] else type("G", (C,), {})
            o = G(*[1 for _ in case["fields"]])
            n = case["name"]
            if case["del"]:
                if not case["exact"] and n not in case["fields"]:
                    object.__setattr__(o, n, 1)
                delattr(o, n)
            else:
                setattr(o, n, 1)
            return None
        if fn == "dc_make":
            items = []
            for i in case["items"]:
                if i[0] == "name":
                    items.append(i[1])
                elif i[0] == "named":
                    items.append((i[1], int))
                elif i[0] == "notStr":
                    items.append((1, int))
                else:
                    items.append(("a", int, enumdc_dc.field(), 1))
            return [f.name for f in enumdc_dc.fields(enumdc_dc.make_dataclass("X", items))]
        o = enumdc_dv(case["v"])
        if fn == "dc_asdict":
            fact = {"dict": dict, "dictLike": lambda p: dict(p), "list": list}[case["fact"]]
            return enumdc_dvenc(enumdc_dc.asdict(o, dict_factory=fact))
        return enumdc_dvenc(enumdc_dc.astuple(o, tuple_factory={"tuple": tuple, "list": list}[case["fact"]]))
    return py_result(go)


def enumdc_run(case):
    fn = case["fn"].split(".")[1]
    if fn == "dc_class":
        return enumdc_dcclass(case)
    if fn in ("dc_hash", "dc_eq", "dc_order", "dc_frozen", "dc_make", "dc_asdict", "dc_astuple", "dc_annotation", "dc_doc"):
        return enumdc_dcmisc(case, fn)
    if fn == "ec_class":
        return enumdc_class(case)
    if fn == "ec_update":
        return enumdc_update(case)
    if fn == "ec_create":
        return enumdc_create(case)
    if fn == "ec_scan":
        return enumdc_scan(case)
    if fn == "ec_progress":
        return py_result(enumdc_new_in_progress)
    if fn == "ec_flag":
        return enumdc_flag(case)
    if fn == "ec_verify_other":
        def go():
            enumdc_enum.verify(enumdc_enum.UNIQUE)(int)
        return py_result(go)
    if fn.startswith("flag_"):
        F = enumdc_cls(case)
        v, w = case["v"], case.get("w", 0)
        if fn == "flag_call":
            return py_result(lambda: enumdc_out(F(v), F))
        if fn == "flag_iter":
            def go():
                x = F(v)
                return [x.value, [m.name if m is not None else None for m in x], len(x)]
            return py_result(go)

        def binop(f):
            def go():
                a = F(v)
                if not isinstance(a, F):
                    return "skip"
                b = F(w)
                if not isinstance(b, F):
                    return "skip"
                return enumdc_out(f(a, b), F)
            return py_result(go)
        if fn == "flag_or":
            return binop(lambda a, b: a | b)
        if fn == "flag_and":
            return binop(lambda a, b: a & b)
        if fn == "flag_xor":
            return binop(lambda a, b: a ^ b)
        return binop(lambda a, b: ~a)
    if fn == "names":
        s = case["s"]
        return {"ok": [enumdc_enum._is_dunder(s), enumdc_enum._is_sunder(s),
                       enumdc_enum._is_private("F", s)]}
    if fn == "bits":
        n = case["n"]
        last = case["last"]
        return {"ok": [enumdc_enum.show_flag_values(n), enumdc_enum._is_single_bit(n),
                       enumdc_enum._high_bit(n),
                       enumdc_enum.Flag._generate_next_value_("x", None, case["count"], last),
                       enumdc_enum.Enum._generate_next_value_("x", 1, case["count"], last)]}
    if fn == "hash_action":
        return enumdc_hash(case)
    if fn == "dc_init":
        return py_result(lambda: [f.name for f in enumdc_dc.fields(enumdc_make(case["fields"]))])
    if fn == "dc_replace":
        def go():
            D = enumdc_make(case["fields"])
            o = object.__new__(D)
            for f in case["fields"]:
                setattr(o, f["name"], 1)
            ch = {k: 2 for k in case["changes"]}
            seen = {}
            orig = D.__init__

            def spy(self, **kw):
                seen.update(kw)
            D.__init__ = spy
            enumdc_dc.replace(o, **ch)
            return sorted(seen)
        return py_result(go)
    raise ValueError(fn)
# ====== END AREA enumdc ======

# ====== BEGIN AREA misc (Lib/contextlib.py, Lib/numbers.py, Lib/keyword.py, Lib/types.py, Lib/weakref.py, Lib/graphlib.py, Lib/sched.py, Lib/queue.py) ======
# Everything for this area stays between these two markers; prefix top-level names with misc_.
import graphlib as misc_graphlib  # noqa: E402


def misc_res(thunk):
    """One operation's outcome: ["ok", value] or ["exc", class, message]."""
    try:
        return ["ok", thunk()]
    except Exception as e:
        return ["exc", type(e).__name__, str(e)]


# --- graphlib ---

def misc_gl_dump(ts):
    return [[[i.node, i.npredecessors, list(i.successors)] for i in ts._node2info.values()],
            None if ts._ready_nodes is None else list(ts._ready_nodes),
            ts._npassedout, ts._nfinished]


def misc_gen_graphlib(rng):
    n = rng.choice([1, 2, 3, 4, 6, 8])
    nodes = list(range(n))
    def preds():
        return [rng.choice(nodes) for _ in range(rng.choice([0, 0, 1, 1, 2, 3]))]
    dag = rng.random() < 0.6
    def dag_preds(v):
        return [rng.randrange(v) for _ in range(rng.choice([0, 1, 1, 2]))] if v else []
    graph = None
    if rng.random() < 0.6:
        graph = []
        for v in rng.sample(nodes, rng.randint(0, n)):
            graph.append([v, dag_preds(v) if dag else preds()])
    ops = []
    for _ in range(rng.randint(0, 3)):
        v = rng.choice(nodes)
        ops.append(["add", v, dag_preds(v) if dag else preds()])
    style = rng.choice(["static", "drive", "drive", "chaos"])
    if style == "static":
        if rng.random() < 0.3:
            ops.append(["prepare"])
        ops.append(["static_order"])
        ops.append(["static_order"])
    elif style == "drive":
        ops.append(["prepare"])
        for _ in range(n + 2):
            ops.append(["is_active"])
            ops.append(["get_ready"])
            ops.append(["done_ready"])
        ops.append(["bool"])
    else:
        for _ in range(rng.randint(1, 12)):
            ops.append(rng.choice([
                ["prepare"], ["get_ready"], ["is_active"], ["bool"],
                ["done", [rng.choice(nodes + [99]) for _ in range(rng.randint(0, 3))]],
                ["add", rng.choice(nodes), preds()], ["done_ready"], ["static_order"]]))
    return {"fn": "misc.graphlib", "graph": graph, "ops": ops}


def misc_run_graphlib(case):
    graph = case["graph"]
    if graph is not None:
        graph = {k: v for k, v in graph}
    # The case's graph may repeat no key: rng.sample picks distinct nodes.
    ts = misc_graphlib.TopologicalSorter(graph)
    out = []
    last = []
    for op in case["ops"]:
        name = op[0]
        if name == "add":
            r = misc_res(lambda: ts.add(op[1], *op[2]))
        elif name == "prepare":
            r = misc_res(ts.prepare)
        elif name == "get_ready":
            r = misc_res(ts.get_ready)
            if r[0] == "ok":
                last = list(r[1])
                r = ["ok", last]
        elif name == "is_active":
            r = misc_res(ts.is_active)
        elif name == "bool":
            r = misc_res(lambda: bool(ts))
        elif name == "done":
            r = misc_res(lambda: ts.done(*op[1]))
        elif name == "done_ready":
            r = misc_res(lambda: ts.done(*last))
            last = []
        else:
            r = misc_res(lambda: list(ts.static_order()))
        out.append(r)
    out.append(misc_gl_dump(ts))
    return {"ok": out}


# --- sched ---

import sched as misc_sched  # noqa: E402


def misc_gen_sched(rng):
    def tv(strs=0.05):
        return "x" if rng.random() < strs else rng.choice([0, 0, 1, 1, 2, 3, 5, -1, 2**63, -2**64])
    def act(depth=0):
        k = rng.random()
        if k < 0.6 or depth > 1:
            return ["log", rng.randint(0, 9)]
        if k < 0.7:
            return ["boom"]
        if k < 0.85:
            return ["enterabs", tv(), tv(), act(depth + 1)]
        return ["cancel", rng.randint(0, 5)]
    def args():
        return [rng.randint(0, 3) for _ in range(rng.randint(0, 2))]
    def kw():
        return None if rng.random() < 0.7 else [["a", 1], ["b", rng.randint(0, 3)]][:rng.randint(0, 2)]
    ops = []
    for _ in range(rng.randint(1, 12)):
        k = rng.random()
        if k < 0.45:
            ops.append(["enterabs", tv(), tv(), act(), args(), kw()])
        elif k < 0.6:
            ops.append(["enter", rng.choice([0, 1, 2, 5, -1, "x"]) if rng.random() < .2 else rng.randint(0, 4),
                        tv(), act(), args(), kw()])
        elif k < 0.7:
            ops.append(["cancel", rng.randint(0, 6)])
        elif k < 0.75:
            ops.append(["empty"])
        elif k < 0.85:
            ops.append(["queue"])
        else:
            ops.append(["run", rng.random() < 0.3, rng.choice([None, None, 0, 1])])
    return {"fn": "misc.sched", "tick": rng.choice([0, 0, 1, 2]), "ops": ops}


def misc_run_sched(case):
    tick = case["tick"]
    w = {"clock": 0, "raise": None}
    log = []
    handles = []

    def timefunc():
        t = w["clock"]
        w["clock"] += tick
        return t

    def delayfunc(d):
        log.append(["delay", d])
        if w["raise"] is not None:
            if w["raise"] == 0:
                w["raise"] = None
                raise RuntimeError("delay failed")
            w["raise"] -= 1
            return
        if isinstance(d, int):
            w["clock"] += d

    sc = misc_sched.scheduler(timefunc, delayfunc)

    def action(a):
        tag = a[1] if a[0] == "log" else a[0]
        def f(*args, **kwargs):
            log.append(["call", tag, list(args), [list(kv) for kv in kwargs.items()]])
            if a[0] == "boom":
                raise RuntimeError("action failed")
            if a[0] == "enterabs":
                handles.append(sc.enterabs(a[1], a[2], action(a[3])))
            if a[0] == "cancel" and a[1] < len(handles):
                sc.cancel(handles[a[1]])
        return f

    def ev5(ev):
        return [ev.time, ev.priority, ev.sequence, list(ev.argument), [list(kv) for kv in ev.kwargs.items()]]

    def ev3(ev):
        return [ev.time, ev.priority, ev.sequence]

    out = []
    for op in case["ops"]:
        name = op[0]
        if name in ("enterabs", "enter"):
            kw = {} if op[5] is None else {"kwargs": dict(op[5])}
            f = sc.enterabs if name == "enterabs" else sc.enter
            def thunk():
                ev = f(op[1], op[2], action(op[3]), tuple(op[4]), **kw)
                handles.append(ev)
                return ev5(ev)
            r = misc_res(thunk)
        elif name == "cancel":
            r = misc_res(lambda: sc.cancel(handles[op[1]])) if op[1] < len(handles) else ["ok", None]
        elif name == "empty":
            r = misc_res(sc.empty)
        elif name == "queue":
            r = misc_res(lambda: [ev3(e) for e in sc.queue])
        else:
            w["raise"] = op[2]
            r = misc_res(lambda: sc.run(op[1]))
            w["raise"] = None
        out.append(r)
    out.append([[ev3(e) for e in sc._queue], next(sc._sequence_generator), w["clock"], log])
    return {"ok": out}


# --- queue ---

import queue as misc_queue  # noqa: E402


def misc_gen_queue(rng):
    cls = rng.choice(["fifo", "fifo", "lifo", "prio", "prio", "pysimple", "csimple"])
    simple = cls.endswith("simple")
    maxsize = rng.choice([0, 0, -1, 1, 2, 3, 5, 2**63])
    def item():
        return "x" if rng.random() < (0.1 if cls == "prio" else 0.02) else rng.randint(-3, 9)
    def tmo():
        return rng.choice([None, None, None, -1, 0, 1])
    def blk():
        return rng.random() < 0.6
    ops = []
    for _ in range(rng.randint(1, 16)):
        k = rng.random()
        if k < 0.3:
            ops.append(["put", item(), blk(), tmo()])
        elif k < 0.55:
            ops.append(["get", blk(), tmo()])
        elif k < 0.65:
            ops.append(["put_nowait", item()])
        elif k < 0.75:
            ops.append(["get_nowait"])
        elif k < 0.8:
            ops.append(["qsize"])
        elif k < 0.85:
            ops.append(["empty"])
        elif simple:
            ops.append(["qsize"])
        elif k < 0.9:
            ops.append(["full"])
        elif k < 0.94:
            ops.append(["task_done"])
        elif k < 0.97:
            ops.append(["join"])
        else:
            ops.append(["shutdown", rng.random() < 0.5])
    return {"fn": "misc.queue", "cls": cls, "maxsize": maxsize, "ops": ops}


def misc_run_queue(case):
    cls = case["cls"]
    simple = cls.endswith("simple")
    if cls == "pysimple":
        q = misc_queue._PySimpleQueue()
    elif cls == "csimple":
        q = misc_queue.SimpleQueue()
    else:
        q = {"fifo": misc_queue.Queue, "lifo": misc_queue.LifoQueue,
             "prio": misc_queue.PriorityQueue}[cls](case["maxsize"])
    blocked = ["exc", "<blocks forever>", ""]
    def secs(t):
        return None if t is None else t * 1e-5
    out = []
    for op in case["ops"]:
        name = op[0]
        if name == "put":
            if not simple and not q.is_shutdown and q.maxsize > 0 and op[2] and op[3] is None and q.qsize() >= q.maxsize:
                r = blocked
            else:
                r = misc_res(lambda: q.put(op[1], op[2], secs(op[3])))
        elif name == "get":
            shut = not simple and q.is_shutdown
            if not shut and op[1] and op[2] is None and q.qsize() == 0:
                r = blocked
            else:
                r = misc_res(lambda: q.get(op[1], secs(op[2])))
        elif name == "put_nowait":
            r = misc_res(lambda: q.put_nowait(op[1]))
        elif name == "get_nowait":
            r = misc_res(q.get_nowait)
        elif name == "join":
            r = blocked if q.unfinished_tasks else misc_res(q.join)
        elif name == "shutdown":
            r = misc_res(lambda: q.shutdown(op[1]))
        else:
            r = misc_res(getattr(q, name))
        out.append(r)
    if cls == "pysimple":
        out.append([list(q._queue), q._count._value])
    elif cls == "csimple":
        out.append([q.get_nowait() for _ in range(q.qsize())])
    else:
        out.append([list(q.queue), q.unfinished_tasks, q.is_shutdown])
    return {"ok": out}


# --- numbers ---

import math as misc_math  # noqa: E402
import numbers as misc_numbers  # noqa: E402

MISC_NUM_STUBS = {
    "Complex": ["__complex__", "real", "imag", "__add__", "__radd__", "__neg__", "__pos__",
                "__mul__", "__rmul__", "__truediv__", "__rtruediv__", "__pow__", "__rpow__",
                "__abs__", "conjugate", "__eq__"],
    "Real": ["__float__", "__trunc__", "__floor__", "__ceil__", "__round__", "__floordiv__",
             "__rfloordiv__", "__mod__", "__rmod__", "__lt__", "__le__"],
    "Rational": ["numerator", "denominator"],
    "Integral": ["__int__", "__pow__", "__lshift__", "__rlshift__", "__rshift__", "__rrshift__",
                 "__and__", "__rand__", "__xor__", "__rxor__", "__or__", "__ror__", "__invert__"],
}
MISC_NUM_MIXINS = ["Complex.__bool__", "Complex.__sub__", "Complex.__rsub__", "Real.__divmod__",
                   "Real.__rdivmod__", "Real.__complex__", "Real.real", "Real.imag",
                   "Real.conjugate", "Rational.__float__", "Integral.__index__",
                   "Integral.__float__", "Integral.numerator", "Integral.denominator"]
MISC_NUM_UNARY = {"__complex__", "real", "imag", "__neg__", "__pos__", "__abs__", "conjugate",
                  "__float__", "__trunc__", "__floor__", "__ceil__", "__round__", "numerator",
                  "denominator", "__int__", "__invert__"}
MISC_NUM_FAIL = ["__eq__", "__add__", "__neg__", "__pos__", "__floordiv__", "__mod__", "__float__",
                 "__int__", "numerator", "denominator"]


def misc_num_ops(base):
    """A concrete subclass of `base` wrapping an int; `fail` names methods that raise."""
    names = set()
    for c in base.__mro__:
        names |= set(getattr(c, "__abstractmethods__", ()))

    def check(self, name):
        if name in self.fail:
            raise ArithmeticError(name)

    def val(x):
        return x.v if hasattr(x, "v") else x

    impl = {
        "__eq__": lambda s, o: s.v == val(o),
        "__add__": lambda s, o: s.wrap(s.v + val(o)),
        "__neg__": lambda s: s.wrap(-s.v),
        "__pos__": lambda s: s.wrap(s.v),
        "__floordiv__": lambda s, o: s.wrap(s.v // val(o)),
        "__mod__": lambda s, o: s.wrap(s.v % val(o)),
        "__float__": lambda s: float(s.v),
        "__int__": lambda s: s.v,
    }
    ns = {"__slots__": ("v", "fail", "num", "den"), "__hash__": None}

    def init(self, v, fail=(), num=None, den=None):
        self.v, self.fail, self.num, self.den = v, fail, num, den
    ns["__init__"] = init
    ns["wrap"] = lambda self, v: type(self)(v, self.fail, self.num, self.den)

    def make(name):
        f = impl.get(name)

        def m(self, *a):
            check(self, name)
            if f is None:
                raise AssertionError("unexpected primitive " + name)
            return f(self, *a)
        return m

    for n in names | set(impl):
        if n in ("real", "imag", "numerator", "denominator"):
            continue
        ns[n] = make(n)
    if issubclass(base, misc_numbers.Rational) and not issubclass(base, misc_numbers.Integral):
        def num(self):
            check(self, "numerator")
            return self.num

        def den(self):
            check(self, "denominator")
            return self.den
        ns["numerator"] = property(num)
        ns["denominator"] = property(den)
    return type("Misc" + base.__name__, (base,), ns)


MISC_NUM_CLASSES = {b.__name__: misc_num_ops(b) for b in
                    (misc_numbers.Real, misc_numbers.Rational, misc_numbers.Integral)}


def misc_sf(x):
    neg = misc_math.copysign(1.0, x) < 0
    if x == 0:
        return [neg, 0, 0]
    m, e = misc_math.frexp(abs(x))
    return [neg, int(m * 2 ** 53), e - 53]


def misc_gen_numbers(rng):
    a = rng.choice([0, 1, -1, 2, -2, 3, 7, -7, 2 ** 53 + 1, 2 ** 63, -2 ** 64, rng.randint(-50, 50)])
    b = rng.choice([0, 1, -1, 2, -2, 3, 7, -7, 2 ** 53 + 1, 2 ** 63, -2 ** 64, rng.randint(-50, 50)])
    if rng.random() < 0.4:
        cls = rng.choice(list(MISC_NUM_STUBS))
        m = cls + "." + rng.choice(MISC_NUM_STUBS[cls])
    else:
        m = rng.choice(MISC_NUM_MIXINS)
    fail = [n for n in MISC_NUM_FAIL if rng.random() < 0.15]
    return {"fn": "misc.numbers", "m": m, "a": a, "b": b, "fail": fail}


def misc_run_numbers(case):
    cname, meth = case["m"].split(".")
    a, b, fail = case["a"], case["b"], case["fail"]
    cls = getattr(misc_numbers, cname)
    conc = MISC_NUM_CLASSES[{"Complex": "Real"}.get(cname, cname)]
    fail = frozenset(fail)
    if case["m"] == "Rational.__float__":
        x = conc(a, fail, a, b)
        def enc(v):
            return misc_sf(v)
    else:
        x = conc(a, fail)
        def enc(v):
            if hasattr(v, "v"):
                return v.v
            if isinstance(v, tuple):
                return [e.v for e in v]
            if isinstance(v, float):
                return misc_sf(v)
            if isinstance(v, complex):
                return [misc_sf(v.real), misc_sf(v.imag)]
            return v
    y = conc(b, fail)
    f = cls.__dict__[meth]
    if isinstance(f, property):
        f = f.fget
    if meth in MISC_NUM_UNARY or case["m"] == "Complex.__bool__" or meth == "__index__":
        return {"ok": misc_res(lambda: enc(f(x)))}
    return {"ok": misc_res(lambda: enc(f(x, y)))}


# --- keyword ---

import keyword as misc_keyword  # noqa: E402


def misc_gen_keyword(rng):
    pool = misc_keyword.kwlist + misc_keyword.softkwlist
    s = rng.choice(pool)
    k = rng.random()
    if k < 0.3:
        s = s + rng.choice(["", "x", " ", "_"])
    elif k < 0.4:
        s = s.upper()
    elif k < 0.5:
        s = rng.choice(["", "print", "exec", "self", "match_", "__debug__", "nonlocal ", "é"])
    return {"fn": "misc.keyword", "s": s}


def misc_run_keyword(case):
    s = case["s"]
    return {"ok": [misc_keyword.iskeyword(s), misc_keyword.issoftkeyword(s),
                   misc_keyword.kwlist, misc_keyword.softkwlist]}


# --- types ---

import abc as misc_abc  # noqa: E402
import collections.abc as misc_cabc  # noqa: E402
import types as misc_types  # noqa: E402


class MiscM0(type):
    def __new__(mcs, name, bases, ns, **kw):
        ns = dict(ns)
        ns["_b"] = bases
        ns["_kw"] = sorted(kw)
        return super().__new__(mcs, name, bases, ns)

    def __init__(cls, name, bases, ns, **kw):
        super().__init__(name, bases, ns)


class MiscM1(MiscM0):
    @classmethod
    def __prepare__(mcs, name, bases, **kw):
        d = {"prep:" + mcs.__name__[4:]: 1}
        d.update((k, 1) for k in kw)
        return d


class MiscM2(MiscM1):
    pass


class MiscM3(MiscM0):
    pass


class MiscM4(MiscM1, MiscM3):
    pass


MISC_METAS = [type, MiscM1, MiscM2, MiscM3, MiscM4]
MISC_META_IDX = {m: i for i, m in enumerate(MISC_METAS)}
MISC_CLS = [MISC_METAS[i]("C" + str(i), (), {}) for i in range(5)]


class MiscPlain:
    pass


class MiscE(MiscPlain):
    def __mro_entries__(self, bases):
        return self.new


class MiscB(MiscPlain):
    def __mro_entries__(self, bases):
        return [object]


class MiscR(MiscPlain):
    def __mro_entries__(self, bases):
        raise RuntimeError("entries failed")


MISC_PLAIN = [MiscPlain, MiscE, MiscB, MiscR]


def misc_ob(spec):
    k = spec[0]
    if k == "m":
        return MISC_METAS[spec[1]]
    if k == "c":
        return MISC_CLS[spec[1]]
    if k == "o":
        return MiscPlain()
    if k == "e":
        e = MiscE()
        e.new = tuple(misc_ob(s) for s in spec[1])
        return e
    if k == "b":
        return MiscB()
    if k == "r":
        return MiscR()
    if k == "f":
        def fm(name, bases, ns, **kw):
            return [["f"], name, [misc_ob_enc(b) for b in bases], misc_ns_keys(ns), sorted(kw)]
        return fm
    if k == "p":
        class P:
            def __call__(self, name, bases, ns, **kw):
                return [["p"], name, [misc_ob_enc(b) for b in bases], misc_ns_keys(ns), sorted(kw)]
            def __prepare__(self, name, bases, **kw):
                d = {"prep:P": 1}
                d.update((k, 1) for k in kw)
                return d
        return P()
    raise AssertionError(k)


def misc_ob_enc(o):
    if isinstance(o, type):
        if o in MISC_META_IDX:
            return ["m", MISC_META_IDX[o]]
        if o in MISC_CLS:
            return ["c", MISC_CLS.index(o)]
        return ["c", 100 + MISC_PLAIN.index(o)]
    if isinstance(o, MiscPlain):
        return {MiscPlain: ["o"], MiscE: ["e"], MiscB: ["b"], MiscR: ["r"]}[type(o)]
    return ["p"] if hasattr(o, "__prepare__") else ["f"]


def misc_ns_keys(ns):
    return sorted(k for k in ns if k.startswith("prep:") or k in ("__orig_bases__", "body", "extra"))


def misc_gen_types(rng):
    def base(depth=0):
        k = rng.random()
        if k < 0.5 or depth > 1:
            return ["c", rng.randint(0, 4)]
        if k < 0.6:
            return ["o"]
        if k < 0.85:
            return ["e", [base(depth + 1) for _ in range(rng.randint(0, 2))]]
        return rng.choice([["b"], ["r"]]) if rng.random() < 0.5 else ["c", 0]
    def bases():
        return [base() for _ in range(rng.choice([0, 1, 1, 2, 2, 3]))]
    def kwds():
        k = rng.random()
        if k < 0.3:
            return None
        d = []
        if rng.random() < 0.6:
            d.append(["metaclass", rng.choice([["m", rng.randint(0, 4)], ["f"], ["p"]])])
        if rng.random() < 0.4:
            d.append(["extra", ["c", 0]])
            d = rng.sample(d, len(d))
        return d
    kind = rng.choice(["resolve", "update", "calc", "prepare", "new", "new", "orig", "dca",
                       "wrapper", "coroutine"])
    case = {"fn": "misc.types", "k": kind}
    if kind in ("resolve", "update"):
        case["bases"] = bases()
    elif kind == "calc":
        case["meta"] = ["m", rng.randint(0, 4)]
        case["bases"] = [["c", rng.randint(0, 4)] if rng.random() < .9 else ["o"]
                         for _ in range(rng.randint(0, 3))]
    elif kind in ("prepare", "new"):
        case["name"] = "N"
        case["bases"] = bases()
        case["kwds"] = kwds()
        if kind == "new":
            case["body"] = rng.random() < 0.5
    elif kind == "orig":
        t = rng.choice(["t", "t", "t", "int", "slots"])
        if t == "t":
            case.update(typeName="MiscObj", hasDict=True, orig=rng.choice([None, 1]),
                        bases=rng.choice([None, 2, 2]))
        elif t == "int":
            case.update(typeName="int", hasDict=False, orig=None, bases=None)
        else:
            case.update(typeName="MiscSlots", hasDict=False, orig=None, bases=None)
    elif kind == "dca":
        fn = lambda: rng.choice([None, 0, 1, 2, 3])
        case["init"] = [fn(), fn(), fn(), rng.choice([None, None, "", "D"])]
        case["ops"] = [rng.choice([["get", True], ["get", False], ["set"], ["delete"],
                                   ["getter", rng.randint(0, 3)], ["setter", rng.randint(0, 3)],
                                   ["deleter", rng.randint(0, 3)]])
                       for _ in range(rng.randint(0, 6))]
    elif kind == "wrapper":
        case["items"] = [rng.randint(1, 9) for _ in range(rng.randint(0, 3))]
        case["isgen"] = True
        case["ops"] = [rng.choice([["next"], ["next"], ["send", 0], ["send", 1], ["throw"],
                                   ["close"], ["attrs"], ["iter"]])
                       for _ in range(rng.randint(1, 7))]
    else:
        case["kind"] = rng.choice(["notcallable", "gen", "async", "itercoro", "plain",
                                   "callable_gen", "ret_abc_gen", "ret_coro", "ret_itercoro",
                                   "ret_abc_both"])
    return case


class MiscAbcGen(misc_cabc.Generator):
    def send(self, v):
        raise StopIteration

    def throw(self, *a):
        raise StopIteration


class MiscAbcBoth(misc_cabc.Generator):
    def send(self, v):
        raise StopIteration

    def throw(self, *a):
        raise StopIteration

    def __await__(self):
        return iter(())


misc_cabc.Coroutine.register(MiscAbcBoth)


def misc_coroutine(kind):
    def g():
        yield 1
    async def a():
        pass
    @misc_types.coroutine
    def ic():
        yield 1
    class CallGen:
        def __call__(self):
            return g()
    def a2():
        c = a()
        c.close()
        return c
    f = {"notcallable": 5, "gen": g, "async": a, "itercoro": ic, "plain": lambda: 5,
         "callable_gen": CallGen(), "ret_abc_gen": lambda: MiscAbcGen(), "ret_coro": a2,
         "ret_itercoro": lambda: ic(), "ret_abc_both": lambda: MiscAbcBoth()}[kind]
    def run():
        r = misc_types.coroutine(f)
        if r is f and kind == "gen":
            return ["flagged", bool(r.__code__.co_flags & 0x100)]
        if r is f:
            return ["same"]
        v = r()
        return ["wrapped", "wrap" if isinstance(v, misc_types._GeneratorWrapper) else "pass"]
    return misc_res(run)


def misc_run_types(case):
    k = case["k"]
    if k == "resolve":
        bases = tuple(misc_ob(s) for s in case["bases"])
        def run():
            r = misc_types.resolve_bases(bases)
            return ["same"] if r is bases else ["new", [misc_ob_enc(b) for b in r]]
        return {"ok": misc_res(run)}
    if k == "update":
        bases = tuple(misc_ob(s) for s in case["bases"])
        def body():
            pass
        def rec(name, bs, ns):
            return bs, ("__orig_bases__" in ns)
        def run():
            bs, orig = __build_class__(body, "N", *bases, metaclass=rec)
            return ["new", [misc_ob_enc(b) for b in bs]] if orig else ["same"]
        return {"ok": misc_res(run)}
    if k == "calc":
        meta = misc_ob(case["meta"])
        bases = tuple(misc_ob(s) for s in case["bases"])
        return {"ok": misc_res(lambda: misc_ob_enc(misc_types._calculate_meta(meta, bases)))}
    if k == "prepare":
        bases = tuple(misc_ob(s) for s in case["bases"])
        kw = None if case["kwds"] is None else {a: misc_ob(b) for a, b in case["kwds"]}
        def run():
            m, ns, kwds = misc_types.prepare_class("N", bases, kw)
            return [misc_ob_enc(m), sorted(ns), sorted(kwds)]
        return {"ok": misc_res(run)}
    if k == "new":
        bases = tuple(misc_ob(s) for s in case["bases"])
        kw = None if case["kwds"] is None else {a: misc_ob(b) for a, b in case["kwds"]}
        body = (lambda ns: ns.__setitem__("body", 1)) if case["body"] else None
        def run():
            r = misc_types.new_class("N", bases, kw, body)
            if isinstance(r, list):
                return r
            d = r.__dict__
            b = d["_b"] if "_b" in d else (() if r.__bases__ == (object,) else r.__bases__)
            return [misc_ob_enc(type(r)), r.__name__, [misc_ob_enc(x) for x in b],
                    misc_ns_keys(d), d.get("_kw", [])]
        return {"ok": misc_res(run)}
    if k == "orig":
        if case["typeName"] == "int":
            obj = 5
        elif case["typeName"] == "MiscSlots":
            obj = type("MiscSlots", (), {"__slots__": ()})()
        else:
            obj = type("MiscObj", (), {})()
            if case["orig"] is not None:
                obj.__orig_bases__ = case["orig"]
            if case["bases"] is not None:
                obj.__bases__ = case["bases"]
        return {"ok": misc_res(lambda: misc_types.get_original_bases(obj))}
    if k == "dca":
        fs = []
        for i, (doc, abstract) in enumerate([(None, False), ("d1", False), ("", False), ("a", True)]):
            def f(*a, i=i):
                return ["got", i] if len(a) == 1 and a[0] == "inst" else None
            f.__doc__ = doc
            if abstract:
                f.__isabstractmethod__ = True
            fs.append(f)
        def fn(i):
            return None if i is None else fs[i]
        def dump(d):
            def idx(f):
                return None if f is None else fs.index(f)
            return [idx(d.fget), idx(d.fset), idx(d.fdel), d.__doc__, d.overwrite_doc,
                    d.__isabstractmethod__]
        i = case["init"]
        d = misc_types.DynamicClassAttribute(fn(i[0]), fn(i[1]), fn(i[2]), i[3])
        out = [dump(d)]
        for op in case["ops"]:
            if op[0] == "get":
                r = misc_res(lambda: d.__get__("inst" if op[1] else None, object))
                if r[0] == "ok" and r[1] is d:
                    r = ["ok", "self"]
                out.append(r)
            elif op[0] == "set":
                out.append(misc_res(lambda: d.__set__("inst", 1)))
            elif op[0] == "delete":
                out.append(misc_res(lambda: d.__delete__("inst")))
            else:
                d = getattr(d, op[0])(fs[op[1]])
                out.append(dump(d))
        return {"ok": out}
    if k == "wrapper":
        items = case["items"]
        def g():
            for x in items:
                yield x
        g.__qualname__ = "g"
        gen = g()
        w = misc_types._GeneratorWrapper(gen)
        out = []
        for op in case["ops"]:
            name = op[0]
            if name == "next":
                r = misc_res(lambda: next(w))
            elif name == "send":
                r = misc_res(lambda: w.send(op[1] or None))
            elif name == "throw":
                r = misc_res(lambda: w.throw(ValueError("thrown")))
            elif name == "close":
                r = misc_res(lambda: 0 if w.close() is None else 1)
            elif name == "attrs":
                r = [["ok", 1 if w.gi_code is g.__code__ else 0],
                     ["ok", 1 if w.gi_frame is not None else 0],
                     ["ok", 1 if w.gi_running else 0],
                     ["ok", 1 if w.gi_yieldfrom is not None else 0],
                     ["ok", 1 if w.gi_suspended else 0], w.__name__, w.__qualname__,
                     ["ok", w.gi_state], ["ok", w.cr_state]]
            else:
                r = "wrapped" if iter(w) is gen else "self"
            out.append(r)
        return {"ok": out}
    return {"ok": misc_coroutine(case["kind"])}


# --- contextlib ---

import contextlib as misc_contextlib  # noqa: E402

sys.unraisablehook = lambda unraisable: None  # generators dropped mid-script


class MiscRt(RuntimeError):
    pass


class BadInit(Exception):
    def __init__(self):
        raise ValueError("init failed")


class MiscEG(ExceptionGroup):
    pass


MISC_EXC = {c.__name__: c for c in
            (ValueError, KeyError, LookupError, RuntimeError, MiscRt, StopIteration,
             StopAsyncIteration, GeneratorExit, KeyboardInterrupt, BadInit)}


def misc_run_co(coro):
    """Drive a coroutine that never suspends."""
    try:
        coro.send(None)
    except StopIteration as e:
        return e.value
    raise AssertionError("coroutine suspended")


def misc_gen_of(script):
    def gen():
        thrown = None
        for step in script:
            k = step[0]
            if k == "y":
                try:
                    yield step[1]
                    thrown = None
                except BaseException as e:
                    thrown = e
            elif k == "ret":
                return
            elif k == "raise":
                raise MISC_EXC[step[1]]("gen")
            else:
                if thrown is not None:
                    raise thrown
                raise RuntimeError("nothing")
    return gen


def misc_agen_of(script):
    async def gen():
        thrown = None
        for step in script:
            k = step[0]
            if k == "y":
                try:
                    yield step[1]
                    thrown = None
                except BaseException as e:
                    thrown = e
            elif k == "ret":
                return
            elif k == "raise":
                raise MISC_EXC[step[1]]("gen")
            else:
                if thrown is not None:
                    raise thrown
                raise RuntimeError("nothing")
    return gen


def misc_arg0(e):
    return e.args[0] if e.args and isinstance(e.args[0], str) else ""


def misc_desc(e, labels, d=3):
    if e is None:
        return None
    if d == 0:
        return "..."
    for o, l in labels:
        if o is e:
            return l
    return [type(e).__name__, misc_arg0(e), misc_desc(e.__cause__, labels, d - 1),
            misc_desc(e.__context__, labels, d - 1)]


def misc_cres(thunk, labels):
    try:
        return ["ok", thunk()]
    except BaseException as e:
        return ["exc", misc_desc(e, labels)]


def misc_some_tb():
    try:
        raise ValueError
    except ValueError as e:
        return e.__traceback__


def misc_gen_ctx(rng):
    excs = ["ValueError", "KeyError", "RuntimeError", "MiscRt", "StopIteration",
            "StopAsyncIteration", "GeneratorExit", "KeyboardInterrupt"]
    def step():
        k = rng.random()
        if k < 0.45:
            return ["y", rng.randint(1, 9)]
        if k < 0.6:
            return ["ret"]
        if k < 0.8:
            return ["reraise"]
        return ["raise", rng.choice(excs)]
    def script():
        s = [["y", 1]] if rng.random() < 0.8 else []
        return s + [step() for _ in range(rng.randint(0, 3))]
    def body():
        return None if rng.random() < 0.4 else rng.choice(excs)
    kind = rng.choice(["gcm", "gcm", "gcm", "with", "deco", "suppress", "stack", "stack",
                       "redirect", "chdir", "hook", "closing", "null"])
    case = {"fn": "misc.ctx", "k": kind}
    if kind == "gcm":
        case["async"] = rng.random() < 0.4
        case["script"] = script()
        ops = [["enter"]] if rng.random() < 0.9 else []
        for _ in range(rng.choice([1, 1, 1, 2])):
            k = rng.random()
            if k < 0.3:
                ops.append(["exit_none"])
            elif k < 0.8:
                ops.append(["exit_inst", rng.choice(excs), rng.random() < 0.5])
            else:
                ops.append(["exit_type", rng.choice(excs + ["BadInit"])])
        if rng.random() < 0.1:
            ops.append(["enter"])
        case["ops"] = ops
    elif kind in ("with", "deco"):
        case["async"] = rng.random() < 0.4
        case["script"] = script()
        case["body"] = body()
    elif kind == "suppress":
        names = ["ValueError", "KeyError", "RuntimeError", "KeyboardInterrupt"]
        def tree(d=0):
            if d < 2 and rng.random() < 0.5 or d == 0 and rng.random() < .7:
                kids = [tree(d + 1) for _ in range(rng.randint(1, 3))]
                has_base = misc_tree_base(kids)
                c = "BaseExceptionGroup" if has_base else rng.choice(["ExceptionGroup", "MiscEG", "BaseExceptionGroup"])
                return ["group", c, kids]
            return ["leaf", rng.choice(names)]
        case["classes"] = rng.sample(names + ["LookupError", "ExceptionGroup", "BaseExceptionGroup"],
                                     rng.randint(0, 3))
        case["tree"] = tree()
        case["with"] = rng.random() < 0.5
    elif kind == "stack":
        a = rng.random() < 0.4
        case["async"] = a
        def beh(d=0):
            k = rng.random()
            if k < 0.45:
                return ["ret", rng.random() < 0.4]
            if k < 0.7:
                return ["raise", rng.choice(excs)]
            if k < 0.85 or d > 0:
                return ["reraise"]
            return ["pushcb", beh(1), rng.randint(50, 60)]
        ops = []
        for i in range(rng.randint(0, 5)):
            k = rng.random()
            asy = a and rng.random() < 0.5
            if k < 0.25:
                ops.append(["push_fn", i, beh(), asy])
            elif k < 0.5:
                ops.append([rng.choice(["push_cm", "push_cm", "push_static"]), i, beh(), asy,
                            rng.choice(["static", "class", "noget"])])
                if rng.random() < .1:
                    ops.append(["push_descfail", asy])
            elif k < 0.75:
                ops.append(["callback", i, beh(), asy])
            elif k < 0.9:
                ops.append(["enter_ctx", i, beh(), rng.randint(0, 9), rng.random() < 0.2, a])
            else:
                ops.append(["enter_bad", a, rng.choice(["none", "noexit", "enterfail", "exitfail"])])
            if rng.random() < 0.1:
                ops.append(["pop_all"])
        if rng.random() < 0.8:
            exc = None if rng.random() < 0.4 else rng.choice(excs)
            ops.append(["exit", exc, exc is not None and rng.random() < 0.5])
        else:
            ops.append(["close"])
        case["ops"] = ops
    elif kind == "redirect":
        case["ops"] = [[rng.choice(["enter", "enter", "exit"]), rng.randint(0, 1)]
                       for _ in range(rng.randint(1, 7))]
    elif kind == "chdir":
        case["paths"] = [rng.choice(["/usr", "/", "/nonexistent", "."]) for _ in range(2)]
        case["ops"] = [[rng.choice(["enter", "enter", "exit"]), rng.randint(0, 1)]
                       for _ in range(rng.randint(1, 7))]
    elif kind == "hook":
        a = rng.random() < 0.5
        ms = ["__aenter__", "__aexit__"] if a else ["__enter__", "__exit__"]
        case["async"] = a
        case["exact"] = rng.random() < 0.8
        case["mro"] = [[[m, rng.random() < 0.3] for m in ms if rng.random() < 0.6]
                       for _ in range(rng.randint(1, 3))] + [[]]
    elif kind == "closing":
        case["fail"] = rng.random() < 0.3
        case["body"] = body()
    else:
        case["v"] = rng.randint(0, 9)
        case["body"] = body()
    return case


def misc_tree_base(kids):
    for k in kids:
        if k[0] == "leaf" and k[1] == "KeyboardInterrupt":
            return True
        if k[0] == "group" and (k[1] == "BaseExceptionGroup" and misc_tree_base(k[2])):
            return True
    return False


def misc_build_tree(t):
    if t[0] == "leaf":
        return MISC_EXC[t[1]]("leaf")
    cls = {"ExceptionGroup": ExceptionGroup, "BaseExceptionGroup": BaseExceptionGroup,
           "MiscEG": MiscEG}[t[1]]
    return cls("g", [misc_build_tree(c) for c in t[2]])


def misc_tree_enc(e, orig):
    if e is orig:
        return "orig"
    if isinstance(e, BaseExceptionGroup):
        return [type(e).__name__, e.message, [misc_tree_enc(c, orig) for c in e.exceptions]]
    return [type(e).__name__, misc_arg0(e)]


class MiscNoCM:
    pass


class MiscRaisingDescr:
    def __get__(self, o, t=None):
        raise ValueError("descr")


class MiscNoExit:
    def __enter__(self):
        raise AssertionError("not reached")

    async def __aenter__(self):
        raise AssertionError("not reached")


class MiscEnterFail:
    __enter__ = __aenter__ = MiscRaisingDescr()
    __exit__ = __aexit__ = MiscRaisingDescr()


class MiscExitFail:
    def __enter__(self):
        raise AssertionError("not reached")

    async def __aenter__(self):
        raise AssertionError("not reached")

    __exit__ = __aexit__ = MiscRaisingDescr()


class MiscPushFail:
    __exit__ = __aexit__ = MiscRaisingDescr()


def misc_raw_exit(f, kind):
    """A class whose `__exit__` reaches `_descriptor_get` as a class, as an object with no `__get__`, or as a staticmethod."""
    if kind == "class":
        class Raw:
            def __new__(cls, *a):
                return f(*a)
    elif kind == "noget":
        class Call:
            def __call__(self, *a):
                return f(*a)
        Raw = Call()
    else:
        Raw = staticmethod(f)

    class S:
        __exit__ = __aexit__ = Raw
    return S


def misc_stack_fn(run, log, tag, stack_ref):
    def f(*a):
        return run(a[1] if len(a) >= 2 else None)
    return f


def misc_run_stack(case):
    a = case["async"]
    Stack = misc_contextlib.AsyncExitStack if a else misc_contextlib.ExitStack
    box = [Stack()]
    log = []
    labels = []

    def behave(i, b, tag, d):
        log.append([i, tag, misc_desc(d, labels, 1)])
        if b[0] == "ret":
            return b[1]
        if b[0] == "raise":
            raise MISC_EXC[b[1]]("cb")
        if b[0] == "reraise":
            if d is not None:
                raise d
            raise RuntimeError("nothing")
        i2, b2 = b[2], b[1]
        def f(*x):
            return behave(i2, b2, "s", x[1] if len(x) > 1 else None)
        box[0].push(f)
        return False

    def afn(i, b):
        async def f(*x):
            return behave(i, b, "a", x[1] if len(x) > 1 else None)
        return f

    def fn(i, b):
        def f(*x):
            return behave(i, b, "s", x[1] if len(x) > 1 else None)
        return f

    def cm(i, b, v=None, fails=False):
        class C:
            def __enter__(self):
                if fails:
                    raise ValueError("enter")
                return v

            def __exit__(self, *x):
                return behave(i, b, "s", x[1])
        return C()

    def acm(i, b, v=None, fails=False):
        class C:
            async def __aenter__(self):
                if fails:
                    raise ValueError("enter")
                return v

            async def __aexit__(self, *x):
                return behave(i, b, "a", x[1])
        return C()

    out = []
    for op in case["ops"]:
        k = op[0]
        if k == "push_fn":
            if op[3]:
                box[0].push_async_exit(afn(op[1], op[2]))
            else:
                box[0].push(fn(op[1], op[2]))
            out.append(op[1])
        elif k == "push_cm":
            box[0].push_async_exit(acm(op[1], op[2])) if op[3] else box[0].push(cm(op[1], op[2]))
            out.append(op[1])
        elif k == "push_static":
            S = misc_raw_exit((afn if op[3] else fn)(op[1], op[2]), op[4])
            if op[3]:
                box[0].push_async_exit(S())
            else:
                box[0].push(S())
            out.append(op[1])
        elif k == "push_descfail":
            if op[1]:
                out.append(misc_cres(lambda: box[0].push_async_exit(MiscPushFail()) and None, labels))
            else:
                out.append(misc_cres(lambda: box[0].push(MiscPushFail()) and None, labels))
        elif k == "callback":
            if op[3]:
                box[0].push_async_callback(afn(op[1], op[2]))
            else:
                box[0].callback(fn(op[1], op[2]))
            out.append(op[1])
        elif k == "enter_ctx":
            i, b, v, fails, is_async = op[1], op[2], op[3], op[4], op[5]
            if is_async:
                c = acm(i, b, v, fails)
                out.append(misc_cres(lambda: misc_run_co(box[0].enter_async_context(c)), labels))
            else:
                c = cm(i, b, v, fails)
                out.append(misc_cres(lambda: box[0].enter_context(c), labels))
        elif k == "enter_bad":
            bad = {"none": MiscNoCM, "noexit": MiscNoExit, "enterfail": MiscEnterFail, "exitfail": MiscExitFail}[op[2]]
            if op[1]:
                out.append(misc_cres(lambda: misc_run_co(box[0].enter_async_context(bad())), labels))
            else:
                out.append(misc_cres(lambda: box[0].enter_context(bad()), labels))
        elif k == "pop_all":
            old = box[0]
            box[0] = old.pop_all()
            out.append(len(old._exit_callbacks))
        elif k == "exit":
            exc = None if op[1] is None else MISC_EXC[op[1]]("body")
            if exc is not None:
                labels.append((exc, "value"))
            details = (None, None, None) if exc is None else (type(exc), exc, exc.__traceback__)
            def call():
                if a:
                    return misc_run_co(box[0].__aexit__(*details))
                return box[0].__exit__(*details)
            def run():
                if op[2]:
                    try:
                        raise exc
                    except BaseException:
                        return bool(call())
                return bool(call())
            out.append(misc_cres(run, labels))
        else:
            if a:
                out.append(misc_cres(lambda: misc_run_co(box[0].aclose()), labels))
            else:
                out.append(misc_cres(box[0].close, labels))
    return {"ok": [out, log, len(box[0]._exit_callbacks)]}


def misc_run_ctx(case):
    k = case["k"]
    if k == "gcm":
        a = case["async"]
        g = (misc_agen_of if a else misc_gen_of)(case["script"])
        cm = (misc_contextlib.asynccontextmanager if a else misc_contextlib.contextmanager)(g)()
        labels = []
        out = []
        for op in case["ops"]:
            n = op[0]
            if n == "enter":
                out.append(misc_cres((lambda: misc_run_co(cm.__aenter__())) if a else cm.__enter__, labels))
            elif n == "exit_none":
                def r():
                    v = misc_run_co(cm.__aexit__(None, None, None)) if a else cm.__exit__(None, None, None)
                    return v
                out.append(misc_cres(r, labels))
            elif n == "exit_inst":
                c = MISC_EXC[op[1]]
                v = c("body")
                labels.append((v, "value"))
                tb = misc_some_tb() if op[2] else None
                def r():
                    return misc_run_co(cm.__aexit__(c, v, tb)) if a else cm.__exit__(c, v, tb)
                out.append(misc_cres(r, labels))
                out.append(v.__traceback__ is tb)
            else:
                c = MISC_EXC[op[1]]
                def r():
                    return misc_run_co(cm.__aexit__(c, None, None)) if a else cm.__exit__(c, None, None)
                out.append(misc_cres(r, labels))
        frame = cm.gen.ag_frame if a else cm.gen.gi_frame
        finished = frame is None
        out.append(finished)
        return {"ok": out}
    if k == "with":
        a = case["async"]
        g = (misc_agen_of if a else misc_gen_of)(case["script"])
        cm = (misc_contextlib.asynccontextmanager if a else misc_contextlib.contextmanager)(g)()
        body = case["body"]
        def run():
            if a:
                async def co():
                    async with cm:
                        if body is None:
                            return 1
                        raise MISC_EXC[body]("body")
                return misc_run_co(co())
            with cm:
                if body is None:
                    return 1
                raise MISC_EXC[body]("body")
        r = misc_cres(run, [])
        frame = cm.gen.ag_frame if a else cm.gen.gi_frame
        return {"ok": [r, frame is None]}
    if k == "deco":
        a = case["async"]
        g = (misc_agen_of if a else misc_gen_of)(case["script"])
        cm = (misc_contextlib.asynccontextmanager if a else misc_contextlib.contextmanager)(g)()
        body = case["body"]
        if a:
            async def f():
                if body is None:
                    return 1
                raise MISC_EXC[body]("body")
            d = cm(f)
            return {"ok": [misc_cres(lambda: misc_run_co(d()), []), misc_cres(lambda: misc_run_co(d()), [])]}
        def f():
            if body is None:
                return 1
            raise MISC_EXC[body]("body")
        d = cm(f)
        return {"ok": [misc_cres(d, []), misc_cres(d, [])]}
    if k == "suppress":
        cs = {"ValueError": ValueError, "KeyError": KeyError, "RuntimeError": RuntimeError,
              "KeyboardInterrupt": KeyboardInterrupt, "LookupError": LookupError,
              "ExceptionGroup": ExceptionGroup, "BaseExceptionGroup": BaseExceptionGroup}
        s = misc_contextlib.suppress(*[cs[c] for c in case["classes"]])
        e = misc_build_tree(case["tree"])
        try:
            if case["with"]:
                try:
                    raise e
                except BaseException:
                    r = s.__exit__(type(e), e, None)
            else:
                r = s.__exit__(type(e), e, None)
            return {"ok": ["ok", r]}
        except BaseException as x:
            ctx = x.__context__
            return {"ok": ["exc", misc_tree_enc(x, e), None if ctx is None else misc_tree_enc(ctx, e), x is e]}
    if k == "stack":
        return misc_run_stack(case)
    if k == "redirect":
        objs = [object(), object(), object()]
        rs = [misc_contextlib.redirect_stdout(objs[1]), misc_contextlib.redirect_stdout(objs[2])]
        saved = sys.stdout
        sys.stdout = objs[0]
        out = []
        try:
            for op in case["ops"]:
                r = rs[op[1]]
                if op[0] == "enter":
                    out.append(objs.index(r.__enter__()))
                else:
                    try:
                        r.__exit__(None, None, None)
                        out.append(objs.index(sys.stdout))
                    except IndexError as e:
                        out.append(["exc", "IndexError", str(e)])
                out.append([objs.index(sys.stdout), [objs.index(o) for o in rs[0]._old_targets],
                            [objs.index(o) for o in rs[1]._old_targets]])
        finally:
            sys.stdout = saved
        return {"ok": out}
    if k == "chdir":
        saved = os.getcwd()
        os.chdir("/")
        cs = [misc_contextlib.chdir(p) for p in case["paths"]]
        out = []
        try:
            for op in case["ops"]:
                c = cs[op[1]]
                if op[0] == "enter":
                    out.append(misc_res(c.__enter__))
                else:
                    out.append(misc_res(lambda: c.__exit__(None, None, None)))
                out.append(os.getcwd())
        finally:
            os.chdir(saved)
        return {"ok": out}
    if k == "hook":
        bases = ()
        for d in reversed(case["mro"][:-1]):
            bases = (type("K", bases, {m: (None if isn else (lambda self: None)) for m, isn in d}),)
        cls = bases[0]
        base = misc_contextlib.AbstractAsyncContextManager if case["async"] else misc_contextlib.AbstractContextManager
        hook = base if case["exact"] else type("Sub", (base,), {"__exit__": None, "__aexit__": None})
        r = hook.__subclasshook__(cls)
        return {"ok": None if r is NotImplemented else r}
    if k == "closing":
        n = [0]
        fail = case["fail"]
        class T:
            def close(self):
                n[0] += 1
                if fail:
                    raise ValueError("close")
        body = case["body"]
        def run():
            with misc_contextlib.closing(T()):
                if body is None:
                    return 1
                raise MISC_EXC[body]("body")
        r = misc_cres(run, [])
        return {"ok": [r, n[0]]}
    body = case["body"]
    def run():
        with misc_contextlib.nullcontext(case["v"]) as v:
            if body is None:
                return v
            raise MISC_EXC[body]("body")
    return {"ok": misc_cres(run, [])}


# --- weakref ---

import copy as misc_copy  # noqa: E402
import gc as misc_gc  # noqa: E402
import weakref as misc_weakref  # noqa: E402


class MiscW:
    def __init__(self, i, val):
        self.i, self.val = i, val

    def __eq__(self, other):
        return isinstance(other, MiscW) and self.val == other.val

    def __hash__(self):
        return hash(self.val)

    def __deepcopy__(self, memo):
        return self

    def m(self):
        pass


class MiscU:
    """Weakly referenceable, `__eq__` and no `__hash__`."""
    def __init__(self, i):
        self.i = i

    def __eq__(self, other):
        return self is other


for misc_c in ("MiscU",):
    globals()[misc_c].__module__ = "builtins"


class MiscHK:
    def __init__(self, i):
        self.i = i

    def __hash__(self):
        raise KeyError("h")


class MiscHV:
    def __init__(self, i):
        self.i = i

    def __hash__(self):
        raise ValueError("h")


class MiscEV:
    def __init__(self, i):
        self.i = i

    def __hash__(self):
        return 7

    def __eq__(self, other):
        raise ValueError("eqv")


class MiscN:
    def __init__(self, i):
        self.i = i

    def __hash__(self):
        return 7

    def __eq__(self, other):
        return False


def misc_wkd_objs(vals):
    objs = {i: MiscW(i, vals[i]) for i in range(4)}
    objs.update({4: MiscU(4), 5: MiscHK(5), 6: MiscHV(6), 7: MiscEV(7), 8: MiscEV(8), 9: MiscN(9)})
    return objs


class misc_KT:
    """A `WeakValueDictionary` key whose `__hash__` raises `TypeError`."""
    name = "T"

    def __hash__(self):
        raise TypeError("custom")

    def __repr__(self):
        return self.name


misc_KT.__name__ = misc_KT.__qualname__ = "HashTE"
misc_KT.__module__ = "builtins"


class misc_KH:
    def __init__(self, name, exc):
        self.name, self.exc = name, exc

    def __hash__(self):
        raise self.exc("h")

    def __repr__(self):
        return self.name


class misc_KE:
    def __init__(self, name):
        self.name = name

    def __hash__(self):
        return 7

    def __eq__(self, other):
        if self.name.startswith("EK"):
            raise KeyError("eq")
        if self.name.startswith("EV"):
            raise ValueError("eqv")
        return False

    def __repr__(self):
        return self.name

    def __deepcopy__(self, memo):
        return self


def misc_wvd_keys():
    keys = {"U": [1], "T": misc_KT(), "HK": misc_KH("HK", KeyError), "HV": misc_KH("HV", ValueError)}
    keys.update({n: misc_KE(n) for n in ["EK1", "EK2", "EV1", "EV2", "N1", "N2"]})
    return keys


MISC_WSPECIAL = ["U", "T", "HK", "HV", "EK1", "EK2", "EV1", "EV2", "N1", "N2"]


def misc_pv(o):
    return ["o", o.i] if hasattr(o, "i") else ["i", o]


def misc_gen_weakref(rng):
    kind = rng.choice(["wvd", "wvd", "wvd", "wkd", "wkd", "wkd", "wm", "keyed", "fin", "fin"])
    case = {"fn": "misc.weakref", "k": kind}
    n = 4
    case["vals"] = [rng.randint(0, 3) for _ in range(n + 16)]

    def pv():
        return ["o", rng.randrange(n)] if rng.random() < 0.9 else ["i", rng.randint(0, 3)]

    def key():
        return rng.choice(MISC_WSPECIAL) if rng.random() < 0.25 else rng.choice("abc")

    def kpv():
        return ["o", rng.randrange(10)] if rng.random() < 0.9 else ["i", 1]

    def other(items):
        r = rng.random()
        if r < 0.1:
            return None
        if r < 0.45:
            return ["map", items()]
        if r < 0.7:
            return ["seq", items()]
        return rng.choice([["hasattr"], ["itemsraise"], ["itemsmid", items()], ["notiter"],
                           ["badlen", items(), rng.randint(0, 3)], ["notseq", items(), rng.randint(0, 3)]])

    def gens(ops, kinds, nops):
        for _ in range(rng.randint(0, 3)):
            pos = rng.randint(0, len(ops))
            ops.insert(pos, ["gen", rng.choice(kinds)])
        ng = sum(1 for o in ops if o[0] == "gen")
        if ng:
            for _ in range(rng.randint(0, nops)):
                ops.insert(rng.randint(0, len(ops)), ["next", rng.randrange(ng)])
        # number the generators in creation order
        g = 0
        for o in ops:
            if o[0] == "gen":
                o.append(g)
                g += 1
        return ops

    if kind == "wvd":
        def items():
            return [[key(), pv()] for _ in range(rng.randint(0, 3))]
        case["eager"] = rng.random() < 0.6
        case["init"] = [[rng.choice("abc"), ["o", rng.randrange(n)]] for _ in range(rng.randint(0, 3))]
        ops = []
        for _ in range(rng.randint(1, 12)):
            kw = [[k, ["o", rng.randrange(n)]] for k in rng.sample("abc", rng.randint(0, 2))]
            ops.append(rng.choice([
                ["set", key(), pv()], ["set", key(), pv()], ["get_", key()], ["del", key()], ["len"],
                ["in", key()], ["copy"], ["deepcopy"], ["get", key(), pv()], ["vrefs"], ["popitem"],
                ["pop", key(), [pv() for _ in range(rng.randint(0, 3))]], ["setdefault", key(), pv()],
                ["update", other(items), kw], ["ior", other(items)],
                ["or", rng.choice([None, items()])], ["ror", rng.choice([None, items()])],
                ["kill", rng.randrange(n)], ["kill", rng.randrange(n)]]))
        case["ops"] = gens(ops, ["items", "keys", "values", "irefs"], 6)
    elif kind == "wkd":
        def items():
            return [[kpv(), rng.randint(0, 3)] for _ in range(rng.randint(0, 3))]
        case["eager"] = rng.random() < 0.6
        case["init"] = [[["o", rng.randrange(n)], rng.randint(0, 3)] for _ in range(rng.randint(0, 3))]
        ops = []
        for _ in range(rng.randint(1, 12)):
            ops.append(rng.choice([
                ["set", kpv(), rng.randint(0, 3)], ["set", kpv(), 1], ["get_", kpv()], ["del", kpv()],
                ["len"], ["copy"], ["deepcopy"], ["get", kpv(), 9], ["in", kpv()],
                ["krefs"], ["popitem"],
                ["pop", kpv(), [9, 8, 7][:rng.randint(0, 3)]], ["setdefault", kpv(), 7],
                ["update", other(items), rng.random() < 0.2], ["ior", other(items)],
                ["or", rng.choice([None, items()])], ["ror", rng.choice([None, items()])],
                ["kill", rng.randrange(10)], ["kill", rng.randrange(10)]]))
        case["ops"] = gens(ops, ["items", "keys", "values"], 6)
    elif kind == "wm":
        case["eqm"] = [rng.choice([0, 0, 1, 2, 3, 4]) for _ in range(n)]
        case["nem"] = [rng.choice([0, 0, 1, 2]) for _ in range(n)]
        ops = []
        for _ in range(rng.randint(1, 10)):
            i, j = rng.randrange(3), rng.randrange(3)
            ops.append(rng.choice([
                ["new", rng.randrange(n), 10 + rng.randrange(2), rng.random() < 0.5],
                ["new", rng.randrange(n), 10 + rng.randrange(2), rng.random() < 0.5],
                ["bad", rng.choice(["int", "onlyself", "raiseself", "funcint", "plain"])],
                ["call", i], ["eq", i, j], ["ne", i, j], ["eqo", i], ["alive", i],
                ["kill", rng.choice([rng.randrange(n), 10 + rng.randrange(2)])]]))
        case["ops"] = ops
    elif kind == "keyed":
        case["v"] = pv()
    else:
        spawned = [99]  # a finalizer is an object: each spawn gets an id of its own

        def fs(d=0):
            k = rng.random()
            if k < 0.45 or d > 1:
                return ["ret", rng.randint(0, 9)]
            if k < 0.6:
                return ["boom"]
            if k < 0.68:
                return ["boom2"]
            if k < 0.78:
                return ["base"]
            spawned[0] += 1
            return ["spawn", spawned[0], rng.randrange(n), fs(d + 1)]
        ops = []
        fid = 0
        for _ in range(rng.randint(1, 12)):
            k = rng.random()
            if k < 0.35:
                ops.append([rng.choice(["new", "new", "newsub"]), fid, pv(), fs()])
                fid += 1
            else:
                f = rng.randrange(fid + 1)
                ops.append(rng.choice([["call", f], ["detach", f], ["peek", f], ["alive", f],
                                       ["atexit", f],
                                       ["set_atexit", f, rng.choice([True, False, "bad", "s"])],
                                       ["repr", f], ["kill", rng.randrange(n)],
                                       ["kill", rng.randrange(n)], ["exit"]]))
        if rng.random() < 0.5:
            ops.append(["exit"])
        case["ops"] = ops
    return case


def misc_eres(thunk):
    try:
        return ["ok", thunk()]
    except Exception as e:
        return ["exc", type(e).__name__, str(e)]


class misc_BadHas:
    def __getattr__(self, name):
        raise ValueError("ga")


class misc_ItemsRaise:
    def items(self):
        raise ValueError("items")


class misc_ItemsMid:
    def __init__(self, items):
        self._items = items

    def items(self):
        yield from self._items
        raise ValueError("mid")


def misc_other(spec, conv):
    """The `other` of an update: `conv` turns a JSON item into a Python pair."""
    if spec is None:
        return None
    t = spec[0]
    if t == "map":
        return misc_MappingItems([conv(x) for x in spec[1]])
    if t == "seq":
        return [conv(x) for x in spec[1]]
    if t == "hasattr":
        return misc_BadHas()
    if t == "itemsraise":
        return misc_ItemsRaise()
    if t == "itemsmid":
        return misc_ItemsMid([conv(x) for x in spec[1]])
    if t == "notiter":
        return 5
    l = [conv(x) for x in spec[1]]
    pos = min(spec[2], len(l))
    l.insert(pos, (1, 2, 3) if t == "badlen" else 5)
    return l


def misc_other_items(spec):
    if spec is None or spec[0] in ("hasattr", "itemsraise", "notiter"):
        return []
    return spec[1]


def misc_wvd_kname(k):
    return k if isinstance(k, str) else ("U" if isinstance(k, list) else k.name)


class misc_Gens:
    """Generators of a script, with the object each one's frame holds."""
    def __init__(self):
        self.gens = []

    def held(self, i):
        return any(h == i for _, _, h in self.gens)

    def next(self, idx, enc):
        if idx >= len(self.gens):
            return "skip"
        g, kind, _ = self.gens[idx]
        try:
            y = next(g)
        except StopIteration:
            self.gens[idx][2] = None
            return "stop"
        j, h = enc(kind, y)
        self.gens[idx][2] = h
        return j


def misc_run_wvd(case, objs):
    dead = set()
    keys = misc_wvd_keys()
    gens = misc_Gens()

    def k_(name):
        return keys.get(name, name)

    def val(p):
        return objs[p[1]] if p[0] == "o" else p[1]

    def isdead(p):
        return p[0] == "o" and p[1] in dead

    def anydead(l):
        return any(isdead(v) for _, v in (l or []))

    def conv(x):
        return (k_(x[0]), val(x[1]))

    def dump(x):
        return [[misc_wvd_kname(k), misc_pv(v)] for k, v in x.items()]

    def enc(kind, y):
        if kind == "items":
            return [misc_wvd_kname(y[0]), misc_pv(y[1])], y[1].i
        if kind == "keys":
            return misc_wvd_kname(y), None
        if kind == "values":
            return misc_pv(y), y.i
        o = y()
        return [None if o is None else misc_pv(o)], None
    WVD = misc_weakref.WeakValueDictionary
    try:
        init = [(k, val(v)) for k, v in case["init"]]
        if case["eager"]:
            d = WVD(init)
        else:
            d = WVD()
            d._remove = lambda wr: None
            d.update(init)
        del init
    except TypeError as e:
        return {"ok": [["exc", "TypeError", str(e)]]}
    out = []
    for op in case["ops"]:
        n = op[0]
        if n == "set":
            r = "skip" if isdead(op[2]) else misc_eres(lambda: d.__setitem__(k_(op[1]), val(op[2])))
        elif n == "get_":
            r = misc_eres(lambda: misc_pv(d[k_(op[1])]))
        elif n == "del":
            r = misc_eres(lambda: d.__delitem__(k_(op[1])))
        elif n == "len":
            r = len(d)
        elif n == "in":
            r = misc_eres(lambda: k_(op[1]) in d)
        elif n == "copy":
            r = misc_eres(lambda: dump(d.copy()))
        elif n == "deepcopy":
            r = misc_eres(lambda: dump(misc_copy.deepcopy(d)))
        elif n == "get":
            r = "skip" if isdead(op[2]) else misc_eres(lambda: misc_pv(d.get(k_(op[1]), val(op[2]))))
        elif n == "vrefs":
            r = [None if x() is None else misc_pv(x()) for x in d.valuerefs()]
        elif n == "popitem":
            def f():
                k, v = d.popitem()
                return [misc_wvd_kname(k), misc_pv(v)]
            r = misc_eres(f)
        elif n == "pop":
            r = "skip" if any(isdead(a) for a in op[2]) else \
                misc_eres(lambda: misc_pv(d.pop(k_(op[1]), *[val(a) for a in op[2]])))
        elif n == "setdefault":
            r = "skip" if isdead(op[2]) else misc_eres(lambda: misc_pv(d.setdefault(k_(op[1]), val(op[2]))))
        elif n == "update":
            if anydead(misc_other_items(op[1]) + op[2]):
                r = "skip"
            else:
                kw = {k: val(v) for k, v in op[2]}
                r = misc_eres(lambda: d.update(misc_other(op[1], conv), **kw))
                del kw
        elif n == "ior":
            r = "skip" if anydead(misc_other_items(op[1])) else \
                misc_eres(lambda: (d.__ior__(misc_other(op[1], conv)), None)[1])
        elif n in ("or", "ror"):
            if anydead(op[1]):
                r = "skip"
            else:
                def f():
                    o = 5 if op[1] is None else misc_MappingItems([conv(x) for x in op[1]])
                    v = getattr(d, "__" + n + "__")(o)
                    return "NotImplemented" if v is NotImplemented else dump(v)
                r = misc_eres(f)
                if r == ["ok", "NotImplemented"]:
                    r = "NotImplemented"
        elif n == "gen":
            m = {"items": d.items, "keys": d.keys, "values": d.values, "irefs": d.itervaluerefs}
            gens.gens.append([m[op[1]](), op[1], None])
            r = None
        elif n == "next":
            r = gens.next(op[1], enc)
        else:
            if gens.held(op[1]):
                r = "held"
            else:
                dead.add(op[1])
                objs.pop(op[1], None)
                r = None
        out.append(r)
    out.append([[misc_wvd_kname(k), None if wr() is None else misc_pv(wr())] for k, wr in d.data.items()])
    return {"ok": out}


class misc_MappingItems(misc_cabc.Mapping):
    """A Mapping that keeps a list of items, repeated keys included, like the model's `other`."""

    def __init__(self, items):
        self._items = list(items)

    def __getitem__(self, k):
        for a, b in self._items:
            if a == k:
                return b
        raise KeyError(k)

    def __iter__(self):
        seen = []
        for a, _ in self._items:
            if a not in seen:
                seen.append(a)
        return iter(seen)

    def __len__(self):
        return len(list(iter(self)))

    def items(self):
        return list(self._items)


def misc_run_wkd(case, objs):
    dead = set()
    gens = misc_Gens()

    def key(p):
        return objs[p[1]] if p[0] == "o" else p[1]

    def isdead(p):
        return p[0] == "o" and p[1] in dead

    def conv(x):
        return (key(x[0]), x[1])

    def anydead(l):
        return any(isdead(k) for k, _ in (l or []))

    def dump(x):
        return [[misc_pv(k), v] for k, v in x.items()]

    def res(thunk):
        r = misc_eres(thunk)
        if r[0] == "exc" and r[1] == "KeyError" and "weakref" in r[2]:
            r[2] = "~"
        return r

    def enc(kind, y):
        if kind == "items":
            return [misc_pv(y[0]), y[1]], y[0].i
        if kind == "keys":
            return misc_pv(y), y.i
        return y, None
    WKD = misc_weakref.WeakKeyDictionary
    init = misc_MappingItems([(key(k), v) for k, v in case["init"]])
    if case["eager"]:
        d = WKD(init)
    else:
        d = WKD()
        d._remove = lambda wr: None
        d.update(init)
    del init
    out = []
    for op in case["ops"]:
        n = op[0]
        if n in ("set", "get_", "del", "get", "in", "pop", "setdefault") and isdead(op[1]):
            r = "skip"
        elif n == "set":
            r = res(lambda: d.__setitem__(key(op[1]), op[2]))
        elif n == "get_":
            r = res(lambda: d[key(op[1])])
        elif n == "del":
            r = res(lambda: d.__delitem__(key(op[1])))
        elif n == "len":
            r = len(d)
        elif n == "copy":
            r = res(lambda: dump(d.copy()))
        elif n == "deepcopy":
            r = res(lambda: dump(misc_copy.deepcopy(d)))
        elif n == "get":
            r = res(lambda: d.get(key(op[1]), op[2]))
        elif n == "in":
            r = res(lambda: key(op[1]) in d)
        elif n == "krefs":
            r = [None if x() is None else misc_pv(x()) for x in d.keyrefs()]
        elif n == "popitem":
            def f():
                k, v = d.popitem()
                return [misc_pv(k), v]
            r = res(f)
        elif n == "pop":
            r = res(lambda: d.pop(key(op[1]), *op[2]))
        elif n == "setdefault":
            r = res(lambda: d.setdefault(key(op[1]), op[2]))
        elif n == "update":
            if anydead(misc_other_items(op[1])):
                r = "skip"
            elif op[2]:
                r = res(lambda: d.update(misc_other(op[1], conv), a=1))
            else:
                r = res(lambda: d.update(misc_other(op[1], conv)))
        elif n == "ior":
            r = "skip" if anydead(misc_other_items(op[1])) else \
                res(lambda: (d.__ior__(misc_other(op[1], conv)), None)[1])
        elif n in ("or", "ror"):
            if anydead(op[1]):
                r = "skip"
            else:
                def f():
                    o = 5 if op[1] is None else misc_MappingItems([conv(x) for x in op[1]])
                    v = getattr(d, "__" + n + "__")(o)
                    return "NotImplemented" if v is NotImplemented else dump(v)
                r = res(f)
                if r == ["ok", "NotImplemented"]:
                    r = "NotImplemented"
        elif n == "gen":
            m = {"items": d.items, "keys": d.keys, "values": d.values}
            gens.gens.append([m[op[1]](), op[1], None])
            r = None
        elif n == "next":
            r = gens.next(op[1], enc)
        else:
            if gens.held(op[1]):
                r = "held"
            else:
                dead.add(op[1])
                objs.pop(op[1], None)
                r = None
        out.append(r)
    out.append([[None if k() is None else misc_pv(k()), v] for k, v in d.data.items()])
    return {"ok": out}


class misc_BadTruth:
    def __bool__(self):
        raise ValueError("truth")


class MiscE:
    def __init__(self, i, val, eqm, nem):
        self.i, self.val, self.eqm, self.nem = i, val, eqm, nem

    def __eq__(self, other):
        if self.eqm == 1:
            raise ValueError("eq")
        if self.eqm == 2:
            return 0
        if self.eqm == 3:
            return "yes"
        if self.eqm == 4:
            return misc_BadTruth()
        return isinstance(other, MiscE) and self.val == other.val

    def __ne__(self, other):
        if self.nem == 1:
            return "ne"
        if self.nem == 2:
            return 0
        r = self.__eq__(other)
        return r if r is NotImplemented else not r

    __hash__ = object.__hash__

    def m(self):
        pass


def misc_enc_rv(v):
    if isinstance(v, misc_BadTruth):
        return "BAD"
    return v


def misc_run_wm(case):
    vals = case["vals"]
    objs = {i: MiscE(i, vals[i], case["eqm"][i], case["nem"][i]) for i in range(4)}
    funcs = {10: (lambda self: None), 11: (lambda self: None)}
    ids = {id(f): i for i, f in funcs.items()}
    ms = []
    fired = []
    out = []

    class OnlySelf:
        pass

    class RaiseSelf:
        @property
        def __self__(self):
            raise ValueError("selfattr")

    class FakeMeth:
        def __init__(self, a, b):
            self.__self__, self.__func__ = a, b

    def bad(kind):
        if kind == "int":
            return misc_types.MethodType(funcs.get(10, lambda s: None), 5)
        if kind == "onlyself":
            m = OnlySelf()
            m.__self__ = objs[0]
            return m
        if kind == "raiseself":
            return RaiseSelf()
        if kind == "funcint":
            return FakeMeth(objs[0], 3)
        return 5
    for op in case["ops"]:
        n = op[0]
        if n == "new":
            o, f = op[1], op[2]
            if o not in objs or f not in funcs:
                out.append("skip")
                continue
            idx = len(ms)

            def cb(wr, idx=idx):
                fired.append(idx)
            ms.append(misc_weakref.WeakMethod(misc_types.MethodType(funcs[f], objs[o]),
                                              cb if op[3] else None))
            out.append(idx)
        elif n == "bad":
            if op[1] in ("onlyself", "funcint") and 0 not in objs:
                out.append("skip")
                continue
            meth = bad(op[1])
            r = misc_eres(lambda: (misc_weakref.WeakMethod(meth), None)[1])
            if r[0] == "exc":
                r[2] = r[2].replace(str(type(meth)), "TP")
            del meth
            out.append(r)
        elif n == "call":
            if op[1] >= len(ms):
                out.append("skip")
            else:
                r = ms[op[1]]()
                out.append(None if r is None else [r.__self__.i, ids[id(r.__func__)]])
                del r
        elif n in ("eq", "ne"):
            if op[1] >= len(ms) or op[2] >= len(ms):
                out.append("skip")
            else:
                def f():
                    return getattr(ms[op[1]], "__" + n + "__")(ms[op[2]])
                r = misc_eres(f)
                if r == ["ok", NotImplemented]:
                    r = None
                elif r[0] == "ok":
                    r = ["ok", misc_enc_rv(r[1])]
                out.append(r)
        elif n == "eqo":
            if op[1] >= len(ms):
                out.append("skip")
            else:
                v = ms[op[1]].__eq__(5)
                out.append(None if v is NotImplemented else ["ok", v])
        elif n == "alive":
            out.append("skip" if op[1] >= len(ms) else ms[op[1]]._alive)
        else:
            fired.clear()
            objs.pop(op[1], None)
            funcs.pop(op[1], None)
            out.append(sorted(fired, reverse=True))
    return {"ok": out}


def misc_run_keyed(case):
    p = case["v"]
    log = []
    if p[0] == "i":
        return {"ok": misc_res(lambda: misc_weakref.KeyedRef(p[1], None, "k"))}
    o = MiscW(p[1], 0)
    r = misc_weakref.KeyedRef(o, log.append, "k")
    first = misc_pv(r())
    has_cb = r.__callback__ is not None
    del o
    assert log == [r]
    return {"ok": [r.key, first, None if r() is None else misc_pv(r()), has_cb]}


class misc_BadBool:
    def __bool__(self):
        raise ValueError("bool")


class MyFin(misc_weakref.finalize):
    __slots__ = ()


def misc_run_fin(case):
    fin = misc_weakref.finalize
    saved = dict(fin._registry), fin._shutdown, fin._dirty
    fin._registry.clear()
    fin._shutdown = False
    fin._dirty = False
    misc_gc.enable()
    vals = case["vals"]
    objs = {i: MiscW(i, vals[i]) for i in range(4)}
    fs = {}
    log = []
    hook_saved = sys.excepthook

    def hook(t, v, tb):
        log.append(["hook", t.__name__, str(v)])
        if str(v) == "boom2":
            raise RuntimeError("hook")
    sys.excepthook = hook
    spec = {}

    def mk(s):
        def f():
            log.append(["run", s, misc_gc.isenabled()])
            if s[0] == "ret":
                return s[1]
            if s[0] == "boom":
                raise ValueError("boom")
            if s[0] == "boom2":
                raise ValueError("boom2")
            if s[0] == "base":
                raise KeyboardInterrupt("base")
            if s[2] in objs:
                fs[s[1]] = fin(objs[s[2]], mk(s[3]))
        spec[f] = s
        return f

    def peek(r):
        return None if r is None else [misc_pv(r[0]), spec[r[1]]]

    def base_res(thunk):
        try:
            return ["ok", thunk()]
        except BaseException as e:
            return ["exc", type(e).__name__, str(e)]

    out = []
    try:
        for op in case["ops"]:
            n = op[0]
            f = fs.get(op[1]) if n in ("call", "detach", "peek", "alive", "atexit", "set_atexit", "repr") else None
            if n in ("new", "newsub"):
                p = op[2]
                if p[0] == "o" and p[1] not in objs:
                    out.append("skip")
                    continue
                o = objs[p[1]] if p[0] == "o" else p[1]
                cls = MyFin if n == "newsub" else fin

                def build():
                    fs[op[1]] = cls(o, mk(op[3]))
                out.append(misc_res(build))
                del o
            elif n == "kill":
                objs.pop(op[1], None)
                out.append(None)
            elif n == "exit":
                r = base_res(fin._exitfunc)
                out.append(r)
            elif f is None:
                # a finalizer that was never created: every query sees a dead one
                out.append({"call": ["ok", None], "detach": None, "peek": None, "alive": False,
                            "atexit": False, "set_atexit": ["ok", None],
                            "repr": "<finalize object at ADDR; dead>"}[n])
            elif n == "call":
                out.append(base_res(f))
            elif n == "detach":
                out.append(peek(f.detach()))
            elif n == "peek":
                out.append(peek(f.peek()))
            elif n == "alive":
                out.append(f.alive)
            elif n == "atexit":
                out.append(f.atexit)
            elif n == "set_atexit":
                v = {"bad": misc_BadBool(), "s": "s"}.get(op[2], op[2]) if isinstance(op[2], str) else op[2]
                out.append(misc_eres(lambda: setattr(f, "atexit", v)))
            else:
                t = f.peek()
                r = repr(f).replace(hex(id(f)), "ADDR")
                if t is not None:
                    r = r.replace(hex(id(t[0])), "OBJ")
                del t
                out.append(r)
        reg = [next(k for k, v in fs.items() if v is f2) for f2 in fin._registry]
        r = [out, log, reg, fin._shutdown, fin._dirty, misc_gc.isenabled()]
    finally:
        fin._registry.clear()
        fin._registry.update(saved[0])
        fin._shutdown, fin._dirty = saved[1], saved[2]
        sys.excepthook = hook_saved
        misc_gc.enable()
    return {"ok": r}


def misc_run_weakref(case):
    k = case["k"]
    hook_saved = sys.unraisablehook
    sys.unraisablehook = lambda u: None
    try:
        if k == "wvd":
            return misc_run_wvd(case, {i: MiscW(i, case["vals"][i]) for i in range(4)})
        if k == "wkd":
            return misc_run_wkd(case, misc_wkd_objs(case["vals"]))
        if k == "wm":
            return misc_run_wm(case)
        if k == "keyed":
            return misc_run_keyed(case)
        return misc_run_fin(case)
    finally:
        sys.unraisablehook = hook_saved


MISC_GENS = [misc_gen_graphlib, misc_gen_sched, misc_gen_queue, misc_gen_numbers,
             misc_gen_keyword, misc_gen_types, misc_gen_ctx, misc_gen_weakref]
MISC_RUNS = {"misc.graphlib": misc_run_graphlib, "misc.sched": misc_run_sched,
             "misc.queue": misc_run_queue, "misc.numbers": misc_run_numbers,
             "misc.keyword": misc_run_keyword, "misc.types": misc_run_types,
             "misc.ctx": misc_run_ctx, "misc.weakref": misc_run_weakref}


MISC_ONLY = os.environ.get("MISC_ONLY")


def misc_gen(rng):
    gens = [g for g in MISC_GENS if not MISC_ONLY or MISC_ONLY in g.__name__]
    return rng.choice(gens)(rng)


def misc_run(case):
    return MISC_RUNS[case["fn"]](case)
# ====== END AREA misc ======

# ====== BEGIN AREA calstat (Lib/calendar.py, Lib/statistics.py) ======
# Everything for this area stays between these two markers; prefix top-level names with calstat_.
# --- calendar ---------------------------------------------------------------
import calendar as calstat_calendar
import contextlib as calstat_ctx
import datetime as calstat_dt
import io as calstat_io
import locale as calstat_locale
import os as calstat_os
import types as calstat_types
import warnings as calstat_warnings
import _colorize as calstat_colorize

calstat_YEARS = [0, 1, 2, 3, 4, -1, -2, -3, -4, 100, 400, -100, -400, 399, 401, 1582, 1900, 1970,
                 2000, 2001, 2023, 2024, 2100, 2400, 9996, 9998, 9999, 10000, 10001, 10400,
                 2 ** 31, -2 ** 31, 2 ** 63, -2 ** 63, 2 ** 64, -2 ** 64, 10 ** 30]
calstat_THEME = calstat_types.SimpleNamespace(calendar=calstat_types.SimpleNamespace(
    header="\x1b[1m", highlight="\x1b[30m\x1b[43m", weekday="\x1b[36m", reset="\x1b[0m"))
calstat_LOCALES = ["C", "C.utf8", "bogus_XX"]


def calstat_year(rng):
    r = rng.random()
    if r < 0.5:
        return rng.choice(calstat_YEARS)
    if r < 0.9:
        return rng.randint(-3000, 12000)
    return rng.randint(-10 ** 12, 10 ** 12)


def calstat_month(rng):
    r = rng.random()
    if r < 0.9:
        return rng.randint(1, 12)
    return rng.choice([0, 13, -1, -12, 100, 2 ** 31, -2 ** 31 - 1, 2 ** 63, -2 ** 64])


def calstat_fw(rng):
    r = rng.random()
    if r < 0.8:
        return rng.randint(0, 6)
    return rng.choice([-1, -6, -7, -8, 7, 8, 13, 14, 700, 2 ** 31, -2 ** 63, 2 ** 64 + 3])


def calstat_small(rng):
    return rng.choice([-3, -1, 0, 1, 2, 2, 3, 3, 4, 5, 6, 7, 9, 10, 12, 13, 15])


def calstat_week(rng):
    n = rng.choice([0, 1, 7, 7, 7, 3])
    return [[rng.choice([0, 0, 1, 9, 10, 28, 31, 100, -5]), rng.randint(0, 6)] for _ in range(n)]


def calstat_hl(rng, y, m):
    r = rng.random()
    if r < 0.2:
        return None
    if r < 0.7 and 1 <= y <= 9999 and isinstance(m, int) and 1 <= m <= 12:
        return [y, m, rng.randint(1, 28)]
    return [rng.randint(1, 9999), rng.randint(1, 12), rng.randint(1, 28)]


def calstat_ymfw(rng):
    return {"y": calstat_year(rng), "m": calstat_month(rng), "fw": calstat_fw(rng)}


def calstat_gen_cal(rng):
    k = rng.randrange(66)
    c = {}
    names = ["isleap", "leapdays", "weekday", "weekday", "monthrange", "monthrange", "_monthlen",
             "_prevmonth", "_nextmonth", "getfirstweekday", "iterweekdays", "itermonthdates",
             "itermonthdays", "itermonthdays2", "itermonthdays3", "itermonthdays4",
             "monthdatescalendar", "monthdays2calendar", "monthdayscalendar", "yeardatescalendar",
             "yeardays2calendar", "yeardayscalendar", "setfirstweekday", "exc_month", "exc_weekday",
             "__getattr__", "loc_get", "loc_slice", "loc_len", "formatstring", "format", "timegm",
             "t.formatday", "t.formatweek", "t.prweek", "t.formatweekday", "t.formatweekheader",
             "t.formatmonthname", "t.formatmonth", "t.prmonth", "t.formatyear", "t.pryear",
             "h.formatday", "h.formatweek", "h.formatweekday", "h.formatweekheader",
             "h.formatmonthname", "h.formatmonth", "h.formatyear", "h.formatyearpage", "h.formatmonthpage",
             "l.default", "l.init", "l.enter_exit", "lt.formatweekday", "lt.formatmonthname",
             "lh.formatweekday", "lh.formatmonthname", "d.formatweek", "d.formatmonth",
             "d.formatmonth", "d.formatyear", "d.formatyear", "main", "main", "main", "main"]
    fn = names[k]
    c = calstat_ymfw(rng)
    if fn == "leapdays":
        c = {"a": calstat_year(rng), "b": calstat_year(rng)}
    elif fn == "weekday":
        c["d"] = rng.choice([1, 15, 28, 29, 30, 31, 0, 32, -1, 2 ** 31, -2 ** 31 - 1, 2 ** 63,
                             rng.randint(1, 31)])
    elif fn in ("yeardatescalendar", "yeardays2calendar", "yeardayscalendar", "h.formatyear",
                "h.formatyearpage"):
        c["y"] = rng.choice([calstat_year(rng), rng.randint(1, 9999), 1, 9999])
        c["width"] = calstat_small(rng)
        if fn == "h.formatyearpage":
            c["css"] = rng.choice([None, "calendar.css", "a&b.css", "café.css", "€.css"])
            c["encoding"] = rng.choice([None, "utf-8", "ascii", "latin-1", "nope"])
    elif fn == "h.formatmonthpage":
        c["css"] = rng.choice([None, "calendar.css", "a&b.css", "café.css", "€.css"])
        c["encoding"] = rng.choice([None, "utf-8", "ascii", "latin-1", "nope"])
    elif fn in ("exc_month", "exc_weekday"):
        c = {"m": rng.choice([0, 13, -1, 7, 2 ** 70])}
    elif fn == "__getattr__":
        c = {"name": rng.choice(["January", "February", "March", "xyz"])}
    elif fn in ("loc_get", "loc_slice", "loc_len"):
        c = {"table": rng.choice(["day_name", "day_abbr", "month_name", "month_abbr"]),
             "i": rng.randint(-15, 15), "start": rng.choice([None, 0, 1, -1, 5, 20, -20]),
             "stop": rng.choice([None, 0, 3, -2, 20, -20]), "step": rng.choice([1, 1, 2, -1, -3, 0])}
    elif fn in ("formatstring", "format"):
        c = {"cols": [rng.choice(["", "a", "abc", "January", "12345678"])
                      for _ in range(rng.randint(0, 4))],
             "colwidth": calstat_small(rng), "spacing": calstat_small(rng)}
    elif fn == "timegm":
        c = {"t": [rng.choice([1970, 1, 9999, 0, 10000, 2000, 2024, rng.randint(1, 9999)]),
                   calstat_month(rng), rng.randint(-40, 400), rng.randint(-30, 30),
                   rng.randint(-100, 100), rng.randint(-100, 100), 1, 2, 3]}
    elif fn == "t.formatday":
        c = {"d": rng.choice([0, 1, 9, 10, 31, -5, 100]), "wd": rng.randint(0, 6),
             "width": calstat_small(rng)}
    elif fn in ("t.formatweek", "t.prweek"):
        c = {"week": calstat_week(rng), "width": calstat_small(rng)}
    elif fn == "t.formatweekday":
        c = {"d": rng.randint(-9, 9), "width": calstat_small(rng)}
    elif fn == "t.formatweekheader":
        c["width"] = calstat_small(rng)
    elif fn == "t.formatmonthname":
        c["width"] = calstat_small(rng) * 3
        c["withyear"] = rng.random() < 0.7
    elif fn in ("t.formatmonth", "t.prmonth", "d.formatmonth"):
        c["w"] = calstat_small(rng)
        c["l"] = rng.choice([-1, 0, 1, 2, 3])
    elif fn in ("t.formatyear", "t.pryear", "d.formatyear"):
        c["w"] = calstat_small(rng)
        c["l"] = rng.choice([-1, 0, 1, 2])
        c["c"] = calstat_small(rng)
        c["m"] = rng.choice([-1, 0, 1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 3, 3])
    elif fn == "h.formatday":
        c = {"d": rng.choice([0, 1, 31, -5]), "wd": rng.randint(-9, 9)}
    elif fn == "h.formatweek":
        c = {"week": calstat_week(rng)}
    elif fn == "h.formatweekday":
        c = {"d": rng.randint(-9, 9)}
    elif fn in ("h.formatmonthname", "h.formatmonth"):
        c["withyear"] = rng.random() < 0.7
    elif fn in ("l.default", "l.init", "l.enter_exit"):
        c = {"cur": rng.choice(["C", "C.utf8"]), "user": rng.choice(["C", "C.utf8", "bogus_XX"]),
             "locale": rng.choice(calstat_LOCALES + [""])}
        if fn == "l.init" and rng.random() < 0.5:
            c["locale"] = None
    elif fn in ("lt.formatweekday", "lh.formatweekday"):
        c = {"d": rng.randint(-9, 9), "width": calstat_small(rng),
             "locale": rng.choice(calstat_LOCALES)}
    elif fn in ("lt.formatmonthname", "lh.formatmonthname"):
        c["width"] = calstat_small(rng) * 3
        c["withyear"] = rng.random() < 0.7
        c["locale"] = rng.choice(calstat_LOCALES)
    elif fn == "d.formatweek":
        c = {"week": calstat_week(rng), "width": calstat_small(rng),
             "hd": rng.choice([None, 0, 1, 9, 31])}
    elif fn == "main":
        c = {"width": rng.choice([2, 2, 3, 0, -1, 5]), "lines": rng.choice([1, 1, 2, 0, -1]),
             "spacing": rng.choice([6, 6, 0, 1, 3, -2]), "months": rng.choice([3, 3, 1, 2, 4, 0, -1, 12]),
             "css": rng.choice(["calendar.css", "x.css", "café.css"]),
             "locale": rng.choice([None, None, None, "", "C"]),
             "encoding": rng.choice([None, None, "utf-8", "ascii", "latin-1", "nope"]),
             "type": rng.choice(["text", "text", "html"]), "fw": rng.choice([0, 0, 6, 1, 7, -1, 9]),
             "year": rng.choice([None, 2000, 2024, rng.randint(1, 9999), 0, 10000, 9999, 1]),
             "today": [rng.choice([2024, 2000, rng.randint(1, 9999)]), rng.randint(1, 12),
                       rng.randint(1, 28)]}
        c["month"] = None if c["year"] is None or rng.random() < 0.4 else rng.choice(
            [0, 13, -1, rng.randint(1, 12), rng.randint(1, 12), rng.randint(1, 12)])
        if c["locale"] == "C" and c["encoding"] is not None:
            c["encoding"] = "utf-8"
    c["fn"] = "calstat." + fn
    if "fw" not in c:
        c["fw"] = calstat_fw(rng)
    return c


def calstat_lists(v):
    if isinstance(v, (list, tuple)):
        return [calstat_lists(x) for x in v]
    if isinstance(v, calstat_dt.date):
        return [v.year, v.month, v.day]
    if isinstance(v, int) and not isinstance(v, bool):
        return int(v)
    return v


def calstat_out(f):
    buf = calstat_io.StringIO()
    with calstat_ctx.redirect_stdout(buf):
        f()
    return buf.getvalue()


class calstat_Stop(Exception):
    pass


def calstat_main(c):
    args = [f"--width={c['width']}", f"--lines={c['lines']}", f"--spacing={c['spacing']}",
            f"--months={c['months']}", f"--css={c['css']}", f"--type={c['type']}",
            f"--first-weekday={c['fw']}"]
    if c["locale"] is not None:
        args.append(f"--locale={c['locale']}")
    if c["encoding"] is not None:
        args.append(f"--encoding={c['encoding']}")
    if c["year"] is not None:
        args.append(f"--")
        args.append(str(c["year"]))
        if c["month"] is not None:
            args.append(str(c["month"]))
    today = c["today"]

    class D(calstat_dt.date):
        @classmethod
        def today(cls):
            return cls(*today)
    saved = calstat_calendar.datetime
    calstat_calendar.datetime = calstat_types.SimpleNamespace(
        date=D, MINYEAR=calstat_dt.MINYEAR, MAXYEAR=calstat_dt.MAXYEAR)
    raw = calstat_io.BytesIO()
    out = calstat_io.TextIOWrapper(raw, encoding="utf-8", write_through=True)
    try:
        with calstat_ctx.redirect_stdout(out), calstat_ctx.redirect_stderr(calstat_io.StringIO()):
            try:
                calstat_calendar.main(args)
            except SystemExit as e:
                raise calstat_Stop(str(e.code))
    finally:
        calstat_calendar.datetime = saved
    return raw.getvalue().decode("latin-1")


def calstat_table(c):
    return getattr(calstat_calendar, c["table"])


def calstat_with_locale(c, f):
    calstat_os.environ["LC_ALL"] = c["user"]
    calstat_locale.setlocale(calstat_locale.LC_TIME, c["cur"])
    try:
        return f()
    finally:
        calstat_locale.setlocale(calstat_locale.LC_TIME, "C")


def calstat_enter_exit(c):
    cur = c["cur"]

    def body():
        d = calstat_calendar.different_locale(c["locale"])
        d.__enter__()
        try:
            inner = calstat_locale.setlocale(calstat_locale.LC_TIME, None)
        finally:
            d.__exit__()
        return [inner, calstat_locale.setlocale(calstat_locale.LC_TIME, None)]
    return calstat_with_locale(c, body)


def calstat_run_cal_inner(c, fn):
    cal = calstat_calendar
    C = cal.Calendar(c["fw"])
    T = cal.TextCalendar(c["fw"])
    H = cal.HTMLCalendar(c["fw"])
    y, m = c.get("y"), c.get("m")
    if fn == "isleap":
        return bool(cal.isleap(y))
    if fn == "leapdays":
        return cal.leapdays(c["a"], c["b"])
    if fn == "weekday":
        return cal.weekday(y, m, c["d"])
    if fn == "monthrange":
        return list(cal.monthrange(y, m))
    if fn == "_monthlen":
        return cal._monthlen(y, m)
    if fn == "_prevmonth":
        return list(cal._prevmonth(y, m))
    if fn == "_nextmonth":
        return list(cal._nextmonth(y, m))
    if fn == "getfirstweekday":
        return C.getfirstweekday()
    if fn == "iterweekdays":
        return list(C.iterweekdays())
    if fn == "itermonthdates":
        return list(C.itermonthdates(y, m))
    if fn == "itermonthdays":
        return list(C.itermonthdays(y, m))
    if fn == "itermonthdays2":
        return list(C.itermonthdays2(y, m))
    if fn == "itermonthdays3":
        return list(C.itermonthdays3(y, m))
    if fn == "itermonthdays4":
        return list(C.itermonthdays4(y, m))
    if fn in ("monthdatescalendar", "monthdays2calendar", "monthdayscalendar"):
        return getattr(C, fn)(y, m)
    if fn in ("yeardatescalendar", "yeardays2calendar", "yeardayscalendar"):
        return getattr(C, fn)(y, c["width"])
    if fn == "setfirstweekday":
        old = cal.firstweekday()
        try:
            cal.setfirstweekday(c["fw"])
            return cal.firstweekday()
        finally:
            cal.c.firstweekday = old
    if fn == "exc_month":
        return {"msg": str(cal.IllegalMonthError(m))}
    if fn == "exc_weekday":
        return {"msg": str(cal.IllegalWeekdayError(m))}
    if fn == "__getattr__":
        with calstat_warnings.catch_warnings(record=True) as w:
            calstat_warnings.simplefilter("always")
            v = getattr(cal, c["name"])
        return [v, str(w[0].message)]
    if fn == "loc_get":
        return calstat_table(c)[c["i"]]
    if fn == "loc_slice":
        return calstat_table(c)[c["start"]:c["stop"]:c["step"]]
    if fn == "loc_len":
        return len(calstat_table(c))
    if fn == "formatstring":
        return cal.formatstring(c["cols"], c["colwidth"], c["spacing"])
    if fn == "format":
        return calstat_out(lambda: cal.format(c["cols"], c["colwidth"], c["spacing"]))
    if fn == "timegm":
        return cal.timegm(tuple(c["t"]))
    if fn == "t.formatday":
        return T.formatday(c["d"], c["wd"], c["width"])
    if fn == "t.formatweek":
        return T.formatweek(c["week"], c["width"])
    if fn == "t.prweek":
        return calstat_out(lambda: T.prweek(c["week"], c["width"]))
    if fn == "t.formatweekday":
        return T.formatweekday(c["d"], c["width"])
    if fn == "t.formatweekheader":
        return T.formatweekheader(c["width"])
    if fn == "t.formatmonthname":
        return T.formatmonthname(y, m, c["width"], c["withyear"])
    if fn == "t.formatmonth":
        return T.formatmonth(y, m, c["w"], c["l"])
    if fn == "t.prmonth":
        return calstat_out(lambda: T.prmonth(y, m, c["w"], c["l"]))
    if fn == "t.formatyear":
        return T.formatyear(y, c["w"], c["l"], c["c"], c["m"])
    if fn == "t.pryear":
        return calstat_out(lambda: T.pryear(y, c["w"], c["l"], c["c"], c["m"]))
    if fn == "h.formatday":
        return H.formatday(c["d"], c["wd"])
    if fn == "h.formatweek":
        return H.formatweek(c["week"])
    if fn == "h.formatweekday":
        return H.formatweekday(c["d"])
    if fn == "h.formatweekheader":
        return H.formatweekheader()
    if fn == "h.formatmonthname":
        return H.formatmonthname(y, m, c["withyear"])
    if fn == "h.formatmonth":
        return H.formatmonth(y, m, c["withyear"])
    if fn == "h.formatyear":
        return H.formatyear(y, c["width"])
    if fn == "h.formatyearpage":
        return H.formatyearpage(y, c["width"], c["css"], c["encoding"]).decode("latin-1")
    if fn == "h.formatmonthpage":
        return H.formatmonthpage(y, m, css=c["css"], encoding=c["encoding"]).decode("latin-1")
    if fn == "l.default":
        return calstat_with_locale(c, cal._get_default_locale)
    if fn == "l.init":
        return calstat_with_locale(c, lambda: cal.LocaleTextCalendar(0, c["locale"]).locale)
    if fn == "l.enter_exit":
        return calstat_enter_exit(c)
    if fn == "lt.formatweekday":
        return cal.LocaleTextCalendar(0, c["locale"]).formatweekday(c["d"], c["width"])
    if fn == "lt.formatmonthname":
        return cal.LocaleTextCalendar(0, c["locale"]).formatmonthname(y, m, c["width"], c["withyear"])
    if fn == "lh.formatweekday":
        return cal.LocaleHTMLCalendar(0, c["locale"]).formatweekday(c["d"])
    if fn == "lh.formatmonthname":
        return cal.LocaleHTMLCalendar(0, c["locale"]).formatmonthname(y, m, c["withyear"])
    if fn == "d.formatweek":
        return cal._CLIDemoCalendar(None).formatweek(c["week"], c["width"], highlight_day=c["hd"])
    if fn in ("d.formatmonth", "d.formatyear"):
        hl = c.get("hl")
        d = cal._CLIDemoCalendar(calstat_dt.date(*hl) if hl else None, c["fw"])
        if fn == "d.formatmonth":
            return d.formatmonth(y, m, c["w"], c["l"])
        return d.formatyear(y, c["w"], c["l"], c["c"], c["m"])
    if fn == "main":
        return calstat_main(c)
    raise KeyError(fn)


def calstat_run_cal(c):
    fn = c["fn"].split(".", 1)[1]
    saved = calstat_colorize.get_theme
    calstat_colorize.get_theme = lambda **k: calstat_THEME

    def thunk():
        return calstat_lists(calstat_run_cal_inner(c, fn))
    try:
        r = py_result(thunk)
    except BaseException:
        raise
    finally:
        calstat_colorize.get_theme = saved
    if r.get("exc") == "calstat_Stop":
        r["exc"] = "SystemExit"
    return r


calstat_locale.setlocale(calstat_locale.LC_TIME, "C")

# --- statistics -------------------------------------------------------------
import enum as calstat_enum
import math as calstat_math
import random as calstat_random
import statistics as calstat_st
from decimal import Decimal as calstat_D
from fractions import Fraction as calstat_F


class calstat_MyInt(int):
    pass


class calstat_MyFloat(float):
    pass


class calstat_MyFrac(calstat_F):
    pass


class calstat_MyDec(calstat_D):
    pass


class calstat_Lvl(calstat_enum.IntEnum):
    LOW = 1
    MID = 2
    HIGH = 3
    TOP = 5


class calstat_Abc:
    def __init__(self, n, d):
        self.numerator, self.denominator = n, d


calstat_USER_CLASSES = {
    "MyInt": (calstat_MyInt, ["MyInt", "int"], None),
    "MyFloat": (calstat_MyFloat, ["MyFloat", "float"], None),
    "MyFrac": (calstat_MyFrac, ["MyFrac", "Fraction"], None),
    "MyDec": (calstat_MyDec, ["MyDec", "Decimal"], None),
    "Lvl": (calstat_Lvl, ["Lvl", "IntEnum", "int"], [1, 2, 3, 5]),
}


for calstat_k, calstat_v in calstat_USER_CLASSES.items():
    calstat_v[0].__name__ = calstat_k


def calstat_ratio_str(x):
    n, d = x.as_integer_ratio()
    return f"{n}/{d}"


def calstat_fstr(x):
    if x != x:
        return "nan"
    if x in (calstat_math.inf, -calstat_math.inf):
        return "inf" if x > 0 else "-inf"
    if x == 0:
        return "-0" if calstat_math.copysign(1.0, x) < 0 else "0"
    return calstat_ratio_str(float(x))


def calstat_dstr(x):
    if x.is_snan():
        return "snan"
    if x.is_nan():
        return "nan"
    if x.is_infinite():
        return "inf" if x > 0 else "-inf"
    return calstat_ratio_str(x)


def calstat_enc(x):
    """Encode a Python value the way the Lean handler prints one."""
    if isinstance(x, bool):
        return "i:" + str(int(x))
    if isinstance(x, int):
        return "i:" + str(int(x))
    if isinstance(x, float):
        return "f:" + calstat_fstr(x)
    if isinstance(x, calstat_F):
        return "q:" + calstat_ratio_str(x)
    if isinstance(x, calstat_D):
        return "d:" + calstat_dstr(x)
    if isinstance(x, str):
        return "s:" + x
    if x is None:
        return "n:"
    return "o:" + type(x).__name__


def calstat_res(x):
    return [type(x).__name__, calstat_enc(x)]


def calstat_spec(x):
    """The JSON spec of a value for the case; bool keeps its class."""
    if isinstance(x, bool):
        return "b:" + str(int(x))
    return calstat_enc(x)


def calstat_obj(spec):
    """Build the Python object of a spec."""
    if isinstance(spec, dict):
        base = calstat_obj(spec["v"])
        return calstat_USER_CLASSES[spec["c"]][0](base)
    tag, body = spec[:2], spec[2:]
    if tag == "i:":
        return int(body)
    if tag == "b:":
        return body == "1"
    if tag == "q:":
        return calstat_F(body)
    if tag == "f:":
        if body in ("nan", "inf", "-inf"):
            return float(body)
        if body == "0":
            return 0.0
        if body == "-0":
            return -0.0
        n, d = body.split("/")
        return float(calstat_F(int(n), int(d)))
    if tag == "d:":
        if body == "nan":
            return calstat_D("NaN")
        if body == "snan":
            return calstat_D("sNaN")
        if body == "inf":
            return calstat_D("Infinity")
        if body == "-inf":
            return calstat_D("-Infinity")
        n, d = body.split("/")
        # value-exact construction of a terminating decimal
        with calstat_D_ctx():
            return calstat_D(int(n)) / calstat_D(int(d))
    if tag == "s:":
        return body
    if tag == "n:":
        return None
    if tag == "a:":
        n, d = body.split("/")
        return calstat_Abc(int(n), int(d))
    raise KeyError(spec)


def calstat_D_ctx():
    import decimal
    ctx = decimal.Context(prec=400)
    return decimal.localcontext(ctx)


def calstat_user(name, spec):
    cls, mro, members = calstat_USER_CLASSES[name]
    return {"c": name, "mro": mro, "m": members, "v": spec}


calstat_FLOATS = [0.0, -0.0, 1.0, -1.0, 0.5, 0.25, 1.5, 2.0, 3.0, 0.1, 0.2, 0.3, 1e-3, 1e10, 1e16, 2.0 ** 53,
                  1e308, -1e308, 1.7976931348623157e308, 5e-324, 2.2250738585072014e-308, 1e-300, 1e300]
calstat_INTS = [0, 1, -1, 2, 3, 4, 5, 7, 10, -3, 100, 2 ** 31, 2 ** 53 + 1, 2 ** 63, -2 ** 63, 2 ** 64,
                10 ** 30, 10 ** 400, -10 ** 400]


def calstat_float(rng):
    r = rng.random()
    if r < 0.45:
        return rng.choice(calstat_FLOATS)
    if r < 0.8:
        return rng.uniform(-10, 10)
    return rng.uniform(-1, 1) * 10.0 ** rng.randint(-300, 300)


def calstat_int(rng):
    return rng.choice(calstat_INTS) if rng.random() < 0.3 else rng.randint(-20, 20)


def calstat_frac(rng):
    return calstat_F(rng.randint(-30, 30), rng.randint(1, 12))


def calstat_dec(rng):
    return calstat_D(rng.randint(-2000, 2000)).scaleb(-rng.randint(0, 4))


def calstat_value_spec(rng, kind):
    if kind == "int":
        return calstat_spec(calstat_int(rng))
    if kind == "smallint":
        return calstat_spec(rng.randint(-6, 9))
    if kind == "posint":
        return calstat_spec(rng.randint(1, 30))
    if kind == "bool":
        return calstat_spec(rng.random() < 0.5)
    if kind == "float":
        return calstat_spec(calstat_float(rng))
    if kind == "unitfloat":
        return calstat_spec(rng.uniform(-3, 3))
    if kind == "posfloat":
        return calstat_spec(rng.uniform(0.001, 50))
    if kind == "frac":
        return calstat_spec(calstat_frac(rng))
    if kind == "posfrac":
        return calstat_spec(calstat_F(rng.randint(1, 30), rng.randint(1, 12)))
    if kind == "dec":
        return calstat_spec(calstat_dec(rng))
    if kind == "specialf":
        return calstat_spec(rng.choice([calstat_math.inf, -calstat_math.inf, float("nan")]))
    if kind == "speciald":
        return "d:" + rng.choice(["nan", "inf", "-inf", "snan"])
    if kind == "str":
        return "s:" + rng.choice(["red", "blue", "x"])
    if kind == "none":
        return "n:"
    if kind == "myint":
        return calstat_user("MyInt", calstat_spec(rng.randint(-9, 9)))
    if kind == "myfloat":
        return calstat_user("MyFloat", calstat_spec(rng.uniform(-9, 9)))
    if kind == "myfrac":
        return calstat_user("MyFrac", calstat_spec(calstat_frac(rng)))
    if kind == "mydec":
        return calstat_user("MyDec", calstat_spec(calstat_dec(rng)))
    if kind == "lvl":
        return calstat_user("Lvl", calstat_spec(rng.choice([1, 2, 3, 5])))
    raise KeyError(kind)


calstat_MIXES = [["smallint"], ["smallint"], ["int"], ["posint"], ["float"], ["unitfloat"], ["unitfloat"],
                 ["posfloat"], ["frac"], ["frac"], ["posfrac"], ["dec"], ["smallint", "frac"], ["smallint", "float"],
                 ["frac", "unitfloat"], ["smallint", "dec"], ["bool", "smallint"], ["bool"], ["myint"],
                 ["myint", "smallint"], ["myfloat", "unitfloat"], ["myfrac", "frac"], ["mydec", "dec"], ["lvl"],
                 ["unitfloat", "specialf"], ["dec", "speciald"], ["frac", "dec"], ["unitfloat", "dec"],
                 ["smallint", "str"], ["str"], ["none", "smallint"], ["myfloat", "myint"], ["myint", "frac"]]


def calstat_data(rng, mixes=calstat_MIXES, maxn=9):
    mix = rng.choice(mixes)
    n = rng.choice([0, 1, 2, 2, 3, 3, 4, 5, 6, 7, maxn])
    return [calstat_value_spec(rng, rng.choice(mix)) for _ in range(n)]


calstat_NUMMIX = [["smallint"], ["int"], ["posint"], ["float"], ["unitfloat"], ["unitfloat"], ["posfloat"], ["frac"],
                  ["posfrac"], ["smallint", "frac"], ["smallint", "unitfloat"], ["bool", "smallint"],
                  ["unitfloat", "specialf"]]
calstat_SIMPLE = [["smallint"], ["int"], ["float"], ["unitfloat"], ["unitfloat"], ["frac"], ["dec"],
                  ["smallint", "frac"], ["smallint", "unitfloat"], ["frac", "unitfloat"], ["bool", "smallint"],
                  ["unitfloat", "specialf"], ["str"], ["none", "smallint"], ["myint"], ["myfloat"]]
calstat_KERNELS = ["normal", "gauss", "logistic", "sigmoid", "rectangular", "uniform", "triangular", "parabolic",
                   "epanechnikov", "quartic", "biweight", "triweight", "cosine"]
calstat_ERFC_NAMES = ("erfc",)


def calstat_nd(rng):
    mu = rng.choice([0.0, 1.0, -2.5, rng.uniform(-10, 10), 1e300, 0.1])
    sigma = rng.choice([1.0, 0.5, 2.0, 0.0, rng.uniform(0.01, 10), 3.0, 1e-300])
    return [calstat_fstr(mu), calstat_fstr(sigma)]


def calstat_ndobj(l):
    return calstat_st.NormalDist(calstat_obj("f:" + l[0]), calstat_obj("f:" + l[1]))


def calstat_const(rng):
    return calstat_value_spec(rng, rng.choice(["smallint", "unitfloat", "frac", "float", "bool"]))


def calstat_gen_stat(rng):
    fns = ["s._exact_ratio", "s._isfinite", "s._coerce", "s._sum", "s._ss", "s._ss", "s._convert", "s._fail_neg", "s._rank", "s._rank",
           "s._integer_sqrt_of_frac_rto", "s._float_sqrt_of_frac", "s._float_sqrt_of_frac",
           "s._decimal_sqrt_of_frac", "s._mean_stdev", "s._sqrtprod",
           "s.mean", "s.mean", "s.fmean", "s.fmean", "s.fmean_it", "s.fmean_it", "s.fmean_it", "s.quantiles_it", "s._fail_neg_gen", "s.nd.setstate",
           "s._sqrtprod", "s.correlation", "s._decimal_sqrt_of_frac", "s.quantiles", "s.geometric_mean", "s.harmonic_mean", "s.harmonic_mean", "s.median", "s.median_low",
           "s.median_high", "s.median_grouped", "s.mode", "s.multimode", "s.variance", "s.variance", "s.pvariance",
           "s.stdev", "s.pstdev", "s.covariance", "s.correlation", "s.correlation", "s.linear_regression",
           "s.linear_regression", "s.quantiles", "s.quantiles", "s.kde", "s.kde", "s.kde_random", "s.kernel", "s.kernel",
           "s.nd.init", "s.nd.from_samples", "s.nd.samples", "s.nd.pdf", "s.nd.cdf", "s.nd.inv_cdf",
           "s.nd.quantiles", "s.nd.overlap", "s.nd.zscore", "s.nd.props", "s.nd.add", "s.nd.sub", "s.nd.addc",
           "s.nd.subc", "s.nd.mulc", "s.nd.divc", "s.nd.rsubc", "s.nd.pos", "s.nd.neg", "s.nd.eq", "s.nd.hash",
           "s.nd.repr", "s.nd.state"]
    fn = rng.choice(fns)
    c = {}
    if fn == "s._isfinite":
        c["x"] = calstat_value_spec(rng, rng.choice(["int", "float", "frac", "dec", "bool", "specialf", "speciald", "str", "none"]))
    elif fn == "s._exact_ratio":
        kind = rng.choice(["smallint", "float", "frac", "dec", "bool", "specialf", "speciald", "str", "none"])
        c["x"] = calstat_value_spec(rng, kind)
        if rng.random() < 0.1:
            c["x"] = f"a:{rng.randint(-9, 9)}/{rng.randint(1, 9)}"
    elif fn == "s._coerce":
        names = ["int", "bool", "float", "Fraction", "Decimal", "MyInt", "MyFloat", "MyFrac", "MyDec"]
        pick2 = [rng.choice(names), rng.choice(names)]
        c["T"], c["S"] = [calstat_cls_spec(n) for n in pick2]
    elif fn == "s._sum":
        c["data"] = calstat_data(rng)
    elif fn == "s._ss":
        c["data"] = calstat_data(rng)
        c["c"] = None
        if rng.random() < 0.4:
            c["c"] = calstat_value_spec(rng, rng.choice(["smallint", "frac", "unitfloat", "dec"]))
    elif fn == "s._convert":
        c["T"] = calstat_cls_spec(rng.choice(["int", "float", "Fraction", "Decimal", "MyInt", "MyFloat", "MyFrac", "Lvl"]))
        c["x"] = calstat_spec(calstat_F(rng.randint(-9, 9), rng.choice([1, 1, 2, 3])))
    elif fn == "s._fail_neg":
        c["data"] = calstat_data(rng, [["smallint"], ["frac"], ["unitfloat"]])
    elif fn == "s._rank":
        c["data"] = calstat_data(rng, [["smallint"], ["unitfloat"], ["frac"], ["smallint", "frac"],
                                       ["unitfloat", "specialf"], ["str"]], 12)
        c["reverse"] = rng.random() < 0.3
        c["ties"] = rng.choice(["average", "average", "average", "min"])
        c["start"] = calstat_spec(rng.choice([1, 0, 2, -1.5, 0.5, 1.0]))
    elif fn == "s._integer_sqrt_of_frac_rto":
        c["n"] = rng.choice([0, 1, 2, 3, 4, 15, 16, 17, rng.randint(0, 10 ** 30), 10 ** 40])
        c["m"] = rng.choice([1, 1, 2, 3, 4, rng.randint(1, 10 ** 10)])
    elif fn == "s._float_sqrt_of_frac":
        c["n"] = rng.choice([0, 1, 2, 3, rng.randint(1, 10 ** 30), rng.randint(1, 10 ** 700), 2 ** 2100])
        c["m"] = rng.choice([1, 2, 3, rng.randint(1, 10 ** 30), rng.randint(1, 10 ** 700)])
    elif fn == "s._decimal_sqrt_of_frac":
        c["n"] = rng.choice([0, 1, 2, 3, rng.randint(1, 10 ** 30), rng.randint(1, 10 ** 60), -rng.randint(1, 100)])
        c["m"] = rng.choice([1, 2, 3, rng.randint(1, 10 ** 30)])
        if c["n"] < 0:
            c["m"] = -c["m"]
        if rng.random() < 0.3:
            # exact squares of 29-digit values: ties, and their neighbours
            k = rng.randint(10 ** 28, 10 ** 29 - 1)
            k = k - k % 10 + rng.choice([5, 5, 5, 4, 6, 0])
            scale = 10 ** rng.randint(20, 32)
            c["n"], c["m"] = k * k, scale * scale
    elif fn == "s._mean_stdev":
        c["data"] = calstat_data(rng, calstat_NUMMIX)
    elif fn == "s._sqrtprod":
        pool = [0.0, 1.0, 2.0, 1e308, 1e-308, 5e-324, 1e200, 1e-200, 3.0, calstat_math.inf, float("nan")]
        c["x"] = calstat_fstr(rng.choice(pool + [rng.uniform(0, 10)]))
        c["y"] = calstat_fstr(rng.choice(pool + [rng.uniform(0, 10)]))
        if rng.random() < 0.5:
            # products in and around the subnormal range, where only sqrt(x*y) == 0 is rescaled
            e = rng.randint(-1100, -1000)
            a = rng.randint(-600, 0)
            x = calstat_math.ldexp(rng.uniform(0.5, 1), a)
            y = calstat_math.ldexp(rng.uniform(0.5, 1), e - a)
            if rng.random() < 0.3:
                x, y = 10 * 2.0 ** -540, 10 * 2.0 ** -538
            c["x"], c["y"] = calstat_fstr(x), calstat_fstr(y)
    elif fn in ("s.mean", "s.variance", "s.pvariance", "s.stdev", "s.pstdev"):
        c["data"] = calstat_data(rng)
        if fn != "s.mean":
            c["c"] = None
            if rng.random() < 0.3:
                c["c"] = calstat_value_spec(rng, rng.choice(["smallint", "frac", "unitfloat", "dec"]))
    elif fn == "s.fmean":
        c["data"] = calstat_data(rng, calstat_NUMMIX)
        c["weights"] = None
        c["iter"] = rng.random() < 0.3
        if rng.random() < 0.5:
            n = len(c["data"]) if rng.random() < 0.9 else rng.randint(0, 4)
            c["weights"] = [calstat_value_spec(rng, rng.choice(["smallint", "unitfloat", "frac"])) for _ in range(n)]
    elif fn == "s.nd.setstate":
        c["state"] = [calstat_value_spec(rng, rng.choice(["smallint", "float", "frac", "str", "none", "dec"]))
                      for _ in range(rng.choice([0, 1, 2, 2, 2, 3, 4]))]
    elif fn == "s._fail_neg_gen":
        c["data"] = calstat_data(rng, [["smallint"], ["frac"], ["unitfloat"], ["smallint", "str"], ["unitfloat", "specialf"],
                                       ["dec", "speciald"]])
    elif fn == "s.quantiles_it":
        c["data"] = calstat_data(rng, calstat_NUMMIX + [["str"]], 8)
        c["n"] = rng.choice([1, 2, 3, 4, 5, 0, -1])
        c["method"] = rng.choice(["exclusive", "inclusive", "bogus"])
        c["src"] = rng.choice(["list", "tuple", "iter", "fail", "fail", "gen"])
        c["exc"] = rng.choice([["ValueError", "boom"], ["TypeError", "bad"], ["RuntimeError", "rt"],
                               ["MyTypeError", "mt"]])
    elif fn == "s.fmean_it":
        mix = rng.choice([["smallint"], ["int"], ["unitfloat"], ["float"], ["frac"], ["smallint", "frac"], ["bool", "smallint"],
                          ["unitfloat", "specialf"], ["str"], ["dec"]])
        c["data"] = calstat_data(rng, [mix])
        c["src"] = rng.choice(["list", "tuple", "iter", "fail", "fail", "badlen", "badlen", "gen",
                               "listsub_iter", "listsub_fail"])
        excs = [["ValueError", "boom"], ["TypeError", "bad"], ["RuntimeError", "rt"], ["MyTypeError", "mt"],
                ["MyValueError", "mv"]]
        c["exc"] = rng.choice(excs)
        c["weights"] = None
        if rng.random() < 0.5:
            n = len(c["data"]) if rng.random() < 0.8 else rng.randint(0, 5)
            c["weights"] = [calstat_value_spec(rng, rng.choice(["smallint", "smallint", "unitfloat", "frac"])) for _ in range(n)]
            if rng.random() < 0.15:
                c["weights"] = [calstat_spec(rng.choice([1, -1])) for _ in range(n)]
                c["weights"] = c["weights"][:-1] + [calstat_spec(-sum(int(x[2:]) for x in c["weights"][:-1]))] if n else []
            c["wsrc"] = rng.choice(["list", "tuple", "iter", "fail", "gen", "listsub_iter", "listsub_fail",
                                    "listsub_fail"])
            c["wexc"] = rng.choice(excs)
            if c["src"] == "badlen":
                c["src"] = "list"
    elif fn == "s.geometric_mean":
        c["data"] = calstat_data(rng, [["posint"], ["posfloat"], ["posfrac"], ["posint", "posfrac"], ["smallint"], ["unitfloat"],
                                       ["posfloat", "specialf"], ["int"], ["float"], ["none"]])
    elif fn == "s.harmonic_mean":
        mix = rng.choice([["posint"], ["posint"], ["smallint"], ["posfloat"], ["posfrac"], ["frac"], ["dec"], ["posfrac", "posint"],
                          ["float"], ["unitfloat", "specialf"], ["str"]])
        c["data"] = calstat_data(rng, [mix])
        c["weights"] = None
        if rng.random() < 0.5:
            n = len(c["data"]) if rng.random() < 0.9 else rng.randint(0, 4)
            wmix = rng.choice([["posint"], ["smallint"], ["posfrac"], ["posfloat"]])
            c["weights"] = [calstat_value_spec(rng, rng.choice(wmix)) for _ in range(n)]
    elif fn in ("s.median", "s.median_low", "s.median_high"):
        c["data"] = calstat_data(rng, calstat_SIMPLE + [["dec"], ["unitfloat", "specialf"]], 12)
    elif fn == "s.median_grouped":
        c["data"] = calstat_data(rng, [["smallint"], ["unitfloat"], ["frac"], ["smallint", "unitfloat"], ["unitfloat", "specialf"]], 12)
        c["interval"] = rng.choice(["f:1/1", "i:1", "i:2", "i:10", "f:1/2", "q:1/3", "s:abc", "n:", "f:0", "i:0"])
    elif fn in ("s.mode", "s.multimode"):
        c["data"] = calstat_data(rng, [["smallint"], ["bool", "smallint"], ["str"], ["smallint", "frac"], ["smallint", "str"]], 14)
        if rng.random() < 0.5:
            c["data"] = [calstat_value_spec(rng, "bool") if rng.random() < 0.5 else calstat_spec(rng.randint(0, 3))
                         for _ in range(rng.randint(0, 10))]
    elif fn in ("s.covariance", "s.correlation", "s.linear_regression"):
        mix = rng.choice([["smallint"], ["unitfloat"], ["posfloat"], ["frac"], ["smallint", "unitfloat"], ["float"], ["int"],
                          ["unitfloat", "specialf"], ["dec"]])
        c["x"] = calstat_data(rng, [mix])
        n = len(c["x"]) if rng.random() < 0.93 else rng.randint(0, 5)
        c["y"] = [calstat_value_spec(rng, rng.choice(mix)) for _ in range(n)]
        if rng.random() < 0.2 and c["x"]:
            c["x"] = [c["x"][0]] * len(c["x"])
        if fn in ("s.correlation", "s.covariance", "s.linear_regression") and rng.random() < 0.15:
            # exactly proportional data whose sums of squares are normal but whose product underflows
            k = rng.randint(2, 6)
            ex, ey = rng.randint(-400, -200), rng.randint(-400, -200)
            base = [rng.randint(-9, 9) for _ in range(k)]
            c["x"] = [calstat_spec(calstat_math.ldexp(b, ex)) for b in base]
            c["y"] = [calstat_spec(calstat_math.ldexp(b * rng.choice([1, 2, 3, -1]), ey)) for b in base]
        if fn == "s.correlation":
            c["method"] = rng.choice(["linear", "linear", "ranked", "ranked", "bogus"])
        if fn == "s.linear_regression":
            c["proportional"] = rng.random() < 0.4
    elif fn == "s.quantiles":
        c["data"] = calstat_data(rng, calstat_NUMMIX + [["str"], ["dec"]], 12)
        c["n"] = rng.choice([1, 2, 3, 4, 4, 5, 7, 10, 20, 0, -1])
        c["method"] = rng.choice(["exclusive", "exclusive", "inclusive", "inclusive", "bogus"])
        if rng.random() < 0.2:
            v = calstat_spec(rng.choice([0.1, 0.3, 0.7, 1 / 3, 1e300, rng.uniform(-5, 5)]))
            c["data"] = [v] * rng.randint(1, 6)
    elif fn in ("s.kde", "s.kde_random"):
        mix = rng.choice([["smallint"], ["unitfloat"], ["smallint", "unitfloat"], ["frac"]])
        c["data"] = calstat_data(rng, [mix])
        c["h"] = calstat_spec(rng.choice([1, 1.5, 0.5, 2, 0, -1, 0.25, 3.0]))
        c["kernel"] = rng.choice(calstat_KERNELS + ["bogus"])
        if fn == "s.kde":
            c["cumulative"] = rng.random() < 0.5
            c["x"] = calstat_spec(rng.choice([0, 1, -1, 0.5, rng.uniform(-6, 6), rng.uniform(-6, 6), 100.0, -100.0]))
            c["data2"] = list(c["data"])
            if rng.random() < 0.15 and c["data2"]:
                c["data2"].append(calstat_spec(rng.randint(-3, 3)))
        else:
            c["draws"] = [[rng.randrange(max(len(c["data"]), 1)), calstat_fstr(rng.random())]
                          for _ in range(rng.randint(0, 3))]
    elif fn == "s.kernel":
        c["kernel"] = rng.choice(calstat_KERNELS)
        c["which"] = rng.choice(["pdf", "cdf", "invcdf"])
        if c["which"] == "invcdf":
            c["t"] = calstat_fstr(rng.choice([0.5, 0.25, 0.75, 0.1, 0.9, 1e-3, 0.999, 0.0106, 0.499, rng.uniform(0.0001, 0.9999)]))
        else:
            c["t"] = calstat_fstr(rng.choice([0.0, -0.0, 1.0, -1.0, 0.5, -0.5, rng.uniform(-1, 1), rng.uniform(-1, 1)]))
    elif fn == "s.nd.init":
        c["mu"] = rng.choice([calstat_const(rng), "s:x", "n:", "i:" + str(10 ** 400)])
        c["sigma"] = rng.choice([calstat_const(rng), calstat_const(rng), "s:x"])
    elif fn == "s.nd.from_samples":
        c["data"] = calstat_data(rng, calstat_NUMMIX)
    elif fn == "s.nd.samples":
        c["X"] = calstat_nd(rng)
        c["seed"] = rng.randint(0, 10 ** 6)
        r2 = calstat_random.Random(c["seed"])
        c["us"] = [calstat_fstr(r2.random()) for _ in range(rng.randint(0, 3))]
    elif fn in ("s.nd.pdf", "s.nd.cdf", "s.nd.zscore"):
        c["X"] = calstat_nd(rng)
        c["x"] = calstat_spec(rng.choice([0, 1, -1, 0.5, rng.uniform(-6, 6), calstat_F(1, 3), 2.5]))
    elif fn == "s.nd.inv_cdf":
        c["X"] = calstat_nd(rng)
        c["x"] = calstat_spec(rng.choice([0.5, 0.0, 1.0, -1, 2, 0.1, 0.9, rng.random(), rng.random(), 1e-10, 1 - 1e-10, 1e-300]))
    elif fn == "s.nd.quantiles":
        c["X"] = calstat_nd(rng)
        c["n"] = rng.choice([0, 1, 2, 3, 4, 10])
    elif fn in ("s.nd.overlap", "s.nd.add", "s.nd.sub", "s.nd.eq"):
        c["X"] = calstat_nd(rng)
        c["Y"] = c["X"] if rng.random() < 0.15 else calstat_nd(rng)
    elif fn in ("s.nd.addc", "s.nd.subc", "s.nd.mulc", "s.nd.divc", "s.nd.rsubc"):
        c["X"] = calstat_nd(rng)
        c["x"] = rng.choice([calstat_const(rng), calstat_const(rng), "s:x", "i:0", "i:" + str(10 ** 400)])
    elif fn == "s.nd.repr":
        c["X"] = calstat_nd(rng)
        if rng.random() < 0.4:
            c["cls"] = rng.choice(["Sub", "MyNormal", "N2"])
    else:
        c["X"] = calstat_nd(rng)
    c["fn"] = "calstat." + fn
    if fn in ("s.kde", "s.kernel", "s.nd.cdf", "s.nd.overlap"):
        c["erfc"] = calstat_record_erfc(c, fn)
    return c


def calstat_cls_spec(name):
    if name in calstat_USER_CLASSES:
        return {"c": name, "mro": calstat_USER_CLASSES[name][1], "m": calstat_USER_CLASSES[name][2]}
    return {"c": name, "mro": {"bool": ["bool", "int"]}.get(name, [name])}


calstat_BUILTIN = {"int": int, "bool": bool, "float": float, "Fraction": calstat_F, "Decimal": calstat_D}


def calstat_cls(spec):
    n = spec["c"]
    return calstat_USER_CLASSES[n][0] if n in calstat_USER_CLASSES else calstat_BUILTIN[n]


def calstat_record_erfc(c, fn):
    table = []
    real = calstat_math.erfc

    def rec(x):
        r = real(x)
        table.append([calstat_fstr(x), calstat_fstr(r)])
        return r
    calstat_st.erfc = rec
    try:
        py_result(lambda: calstat_stat_call(c, fn[2:]))
    finally:
        calstat_st.erfc = real
    return table


def calstat_L(k):
    return [calstat_obj(s) for s in k]


class calstat_MyTypeError(TypeError):
    pass


class calstat_MyValueError(ValueError):
    pass


calstat_MyTypeError.__name__ = "MyTypeError"
calstat_MyValueError.__name__ = "MyValueError"
calstat_EXC = {"ValueError": ValueError, "TypeError": TypeError, "RuntimeError": RuntimeError,
               "MyTypeError": calstat_MyTypeError, "MyValueError": calstat_MyValueError}


def calstat_exc(spec):
    return calstat_EXC[spec[0]](spec[1])


class calstat_FailIter:
    """An iterator (no `__len__`) that yields `items` and then raises `exc` from `__next__`."""

    def __init__(self, items, exc):
        self.items = list(items)
        self.exc = exc

    def __iter__(self):
        return self

    def __next__(self):
        if self.items:
            return self.items.pop(0)
        raise self.exc


class calstat_BadLen:
    """An iterable whose `__len__` raises `exc`."""

    def __init__(self, items, exc):
        self.items = list(items)
        self.exc = exc

    def __len__(self):
        raise self.exc

    def __iter__(self):
        return iter(self.items)


def calstat_gen_stop(items):
    """A generator whose body lets a StopIteration escape: PEP 479 turns it into RuntimeError."""
    yield from items
    raise StopIteration


class calstat_ListIterErr(list):
    """A list subclass whose `__iter__` raises."""

    def __iter__(self):
        raise self.exc


class calstat_ListFail(list):
    """A list subclass whose iterator raises after the items."""

    def __iter__(self):
        return calstat_FailIter(list.__iter__(self), self.exc)


def calstat_src(items, src, exc):
    if src in ("listsub_iter", "listsub_fail"):
        obj = (calstat_ListIterErr if src == "listsub_iter" else calstat_ListFail)(items)
        obj.exc = calstat_exc(exc)
        return obj
    if src == "list":
        return list(items)
    if src == "tuple":
        return tuple(items)
    if src == "iter":
        return iter(items)
    if src == "fail":
        return calstat_FailIter(items, calstat_exc(exc))
    if src == "badlen":
        return calstat_BadLen(items, calstat_exc(exc))
    if src == "gen":
        return calstat_gen_stop(items)
    raise KeyError(src)


class calstat_Script:
    """What `_random.Random(seed)` is replaced by in `kde_random`: scripted draws."""

    def __init__(self, draws, data):
        self.draws = list(draws)
        self.data = data
        self.cur = None

    def choice(self, data):
        self.cur = self.draws.pop(0)
        return data[self.cur[0]]

    def random(self):
        return calstat_obj("f:" + self.cur[1])


def calstat_nds(c):
    return calstat_ndobj(c["X"])


def calstat_ndpair(n):
    return [calstat_fstr(n.mean), calstat_fstr(n.stdev)]


def calstat_stat_call(c, fn):
    st = calstat_st
    if fn == "_exact_ratio":
        r = st._exact_ratio(calstat_obj(c["x"]))
        return [r[0], r[1]] if r[1] is not None else [calstat_res(r[0]), None]
    if fn == "_isfinite":
        return bool(st._isfinite(calstat_obj(c["x"])))
    if fn == "_coerce":
        return st._coerce(calstat_cls(c["T"]), calstat_cls(c["S"])).__name__
    if fn == "_sum":
        T, total, n = st._sum(calstat_L(c["data"]))
        return [T.__name__, calstat_res(total), n]
    if fn == "_ss":
        d = calstat_L(c["data"])
        T, ss, cc, n = st._ss(d, None if c["c"] is None else calstat_obj(c["c"]))
        return [T.__name__, calstat_res(ss), calstat_res(cc), n]
    if fn == "_convert":
        return calstat_res(st._convert(calstat_obj(c["x"]), calstat_cls(c["T"])))
    if fn == "_fail_neg":
        return [calstat_res(x) for x in st._fail_neg(calstat_L(c["data"]))]
    if fn == "_rank":
        r = st._rank(calstat_L(c["data"]), reverse=c["reverse"], ties=c["ties"], start=calstat_obj(c["start"]))
        return [calstat_res(x) for x in r]
    if fn == "_integer_sqrt_of_frac_rto":
        return st._integer_sqrt_of_frac_rto(c["n"], c["m"])
    if fn == "_float_sqrt_of_frac":
        return calstat_fstr(st._float_sqrt_of_frac(c["n"], c["m"]))
    if fn == "_decimal_sqrt_of_frac":
        return calstat_res(st._decimal_sqrt_of_frac(c["n"], c["m"]))
    if fn == "_mean_stdev":
        a, b = st._mean_stdev(calstat_L(c["data"]))
        return [calstat_fstr(a), calstat_fstr(b)]
    if fn == "_sqrtprod":
        return calstat_fstr(st._sqrtprod(calstat_obj("f:" + c["x"]), calstat_obj("f:" + c["y"])))
    if fn == "mean":
        return calstat_res(st.mean(calstat_L(c["data"])))
    if fn == "fmean":
        w = c["weights"]
        d = calstat_L(c["data"])
        return calstat_res(st.fmean(iter(d) if c["iter"] else d, None if w is None else calstat_L(w)))
    if fn == "nd.setstate":
        Z = st.NormalDist()
        Z.__setstate__(tuple(calstat_L(c["state"])))
        return [calstat_res(Z._mu), calstat_res(Z._sigma)]
    if fn == "_fail_neg_gen":
        out = []
        try:
            for v in st._fail_neg(calstat_L(c["data"])):
                out.append(calstat_res(v))
            end = None
        except Exception as e:
            end = type(e).__name__
        return [out, end]
    if fn == "quantiles_it":
        d = calstat_src(calstat_L(c["data"]), c["src"], c.get("exc"))
        return [calstat_res(x) for x in st.quantiles(d, n=c["n"], method=c["method"])]
    if fn == "fmean_it":
        d = calstat_src(calstat_L(c["data"]), c["src"], c.get("exc"))
        w = None
        if c["weights"] is not None:
            w = calstat_src(calstat_L(c["weights"]), c["wsrc"], c.get("wexc"))
        return calstat_res(st.fmean(d, w))
    if fn == "geometric_mean":
        return calstat_fstr(st.geometric_mean(calstat_L(c["data"])))
    if fn == "harmonic_mean":
        w = c["weights"]
        return calstat_res(st.harmonic_mean(calstat_L(c["data"]), None if w is None else calstat_L(w)))
    if fn in ("median", "median_low", "median_high", "mode"):
        return calstat_res(getattr(st, fn)(calstat_L(c["data"])))
    if fn == "median_grouped":
        return calstat_fstr(st.median_grouped(calstat_L(c["data"]), calstat_obj(c["interval"])))
    if fn == "multimode":
        return [calstat_res(x) for x in st.multimode(calstat_L(c["data"]))]
    if fn in ("variance", "pvariance", "stdev", "pstdev"):
        return calstat_res(getattr(st, fn)(calstat_L(c["data"]), None if c["c"] is None else calstat_obj(c["c"])))
    if fn == "covariance":
        return calstat_res(st.covariance(calstat_L(c["x"]), calstat_L(c["y"])))
    if fn == "correlation":
        return calstat_res(st.correlation(calstat_L(c["x"]), calstat_L(c["y"]), method=c["method"]))
    if fn == "linear_regression":
        r = st.linear_regression(calstat_L(c["x"]), calstat_L(c["y"]), proportional=c["proportional"])
        return [calstat_res(r.slope), calstat_res(r.intercept)]
    if fn == "quantiles":
        return [calstat_res(x) for x in st.quantiles(calstat_L(c["data"]), n=c["n"], method=c["method"])]
    if fn == "kde":
        d = calstat_L(c["data"])
        f = st.kde(d, calstat_obj(c["h"]), c["kernel"], cumulative=c["cumulative"])
        d[:] = calstat_L(c["data2"])
        return calstat_res(f(calstat_obj(c["x"])))
    if fn == "kde_random":
        script = calstat_Script(c["draws"], None)
        saved = st._random
        st._random = calstat_types.SimpleNamespace(Random=lambda seed: script)
        try:
            f = st.kde_random(calstat_L(c["data"]), calstat_obj(c["h"]), c["kernel"])
            return [calstat_res(f()) for _ in c["draws"]]
        finally:
            st._random = saved
    if fn == "kernel":
        return calstat_fstr(st._kernel_specs[c["kernel"]][c["which"]](calstat_obj("f:" + c["t"])))
    if fn == "nd.init":
        return calstat_ndpair(st.NormalDist(calstat_obj(c["mu"]), calstat_obj(c["sigma"])))
    if fn == "nd.from_samples":
        return calstat_ndpair(st.NormalDist.from_samples(calstat_L(c["data"])))
    if fn == "nd.samples":
        return [calstat_fstr(x) for x in calstat_nds(c).samples(len(c["us"]), seed=c["seed"])]
    if fn in ("nd.pdf", "nd.cdf", "nd.zscore"):
        return calstat_res(getattr(calstat_nds(c), fn[3:])(calstat_obj(c["x"])))
    if fn == "nd.inv_cdf":
        return calstat_fstr(calstat_nds(c).inv_cdf(calstat_obj(c["x"])))
    if fn == "nd.quantiles":
        return [calstat_fstr(x) for x in calstat_nds(c).quantiles(c["n"])]
    if fn == "nd.overlap":
        return calstat_fstr(calstat_nds(c).overlap(calstat_ndobj(c["Y"])))
    if fn == "nd.props":
        X = calstat_nds(c)
        return [calstat_fstr(v) for v in (X.mean, X.median, X.mode, X.stdev, X.variance)]
    if fn == "nd.add":
        return calstat_ndpair(calstat_nds(c) + calstat_ndobj(c["Y"]))
    if fn == "nd.sub":
        return calstat_ndpair(calstat_nds(c) - calstat_ndobj(c["Y"]))
    if fn == "nd.addc":
        v = calstat_obj(c["x"])
        return calstat_ndpair(calstat_nds(c) + v)
    if fn == "nd.subc":
        return calstat_ndpair(calstat_nds(c) - calstat_obj(c["x"]))
    if fn == "nd.mulc":
        return calstat_ndpair(calstat_nds(c) * calstat_obj(c["x"]))
    if fn == "nd.divc":
        return calstat_ndpair(calstat_nds(c) / calstat_obj(c["x"]))
    if fn == "nd.rsubc":
        return calstat_ndpair(calstat_obj(c["x"]) - calstat_nds(c))
    if fn == "nd.pos":
        return calstat_ndpair(+calstat_nds(c))
    if fn == "nd.neg":
        return calstat_ndpair(-calstat_nds(c))
    if fn == "nd.eq":
        return calstat_nds(c) == calstat_ndobj(c["Y"])
    if fn == "nd.hash":
        X = calstat_nds(c)
        return hash(X)
    if fn == "nd.repr" and c.get("cls"):
        sub = type(c["cls"], (st.NormalDist,), {"__slots__": ()})
        X = calstat_nds(c)
        return repr(sub(X.mean, X.stdev))
    if fn == "nd.repr":
        return repr(calstat_nds(c))
    if fn == "nd.state":
        X = calstat_nds(c)
        s = X.__getstate__()
        Y = st.NormalDist()
        Y.__setstate__(s)
        return [calstat_fstr(s[0]), calstat_fstr(s[1]), calstat_ndpair(Y)]
    raise KeyError(fn)


def calstat_run_stat(c):
    fn = c["fn"].split(".", 2)[2]
    real = calstat_math.erfc
    table = c.get("erfc")
    return py_result(lambda: calstat_stat_call(c, fn))

def calstat_gen(rng):
    if rng.random() < calstat_CAL_SHARE:
        return calstat_gen_cal(rng)
    return calstat_gen_stat(rng)


def calstat_run(c):
    if c["fn"].startswith("calstat.s."):
        return calstat_run_stat(c)
    return calstat_run_cal(c)


calstat_CAL_SHARE = 0.25
# ====== END AREA calstat ======

# ====== BEGIN AREA rand (Lib/random.py, Modules/_randommodule.c) ======
# Everything for this area stays between these two markers; prefix top-level names with rand_.
import _random as rand_c  # noqa: E402
import contextlib as rand_contextlib  # noqa: E402
import io as rand_io  # noqa: E402
import math as rand_math  # noqa: E402
import operator as rand_operator  # noqa: E402
import os as rand_os  # noqa: E402
import pickle as rand_pickle  # noqa: E402
import random as rand_random  # noqa: E402
import struct as rand_struct  # noqa: E402
import warnings as rand_warnings  # noqa: E402

rand_NAN_BITS = 0x7ff8000000000000


def rand_ienc(n):
    """JSON cannot carry ints past the 4300-digit limit: those cross as hex strings."""
    return n if abs(n) < 10**4000 else {"x": hex(n)}


def rand_idec(v):
    return int(v["x"], 16) if isinstance(v, dict) else v


def rand_bits(x):
    if x != x:
        return rand_NAN_BITS
    return rand_struct.unpack('<Q', rand_struct.pack('<d', x))[0]


def rand_float(b):
    return rand_struct.unpack('<d', rand_struct.pack('<Q', b))[0]


def rand_optf(b):
    return None if b is None else rand_float(b)


class rand_Sub(rand_random.Random):
    """Overrides random() only, so __init_subclass__ picks _randbelow_without_getrandbits."""

    def random(self):
        return super().random()


class rand_I(int):
    """An int subclass whose __abs__ must not be called (bpo-31478)."""

    def __abs__(self):
        raise RuntimeError("called")


class rand_H:
    def __init__(self, h):
        self.h = h

    def __hash__(self):
        return self.h


class rand_BadMod:
    """__mod__ raises ValueError, the only way into Lib/random.py:194."""

    def __mod__(self, other):
        raise ValueError("no")


def rand_mk(case):
    cls = rand_Sub if case.get("sub") else rand_random.Random
    r = cls(rand_idec(case.get("seed", 0)))
    for _ in range(case.get("burn", 0)):
        rand_c.Random.getrandbits(r, 32)
    return r


def rand_fp(r):
    st = rand_c.Random.getstate(r)
    return [st[624], st[0], st[311], st[623], rand_c.Random.getrandbits(r, 32)]


def rand_py(thunk):
    res = py_result(thunk)
    if "exc" in res:
        m = res["msg"]
        if res["exc"] == "ValueError" and (m.startswith("expected ") or m == "math domain error"):
            res["msg"] = "~domain"
        if res["exc"] == "UnicodeEncodeError":
            res["msg"] = "~surrogate"
    return res


def rand_wrap(res, r):
    return {"ok": {"r": res, "fp": rand_fp(r)}}


def rand_obj(ty):
    return {"float": 1.5, "NoneType": None, "str": "a", "bytes": b"x", "list": [1], "BadMod": rand_BadMod()}[ty]


def rand_arg(d):
    if "i" in d:
        return rand_idec(d["i"])
    if "b" in d:
        return d["b"]
    return rand_obj(d["o"])


def rand_elems(xs):
    return [rand_obj(x) if isinstance(x, str) else x for x in xs]


def rand_num(d):
    return rand_float(d["f"]) if "f" in d else rand_idec(d["i"])


def rand_call(case, thunk):
    r = rand_mk(case)
    return rand_wrap(rand_py(lambda: thunk(r)), r)


def rand_f(case, name, *keys):
    args = [rand_float(case[k]) for k in keys]
    return rand_call(case, lambda r: rand_bits(getattr(r, name)(*args)))


def rand_stub(r):
    real = rand_os.urandom

    def stub(n):
        if not isinstance(n, int) or n < 0 or n >= 2**20:
            return real(n)
        return bytes(rand_c.Random.getrandbits(r, 32) >> 24 for _ in range(n))
    return stub


def rand_sys(case, thunk):
    r = rand_mk(case)
    sr = rand_random.SystemRandom()
    saved = rand_random._urandom
    rand_random._urandom = rand_stub(r)
    try:
        res = rand_py(lambda: thunk(sr))
    finally:
        rand_random._urandom = saved
    return rand_wrap(res, r)


def rand_carg(case):
    k = case["kind"]
    if k == "int":
        return rand_idec(case["n"])
    if k == "intsub":
        return rand_I(rand_idec(case["n"]))
    if k == "hash":
        return rand_H(case["h"])
    return [1]


def rand_seedobj(case):
    k = case["kind"]
    if k == "none":
        return None
    if k == "int":
        return rand_idec(case["n"])
    if k == "intsub":
        return case["obj_bool"] if "obj_bool" in case else rand_I(rand_idec(case["n"]))
    if k == "float":
        return rand_float(case["x"])
    if k == "str":
        return ''.join(map(chr, case["b"]))
    if k == "bytes":
        return bytes(case["b"])
    if k == "bytearray":
        return bytearray(case["b"])
    return (1, 2)


def rand_h_cseed(c):
    r = rand_mk(c)
    return rand_wrap(rand_py(lambda: rand_c.Random.seed(r, rand_carg(c))), r)


def rand_h_cinit(c):
    r = rand_mk(c)
    res = {"ok": None}
    try:
        o = rand_c.Random(rand_carg(c))
    except Exception as e:
        res = {"exc": type(e).__name__, "msg": str(e)}
        o = r
    return rand_wrap(res, o)


def rand_h_getstate(c):
    r = rand_mk(c)
    acc = 0
    for i, x in enumerate(rand_c.Random.getstate(r)):
        acc = (acc + x * (i + 1)) % (2**61 - 1)
    return rand_wrap({"ok": acc}, r)


def rand_h_csetstate(c):
    r = rand_mk(c)
    st = tuple(rand_elems(c["xs"])) if c["ikind"] == "tuple" else list(rand_elems(c["xs"]))
    return rand_wrap(rand_py(lambda: rand_c.Random.setstate(r, st)), r)


def rand_state(c):
    sk = c["skind"]
    if sk == "notsub":
        return 3 if c["sty"] == "int" else None
    if sk == "emptytuple":
        return ()
    if sk == "emptylist":
        return []
    ik = c["ikind"]
    if ik == "tuple":
        inner = tuple(rand_elems(c["xs"]))
    elif ik == "list":
        inner = rand_elems(c["xs"])
    else:
        inner = 5
    full = (c["vobj"], inner, rand_optf(c.get("gauss")), 0, 0)
    return full[:c["len"]]


def rand_obj_result(res, r):
    g = r.gauss_next
    return {"ok": {"v": rand_wrap(res, r), "o": {"gauss": None if g is None else rand_bits(g)}}}


def rand_h_pysetstate(c):
    r = rand_mk(c)
    r.gauss_next = rand_optf(c.get("gauss0"))
    st = rand_state(c)
    return rand_obj_result(rand_py(lambda: r.setstate(st)), r)


def rand_h_pyseed(c):
    r = rand_mk(c)
    r.gauss_next = 1.5
    x = rand_seedobj(c)
    return rand_obj_result(rand_py(lambda: r.seed(x, version=c["version"])), r)


def rand_h_pickle(c):
    r = rand_mk(c)
    r.gauss_next = rand_optf(c.get("gauss0"))
    r2 = rand_pickle.loads(rand_pickle.dumps(r))
    return rand_obj_result({"ok": None}, r2)


def rand_h_new(c):
    o = rand_c.Random.__new__(rand_c.Random)
    for _ in range(c["skip"]):
        o.getrandbits(32)
    words = [o.getrandbits(32) for _ in range(c["n"])]
    return rand_wrap({"ok": words}, o)


def rand_h_time_pid(c):
    now, mono, pid = c["now"], c["mono"], c["pid"]
    key = [now & 0xffffffff, (now >> 32) & 0xffffffff, pid & 0xffffffff,
           mono & 0xffffffff, (mono >> 32) & 0xffffffff]
    o = rand_c.Random(sum(w << (32 * i) for i, w in enumerate(key)))
    return rand_wrap({"ok": key}, o)


def rand_randrange(r, c):
    kw = {}
    if "stop" in c and c["stop"] is not None:
        kw["stop"] = rand_arg(c["stop"])
    if "step" in c and c["step"] is not None:
        kw["step"] = rand_arg(c["step"])
    return r.randrange(rand_arg(c["start"]), **kw)


def rand_shuffle(r, c):
    imm = c.get("imm")
    if imm == "tuple":
        r.shuffle(tuple(c["x"]))
        return c["x"]
    if imm == "str":
        r.shuffle(''.join(map(str, c["x"])))
        return c["x"]
    y = list(c["x"])
    r.shuffle(y)
    return y


def rand_sample(r, c):
    pop = set(c["pop"]) if c["seqkind"] == "set" else list(c["pop"])
    counts = c.get("counts")
    if isinstance(counts, str):
        counts = rand_obj(counts) if counts != "int" else 5
    elif counts is not None:
        counts = [1.5 if x is None else x for x in counts]
    return r.sample(pop, c["k"], counts=counts)


def rand_choices(r, c):
    pop = list(c["pop"])
    w = c["weights"]
    if isinstance(w, dict):
        w = rand_arg(w["wint"]) if "wint" in w else rand_obj(w["wother"])
    elif w is not None:
        w = [rand_num(x) for x in w]
    cum = c["cum"]
    if cum is not None:
        cum = [rand_num(x) for x in cum]
    return r.choices(pop, w, cum_weights=cum, k=c["k"])


def rand_h_gauss(c):
    def go(r):
        r.gauss_next = rand_optf(c.get("gauss0"))
        v = r.gauss(rand_float(c["a"]), rand_float(c["b"]))
        n = r.gauss_next
        return {"v": rand_bits(v), "next": None if n is None else rand_bits(n)}
    return rand_call(c, go)


def rand_h_without(c):
    def go(r):
        with rand_warnings.catch_warnings():
            rand_warnings.simplefilter("ignore")
            return r._randbelow_without_getrandbits(c["n"])
    return rand_call(c, go)


rand_warnings.filterwarnings("ignore", message="Underlying random", category=UserWarning)


def rand_setsize(k):
    s = 21
    if k > 5:
        s += 4 ** rand_math.ceil(rand_math.log(k * 3, 4))
    return s


def rand_h_init_subclass(c):
    made, out = [], []
    for i, spec in enumerate(c["classes"]):
        d = {}
        if spec.get("rb"):
            d["_randbelow"] = lambda self, n: 0
            d["_randbelow"].__name__ = spec["rb"]
        if spec["gb"]:
            d["getrandbits"] = lambda self, k: 0
        if spec["rnd"]:
            d["random"] = lambda self: 0.0
        bases = tuple(rand_random.Random if b == -1 else made[b] for b in spec["bases"])
        cls = type(f"C{i}", bases, d)
        made.append(cls)
        f = getattr(cls, "_randbelow", None)
        out.append(f.__name__ if f is not None else None)
    return {"ok": {"r": {"ok": out}, "fp": rand_fp(rand_mk(c))}}


def rand_h_main(c):
    r = rand_random._inst
    r.seed(rand_idec(c.get("seed", 0)))
    for _ in range(c.get("burn", 0)):
        rand_c.Random.getrandbits(r, 32)

    def go():
        out = rand_random.main(c["argv"])
        if isinstance(out, float):
            return {"f": rand_bits(out)}
        if isinstance(out, int):
            return {"i": rand_ienc(out)}
        if out.startswith("usage:"):
            return {"s": "HELP"}
        return {"s": out}
    return rand_wrap(rand_py(go), r)


rand_handlers = {
    "words": lambda c: rand_call(c, lambda r: [r.getrandbits(32) for _ in range(c["n"])]),
    "random": lambda c: rand_call(c, lambda r: (lambda xs: {"bits": [rand_bits(x) for x in xs],
                                                            "nums": [int(x * 2**53) for x in xs]})(
        [r.random() for _ in range(c["n"])])),
    "getrandbits": lambda c: rand_call(c, lambda r: rand_ienc(r.getrandbits(rand_arg(c["k"])))),
    "cseed": rand_h_cseed,
    "cinit": rand_h_cinit,
    "getstate": rand_h_getstate,
    "csetstate": rand_h_csetstate,
    "pysetstate": rand_h_pysetstate,
    "pyseed": rand_h_pyseed,
    "pickle": rand_h_pickle,
    "new": rand_h_new,
    "time_pid": rand_h_time_pid,
    "randbelow_with": lambda c: rand_call(c, lambda r: r._randbelow_with_getrandbits(c["n"])),
    "randbelow_without": rand_h_without,
    "randbytes": lambda c: rand_call(c, lambda r: list(r.randbytes(rand_arg(c["n"])))),
    "randrange": lambda c: rand_call(c, lambda r: rand_ienc(rand_randrange(r, c))),
    "randint": lambda c: rand_call(c, lambda r: rand_ienc(r.randint(rand_arg(c["a"]), rand_arg(c["b"])))),
    "choice": lambda c: rand_call(c, lambda r: r.choice(c["pop"])),
    "choice_obj": lambda c: rand_call(c, lambda r: r.choice(dict(zip(c["keys"], c["vals"])))),
    "shuffle": lambda c: rand_call(c, lambda r: rand_shuffle(r, c)),
    "sample": lambda c: rand_call(c, lambda r: rand_sample(r, c)),
    "sample_range": lambda c: rand_call(c, lambda r: r.sample(range(c["n"]), c["k"])),
    "setsize": lambda c: rand_call(c, lambda r: rand_setsize(c["k"])),
    "choices": lambda c: rand_call(c, lambda r: rand_choices(r, c)),
    "uniform": lambda c: rand_f(c, "uniform", "a", "b"),
    "triangular": lambda c: rand_call(c, lambda r: rand_bits(r.triangular(
        rand_float(c["a"]), rand_float(c["b"]), rand_optf(c.get("c"))))),
    "normalvariate": lambda c: rand_f(c, "normalvariate", "a", "b"),
    "gauss": rand_h_gauss,
    "lognormvariate": lambda c: rand_f(c, "lognormvariate", "a", "b"),
    "expovariate": lambda c: rand_f(c, "expovariate", "a"),
    "vonmisesvariate": lambda c: rand_f(c, "vonmisesvariate", "a", "b"),
    "gammavariate": lambda c: rand_f(c, "gammavariate", "a", "b"),
    "betavariate": lambda c: rand_f(c, "betavariate", "a", "b"),
    "paretovariate": lambda c: rand_f(c, "paretovariate", "a"),
    "weibullvariate": lambda c: rand_f(c, "weibullvariate", "a", "b"),
    "lgamma": lambda c: rand_call(c, lambda r: rand_bits(rand_math.lgamma(rand_float(c["x"])))),
    "binomialvariate": lambda c: rand_call(c, lambda r: r.binomialvariate(c["n"], rand_float(c["p"]))),
    "sys_random": lambda c: rand_sys(c, lambda sr: rand_bits(sr.random())),
    "sys_getrandbits": lambda c: rand_sys(c, lambda sr: rand_ienc(sr.getrandbits(rand_arg(c["k"])))),
    "sys_randbytes": lambda c: rand_sys(c, lambda sr: list(sr.randbytes(rand_arg(c["n"])))),
    "sys_randrange": lambda c: rand_sys(c, lambda sr: rand_ienc(rand_randrange(sr, c))),
    "sys_seed": lambda c: rand_sys(c, lambda sr: sr.seed(1, 2, x=3)),
    "sys_state": lambda c: rand_sys(c, lambda sr: sr.getstate()),
    "init_subclass": rand_h_init_subclass,
    "main": rand_h_main,
}


def rand_run(case):
    return rand_handlers[case["fn"].split(".", 1)[1]](case)


rand_INTS = [0, 1, -1, 2, -2, 3, 7, 8, 31, 32, 33, 63, 64, 65, 255, 256, 1000, 2**31 - 1, 2**31, 2**32 - 1,
             2**32, 2**32 + 1, 2**53 - 1, 2**53, 2**53 + 1, 2**63 - 1, 2**63, -2**63, 2**64 - 1, 2**64, -2**64,
             2**128 + 5, 10**30, -10**30, 10**4300 - 1, 10**4300, -10**4300]
rand_SMALL_FLOATS = [0.0, -0.0, 1.0, -1.0, 0.5, 2.0, 3.0, 10.0, 1e-3, 0.25, 0.9, 1.5, 100.0, 1e-300, 1e300]
rand_ALL_FLOATS = rand_SMALL_FLOATS + [float('inf'), float('-inf'), float('nan'), 5e-324, 1.7976931348623157e308]


def rand_seed_val(rng):
    if rng.random() < 0.7:
        return rng.getrandbits(rng.choice([8, 32, 64, 256]))
    return rand_ienc(rng.choice([0, 1, -1, 2, 42, 2**32 - 1, 2**32, 2**32 + 1, 2**64 - 1, 2**64, -2**64, 2**63,
                                 2**128 + 5, (1 << 2000) + 3, (1 << 20000) + 1, 2**31, 2**19937 - 1]))


def rand_burn(rng):
    return rng.choice([0, 0, 1, 2, 3, 623, 624, 625, 1247, 1248, rng.randrange(1400)])


def rand_base(rng, name):
    return {"fn": "rand." + name, "seed": rand_seed_val(rng), "burn": rand_burn(rng)}


def rand_intarg(rng, vals=None, others=("float", "NoneType", "str", "bytes")):
    p = rng.random()
    if p < 0.05:
        return {"b": rng.random() < 0.5}
    if p < 0.1:
        return {"o": rng.choice(others)}
    if vals is not None and rng.random() < 0.5:
        return {"i": rand_ienc(rng.choice(vals))}
    if rng.random() < 0.5:
        return {"i": rand_ienc(rng.choice(rand_INTS))}
    return {"i": rng.randrange(-300, 301)}


def rand_clamp(d, lo, hi, *big):
    """Keep ints in [lo, hi] or among `big`, so that no case tries a huge allocation that may succeed."""
    if "i" not in d:
        return d
    v = rand_idec(d["i"])
    if v in big or v <= hi:
        return d
    return {"i": rand_ienc(big[int(v) % len(big)])}


def rand_pos(rng):
    p = rng.random()
    if p < 0.4:
        return rng.randrange(1, 300)
    if p < 0.7:
        return 1 << rng.randrange(1, 130)
    if p < 0.85:
        return (1 << rng.randrange(1, 130)) + rng.randrange(-1, 2) + 1
    return rng.getrandbits(rng.randrange(1, 200)) + 1


def rand_pop(rng, n=None):
    if n is None:
        n = rng.choice([0, 1, 2, 3, 5, 6, 7, 21, 22, 40, rng.randrange(120)])
    return [rng.randrange(1000) for _ in range(n)]


def rand_gen_core(rng, c):
    fn = c["fn"]
    if fn == "rand.words":
        c["n"] = rng.choice([1, 2, 3, 623, 624, 625, 1300])
    elif fn == "rand.random":
        c["n"] = rng.choice([1, 2, 3, 312, 313])
    elif fn == "rand.getrandbits":
        c["k"] = rand_intarg(rng, [0, 1, 2, 31, 32, 33, 63, 64, 65, 95, 96, 97, 1000, 19937, -1,
                                   2**64 - 1, 2**64, -2**64, 2**60, 2**63], ("float", "NoneType", "str"))
        c["k"] = rand_clamp(c["k"], 0, 2**20, 2**64 - 1, 2**63, 2**64, 2**60, 2**128)
    elif fn in ("rand.cseed", "rand.cinit"):
        k = rng.choice(["int", "int", "intsub", "hash", "unhashable"])
        c["kind"] = k
        if k in ("int", "intsub"):
            c["n"] = rand_seed_val(rng)
        elif k == "hash":
            c["h"] = rng.choice([0, 1, -2, 2**63 - 1, -2**63, rng.getrandbits(63), -rng.getrandbits(63) - 2])
        else:
            c["ty"] = "list"
    elif fn == "rand.time_pid":
        c["now"] = rng.choice([0, 1, -1, 1 << 62, -(1 << 62), rng.getrandbits(62), -rng.getrandbits(62)])
        c["mono"] = rng.getrandbits(62) | (1 << 40)
        c["pid"] = rng.getrandbits(32) + 1
    elif fn == "rand.new":
        c["n"] = rng.choice([1, 3, 700])
        c["skip"] = rng.choice([0, 1, 623, 624, 625, 1300])


def rand_state_xs(rng, c):
    base = list(rand_random.Random(rand_idec(c["seed"])).getstate()[1])
    n = rng.random()
    if n < 0.1:
        base = base[:rng.choice([0, 1, 624])]
    elif n < 0.15:
        base = base + [0]
    elif n < 0.5:
        base[624] = rng.choice([-1, 0, 1, 311, 623, 624, 625, 2**31, 2**63 - 1, 2**63, -2**63 - 1, 2**64,
                                "float", "NoneType"])
    elif n < 0.8:
        i = rng.choice([0, 1, 311, 623])
        base[i] = rng.choice([-1, 2**32 - 1, 2**32, 2**64 - 1, 2**64, -2**64, "float", "NoneType"])
    return base


def rand_gen_state(rng, c):
    fn = c["fn"]
    if fn == "rand.csetstate":
        c["ikind"] = rng.choice(["tuple"] * 5 + ["list"])
        c["xs"] = rand_state_xs(rng, c)
    elif fn == "rand.pysetstate":
        c["gauss0"] = rng.choice([None, rand_bits(0.25)])
        p = rng.random()
        if p < 0.05:
            c["skind"] = "notsub"
            c["sty"] = rng.choice(["int", "NoneType"])
        elif p < 0.1:
            c["skind"] = rng.choice(["emptytuple", "emptylist"])
        else:
            c["skind"] = "seq"
            c["len"] = rng.choice([3, 3, 3, 3, 3, 3, 1, 2, 4, 5])
            vobj, vval = rng.choice([(3, 3), (3, 3), (3, 3), (2, 2), (2, 2), (3.0, 3), (2.0, 2), (1, 1), (0, 0),
                                     (True, 1), (4, 4), ("3", None), ("x", None), (2.5, None)])
            c["vobj"], c["vval"], c["vtext"] = vobj, vval, str(vobj)
            c["ikind"] = rng.choice(["tuple", "tuple", "tuple", "list", "other"])
            c["ity"] = "int"
            c["gauss"] = rng.choice([None, rand_bits(1.5)])
            c["xs"] = rand_state_xs(rng, c)
            if vval == 2 and rng.random() < 0.3:
                i = rng.randrange(625) if c["xs"] else 0
                if c["xs"]:
                    c["xs"][i % len(c["xs"])] = rng.choice(["BadMod", "NoneType", "float", -1, -2**70, 2**70])
    elif fn == "rand.pickle":
        c["gauss0"] = rng.choice([None, rand_bits(0.25)])
    elif fn == "rand.pyseed":
        c["version"] = rng.choice([2, 2, 2, 1, 1, 0, 3])
        k = rng.choice(["none_skip", "int", "intsub", "float", "str", "bytes", "bytearray", "other"])
        if k == "none_skip":
            k = "int"
        c["kind"] = k
        if k in ("int", "intsub"):
            c["n"] = rand_seed_val(rng)
            if k == "intsub" and rng.random() < 0.3:
                c["n"] = 1
                c["obj_bool"] = True
        elif k == "float":
            x = rng.choice(rand_SMALL_FLOATS + [rng.random(), float('inf'), float('-inf')])
            c["x"] = rand_bits(x)
            c["h"] = hash(x)
        elif k in ("str", "bytes", "bytearray"):
            n = rng.choice([0, 1, 2, 3, 55, 111, 112, 127, 128, 129, 300])
            top = 256 if k != "str" else rng.choice([128, 256, 0x800, 0x10000, 0x110000])
            b = [rng.randrange(top) for _ in range(n)]
            if k == "str" and rng.random() < 0.1 and b:
                b[rng.randrange(n)] = rng.randrange(0xD800, 0xE000)
            elif k == "str":
                b = [x if not 0xD800 <= x < 0xE000 else 65 for x in b]
            c["b"] = b
            if k == "str":
                c["h"] = hash(''.join(map(chr, b)))
            elif k == "bytes":
                c["h"] = hash(bytes(b))


def rand_gen_exact(rng, c):
    fn = c["fn"]
    c["sub"] = rng.random() < 0.3 and fn in ("rand.randrange", "rand.randint", "rand.choice", "rand.shuffle",
                                             "rand.sample", "rand.sample_range", "rand.main")
    if fn == "rand.randbelow_with":
        c["n"] = rand_pos(rng)
    elif fn == "rand.randbelow_without":
        c["n"] = rand_pos(rng) if rng.random() < 0.8 else rng.choice([2**53 - 1, 2**53, 2**53 + 1, 2**60, 10**400])
    elif fn == "rand.randbytes":
        c["n"] = rand_intarg(rng, [0, 1, 2, 3, 4, 5, 7, 8, 9, 16, 1000, -1, 2**61, 2**62, 2**64])
        c["n"] = rand_clamp(c["n"], 0, 2**17, 2**61, 2**62, 2**64)
    elif fn == "rand.randrange":
        c["start"] = rand_intarg(rng)
        if rng.random() < 0.8:
            c["stop"] = rand_intarg(rng)
            if rng.random() < 0.6:
                c["step"] = rand_intarg(rng, [1, -1, 2, -2, 0, 3, 10, 2**64, -2**64, 2**100])
        elif rng.random() < 0.3:
            c["step"] = rand_intarg(rng, [1, 1, 2])
    elif fn == "rand.randint":
        c["a"] = rand_intarg(rng)
        c["b"] = rand_intarg(rng)
    elif fn == "rand.choice":
        c["pop"] = rand_pop(rng)
    elif fn == "rand.choice_obj":
        c["keys"] = rng.choice([[0, 1], [0, 2], [5], [1, 0, 2], [0]])
        c["vals"] = [rng.randrange(100) for _ in c["keys"]]
    elif fn == "rand.shuffle":
        c["x"] = rand_pop(rng)
        if rng.random() < 0.15:
            c["imm"] = rng.choice(["tuple", "str"])
            c["x"] = [rng.randrange(10) for _ in range(rng.choice([0, 1, 2, 3, 9]))]
    elif fn == "rand.sample":
        c["pop"] = rand_pop(rng)
        c["seqkind"] = rng.choice(["list"] * 19 + ["set"])
        n = len(c["pop"])
        p = rng.random()
        c["k"] = rng.choice([-1, 0, 1, n - 1, n, n + 1, rng.randrange(n + 1), rng.randrange(n + 1), 5, 6, 7])
        if p < 0.4:
            q = rng.random()
            if q < 0.03:
                c["counts"] = "int"
            elif q < 0.06:
                c["counts"] = [1] * (n + 1)
            elif q < 0.5:
                c["counts"] = [rng.randrange(6) for _ in range(n)]
                c["k"] = rng.randrange(sum(c["counts"]) + 2)
            elif q < 0.7:
                c["counts"] = [rng.randrange(-3, 6) for _ in range(n)]
                c["k"] = rng.randrange(0, max(1, sum(c["counts"]) + 2))
            elif q < 0.8:
                c["counts"] = [rng.choice([None, 1, 2]) for _ in range(n)]
            elif q < 0.9:
                c["counts"] = [2**rng.randrange(62, 66) for _ in range(n)]
                c["k"] = rng.randrange(0, 5)
            else:
                c["counts"] = [rng.randrange(40) for _ in range(n)]
                c["k"] = rng.randrange(0, max(1, sum(c["counts"])))
    elif fn == "rand.sample_range":
        c["n"] = rng.choice([0, 1, 21, 22, 40, 100, 1000, 10**6, 2**31, 2**62, 2**63 - 1, 2**63, 2**64, 10**30])
        c["k"] = rng.choice([0, 1, 2, 5, 6, 7, 20, 21, 22, 30, 100, 300])
    elif fn == "rand.setsize":
        c["k"] = rng.choice([0, 1, 5, 6, 7, 8, 21, 22, 85, 86, 341, 342, 1365, 1366, 5461, 5462,
                             rng.randrange(10**6), rng.randrange(2**40), (4**rng.randrange(1, 20) + 2) // 3,
                             (4**rng.randrange(1, 20) - 1) // 3])
    elif fn == "rand.choices":
        c["pop"] = rand_pop(rng)
        c["seqkind"] = "list"
        n = len(c["pop"])
        c["k"] = rng.choice([-1, 0, 1, 2, 5, 20])
        c["weights"], c["cum"] = None, None
        p = rng.random()

        def num():
            q = rng.random()
            if q < 0.5:
                return {"i": rng.randrange(0, 6)}
            if q < 0.9:
                return {"f": rand_bits(rng.choice([0.0, 0.5, 1.5, 1e-3, rng.random()]))}
            return rng.choice([{"i": -1}, {"i": 2**70}, {"i": 10**400}, {"f": rand_bits(float('inf'))},
                               {"f": rand_bits(float('nan'))}, {"f": rand_bits(-0.5)}])
        if p < 0.3:
            pass
        elif p < 0.6:
            c["weights"] = [num() for _ in range(n)]
        elif p < 0.8:
            acc, cum = 0, []
            for _ in range(n):
                acc += rng.randrange(0, 4)
                cum.append({"i": acc})
            c["cum"] = cum
        elif p < 0.9:
            c["cum"] = [num() for _ in range(n)]
        elif p < 0.93:
            c["weights"] = [num() for _ in range(n + 1)]
        elif p < 0.96:
            c["weights"] = {"wint": rng.choice([{"i": 2}, {"b": True}])}
        elif p < 0.98:
            c["weights"] = {"wother": "float"}
        else:
            c["weights"] = [{"i": 1} for _ in range(n)]
            c["cum"] = [{"i": 1} for _ in range(n)]


def rand_gen_dist(rng, c):
    fn = c["fn"]

    def f(pool=rand_ALL_FLOATS):
        return rand_bits(rng.choice(pool + [rng.uniform(-5, 5)]))

    def pos(pool=(0.01, 0.1, 0.5, 0.9, 1.0, 1.0, 1.1, 2.0, 3.5, 20.0, 200.0, 1e4, 1e-3, 1e-5, 1e300)):
        return rand_bits(rng.choice(list(pool) + [rng.random() + 1e-3, rng.uniform(1, 50)]))
    if fn in ("rand.uniform", "rand.normalvariate", "rand.lognormvariate", "rand.gauss"):
        c["a"], c["b"] = f(), f()
        if fn == "rand.gauss":
            c["gauss0"] = rng.choice([None, None, rand_bits(0.75)])
    elif fn == "rand.triangular":
        c["a"], c["b"] = f(), f()
        c["c"] = rng.choice([None, c["a"], c["b"], f()])
    elif fn in ("rand.expovariate", "rand.paretovariate"):
        c["a"] = f()
    elif fn == "rand.weibullvariate":
        c["a"], c["b"] = f(), f()
    elif fn == "rand.vonmisesvariate":
        c["a"] = f()
        c["b"] = rand_bits(rng.choice([0.0, 1e-7, 1e-6, 2e-6, 0.5, 1.0, 4.0, 100.0, 1e6, -1.0, float('inf')]))
    elif fn == "rand.gammavariate":
        c["a"], c["b"] = pos(), pos()
        if rng.random() < 0.15:
            c["a"] = rand_bits(rng.choice([0.0, -1.0, -0.0]))
        elif rng.random() < 0.15:
            c["b"] = rand_bits(rng.choice([0.0, -1.0, float('nan'), float('inf')]))
    elif fn == "rand.betavariate":
        c["a"], c["b"] = pos(), pos()
        if rng.random() < 0.05:
            c["b"] = rand_bits(-1.0)
    elif fn == "rand.lgamma":
        c["x"] = rand_bits(float(rng.choice([1, 2, 3, 4, 5, 6, 7, rng.randrange(1, 40), rng.randrange(1, 3000),
                                             rng.randrange(1, 10**7), 2**53, 10**20])) + rng.choice([0.0, 0.0, 0.5]))
    elif fn == "rand.binomialvariate":
        c["n"] = rng.choice([-1, 0, 1, 2, 3, 10, 19, 20, 21, 100, 1000, 10**6, 10**15, 2**53, 2**64, 10**400])
        c["p"] = rand_bits(rng.choice([0.0, -0.0, 1.0, 0.5, 0.1, 0.9, 1e-9, 1 - 1e-9, 0.3, 0.7, 1.5, -0.1, 1e-20,
                                       float('nan'), float('inf'), rng.random()]))


def rand_gen_sys(rng, c):
    fn = c["fn"]
    if fn == "rand.sys_getrandbits":
        c["k"] = rand_intarg(rng, [0, 1, 7, 8, 9, 16, 17, -1, 2**70], ("float", "NoneType", "str"))
        c["k"] = rand_clamp(c["k"], 0, 2**15, 2**70)
    elif fn == "rand.sys_randbytes":
        c["n"] = rand_intarg(rng, [0, 1, 2, 7, 8, -1, 2**70], ("float", "NoneType", "str"))
        c["n"] = rand_clamp(c["n"], 0, 2**15, 2**70)
    elif fn == "rand.sys_randrange":
        c["start"] = {"i": rand_pos(rng) if rng.random() < 0.8 else rng.choice([0, -1])}
        if rng.random() < 0.5:
            c["stop"] = {"i": c["start"]["i"] + rng.randrange(-1, 100)}
            if rng.random() < 0.2:
                c["start"] = {"i": 5000}


def rand_gen_subclass(rng, c):
    specs, made = [], []
    for i in range(rng.randrange(1, 6)):
        mixin = rng.random() < 0.25
        if mixin or not made:
            bases = [] if mixin else [-1]
        else:
            k = rng.randrange(1, min(3, len(made)) + 1)
            bases = rng.sample(range(len(made)), k)
            if rng.random() < 0.3:
                bases.insert(rng.randrange(len(bases) + 1), -1)
        spec = {"bases": bases, "mixin": mixin, "gb": rng.random() < 0.3, "rnd": rng.random() < 0.3}
        if not mixin and rng.random() < 0.15:
            spec["rb"] = f"custom{i}"
        d = {}
        for name, flag in (("getrandbits", spec["gb"]), ("random", spec["rnd"]), ("_randbelow", spec.get("rb"))):
            if flag:
                d[name] = lambda self, *a: 0
        try:
            cls = type(f"G{i}", tuple(rand_random.Random if b == -1 else made[b] for b in bases), d)
        except TypeError:
            return None
        made.append(cls)
        mro = []
        for k_ in cls.__mro__:
            if k_ is rand_random.Random:
                break
            if k_ is not object:
                mro.append(made.index(k_))
        spec["mro"] = mro
        spec["random"] = issubclass(cls, rand_random.Random)
        specs.append(spec)
    c["classes"] = specs
    return c


def rand_gen_main(rng, c):
    p = rng.random()
    if p < 0.5:
        val = rng.choice(["0", "-5", "1", "5", "10", "1.5", "-1.5", "0.0", "1e3", "inf", "nan", "-inf", "a b c", "abc",
                          " ", "", "  x  ", "1_000", "-1", "-" + "1" + "0" * 400, "1" + "0" * 400, "1" + "0" * 5000,
                          str(rng.randrange(-20, 200)), str(rng.uniform(-3, 3))])
        argv = ["--", val] if val.startswith("-") and rng.random() < 0.5 else [val]
    elif p < 0.65:
        argv = [rng.choice(["a", "b", "1", "2.5"]) for _ in range(rng.randrange(2, 6))]
    elif p < 0.75:
        argv = [rng.choice(["-c", "--choice"])] + [rng.choice(["a", "b", "c"]) for _ in range(rng.randrange(1, 5))]
    elif p < 0.85:
        argv = [rng.choice(["-i", "--integer"]), str(rng.choice([0, 1, 5, -3, 100]))]
    elif p < 0.93:
        argv = [rng.choice(["-f", "--float"]), rng.choice(["0", "1.5", "-2.5", "100"])]
    elif p < 0.97:
        argv = []
    else:
        argv = ["--test", "0", rng.choice(["5", "a"])]
    c["argv"] = argv
    try:
        with rand_contextlib.redirect_stderr(rand_io.StringIO()):
            args, _ = rand_random._parse_args(argv)
    except SystemExit:
        return None

    def inp(x):
        try:
            ai = int(x)
        except ValueError:
            ai = None
        try:
            af = rand_bits(float(x))
        except ValueError:
            af = None
        return {"asint": ai, "asfloat": af, "words": x.split()}
    c["choice"] = args.choice
    c["integer"] = args.integer
    c["float"] = None if args.float is None else rand_bits(args.float)
    c["test"] = args.test
    c["input"] = [inp(x) for x in args.input]
    c["inputstrs"] = list(args.input)
    return c


rand_GROUPS = {
    rand_gen_core: ["words", "random", "getrandbits", "cseed", "cinit", "getstate", "new", "time_pid"],
    rand_gen_state: ["csetstate", "pysetstate", "pyseed", "pickle"],
    rand_gen_exact: ["randbelow_with", "randbelow_without", "randbytes", "randrange", "randrange", "randint",
                     "choice", "choice_obj", "shuffle", "sample", "sample", "sample", "sample_range", "setsize",
                     "choices", "choices"],
    rand_gen_dist: ["uniform", "triangular", "normalvariate", "gauss", "lognormvariate", "expovariate",
                    "vonmisesvariate", "gammavariate", "betavariate", "paretovariate", "weibullvariate",
                    "binomialvariate", "binomialvariate", "lgamma"],
    rand_gen_sys: ["sys_random", "sys_getrandbits", "sys_randbytes", "sys_randrange", "sys_seed", "sys_state"],
}
rand_TABLE = [(g, n) for g, names in rand_GROUPS.items() for n in names]


def rand_gen(rng):
    p = rng.random()
    if p < 0.03:
        return rand_gen_subclass(rng, rand_base(rng, "init_subclass"))
    if p < 0.09:
        c = rand_base(rng, "main")
        c["sub"] = False
        return rand_gen_main(rng, c)
    g, n = rng.choice(rand_TABLE)
    c = rand_base(rng, n)
    r = g(rng, c)
    return c if r is None else r
# ====== END AREA rand ======

# ====== BEGIN AREA warn (Python/_warnings.c, Lib/_py_warnings.py) ======
import json as warn_json  # noqa: E402
import contextvars as warn_contextvars  # noqa: E402
import io as warn_io  # noqa: E402
import builtins as warn_builtins  # noqa: E402
import re as warn_re  # noqa: E402
from test.support import import_helper as warn_ih  # noqa: E402

# The process's own warnings machinery, as the other areas left it, before this area touches it.
# The warn cases rebind `sys.modules['warnings']` to `warn_c` (whose `_showwarnmsg` they leave a
# no-op) and empty the interpreter's filters list in place; C `warn` looks up `filters`,
# `defaultaction`, `onceregistry` and `_showwarnmsg` on `sys.modules['warnings']`. Left that way,
# every later case of another area that records a warning with the stock `catch_warnings(record=True)`
# records nothing. `warn_restore_std` puts this back after the warmup and after each warn case.
warn_STD_MODS = {k: sys.modules.get(k) for k in ("warnings", "_warnings", "_py_warnings")}
warn_STD_FILTERS_OBJ = warn_STD_MODS["warnings"].filters
warn_STD_FILTERS = list(warn_STD_FILTERS_OBJ)


def warn_restore_std():
    """Give the other areas the process warnings state they had before this area ran.

    Their Lean models assume a warning reaches the stock `warnings` module: each such case
    records with `catch_warnings(record=True)` under `simplefilter("always")` (or `"error"`), so
    the default filters, the once registry and any `__warningregistry__` do not decide the outcome.
    """
    for k, v in warn_STD_MODS.items():
        if v is None:
            sys.modules.pop(k, None)
        else:
            sys.modules[k] = v
    std = warn_STD_MODS["warnings"]
    std.filters = warn_STD_FILTERS_OBJ
    warn_STD_FILTERS_OBJ[:] = warn_STD_FILTERS


warn_py = warn_ih.import_fresh_module('_py_warnings')
warn_py._set_module(warn_py)
warn_c = warn_ih.import_fresh_module("warnings", fresh=["_warnings", "_py_warnings"])
warn_c._set_module(warn_c)
warn_PYG = warn_c.catch_warnings.__init__.__globals__   # the _py_warnings module warn_c uses


class warn_W1(UserWarning):
    pass


class warn_Meta(type):
    def __subclasscheck__(cls, sub):
        raise KeyError('boom')


class warn_Odd(UserWarning, metaclass=warn_Meta):
    pass


class warn_BadInit(UserWarning):
    def __init__(self, *a):
        raise ValueError("bad message")


warn_W1.__name__ = "W1"
warn_BadInit.__name__ = "BadInit"
warn_CATS = [Warning, UserWarning, warn_W1, DeprecationWarning, warn_Odd, warn_BadInit]


class warn_LieW(UserWarning):
    """A Warning whose `__class__` gives DeprecationWarning (category 6)."""

    @property
    def __class__(self):
        return DeprecationWarning


class warn_LieU(str):
    @property
    def __class__(self):
        return UserWarning


class warn_LieI(str):
    @property
    def __class__(self):
        return int


class warn_RaiseS(str):
    @property
    def __class__(self):
        raise ValueError("cls")


class warn_RaiseA(str):
    @property
    def __class__(self):
        raise AttributeError("cls")


class warn_AE(AttributeError):
    pass


warn_LieW.__name__ = "LieW"
warn_AE.__name__ = "AE"
# the registry keys of the warn_explicit and warn cases can also hold LieW
warn_CATS_WE = warn_CATS + [warn_LieW]
warn_MSGS = {"lieU": warn_LieU, "lieI": warn_LieI, "raise": warn_RaiseS, "raiseA": warn_RaiseA}


def warn_install_getattr(mod, spec):
    """A module `__getattr__` that raises what `spec` names for an attribute, AttributeError else."""
    def ga(name):
        k = spec.get(name)
        if k == "key":
            raise KeyError("k")
        if k == "ae":
            raise warn_AE("a")
        raise AttributeError(f"module {mod.__name__!r} has no attribute {name!r}")
    mod.__getattr__ = ga


class warn_Bad:
    def match(self, *a):
        raise ValueError("bad pattern")


warn_ACTS = ["error", "ignore", "always", "all", "default", "module", "once"]
warn_TEXTS = ["a", "ab", "b", "A", "xb"]


def warn_gen_we(rng):
    def pat(mod):
        return rng.choice([None, None, "a", "ab", ".*b", "x"] + (["m"] if mod else []) +
                          (["RAISE"] if rng.random() < .1 else []) +
                          ([rng.choice(["PLAIN:a", "PLAIN:m", "PLAIN:ab", "PLAIN:x.a"])] if rng.random() < .1 else []))
    fs = []
    for _ in range(rng.choice([0, 1, 1, 2, 3])):
        fs.append([rng.choice(warn_ACTS + (["bogus"] if rng.random() < .05 else []) + ([5] if rng.random() < .03 else [])
                              + ([["u"]] if rng.random() < .03 else [])),
                   pat(False),
                   rng.choice([0, 1, 1, 2, 3] + ([4] if rng.random() < .1 else [])), pat(True),
                   rng.choice([0, 0, 0, 1, 2] + ([2**63, 2**64] if rng.random() < .05 else [])
                              + (["5"] if rng.random() < .03 else [])),
                   rng.choice(["tuple"] * 30 + ["list", "short"])])
    text = rng.choice(warn_TEXTS)
    cat = rng.choice([0, 1, 2, 3] + ([5] if rng.random() < .05 else []))
    ln = rng.choice([0, 1, 1, 2, -1] + ([2**31, -2**31 - 1, 2**31 - 1] if rng.random() < .05 else []) +
                    ([["obj", rng.choice(["s5", "f", "x"])]] if rng.random() < .04 else []))

    def entries():
        es = []
        k = rng.random()
        if k < .5:
            es.append(["v", "cur"])
        elif k < .7:
            es.append(["v", "stale"])
        elif k < .75:
            es.append(["v", rng.choice([2**64, -2**64, 2**63])])
        elif k < .78:
            es.append(["v", "true"])
        for _ in range(rng.choice([0, 0, 1, 2])):
            t = rng.choice([text, rng.choice(warn_TEXTS)])
            c = rng.choice([cat, rng.choice([0, 1, 2, 3])])
            v = rng.choice([1, 1, 0])
            if rng.random() < .5:
                es.append(["t", t, c, rng.choice([ln if isinstance(ln, int) else 5, 0, 1]), v])
            else:
                es.append(["p", t, c, v])
        # one entry per key, as a dict
        seen, out = set(), []
        for e in es:
            key = tuple(e[:-1]) if e[0] != "v" else ("v",)
            if key not in seen:
                seen.add(key)
                out.append(e)
        return out
    reg = None if rng.random() < .25 else ("obj" if rng.random() < .03 else
                                          {"map": entries()} if rng.random() < .03 else entries())
    once = entries() if rng.random() < .5 else []
    module = rng.choice([["omit"], ["omit"], ["none"], ["s", "a"], ["s", "m"], ["s", "x.a"], ["s", "b"]] +
                        ([["obj"]] if rng.random() < .05 else []))
    extra = {}
    if rng.random() < .25:
        k = rng.random()
        if k < .15:
            extra["ctx"] = True
        if rng.random() < .1:
            extra["tuple"] = True
        if rng.random() < .15:
            extra["dfltdel"] = True
        if rng.random() < .2:
            extra["oncek"] = rng.choice(["int", "deleted"])
        if rng.random() < .3:
            extra["show"] = rng.choice(["deleted", "noncallable", "nowm"])
        if rng.random() < .3:
            extra["globs"] = rng.choice(["int", "empty", "bad"])
        ga = {}
        if extra.get("dfltdel") and rng.random() < .5:
            ga["defaultaction"] = rng.choice(["key", "ae"])
        if extra.get("oncek") == "deleted" and rng.random() < .5:
            ga["onceregistry"] = rng.choice(["key", "ae"])
        if extra.get("show") == "deleted" and rng.random() < .5:
            ga["_showwarnmsg"] = rng.choice(["key", "ae"])
        if extra.get("show") == "nowm" and rng.random() < .5:
            ga["WarningMessage"] = rng.choice(["key", "ae"])
        if ga:
            extra["getattr"] = ga
    if rng.random() < .1:
        extra["msg"] = rng.choice(["lieU", "lieI", "raise", "raiseA"] + (["inst", "instlie"] if cat != 5 else []))
    if rng.random() < .06:
        imp = rng.choice(["raise", "none"])
        if imp == "raise" or (extra.get("oncek") != "int" and not extra.get("ctx") and not extra.get("tuple")
                              and "getattr" not in extra):
            extra["imp"] = imp
    dflt = rng.choice(["default", "default", "always", "error", "ignore", "once", "module"] +
                      (["bogus"] if rng.random() < .03 else []) + ([5] if rng.random() < .02 else []))
    if extra.get("imp") == "none" and not isinstance(dflt, str):
        dflt = "default"
    if "imp" in extra:
        # the import under a pending OverflowError (a version outside C long) is out of the model's
        # scope (Model.lean): keep the versions in range
        def fit(es):
            return [["v", "cur"] if e[0] == "v" and isinstance(e[1], int) else e for e in es]
        once = fit(once)
        if isinstance(reg, list):
            reg = fit(reg)
        elif isinstance(reg, dict):
            reg = {"map": fit(reg["map"])}
    return {"fn": "warn." + rng.choice(["c", "py"]), "filters": fs, **extra,
            "dflt": dflt,
            "text": text, "cat": cat, "filename": rng.choice(["a.py", "m.py", "<s>", "", "pkg/a.py",
                                                              "x/__init__.py", "g", "b.py"]),
            "lineno": ln, "module": module, "reg": reg, "once": once,
            "showraise": rng.random() < .05}


def warn_pat(p, ci):
    if p is None:
        return None
    if p == "RAISE":
        return warn_Bad()
    if p.startswith("PLAIN:"):
        return p[6:]
    return warn_re.compile(p, warn_re.I if ci else 0)


def warn_item(f):
    fields = ([] if f[0] == ["u"] else f[0], warn_pat(f[1], True), warn_CATS[f[2]], warn_pat(f[3], False), f[4])
    if f[5] == "list":
        return list(fields)
    if f[5] == "short":
        return fields[:3]
    return fields


warn_LINES = {"s5": "5", "f": 5.5, "x": "x"}


def warn_norm(msg):
    for prefix, rep in (("Can't compare", "~Can't compare str and object"),
                        ("action must be a string", "~action must be a string"),
                        ("warnings.defaultaction must be a string", "~warnings.defaultaction must be a string"),
                        ("_warnings.defaultaction must be a string", "~warnings.defaultaction must be a string")):
        if msg.startswith(prefix):
            return rep
    if msg.endswith("object has no attribute 'get'"):
        return "~object has no attribute 'get'"
    # the Python twin under test is the module `_py_warnings`; as `warnings` its name is `warnings`
    return msg.replace("module '_py_warnings'", "module 'warnings'")


def warn_key(e):
    if e[0] == "t":
        return (e[1], warn_CATS_WE[e[2]], e[3])
    if e[0] == "p":
        return (e[1], warn_CATS_WE[e[2]])
    return "version"


def warn_mkdict(es, cur):
    d = {}
    for e in es:
        if e[0] == "v":
            v = e[1]
            d["version"] = cur if v == "cur" else cur - 1 if v == "stale" else True if v == "true" else v
        else:
            d[warn_key(e)] = e[-1]
    return d


def warn_enc(d, cur):
    out = []
    for k, v in d.items():
        if k == "version":
            out.append(["v", "cur" if v == cur else "stale" if v == cur - 1 else int(v)])
        elif len(k) == 3:
            out.append(["t", str(k[0]), warn_CATS_WE.index(k[1]), k[2], int(v)])
        else:
            out.append(["p", str(k[0]), warn_CATS_WE.index(k[1]), int(v)])
    return sorted(out, key=lambda e: warn_json.dumps(e, separators=(',', ':')))


class warn_Map:
    """A mapping registry that is not a dict: `get`, `clear` and item assignment."""

    def __init__(self, d):
        self.d = d

    def get(self, k, default=None):
        return self.d.get(k, default)

    def clear(self):
        self.d.clear()

    def __setitem__(self, k, v):
        self.d[k] = v


class warn_BadLoader:
    def get_source(self, name):
        raise ValueError("no source")


warn_BAD_GLOBALS_LOADER = warn_BadLoader()


def warn_globals(kind):
    if kind == "int":
        return 5
    if kind == "empty":
        return {}
    import types
    return {"__name__": "m", "__loader__": warn_BAD_GLOBALS_LOADER,
            "__spec__": types.SimpleNamespace(name="m", loader=warn_BAD_GLOBALS_LOADER)}


warn_ONCE_C = warn_c.onceregistry
warn_ONCE_PY = warn_py.onceregistry
warn_FILTERS_C = warn_c.filters
warn_FILTERS_PY = warn_py.filters


def warn_run_we(case):
    return warn_contextvars.copy_context().run(warn_run_we1, case)


class warn_YMeta(type):
    def mro(cls):
        return [cls, UnicodeEncodeError, BaseException, object]


class warn_Y(UnicodeEncodeError, metaclass=warn_YMeta):
    """In UnicodeEncodeError's MRO but, by its metaclass, not under UnicodeError or ValueError."""

    def __str__(self):
        return "y"


def warn_mk_y(*a):
    return warn_Y("utf-8", "x", 0, 1, "r")


warn_Y.__name__ = "Y"
# `except Exception` does not catch a Y (its MRO leaves Exception out), so the harness catches both.
warn_EXC = (Exception, warn_Y)

# The Python twin's filters version starts at 1, where a registry version `True` (== 1) would encode
# as "cur" or "stale" (the model's version is symbolic and large); start it above both.
for _ in range(3):
    warn_py._filters_mutated()


def warn_run_we1(case):
    import linecache
    linecache.clearcache()
    twin = case["fn"].split(".")[1]
    mod = warn_c if twin == "c" else warn_py
    sys.modules['warnings'] = warn_c
    mod.filters = warn_FILTERS_C if mod is warn_c else warn_FILTERS_PY
    items = [warn_item(f) for f in case["filters"]]
    mod.filters[:] = items
    mod._filters_mutated()
    if twin == "c":
        probe = {}
        mod.filters[:] = []
        mod.defaultaction = "ignore"
        mod.warn_explicit("probe", UserWarning, "p", 1, registry=probe)
        mod.filters[:] = items
        cur = probe["version"]
    else:
        cur = mod._filters_version
    mod.defaultaction = case["dflt"]
    if case.get("tuple"):
        mod.filters = tuple(items)
    if case.get("ctx") and twin == "c":
        mod._warnings_context.set(warn_PYG["_Context"](mod.filters))
    if case.get("imp") == "none" and twin == "c" and not case.get("dfltdel"):
        # C reads `defaultaction` once here, so the value it caches is the current one: with
        # `sys.modules['warnings']` None its lookup finds nothing and uses that cache
        # (the filters list is emptied in place: C caches the list object, and with
        # sys.modules['warnings'] None it searches that cached list)
        saved_show, saved_f = mod._showwarnmsg, list(mod.filters)
        mod._showwarnmsg = lambda m: None
        mod.filters[:] = []
        try:
            mod.warn_explicit("probe2", UserWarning, "p", 1, registry={})
        except warn_EXC:
            pass
        finally:
            mod._showwarnmsg = saved_show
            mod.filters[:] = saved_f
    if case.get("dfltdel"):
        del mod.defaultaction

    shown = []

    def show(m):
        if case["showraise"]:
            raise ValueError("show failed")
        shown.append(m)
    sk = case.get("show", "ok")
    saved_wm = mod.WarningMessage
    if sk == "deleted":
        if hasattr(mod, "_showwarnmsg"):
            del mod._showwarnmsg
    elif sk == "noncallable":
        mod._showwarnmsg = 5
    else:
        mod._showwarnmsg = show
        if sk == "nowm":
            del mod.WarningMessage
    reg = (None if case["reg"] is None else 5 if case["reg"] == "obj" else
           warn_Map(warn_mkdict(case["reg"]["map"], cur)) if isinstance(case["reg"], dict) else
           warn_mkdict(case["reg"], cur))
    once_d = warn_ONCE_C if mod is warn_c else warn_ONCE_PY
    mod.onceregistry = once_d
    once_d.clear()
    once_d.update(warn_mkdict(case["once"], cur))
    ok = case.get("oncek", "dict")
    if ok == "int":
        mod.onceregistry = 5
    elif ok == "deleted":
        del mod.onceregistry
    kw = {}
    if case["module"][0] == "none":
        kw["module"] = None
    elif case["module"][0] == "s":
        kw["module"] = case["module"][1]
    elif case["module"][0] == "obj":
        kw["module"] = 5
    if reg is not None:
        kw["registry"] = reg
    gk = case.get("globs", "none")
    if gk != "none":
        kw["module_globals"] = warn_globals(gk)
    mk = case.get("msg", "str")
    message = (warn_MSGS[mk](case["text"]) if mk in warn_MSGS else
               warn_CATS[case["cat"]](case["text"]) if mk == "inst" else
               warn_LieW(case["text"]) if mk == "instlie" else case["text"])
    if "getattr" in case:
        warn_install_getattr(mod, case["getattr"])
    imp = case.get("imp")
    real_import = warn_builtins.__import__

    def bad_import(name, *a, **k):
        if name == "warnings":
            raise RuntimeError("no import")
        return real_import(name, *a, **k)
    err, old_err = warn_io.StringIO(), sys.stderr
    sys.stderr = err
    try:
        ln = case["lineno"]
        if isinstance(ln, list):
            ln = warn_LINES[ln[1]]
        if imp == "raise":
            warn_builtins.__import__ = bad_import
        elif imp == "none":
            sys.modules['warnings'] = None
        try:
            mod.warn_explicit(message, warn_CATS[case["cat"]], case["filename"], ln, **kw)
        finally:
            warn_builtins.__import__ = real_import
            sys.modules['warnings'] = warn_c
            mod.__dict__.pop("__getattr__", None)
        out = ["ok", True]
    except warn_EXC as e:
        msg = str(e)
        if isinstance(e, SystemError):
            msg = "~returned a result with an exception set"
        elif isinstance(e, RuntimeError) and msg.startswith("Unrecognized action"):
            msg = "~Unrecognized action in warnings.filters"
        else:
            msg = warn_norm(msg)
        out = ["exc", type(e).__name__, msg]
    finally:
        sys.stderr = old_err
    printed = err.getvalue() != ""
    if out[0] == "ok":
        out = ["ok", bool(shown) or printed]
    once = warn_enc(once_d, cur)
    mod.onceregistry = once_d
    mod.WarningMessage = saved_wm
    mod._showwarnmsg = lambda m: None
    mod.filters = warn_FILTERS_C if mod is warn_c else warn_FILTERS_PY
    mod.filters[:] = []
    mod.defaultaction = "default"
    regd = reg if isinstance(reg, dict) else reg.d if isinstance(reg, warn_Map) else None
    return {"ok": [out, None if regd is None else warn_enc(regd, cur), once, printed]}


def warn_warmup():
    # A Python callback that raises while C warn_explicit has an OverflowError left set reports
    # its own exception, except on the first such call in a process, which reports SystemError
    # (measured on 3.15.2). The model describes the steady state, so run those paths once here.
    base = {"fn": "warn.c", "dflt": "always", "text": "a", "cat": 1, "filename": "a.py", "lineno": 1,
            "once": [], "showraise": False, "module": ["s", "m"], "reg": [["v", 2**64]]}
    for fs in ([["always", "RAISE", 1, None, 0, "tuple"]], [["always", None, 1, "RAISE", 0, "tuple"]],
               [["always", None, 4, None, 0, "tuple"]]):
        for module in (["s", "m"], ["omit"]):
            for _ in range(3):
                warn_run_we(dict(base, filters=fs, module=module))


warn_warmup()
warn_restore_std()

# --- filters-list API, the lock, -W options (Warn/Filters.lean, Warn/Option.lean) ---
import io as warn_io  # noqa: E402
import subprocess as warn_subprocess  # noqa: E402
import os as warn_os  # noqa: E402


class warn_MyOSError(OSError):
    pass


class warn_MyValueError(ValueError):
    pass


warn_MyOSError.__name__ = "MyOSError"
warn_MyValueError.__name__ = "MyValueError"


class warn_Other:
    """A filters-list element that is not a filter item; its `__eq__` gives `r`."""

    def __init__(self, i, r):
        self.i, self.r = i, r

    def __eq__(self, o):
        if self.r == "raise":
            raise KeyError("eq")
        if self.r == "verr":
            raise ValueError("eq")
        if self.r == "uerr":
            raise UnicodeError("eq")
        if self.r == "unsup":
            raise warn_io.UnsupportedOperation("eq")
        if self.r == "myverr":
            raise warn_MyValueError("eq")
        if self.r == "yerr":
            raise warn_mk_y()
        return self.r == "t"

    __hash__ = object.__hash__


# object ids: categories 0-5 as above, then more classes, a non-class object and a function
warn_OBJS = warn_CATS + [PendingDeprecationWarning, ImportWarning, ResourceWarning, RuntimeWarning,
                         int, ValueError, 5, print, SyntaxWarning, OSError, warn_py._OptionError,
                         warn_py.WarningMessage]


def warn_oid(o):
    for i, x in enumerate(warn_OBJS):
        if x is o:
            return i
    raise AssertionError(o)


def warn_rx_enc(p):
    return None if p is None else [p.pattern, bool(p.flags & warn_re.I)]


def warn_elem_enc(e):
    if isinstance(e, warn_Other):
        return ["o", e.i]
    a, m, c, d, ln = e
    return ["i", a, warn_rx_enc(m), warn_oid(c), warn_rx_enc(d), int(ln)]


def warn_cont_enc(mod):
    f = mod.__dict__.get("filters", warn_SENT)
    if f is warn_SENT:
        return ["deleted"]
    return ["list" if isinstance(f, list) else "tuple", [warn_elem_enc(e) for e in f]]


def warn_elem_mk(e):
    if e[0] == "o":
        return warn_Other(e[1], e[2])
    rx = (lambda r: None if r is None else warn_re.compile(r[0], warn_re.I if r[1] else 0))
    return (e[1], rx(e[2]), warn_OBJS[e[3]], rx(e[4]), e[5])


def warn_cver():
    """The C filters version: what already_warned stores in a stale registry."""
    probe = {}
    old = getattr(warn_c, "_showwarnmsg", lambda m: None)
    warn_c._showwarnmsg = lambda m: None
    try:
        warn_c.warn_explicit("probe", UserWarning, "p", 1, module="probe", registry=probe)
    except Exception:
        pass
    finally:
        warn_c._showwarnmsg = old
    return probe["version"]


def warn_ver(mod):
    return warn_cver() if mod is warn_c else mod._filters_version


warn_STRS = ["", "a", "x.*", "(", "a{4294967296}", "[", "__main__", "mod"]


def warn_gen_elem(rng):
    if rng.random() < .15:
        return ["o", rng.randrange(3), rng.choice(["t", "f", "f", "raise", "verr", "uerr", "unsup", "myverr", "yerr"])]
    rx = (lambda ci: None if rng.random() < .6 else [rng.choice(["a", "x.*", "__main__"]), ci])
    return ["i", rng.choice(warn_ACTS), rx(True), rng.choice([0, 1, 3, 12]), rx(False), rng.choice([0, 0, 1, 2])]


def warn_gen_act(rng):
    k = rng.random()
    if k < .8:
        return ["s", rng.choice(warn_ACTS)]
    if k < .9:
        return ["s", rng.choice(["bogus", "", "Error", "it's", "a\xa0b"])]
    if k < .95:
        return ["o", rng.choice(["5", "None"])]
    return ["u"]


def warn_gen_line(rng):
    k = rng.random()
    if k < .85:
        return ["i", rng.choice([0, 0, 1, 2, -1, 2**70])]
    if k < .93:
        return ["b", rng.random() < .5]
    return ["o"]


def warn_gen_str(rng):
    return ["o"] if rng.random() < .05 else ["s", rng.choice(warn_STRS)]


def warn_gen_filt(rng):
    twin = rng.choice(["filt_c", "filt_py"])
    k = rng.random()
    if k < .8:
        init = ["list", [warn_gen_elem(rng) for _ in range(rng.choice([0, 1, 2, 3]))]]
    elif k < .9:
        init = ["tuple", [warn_gen_elem(rng) for _ in range(rng.choice([0, 1, 2]))]]
    else:
        init = ["deleted"] + ([rng.choice(["key", "ae"])] if rng.random() < .4 else [])
    ops = []
    for _ in range(rng.choice([1, 2, 3, 4])):
        r = rng.random()
        cat = rng.choice([0, 1, 2, 3, 3, 10, 12, 13])
        if r < .45:
            ops.append(["fw", warn_gen_act(rng), warn_gen_str(rng), cat, warn_gen_str(rng), warn_gen_line(rng),
                        rng.random() < .3])
        elif r < .75:
            ops.append(["sf", warn_gen_act(rng), cat, warn_gen_line(rng), rng.random() < .3])
        elif r < .82:
            ops.append(["reset"])
        elif r < .87:
            ops.append(["mut"])
        else:
            ops.append([rng.choice(["acq", "rel", "mlh", "oacq", "orel"])])
    return {"fn": "warn." + twin, "init": init, "ops": ops}


def warn_res(thunk):
    try:
        thunk()
        return ["ok"]
    except warn_EXC as e:
        return ["exc", type(e).__name__, str(e)]


def warn_act_mk(a):
    return a[1] if a[0] == "s" else (5 if a[1] == "5" else None) if a[0] == "o" else []


def warn_line_mk(ln):
    return ln[1] if ln[0] in ("i", "b") else "5"


def warn_str_mk(s):
    return s[1] if s[0] == "s" else 5


def warn_set_cont(mod, init):
    if init[0] == "deleted":
        mod.__dict__.pop("filters", None)
        if len(init) > 1:
            warn_install_getattr(mod, {"filters": init[1]})
    else:
        xs = [warn_elem_mk(e) for e in init[1]]
        mod.filters = xs if init[0] == "list" else tuple(xs)


import queue as warn_queue  # noqa: E402
import threading as warn_threading  # noqa: E402

warn_HQ_IN, warn_HQ_OUT = warn_queue.Queue(), warn_queue.Queue()


def warn_helper():
    while True:
        f = warn_HQ_IN.get()
        warn_HQ_OUT.put(warn_res(f))


warn_threading.Thread(target=warn_helper, daemon=True).start()


def warn_in_helper(f):
    warn_HQ_IN.put(f)
    return warn_HQ_OUT.get()


def warn_run_filt(case):
    mod = warn_c if case["fn"] == "warn.filt_c" else warn_py
    sys.modules['warnings'] = warn_c
    warn_set_cont(mod, case["init"])
    v0 = warn_ver(mod)
    depth, odepth = 0, 0
    outs = []
    for op in case["ops"]:
        k = op[0]
        if mod is warn_c and ((odepth > 0 and k in ("fw", "sf", "reset", "mut", "acq")) or
                              (depth > 0 and k == "oacq")):
            outs.append(["blocked"])
            continue
        if k == "fw":
            f = (lambda op=op: mod.filterwarnings(warn_act_mk(op[1]), warn_str_mk(op[2]), warn_OBJS[op[3]],
                                                  warn_str_mk(op[4]), warn_line_mk(op[5]), op[6]))
        elif k == "sf":
            f = (lambda op=op: mod.simplefilter(warn_act_mk(op[1]), warn_OBJS[op[2]], warn_line_mk(op[3]), op[4]))
        elif k == "reset":
            f = mod.resetwarnings
        elif k == "mut":
            f = mod._filters_mutated
        elif k in ("acq", "oacq"):
            f = (mod._acquire_lock if mod is warn_c else (lambda: None))
        elif k in ("rel", "orel"):
            f = (mod._release_lock if mod is warn_c else (lambda: None))
        else:
            f = mod._filters_mutated_lock_held
        r = warn_in_helper(f) if k in ("oacq", "orel") else warn_res(f)
        if mod is warn_c and r == ["ok"]:
            depth += {"acq": 1, "rel": -1}.get(k, 0)
            odepth += {"oacq": 1, "orel": -1}.get(k, 0)
        outs.append(r)
    for _ in range(odepth):
        warn_in_helper(warn_c._release_lock)
    for _ in range(depth):
        warn_c._release_lock()
    mod.__dict__.pop("__getattr__", None)
    cont = warn_cont_enc(mod)
    dv = warn_ver(mod) - v0
    mod.filters = []
    return {"ok": [outs, cont, dv]}


# -W options: run on the warnings module itself (the startup configuration), filters starting empty
warn_OPT_ACTS = ["", "d", "default", "a", "al", "all", "alw", "i", "ignore", "m", "o", "e", "error", "x",
                 "Ignore", "always ", "defaults", " once"]
warn_OPT_MSGS = ["", "abc", "a.b", "/a.*b/", "/(/", "(", "/", "//", " x ", "/a{4294967296}/", "a{4294967296}",
                 "/[/", "a\xa0b", " a", "it's"]
warn_OPT_CATS = ["", "Warning", "UserWarning", "DeprecationWarning", "RuntimeWarning", "int", "ValueError",
                 "print", "None", "Foo", "0", "builtins.UserWarning", "builtins.print", "os.path", "os.sep",
                 "os.error", "os.path.sep", "warnings.filters", "warnings._OptionError", "nosuch.X", ".X",
                 "x..Y", "os.", "warnings.Foo", " UserWarning ", "builtins.", "..X"]
warn_OPT_MODS = ["", "mod", "a.b", "/x.*/", "/(/", "/a{4294967296}/", "__main__", "/"]
warn_OPT_LINES = ["", "0", "5", "-1", "-0", "5_0", "٥", "x", "1.5", " 7 ", "+3", "_5",
                  "99999999999999999999", "0x10", "１２", "5__0", "5_"]


def warn_gen_opt(rng):
    args = []
    for _ in range(rng.choice([1, 1, 2, 3])):
        fields = [rng.choice(warn_OPT_ACTS), rng.choice(warn_OPT_MSGS), rng.choice(warn_OPT_CATS),
                  rng.choice(warn_OPT_MODS), rng.choice(warn_OPT_LINES)]
        n = rng.choice([1, 2, 3, 3, 4, 5, 5, 5, 6])
        if n == 6:
            fields.append("x")
        args.append(":".join(fields[:n]))
    return {"fn": "warn.opt", "args": args}


def warn_run_opt(case):
    sys.modules['warnings'] = warn_c
    warn_c.filters = []
    err, old = warn_io.StringIO(), sys.stderr
    sys.stderr = err
    try:
        out = warn_res(lambda: warn_c._processoptions(case["args"]))
    finally:
        sys.stderr = old
    lines = err.getvalue().splitlines(keepends=True)
    cont = warn_cont_enc(warn_c)
    warn_c.filters = []
    return {"ok": [lines, out, cont]}


# the C initial filters list and the Python `_setup_defaults` result, each in a fresh interpreter
warn_DEFAULTS = None


def warn_run_defaults(case):
    global warn_DEFAULTS
    if warn_DEFAULTS is None:
        src = ("import sys, json\n"
               "sys.modules['_warnings'] = None if sys.argv[1] == 'py' else sys.modules.get('_warnings')\n"
               "import warnings, re\n"
               "ids = {DeprecationWarning: 3, PendingDeprecationWarning: 6, ImportWarning: 7, ResourceWarning: 8}\n"
               "def m(p):\n"
               "    return None if p is None else ['plain', p] if isinstance(p, str) else [p.pattern, bool(p.flags & re.I)]\n"
               "print(json.dumps([[a, m(x), ids[c], m(d), l] for a, x, c, d, l in warnings.filters]))\n")
        warn_DEFAULTS = {}
        for t in ("c", "py"):
            r = warn_subprocess.run([sys.executable, "-I", "-c", src, t], capture_output=True, text=True,
                                    env={k: v for k, v in warn_os.environ.items() if k != "PYTHONWARNINGS"})
            warn_DEFAULTS[t] = warn_json.loads(r.stdout)
    return {"ok": warn_DEFAULTS[case["twin"]]}


def warn_gen_defaults(rng):
    return {"fn": "warn.defaults", "twin": rng.choice(["c", "py"])}


def warn_gen(rng):
    k = rng.random()
    if k < .3:
        return warn_gen_we(rng)
    if k < .5:
        return warn_gen_filt(rng)
    if k < .65:
        return warn_gen_opt(rng)
    if k < .8:
        return warn_gen_call(rng)
    if k < .995:
        return warn_gen_ctx(rng)
    return warn_gen_defaults(rng)


def warn_run(case):
    try:
        return warn_run1(case)
    finally:
        warn_restore_std()


def warn_run1(case):
    fn = case["fn"]
    if fn in ("warn.c", "warn.py"):
        return warn_run_we(case)
    if fn in ("warn.filt_c", "warn.filt_py"):
        return warn_run_filt(case)
    if fn == "warn.opt":
        return warn_run_opt(case)
    if fn in ("warn.call_c", "warn.call_py"):
        return warn_run_call(case)
    if fn == "warn.ctx":
        return warn_run_ctx(case)
    return warn_run_defaults(case)


# --- warnings.warn: the stack walk and the context (Warn/WarnCall.lean) ---
import _thread as warn_thread  # noqa: E402
import functools as warn_functools  # noqa: E402
import collections as warn_collections  # noqa: E402

warn_FNAMES = ["a/m.py", "lib/b.py", "importlib/_bootstrap.py", "<frozen importlib._bootstrap_external>",
               "importlib/util.py", "x_bootstrap.py", "zz.py"]
warn_PFX = [["s", "a/"], ["s", "lib"], ["s", "importlib"], ["s", "<"], ["s", ""], ["s", "zz"],
            ["t", ["a/", "zz"]], ["o"]]
warn_SL = [-2**40, -1, 0, 1, 1, 1, 2, 2, 2, 3, 3, 4, 5, 2**31, 2**64]


def warn_gen_call(rng):
    ng = rng.choice([1, 2, 3])
    gl = [[rng.choice(["m", "m", "n", "none", "obj", "missing"]),
           rng.choice(["missing", "missing", "empty", "stale", "none", "obj"])] for _ in range(ng)]
    frames = [[rng.choice(warn_FNAMES), rng.randrange(ng), rng.randrange(3)]
              for _ in range(rng.choice([0, 1, 2, 3, 3, 4, 5]))]
    k = rng.random()
    skip = (["o"] if k < .03 else ["t", []] if k < .6 else
            ["t", [rng.choice(warn_PFX[:-1] + ([warn_PFX[-1]] if rng.random() < .2 else []))
                   for _ in range(rng.choice([1, 1, 2]))]])
    cat = rng.choice([["none"], ["none"], ["c", 1], ["c", 3], ["c", 5], ["c", 10], ["c", 18], ["obj", "str"],
                      ["obj", "od"]])
    msg = rng.choice([["s", "m"], ["s", "m"], ["w", 1, "wm"], ["w", 2, "w1"]] +
                     ([rng.choice([["lie", "m"], ["raise", "m"], ["raiseA", "m"], ["wlie", "wl"]])]
                      if rng.random() < .15 else []))
    return {"fn": "warn." + rng.choice(["call_c", "call_py"]), "globals": gl, "frames": frames,
            "sl": rng.choice(warn_SL), "skip": skip, "cat": cat, "msg": msg}


warn_CALL_CATS = {1: UserWarning, 3: DeprecationWarning, 5: warn_BadInit, 10: int,
                  18: warn_collections.OrderedDict}
warn_SENT = object()


def warn_mk_globals(spec, cur):
    name, reg = spec
    g = {}
    if name != "missing":
        g["__name__"] = {"m": "m", "n": "n", "none": None, "obj": 5}[name]
    if reg != "missing":
        g["__warningregistry__"] = {"empty": {}, "stale": {"version": cur - 1}, "none": None, "obj": 5}[reg]
    return g


def warn_enc_reg(g, cur):
    r = g.get("__warningregistry__", warn_SENT)
    if r is warn_SENT:
        return ["missing"]
    if r is None:
        return ["none"]
    if not isinstance(r, dict):
        return ["obj"]
    return ["dict", warn_enc(r, cur)]


# The bottom frame of the thread: a function of its own file and globals, so the generated frames
# and this one are the whole stack (the model's frame "<top>", line 3, globals k+2).
warn_TOPG = {"__name__": "top"}
exec(compile("def top(nxt, box, done, E=None):\n    try:\n        nxt()\n        box.append(['ok'])\n"
             "    except E as e:\n        box.append(['exc', type(e).__name__, str(e)])\n"
             "    finally:\n        done.release()\n", "<top>", "exec"), warn_TOPG)
warn_TOPG["top"].__defaults__ = (warn_EXC,)


def warn_run_call(case):
    isc = case["fn"] == "warn.call_c"
    mod = warn_c if isc else warn_py
    sys.modules['warnings'] = warn_c
    mod.filters[:] = []
    mod.defaultaction = "default"
    cur = warn_cver() if isc else mod._filters_version
    gls = [warn_mk_globals(s, cur) for s in case["globals"]]
    extra = [sys.__dict__, warn_py.__dict__, warn_TOPG]
    for g in extra:
        g.pop("__warningregistry__", None)
    shown = []
    mod._showwarnmsg = lambda m: shown.append(m)
    msg = case["msg"]
    message = (msg[1] if msg[0] == "s" else warn_LieU(msg[1]) if msg[0] == "lie" else
               warn_RaiseS(msg[1]) if msg[0] == "raise" else warn_RaiseA(msg[1]) if msg[0] == "raiseA" else
               warn_LieW(msg[1]) if msg[0] == "wlie" else (UserWarning if msg[1] == 1 else warn_W1)(msg[2]))
    c = case["cat"]
    category = (None if c[0] == "none" else warn_CALL_CATS[c[1]] if c[0] == "c" else
                "abc" if c[1] == "str" else warn_collections.OrderedDict())
    sk = case["skip"]
    skip = ['a'] if sk[0] == "o" else tuple(
        p[1] if p[0] == "s" else tuple(p[1]) if p[0] == "t" else 5 for p in sk[1])
    nxt = warn_functools.partial(mod.warn, message, category, case["sl"], skip_file_prefixes=skip)
    for fname, gi, blank in case["frames"]:
        ns = gls[gi]
        before = dict(ns)
        exec(compile("\n" * blank + "def _f(nxt):\n    return nxt()\n", fname, "exec"), ns)
        f = ns.pop("_f")
        for k in list(ns):
            if k not in before and k != "__builtins__":
                del ns[k]
        nxt = warn_functools.partial(f, nxt)
    done = warn_thread.allocate_lock()
    done.acquire()
    box = []

    warn_TOPG.pop("__warningregistry__", None)
    warn_thread.start_new_thread(warn_TOPG["top"], (nxt, box, done))
    done.acquire()
    out = box[0]
    if out[0] == "ok":
        out = ["ok", bool(shown)]
    else:
        out = [out[0], out[1], warn_norm(out[2])]
    sh = None
    if shown:
        m = shown[0]
        fn = "PYW" if m.filename == warn_py.__file__ else m.filename
        mo = m.module
        sh = [fn, m.lineno, mo if isinstance(mo, str) or mo is None else ["obj"]]
    regs = [warn_enc_reg(g, cur) for g in gls + extra]
    for g in extra:
        g.pop("__warningregistry__", None)
    for g in gls:
        g.pop("__builtins__", None)
    mod._showwarnmsg = warn_c._showwarnmsg if False else (lambda m: None)
    return {"ok": [out, sh, regs]}


# --- catch_warnings, the contexts, _showwarnmsg (Warn/Context.lean) ---
import contextvars as warn_contextvars  # noqa: E402
import io as warn_io  # noqa: E402



class warn_ErrFile:
    def __init__(self, exc):
        self.exc = exc

    def write(self, s):
        raise self.exc("write failed")


import types as warn_types  # noqa: E402

warn_OTHERMOD = warn_types.ModuleType("othermod")


def warn_gen_ctx(rng):
    ops = []
    ncw = 0
    for _ in range(rng.choice([2, 3, 4, 5, 6, 8])):
        r = rng.random()
        if r < .2 or ncw == 0:
            a = None if rng.random() < .6 else warn_gen_act(rng)
            ops.append(["new", rng.random() < .5, a, rng.choice([0, 1, 3, 12]), warn_gen_line(rng),
                        rng.random() < .3])
            ncw += 1
        elif r < .45:
            ops.append(["enter", rng.randrange(ncw)])
        elif r < .65:
            ops.append(["exit", rng.randrange(ncw)])
        elif r < .8:
            ops.append(["show", rng.randrange(100)])
        elif r < .88:
            ops.append(["sf", warn_gen_act(rng), rng.choice([0, 1, 3]), ["i", 0], rng.random() < .3])
        elif r < .95:
            ops.append(["setshow", rng.choice(["orig", "user", "noncallable", "deleted", "userraise"])])
        else:
            v = rng.choice(["ok", "ok", "nosys", "swap"])
            if rng.random() < .5:
                ops.append(["repr", rng.randrange(ncw), v])
            else:
                ops.append(["mrepr", rng.random() < .5, v])
    return {"fn": "warn.ctx", "use": rng.random() < .5,
            "filters": [warn_gen_elem(rng) for _ in range(rng.choice([0, 1, 2]))],
            "show": rng.choice(["orig", "orig", "orig", "user", "noncallable", "deleted", "userraise"]),
            "impl": rng.choice(["orig", "orig", "orig", "user", "noncallable", "userraise"]),
            "stderr": rng.choice(["ok", "ok", "ok", "none", "oserr", "keyerr", "brokenpipe", "unsupported",
                                  "myoserr", "yerr"]),
            "fmt": rng.choice(["raise", "deleted", "ret", "ret", "none", "show", "impl", "log"])
            if rng.random() < .3 else "orig", "ops": ops,
            **({"fdel": True} if rng.random() < .1 else {}),
            **({"getattr": {a: rng.choice(["key", "ae"]) for a in ["showwarning", "formatwarning", "filters"]
                            if rng.random() < .5}} if rng.random() < .2 else {})}


def warn_run_ctx(case):
    return warn_contextvars.copy_context().run(warn_run_ctx1, case)


def warn_run_ctx1(case):
    sys.modules['warnings'] = warn_c
    mod = warn_c
    old_use, old_stderr = warn_PYG["_use_context"], sys.stderr
    orig_show, orig_impl = warn_PYG["showwarning"], warn_PYG["_showwarnmsg_impl"]
    mod.showwarning, mod._showwarnmsg_impl = orig_show, orig_impl
    warn_PYG["_use_context"] = case["use"]
    shown = []
    def raising_hook(*a):
        raise ValueError("hook failed")
    hooks = {"user": lambda *a: shown.append(["hook", 1]), "noncallable": 5, "userraise": raising_hook}
    init = [warn_elem_mk(e) for e in case["filters"]]
    mod.filters = init
    if case.get("fdel"):
        del mod.filters
    if case["show"] == "deleted":
        del mod.showwarning
    elif case["show"] != "orig":
        mod.showwarning = hooks[case["show"]]
    if case["impl"] == "user":
        mod._showwarnmsg_impl = lambda m: shown.append(["hook", 2])
    elif case["impl"] == "userraise":
        mod._showwarnmsg_impl = raising_hook
    elif case["impl"] == "noncallable":
        mod._showwarnmsg_impl = 5
    err = warn_io.StringIO()
    sys.stderr = {"ok": err, "none": None, "oserr": warn_ErrFile(OSError),
                  "keyerr": warn_ErrFile(KeyError), "brokenpipe": warn_ErrFile(BrokenPipeError),
                  "unsupported": warn_ErrFile(warn_io.UnsupportedOperation),
                  "myoserr": warn_ErrFile(warn_MyOSError),
                  "yerr": warn_ErrFile(warn_mk_y)}[case["stderr"]]
    if case.get("fmt") == "raise":
        def raising_fmt(*a):
            raise ValueError("fmt failed")
        mod.formatwarning = raising_fmt
    elif case.get("fmt") == "deleted":
        del mod.formatwarning
    elif case.get("fmt") in ("ret", "none", "show", "impl", "log"):
        mod.formatwarning = {"ret": lambda *a: "FMT\n", "none": lambda *a: None, "show": mod._showwarning_orig,
                             "impl": orig_impl, "log": [].append}[case["fmt"]]
    if "getattr" in case:
        warn_install_getattr(mod, case["getattr"])
    v0 = warn_cver()
    cws, logs, outs = [], [], []

    def logid(lst):
        for i, x in enumerate(logs):
            if x is lst:
                return i
        logs.append(lst)
        return len(logs) - 1
    try:
        for op in case["ops"]:
            k = op[0]
            try:
                if k == "new":
                    kw = {"record": op[1]}
                    if op[2] is not None:
                        kw.update(action=warn_act_mk(op[2]), category=warn_OBJS[op[3]],
                                  lineno=warn_line_mk(op[4]), append=op[5])
                    cws.append(mod.catch_warnings(**kw))
                    outs.append(["ok"])
                elif k == "enter":
                    log = cws[op[1]].__enter__()
                    outs.append(["ok", None if log is None else logid(log)])
                elif k == "exit":
                    cws[op[1]].__exit__(None, None, None)
                    outs.append(["ok"])
                elif k == "show":
                    sizes = [len(x) for x in logs]
                    n0, e0 = len(shown), err.tell()
                    m = mod.WarningMessage(str(op[1]), UserWarning, "f.py", 1)
                    warn_PYG["_showwarnmsg"](m)
                    grew = [i for i, x in enumerate(logs) if len(x) > sizes[i]]
                    if grew:
                        res = ["log", grew[0]]
                    elif len(shown) > n0:
                        res = shown[-1]
                    elif err.tell() > e0:
                        text = err.getvalue()[e0:]
                        res = ["written", "dflt" if text == warn_PYG["_formatwarnmsg_impl"](m) else ["s", text]]
                    else:
                        cand = None
                        impl = getattr(mod, "_showwarnmsg_impl", None)
                        if isinstance(getattr(impl, "__self__", None), list):
                            cand = impl.__self__
                        ctx = mod._get_context()
                        if cand is None and ctx.log is not None:
                            cand = ctx.log
                        res = ["log", logid(cand)] if cand is not None and m in cand else ["lost"]
                    outs.append(["ok", res])
                elif k == "sf":
                    mod.simplefilter(warn_act_mk(op[1]), warn_OBJS[op[2]], warn_line_mk(op[3]), op[4])
                    outs.append(["ok"])
                elif k == "setshow":
                    if op[1] == "deleted":
                        mod.__dict__.pop("showwarning", None)
                    else:
                        mod.showwarning = {"orig": mod._showwarning_orig, **hooks}[op[1]]
                    outs.append(["ok"])
                else:
                    cw = (cws[op[1]] if k == "repr" else
                          mod.catch_warnings(record=op[1], module=warn_OTHERMOD))
                    saved = sys.modules["warnings"]
                    if op[2] == "nosys":
                        del sys.modules["warnings"]
                    elif op[2] == "swap":
                        sys.modules["warnings"] = warn_OTHERMOD
                    try:
                        r = repr(cw)
                    finally:
                        sys.modules["warnings"] = saved
                    outs.append(["ok", r.replace(repr(warn_c), "<W>").replace(repr(warn_OTHERMOD), "<X>")])
            except warn_EXC as e:
                outs.append(["exc", type(e).__name__, str(e)])
        sw = mod.__dict__.get("showwarning", warn_SENT)
        swk = ("deleted" if sw is warn_SENT else "orig" if sw is mod._showwarning_orig else
               "user" if sw is hooks["user"] else "noncallable" if sw is hooks["noncallable"] else
               "userraise" if sw is raising_hook else "other")
        imp = mod._showwarnmsg_impl
        impk = ("orig" if imp is orig_impl else "noncallable" if isinstance(imp, int) else
                "userraise" if imp is raising_hook else
                ["log", logid(imp.__self__)] if isinstance(getattr(imp, "__self__", None), list) else "user")
        try:
            fin = [warn_elem_enc(e) for e in mod._get_filters()]
        except warn_EXC as e:
            fin = ["exc", type(e).__name__, str(e)]
        final = [fin, mod.__dict__.get("filters") is init, swk, impk,
                 warn_cver() - v0, [[str(getattr(x, "message", x)) for x in lg] for lg in logs]]
    finally:
        sys.stderr = old_stderr
        warn_PYG["_use_context"] = old_use
        mod.__dict__.pop("__getattr__", None)
        mod.showwarning, mod._showwarnmsg_impl = orig_show, orig_impl
        mod.formatwarning = warn_PYG["formatwarning"]
        mod.filters = []
    return {"ok": [outs, final]}


# @@WARN_EXT@@
# ====== END AREA warn ======


AREAS = {name: (globals()[name + "_gen"], globals()[name + "_run"])
         for name in ['coll', 'collabc', 'functools', 'operator', 'enumdc', 'misc', 'calstat', 'rand', 'warn']}
selected = os.environ.get("CORELIBS_AREA")
ACTIVE = [a for a in (selected.split(",") if selected else AREAS) if AREAS[a][0] is not None]


def gen_case(rng):
    case = AREAS[rng.choice(ACTIVE)][0](rng)
    if case is not None:
        case["mod"] = "corelibs"
    return case


def run_python(case):
    return AREAS[case["fn"].split(".")[0]][1](case)


if __name__ == "__main__":
    main(gen_case, run_python)
