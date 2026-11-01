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


def coll_xs(rng):
    return [rng.choice(coll_KEYS) for _ in range(rng.randint(0, 10))]


def coll_src(rng, case):
    case["src"] = rng.choice(["none", "mapping", "iter"])
    if case["src"] == "mapping":
        case["items"] = coll_items(rng)
    elif case["src"] == "iter":
        case["xs"] = coll_xs(rng)
    case["kw"] = coll_items(rng) if rng.random() < 0.3 else []


def coll_gen_ctr(rng):
    op = rng.choice(["new", "update", "subtract", "count_py", "count_c", "count_slow", "total",
                     "most_common", "most_common", "elements", "copy", "reduce", "delitem",
                     "getitem", "repr", "fromkeys", "keep_positive", "pos", "neg", "add", "sub",
                     "or", "and", "eq", "ne", "le", "lt", "ge", "gt", "iadd", "isub", "ior",
                     "iand"])
    case = {"fn": "coll.ctr", "op": op, "a": coll_items(rng)}
    if op in ("new", "update", "subtract"):
        coll_src(rng, case)
    if op in ("count_py", "count_c", "count_slow", "fromkeys"):
        case["xs"] = coll_xs(rng)
    if op in ("delitem", "getitem"):
        case["e"] = rng.choice(coll_KEYS)
    if op == "most_common":
        case["n"] = rng.choice([None, None, 0, 1, 2, 3, 4, 5, 6, 7, 100, -1, -2, 2**63, -2**63])
    if op == "elements":
        case["a"] = coll_items(rng, small=True)
        if rng.random() < 0.1:
            case["a"].append(["z", rng.choice([2**63, -2**63 - 1, 2**64])])
    if op in ("add", "sub", "or", "and", "eq", "ne", "le", "lt", "ge", "gt"):
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
    if op in ("iadd", "isub", "ior", "iand"):
        case["bty"] = rng.choice(["Counter", "Counter", "Counter", "dict", "int"])
        case["b"] = coll_items(rng)
    return case


def coll_ctr(items):
    c = coll_collections.Counter()
    for k, v in items:
        dict.__setitem__(c, k, v)
    return c


def coll_enc(d):
    return [[k, v] for k, v in d.items()]


def coll_src_arg(case):
    if case["src"] == "none":
        return None
    if case["src"] == "mapping":
        return dict(map(tuple, case["items"]))
    return iter(case["xs"])


def coll_ipy_count(m, xs):
    mapping_get = m.get
    for elem in xs:
        m[elem] = mapping_get(elem, 0) + 1


class coll_SlowCounter(coll_collections.Counter):
    """Overrides `get`, which sends the C `_count_elements` down its slow path."""
    def get(self, *args):
        return super().get(*args)


def coll_run_ctr(case):
    op = case["op"]
    a = coll_ctr(case["a"])
    Counter = coll_collections.Counter

    def body():
        if op == "new":
            return coll_enc(Counter(coll_src_arg(case), **dict(map(tuple, case["kw"]))))
        if op == "update":
            a.update(coll_src_arg(case), **dict(map(tuple, case["kw"])))
            return coll_enc(a)
        if op == "subtract":
            a.subtract(coll_src_arg(case), **dict(map(tuple, case["kw"])))
            return coll_enc(a)
        if op == "count_py":
            coll_ipy_count(a, case["xs"])
            return coll_enc(a)
        if op == "count_c":
            coll_collections._count_elements(a, case["xs"])
            return coll_enc(a)
        if op == "count_slow":
            s = coll_SlowCounter()
            for k, v in case["a"]:
                dict.__setitem__(s, k, v)
            coll_collections._count_elements(s, case["xs"])
            return coll_enc(s)
        if op == "total":
            return a.total()
        if op == "most_common":
            r = a.most_common(case["n"]) if case["n"] is not None else a.most_common()
            return [list(p) for p in r]
        if op == "elements":
            return list(a.elements())
        if op == "copy":
            return coll_enc(a.copy())
        if op == "reduce":
            cls, args = a.__reduce__()
            assert cls is Counter and len(args) == 1 and type(args[0]) is dict
            return coll_enc(args[0])
        if op == "delitem":
            del a[case["e"]]
            return coll_enc(a)
        if op == "getitem":
            return a[case["e"]]
        if op == "repr":
            return repr(a)
        if op == "fromkeys":
            return coll_enc(Counter.fromkeys(case["xs"]))
        if op == "keep_positive":
            return coll_enc(a._keep_positive())
        if op == "pos":
            return coll_enc(+a)
        if op == "neg":
            return coll_enc(-a)
        if op in ("add", "sub", "or", "and"):
            b = coll_ctr(case["b"]) if "b" in case else 5
            r = {"add": lambda: a + b, "sub": lambda: a - b, "or": lambda: a | b,
                 "and": lambda: a & b}[op]()
            return coll_enc(r)
        if op in ("eq", "ne", "le", "lt", "ge", "gt"):
            b = coll_ctr(case["b"]) if "b" in case else 5
            return {"eq": lambda: a == b, "ne": lambda: a != b, "le": lambda: a <= b,
                    "lt": lambda: a < b, "ge": lambda: a >= b, "gt": lambda: a > b}[op]()
        if op in ("iadd", "isub", "ior", "iand"):
            ty = case["bty"]
            b = coll_ctr(case["b"]) if ty == "Counter" else (
                dict(map(tuple, case["b"])) if ty == "dict" else 5)
            nonlocal_a = a
            if op == "iadd":
                nonlocal_a += b
            elif op == "isub":
                nonlocal_a -= b
            elif op == "ior":
                nonlocal_a |= b
            else:
                nonlocal_a &= b
            return coll_enc(nonlocal_a)
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


coll_UD_CLASSES = [coll_collections.UserDict, coll_UDPlain, coll_UDMiss]


def coll_d(items):
    return dict(map(tuple, items))


def coll_gen_cm(rng):
    op = rng.choice(["new", "getitem", "get", "len", "iter", "contains", "bool", "repr", "fromkeys",
                     "copy", "new_child", "parents", "setitem", "delitem", "popitem", "pop",
                     "clear", "ior", "or", "ror"])
    n = rng.choice([0, 1, 1, 2, 2, 3, 4])
    case = {"fn": "coll.cm", "op": op, "k": rng.choice(coll_KEYS),
            "maps": [coll_items(rng, small=True) if rng.random() < 0.8 else [] for _ in range(n)]}
    if rng.random() < 0.4:
        case["d"] = rng.randint(-3, 3)
    if op in ("get", "getitem") and rng.random() < 0.5:
        case["sub"] = 1
    if op == "fromkeys":
        case["xs"] = coll_xs(rng)
    if op in ("or", "ror", "new_child"):
        if rng.random() < 0.8:
            case["o"] = coll_items(rng, small=True)
    if op == "ior":
        case["o"] = coll_items(rng, small=True)
    if op == "new_child":
        case["kw"] = coll_items(rng, small=True) if rng.random() < 0.5 else []
    return case


def coll_enc_cm(c):
    return [coll_enc(m) for m in c.maps]


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
        if op == "fromkeys":
            return coll_enc_cm(ChainMap.fromkeys(case["xs"], 0 if d is None else d))
        if op == "copy":
            return coll_enc_cm(c.copy())
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
            r = c
            r |= coll_d(case["o"])
            return coll_enc_cm(r)
        if op == "or":
            return coll_enc_cm(c | (coll_d(case["o"]) if "o" in case else 5))
        if op == "ror":
            return coll_enc_cm((coll_d(case["o"]) if "o" in case else 5) | c)
        raise AssertionError(op)
    return py_result(body)


def coll_gen_ud(rng):
    op = rng.choice(["new", "len", "getitem", "setitem", "delitem", "iter", "contains", "get",
                     "repr", "or", "ror", "ior", "copy", "copy_dunder", "fromkeys", "pop",
                     "popitem", "setdefault", "clear", "items_contains", "dict_getitem",
                     "dict_pop", "dict_popitem", "dict_setdefault", "dict_items_contains"])
    case = {"fn": "coll.ud", "op": op, "a": coll_items(rng, small=True),
            "sub": rng.choice([0, 1, 2]), "k": rng.choice(coll_KEYS)}
    if rng.random() < 0.5:
        case["d"] = rng.randint(-3, 3)
    if op in ("items_contains", "dict_items_contains") and rng.random() < 0.5:
        case["d"] = -1
    if op == "new":
        case["kw"] = coll_items(rng, small=True) if rng.random() < 0.5 else []
        if rng.random() < 0.7:
            case["o"] = coll_items(rng, small=True)
    if op in ("or", "ror"):
        case["oty"] = rng.choice(["user", "dict", "int"])
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
            r = coll_abc.MutableMapping.popitem(u)
            return [list(r), coll_enc_ud(u)]
        if op == "setdefault":
            r = u.setdefault(k, 0 if d is None else d)
            return [r, coll_enc_ud(u)]
        if op == "clear":
            u.clear()
            return coll_enc_ud(u)
        if op == "items_contains":
            return (k, 0 if d is None else d) in u.items()
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
        raise AssertionError(op)
    return py_result(body)


coll_GENS = [coll_gen_ctr, coll_gen_cm, coll_gen_ud]
coll_RUNS = {"coll.ctr": coll_run_ctr, "coll.cm": coll_run_cm, "coll.ud": coll_run_ud}


def coll_gen(rng):
    return rng.choice(coll_GENS)(rng)


def coll_run(case):
    return coll_RUNS[case["fn"]](case)
# ====== END AREA coll ======

# ====== BEGIN AREA collabc (Lib/_collections_abc.py, Lib/collections/abc.py) ======
# Everything for this area stays between these two markers; prefix top-level names with collabc_.
collabc_gen = None  # replace with def collabc_gen(rng) -> case dict with "fn": "collabc.<name>"
collabc_run = None  # replace with def collabc_run(case) -> common.py_result-style dict
# ====== END AREA collabc ======

# ====== BEGIN AREA functools (Lib/functools.py, Modules/_functoolsmodule.c) ======
# Everything for this area stays between these two markers; prefix top-level names with functools_.
functools_gen = None  # replace with def functools_gen(rng) -> case dict with "fn": "functools.<name>"
functools_run = None  # replace with def functools_run(case) -> common.py_result-style dict
# ====== END AREA functools ======

# ====== BEGIN AREA operator (Lib/operator.py, Modules/_operator.c, Lib/copy.py, Lib/abc.py) ======
# Everything for this area stays between these two markers; prefix top-level names with operator_.
operator_gen = None  # replace with def operator_gen(rng) -> case dict with "fn": "operator.<name>"
operator_run = None  # replace with def operator_run(case) -> common.py_result-style dict
# ====== END AREA operator ======

# ====== BEGIN AREA enumdc (Lib/enum.py, Lib/dataclasses.py) ======
# Everything for this area stays between these two markers; prefix top-level names with enumdc_.
enumdc_gen = None  # replace with def enumdc_gen(rng) -> case dict with "fn": "enumdc.<name>"
enumdc_run = None  # replace with def enumdc_run(case) -> common.py_result-style dict
# ====== END AREA enumdc ======

# ====== BEGIN AREA misc (Lib/contextlib.py, Lib/numbers.py, Lib/keyword.py, Lib/types.py, Lib/weakref.py, Lib/graphlib.py, Lib/sched.py, Lib/queue.py) ======
# Everything for this area stays between these two markers; prefix top-level names with misc_.
misc_gen = None  # replace with def misc_gen(rng) -> case dict with "fn": "misc.<name>"
misc_run = None  # replace with def misc_run(case) -> common.py_result-style dict
# ====== END AREA misc ======

# ====== BEGIN AREA calstat (Lib/calendar.py, Lib/statistics.py) ======
# Everything for this area stays between these two markers; prefix top-level names with calstat_.
calstat_gen = None  # replace with def calstat_gen(rng) -> case dict with "fn": "calstat.<name>"
calstat_run = None  # replace with def calstat_run(case) -> common.py_result-style dict
# ====== END AREA calstat ======

# ====== BEGIN AREA rand (Lib/random.py, Modules/_randommodule.c) ======
# Everything for this area stays between these two markers; prefix top-level names with rand_.
rand_gen = None  # replace with def rand_gen(rng) -> case dict with "fn": "rand.<name>"
rand_run = None  # replace with def rand_run(case) -> common.py_result-style dict
# ====== END AREA rand ======


AREAS = {name: (globals()[name + "_gen"], globals()[name + "_run"])
         for name in ['coll', 'collabc', 'functools', 'operator', 'enumdc', 'misc', 'calstat', 'rand']}
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
