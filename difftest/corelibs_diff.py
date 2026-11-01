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
import itertools as coll_itertools  # noqa: E402

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


coll_GENS = [coll_gen_ctr]
coll_RUNS = {"coll.ctr": coll_run_ctr}


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
