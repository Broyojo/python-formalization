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
                     "popitem", "setdefault", "clear", "items_contains", "reversed",
                     "dict_reversed", "dict_getitem",
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


def coll_gen_ul(rng):
    op = rng.choice(["new", "repr", "lt", "le", "eq", "gt", "ge", "contains", "len", "getitem",
                     "getslice", "setitem", "setslice", "delitem", "delslice", "add", "radd",
                     "iadd", "mul", "imul", "copy", "copy_dunder", "append", "insert", "pop",
                     "remove", "clear", "count", "index", "reverse", "sort", "extend"])
    case = {"fn": "coll.ul", "op": op, "sub": rng.choice([0, 1]), "a": coll_ints(rng)}
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
        case["s"] = list(map(ord, rng.choice(["x", "{}", "{}{}", "{0}", "{1}", ""])))
        case["args"] = coll_ints(rng)[:2]
    if op == "format_map":
        case["s"] = list(map(ord, rng.choice(["x", "{a}", "{b}", ""])))
        case["m"] = [["a", rng.randint(0, 9)]]
    if op == "mod":
        case["s"] = list(map(ord, rng.choice(["x", "%d", "%s%d", "%%", "", "%d%%"])))
        case["args"] = coll_ints(rng)[:2]
    if op == "rmod":
        case["t"] = list(map(ord, rng.choice(["5", "%s", "x%sy", "%s%s"])))
    if op == "translate":
        case["t"] = [[ord(rng.choice(coll_ALPHA)), rng.choice([None, 120])]
                     for _ in range(rng.randint(0, 3))]
        case["t"] = list({p[0]: p for p in case["t"]}.values())
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
            return coll_enc_us(u.format(*case["args"]))
        if op == "format_map":
            return coll_enc_us(u.format_map(coll_d(case["m"])))
        if op == "mod":
            return coll_enc_us(u % tuple(case["args"]))
        if op == "translate":
            return coll_enc_us(u.translate(coll_d(case["t"])))
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
    def __init__(self, xs, fail):
        self.xs, self.fail = xs, fail

    def __getitem__(self, i):
        if i == self.fail:
            raise ValueError("fail")
        return self.xs[i]

    def __len__(self):
        return len(self.xs)


class collabc_MSeq(collabc_A.MutableSequence):
    def __init__(self, xs, fail):
        self.xs, self.fail = list(xs), fail

    def __getitem__(self, i):
        if i == self.fail:
            raise ValueError("fail")
        return self.xs[i]

    def __setitem__(self, i, v):
        self.xs[i] = v

    def __delitem__(self, i):
        del self.xs[i]

    def __len__(self):
        return len(self.xs)

    def insert(self, i, v):
        self.xs.insert(i, v)


class collabc_Set(collabc_A.MutableSet):
    bad = None

    def __init__(self, it=()):
        self.xs = []
        for x in it:
            if x not in self.xs:
                self.xs.append(x)

    def __contains__(self, x):
        if x == collabc_Set.bad:
            raise ValueError("bad")
        return x in self.xs

    def __iter__(self):
        return iter(list(self.xs))

    def __len__(self):
        return len(self.xs)

    def add(self, x):
        if x not in self.xs:
            self.xs.append(x)

    def discard(self, x):
        if x in self.xs:
            self.xs.remove(x)

    __hash__ = None


class collabc_Map(collabc_A.MutableMapping):
    def __init__(self, items, fail):
        self.d, self.fail = dict(items), fail

    def __getitem__(self, k):
        if k == self.fail:
            raise ValueError("fail")
        return self.d[k]

    def __setitem__(self, k, v):
        self.d[k] = v

    def __delitem__(self, k):
        del self.d[k]

    def __iter__(self):
        return iter(list(self.d))

    def __len__(self):
        return len(self.d)


class collabc_HSet(collabc_A.Set):
    """A Set that reports the given hashes, for Set._hash."""

    def __init__(self, hashes):
        self.hs = [collabc_H(h) for h in hashes]

    def __contains__(self, x):
        return x in self.hs

    def __iter__(self):
        return iter(self.hs)

    def __len__(self):
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
    "Hashable.__hash__": lambda: collabc_A.Hashable.__hash__(None),
    "Sized.__len__": lambda: collabc_A.Sized.__len__(None),
    "Container.__contains__": lambda: collabc_A.Container.__contains__(None, 1),
    "Callable.__call__": lambda: collabc_A.Callable.__call__(None),
    "Awaitable.__await__": lambda: len(list(collabc_A.Awaitable.__await__(None))),
    "Iterable.__iter__": lambda: len(list(collabc_A.Iterable.__iter__(None))),
    "Reversible.__reversed__": lambda: len(list(collabc_A.Reversible.__reversed__(None))),
    "Iterator.__next__": lambda: collabc_A.Iterator.__next__(None),
    "Generator.send": lambda: collabc_A.Generator.send(None, 1),
    "Coroutine.send": lambda: collabc_A.Coroutine.send(None, 1),
    "AsyncIterator.__anext__": lambda: collabc_drive(collabc_A.AsyncIterator.__anext__(None)),
    "AsyncGenerator.asend": lambda: collabc_drive(collabc_A.AsyncGenerator.asend(None, 1)),
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
collabc_EXCS = {"ValueError": ValueError, "KeyError": KeyError, "GeneratorExit": GeneratorExit}


def collabc_rand_class(rng):
    C = object
    for depth in range(rng.randrange(0, 4)):
        d = {}
        for m in rng.sample(collabc_METHODS, rng.randrange(0, 6)):
            d[m] = None if rng.random() < 0.25 else (lambda self: 0)
        C = type(f"C{depth}", (C,), d)
    return C


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
        return {"fn": "collabc.hook", "mro": collabc_mro(collabc_rand_class(rng)),
                "x": rng.choice(collabc_HOOKS), "cls": rng.choice(collabc_HOOKS)}
    if r == 2:
        return {"fn": "collabc.stub", "name": rng.choice(list(collabc_STUBS))}
    if r == 3:
        def arg():
            return rng.choice([{"k": "cls", "n": "ValueError"}, {"k": "cls", "n": "KeyError"},
                               {"k": "inst", "n": "ValueError"}, {"k": "other"}])
        return {"fn": "collabc.throw", "typ": arg(), "val": None if rng.random() < .5 else arg(),
                "tb": rng.random() < .5}
    if r in (4, 5):
        script = [rng.choice([["y", 1], ["r", 7], ["exit", 0], ["e", 3]])
                  for _ in range(rng.randrange(0, 3))]
        if r == 4:
            return {"fn": "collabc.gen_close", "script": script,
                    "kind": rng.choice(["gen", "coro", "agen"])}
        return {"fn": rng.choice(["collabc.gen_next", "collabc.builtin_close"]), "script": script[:1]}
    if r == 6:
        if rng.random() < .3:
            return {"fn": "collabc.callable_getitem", "shape": rng.choice(["tv", "param"]),
                    "a": rng.choice(["int", "str"]), "b": rng.choice(["bool", "float"])}
        k = rng.choice(["seq", "ell", "param", "other", "bad"])
        return {"fn": "collabc.callable_new", "a": {"k": k, "repr": "~T", "items":
                rng.sample(["int", "str", "bool"], rng.randrange(0, 3))}, "r": "float"}
    if r == 7:
        return {"fn": "collabc.seq_iter", "xs": xs, "fail": fail}
    if r == 8:
        return {"fn": "collabc.seq_reversed", "xs": xs, "fail": fail}
    if r in (9, 10):
        return {"fn": "collabc." + ("seq_contains" if r == 9 else "seq_count"), "xs": xs,
                "fail": fail, "bad": bad, "v": v}
    if r == 11:
        n = len(xs)
        start = rng.choice([0, 1, -1, n, -n, n + 1, -n - 1, n // 2, -2**70, 2**70])
        stop = rng.choice([None, 0, 1, -1, n, -n, n + 1, -n - 1, n // 2, -2**70, 2**70])
        return {"fn": rng.choice(["collabc.seq_index", "collabc.list_index"]), "xs": xs,
                "fail": fail, "bad": bad, "v": v, "start": start, "stop": stop}
    if r == 12:
        return {"fn": "collabc.mseq_append", "xs": xs, "v": v}
    if r == 13:
        return {"fn": "collabc.mseq_pop", "xs": xs, "i": idx, "fail": fail}
    if r == 14:
        return {"fn": rng.choice(["collabc.mseq_clear", "collabc.mseq_reverse"]), "xs": xs,
                "fail": fail}
    if r == 15:
        return {"fn": "collabc.mseq_extend", "xs": xs, "fail": fail,
                "vs": None if rng.random() < .3 else collabc_list(rng, 4)}
    if r == 16:
        k = rng.randrange(0, 5)
        if k == 0:
            return {"fn": "collabc.list_remove", "xs": xs, "v": v, "bad": bad}
        if k == 1:
            return {"fn": "collabc.bytestring_new",
                    "name": rng.choice(["ByteString", "Other", "bytestring"])}
        if k == 2:
            return {"fn": "collabc.bytestring_check", "answer": rng.random() < .5}
        if k == 3:
            return {"fn": "collabc.view_repr", "cls": rng.choice(["KeysView", "ItemsView", "ValuesView"]),
                    "r": "{1: 2}"}
        return {"fn": "collabc.mseq_remove", "xs": xs, "v": v, "fail": fail, "bad": bad}
    a, b = collabc_uniq(xs), collabc_list(rng)
    kind = rng.choice(["set", "iter", "other"])
    if kind == "set":
        b = collabc_uniq(b)
    if r == 17:
        return {"fn": "collabc.set_cmp", "op": rng.choice(["le", "lt", "ge", "gt", "eq"]), "xs": a,
                "other": b, "okind": kind, "bad": bad}
    if r == 18:
        return {"fn": "collabc.set_op", "op": rng.choice(["and", "or", "sub", "rsub", "xor"]),
                "xs": a, "other": b, "okind": kind, "bad": bad}
    if r == 19:
        return {"fn": "collabc.set_isdisjoint", "xs": a, "other": b, "okind": kind, "bad": bad}
    if r == 20:
        hs = rng.sample([0, 1, -2, 2**61 - 1, -2**63, 2**63 - 1, 5, 2**32, 123456789, -77,
                         rng.randrange(-2**63, 2**63)], rng.randrange(0, 8))
        return {"fn": rng.choice(["collabc.set_hash", "collabc.frozenset_hash"]), "hashes": hs,
                "nulls": rng.randrange(0, 9), "dummies": rng.randrange(0, 3)}
    if r == 21:
        return {"fn": "collabc.mset_op", "op": rng.choice(["ior", "iand", "ixor", "isub", "clear",
                                                           "remove", "pop"]),
                "xs": a, "other": b, "okind": kind, "bad": bad, "v": v,
                "selfit": rng.random() < .2}
    d = [[k, rng.randrange(-2, 4)] for k in collabc_uniq(xs)]
    k = rng.choice(xs) if xs and rng.random() < .6 else rng.randrange(-3, 6)
    failk = None if rng.random() < .75 else rng.randrange(-3, 6)
    if r == 22:
        return {"fn": "collabc.map_op", "op": rng.choice(["get", "contains", "items", "values",
                                                          "valuecontains", "keyscontain",
                                                          "itemcontains"]),
                "d": d, "k": k, "default": 99, "fail": failk, "bad": bad, "v": rng.randrange(-2, 4),
                "ikind": rng.choice(["tuple", "list", "short", "long", "none"]),
                "who": rng.choice(["abc", "dict"])}
    other = [[rng.randrange(-3, 6), rng.randrange(-2, 4)] for _ in range(rng.randrange(0, 4))]
    op = rng.choice(["pop", "popd", "popitem", "clear", "setdefault", "update_map", "update_pairs"])
    if op == "update_map":
        other = [[k2, v2] for k2, v2 in dict(map(tuple, other)).items()]
    return {"fn": "collabc.mmap_op", "op": op, "d": d, "k": k, "default": 99, "fail": failk,
            "kw": [], "other": other}


def collabc_operand(case):
    k = case["okind"]
    if k == "set":
        return collabc_Set(case["other"])
    if k == "iter":
        return iter(case["other"])
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
    if fn == "check_methods":
        return {"ok": collabc_ret(collabc_check_methods(collabc_fake(case["mro"]),
                                                        *case["methods"]))}
    if fn == "hook":
        cls = getattr(collabc_A, case["cls"])
        hook = getattr(collabc_A, case["x"]).__dict__["__subclasshook__"].__func__
        return collabc_hook(cls, hook, case["mro"])
    if fn == "stub":
        return py_result(collabc_STUBS[case["name"]])
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
        return collabc_builtin_close([tuple(s) for s in case["script"]])
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
        s = collabc_Seq(raw, fail)
        return py_result(lambda: list(reversed(s)))
    if fn == "seq_contains":
        s = collabc_Seq(xs, fail)
        return py_result(lambda: collabc_E(case["v"]) in s)
    if fn == "seq_count":
        s = collabc_Seq(xs, fail)
        return py_result(lambda: s.count(collabc_E(case["v"])))
    if fn == "seq_index":
        s = collabc_Seq(xs, fail)
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
        s = collabc_MSeq(raw, None)
        s.append(case["v"])
        return {"ok": s.xs}
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
        s = collabc_MSeq(raw, fail)
        vs = case["vs"]
        return py_result(lambda: (s.extend(s if vs is None else vs), s.xs)[1])
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
    if fn == "bytestring_new":
        import warnings
        with warnings.catch_warnings(record=True) as w:
            warnings.simplefilter("always")
            type(collabc_A.ByteString)(case["name"], (), {})
        return {"ok": any(x.category is DeprecationWarning for x in w)}
    if fn == "bytestring_check":
        import warnings
        with warnings.catch_warnings(record=True) as w:
            warnings.simplefilter("always")
            a = isinstance(b"" if case["answer"] else 1, collabc_A.ByteString)
        return {"ok": [any(x.category is DeprecationWarning for x in w), a]}
    if fn == "view_repr":
        cls = getattr(collabc_A, case["cls"])
        return {"ok": repr(cls({1: 2}))}
    if fn == "set_cmp":
        s = collabc_Set(raw)
        o = collabc_operand(case)
        m = {"le": s.__le__, "lt": s.__lt__, "ge": s.__ge__, "gt": s.__gt__, "eq": s.__eq__}
        return py_result(lambda: collabc_ret(m[case["op"]](o)))
    if fn == "set_op":
        s = collabc_Set(raw)
        o = collabc_operand(case)
        m = {"and": s.__and__, "or": s.__or__, "sub": s.__sub__, "rsub": s.__rsub__,
             "xor": s.__xor__}
        return py_result(lambda: collabc_setret(m[case["op"]](o)))
    if fn == "set_isdisjoint":
        s = collabc_Set(raw)
        o = collabc_operand(case)
        return py_result(lambda: s.isdisjoint(o))
    if fn == "set_hash":
        return collabc_plain(lambda: collabc_A.Set._hash(collabc_HSet(case["hashes"])))
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


def collabc_throw(case):
    def mk(a):
        if a is None:
            return None
        if a["k"] == "cls":
            return {"ValueError": ValueError, "KeyError": KeyError}[a["n"]]
        if a["k"] == "inst":
            return {"ValueError": ValueError}[a["n"]]("x")
        return 5
    tb = None
    if case["tb"]:
        try:
            raise ValueError
        except ValueError as e:
            tb = e.__traceback__
    try:
        collabc_A.Generator.throw(None, mk(case["typ"]), mk(case["val"]), tb)
    except (ValueError, KeyError) as e:
        return {"ok": {"raised": type(e).__name__,
                       "tb": e.__traceback__.tb_next.tb_next is not None}}
    except (TypeError, AttributeError) as e:
        return {"ok": {"wrong": type(e).__name__}}


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


def collabc_builtin_close(script):
    g = collabc_real(script[0] if script else ("exit", 0))
    next(g)
    return {"ok": {"r": py_result(g.close), "left": 0}}


def collabc_callable(case):
    import typing
    a, r = case["a"], {"float": float}[case["r"]]
    names = {"int": int, "str": str, "bool": bool}
    T = typing.ParamSpec("T")
    arg = {"seq": lambda: [names[n] for n in a["items"]], "ell": lambda: Ellipsis, "param": lambda: T,
           "other": lambda: int}.get(a["k"])
    item = (r,) if arg is None else (arg(), r)
    if arg is None:
        item = (int, str, r)

    def f():
        x = collabc_A._CallableGenericAlias(collabc_A.Callable, item)
        args = [getattr(t, "__name__", "...") if t is not T else "~T" for t in x.__args__]
        red = x.__reduce__()[1][1][0]
        red = ([t.__name__ for t in red] if isinstance(red, list)
               else "..." if red is Ellipsis else "~T")
        return {"args": args, "repr": repr(x), "reduce": red}
    return py_result(f)


def collabc_getitem(case):
    import typing
    names = {"int": int, "str": str, "bool": bool, "float": float}
    a, b = names[case["a"]], names[case["b"]]
    if case["shape"] == "tv":
        T, S = typing.TypeVar("T"), typing.TypeVar("S")
        x = collabc_A.Callable[[T, int], S][a, b]
    else:
        P = typing.ParamSpec("P")
        x = collabc_A.Callable[P, int][[a, b]]
    assert type(x) is collabc_A._CallableGenericAlias
    return {"ok": [t.__name__ for t in x.__args__]}


def collabc_mset(case, raw):
    s = collabc_Set(raw)
    o = s if case["selfit"] else collabc_operand(case)
    op = case["op"]

    def f():
        if op == "ior":
            s.__ior__(collabc_operand(case))
        elif op == "iand":
            s.__iand__(collabc_operand(case))
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


def collabc_map(case):
    m = collabc_Map(case["d"], case["fail"])
    op, k = case["op"], case["k"]
    E = collabc_E
    if op == "get":
        return py_result(lambda: m.get(k, case["default"]))
    if op == "contains":
        return py_result(lambda: k in m)
    if op == "items":
        return py_result(lambda: [list(p) for p in m.items()])
    if op == "values":
        return py_result(lambda: list(m.values()))
    if op == "valuecontains":
        m2 = collabc_Map([(a, E(b)) for a, b in case["d"]], case["fail"])
        return py_result(lambda: E(k) in m2.values())
    if op == "keyscontain":
        return py_result(lambda: k in m.keys())
    item = {"tuple": (k, case["v"]), "list": [k, case["v"]], "short": (1,), "long": (1, 2, 3),
            "none": 5}[case["ikind"]]
    if case["who"] == "abc":
        return py_result(lambda: item in m.items())
    return py_result(lambda: item in dict(case["d"]).items())


def collabc_mmap(case):
    m = collabc_Map(case["d"], case["fail"])
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
        other = dict(tuple(p) for p in case["other"])
        return py_result(lambda: (m.update(other), items())[1])
    return py_result(lambda: (m.update(iter(case["other"])), items())[1])
# ====== END AREA collabc ======

# ====== BEGIN AREA functools (Lib/functools.py, Modules/_functoolsmodule.c) ======
# Everything for this area stays between these two markers; prefix top-level names with functools_.
import abc as functools_abc  # noqa: E402
from test.support import import_helper as functools_ih  # noqa: E402

functools_C = functools_ih.import_fresh_module("functools", fresh=["_functools"])
functools_P = functools_ih.import_fresh_module("functools", blocked=["_functools"])


def functools_mod(case):
    return functools_C if case.get("twin") == "c" else functools_P


def functools_iter(case):
    def gen():
        yield from case["xs"]
        if case["itfail"]:
            raise ValueError("it")
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


def functools_run_partial(case):
    m = functools_mod(case)

    def go():
        p = functools_build(m, case["spec"])
        if not isinstance(p, m.partial):
            return "notpartial"
        PH = m.Placeholder
        return {"func": functools_fid_safe(p.func, m),
                "args": ["PH" if a is PH else a for a in p.args],
                "kw": [[k, v] for k, v in p.keywords.items()],
                "call": py_result(lambda: p(*case["more"], **dict(case["morekw"])))}
    return py_result(go)


def functools_fid_safe(f, m):
    if isinstance(f, m.partial):
        o = getattr(type(f), "_o", None)
        return {"partial": o}
    return f()[0]


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


functools_V = [(0, 0), (1, 0), (2, 0), (1, 1), (1, 2), (2, 2), (3, 0)]  # (value, type)


def functools_val(p):
    n, t = p
    return [n, float(n), str(n)][t]


def functools_lru_call(rng):
    args = [list(rng.choice(functools_V)) for _ in range(rng.randrange(0, 3))]
    kw = [[k, list(rng.choice(functools_V))] for k in rng.sample(["x", "y"], rng.randrange(0, 2))]
    return {"args": args, "kw": kw}


def functools_worlds(rng):
    """A random hierarchy: returns real classes, with virtual registrations applied later."""
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
    return classes


def functools_world_json(classes):
    idx = {c: i for i, c in enumerate(classes)}
    def members(cs):
        return [idx[c] for c in cs if c in idx]
    return {"n": len(classes),
            "bases": [members(c.__bases__) for c in classes],
            "mro": [members(c.__mro__) for c in classes],
            "subclasses": [members(c.__subclasses__()) if c is not object else []
                           for c in classes],
            "issub": [[j for j, b in enumerate(classes) if issubclass(c, b)] for c in classes],
            "abc": [i for i, c in enumerate(classes) if hasattr(c, "__abstractmethods__")]}


functools_HIER = {}


def functools_gen(rng):
    r = rng.randrange(0, 15)
    twin = rng.choice(["c", "py"])
    if r == 0:
        xs = [rng.randrange(-3, 6) for _ in range(rng.randrange(0, 5))]
        return {"fn": "functools.reduce", "twin": twin, "xs": xs,
                "noniter": rng.random() < .1, "itfail": rng.random() < .2,
                "initial": rng.choice([None, 0, 7]), "kind": rng.choice(["add", "sub"]),
                "bad": rng.choice([None, None, 2])}
    if r == 1:
        ops = ["__lt__", "__le__", "__gt__", "__ge__"]
        return {"fn": "functools.total_ordering", "roots": rng.sample(ops, rng.randrange(0, 3)),
                "op": rng.choice(ops), "a": rng.randrange(0, 3), "b": rng.randrange(0, 3),
                "foreign": rng.random() < .2}
    if r == 2:
        return {"fn": "functools.cmp_key", "twin": twin, "x": rng.randrange(0, 4),
                "other": rng.choice([0, 1, 2, 3, None]),
                "op": rng.choice(["lt", "le", "eq", "ne", "gt", "ge"]),
                "bad": rng.choice([None, None, 1])}
    if r in (3, 4, 5):
        spec = functools_spec(rng, 3)
        if spec["kind"] == "base":
            spec = {"kind": "partial", "func": spec, "args": [], "kw": [], "override": None,
                    "dict": False}
        spec["override"] = None
        return {"fn": "functools.partial", "twin": twin, "spec": spec,
                "more": [rng.randrange(0, 9) for _ in range(rng.randrange(0, 4))],
                "morekw": [["b", 9]] if rng.random() < .3 else []}
    if r == 6:
        n = rng.randrange(0, 4)
        args = [("PH" if rng.random() < .3 else 1) for _ in range(n)]
        kw = rng.choice(["none", "dict", "bad"])
        ns = rng.choice(["none", "dict", "bad"])
        return {"fn": "functools.setstate", "twin": twin, "isTuple": rng.random() < .9,
                "size": rng.choice([4, 4, 4, 4, 3]), "callable": rng.random() < .9,
                "argsTuple": rng.random() < .9, "args": args, "kwNone": kw == "none",
                "kwDict": kw == "dict", "nsNone": ns == "none", "nsDict": ns == "dict"}
    if r == 7:
        return {"fn": "functools.make_key", "typed": False, **functools_lru_call(rng)}
    if r in (8, 9):
        ops = ["clear" if rng.random() < .07 else functools_lru_call(rng)
               for _ in range(rng.randrange(0, 12))]
        return {"fn": "functools.lru", "twin": twin, "ops": ops, "typed": rng.random() < .3,
                "maxsize": rng.choice([None, 0, 1, 2, 3]), "bad": rng.choice([None, None, 2])}
    if r == 10:
        k = rng.choice(["int", "int", "none", "callable", "other"])
        return {"fn": "functools.lru_mode", "twin": twin, "kind": k, "typedbool": rng.random() < .7,
                "n": rng.choice([-2**70, -1, 0, 1, 5, 2**63 - 1])}
    if r == 11:
        seqs = [rng.sample(range(5), rng.randrange(0, 4)) for _ in range(rng.randrange(0, 4))]
        return {"fn": "functools.c3_merge", "seqs": seqs}
    if r == 12:
        classes = functools_worlds(rng)
        key = len(functools_HIER)
        for c in classes[1:]:
            if rng.random() < .3:
                targets = [t for t in classes[1:] if isinstance(t, functools_abc.ABCMeta)
                           and not issubclass(t, c)]
                if targets:
                    rng.choice(targets).register(c)
        functools_HIER[key] = classes
        i = rng.randrange(len(classes))
        types = rng.sample(range(len(classes)), rng.randrange(0, len(classes) + 1))
        which = rng.choice(["c3_mro", "compose_mro", "find_impl"])
        if which == "find_impl" and 0 not in types:
            types.append(0)
        w = functools_world_json(classes)
        extra = {"abcs": [t for t in types if t in w["abc"]]} if which == "c3_mro" else {}
        return {"fn": "functools." + which, "key": key, "cls": i, "types": types, **w, **extra}
    if r == 13:
        return functools_dispatch_case(rng)
    k = rng.randrange(0, 11)
    if k == 4:
        n = rng.randrange(0, 3)
        return {"fn": "functools.pm_call", "bound": rng.random() < .5,
                "args": [("PH" if i < n - 1 and rng.random() < .5 else 7) for i in range(n)],
                "obj": 1, "more": [rng.randrange(0, 5) for _ in range(rng.randrange(0, 3))]}
    if k == 5:
        return {"fn": "functools.descr_get", "twin": twin, "obj": rng.choice([None, 3]),
                "more": [rng.randrange(0, 5) for _ in range(rng.randrange(0, 3))]}
    if k == 6:
        return {"fn": "functools.sdm_getattr",
                "name": rng.choice(["__name__", "__qualname__", "__isabstractmethod__",
                                    "__annotations__", "__type_params__", "foo", "__dict2__"])}
    if k == 7:
        return {"fn": "functools.sdm_init", "callable": rng.random() < .5,
                "hasget": rng.random() < .5}
    if k == 8:
        return {"fn": "functools.sd_noarg"}
    if k == 9:
        return {"fn": "functools.reduce_warns",
                "names": rng.sample(["function", "sequence", "initial"], rng.randrange(0, 3))}
    if k == 10:
        return {"fn": rng.choice(["functools.key_sig", "functools.lru_misc", "functools.unwrap"]),
                "q": "functools_mod", "depth": 2}
    if k == 0:
        return {"fn": "functools.update_wrapper",
                "wrapper": [["__name__", 1]], "wrapped": rng.sample([["__name__", 2], ["__doc__", 3],
                                                                     ["__module__", 4]], 2),
                "wrapperd": [["x", 1], ["y", 2]], "wrappedd": rng.sample([["y", 5], ["z", 6]], 1),
                "assigned": rng.sample(["__name__", "__doc__", "__module__", "__qualname__"], 3)}
    if k == 1:
        return {"fn": "functools.cached_get",
                "name": rng.choice(["p", None]), "fail": rng.random() < .2,
                "dict": rng.choice([None, [], [["p", 1]], [["q", 1]]]), "frozen": rng.random() < .2}
    if k == 2:
        return {"fn": "functools.set_name", "attr": rng.choice([None, "a", "b"]), "name": "a"}
    return {"fn": "functools.sdm_repr", "q": rng.choice([None, "A.f"]), "n": rng.choice([None, "f"]),
            "o": rng.choice([None, "5"])}


def functools_dispatch_case(rng):
    classes = functools_worlds(rng)
    m = rng.choice([functools_P])

    def f(x):
        return 1000
    d = m.singledispatch(f)
    worlds, ops, out = [], [], []
    impls = {}

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
                       and not issubclass(t, classes[c])]
            if targets and classes[c] is not object:
                rng.choice(targets).register(classes[c])
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
    return {"fn": "functools.dispatch", "worlds": worlds, "ops": ops, "expect": out}


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
    if fn == "total_ordering":
        return functools_total(case)
    if fn == "cmp_key":
        bad = case["bad"]

        def cmp(a, b):
            if a == bad:
                raise ValueError("cmp")
            return a - b
        K = m.cmp_to_key(cmp)
        x = K(case["x"])
        o = K(case["other"]) if case["other"] is not None else 5
        import operator
        op = getattr(operator, case["op"])
        return py_result(lambda: op(x, o))
    if fn == "partial":
        return functools_run_partial(case)
    if fn == "setstate":
        return functools_setstate(case, m)
    if fn == "make_key":
        args = tuple(functools_val(p) for p in case["args"])
        kw = {k: functools_val(v) for k, v in case["kw"]}
        k = functools_P._make_key(args, kw, False)
        return {"ok": k if isinstance(k, int) else ("tuple" if not isinstance(k, str) else int(k))}
    if fn == "lru":
        return functools_lru(case, m)
    if fn == "lru_mode":
        return functools_lru_mode(case, m)
    if fn == "c3_merge":
        return py_result(lambda: functools_P._c3_merge([list(s) for s in case["seqs"]]))
    if fn in ("c3_mro", "compose_mro", "find_impl"):
        cs = functools_HIER[case["key"]]
        idx = {c: i for i, c in enumerate(cs)}
        cls = cs[case["cls"]]
        if fn == "c3_mro":
            return py_result(lambda: [idx[c] for c in functools_P._c3_mro(
                cls, [cs[a] for a in case["abcs"]])])
        if fn == "compose_mro":
            return py_result(lambda: [idx[c] for c in functools_P._compose_mro(
                cls, [cs[a] for a in case["types"]])])
        reg = {cs[t]: t + 1000 for t in case["types"]}
        return py_result(lambda: functools_P._find_impl(cls, reg))
    if fn == "dispatch":
        return {"ok": case["expect"]}
    if fn == "update_wrapper":
        wrapper = functools_attrobj(dict(case["wrapper"]), case["wrapperd"])
        wrapped = functools_attrobj(dict(case["wrapped"]), case["wrappedd"])
        r = functools_P.update_wrapper(wrapper, wrapped, tuple(case["assigned"]))
        attrs = dict(r.attrs)
        attrs["__wrapped__"] = 7 if attrs["__wrapped__"] is wrapped else -1
        return {"ok": [sorted([k, v] for k, v in attrs.items()),
                       sorted([k, v] for k, v in r.d.items())]}
    if fn == "cached_get":
        return functools_cached(case)
    if fn == "set_name":
        cp = functools_P.cached_property(lambda s: 1)
        cp.attrname = case["attr"]

        def go():
            cp.__set_name__(object, case["name"])
            return cp.attrname
        return py_result(go)
    if fn == "sdm_repr":
        return functools_sdm(case)
    if fn == "pm_call":
        return functools_pm(case)
    if fn == "descr_get":
        q = m.partial(lambda *a: list(a))
        obj = case["obj"]
        return {"ok": q.__get__(obj, int)(*case["more"])}
    if fn == "sdm_getattr":
        def f():
            return 0
        g = functools_P.singledispatchmethod(f).__get__(None, int)
        n = case["name"]
        try:
            g.__getattr__(n)
            return {"ok": True}
        except AttributeError as e:
            return {"ok": str(e) != ""}
    if fn == "sdm_init":
        cls = type("X", (), {**({"__call__": lambda s: 0} if case["callable"] else {}),
                             **({"__get__": lambda s, o, t=None: s} if case["hasget"] else {})})
        return py_result(lambda: (functools_P.singledispatchmethod(cls()), None)[1])
    if fn == "sd_noarg":
        def f2(*a):
            return 0
        f2.__name__ = "f"
        return py_result(functools_P.singledispatch(f2))
    if fn == "reduce_warns":
        import warnings
        kw = {k: {"function": max, "sequence": [1], "initial": 0}[k] for k in case["names"]}
        with warnings.catch_warnings(record=True) as w:
            warnings.simplefilter("always")
            try:
                if "function" in kw or "sequence" in kw:
                    functools_P.reduce(**kw)
                else:
                    functools_P.reduce(max, [1], **kw)
            except TypeError:
                pass
        return {"ok": any(x.category is DeprecationWarning for x in w)}
    if fn == "key_sig":
        return {"ok": functools_C.cmp_to_key(max).__text_signature__}
    if fn == "lru_misc":
        import copy
        wr = functools_C.lru_cache(functools_mod)
        assert copy.copy(wr) is wr and copy.deepcopy(wr) is wr
        assert wr.__get__(None, int) is wr and type(wr.__get__(1, int)).__name__ == "method"
        return {"ok": [wr.__reduce__()]}
    if fn == "unwrap":
        f = functools_mod
        q = functools_P.partial(functools_P.partial(f))
        assert functools_P._unwrap_partial(q) is f
        assert functools_P._unwrap_partialmethod(functools_P.partialmethod(q)) is f
        return {"ok": True}
    raise ValueError(fn)


def functools_pm(case):
    P = functools_P.Placeholder
    args = [P if a == "PH" else a for a in case["args"]]

    def target(*a):
        return [1, list(a), []]
    if case["bound"]:
        class A:
            h = functools_P.partialmethod(target, *args)
    else:
        class Plain:
            def __call__(self, *a):
                return [1, list(a), []]

        class A:
            h = functools_P.partialmethod(Plain(), *args)
    obj = A()
    r = py_result(lambda: obj.h(*case["more"]))
    if "ok" in r:
        r["ok"][1][0] = 1
    return r


class functools_attrobj:
    """An object whose attribute reads and writes are visible as a dict, and whose `__dict__`
    is a separate dict, so `update_wrapper` can be observed."""

    def __init__(self, attrs, d):
        object.__setattr__(self, "attrs", dict(attrs))
        object.__setattr__(self, "d", dict(d))

    def __getattribute__(self, k):
        if k == "__dict__":
            return object.__getattribute__(self, "d")
        if k in ("attrs", "d"):
            return object.__getattribute__(self, k)
        a = object.__getattribute__(self, "attrs")
        if k in a:
            return a[k]
        raise AttributeError(k)

    def __setattr__(self, k, v):
        object.__getattribute__(self, "attrs")[k] = v


def functools_total(case):
    root_ops = {"__lt__": "<", "__le__": "<=", "__gt__": ">", "__ge__": ">="}
    foreign = case["foreign"]
    body = {"__eq__": lambda s, o: s.v == o.v, "__hash__": None,
            "__init__": lambda s, v: setattr(s, "v", v)}
    for r in case["roots"]:
        body[r] = eval(f"lambda s, o: NotImplemented if {foreign} else s.v {root_ops[r]} o.v")

    def go():
        c = functools_P.total_ordering(type("T", (), body))
        v = getattr(c, case["op"])(c(case["a"]), c(case["b"]))
        return "NotImplemented" if v is NotImplemented else {"val": v}
    return py_result(go)


def functools_setstate(case, m):
    PH = m.Placeholder
    args = [PH if a == "PH" else a for a in case["args"]]
    fn = (lambda: 0) if case["callable"] else 5
    a = tuple(args) if case["argsTuple"] else args
    kw = None if case["kwNone"] else ({} if case["kwDict"] else 5)
    ns = None if case["nsNone"] else ({} if case["nsDict"] else 5)
    st = (fn, a, kw, ns)
    if case["size"] != 4:
        st = st[:case["size"]]
    if not case["isTuple"]:
        st = list(st)
    p = m.partial(lambda: 0)

    def go():
        p.__setstate__(st)
        return sum(1 for x in p.args if x is PH)
    return py_result(go)


def functools_lru(case, m):
    bad = case["bad"]

    def f(*a, **k):
        v = sum(int(x) for x in a) + sum(int(x) for x in k.values())
        if v == bad:
            raise ValueError("f")
        return v
    w = m.lru_cache(maxsize=case["maxsize"], typed=case["typed"])(f)
    out = []
    for op in case["ops"]:
        if op == "clear":
            w.cache_clear()
            continue
        args = [functools_val(p) for p in op["args"]]
        kw = {k: functools_val(v) for k, v in op["kw"]}
        out.append(py_result(lambda: w(*args, **kw)))
    i = w.cache_info()
    return {"ok": [out, [i.hits, i.misses, i.maxsize, i.currsize]]}


def functools_lru_mode(case, m):
    k = case["kind"]
    arg = {"int": case["n"], "none": None, "callable": (lambda: 0), "other": 1.5}[k]
    typed = False if case["typedbool"] else 1

    def go():
        w = m.lru_cache(arg, typed)
        if k != "callable":
            w = w(lambda: 0)
        i = w.cache_info()
        return ("infinite" if i.maxsize is None else "uncached" if i.maxsize == 0
                else int(i.maxsize))
    return py_result(go)


def functools_cached(case):
    class Plain:
        pass

    def func(self):
        if case["fail"]:
            raise ValueError("f")
        return 5
    cp = functools_P.cached_property(func)
    cp.attrname = case["name"]
    d = case["dict"]
    if d is None:
        inst = type("S", (), {"__slots__": ()})()
    else:
        inst = Plain()
        if case["frozen"]:
            inst = functools_frozen(dict(d))
        else:
            inst.__dict__.update(d)

    def go():
        v = cp.__get__(inst, type(inst))
        dd = inst.__dict__
        return [v, [[k, x] for k, x in dd.items()]]
    return py_result(go)


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
    q, n, o = case["q"], case["n"], case["o"]

    class F:
        def __call__(self):
            return 0
    f = F()
    if q is not None:
        f.__qualname__ = q
    if n is not None:
        f.__name__ = n
    s = functools_P.singledispatchmethod(f)

    class Obj:
        def __repr__(self):
            return o
    g = s.__get__(Obj() if o is not None else None, Obj)
    return {"ok": [repr(s), repr(g)]}
# ====== END AREA functools ======

# ====== BEGIN AREA operator (Lib/operator.py, Modules/_operator.c, Lib/copy.py, Lib/abc.py) ======
# Everything for this area stays between these two markers; prefix top-level names with operator_.
import abc as operator_abc  # noqa: E402
import copy as operator_copy  # noqa: E402
import _operator as operator_C  # noqa: E402
from test.support import import_helper as operator_ih  # noqa: E402

operator_P = operator_ih.import_fresh_module("operator", blocked=["_operator"])
operator_BIN = {"add": "+", "sub": "-", "mul": "*", "matmul": "@", "floordiv": "//",
                "truediv": "/", "mod": "%", "lshift": "<<", "rshift": ">>", "and_": "&",
                "xor": "^", "or_": "|"}
operator_DUNDER = {"add": "add", "sub": "sub", "mul": "mul", "matmul": "matmul",
                   "floordiv": "floordiv", "truediv": "truediv", "mod": "mod",
                   "lshift": "lshift", "rshift": "rshift", "and_": "and", "xor": "xor",
                   "or_": "or"}
operator_DUNDER["pow"] = "pow"


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
    if case["sub"]:
        B = type("B", (A,), r)
    else:
        B = type("B", (), r)
    return A, B


def operator_gen(rng):
    r = rng.randrange(0, 18)
    twin = rng.choice(["c", "py"])
    if r in (0, 1):
        name = rng.choice(list(operator_BIN))
        l, rr = rng.choice(["none", "val", "ni", "raise"]), rng.choice(["none", "val", "ni", "raise"])
        sub = rng.random() < .3 and rr != "none"
        case = {"twin": twin, "name": name, "sym": operator_BIN[name], "l": l, "r": rr, "sub": sub}
        if r == 0:
            return {"fn": "operator.binop", **case}
        return {"fn": "operator.iop", **case, "i": rng.choice(["none", "val", "ni", "raise"])}
    if r == 2:
        return {"fn": "operator.cmp", "twin": twin, "op": rng.choice(["lt", "le", "eq", "ne", "gt", "ge"]),
                "l": rng.choice(["val", "ni", "raise"]), "r": rng.choice(["val", "ni", "raise"]),
                "sub": rng.random() < .3}
    if r == 3:
        return {"fn": "operator.unary", "twin": twin, "name": rng.choice(["neg", "pos", "invert", "abs"]),
                "has": rng.random() < .6, "desc": ""}
    if r == 4:
        return {"fn": "operator.index", "twin": twin, "k": rng.choice(["int", "none", "bad"]),
                "n": rng.choice([0, -1, 2**70])}
    if r == 5:
        kinds = ["list", "tuple", "dict", "seqadd", "radd", "plain", "int"]
        return {"fn": "operator.concat", "twin": twin, "a": rng.choice(kinds), "b": rng.choice(kinds),
                "inplace": rng.random() < .4}
    if r in (6, 7):
        xs = [rng.randrange(0, 4) for _ in range(rng.randrange(0, 6))]
        return {"fn": "operator." + ("count_of" if r == 6 else "index_of"), "twin": twin, "xs": xs,
                "b": rng.randrange(0, 4), "bad": rng.choice([None, None, None, 1]),
                "itfail": rng.random() < .2}
    if r == 8:
        return {"fn": "operator.length_hint", "twin": twin,
                "len": rng.choice([None, None, 3, 0, "raise"]),
                "hint": rng.choice([None, 0, 2, -1, "ni", "typeerror", "raise", "str"]),
                "dkind": rng.choice(["int", "int", "int", "other"]) if True else "",
                "d": rng.choice([0, 7, -1])}
    if r == 9:
        xs = [rng.randrange(0, 9) for _ in range(rng.randrange(0, 5))]
        return rng.choice([
            {"fn": "operator.itemgetter", "twin": twin, "xs": xs,
             "items": [rng.randrange(-6, 6) for _ in range(rng.randrange(1, 4))]},
            {"fn": "operator.itemgetter_fast", "xs": xs, "i": rng.randrange(-6, 6)}])
    if r == 10:
        return {"fn": "operator.getter_repr", "twin": twin, "cls": "operator.itemgetter",
                "items": [str(rng.randrange(0, 5)) for _ in range(rng.randrange(1, 4))]}
    if r == 11:
        names = ["a", "b.c", "x", "a.x", "", "a.", ".b", 5]
        return {"fn": "operator.attrgetter", "twin": twin,
                "attrs": [rng.choice(names) for _ in range(rng.randrange(1, 3))]}
    if r == 12:
        k = rng.randrange(0, 3)
        if k == 0:
            return {"fn": "operator.mc_new", "twin": twin, "name": rng.choice([None, "BAD", "m"])}
        args = [rng.randrange(0, 5) for _ in range(rng.randrange(0, 9))]
        kw = [[n, rng.randrange(0, 5)] for n in rng.sample(["p", "q", "r"], rng.randrange(0, 3))]
        if k == 1:
            return {"fn": "operator.mc_call", "twin": twin, "args": args, "kw": kw}
        return {"fn": "operator.mc_repr", "twin": twin, "args": [repr(a) for a in args],
                "kw": [[n, repr(v)] for n, v in kw]}
    if r == 13:
        def arg():
            k = rng.choice(["str", "str", "bytes", "bytes", "int"])
            return {"k": k, "ascii": rng.random() < .8,
                    "data": [rng.randrange(97, 100) for _ in range(rng.randrange(0, 4))]}
        a = arg()
        return {"fn": "operator.digest", "a": a, "b": dict(a) if rng.random() < .3 else arg()}
    if r == 14:
        return operator_graph(rng)
    if r == 15:
        return rng.choice([
            {"fn": "operator.copy_route", "k": "tuple", "n": rng.randrange(2, 7)},
            {"fn": "operator.deep_method", "self": rng.choice([0, 1])},
            {"fn": "operator.subscript", "twin": twin, "op": rng.choice(["get", "contains"]),
             "xs": [1, 2, 3], "i": rng.randrange(-5, 5)},
            {"fn": "operator.call_op", "twin": twin, "args": [0] * rng.randrange(0, 3)},
            {"fn": "operator.replace", "has": rng.random() < .5}])
    if r == 16:
        names = ["f", "g", "h"]
        return {"fn": "operator.update_abstract", "isabc": rng.random() < .8,
                "parents": [rng.sample(names, rng.randrange(0, 3)) for _ in range(rng.randrange(1, 3))],
                "abstract": rng.sample(names, rng.randrange(0, 3)),
                "own": [[n, rng.random() < .5] for n in rng.sample(["u", "v"], rng.randrange(0, 2))]}
    return operator_abc_case(rng)


def operator_graph(rng):
    n = rng.randrange(1, 7)
    cells = []
    for i in range(n):
        k = rng.choice(["atom", "atom", "list", "tuple", "dict"])
        if k == "atom":
            cells.append({"k": k, "n": rng.randrange(0, 4)})
        elif k == "list":
            cells.append({"k": k, "items": [rng.randrange(0, n) for _ in range(rng.randrange(0, 3))]})
        elif k == "tuple":
            low = [j for j in range(i) if cells[j]["k"] != "tuple"] + list(range(i + 1, n))
            cells.append({"k": k, "items": rng.sample(low, min(len(low), rng.randrange(0, 3)))})
        else:
            atoms = list({cells[j]["n"]: j for j in range(i) if cells[j]["k"] == "atom"}.values())
            items = []
            for key in rng.sample(atoms, min(len(atoms), 2)):
                items += [key, rng.randrange(0, n)]
            cells.append({"k": k, "items": items})
    # a tuple may only refer forward to non-tuples, so it can be built after them
    for i, c in enumerate(cells):
        if c["k"] == "tuple":
            c["items"] = [j for j in c["items"] if cells[j]["k"] != "tuple"]
    return {"fn": "operator.deepcopy", "cells": cells, "root": rng.randrange(0, n)}


def operator_build_graph(cells):
    objs = {}
    for i, c in enumerate(cells):
        if c["k"] == "atom":
            objs[i] = operator_Atom(c["n"])
        elif c["k"] == "list":
            objs[i] = []
        elif c["k"] == "dict":
            objs[i] = {}
    for i, c in enumerate(cells):
        if c["k"] == "tuple":
            objs[i] = tuple(objs[j] for j in c["items"])
    for i, c in enumerate(cells):
        if c["k"] == "list":
            objs[i].extend(objs[j] for j in c["items"])
        elif c["k"] == "dict":
            it = c["items"]
            for a, b in zip(it[::2], it[1::2]):
                objs[i][objs[a]] = objs[b]
    return objs


class operator_Atom(int):
    """An int subclass would be copied, so use exact behaviour through deepcopy's atomic table."""

    def __deepcopy__(self, memo):
        return self


def operator_render(o, seen):
    if isinstance(o, operator_Atom):
        return ["atom", int(o)]
    for i, s in enumerate(seen):
        if s is o:
            return ["ref", i]
    seen.append(o)
    if isinstance(o, list):
        return ["list", [operator_render(x, seen) for x in o]]
    if isinstance(o, tuple):
        return ["tuple", [operator_render(x, seen) for x in o]]
    out = []
    for k, v in o.items():
        out.append(operator_render(k, seen))
        out.append(operator_render(v, seen))
    return ["dict", out]


def operator_abc_case(rng):
    n = rng.randrange(2, 5)
    A = operator_abc.ABCMeta("C0", (), {})
    classes = [A]
    hooks = []
    for i in range(1, n):
        base = rng.choice(classes)
        classes.append(operator_abc.ABCMeta(f"C{i}", (base,), {}))
    for i in range(1, n):
        if rng.random() < .3:
            j = rng.randrange(0, n)
            if j != i and not issubclass(classes[j], classes[i]):
                try:
                    classes[i].register(classes[j])
                except RuntimeError:
                    pass
    idx = {c: i for i, c in enumerate(classes)}
    W = {"mro": [[idx[m] for m in c.__mro__ if m in idx] for c in classes],
         "reg": [[idx[r] for r in c._abc_impl and operator_registry(c) if r in idx] for c in classes],
         "subs": [[idx[s] for s in c.__subclasses__() if s in idx] for c in classes]}
    key = len(operator_HIER)
    operator_HIER[key] = classes
    return {"fn": "operator.abc_check", "key": key, "cls": rng.randrange(n), "sub": rng.randrange(n),
            "hooks": hooks, **W}


operator_HIER = {}


def operator_registry(c):
    import _abc
    reg, _, _, _ = _abc._get_dump(c)
    return [r() for r in reg]


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
        name = {"and_": "iand", "or_": "ior"}.get(case["name"], "i" + case["name"])
        return py_result(lambda: getattr(m, name)(A(), B()))
    if fn == "cmp":
        return operator_cmp(case, m)
    if fn == "unary":
        name = case["name"]
        d = {"neg": "neg", "pos": "pos", "invert": "invert", "abs": "abs"}[name]
        cls = type("A", (), {f"__{d}__": (lambda s: 4)} if case["has"] else {})
        r = py_result(lambda: getattr(m, name)(cls()))
        if "exc" in r:
            r["msg"] = r["msg"]
            return {"exc": r["exc"], "msg": "bad operand type for : 'A'"}
        return r
    if fn == "index":
        k = case["k"]
        cls = {"int": type("I", (), {"__index__": lambda s: case["n"]}),
               "none": object, "bad": type("I", (), {"__index__": lambda s: "x"})}[k]

        def go():
            v = m.index(cls())
            return v if isinstance(v, int) else None
        return py_result(go)
    if fn == "concat":
        return operator_concat(case, m)
    if fn in ("count_of", "index_of"):
        bad = case["bad"]

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
        f = m.countOf if fn == "count_of" else m.indexOf
        return py_result(lambda: f(gen(), case["b"]))
    if fn == "length_hint":
        return operator_hint(case, m)
    if fn == "itemgetter":
        items = case["items"]
        return py_result(lambda: operator_as_list(m.itemgetter(*items)(tuple(case["xs"])), len(items)))
    if fn == "itemgetter_fast":
        return py_result(lambda: operator_C.itemgetter(case["i"])(tuple(case["xs"])))
    if fn == "getter_repr":
        ints = [int(i) for i in case["items"]]
        return {"ok": repr(m.itemgetter(*ints))}
    if fn == "attrgetter":
        return operator_attr(case, m)
    if fn == "mc_new":
        n = case["name"]
        if n is None:
            return py_result(lambda: (m.methodcaller(), None)[1])
        return py_result(lambda: (m.methodcaller(5 if n == "BAD" else n), n)[1])
    if fn == "mc_call":
        class O:
            def m(self, *a, **k):
                return [list(a), [[x, y] for x, y in k.items()]]
        return {"ok": m.methodcaller("m", *case["args"], **dict(case["kw"]))(O())}
    if fn == "mc_repr":
        args = [eval(a) for a in case["args"]]
        kw = {k: eval(v) for k, v in case["kw"]}
        return {"ok": repr(m.methodcaller("m", *args, **kw))}
    if fn == "digest":
        def conv(a):
            if a["k"] == "str":
                return "".join(map(chr, a["data"])) + ("" if a["ascii"] else "é")
            if a["k"] == "bytes":
                return bytes(a["data"])
            return 5
        return py_result(lambda: operator_C._compare_digest(conv(case["a"]), conv(case["b"])))
    if fn == "deepcopy":
        objs = operator_build_graph(case["cells"])
        x = objs[case["root"]]
        y = operator_copy.deepcopy(x)
        return {"ok": [operator_render(y, []), y is x]}
    if fn == "copy_route":
        n = case["n"]

        class R:
            def __reduce__(self):
                return (operator_mk, (), None, None, None, None)[:n]
        return py_result(lambda: (operator_copy.copy(R()), "reconstruct")[1])
    if fn == "deep_method":
        class O:
            def __init__(self, v):
                self.v = v

            def m(self):
                return 0
        o = O(1)
        bound = o.m if case["self"] == 1 else operator_Atom(1).__index__
        if case["self"] == 0:
            return {"ok": [True, True]}
        c = operator_copy.deepcopy(bound)
        return {"ok": [c.__func__ is bound.__func__, c.__self__ is bound.__self__]}
    if fn == "subscript":
        xs = tuple(case["xs"])
        if case["op"] == "get":
            return py_result(lambda: m.getitem(xs, case["i"]))
        return py_result(lambda: m.contains(xs, case["i"]))
    if fn == "call_op":
        args = [(lambda *a: len(a))] + [0] * (len(case["args"]) - 1) if case["args"] else []
        return py_result(lambda: m.call(*args))
    if fn == "replace":
        cls = type("X", (), {"__replace__": lambda s, **k: None} if case["has"] else {})
        return py_result(lambda: (operator_copy.replace(cls()), None)[1])
    if fn == "update_abstract":
        return operator_update(case)
    if fn == "abc_check":
        cs = operator_HIER[case["key"]]
        return {"ok": issubclass(cs[case["sub"]], cs[case["cls"]])}
    raise ValueError(fn)


def operator_mk():
    return object.__new__(operator_Empty)


class operator_Empty:
    pass


def operator_as_list(v, n):
    return list(v) if n > 1 else [v]


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
    A = type("A", (), {f"__{op}__": mk(case["l"], True), "__hash__": None})
    B = type("B", (A,) if case["sub"] else (), {f"__{refl}__": mk(case["r"], False),
                                                "__hash__": None})
    return py_result(lambda: getattr(m, op)(A(), B()))


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
    mk = {"list": list, "tuple": tuple, "dict": dict, "seqadd": SeqAdd, "radd": RAdd, "plain": Plain,
          "int": lambda: 5}
    names = {list: "list", tuple: "tuple", SeqAdd: "seqadd", RAdd: "radd", Plain: "plain"}
    a, b = mk[case["a"]](), mk[case["b"]]()
    f = m.iconcat if case["inplace"] else m.concat
    return py_result(lambda: names[type(f(a, b))])


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
            return {"ni": NotImplemented, "str": "x"}.get(hint, hint)
        body["__length_hint__"] = h
    obj = type("O", (), body)()
    d = case["d"] if case["dkind"] == "int" else "x"
    r = py_result(lambda: m.length_hint(obj, d))
    return r


def operator_attr(case, m):
    class N:
        def __init__(self, path):
            self.path = path

        def __getattr__(self, n):
            if n in ("", "x"):
                raise AttributeError("no attribute")
            return N(self.path + "." + n)

    attrs = case["attrs"]

    def go():
        v = m.attrgetter(*attrs)(N("o"))
        return [x.path for x in v] if isinstance(v, tuple) else [v.path]
    return py_result(go)


def operator_update(case):
    names = {}
    abstract = set(case["abstract"])
    parents = []
    for i, p in enumerate(case["parents"]):
        parents.append(p)
    body = {}
    for n, is_abs in case["own"]:
        f = (lambda: 0)
        if is_abs:
            f.__isabstractmethod__ = True
        body[n] = f

    class P:
        __slots__ = ("__abstractmethods__",)
    bases = []
    for i, p in enumerate(parents):
        ns = {n: operator_mark(n in abstract) for n in p}
        b = operator_abc.ABCMeta(f"P{i}", (), ns)
        b.__abstractmethods__ = frozenset(p)
        bases.append(b)
    all_names = {n for p in parents for n in p}
    if case["isabc"]:
        c = operator_abc.ABCMeta("C", tuple(bases), {**{n: operator_mark(n in abstract)
                                                       for n in all_names}, **body})
    else:
        return {"ok": None}
    operator_abc.update_abstractmethods(c)
    return {"ok": sorted(c.__abstractmethods__)}


def operator_mark(is_abs):
    def f():
        return 0
    if is_abs:
        f.__isabstractmethod__ = True
    return f
# ====== END AREA operator ======

# ====== BEGIN AREA enumdc (Lib/enum.py, Lib/dataclasses.py) ======
# Everything for this area stays between these two markers; prefix top-level names with enumdc_.
import dataclasses as enumdc_dc  # noqa: E402
import enum as enumdc_enum  # noqa: E402

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


def enumdc_gen(rng):
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


def enumdc_run(case):
    fn = case["fn"].split(".")[1]
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
                     ["ok", 1 if w.gi_suspended else 0], w.__name__, w.__qualname__]
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
                ops.append(["push_cm", i, beh(), asy])
            elif k < 0.75:
                ops.append(["callback", i, beh(), asy])
            elif k < 0.9:
                ops.append(["enter_ctx", i, beh(), rng.randint(0, 9), rng.random() < 0.2, a])
            else:
                ops.append(["enter_bad", a])
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
            if op[1]:
                out.append(misc_cres(lambda: misc_run_co(box[0].enter_async_context(MiscNoCM())), labels))
            else:
                out.append(misc_cres(lambda: box[0].enter_context(MiscNoCM()), labels))
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


def misc_pv(o):
    return ["o", o.i] if isinstance(o, MiscW) else ["i", o]


def misc_gen_weakref(rng):
    kind = rng.choice(["wvd", "wvd", "wkd", "wkd", "wm", "keyed", "fin", "fin"])
    case = {"fn": "misc.weakref", "k": kind}
    n = 4
    case["vals"] = [rng.randint(0, 3) for _ in range(n + 16)]
    def pv():
        return ["o", rng.randrange(n)] if rng.random() < 0.9 else ["i", rng.randint(0, 3)]
    def key():
        return rng.choice("abc")
    def kpv():
        return ["o", rng.randrange(n)] if rng.random() < 0.9 else ["i", 1]
    if kind == "wvd":
        def items():
            return [[key(), pv()] for _ in range(rng.randint(0, 3))]
        case["eager"] = rng.random() < 0.6
        case["init"] = [[key(), ["o", rng.randrange(n)]] for _ in range(rng.randint(0, 3))]
        ops = []
        for _ in range(rng.randint(1, 12)):
            k = rng.random()
            ops.append(rng.choice([
                ["set", key(), pv()], ["set", key(), pv()], ["get_", key()], ["del", key()], ["len"],
                ["in", key()], ["repr"], ["copy"], ["deepcopy"], ["get", key(), pv()], ["items"],
                ["keys"], ["iter"], ["irefs"], ["vrefs"], ["values"], ["popitem"],
                ["pop", key(), [pv()][:rng.randint(0, 1)]], ["setdefault", key(), pv()],
                ["update", rng.choice([None, items()])], ["update_pairs", items()], ["ior", items()],
                ["or", rng.choice([None, items()])], ["ror", rng.choice([None, items()])],
                ["kill", rng.randrange(n)], ["kill", rng.randrange(n)]]))
        case["ops"] = ops
    elif kind == "wkd":
        def items():
            return [[kpv(), rng.randint(0, 3)] for _ in range(rng.randint(0, 3))]
        case["eager"] = rng.random() < 0.6
        case["init"] = [[["o", rng.randrange(n)], rng.randint(0, 3)] for _ in range(rng.randint(0, 3))]
        ops = []
        for _ in range(rng.randint(1, 12)):
            ops.append(rng.choice([
                ["set", kpv(), rng.randint(0, 3)], ["set", kpv(), 1], ["get_", kpv()], ["del", kpv()],
                ["len"], ["repr"], ["copy"], ["deepcopy"], ["get", kpv(), 9], ["in", kpv()],
                ["items"], ["keys"], ["iter"], ["values"], ["krefs"], ["popitem"],
                ["pop", kpv(), [9][:rng.randint(0, 1)]], ["setdefault", kpv(), 7],
                ["update", rng.choice([None, items()]), rng.random() < 0.2],
                ["update_pairs", items()], ["ior", items()],
                ["or", rng.choice([None, items()])], ["ror", rng.choice([None, items()])],
                ["kill", rng.randrange(n)], ["kill", rng.randrange(n)]]))
        case["ops"] = ops
    elif kind == "wm":
        ops = []
        for _ in range(rng.randint(1, 10)):
            i, j = rng.randrange(3), rng.randrange(3)
            ops.append(rng.choice([
                ["new", rng.randrange(n), 10 + rng.randrange(2), rng.random() < 0.5],
                ["new", rng.randrange(n), 10 + rng.randrange(2), rng.random() < 0.5],
                ["bad"], ["call", i], ["eq", i, j], ["ne", i, j], ["eqo", i], ["alive", i],
                ["kill", rng.choice([rng.randrange(n), 10 + rng.randrange(2)])]]))
        case["ops"] = ops
    elif kind == "keyed":
        case["v"] = pv()
    else:
        spawned = [99]  # a finalizer is an object: each spawn gets an id of its own

        def fs(d=0):
            k = rng.random()
            if k < 0.5 or d > 1:
                return ["ret", rng.randint(0, 9)]
            if k < 0.7:
                return ["boom"]
            if k < 0.8:
                return ["base"]
            spawned[0] += 1
            return ["spawn", spawned[0], rng.randrange(n), fs(d + 1)]
        ops = []
        fid = 0
        for _ in range(rng.randint(1, 12)):
            k = rng.random()
            if k < 0.35:
                ops.append(["new", fid, pv(), fs()])
                fid += 1
            else:
                f = rng.randrange(fid + 1)
                ops.append(rng.choice([["call", f], ["detach", f], ["peek", f], ["alive", f],
                                       ["atexit", f], ["set_atexit", f, rng.random() < 0.5],
                                       ["repr", f], ["kill", rng.randrange(n)],
                                       ["kill", rng.randrange(n)], ["exit"]]))
        if rng.random() < 0.5:
            ops.append(["exit"])
        case["ops"] = ops
    return case


def misc_run_wvd(case, objs):
    dead = set()
    def val(p):
        return objs[p[1]] if p[0] == "o" else p[1]
    def isdead(p):
        return p[0] == "o" and p[1] in dead
    def items(l):
        return None if l is None else misc_MappingItems([(k, val(v)) for k, v in l])
    def anydead(l):
        return any(isdead(v) for _, v in (l or []))
    def dump(x):
        return [[k, misc_pv(v)] for k, v in x.items()]
    def res(thunk):
        try:
            return ["ok", thunk()]
        except KeyError as e:
            return ["exc", "KeyError", str(e)]
        except TypeError as e:
            return ["exc", "TypeError", str(e)]
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
            r = "skip" if isdead(op[2]) else res(lambda: d.__setitem__(op[1], val(op[2])))
        elif n == "get_":
            r = res(lambda: misc_pv(d[op[1]]))
        elif n == "del":
            r = res(lambda: d.__delitem__(op[1]))
        elif n == "len":
            r = len(d)
        elif n == "in":
            r = op[1] in d
        elif n == "repr":
            r = repr(d).replace(hex(id(d)), "ADDR")
        elif n == "copy":
            r = res(lambda: dump(d.copy()))
        elif n == "deepcopy":
            r = res(lambda: dump(misc_copy.deepcopy(d)))
        elif n == "get":
            r = "skip" if isdead(op[2]) else misc_pv(d.get(op[1], val(op[2])))
        elif n == "items":
            r = [[k, misc_pv(v)] for k, v in d.items()]
        elif n == "keys":
            r = list(d.keys())
        elif n == "iter":
            r = list(d)
        elif n == "irefs":
            r = [None if x() is None else misc_pv(x()) for x in d.itervaluerefs()]
        elif n == "vrefs":
            r = [None if x() is None else misc_pv(x()) for x in d.valuerefs()]
        elif n == "values":
            r = [misc_pv(v) for v in d.values()]
        elif n == "popitem":
            def f():
                k, v = d.popitem()
                return [k, misc_pv(v)]
            r = res(f)
        elif n == "pop":
            r = "skip" if any(isdead(a) for a in op[2]) else res(lambda: misc_pv(d.pop(op[1], *[val(a) for a in op[2]])))
        elif n == "setdefault":
            r = "skip" if isdead(op[2]) else res(lambda: misc_pv(d.setdefault(op[1], val(op[2]))))
        elif n == "update":
            r = "skip" if anydead(op[1]) else res(lambda: d.update(items(op[1])))
        elif n == "update_pairs":
            r = "skip" if anydead(op[1]) else res(lambda: d.update([(k, val(v)) for k, v in op[1]]))
        elif n == "ior":
            r = "skip" if anydead(op[1]) else res(lambda: (d.__ior__(items(op[1])), None)[1])
        elif n in ("or", "ror"):
            if anydead(op[1]):
                r = "skip"
            else:
                def f():
                    v = getattr(d, "__" + n + "__")(5 if op[1] is None else items(op[1]))
                    return "NotImplemented" if v is NotImplemented else dump(v)
                r = res(f)
                if r == ["ok", "NotImplemented"]:
                    r = "NotImplemented"
        else:
            dead.add(op[1])
            objs.pop(op[1], None)
            r = None
        out.append(r)
    out.append([[k, None if wr() is None else misc_pv(wr())] for k, wr in d.data.items()])
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
    def key(p):
        return objs[p[1]] if p[0] == "o" else p[1]
    def isdead(p):
        return p[0] == "o" and p[1] in dead
    def items(l):
        return None if l is None else misc_MappingItems([(key(k), v) for k, v in l])
    def anydead(l):
        return any(isdead(k) for k, _ in (l or []))
    def dump(x):
        return [[misc_pv(k), v] for k, v in x.items()]
    def res(thunk):
        try:
            return ["ok", thunk()]
        except KeyError as e:
            m = str(e)
            return ["exc", "KeyError", "~" if "weakref" in m else m]
        except TypeError as e:
            return ["exc", "TypeError", str(e)]
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
        elif n == "repr":
            r = repr(d).replace(hex(id(d)), "ADDR")
        elif n == "copy":
            r = res(lambda: dump(d.copy()))
        elif n == "deepcopy":
            r = res(lambda: dump(misc_copy.deepcopy(d)))
        elif n == "get":
            r = res(lambda: d.get(key(op[1]), op[2]))
        elif n == "in":
            r = key(op[1]) in d
        elif n == "items":
            r = [[misc_pv(k), v] for k, v in d.items()]
        elif n == "keys":
            r = [misc_pv(k) for k in d.keys()]
        elif n == "iter":
            r = [misc_pv(k) for k in d]
        elif n == "values":
            r = list(d.values())
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
            if anydead(op[1]):
                r = "skip"
            elif op[2]:
                r = res(lambda: d.update(items(op[1]), a=1))
            else:
                r = res(lambda: d.update(items(op[1])))
        elif n == "update_pairs":
            r = "skip" if anydead(op[1]) else res(lambda: d.update([(key(k), v) for k, v in op[1]]))
        elif n == "ior":
            r = "skip" if anydead(op[1]) else res(lambda: (d.__ior__(items(op[1])), None)[1])
        elif n in ("or", "ror"):
            if anydead(op[1]):
                r = "skip"
            else:
                def f():
                    v = getattr(d, "__" + n + "__")(5 if op[1] is None else items(op[1]))
                    return "NotImplemented" if v is NotImplemented else dump(v)
                r = res(f)
                if r == ["ok", "NotImplemented"]:
                    r = "NotImplemented"
        else:
            dead.add(op[1])
            objs.pop(op[1], None)
            r = None
        out.append(r)
    out.append([[None if k() is None else misc_pv(k()), v] for k, v in d.data.items()])
    return {"ok": out}


def misc_run_wm(case):
    vals = case["vals"]
    objs = {i: MiscW(i, vals[i]) for i in range(4)}
    funcs = {10: (lambda self: None), 11: (lambda self: None)}
    ids = {id(f): i for i, f in funcs.items()}
    ms = []
    fired = []
    out = []
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
            out.append(misc_res(lambda: misc_weakref.WeakMethod(5)))
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
                v = getattr(ms[op[1]], "__" + n + "__")(ms[op[2]])
                out.append(None if v is NotImplemented else v)
        elif n == "eqo":
            if op[1] >= len(ms):
                out.append("skip")
            else:
                v = ms[op[1]].__eq__(5)
                out.append(None if v is NotImplemented else v)
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
    del o
    assert log == [r]
    return {"ok": [r.key, first, None if r() is None else misc_pv(r())]}


def misc_run_fin(case):
    fin = misc_weakref.finalize
    saved = dict(fin._registry), fin._shutdown, fin._dirty
    fin._registry.clear()
    fin._shutdown = False
    fin._dirty = False
    vals = case["vals"]
    objs = {i: MiscW(i, vals[i]) for i in range(4)}
    fs = {}
    log = []
    hook_saved = sys.excepthook
    def hook(t, v, tb):
        log.append(["hook", t.__name__, str(v)])
    sys.excepthook = hook
    spec = {}

    def mk(s):
        def f():
            log.append(["run", s])
            if s[0] == "ret":
                return s[1]
            if s[0] == "boom":
                raise ValueError("boom")
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
            if n == "new":
                p = op[2]
                if p[0] == "o" and p[1] not in objs:
                    out.append("skip")
                    continue
                o = objs[p[1]] if p[0] == "o" else p[1]
                def build():
                    fs[op[1]] = fin(o, mk(op[3]))
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
                            "atexit": False, "set_atexit": None,
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
                f.atexit = op[2]
                out.append(None)
            else:
                t = f.peek()
                r = repr(f).replace(hex(id(f)), "ADDR")
                if t is not None:
                    r = r.replace(hex(id(t[0])), "OBJ")
                del t
                out.append(r)
        reg = [next(k for k, v in fs.items() if v is f2) for f2 in fin._registry]
        r = [out, log, reg, fin._shutdown, fin._dirty]
    finally:
        fin._registry.clear()
        fin._registry.update(saved[0])
        fin._shutdown, fin._dirty = saved[1], saved[2]
        sys.excepthook = hook_saved
    return {"ok": r}


def misc_run_weakref(case):
    k = case["k"]
    if k in ("wvd", "wkd"):
        objs = {i: MiscW(i, case["vals"][i]) for i in range(4)}
        return misc_run_wvd(case, objs) if k == "wvd" else misc_run_wkd(case, objs)
    if k == "wm":
        return misc_run_wm(case)
    if k == "keyed":
        return misc_run_keyed(case)
    return misc_run_fin(case)


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
calstat_ANSI = calstat_types.SimpleNamespace(BLACK="\x1b[30m", BACKGROUND_YELLOW="\x1b[43m",
                                             RESET="\x1b[0m")
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
             "h.formatmonthname", "h.formatmonth", "h.formatyear", "h.formatyearpage",
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
    saved = calstat_colorize.get_colors
    calstat_colorize.get_colors = lambda **k: calstat_ANSI

    def thunk():
        return calstat_lists(calstat_run_cal_inner(c, fn))
    try:
        r = py_result(thunk)
    except BaseException:
        raise
    finally:
        calstat_colorize.get_colors = saved
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
           "s.mean", "s.mean", "s.fmean", "s.fmean", "s.geometric_mean", "s.harmonic_mean", "s.harmonic_mean", "s.median", "s.median_low",
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
    elif fn == "s._mean_stdev":
        c["data"] = calstat_data(rng, calstat_NUMMIX)
    elif fn == "s._sqrtprod":
        pool = [0.0, 1.0, 2.0, 1e308, 1e-308, 5e-324, 1e200, 1e-200, 3.0, calstat_math.inf, float("nan")]
        c["x"] = calstat_fstr(rng.choice(pool + [rng.uniform(0, 10)]))
        c["y"] = calstat_fstr(rng.choice(pool + [rng.uniform(0, 10)]))
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
        if fn == "s.correlation":
            c["method"] = rng.choice(["linear", "linear", "ranked", "ranked", "bogus"])
        if fn == "s.linear_regression":
            c["proportional"] = rng.random() < 0.4
    elif fn == "s.quantiles":
        c["data"] = calstat_data(rng, calstat_NUMMIX + [["str"], ["dec"]], 12)
        c["n"] = rng.choice([1, 2, 3, 4, 4, 5, 7, 10, 20, 0, -1])
        c["method"] = rng.choice(["exclusive", "exclusive", "inclusive", "inclusive", "bogus"])
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
