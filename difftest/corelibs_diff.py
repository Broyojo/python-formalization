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
