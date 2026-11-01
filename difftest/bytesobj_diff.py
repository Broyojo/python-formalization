"""Differential test: Lean model of tuple, list, bytes, bytearray and memoryview
vs. the running CPython.

Usage: python3 difftest/bytesobj_diff.py [--cases N] [--seed S] [--family F]

Each family below supplies `gen_<family>(rng)` and `run_<family>(case)`. Cases
carry "mod": "bytesobj" and a `fn` starting with the family prefix.
"""

import ctypes
import gc
import operator
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
#
# Elements are ints, tuples, or `El` instances (see lean/PyLean/BytesObj/Seq/Diff.lean,
# which documents the kinds). `TARGET` is the list a side-effecting element acts on.
# The collector is off, so `gc.is_tracked` only shows what the constructors decide.

gc.disable()

M = sys.maxsize
BIG = 2000              # largest repeat result the generator lets CPython allocate
ALLOC_LIMIT = M // 8    # past this the C code raises MemoryError by its own checks
TARGET = [None]
STOP = object()
EMPTY = ()


class Weird:
    def __bool__(self):
        raise TypeError("weird")


class TS(tuple):
    pass


class El:
    def __init__(self, kind, id_):
        self.kind, self.id, self.calls = kind, id_, 0

    def _effect(self):
        t, k = TARGET[0], self.kind
        if t is None:
            return
        if k == "pop":
            if t:
                t.pop()
        elif k == "clear":
            t.clear()
        elif k == "add":
            if len(t) < 12:
                t.append(0)

    def _cmp(self, res):
        if self.kind == "bad":
            raise ValueError("bad")
        self._effect()
        return Weird() if self.kind == "weird" else res

    def __eq__(self, other):
        return self._cmp(False)

    def __ne__(self, other):
        return self._cmp(True)

    def __lt__(self, other):
        return self._cmp(False)

    def __le__(self, other):
        return self._cmp(False)

    def __gt__(self, other):
        return self._cmp(False)

    def __ge__(self, other):
        return self._cmp(False)

    def __hash__(self):
        self.calls += 1
        if self.kind == "bad":
            raise ValueError("badhash")
        if self.kind == "cnt":
            return 100 * self.calls + self.id
        if self.kind == "flaky":
            if self.calls == 1:
                raise ValueError("flaky")
            return 5
        return 1000 + self.id

    def __repr__(self):
        if self.kind == "bad":
            raise ValueError("badrepr")
        self._effect()
        return f"<{self.kind}{self.id}>"


def _display(n):
    names = [f"a{i}" for i in range(n)]
    return eval(f"lambda {', '.join(names)}: [{', '.join(names)}]")


DISPLAY = {n: _display(n) for n in range(40)}


class Reg:
    """One object per (kind, id) within a case, so that identity means something."""

    def __init__(self):
        self.objs = {}

    def mk(self, x):
        if isinstance(x, dict):
            return self.objs.setdefault((x["k"], x["id"]), El(x["k"], x["id"]))
        if isinstance(x, list):
            return tuple(self.mk(e) for e in x)
        return x

    def mks(self, xs):
        return [self.mk(x) for x in xs]


def enc(x):
    if isinstance(x, El):
        return {"k": x.kind, "id": x.id}
    if isinstance(x, tuple):
        return [enc(e) for e in x]
    return x


def encs(xs):
    return [enc(x) for x in xs]


def enc_state(o):
    return [encs(o), o.__sizeof__()]


def as_slice(s):
    return slice(s[0], s[1], s[2])


def enc_res(r):
    return "weird" if isinstance(r, Weird) else r


class Hinted:
    """An iterable with `__length_hint__`, which may raise."""

    def __init__(self, items, hint, err):
        self.items, self.hint, self.err = items, hint, err

    def __iter__(self):
        return gen_items(self.items, self.err)

    def __length_hint__(self):
        if self.hint == "raise":
            raise ValueError("hint")
        return self.hint


def gen_items(items, err):
    yield from items
    if err:
        raise ValueError("gen")


def build_ext(arg, reg, self_list):
    k = arg["k"]
    if k == "self":
        return self_list
    if k == "noniter":
        return 5
    if k == "fast":
        items = reg.mks(arg["items"])
        return tuple(items) if arg["as"] == "tuple" else DISPLAY[len(items)](*items)
    if k == "sized":
        src = arg["src"]
        return {"set": lambda: set(src), "frozenset": lambda: frozenset(src),
                "dict": lambda: dict.fromkeys(src, 1), "keys": lambda: dict.fromkeys(src, 1).keys(),
                "values": lambda: {i: v for i, v in enumerate(src)}.values(),
                "items": lambda: dict.fromkeys(src, 1).items()}[arg["as"]]()
    items = reg.mks(arg["items"])
    if arg["hint"] is None:
        return gen_items(items, arg.get("err", False))
    return Hinted(items, arg["hint"], arg.get("err", False))


def list_op(l, op, reg):
    name = op[0]
    if name == "append":
        return l.append(reg.mk(op[1]))
    if name == "insert":
        return l.insert(op[1], reg.mk(op[2]))
    if name == "pop":
        return enc(l.pop(*op[1:]))
    if name == "remove":
        return l.remove(reg.mk(op[1]))
    if name == "index":
        return l.index(reg.mk(op[1]), 0 if op[2] is None else op[2], M if op[3] is None else op[3])
    if name == "count":
        return l.count(reg.mk(op[1]))
    if name == "contains":
        return operator.contains(l, reg.mk(op[1]))
    if name == "repr":
        return repr(l)
    if name == "clear":
        return l.clear()
    if name == "copy":
        return enc_state(l.copy())
    if name == "reverse":
        return l.reverse()
    if name == "getitem":
        return enc(operator.getitem(l, op[1]))
    if name == "getslice":
        return enc_state(operator.getitem(l, as_slice(op[1])))
    if name == "setitem":
        return operator.setitem(l, op[1], reg.mk(op[2]))
    if name == "delitem":
        return operator.delitem(l, op[1])
    if name == "setslice":
        return operator.setitem(l, as_slice(op[1]), tuple(reg.mks(op[2])))
    if name == "setslice_self":
        return operator.setitem(l, as_slice(op[1]), l)
    if name == "setslice_bad":
        return operator.setitem(l, as_slice(op[1]), 5)
    if name == "delslice":
        return operator.delitem(l, as_slice(op[1]))
    if name == "imul":
        operator.imul(l, op[1])
        return None
    if name == "mul":
        return enc_state(operator.mul(l, op[1]))
    if name == "add":
        return enc_state(operator.add(l, reg.mks(op[1])))
    if name == "add_bad":
        return enc_state(operator.add(l, ()))
    if name == "extend":
        return l.extend(build_ext(op[1], reg, l))
    if name == "iadd":
        operator.iadd(l, build_ext(op[1], reg, l))
        return None
    if name == "init":
        return l.__init__() if op[1] is None else l.__init__(build_ext(op[1], reg, l))
    raise ValueError(name)


def run_list_ops(c):
    reg = Reg()
    TARGET[0] = None
    items = reg.mks(c["init"]["items"])
    how = c["init"]["how"]
    if how == "display":
        l = DISPLAY[len(items)](*items)
    elif how == "tuple":
        l = list(tuple(items))
    else:
        l = list(x for x in items)
    TARGET[0] = l
    out = []
    for op in c["ops"]:
        r = common.py_result(lambda: list_op(l, op, reg))
        out.append([r, enc_state(l)])
    TARGET[0] = None
    return {"ok": out}


def iter_op(it, op, l):
    name = op[0]
    if name == "next":
        x = next(it, STOP)
        return "stop" if x is STOP else enc(x)
    if name == "hint":
        return it.__length_hint__()
    if name == "refs":
        return len(gc.get_referents(it))
    if name == "reduce":
        r = it.__reduce__()
        return [encs(r[1][0]), r[2] if len(r) > 2 else None]
    if name == "setstate":
        return it.__setstate__(op[1])
    if name == "pop":
        if l:
            l.pop()
        return None
    if name == "add":
        return l.append(0)
    if name == "clear":
        return l.clear()
    raise ValueError(name)


def run_list_iter(c):
    reg = Reg()
    TARGET[0] = None
    l = reg.mks(c["items"])
    it = iter(l) if c["forward"] else reversed(l)
    out = []
    for op in c["ops"]:
        out.append([common.py_result(lambda: iter_op(it, op, l)), encs(l)])
    return {"ok": out}


def run_tuple_iter(c):
    reg = Reg()
    t = tuple(reg.mks(c["items"]))
    it = iter(t)
    out = []
    for op in c["ops"]:
        out.append(common.py_result(lambda: iter_op(it, op, None)))
    return {"ok": out}


def mk_tuple(d, reg):
    items = reg.mks(d["items"])
    return TS(items) if d.get("sub") else tuple(items)


def out_tuple(res, a=None, b=None):
    if res is EMPTY:
        return {"r": "empty", "items": [], "tracked": False}
    who = "arg0" if res is a else "arg1" if res is b else "fresh"
    return {"r": who, "items": encs(res), "tracked": gc.is_tracked(res)}


def mk_src(s, reg):
    items = reg.mks(s["items"])
    return {"tuple": lambda: tuple(items), "list": lambda: list(items),
            "iter": lambda: (x for x in items)}[s["k"]]()


SIZE = ctypes.c_ssize_t
OBJ = ctypes.py_object
VOID = ctypes.c_void_p


def cfn(name, restype, *argtypes):
    f = getattr(ctypes.PyDLL(None), name)
    f.restype, f.argtypes = restype, list(argtypes)
    return f


T_SIZE = cfn("PyTuple_Size", SIZE, OBJ)
T_GETITEM = cfn("PyTuple_GetItem", VOID, OBJ, SIZE)
T_GETITEM_R = cfn("PyTuple_GetItem", VOID, VOID, SIZE)
T_SETITEM = cfn("PyTuple_SetItem", ctypes.c_int, VOID, SIZE, VOID)
T_SETITEM_O = cfn("PyTuple_SetItem", ctypes.c_int, OBJ, SIZE, VOID)
T_NEW = cfn("PyTuple_New", OBJ, SIZE)
T_NEW_R = cfn("PyTuple_New", VOID, SIZE)
T_SLICE = cfn("PyTuple_GetSlice", OBJ, OBJ, SIZE, SIZE)
T_RESIZE = cfn("_PyTuple_Resize", ctypes.c_int, ctypes.POINTER(VOID), SIZE)
T_PACK = getattr(ctypes.PyDLL(None), "PyTuple_Pack")
T_PACK.restype = OBJ
L_NEW = cfn("PyList_New", OBJ, SIZE)
L_SIZE = cfn("PyList_Size", SIZE, OBJ)
L_GETITEM = cfn("PyList_GetItem", VOID, OBJ, SIZE)
L_GETITEMREF = cfn("PyList_GetItemRef", OBJ, OBJ, SIZE)
L_SETITEM = cfn("PyList_SetItem", ctypes.c_int, OBJ, SIZE, VOID)
L_INSERT = cfn("PyList_Insert", ctypes.c_int, OBJ, SIZE, VOID)
L_APPEND = cfn("PyList_Append", ctypes.c_int, OBJ, VOID)
L_GETSLICE = cfn("PyList_GetSlice", OBJ, OBJ, SIZE, SIZE)
L_SETSLICE = cfn("PyList_SetSlice", ctypes.c_int, OBJ, SIZE, SIZE, VOID)
L_EXTEND = cfn("PyList_Extend", ctypes.c_int, OBJ, OBJ)
L_CLEAR = cfn("PyList_Clear", ctypes.c_int, OBJ)
L_REVERSE = cfn("PyList_Reverse", ctypes.c_int, OBJ)
L_ASTUPLE = cfn("PyList_AsTuple", OBJ, OBJ)
INCREF = cfn("Py_IncRef", None, VOID)


def new_ref(x):
    p = id(x)
    INCREF(p)
    return p


def from_ptr(p):
    return ctypes.cast(p, OBJ).value


def tuple_raw(items):
    """A tuple only `p` refers to, so that it is uniquely referenced."""
    p = T_NEW_R(len(items))
    for i, x in enumerate(items):
        T_SETITEM(p, i, new_ref(x))
    return p


def tuple_c_setitem(c, reg):
    x = reg.mk(c["x"])
    if c["items"] == "x":
        return T_SETITEM_O(5, c["i"], new_ref(x))
    items = reg.mks(c["items"])
    if c["unique"]:
        p = tuple_raw(items)
        T_SETITEM(p, c["i"], new_ref(x))
        return encs(from_ptr(p))
    t = tuple(items)
    T_SETITEM_O(t, c["i"], new_ref(x))
    return encs(t)


def tuple_c_resize(c, reg):
    p = VOID(tuple_raw(reg.mks(c["items"])))
    T_RESIZE(ctypes.byref(p), c["n"])
    n = T_SIZE(from_ptr(p.value))
    out = []
    for i in range(n):
        q = T_GETITEM_R(p.value, i)
        out.append(None if q is None else enc(from_ptr(q)))
    return out


def tuple_untrack(c, reg):
    t = tuple(x for x in reg.mks(c["items"]))
    gc.collect()
    return gc.is_tracked(t)


def tuple_case(c):
    fn, reg = c["fn"], Reg()
    TARGET[0] = None
    items = lambda: reg.mks(c["items"])
    if fn == "tuple.hash":
        t = mk_tuple(c["t"], reg)
        return common.py_result(lambda: hash(t))
    if fn == "tuple.hash2":
        t = mk_tuple(c["t"], reg)
        return {"ok": [common.py_result(lambda: hash(t)), common.py_result(lambda: hash(t))]}
    if fn == "tuple.repr":
        t = tuple(items())
        return common.py_result(lambda: repr(t))
    if fn == "tuple.getitem":
        t = tuple(items())
        return common.py_result(lambda: enc(operator.getitem(t, c["i"])))
    if fn == "tuple.getslice":
        t = mk_tuple(c["t"], reg)
        return common.py_result(lambda: out_tuple(operator.getitem(t, as_slice(c["s"])), t))
    if fn == "tuple.add":
        a = mk_tuple(c["a"], reg)
        if "other" in c:
            return common.py_result(lambda: out_tuple(operator.add(a, []), a))
        b = mk_tuple(c["b"], reg)
        return common.py_result(lambda: out_tuple(operator.add(a, b), a, b))
    if fn == "tuple.mul":
        t = mk_tuple(c["t"], reg)
        return common.py_result(lambda: out_tuple(operator.mul(t, c["n"]), t))
    if fn == "tuple.index":
        t = tuple(items())
        x = reg.mk(c["x"])
        start = 0 if c["start"] is None else c["start"]
        stop = M if c["stop"] is None else c["stop"]
        return common.py_result(lambda: t.index(x, start, stop))
    if fn == "tuple.count":
        t = tuple(items())
        return common.py_result(lambda: t.count(reg.mk(c["x"])))
    if fn == "tuple.contains":
        t = tuple(items())
        return common.py_result(lambda: operator.contains(t, reg.mk(c["x"])))
    if fn == "tuple.cmp":
        a, b = tuple(reg.mks(c["a"])), tuple(reg.mks(c["b"]))
        return common.py_result(lambda: enc_res(getattr(operator, c["op"])(a, b)))
    if fn == "tuple.new":
        s = mk_src(c["src"], reg)
        return common.py_result(lambda: out_tuple(tuple(s), s))
    if fn == "tuple.sub_new":
        s = mk_src(c["src"], reg)
        return common.py_result(lambda: (lambda r: [encs(r), type(r) is tuple])(TS(s)))
    if fn == "tuple.call":
        args = [()] * c["nargs"]
        kw = {f"k{i}": 1 for i in range(c["nkw"])}
        return common.py_result(lambda: (tuple(*args, **kw), None)[1])
    if fn == "tuple.getnewargs":
        t = mk_tuple(c["t"], reg)
        return common.py_result(lambda: out_tuple(t.__getnewargs__()[0], t))
    if fn == "tuple.iter":
        return run_tuple_iter(c)
    if fn == "tuple.referents":
        return {"ok": encs(gc.get_referents(tuple(items())))}
    if fn == "tuple.release":
        return {"ok": release_order(tuple, c["n"])}
    if fn == "tuple.c_size":
        o = 5 if c["items"] == "x" else tuple(items())
        return common.py_result(lambda: T_SIZE(o))
    if fn == "tuple.c_getitem":
        o = 5 if c["items"] == "x" else tuple(items())
        return common.py_result(lambda: enc(from_ptr(T_GETITEM(o, c["i"]))))
    if fn == "tuple.c_setitem":
        return common.py_result(lambda: tuple_c_setitem(c, reg))
    if fn == "tuple.c_getslice":
        t = tuple(items())
        return common.py_result(lambda: out_tuple(T_SLICE(t, c["i"], c["j"]), t))
    if fn == "tuple.c_new":
        return common.py_result(lambda: len(T_NEW(c["n"])))
    if fn == "tuple.c_pack":
        xs = items()
        return common.py_result(lambda: out_tuple(T_PACK(SIZE(len(xs)), *[OBJ(x) for x in xs])))
    if fn == "tuple.c_resize":
        return common.py_result(lambda: tuple_c_resize(c, reg))
    if fn == "tuple.untrack":
        return common.py_result(lambda: tuple_untrack(c, reg))
    raise ValueError(fn)


def heap_build(cells):
    objs = [[] if cell["list"] else None for cell in cells]

    def item(x):
        return int(x) if isinstance(x, str) else objs[x]

    for i, cell in enumerate(cells):
        if not cell["list"]:
            objs[i] = tuple(item(x) for x in cell["items"])
    for i, cell in enumerate(cells):
        if cell["list"]:
            objs[i].extend(item(x) for x in cell["items"])
    return objs


class Finalized:
    def __init__(self, i, log):
        self.i, self.log = i, log

    def __del__(self):
        self.log.append(self.i)


def release_order(make, n):
    """The order finalizers run in when a container of `n` items dies."""
    log = []
    o = make([Finalized(i, log) for i in range(n)])
    del o
    return log


def sizes_in_sort():
    seen = []
    l = [3, 2, 1]
    l.sort(key=lambda x: (seen.append(l.__sizeof__()), x)[1])
    return seen[0]


def list_case(c):
    fn, reg = c["fn"], Reg()
    TARGET[0] = None
    items = lambda: reg.mks(c["items"])
    obj = lambda: 5 if c["items"] == "x" else DISPLAY[len(c["items"])](*items())
    if fn == "list.ops":
        return run_list_ops(c)
    if fn == "list.iter":
        return run_list_iter(c)
    if fn == "list.cmp":
        a, b = reg.mks(c["a"]), reg.mks(c["b"])
        TARGET[0] = a
        r = common.py_result(lambda: enc_res(getattr(operator, c["op"])(a, b)))
        TARGET[0] = None
        return {"ok": [r, encs(a)]}
    if fn == "list.repr":
        objs = heap_build(c["heap"])
        return common.py_result(lambda: repr(objs[c["root"]]))
    if fn == "list.call":
        args = [()] * c["nargs"]
        kw = {f"k{i}": 1 for i in range(c["nkw"])}
        return common.py_result(lambda: (list(*args, **kw), None)[1])
    if fn == "list.referents":
        return {"ok": encs(gc.get_referents(items()))}
    if fn == "list.release":
        return {"ok": release_order(list, c["n"])}
    if fn == "list.sort_sizeof":
        return {"ok": sizes_in_sort()}
    if fn == "list.latin_lt":
        v, w = "".join(map(chr, c["v"])), "".join(map(chr, c["w"]))
        return {"ok": [v < w, v < w]}
    if fn == "list.tuple_sort":
        return {"ok": [list(k) for k in sorted(tuple(k) for k in c["keys"])]}
    if fn == "list.c_size":
        o = obj()
        return common.py_result(lambda: L_SIZE(o))
    if fn == "list.c_getitem":
        o = obj()
        return common.py_result(lambda: enc(from_ptr(L_GETITEM(o, c["i"]))))
    if fn == "list.c_getitemref":
        o = obj()
        return common.py_result(lambda: enc(L_GETITEMREF(o, c["i"])))
    if fn == "list.c_setitem":
        o, x = obj(), reg.mk(c["x"])
        return common.py_result(lambda: (L_SETITEM(o, c["i"], new_ref(x)), enc_state(o))[1])
    if fn == "list.c_insert":
        o = obj()
        x = None if "null" in c else id(reg.mk(c["x"]))
        return common.py_result(lambda: (L_INSERT(o, c["i"], x), enc_state(o))[1])
    if fn == "list.c_append":
        o = obj()
        x = None if "null" in c else id(reg.mk(c["x"]))
        return common.py_result(lambda: (L_APPEND(o, x), enc_state(o))[1])
    if fn == "list.c_getslice":
        o = obj()
        return common.py_result(lambda: enc_state(L_GETSLICE(o, c["i"], c["j"])))
    if fn == "list.c_setslice":
        o = obj()
        v = o if c["self"] else None if c["v"] == "x" else DISPLAY[len(c["v"])](*reg.mks(c["v"]))
        return common.py_result(lambda: (L_SETSLICE(o, c["i"], c["j"], None if v is None else id(v)), enc_state(o))[1])
    if fn == "list.c_clear":
        o = obj()
        return common.py_result(lambda: (L_CLEAR(o), enc_state(o))[1])
    if fn == "list.c_reverse":
        o = obj()
        return common.py_result(lambda: (L_REVERSE(o), enc_state(o))[1])
    if fn == "list.c_astuple":
        o = obj()
        return common.py_result(lambda: out_tuple(L_ASTUPLE(o)))
    if fn == "list.c_new":
        return common.py_result(lambda: (lambda r: [len(r), r.__sizeof__()])(L_NEW(c["n"])))
    if fn == "list.c_extend":
        o = obj()
        return common.py_result(lambda: (L_EXTEND(o, build_ext(c["arg"], reg, o)), enc_state(o))[1])
    raise ValueError(fn)


def seq_edge(rng, n):
    return rng.choice([0, 1, -1, 2, -2, n, -n, n - 1, -n - 1, n + 1, -n + 1,
                       rng.randint(-n - 3, n + 3), rng.randint(-n - 3, n + 3),
                       M, -M, -M - 1, M + 1, -M - 2, 2 ** 64, -2 ** 64, 2 ** 64 - 1,
                       2 ** 62, -2 ** 62, 10 ** 30, -10 ** 30])


def seq_edge_c(rng, n):
    """An index that fits `Py_ssize_t`, for the C API."""
    return rng.choice([0, 1, -1, 2, n, -n, n - 1, -n - 1, n + 1, M, -M, -M - 1,
                       rng.randint(-n - 3, n + 3), rng.randint(-n - 3, n + 3)])


def seq_elem(rng, kinds=("nan", "bad", "weird")):
    r = rng.random()
    if r < 0.8:
        return rng.randint(0, 4)
    if r < 0.85:
        return rng.choice([2 ** 31, -2 ** 31, 2 ** 61 - 1, 2 ** 61, -(2 ** 61) + 1, 2 ** 63, -1, -2, 10 ** 30])
    return {"k": rng.choice(kinds), "id": rng.randint(0, 2)}


def seq_items(rng, maxlen=8, kinds=("nan", "bad", "weird")):
    n = rng.choice([0, 0, 1, 1, 2, 3, rng.randint(0, maxlen)])
    if rng.random() < 0.4:
        return [rng.randint(0, 3) for _ in range(n)]
    return [seq_elem(rng, kinds) for _ in range(n)]


def seq_slice(rng, n):
    def part():
        return None if rng.random() < 0.3 else seq_edge(rng, n)
    step = None if rng.random() < 0.35 else rng.choice(
        [1, 1, 2, -1, -2, 3, -3, 0, n + 1, -n - 1, M, -M, -M - 1, M + 1, -M - 2, 2 ** 64, -2 ** 64])
    return [part(), part(), step]


def fits(size, n):
    """Is `size * n` small, or rejected by an explicit check in the C code?"""
    return size == 0 or n <= 1 or size * n <= BIG or size * n > ALLOC_LIMIT


def seq_count(rng, size):
    while True:
        n = rng.choice([0, 1, -1, 2, 3, 5, M, -M, M + 1, -M - 2, 2 ** 64, 10 ** 30,
                        2 ** 60, 2 ** 61, 2 ** 62, M // 2, M // 3 + 1, M // max(size, 1) + 1,
                        ALLOC_LIMIT // max(size, 1) + 1])
        if n > M or n < -M - 1 or fits(size, n):
            return n


def seq_tup(rng, maxlen=6, kinds=("nan", "bad", "weird")):
    return {"items": seq_items(rng, maxlen, kinds), "sub": rng.random() < 0.2}


def gen_ext(rng, allow_self=True):
    k = rng.choice(["fast", "fast", "sized", "iter", "iter", "iter", "noniter"] + (["self"] if allow_self else []))
    if k == "self" or k == "noniter":
        return {"k": k}
    if k == "fast":
        return {"k": k, "items": seq_items(rng, 20), "as": rng.choice(["list", "tuple"])}
    if k == "sized":
        how = rng.choice(["set", "frozenset", "dict", "keys", "values", "items"])
        src = [rng.randint(0, 30) for _ in range(rng.randint(0, 12))]
        order = {"set": lambda: list(set(src)), "frozenset": lambda: list(frozenset(src)),
                 "dict": lambda: list(dict.fromkeys(src)), "keys": lambda: list(dict.fromkeys(src)),
                 "values": lambda: src, "items": lambda: [[k, 1] for k in dict.fromkeys(src)]}[how]()
        return {"k": k, "as": how, "src": src, "items": order}
    hint = rng.choice([None, None, 0, 1, 2, 3, 8, 20, 100, 1000, "raise", -1, M, M - 1, M - 2,
                       M + 1, 2 ** 60, 2 ** 61, ALLOC_LIMIT + 1, ALLOC_LIMIT + 2])
    return {"k": k, "hint": hint, "items": seq_items(rng, 30), "err": rng.random() < 0.15}


def gen_list_op(rng, n):
    kinds = ("nan", "bad", "weird", "pop", "clear", "add")
    e = lambda: seq_elem(rng, kinds)
    k = rng.randrange(26)
    if k <= 3:
        return ["append", e()]
    if k == 4:
        return ["insert", seq_edge(rng, n), e()]
    if k == 5:
        return ["pop"] + ([] if rng.random() < 0.5 else [seq_edge(rng, n)])
    if k == 6:
        return ["remove", e()]
    if k == 7:
        return ["index", e(), rng.choice([None, seq_edge(rng, n)]), rng.choice([None, seq_edge(rng, n)])]
    if k == 8:
        return ["count", e()]
    if k == 9:
        return ["contains", e()]
    if k == 10:
        return ["repr"]
    if k == 11:
        return [rng.choice(["clear", "copy", "reverse"])]
    if k == 12:
        return ["getitem", seq_edge(rng, n)]
    if k == 13:
        return ["getslice", seq_slice(rng, n)]
    if k == 14:
        return ["setitem", seq_edge(rng, n), e()]
    if k == 15:
        return ["delitem", seq_edge(rng, n)]
    if k == 16:
        return ["setslice", seq_slice(rng, n), seq_items(rng, 10)]
    if k == 17:
        return [rng.choice(["setslice_self", "setslice_bad"]), seq_slice(rng, n)]
    if k <= 19:
        return ["delslice", seq_slice(rng, n)]
    if k == 20:
        return ["imul", seq_count(rng, n)]
    if k == 21:
        return ["mul", seq_count(rng, n)]
    if k == 22:
        return ["add", seq_items(rng, 6)] if rng.random() < 0.8 else ["add_bad", "tuple"]
    if k <= 24:
        return [rng.choice(["extend", "iadd"]), gen_ext(rng)]
    return ["init", None if rng.random() < 0.3 else gen_ext(rng)]


def gen_ops(rng):
    """Each op is chosen against a shadow of the list, so that a repeat count is
    judged on the size the list really has when the op runs."""
    items = seq_items(rng, 24)
    how = rng.choice(["display", "tuple", "gen"])
    reg = Reg()
    shadow = reg.mks(items)
    TARGET[0] = shadow
    ops = []
    for _ in range(rng.randint(1, 8)):
        op = gen_list_op(rng, len(shadow))
        ops.append(op)
        common.py_result(lambda: list_op(shadow, op, reg))
    TARGET[0] = None
    return {"mod": "bytesobj", "fn": "list.ops", "init": {"how": how, "items": items}, "ops": ops}


def gen_iter(rng):
    items = [rng.randint(0, 3) for _ in range(rng.randint(0, 6))]
    n = len(items)

    def op():
        k = rng.choice(["next", "next", "next", "hint", "refs", "reduce", "setstate", "pop", "add", "clear"])
        return [k, rng.choice([0, 1, -1, -2, n, n + 1, n - 1, M, -M - 1, M + 1, 2 ** 64])] if k == "setstate" else [k]
    return {"mod": "bytesobj", "fn": "list.iter", "items": items, "forward": rng.random() < 0.5,
            "ops": [op() for _ in range(rng.randint(1, 12))]}


def gen_tuple_iter(rng):
    items = [rng.randint(0, 3) for _ in range(rng.randint(0, 6))]
    n = len(items)

    def op():
        k = rng.choice(["next", "next", "next", "hint", "refs", "reduce", "setstate"])
        return [k, rng.choice([0, 1, -1, n, n + 1, n - 1, M, -M - 1, M + 1])] if k == "setstate" else [k]
    return {"mod": "bytesobj", "fn": "tuple.iter", "items": items,
            "ops": [op() for _ in range(rng.randint(1, 10))]}


def gen_heap(rng):
    n = rng.randint(1, 6)
    cells = []
    for i in range(n):
        is_list = rng.random() < 0.7
        items = []
        for _ in range(rng.randint(0, 3)):
            refs = list(range(n)) if is_list else list(range(i))
            if rng.random() < 0.4 or not refs:
                items.append(str(rng.randint(0, 9)))
            else:
                items.append(rng.choice(refs))
        cells.append({"list": is_list, "items": items})
    return {"mod": "bytesobj", "fn": "list.repr", "heap": cells, "root": rng.randrange(n)}


def gen_capi_tuple(rng):
    case = {"mod": "bytesobj"}
    items = seq_items(rng)
    n = len(items)
    which = rng.randrange(7)
    x = seq_elem(rng)
    if which == 0:
        return {**case, "fn": "tuple.c_size", "items": rng.choice([items, "x"])}
    if which == 1:
        return {**case, "fn": "tuple.c_getitem", "items": rng.choice([items, "x"]), "i": seq_edge_c(rng, n)}
    if which == 2:
        return {**case, "fn": "tuple.c_setitem", "items": rng.choice([items, "x"]) if n else items,
                "unique": n > 0 and rng.random() < 0.7, "i": seq_edge_c(rng, n), "x": x}
    if which == 3:
        return {**case, "fn": "tuple.c_getslice", "items": items, "i": seq_edge_c(rng, n), "j": seq_edge_c(rng, n)}
    if which == 4:
        return {**case, "fn": "tuple.c_new", "n": rng.choice([0, 1, 2, 7, 25, 1000, -1, -M - 1, ALLOC_LIMIT + 1, M])}
    if which == 5 or not n:
        return {**case, "fn": "tuple.c_pack", "items": items}
    return {**case, "fn": "tuple.c_resize", "items": [e for e in items if not isinstance(e, dict)] or [1],
            "n": rng.randint(0, n + 3)}


def gen_capi_list(rng):
    case = {"mod": "bytesobj"}
    items = seq_items(rng, 10)
    n = len(items)
    o = rng.choice([items, items, items, items, "x"])
    which = rng.randrange(14)
    x = seq_elem(rng)
    extra = {"null": 1} if rng.random() < 0.15 else {}
    if which == 0:
        return {**case, "fn": "list.c_size", "items": o}
    if which == 1:
        return {**case, "fn": "list.c_getitem", "items": o, "i": seq_edge_c(rng, n)}
    if which == 2:
        return {**case, "fn": "list.c_getitemref", "items": o, "i": seq_edge_c(rng, n)}
    if which == 3:
        return {**case, "fn": "list.c_setitem", "items": o, "i": seq_edge_c(rng, n), "x": x}
    if which == 4:
        return {**case, "fn": "list.c_insert", "items": o, "i": seq_edge_c(rng, n), "x": x, **extra}
    if which == 5:
        return {**case, "fn": "list.c_append", "items": o, "x": x, **extra}
    if which == 6:
        return {**case, "fn": "list.c_getslice", "items": o, "i": seq_edge_c(rng, n), "j": seq_edge_c(rng, n)}
    if which == 7:
        return {**case, "fn": "list.c_setslice", "items": o, "i": seq_edge_c(rng, n), "j": seq_edge_c(rng, n),
                "v": rng.choice(["x", seq_items(rng, 6), seq_items(rng, 6)]), "self": o != "x" and rng.random() < 0.2}
    if which == 8:
        return {**case, "fn": "list.c_clear", "items": o}
    if which == 9:
        return {**case, "fn": "list.c_reverse", "items": o}
    if which == 10:
        return {**case, "fn": "list.c_astuple", "items": o}
    if which == 11:
        return {**case, "fn": "list.c_new", "n": rng.choice([0, 1, 2, 7, 1000, -1, -M - 1, ALLOC_LIMIT + 1, M])}
    return {**case, "fn": "list.c_extend", "items": o, "arg": gen_ext(rng, allow_self=False)}


def gen_seq(rng):
    k = rng.randrange(50)
    case = {"mod": "bytesobj"}
    if k < 16:
        return gen_ops(rng)
    if k < 19:
        return gen_iter(rng)
    if k == 19:
        return gen_tuple_iter(rng)
    if k == 20:
        return gen_heap(rng)
    if k == 21:
        kinds = ("nan", "bad", "weird", "pop", "clear", "add")
        a = seq_items(rng, 5, kinds)
        b = list(a) if rng.random() < 0.5 else seq_items(rng, 5, kinds)
        return {**case, "fn": "list.cmp", "op": rng.choice(["lt", "le", "eq", "ne", "gt", "ge"]), "a": a, "b": b}
    if k == 22:
        return {**case, "fn": "list.call", "nargs": rng.randint(0, 3), "nkw": rng.randint(0, 1)}
    if k == 23:
        return {**case, "fn": "list.sort_sizeof"}
    if k == 24:
        s = lambda: [rng.choice([0, 1, 2, 65, 200, 255]) for _ in range(rng.randint(0, 4))]
        return {**case, "fn": "list.latin_lt", "v": s(), "w": s()}
    if k == 25:
        keys = [[rng.randint(0, 3) for _ in range(rng.randint(1, 3))] for _ in range(rng.randint(0, 12))]
        return {**case, "fn": "list.tuple_sort", "keys": keys}
    if k == 26:
        return {**case, "fn": "tuple.hash", "t": seq_tup(rng, 6, ("nan", "bad"))}
    if k == 27:
        items = [rng.randint(0, 3) for _ in range(rng.randint(0, 3))]
        items += [{"k": "cnt", "id": i} for i in range(rng.randint(0, 2))]
        if rng.random() < 0.3:
            items.append({"k": "flaky", "id": 0})
        return {**case, "fn": "tuple.hash2", "t": {"items": items}}
    if k == 28:
        return {**case, "fn": "tuple.repr", "items": seq_items(rng, 5)}
    if k == 29:
        items = seq_items(rng)
        return {**case, "fn": "tuple.getitem", "items": items, "i": seq_edge(rng, len(items))}
    if k == 30:
        t = seq_tup(rng)
        return {**case, "fn": "tuple.getslice", "t": t, "s": seq_slice(rng, len(t["items"]))}
    if k == 31:
        if rng.random() < 0.1:
            return {**case, "fn": "tuple.add", "a": seq_tup(rng), "other": "list"}
        return {**case, "fn": "tuple.add", "a": seq_tup(rng), "b": seq_tup(rng)}
    if k == 32:
        t = seq_tup(rng)
        return {**case, "fn": "tuple.mul", "t": t, "n": seq_count(rng, len(t["items"]))}
    if k == 33:
        items = seq_items(rng)
        n = len(items)
        return {**case, "fn": "tuple.index", "items": items, "x": seq_elem(rng),
                "start": rng.choice([None, seq_edge(rng, n)]), "stop": rng.choice([None, seq_edge(rng, n)])}
    if k == 34:
        return {**case, "fn": rng.choice(["tuple.count", "tuple.contains"]), "items": seq_items(rng), "x": seq_elem(rng)}
    if k == 35:
        a = seq_items(rng, 5)
        b = list(a) if rng.random() < 0.5 else seq_items(rng, 5)
        return {**case, "fn": "tuple.cmp", "op": rng.choice(["lt", "le", "eq", "ne", "gt", "ge"]), "a": a, "b": b}
    if k == 36:
        src = {"k": rng.choice(["tuple", "list", "iter"]), "items": seq_items(rng, 14)}
        return {**case, "fn": rng.choice(["tuple.new", "tuple.sub_new"]), "src": src}
    if k == 37:
        return {**case, "fn": "tuple.call", "nargs": rng.randint(0, 3), "nkw": rng.randint(0, 1)}
    if k == 38:
        return {**case, "fn": "tuple.getnewargs", "t": seq_tup(rng)}
    if k == 39:
        return gen_capi_tuple(rng)
    if k == 40:
        items = [rng.randint(0, 3) if rng.random() < 0.9 else {"k": "nan", "id": 0} for _ in range(rng.randint(1, 5))]
        return {**case, "fn": "tuple.untrack", "items": items}
    if k == 41:
        return {**case, "fn": rng.choice(["tuple.referents", "list.referents"]), "items": seq_items(rng)}
    if k == 42:
        return {**case, "fn": rng.choice(["tuple.release", "list.release"]), "n": rng.randint(0, 6)}
    return gen_capi_list(rng)


def run_seq(case):
    if case["fn"].startswith("tuple."):
        return tuple_case(case)
    return list_case(case)


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
