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


def gen_bytes(rng):
    return None


def run_bytes(case):
    raise NotImplementedError(case["fn"])


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
