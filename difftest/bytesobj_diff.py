"""Differential test: Lean model of tuple, list, bytes, bytearray and memoryview
vs. the running CPython.

Usage: python3 difftest/bytesobj_diff.py [--cases N] [--seed S] [--family F]

Each family below supplies `gen_<family>(rng)` and `run_<family>(case)`. Cases
carry "mod": "bytesobj" and a `fn` starting with the family prefix.
"""

import builtins
import ctypes
import gc
import itertools
import operator
import sys
import weakref

import common


def choose_family():
    """`--family seq|bytes|mem|bare` restricts the run; the option is removed from argv."""
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


class RevList(list):
    """A list subclass with its own `__iter__`: `_list_extend` must not take the fast path."""

    def __iter__(self):
        return iter(list.copy(self)[::-1])


def mut_items(items):
    """A generator that changes the list under test before each item."""
    for x in items:
        TARGET[0].append(0)
        yield x


def clear_items(items):
    """A generator that clears the list under test (freeing its array) before its second item."""
    for i, x in enumerate(items):
        if i == 1:
            TARGET[0].clear()
        yield x


class Ix:
    """An object with `__index__`, which may change the list under test or raise first."""

    def __init__(self, v, eff):
        self.v, self.eff = v, eff

    def __index__(self):
        t = TARGET[0]
        if self.eff == "bad":
            raise ValueError("idx")
        if t is not None:
            if self.eff == "pop":
                if t:
                    t.pop()
            elif self.eff == "clear":
                t.clear()
            elif self.eff == "add":
                if len(t) < 12:
                    t.append(0)
        return self.v


def mk_ix(a):
    """An index argument: `{"ix": "int"|"obj"|"str"|"float", "v": n, "eff": ...}`."""
    k = a["ix"]
    if k == "int":
        return a["v"]
    if k == "obj":
        return Ix(a["v"], a["eff"])
    if k == "str":
        return "a"
    return 1.5


def build_ext(arg, reg, self_list):
    k = arg["k"]
    if k == "self":
        return self_list
    if k == "noniter":
        return 5
    if k == "sub":
        return RevList(reg.mks(arg["items"]))
    if k == "mutiter":
        return mut_items(reg.mks(arg["items"]))
    if k == "cleariter":
        return clear_items(reg.mks(arg["items"]))
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
    if name == "getitemx":
        return enc(operator.getitem(l, mk_ix(op[1])))
    if name == "setitemx":
        return operator.setitem(l, mk_ix(op[1]), reg.mk(op[2]))
    if name == "delitemx":
        return operator.delitem(l, mk_ix(op[1]))
    if name == "setslice_gen":
        return operator.setitem(l, as_slice(op[1]), build_ext(op[2], reg, l))
    if name == "indexx":
        args = [mk_ix(a) for a in op[2:] if a is not None]
        return l.index(reg.mk(op[1]), *args)
    if name == "getslice":
        return enc_state(operator.getitem(l, as_slice(op[1])))
    if name == "binslice":
        a, b = op[1]
        return enc_state(l[a:b])
    if name == "forloop":
        return [enc_res(x) for x in l]
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
        # In a variable: 3.15 compiles `list(<genexpr>)` to a loop of LIST_APPEND, so written inline
        # it would not reach list_extend_iter_lock_held.
        g = (x for x in items)
        l = list(g)
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
        out = [encs(r[1][0]), r[2] if len(r) > 2 else None]
        # list iterators (l given) also report the callable, `iter` or `reversed`
        return out if l is None else out + [r[0].__name__]
    if name in ("reduce_exhaust", "reduce_add", "reduce_missing"):
        return reduce_hooked(it, l, name)
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


def reduce_hooked(it, l, how):
    """`it.__reduce__()` with the builtins entry it looks up replaced: by a key whose `__eq__`
    exhausts the iterator or appends to the list before it matches (gh-101765), or removed."""
    bd = builtins.__dict__
    name = "iter" if type(it).__name__ == "list_iterator" else "reversed"
    orig = bd[name]

    class Key:
        def __hash__(self):
            return hash(name)

        def __eq__(self, other):
            if how == "reduce_exhaust":
                for _ in it:
                    pass
            else:
                l.append(0)
            return other == name

    del bd[name]
    if how != "reduce_missing":
        bd[Key()] = orig
    try:
        r = it.__reduce__()
        return [encs(r[1][0]), r[2] if len(r) > 2 else None, r[0].__name__]
    finally:
        for k in [k for k in bd if isinstance(k, Key)]:
            del bd[k]
        bd[name] = orig


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
    if fn == "tuple.hashdeep":
        t = ()
        for _ in range(c["depth"]):
            t = (t,)
        return common.py_result(lambda: hash(t))
    if fn == "tuple.repr":
        t = tuple(items())
        return common.py_result(lambda: repr(t))
    if fn == "tuple.getitem":
        t = tuple(items())
        return common.py_result(lambda: enc(operator.getitem(t, c["i"])))
    if fn == "tuple.getslice":
        t = mk_tuple(c["t"], reg)
        return common.py_result(lambda: out_tuple(operator.getitem(t, as_slice(c["s"])), t))
    if fn == "tuple.binslice":
        t = mk_tuple(c["t"], reg)
        a, b = c["s"][:2]
        return common.py_result(lambda: out_tuple(t[a:b], t))
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
    if fn == "list.clear_release":
        log = []
        o = [Finalized(i, log) for i in range(c["n"])]
        o.clear()
        return {"ok": log}
    if fn == "list.sort_sizeof":
        return {"ok": sizes_in_sort()}
    if fn == "list.sizeof_sub":
        cls = type("L", (list,), {"__slots__": tuple(f"s{i}" for i in range(c["k"]))})
        return {"ok": cls(c["items"]).__sizeof__()}
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
        v = (o if c["self"] else None if c["v"] == "x" else 5 if c["v"] == "noniter"
             else DISPLAY[len(c["v"])](*reg.mks(c["v"])))
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


def fits(size, n, inplace=False):
    """Is `size * n` small, or rejected by an explicit check in the C code? `l *= n` rounds the
    size up to a multiple of 4 before `py_list_resize`'s test, so it refuses 3 sizes more."""
    return (size == 0 or n <= 1 or size * n <= BIG or size * n > ALLOC_LIMIT
            or (inplace and size * n > ALLOC_LIMIT - 3))


def seq_count(rng, size, inplace=False):
    s = max(size, 1)
    while True:
        n = rng.choice([0, 1, -1, 2, 3, 5, M, -M, M + 1, -M - 2, 2 ** 64, 10 ** 30,
                        2 ** 60, 2 ** 61, 2 ** 62, M // 2, M // 3 + 1, M // s + 1,
                        ALLOC_LIMIT // s + 1, ALLOC_LIMIT // s, (ALLOC_LIMIT - 3) // s + 1,
                        (ALLOC_LIMIT - 3) // s])
        if n > M or n < -M - 1 or fits(size, n, inplace):
            return n


def seq_tup(rng, maxlen=6, kinds=("nan", "bad", "weird")):
    return {"items": seq_items(rng, maxlen, kinds), "sub": rng.random() < 0.2}


def gen_ext(rng, allow_self=True):
    k = rng.choice(["fast", "fast", "sized", "iter", "iter", "iter", "noniter", "sub"]
                   + (["self", "mutiter", "cleariter"] if allow_self else []))
    if k == "self" or k == "noniter":
        return {"k": k}
    if k in ("sub", "mutiter", "cleariter"):
        return {"k": k, "items": seq_items(rng, 20)}
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


def gen_ix(rng, n):
    r = rng.random()
    if r < 0.15:
        return {"ix": "int", "v": seq_edge(rng, n)}
    if r < 0.85:
        return {"ix": "obj", "v": seq_edge(rng, n), "eff": rng.choice(["none", "none", "pop", "clear", "add", "bad"])}
    return {"ix": rng.choice(["str", "float"])}


def gen_list_op(rng, n):
    kinds = ("nan", "bad", "weird", "pop", "clear", "add")
    e = lambda: seq_elem(rng, kinds)
    k = rng.randrange(26)
    if rng.random() < 0.12:
        k = rng.randrange(5)
        if k == 4:
            return ["setslice_gen", seq_slice(rng, n),
                    {"k": rng.choice(["iter", "mutiter", "cleariter"]), "items": seq_items(rng, 10),
                     "hint": None, "err": rng.random() < 0.2}]
        if k == 0:
            return ["getitemx", gen_ix(rng, n)]
        if k == 1:
            return ["setitemx", gen_ix(rng, n), e()]
        if k == 2:
            return ["delitemx", gen_ix(rng, n)]
        start = gen_ix(rng, n) if rng.random() < 0.8 else None
        stop = gen_ix(rng, n) if start is not None and rng.random() < 0.6 else None
        return ["indexx", e(), start, stop]
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
        return rng.choice([["getslice", seq_slice(rng, n)], ["binslice", seq_slice(rng, n)[:2]]])
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
        return ["imul", seq_count(rng, n, inplace=True)]
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
        k = rng.choice(["next", "next", "next", "hint", "refs", "reduce", "setstate", "pop", "add", "clear",
                        "reduce_exhaust", "reduce_add", "reduce_missing"])
        return [k, rng.choice([0, 1, -1, -2, n, n + 1, n - 1, M, -M - 1, M + 1, 2 ** 64, "x"])] if k == "setstate" else [k]
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
                "v": rng.choice(["x", "noniter", seq_items(rng, 6), seq_items(rng, 6)]),
                "self": o != "x" and rng.random() < 0.2}
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
        if rng.random() < 0.5:
            return {**case, "fn": "list.sizeof_sub", "k": rng.randint(0, 5),
                    "items": [rng.randint(0, 3) for _ in range(rng.randint(0, 9))]}
        return {**case, "fn": "list.sort_sizeof"}
    if k == 24:
        s = lambda: [rng.choice([0, 1, 2, 65, 200, 255]) for _ in range(rng.randint(0, 4))]
        return {**case, "fn": "list.latin_lt", "v": s(), "w": s()}
    if k == 25:
        keys = [[rng.randint(0, 3) for _ in range(rng.randint(1, 3))] for _ in range(rng.randint(0, 12))]
        return {**case, "fn": "list.tuple_sort", "keys": keys}
    if k == 26:
        if rng.random() < 0.002:
            return {**case, "fn": "tuple.hashdeep", "t": {"items": []}, "depth": 1000000}
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
        return {**case, "fn": rng.choice(["tuple.getslice", "tuple.binslice"]) , "t": t, "s": seq_slice(rng, len(t["items"]))}
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
        return {**case, "fn": rng.choice(["tuple.release", "list.release", "list.clear_release"]),
                "n": rng.randint(0, 6)}
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


class BBoom(Exception):
    """A class no C code tests for: it has to come back as it went in."""


def b_exc(e):
    return {"TypeError": TypeError, "ValueError": ValueError, "OverflowError": OverflowError,
            "BBoom": BBoom, "TSub": TSub, "VSub": VSub, "StopIteration": StopIteration}[e[0]](e[1])


class BIdxRaises:
    def __init__(self, e):
        self.e = e

    def __index__(self):
        raise b_exc(self.e)


class BIdxBad:
    """`__index__` returning a non-int: the same as raising the `TypeError` it causes."""

    def __index__(self):
        return "x"


class BDunRaises:
    def __init__(self, e):
        self.e = e

    def __bytes__(self):
        raise b_exc(self.e)


class BIterCall:
    def __init__(self, e):
        self.e = e

    def __iter__(self):
        raise b_exc(self.e)


class BHint:
    def __init__(self, xs, hint):
        self.it = iter(xs)
        self.hint = hint

    def __iter__(self):
        return self

    def __next__(self):
        return next(self.it)

    def __length_hint__(self):
        if isinstance(self.hint, list):
            raise b_exc(self.hint)
        return self.hint


def b_iter_raises(xs, e):
    yield from xs
    raise b_exc(e)


def b_map_raises(xs, e):
    """`map(f, ...)`, a C iterator, whose `f` gives `xs` and then raises `e` (a `StopIteration` ends it)."""
    it = iter(xs)

    def f(_):
        try:
            return next(it)
        except StopIteration:
            pass
        raise b_exc(e)
    return map(f, itertools.count())


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
    if t == "iterraises":
        return b_iter_raises([b_build(x) for x in o[1]], o[2])
    if t == "mapraises":
        return b_map_raises([b_build(x) for x in o[1]], o[2])
    if t == "iterhint":
        return BHint([b_build(x) for x in o[1]], o[2])
    if t == "itercallraises":
        return BIterCall(o[1])
    if t == "indexraises":
        return BIdxRaises(o[1])
    if t == "dunderraises":
        return BDunRaises(o[1])
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
    if rng.random() < 0.06:
        return b_rfail(rng)
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


B_EXC = [["TypeError", "boom"], ["ValueError", "boom"], ["OverflowError", "boom"], ["BBoom", "boom"],
         ["TSub", "boom"], ["VSub", "boom"], ["StopIteration", "boom"]]
B_HINT = [0, 1, 3, 64, 100, 255, 256, 257, -1, -5, 2 ** 70, -2 ** 70, sys.maxsize, sys.maxsize - 32, sys.maxsize - 33,
          2 ** 47]


def b_rfail(rng):
    """An object one of whose methods raises, or an iterator with a hint."""
    k = rng.randrange(6)
    e = rng.choice(B_EXC)
    items = b_rbyteobjs(rng)
    if rng.random() < 0.2 and items:
        items[rng.randrange(len(items))] = rng.choice([["int", 256], ["str", [97]], ["indexraises", e]])
    if k == 0:
        return ["indexraises", e]
    if k == 1:
        return ["dunderraises", e]
    if k == 2:
        return [rng.choice(["iterraises", "mapraises"]), items, e]
    if k == 3:
        return ["itercallraises", e]
    return ["iterhint", items, rng.choice(B_HINT + B_EXC)]


def b_rbyteobjs(rng):
    return [["int", rng.choice([0, 1, 97, 255, 256, -1, 2 ** 63, 300])] if rng.random() < 0.1
            else ["int", rng.randint(0, 255)] for _ in range(rng.randint(0, 6))]


def b_cap_stars(fmt, arg):
    """Cap the ints a `*` really consumes, so that no case asks for a huge result.

    A value is dangerous by position, not size: as a precision `2 ** 40` is a cheap
    OverflowError, as a width it pads to 1 TiB, which the model would build as a list.
    A bare `%` part before a `%.*` spec re-parses as `%%` and shifts every later
    argument by one, so a value generated as a precision can become a width. This
    walks the format as `_PyBytes_FormatEx` does (bytesobject.c:693-883) to find what
    each `*` takes. Only a tuple can get as far as allocating: a single argument is
    used up by the `*`, and the `getnextarg` at :823 then raises.
    """
    if arg[0] != "tuple":
        return arg
    args, i, k, n = arg[1], 0, 0, len(fmt)

    def take(risky):
        nonlocal k
        if k < len(args) and args[k][0] == "int" and risky(args[k][1]):
            args[k] = ["int", args[k][1] % 1000]
        k += 1

    while i < n:
        if fmt[i] != 37:
            i += 1
            continue
        i += 1
        if i < n and fmt[i] == 37:      # `%%` takes no argument; `%5%` does (:823)
            i += 1
            continue
        if i < n and fmt[i] == 40:      # no mapping: "format requires a mapping"
            break
        while i < n and fmt[i] in b"-+ #0":
            i += 1
        if i < n and fmt[i] == 42:
            take(lambda v: 2000 < abs(v) < 2 ** 47)
            i += 1
        else:
            while i < n and 48 <= fmt[i] <= 57:
                i += 1
        if i < n and fmt[i] == 46:
            i += 1
            if i < n and fmt[i] == 42:
                take(lambda v: 2000 < v < 2 ** 31)
                i += 1
            else:
                while i < n and 48 <= fmt[i] <= 57:
                    i += 1
        if i < n and fmt[i] in b"hlL":
            i += 1
        if i >= n:
            break
        i += 1
        k += 1
    return arg


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
    return list(fmt), b_cap_stars(fmt, a)


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
    if t in ("memview", "plain", "iter", "index", "dunder", "iterraises", "mapraises", "iterhint", "itercallraises",
             "indexraises", "dunderraises"):
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


def b_sweep():
    """Every call site that runs a callback, against every raising object and exception class. A
    combination of three random choices is too rare to rely on: one wrong arm took 400000 cases."""
    items = [[["int", 1], ["int", 2]], [], [["int", 256]], [["str", [97]]],
             [["int", 1], ["indexraises", ["ValueError", "boom"]]]]
    objs = []
    for e in B_EXC:
        objs += [["indexraises", e], ["dunderraises", e], ["itercallraises", e]]
        for it in items:
            objs += [["iterraises", it, e], ["mapraises", it, e], ["iterhint", it, e]]
    for it in items:
        objs += [["iterhint", it, h] for h in [0, 1, 64, -1, 2 ** 70, -2 ** 70]]
    cases = []
    for ty in ("bytes", "bytearray"):
        for x in objs:
            base = {"mod": "bytesobj", "s": [97, 98]}
            cases.append({**base, "fn": ty + ".new", "x": x})
            cases.extend({**base, "fn": f"{ty}.{m}", "sub": x, "start": None, "end": None} for m in BSEARCH_M)
            cases.append({**base, "fn": ty + ".contains", "sub": x})
            cases.append({**base, "fn": ty + ".join", "it": x})
            for m in ("startswith", "endswith"):
                cases.append({**base, "fn": f"{ty}.{m}", "sub": x, "start": None, "end": None})
                cases.append({**base, "fn": f"{ty}.{m}", "sub": ["tuple", [["bytes", [122]], x]],
                              "start": None, "end": None})
            for conv in b"dixoXucbsfeEgG":
                cases.append({**base, "fn": ty + ".mod", "s": [37, conv], "arg": x})
                cases.append({**base, "fn": ty + ".mod", "s": [37, conv], "arg": ["tuple", [x]]})
            cases.extend({**base, "fn": f"{ty}.{m}", "arg": x} for m in ("removeprefix", "removesuffix"))
            cases.append({**base, "fn": ty + ".fromhex", "x": x})
            cases.append({**base, "fn": ty + ".translate", "table": x})
            cases.append({**base, "fn": ty + ".strip", "chars": x})
            cases.append({**base, "fn": ty + ".hex", "sep": x, "n": 1})
    return cases


_B_SWEEP = None


def b_rfmt_error(rng):
    """Formats that reach each refusal of `_PyBytes_FormatEx`, at a position that varies."""
    lead = bytes(rng.choice(b"xy%") for _ in range(rng.randint(0, 3))).replace(b"%", b"%%")
    key = rng.choice([b"a", b"(x)", b"", b"it's", b'"', b"\xff", b"a\\b", b"it's\"", b"\n"])
    bad = rng.choice(b"zQyZjw'\"\x00\x01\x1f\x7f\x80\xff\n !,:;<?@[]^_`{|}~")
    k = rng.randrange(16)
    d = ["dict", [[list(key), rng.choice([["int", 7], ["bytes", [97, 98]], ["str", [97]], ["none"], ["plain"], ["list", []],
                                          ["dunder", ["int", 1]], b_bflt(1.5), ["int", 2 ** 70], ["int", 300]])]]]
    one = rng.choice([["int", 5], ["bytes", [97]], ["none"], ["str", [97]], ["plain"], b_bflt(2.5), ["bool", True]])
    two = ["tuple", [one, rng.choice([["int", 3], ["bytes", []], ["none"], ["int", 2 ** 64], ["int", -2 ** 63],
                                      ["int", -2 ** 63 + 1], ["int", 2 ** 31], ["int", -2 ** 31 - 1]])]]
    conv = bytes([rng.choice(b"dixoXucbsfeEgGar")])
    flags = rng.choice([b"", b"-", b"+", b" ", b"#", b"0", b"5", b".2", b"-5.1"])
    if k == 0:
        return lead + b"%(" + key + b")" + flags + conv, d
    if k == 1:
        return lead + b"%(" + key + b")" + conv + rng.choice([b"%d", b" %s", b"%%", b"%%%d"]), d
    if k == 2:
        return lead + b"%(" + key + b")" + rng.choice([b"*d", b"-*d", b".*f", b"5.*f", b"*.*d"]), d
    if k == 3:
        return lead + b"%(" + rng.choice([b"", b"a", b"(a)", b"((a"]), d
    if k == 4:
        return lead + b"%(" + key + b")" + flags + conv, rng.choice([one, two, ["tuple", []]])
    if k == 5:
        return lead + b"%" + rng.choice([b"", b"-", b"5", b".", b".*", b"*", b"l", b"h", b"-5.2l", b"0"]), \
            rng.choice([one, two, ["tuple", []]])
    if k == 6:
        return lead + b"%" + flags + bytes([bad]) + rng.choice([b"", b"x", b"%d"]), rng.choice([one, two])
    if k == 7:
        return lead + b"%" + rng.choice([b"*", b".*", b"*.*", b"-*", b"0*", b"*.2", b"5.*"]) + conv, \
            rng.choice([one, two, ["tuple", [one]], ["tuple", [["int", 1], ["int", 2], one]]])
    if k == 8:
        return lead + b"%d" * rng.randint(0, 3), rng.choice([one, two, ["tuple", []], ["tuple", [["int", 1]] * 4]])
    if k == 9:
        return lead + b"%" + flags + conv, rng.choice([one, two, ["tuple", [["tuple", []]]], ["list", []]])
    if k == 10:
        return lead + b"%c", rng.choice([["int", -1], ["int", 256], ["int", 2 ** 70], ["int", -2 ** 70], ["bytes", []],
                                         ["bytes", [97, 98]], ["bytearray", []], ["bytearray", [1, 2]], one])
    if k == 11:
        return lead + rng.choice([b"%%", b"x"]) * rng.randint(0, 2), rng.choice([one, two, ["tuple", []], d, ["list", []]])
    if k == 12:
        return lead + b"%%" + rng.choice([b"%s", b"%(a)s"]), rng.choice([one, d])
    if k == 13:
        return lead + b"%" + str(rng.choice([2 ** 63 - 1, 2 ** 63, 2 ** 63 + 7, 10 ** 30])).encode() + conv, one
    if k == 14:
        # no float conversion: a precision this large is a 2 GB result
        return lead + b"%." + str(rng.choice([2 ** 31 - 1, 2 ** 31, 2 ** 31 + 7, 10 ** 30])).encode() + rng.choice(
            [b"d", b"x", b"s", b"a"]), one
    return lead + b"%" + rng.choice([b"", b"5", b".1"]) + rng.choice([b"h", b"l", b"L", b"ll", b"hh"]) + conv, one


def b_gen_writer(rng):
    """A session of `_testcapi.PyBytesWriter`: every function of the writer, and its limits."""
    m = sys.maxsize
    size = rng.choice([0, 0, 0, 0, 1, 5, 255, 256, 257, 300, -1, -5, m, m - 32, m - 33, m - 34, 2 ** 47])
    known = size == 0
    ops = []
    grew = False
    for _ in range(rng.randint(0, 6)):
        k = rng.randrange(7)
        if k <= 1:
            b = bytes(rng.choice(b"ab\x00") for _ in range(rng.randint(0, 5)))
            ops.append(["write", list(b), rng.choice([len(b), len(b), -1, 0, min(1, len(b))])])
        elif k == 2:
            n = rng.choice([0, 1, 3, 200, 300, -1, -3, -1000, m, m - 1, m - 32, m - 33, 2 ** 47, -m - 1])
            grew = grew or n > 0
            ops.append(["grow", n])
        elif k == 3:
            n = rng.choice([0, 1, 3, 200, 256, 257, 300, -1, m, m - 33, m - 32, 2 ** 47])
            grew = True
            ops.append(["resize", n])
        elif k == 4:
            f = rng.choice([b"%d", b"x%d", b"%5d", b"%i", b"%u", b"%x", b"%c", b"%%", b"plain", b"%ld", b"%zd", b"%zu", b"%q",
                            b"", b"%"])
            # an int passed for %ld or %zd: only its low half is defined
            v = rng.choice([0, 1, -1, 65, 255, 256, 2 ** 31 - 1, -2 ** 31])
            ops.append(["fmti", list(f), abs(v) % 2 ** 31 if b"l" in f or b"z" in f else v])
        elif k == 5:
            ops.append(["fmts", list(rng.choice([b"%s", b" %s!", b"%.2s", b"%.0s", b"%5s"])),
                        list(rng.choice([b"", b"World", b"ab"]))])
    if rng.random() < 0.7:
        ops.append(["finish"] if rng.random() < 0.7 else ["finish", rng.choice([0, 1, -1, 5, 2 ** 40])])
    return {"mod": "bytesobj", "fn": "bytes.writer", "size": size, "ba": rng.random() < 0.4,
            "known": known and not grew, "ops": ops, "s": []}


def b_run_writer(c):
    import _testcapi
    try:
        w = _testcapi.PyBytesWriter(c["size"], 1 if c["ba"] else 0)
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}
    out = []
    for op in c["ops"]:
        name = op[0]
        if name == "finish":
            def fin():
                r = w.finish() if len(op) == 1 else w.finish_with_size(op[1])
                return [len(r), isinstance(r, bytearray), list(r) if c["known"] else None]
            out.append([common.py_result(fin), -1])
            continue
        if name == "write":
            r = common.py_result(lambda: w.write_bytes(bytes(op[1]), op[2]))
        elif name == "grow":
            r = common.py_result(lambda: w.grow(op[1]))
        elif name == "resize":
            r = common.py_result(lambda: w.resize(op[1]))
        elif name == "fmti":
            r = common.py_result(lambda: w.format_i(bytes(op[1]), op[2]))
        else:
            r = common.py_result(lambda: w.format_s(bytes(op[1]), bytes(op[2])))
        out.append([r, w.get_size()])
    return {"ok": out}


def b_gen_315(rng):
    """Cases that reach what changed in 3.15: the messages of the format loop, `Py_ssize_t`
    separators, the common repr, and what follows a `fromhex` view."""
    ty = rng.choice(["bytes", "bytearray"])
    s = b_rbytes(rng)
    c = {"mod": "bytesobj", "s": s}
    k = rng.randrange(7)
    if k <= 2:
        fmt, arg = b_rfmt_error(rng)
        c["fn"], c["s"], c["arg"] = ty + ".mod", list(fmt), b_noaddr(arg) if 97 in fmt or 114 in fmt else arg
    elif k == 3:
        c["fn"] = ty + ".hex"
        c["sep"] = rng.choice([None, ["str", [58]], ["bytes", [32]]])
        c["n"] = rng.choice([2 ** 31, 2 ** 40, sys.maxsize, -sys.maxsize - 1, 2 ** 63, -2 ** 63 - 1, len(s), len(s) - 1,
                             len(s) + 1, -len(s), 1 - len(s)])
    elif k == 4:
        c["s"] = [rng.choice(list(b"'\"\\ab\t\n\r\x00\x7f\xff")) for _ in range(rng.randint(0, 6))]
        c["fn"] = rng.choice(["bytes.repr", "bytearray.repr", "bytearray.reprsub"])
    elif k == 5:
        c["fn"] = ty + ".fromhex"
        t = list(rng.choice([b"1", b"12 ", b"123", b" 1", b"1 ", b"12  ", b"   "]))
        c["x"] = ["memview", t, [rng.choice(b"0123456789abcdefABCDEF \t\n"), 0]]
    else:
        c["fn"] = ty + ".new"
        c["x"] = ["iterhint", b_rbyteobjs(rng), rng.choice(B_HINT)]
    return c


def b_gen_fail(rng):
    """Every C call that runs a callback, with a callback that raises."""
    ty = rng.choice(["bytes", "bytearray"])
    s = b_rbytes(rng)
    c = {"mod": "bytesobj", "s": s}
    x = b_rfail(rng)
    k = rng.randrange(6)
    if k == 0:
        c["fn"], c["x"] = ty + ".new", x
    elif k == 1:
        c["fn"] = ty + "." + rng.choice(BSEARCH_M)
        c["sub"], c["start"], c["end"] = x, None, None
    elif k == 2:
        c["fn"], c["sub"] = ty + ".contains", x
    elif k == 3:
        c["fn"], c["it"] = ty + ".join", x
    elif k == 4:
        c["fn"] = ty + "." + rng.choice(["startswith", "endswith"])
        c["sub"] = rng.choice([x, ["tuple", [["bytes", s[:1]], x]]])
        c["start"], c["end"] = None, None
    else:
        conv = rng.choice(b"dixoXucbsfeg")
        c["fn"], c["s"], c["arg"] = ty + ".mod", [37, conv], rng.choice([x, ["tuple", [x]]])
    return c


def gen_bytes(rng):
    global _B_SWEEP
    if _B_SWEEP is None:
        _B_SWEEP = b_sweep()
    if _B_SWEEP:
        return _B_SWEEP.pop()
    if rng.random() < 0.08:
        return b_gen_fail(rng)
    if rng.random() < 0.12:
        return b_gen_315(rng)
    if rng.random() < 0.04:
        return b_gen_writer(rng)
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
        if rng.random() < 0.15:
            return b_rfail(rng)
        return rng.choice([["int", rng.randint(0, 255)], ["int", rng.randint(0, 255)], ["int", 256], ["int", -1], ["int", 2 ** 70],
                           ["index", 5], ["bool", True], ["str", [97]], ["none"], b_bflt(1.0)])

    def src():
        if rng.random() < 0.25:
            return b_rfail(rng)
        return rng.choice([["bytes", b_rbytes(rng)], ["bytes", b_rbytes(rng)], ["bytes", []], ["bytearray", b_rbytes(rng)],
                           ["list", b_rbyteobjs(rng)], ["iter", b_rbyteobjs(rng)], ["tuple", b_rbyteobjs(rng)], ["int", 3], ["str", [97]],
                           ["str", []], ["none"], ["memview", b_rbytes(rng), [0]]])

    def idx():
        return rng.choice([0, 1, -1, 2, -2, 5, -5, 40, -40, 2 ** 63, -2 ** 63 - 1, sys.maxsize, -sys.maxsize - 1])

    if rng.random() < 0.08:
        return {"m": "take", "x": rng.choice([["none"], ["none"], ["int", 0], ["int", 1], ["int", 2], ["int", 3], ["int", 5],
                                              ["int", 20], ["int", 21], ["int", -1], ["int", -2], ["int", -20], ["int", -21],
                                              ["int", 2 ** 63], ["int", -2 ** 63 - 1], ["int", sys.maxsize],
                                              ["int", -sys.maxsize - 1], ["index", 1], ["index", -1], ["index", 2 ** 63],
                                              ["bool", True], ["str", [97]], b_bflt(1.0), ["plain"], ["indexraises", ["ValueError", "boom"]],
                                              ["indexraises", ["TypeError", "boom"]]])}
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
        return {"m": "resize", "n": rng.choice([0, 1, 2, 5, 9, 10, 16, 32, 33, 100, 200, -1, 2 ** 63, 2 ** 47, sys.maxsize,
                                                sys.maxsize - 33, sys.maxsize - 32, 2 ** 62])}
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
        return {"m": "imul", "n": rng.choice([0, 1, 2, 3, -1, 2 ** 63, sys.maxsize, 2 ** 47, 2 ** 58])}
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
    if r < 0.975:
        return {"m": "init", "x": rng.choice([None, ["bytes", b_rbytes(rng)], ["int", 5], ["int", 0], ["int", -1], ["str", [97]],
                                              ["list", [["int", rng.randint(0, 255)] for _ in range(rng.randint(0, 4))]],
                                              ["tuple", [["int", 1], ["index", 2]]], ["iter", b_rbyteobjs(rng)], ["none"],
                                              b_rfail(rng), b_rfail(rng), b_rfail(rng)]),
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
    if m == "take":
        return list(b.take_bytes(b_build(op["x"])))
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


class BSub(bytearray):
    pass


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
    if m == "writer":
        return b_run_writer(c)
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
        if m == "reprsub":
            return b_benc(repr(BSub(s)))
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
            # not `s * n`: a warm BINARY_OP site has another message for a huge n, see
            # bugs/bytesobj-seq-repeat-specialized-overflow-message.yaml
            return b_benc(operator.mul(s, c["n"]))
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

import ctypes as _ct
import struct
from array import array

try:
    import _testbuffer as _tb
except ImportError:
    _tb = None

_M = sys.maxsize
_NATIVE = "cbBhHiIlLqQnNfde?P"
_ND_FORMATS = list(_NATIVE) + ["@B", "@i", "@d", "<i", ">h", "=q", "!H", "<d", ">f", "<e", ">?",
                               "2B", "<2h", "3s", "bB", "hb", "2x", "xB", "5p", "Zf", "Zd", "Zd", "@Zf", "@Zd", "<Zd",
                               ">Zf", "2Zf", "ZdB"]
_CAST_FORMATS = list(_NATIVE) * 2 + ["@B", "@i", "@c", "@", "", "x", "BB", "<i", "B\0x", "@B\0",
                                     "\xe9", "s", " B", "Zf", "Zd", "Zf", "Zd", "@Zf", "@Zd", "Z", "Zq", "ZZ", "Zd\0",
                                     "@Z"]
_KEY_INTS = [0, 1, -1, 2, -2, 3, -3, 4, 7, -8, 100, -100, _M, -_M, -_M - 1, _M + 1, 2 ** 64,
             -2 ** 64, 2 ** 100]
_VAL_INTS = [0, 1, -1, 2, 127, 128, -128, -129, 255, 256, 32767, 32768, -32768, -32769, 65535,
             65536, 2 ** 31 - 1, 2 ** 31, -2 ** 31, -2 ** 31 - 1, 2 ** 32 - 1, 2 ** 32, _M, _M + 1,
             -_M - 1, -_M - 2, 2 ** 64 - 1, 2 ** 64, -2 ** 64, 2 ** 100, 2 ** 1024, 2 ** 53 + 1]
_FLOATS = [0.0, -0.0, 1.0, -1.5, 1e-40, 1e39, 1e308, 5e-324, 65504.0, 65520.0, 65519.99,
           6.1e-5, 5.96e-8, 2.98e-8, 1e-10, float("inf"), -float("inf"), float("nan"),
           1.17549435e-38, 3.4028235677973366e+38, 3.4028234e38, 0.1]
_BUF_FLAGS = [0, 1, 4, 5, 8, 9, 12, 13, 24, 25, 28, 29, 56, 57, 60, 88, 92, 152, 156, 280, 281, 284, 285]
_ATTRS = ["obj", "nbytes", "readonly", "itemsize", "format", "ndim", "shape", "strides",
          "suboffsets", "c_contiguous", "f_contiguous", "contiguous"]


def _fbits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def _unfbits(b):
    return struct.unpack("<d", struct.pack("<Q", b))[0]


def _rand_bytes(rng, n):
    mode = rng.randrange(4)
    if mode == 0:
        return [rng.choice([0, 1, 0xff, 0x7f, 0x80]) for _ in range(n)]
    if mode == 1:
        return [rng.randrange(4) for _ in range(n)]
    return [rng.randrange(256) for _ in range(n)]


def _rand_item(rng, c):
    """One element for `struct.pack(fmt)`, for a single native or standard code."""
    if c in "fde":
        return rng.choice([0.0, -0.0, 1.0, -1.5, 0.5, 2.0, 0.25, 3.5])
    if c == "?":
        return rng.random() < 0.5
    if c == "c":
        return bytes([rng.randrange(256)])
    bits = struct.calcsize("@" + c) * 8
    if c.isupper():
        return rng.choice([0, 1, 2, 2 ** bits - 1, rng.randrange(2 ** bits)])
    return rng.choice([0, 1, -1, 2, 2 ** (bits - 1) - 1, -2 ** (bits - 1), rng.randrange(-5, 5)])


def _nd_items(rng, fmt, n):
    """`n` packed elements of `fmt`, as flat bytes."""
    size = struct.calcsize(fmt)
    out = []
    code = fmt.lstrip("@<>=!")
    if code in tuple(_NATIVE):
        for _ in range(n):
            out.extend(struct.pack(fmt, _rand_item(rng, code)))
    else:
        for _ in range(n):
            vals = struct.unpack(fmt, bytes(_rand_bytes(rng, size)))
            out.extend(struct.pack(fmt, *vals))
    return out


# Nothing in the model's store lives at address 0, which is NULL.
_NULLPAGE = 8


def _gen_exporter(rng, store):
    """Lay one exporter out in `store` and return its spec."""
    kind = rng.choice(["bytes", "bytearray", "bytearray", "array", "nd", "nd", "nd", "nd"])
    if _tb is None and kind == "nd":
        kind = "bytes"
    b = len(store)
    if kind in ("bytes", "bytearray"):
        data = _rand_bytes(rng, rng.choice([0, 1, 2, 3, 4, 6, 7, 8, 12, 16, 24, 32]))
        store.extend(data)
        unhash = None if kind == "bytes" else {"cls": "TypeError", "msg": "unhashable type: 'bytearray'"}
        return {"kind": kind, "data": data, "buf": b, "len": len(data), "itemsize": 1,
                "readonly": kind == "bytes", "ndim": 1, "format": "B", "shape": [len(data)],
                "strides": [1], "suboffsets": None, "unhash": unhash}
    if kind == "array":
        tc = rng.choice("bBhHiIlLqQfd")
        size = array(tc).itemsize
        n = rng.choice([0, 1, 2, 3, 4, 6])
        data = _nd_items(rng, tc, n)
        store.extend(data)
        return {"kind": "array", "tc": tc, "data": data, "buf": b, "len": len(data), "itemsize": size,
                "readonly": False, "ndim": 1, "format": tc, "shape": [n], "strides": [size],
                "suboffsets": None,
                "unhash": {"cls": "TypeError", "msg": "unhashable type: 'array.array'"}}

    fmt = rng.choice(_ND_FORMATS)
    itemsize = struct.calcsize(fmt)
    if rng.random() < 0.02:
        ndim = 65
        shape = [1] * 65
    else:
        ndim = rng.choice([0, 1, 1, 1, 2, 2, 2, 3])
        shape = [rng.choice([0, 1, 1, 2, 2, 3, 4]) for _ in range(ndim)]
    writable = rng.random() < 0.6
    fortran = rng.random() < 0.25 and 2 <= ndim <= 3
    pil = rng.random() < 0.3 and 1 <= ndim <= 3
    flags = (_tb.ND_WRITABLE if writable else 0) | (_tb.ND_PIL if pil else 0)
    if ndim == 0:
        flags |= _tb.ND_SCALAR
    # C or Fortran strides of the logical array, then random multipliers
    strides = [0] * ndim
    sd = itemsize
    for i in (range(ndim) if fortran else reversed(range(ndim))):
        strides[i] = sd
        sd *= max(shape[i], 1)
    custom = not fortran and 1 <= ndim <= 3 and rng.random() < 0.6
    if custom:
        extra = 1
        for i in reversed(range(ndim)):
            m = rng.choice([1, 1, 2, 3, -1, -2])
            strides[i] = strides[i] * extra * m
            extra *= abs(m)
    if fortran:
        if rng.random() < 0.5:
            custom = True    # the same strides given explicitly
        else:
            flags |= _tb.ND_FORTRAN
    imin = imax = 0
    if 0 not in shape:
        for s, st in zip(shape, strides):
            if st < 0:
                imin += (s - 1) * st
            else:
                imax += (s - 1) * st
    offset = -imin
    nitems = (imax - imin) // itemsize + 1
    data = _nd_items(rng, fmt, nitems)
    spec = {"kind": "nd", "fmt": fmt, "data": data, "nd_shape": shape, "nd_flags": flags,
            "nd_strides": strides if custom else None, "nd_offset": offset if custom else 0,
            "itemsize": itemsize, "readonly": not writable, "ndim": ndim, "format": fmt,
            "shape": shape if ndim else None, "len": 0}
    try:
        ex = _build_exporter(spec)
    except (ValueError, TypeError, NotImplementedError, struct.error, OverflowError):
        return None
    spec["len"] = ex.nbytes
    spec["unhash"] = None if not writable else {"cls": "ValueError",
                                                "msg": "cannot hash writable ndarray object"}
    if ndim == 0:
        store.extend(data)
        spec.update(buf=b, strides=None, suboffsets=None)
        return spec
    actual = list(ex.strides)
    if not pil:
        store.extend(data)
        spec.update(buf=b + spec["nd_offset"], strides=actual, suboffsets=None)
        return spec
    # init_suboffsets, Modules/_testbuffer.c:1030-1104
    addsize = 8 * ((shape[0] * 8 + 7) // 8)
    imin = sub0 = 0
    for n in range(ndim):
        if shape[n] == 0:
            break
        if strides[n] <= 0:
            x = (shape[n] - 1) * strides[n]
            imin += x
            sub0 += -x if n >= 1 else 0
    start = addsize + spec["nd_offset"] + imin
    step = abs(strides[0])
    table = []
    for n in range(shape[0]):
        table.extend(struct.pack("<Q", (b + start + n * step) % 2 ** 64))
    table.extend([0] * (addsize - len(table)))
    store.extend(table + data)
    buf = b
    if strides[0] < 0 and shape[0] > 0:
        buf = b + (shape[0] - 1) * 8
    spec.update(buf=buf, strides=actual, suboffsets=[sub0] + [-1] * (ndim - 1))
    return spec


def _build_exporter(spec):
    kind = spec["kind"]
    data = bytes(spec["data"])
    if kind == "nil":
        return _NilTable(data, spec["null"])
    if kind == "rawfmt":
        return _RawFmt(data, spec["fmt"], spec["itemsize"])
    if kind == "bytes":
        if "hashrel" in spec:
            e = HashBytes(data)
            e.fails = spec["unhash"] is not None
            return e
        return data
    if kind == "bytearray":
        return bytearray(data)
    if kind == "array":
        a = array(spec["tc"])
        a.frombytes(data)
        return a
    fmt = spec["fmt"]
    size = spec["itemsize"]
    items = []
    for i in range(0, len(data), size):
        v = struct.unpack(fmt, data[i:i + size])
        items.append(v[0] if len(v) == 1 else v)
    kw = {}
    if spec["nd_strides"] is not None:
        kw = {"strides": spec["nd_strides"], "offset": spec["nd_offset"]}
    if spec["ndim"] == 0:
        return _tb.ndarray(items[0], shape=[], format=fmt, flags=spec["nd_flags"])
    return _tb.ndarray(items, shape=spec["nd_shape"], format=fmt, flags=spec["nd_flags"], **kw)


def _gen_rel(rng):
    return rng.randrange(4) if rng.random() < 0.3 else None


def _gen_obj(rng, n_exp):
    """An argument object."""
    r = rng.random()
    if r < 0.37:
        return rng.choice(_VAL_INTS)
    if r < 0.41:
        return {"flt": _gen_end(rng, _fbits(rng.choice(_FLOATS))), "rel": _gen_rel(rng)}
    if r < 0.45:
        return {"bln": _gen_end(rng, rng.random() < 0.5), "rel": _gen_rel(rng)}
    if r < 0.5:
        return {"bool": rng.random() < 0.5}
    if r < 0.55:
        return {"complex": [_fbits(rng.choice(_FLOATS)), _fbits(rng.choice(_FLOATS))]}
    if r < 0.62:
        return {"float": _fbits(rng.choice(_FLOATS))}
    if r < 0.72:
        return {"bytes": _rand_bytes(rng, rng.choice([0, 1, 1, 1, 2, 3, 4, 8]))}
    if r < 0.75:
        return {"str": rng.choice(["", "a", "ab", "\xe9", "Δ"])}
    if r < 0.77:
        return None
    if r < 0.79:
        return {"list": rng.randrange(3)}
    if r < 0.86:
        return {"mv": rng.randrange(6)}
    if r < 0.9:
        d = {"exp": rng.randrange(n_exp), "rel": _gen_rel(rng)}
        ending = _gen_end(rng, None)
        if ending is not None:
            d["end"] = ending
        return d
    if r < 0.95:
        return {"idx": _gen_end(rng, rng.choice(_VAL_INTS)), "rel": _gen_rel(rng)}
    if r < 0.98:
        return {"flt": _gen_end(rng, _fbits(rng.choice(_FLOATS))), "rel": _gen_rel(rng)}
    return {"bln": _gen_end(rng, rng.random() < 0.5), "rel": _gen_rel(rng)}


def _gen_end(rng, value):
    """A callback's ending: usually `value`; sometimes it raises or returns the wrong type."""
    r = rng.random()
    if r < 0.15:
        return {"raise": rng.choice(["ValueError", "TypeError", "OverflowError", "LookupError", "Boom"])}
    if r < 0.25:
        return {"wrong": rng.choice(["str", "NoneType", "list"])}
    return value


def _gen_slice(rng):
    def part():
        return rng.choice([None, None, 0, 1, 2, 3, -1, -2, -3, 4, 100, -100, _M, -_M - 1, 2 ** 64, -2 ** 64])
    step = rng.choice([None, None, 1, 1, 2, 3, -1, -2, 0, _M, -_M, -_M - 1, _M - 1, 2 ** 64])
    a, b = part(), part()
    rel = _gen_rel(rng) if step != 0 and (a is not None or b is not None or step is not None) else None
    return {"slice": [a, b, step], "rel": rel}


def _gen_key_elem(rng):
    r = rng.random()
    if r < 0.55:
        return rng.choice(_KEY_INTS)
    if r < 0.8:
        return _gen_slice(rng)
    if r < 0.9:
        return {"idx": _gen_end(rng, rng.choice(_KEY_INTS)), "rel": _gen_rel(rng)}
    if r < 0.95:
        return {"bool": rng.random() < 0.5}
    return rng.choice([{"float": _fbits(1.0)}, {"str": "a"}, None, {"bytes": [1]}])


def _gen_key(rng):
    r = rng.random()
    if r < 0.7:
        return _gen_key_elem(rng)
    if r < 0.93:
        return {"tuple": [_gen_key_elem(rng) for _ in range(rng.choice([0, 1, 2, 2, 2, 3, 4]))]}
    return {"ellipsis": True}


def _gen_cast_shape(rng):
    r = rng.random()
    if r < 0.55:
        return None
    if r < 0.6:
        return "notseq"
    if r < 0.65:
        return [rng.choice([1, 2, {"bool": True}, None, {"idx": 2}, 2 ** 64, -2 ** 64, 0, -1, _M, 2 ** 62])
                for _ in range(rng.choice([1, 2, 3]))]
    if r < 0.67:
        return [1] * 65
    return [rng.choice([1, 1, 2, 2, 3, 4, 6, 8]) for _ in range(rng.choice([0, 1, 2, 2, 3]))]


def _gen_op(rng, specs):
    n_exp = len(specs)
    h = rng.randrange(8)
    k = rng.choice(["get"] * 6 + ["set"] * 6 + ["cast"] * 6 + ["tolist"] * 4 + ["tobytes"] * 3 + ["hex"] * 2
                   + ["del", "len", "toreadonly", "release", "enter", "exit", "repr", "drop"]
                   + ["cmp"] * 4 + ["hash"] * 3 + ["count"] * 2 + ["index"] * 3 + ["iter"] * 2 + ["next"] * 4
                   + ["attr"] * 5 + ["view"] * 2 + ["fromflags", "buffer", "buffer", "toc", "iscontig", "contig",
                                                     "resize", "frommem", "frombuffer", "restricted"])
    if k == "get":
        return [k, h, _gen_key(rng)]
    if k == "set":
        return [k, h, _gen_key(rng), _gen_obj(rng, n_exp)]
    if k == "del":
        return [k, h, _gen_key(rng)]
    if k == "cast":
        return [k, h, rng.choice(_CAST_FORMATS), _gen_cast_shape(rng)]
    if k == "tobytes":
        return [k, h, rng.choice([None, "C", "F", "A", "", "X", "CC"])]
    if k == "hex":
        return [k, h, rng.choice([None, None, {"str": ":"}, {"str": "ab"}, {"str": "\xe9"}, {"str": "Δ"},
                                  {"str": ""}, {"bytes": [45]}, {"bytes": [200]}, {"bytes": [1, 2]},
                                  {"list": 1}, {"list": 2}, 5]),
                rng.choice([None, 1, 2, 3, -1, -2, -3, 0, 100, -100, 2 ** 31 - 1, -2 ** 31, 2 ** 31, 2 ** 40, _M, -_M - 1,
                            2 ** 63, -2 ** 63 - 1])]
    if k == "cmp":
        return [k, h, _gen_obj(rng, n_exp), rng.choice(["eq", "eq", "ne", "lt"])]
    if k in ("count", "index"):
        v = rng.choice([rng.choice([0, 1, 2, 255, -1]), _gen_obj(rng, n_exp)])
        if isinstance(v, dict) and ("mv" in v or "exp" in v or "idx" in v or "flt" in v or "bln" in v):
            v = 0
        if k == "count":
            return [k, h, v]
        return [k, h, v, rng.choice([None, 0, 1, -1, 2, -2, 5, -5, _M, -_M - 1, 2 ** 64, -2 ** 64]),
                rng.choice([None, 0, 1, -1, 2, -2, 5, -5, _M, -_M - 1, 2 ** 64, -2 ** 64])]
    if k == "next":
        return [k, rng.randrange(4)]
    if k == "attr":
        return [k, h, rng.choice(_ATTRS)]
    if k == "view":
        return [k, rng.choice([{"mv": h}, {"exp": rng.randrange(n_exp), "rel": None}, {"bytes": [1, 2]},
                               5, None, {"str": "a"}])]
    if k == "fromflags":
        e = rng.randrange(n_exp)
        if specs[e]["kind"] == "nd":
            return ["fromflags", {"mv": h}, rng.choice(_BUF_FLAGS)]
        return ["fromflags", {"exp": e, "rel": None}, rng.choice(_BUF_FLAGS)]
    if k == "buffer":
        return [k, h, rng.choice(_BUF_FLAGS)]
    if k in ("toc", "iscontig"):
        return [k, h, rng.choice("CFA")]
    if k == "contig":
        return [k, {"mv": h}, rng.random() < 0.3, rng.choice("CFA")]
    if k == "resize":
        ids = [i for i, s in enumerate(specs) if s["kind"] == "bytearray"]
        return [k, rng.choice(ids)] if ids else ["len", h]
    if k == "frommem":
        ids = [i for i, s in enumerate(specs) if s["kind"] == "bytearray" and s["len"] > 0]
        return [k, rng.choice(ids), rng.random() < 0.5] if ids else ["len", h]
    if k == "restricted":
        ids = [i for i, s in enumerate(specs) if s["kind"] in ("bytes", "bytearray")]
        return [k, rng.choice(ids)] if ids else ["len", h]
    if k == "frombuffer":
        e = rng.randrange(n_exp)
        return [k, e, 284 if specs[e]["kind"] == "nd" else rng.choice([b for b in _BUF_FLAGS if not b & 1])]
    return [k, h]


_LOW_FNS = ["mem.narrow32", "mem.widen32", "mem.pack2", "mem.unpack2", "mem.long2d", "mem.deqint",
            "mem.fmtchar", "mem.fmtstr"]


def _gen_low(rng):
    fn = rng.choice(_LOW_FNS)
    case = {"mod": "bytesobj", "fn": fn}
    if fn in ("mem.narrow32", "mem.pack2"):
        r = rng.random()
        if r < 0.3:
            case["d"] = _fbits(rng.choice(_FLOATS))
        elif r < 0.5:
            case["d"] = rng.getrandbits(64)
        else:
            e = rng.randrange(1023 - 160, 1023 + 136)
            frac = rng.choice([0, 1, 2 ** 52 - 1, 2 ** 28, 2 ** 29, 2 ** 29 + 1, 2 ** 41, 2 ** 42 - 1,
                               2 ** 41 + 2 ** 42, rng.getrandbits(52), 2 ** 52 - 2 ** 28, 2 ** 52 - 2 ** 41])
            case["d"] = (rng.getrandbits(1) << 63) | (e << 52) | frac
    elif fn in ("mem.widen32", "mem.unpack2"):
        n = 32 if fn == "mem.widen32" else 16
        case["x"] = rng.choice([rng.getrandbits(n), rng.getrandbits(n) & ((1 << (n - 9)) - 1)])
    elif fn == "mem.long2d":
        bits = rng.choice([1, 8, 53, 54, 55, 64, 65, 100, 1023, 1024, 1025])
        case["n"] = rng.choice([1, -1]) * rng.choice([rng.getrandbits(bits), 2 ** bits - 1, 2 ** bits + 1,
                                                       2 ** bits, (2 ** 53 + 1) << max(bits - 54, 0)])
    elif fn == "mem.deqint":
        n = rng.choice([0, 1, -1, 3, 2 ** 53, 2 ** 53 + 1, 2 ** 100, -2 ** 100, 10 ** 400, rng.getrandbits(60)])
        d = rng.choice([float(n) if abs(n) < 2 ** 1000 else 1.0, 0.5, -0.0, 1.5, float("inf"), float("nan")])
        case.update(d=_fbits(d), n=n)
    else:
        case["fmt"] = rng.choice(_CAST_FORMATS + ["@@B", "BB", "@BB", "\0", "B\0", "@\0B", "\xe9"])
    return case


def _gen_script(rng):
    store = [0] * _NULLPAGE
    specs = []
    singletons = []     # empty and one-byte `bytes` are shared, so `m.obj` could not tell two apart
    for _ in range(rng.choice([1, 1, 2, 3])):
        s = _gen_exporter(rng, store)
        if s is None:
            return None
        if s["kind"] == "bytes":
            o = _build_exporter(s)
            if any(o is e for e in singletons):
                continue
            singletons.append(o)
        specs.append(s)
    exps = [{k: s[k] for k in ("buf", "len", "itemsize", "readonly", "ndim", "format", "shape", "strides",
                               "suboffsets", "unhash")} for s in specs]
    ops = [["view", {"exp": rng.randrange(len(specs)), "rel": None}]]
    ops += [_gen_op(rng, specs) for _ in range(rng.choice([2, 3, 5, 8, 12]))]
    # A `contig` view of a short buffer owns a temporary `bytes`, which is the same shared
    # object as a short exporter, so `.obj` cannot say which. Each pair of these still occurs.
    if (any(len(e) <= 1 for e in singletons) and any(op[0] == "contig" for op in ops)
            and any(op[0] == "attr" and op[2] == "obj" for op in ops)):
        return None
    return {"mod": "bytesobj", "fn": "mem.script", "mem": store, "exps": exps, "specs": specs, "ops": ops}


def _gen_pack_fail(rng):
    """Assign a failing item through a view cast to each format. A random script rarely
    pairs a format like `?` with the callback object that format runs."""
    data = _rand_bytes(rng, 8)
    spec = {"kind": "bytearray", "data": data, "buf": _NULLPAGE, "len": 8, "itemsize": 1, "readonly": False,
            "ndim": 1, "format": "B", "shape": [8], "strides": [1], "suboffsets": None,
            "unhash": {"cls": "TypeError", "msg": "unhashable type: 'bytearray'"}}
    fmt = rng.choice("??fdebBhHiIlLqQnN")
    key = "bln" if fmt == "?" else "flt" if fmt in "fde" else "idx"
    value = {"bln": True, "flt": _fbits(1.5), "idx": 1}[key]
    ending = _gen_end(rng, value)
    if ending is value and rng.random() < 0.8:
        ending = rng.choice([{"raise": rng.choice(list(_RAISES))}, {"wrong": rng.choice(list(_WRONG))}])
    item = {key: ending, "rel": rng.choice([None, None, 0, 1])}
    ops = [["view", {"exp": 0, "rel": None}], ["cast", 0, fmt, None], ["set", 1, 0, item], ["get", 1, 0],
           ["tobytes", 0, ""]]
    exps = [{k: spec[k] for k in ("buf", "len", "itemsize", "readonly", "ndim", "format", "shape", "strides",
                                  "suboffsets", "unhash")}]
    return {"mod": "bytesobj", "fn": "mem.script", "mem": [0] * _NULLPAGE + list(data), "exps": exps,
            "specs": [spec], "ops": ops}


def _spec_bytearray(rng, n=8):
    return {"kind": "bytearray", "data": _rand_bytes(rng, n), "buf": _NULLPAGE, "len": n, "itemsize": 1,
            "readonly": False, "ndim": 1, "format": "B", "shape": [n], "strides": [1], "suboffsets": None,
            "unhash": {"cls": "TypeError", "msg": "unhashable type: 'bytearray'"}}


def _script_of(spec, ops, extra=()):
    keys = ("buf", "len", "itemsize", "readonly", "ndim", "format", "shape", "strides", "suboffsets",
            "unhash") + tuple(extra)
    return {"mod": "bytesobj", "fn": "mem.script", "mem": [0] * _NULLPAGE + list(spec["data"]),
            "exps": [{k: spec[k] for k in keys}], "specs": [spec], "ops": ops}


def _gen_failure(rng):
    """A callback's failure, not a value."""
    return rng.choice([{"raise": rng.choice(list(_RAISES))}, {"wrong": rng.choice(list(_WRONG))}])


def _gen_effect(rng):
    """One short script for each effect of the Python code a memoryview runs. Random scripts
    rarely line up the object, the operation and the view that each of these needs."""
    k = rng.randrange(15)
    spec = _spec_bytearray(rng)
    view = ["view", {"exp": 0, "rel": None}]
    tail = [["tobytes", 0, None], ["release", 0], ["tobytes", 0, None]]
    if k == 0:      # `__buffer__`: memoryview(x), `==` (cleared) and a slice assignment
        bad = {"exp": 0, "rel": None, "end": _gen_failure(rng)}
        return _script_of(spec, [["view", bad], view, ["set", 0, {"slice": [0, 2, None], "rel": None}, bad],
                                 ["cmp", 0, bad, "eq"]] + tail)
    if k == 1:      # `__release_buffer__`, on the last view, or at the end of `==`
        hooked = {"exp": 0, "rel": None, "hook": 0}
        if rng.random() < 0.5:
            return _script_of(spec, [view, ["view", hooked], ["tobytes", 1, None], ["release", 1]] + tail)
        return _script_of(spec, [view, ["cmp", 0, hooked, rng.choice(["eq", "ne"])]] + tail)
    if k == 2:      # a weakref callback runs after the release in `memory_dealloc`
        return _script_of(spec, [view, view, ["weak", 1, 0], ["drop", 1]] + tail)
    if k == 3:      # `__hash__` of a real exporter, with `self` holding an export
        spec = dict(spec, kind="bytes", readonly=True, hashrel=0,
                    unhash=rng.choice([None, {"cls": "ValueError", "msg": "boom"}]))
        h = rng.randrange(2)     # on view 0, `self.release()`; on view 1, the release of another view
        return _script_of(spec, [view, view, ["hash", h], ["hash", h]] + tail, ("hashrel",))
    if k == 4:      # a slice part that fails, in `PySlice_Unpack`'s order
        how = rng.choice([_gen_failure(rng), {"notindex": True}])
        fail = dict(how, part=rng.choice(["start", "stop", "step"]))
        rel = None if "notindex" in how else rng.choice([None, 0])
        parts = rng.choice([[0, 4, 2], [1, 4, None], [0, 4, 0], [None, None, 0]])
        key = {"slice": parts, "rel": rel, "fail": fail}
        return _script_of(spec, [view, rng.choice([["get", 0, key], ["set", 0, key, {"bytes": [1, 2]}]])] + tail)
    if k == 5:      # a `sep` with `__len__`: `self` holds an export only if contiguous
        sep = {"lenobj": rng.choice([1, 2, 0, -1, _gen_failure(rng)]), "rel": rng.choice([None, 0, 1])}
        return _script_of(spec, [view, ["get", 0, {"slice": [None, None, 2], "rel": None}],
                                 ["hex", rng.randrange(2), sep, None], ["tobytes", 1, None]] + tail)
    if k == 6:      # `import struct` fails: the same format stays on the `switch`
        hooked = {"exp": 0, "rel": None, "hook": 0}
        c = _script_of(spec, [view, ["cast", 0, rng.choice(["b", "B", "c"]), None],
                              ["cmp", 0, {"mv": 1}, rng.choice(["eq", "ne"])], ["cmp", 1, {"mv": 0}, "eq"],
                              ["cmp", 1, hooked, "eq"]] + tail)
        c["nostruct"] = rng.random() < 0.8
        return c
    if k == 8:      # `bytes == memoryview`: the item of format `c` against a view, reflected
        one = ["get", 0, {"slice": [0, 1, None], "rel": None}]
        fmt = rng.choice(["c", "c", "c", "B", "b"])
        value = {"mv": rng.choice([0, 2, 2, 2])}
        release = rng.choice([[], [], [["release", 2]]])
        return _script_of(spec, [view, ["cast", 0, fmt, None], one] + release +
                          [rng.choice([["count", 1, value], ["index", 1, value, None, None]]), ["tobytes", 0, ""]])
    if k == 9:      # a truth with no `__bool__`, stored through `?`
        item = {"lenobj": rng.choice([0, 1, 2, -1, _gen_failure(rng)]), "rel": rng.choice([None, None, 0])}
        return _script_of(spec, [view, ["cast", 0, "?", None], ["set", 1, 0, item], ["tobytes", 1, ""]] + tail)
    if k == 10:     # what `__eq__` returns is tested for truth, whatever it is
        value = {"eqobj": {"wrong": rng.choice(list(_WRONG))}, "rel": rng.choice([None, None, 0])}
        return _script_of(spec, [view, rng.choice([["count", 0, value], ["index", 0, value, None, None]])] + tail)
    if k == 11:     # `fix_error_int` and `fix_struct_error_int` match subclasses
        fmt = rng.choice("bBhHiIqQnNfd")
        key = "flt" if fmt in "fd" else "idx"
        item = {key: {"raise": rng.choice(["VSub", "TSub", "OSub", "UnicodeError"])}, "rel": None}
        return _script_of(spec, [view, ["cast", 0, fmt, None], ["set", 1, 0, item], ["tobytes", 0, ""]])
    if k == 12:
        return _gen_nil(rng)
    if k == 13:
        return _gen_rawfmt(rng)
    if k == 14:     # a chain of `__release_buffer__`, each releasing an earlier view
        ops = [view]
        n = rng.randint(2, 4)
        for h in range(1, n):
            ops.append(["view", {"exp": 0, "rel": None, "hook": rng.randrange(h + 1)}])
        for h in rng.sample(range(n), rng.randint(1, n)):
            ops.append(["release", h])
        return _script_of(spec, ops + [["tobytes", h, ""] for h in range(n)])
    value = {"eqobj": rng.choice([True, False, False, {"raise": rng.choice(list(_RAISES))}]),
             "rel": rng.choice([None, None, 0])}
    return _script_of(spec, [view, rng.choice([["count", 0, value], ["index", 0, value, None, None]])] + tail)


def _gen_rawfmt(rng):
    """A view whose format no exporter in Python can have: a repeat count `Struct` refuses, which
    `==` reads as "not equal", or one it accepts and `unpack_from` then refuses."""
    n = rng.randint(1, 4)
    data = _rand_bytes(rng, n)
    fmt = rng.choice([str(2 ** 63 - 1) + "B", str(2 ** 63) + "B", "9" * 25 + "B", str(2 ** 62) + "H",
                      str(2 ** 61) + "Q", "B" + str(2 ** 63 - 1) + "B", str(2 ** 63 - 1) + "x" + "B",
                      "9" * 25, str(2 ** 63) + "?!", "<" + str(2 ** 62) + "h", "1B", "2B", "Bx"])
    size = 1
    if rng.random() < 0.25:     # `PyMem_Malloc(itemsize)` fails, after `Struct` accepted the format
        size, n, fmt, data = 2 ** 62, 1, rng.choice(["2B", "Bx", "1B"]), data[:1]
    spec = {"kind": "rawfmt", "data": data, "fmt": fmt, "buf": _NULLPAGE, "len": n, "itemsize": size, "readonly": True,
            "ndim": 1, "format": fmt, "shape": [n], "strides": [size], "suboffsets": None, "unhash": None}
    keys = ("buf", "len", "itemsize", "readonly", "ndim", "format", "shape", "strides", "suboffsets", "unhash")
    ops = [["fromnil", 0], ["cmp", 0, {"bytes": data}, "eq"], ["cmp", 0, {"bytes": data}, "ne"]]
    return {"mod": "bytesobj", "fn": "mem.script", "mem": [0] * _NULLPAGE + data,
            "exps": [{k: spec[k] for k in keys}], "specs": [spec], "ops": ops}


def _gen_nil(rng):
    """A PIL view whose pointer table has NULL entries, through `PyMemoryView_FromBuffer`. Only
    `memoryiter_next` looks at the pointer: anything else that reached a NULL would crash."""
    n = rng.randint(1, 5)
    data = _rand_bytes(rng, n)
    null = [rng.random() < 0.4 for _ in range(n)]
    table = _NULLPAGE
    base = table + 8 * n
    mem = [0] * _NULLPAGE
    for i in range(n):
        mem.extend(struct.pack("<Q", 0 if null[i] else base + i))
    mem.extend(data)
    spec = {"kind": "nil", "data": data, "null": null, "buf": table, "len": n, "itemsize": 1, "readonly": True,
            "ndim": 1, "format": "B", "shape": [n], "strides": [8], "suboffsets": [0], "unhash": None}
    keys = ("buf", "len", "itemsize", "readonly", "ndim", "format", "shape", "strides", "suboffsets", "unhash")
    ops = [["fromnil", 0], ["iter", 0]] + [["next", 0]] * (n + 1) + [["count", 0, rng.choice([0, 1, data[0]])]]
    return {"mod": "bytesobj", "fn": "mem.script", "mem": mem, "exps": [{k: spec[k] for k in keys}],
            "specs": [spec], "ops": ops}


def _gen_complex(rng):
    """Complex items: what 3.15 added to `get_native_fmtchar`, `unpack_single`, `pack_single`,
    `unpack_cmp`, `adjust_fmt`, and the `v == v` shortcut for the formats that have one."""
    n = rng.choice([8, 16, 32, 48])
    spec = _spec_bytearray(rng, n)
    fa, fb = rng.choice(["Zf", "Zd"]), rng.choice(["Zf", "Zd", "f", "d", "B", "q", "?", "e"])
    view = ["view", {"exp": 0, "rel": None}]
    obj = rng.choice([{"complex": [_fbits(rng.choice(_FLOATS)), _fbits(rng.choice(_FLOATS))]},
                      {"float": _fbits(rng.choice(_FLOATS))}, 1, {"bool": True},
                      {"flt": _gen_end(rng, _fbits(1.5)), "rel": None}, {"idx": 1, "rel": None}, {"str": "a"}, None,
                      {"bytes": [1]}])
    ops = [view, ["cast", 0, "B", None], ["cast", 0, fa, None], ["cast", 0, fb, None]]
    tail = rng.choice([[["tolist", 2], ["tolist", 3]], [["get", 2, 0], ["get", 2, -1]], [["get", 3, 0]],
                       [["set", 2, 0, obj], ["tobytes", 0, ""], ["get", 2, 0]],
                       [["set", 3, 0, obj], ["tobytes", 0, ""]],
                       [["cmp", 2, {"mv": 2}, "eq"], ["cmp", 2, {"mv": 3}, "eq"], ["cmp", 3, {"mv": 2}, "ne"]],
                       [["cmp", 0, {"mv": 0}, "eq"], ["cmp", 1, {"mv": 1}, "eq"], ["cmp", 3, {"mv": 3}, "eq"]],
                       [["hash", 2], ["hash", 3]], [["count", 2, obj], ["index", 2, obj, None, None]],
                       [["tobytes", 2, "A"], ["hex", 2, None, None]]])
    return _script_of(spec, ops + tail)


def gen_mem(rng):
    r = rng.random()
    if r < 0.04:
        return _gen_complex(rng)
    if r < 0.15:
        return _gen_low(rng)
    if r < 0.2:
        return _gen_pack_fail(rng)
    return _gen_effect(rng) if r < 0.3 else _gen_script(rng)


def _item_json(x):
    if x is True or x is False:
        return {"bool": x}
    if isinstance(x, int):
        return x
    if isinstance(x, float):
        return {"float": _fbits(x)}
    if isinstance(x, complex):
        return {"complex": [_fbits(x.real), _fbits(x.imag)]}
    if isinstance(x, bytes):
        return {"bytes": list(x)}
    if isinstance(x, list):
        return [_item_json(y) for y in x]
    raise TypeError(type(x))


class _Gone:
    pass


class _PyBuffer(_ct.Structure):
    _fields_ = [("buf", _ct.c_void_p), ("obj", _ct.c_void_p), ("len", _ct.c_ssize_t),
                ("itemsize", _ct.c_ssize_t), ("readonly", _ct.c_int), ("ndim", _ct.c_int),
                ("format", _ct.c_char_p), ("shape", _ct.c_void_p), ("strides", _ct.c_void_p),
                ("suboffsets", _ct.c_void_p), ("internal", _ct.c_void_p)]


class _NilTable:
    """The memory of a PIL view: bytes, and a table of pointers to them, some NULL."""

    def __init__(self, data, null):
        n = len(data)
        self.data = (_ct.c_char * n).from_buffer_copy(data)
        self.table = (_ct.c_void_p * n)(*[None if null[i] else _ct.addressof(self.data) + i for i in range(n)])
        self.shape = (_ct.c_ssize_t * 1)(n)
        self.strides = (_ct.c_ssize_t * 1)(8)
        self.suboffsets = (_ct.c_ssize_t * 1)(0)
        self.fmt = _ct.create_string_buffer(b"B")
        self.n = n

    def view(self):
        info = _PyBuffer()
        info.buf = _ct.addressof(self.table)
        info.obj = None
        info.len = self.n
        info.itemsize = 1
        info.readonly = 1
        info.ndim = 1
        info.format = _ct.cast(self.fmt, _ct.c_char_p)
        info.shape = _ct.addressof(self.shape)
        info.strides = _ct.addressof(self.strides)
        info.suboffsets = _ct.addressof(self.suboffsets)
        f = _ct.pythonapi.PyMemoryView_FromBuffer
        f.restype = _ct.py_object
        f.argtypes = [_ct.POINTER(_PyBuffer)]
        return f(_ct.byref(info))


class _RawFmt:
    """Bytes under a format that no Python exporter would give them."""

    def __init__(self, data, fmt, itemsize):
        n = len(data)
        self.data = (_ct.c_char * n).from_buffer_copy(data)
        self.shape = (_ct.c_ssize_t * 1)(n)
        self.strides = (_ct.c_ssize_t * 1)(itemsize)
        self.fmt = _ct.create_string_buffer(fmt.encode())
        self.n = n
        self.itemsize = itemsize

    def view(self):
        info = _PyBuffer()
        info.buf = _ct.addressof(self.data)
        info.obj = None
        info.len = self.n
        info.itemsize = self.itemsize
        info.readonly = 1
        info.ndim = 1
        info.format = _ct.cast(self.fmt, _ct.c_char_p)
        info.shape = _ct.addressof(self.shape)
        info.strides = _ct.addressof(self.strides)
        info.suboffsets = None
        f = _ct.pythonapi.PyMemoryView_FromBuffer
        f.restype = _ct.py_object
        f.argtypes = [_ct.POINTER(_PyBuffer)]
        return f(_ct.byref(info))


class Boom(Exception):
    """Not a built-in class on purpose: `fix_error_int` must pass it through."""


class TSub(TypeError):
    pass


class VSub(ValueError):
    pass


class OSub(OverflowError):
    pass


_RAISES = {"ValueError": ValueError, "TypeError": TypeError, "OverflowError": OverflowError,
           "LookupError": LookupError, "Boom": Boom, "TSub": TSub, "VSub": VSub, "OSub": OSub,
           "UnicodeError": UnicodeError}
_WRONG = {"str": "x", "NoneType": None, "list": []}


def _end(spec):
    """How a callback ends: a value, a raise, or an object of the wrong type."""
    if isinstance(spec, dict) and "raise" in spec:
        raise _RAISES[spec["raise"]]("boom")
    if isinstance(spec, dict) and "wrong" in spec:
        return _WRONG[spec["wrong"]]
    return spec


class Idx:
    def __init__(self, n, fire):
        self.n, self.fire = n, fire

    def __index__(self):
        self.fire()
        return _end(self.n)


class Flt:
    def __init__(self, x, fire):
        self.x, self.fire = x, fire

    def __float__(self):
        self.fire()
        v = _end(self.x)
        return _unfbits(v) if isinstance(v, int) else v


class Bln:
    def __init__(self, b, fire):
        self.b, self.fire = b, fire

    def __bool__(self):
        self.fire()
        return _end(self.b)


class Exporter:
    def __init__(self, ex, fire, ending=None):
        self.ex, self.fire, self.ending = ex, fire, ending

    def __buffer__(self, flags):
        self.fire()
        if self.ending is not None:
            return _end(self.ending)
        return memoryview(self.ex)


class HookExporter(Exporter):
    """An exporter whose `__release_buffer__` releases a view."""

    def __init__(self, ex, fire, ending, hook):
        super().__init__(ex, fire, ending)
        self.hook = hook

    def __release_buffer__(self, view):
        self.hook()
        view.release()


HookExporter.__qualname__ = "Exporter"     # one name in the errors that print the class


class Len:
    def __init__(self, n, fire):
        self.n, self.fire = n, fire

    def __len__(self):
        self.fire()
        return _end(self.n)


class Eql:
    def __init__(self, b, fire):
        self.b, self.fire = b, fire

    def __eq__(self, other):
        self.fire()
        return _end(self.b)

    __hash__ = None


class HashBytes(bytes):
    """A real exporter with a Python `__hash__`: a `memoryview` of an `Exporter` hashes the
    wrapper of `__buffer__`, so only this reaches `PyObject_Hash(view->obj)` with Python code."""
    on_hash = None
    fails = False

    def __hash__(self):
        self.on_hash()
        if self.fails:
            raise ValueError("boom")
        return bytes.__hash__(self)


class _Script:
    """Runs one script against the real objects."""

    def __init__(self, case):
        self.specs = case["specs"]
        self.exps = [_build_exporter(s) for s in self.specs]
        for e in self.exps:
            if isinstance(e, HashBytes):
                e.on_hash = lambda: self.rel({"rel": 0})()
        self.handles = []
        self.dropped = set()
        self.iters = []
        self.hashed = {}
        self.pinned = set()
        self.pinned_objs = []
        self.weak = []

    def pick(self, h):
        if not self.handles:
            return None
        i = h % len(self.handles)
        return None if i in self.dropped else i

    def reg(self, m):
        for i, x in enumerate(self.handles):
            if x is m:
                return {"mv": i}
        self.handles.append(m)
        return {"mv": len(self.handles) - 1}

    def rel(self, j):
        """The callback of an object spec: `m.release()`, ignoring BufferError."""
        r = j.get("rel")
        i = None if r is None else self.pick(r)
        if i is None:
            return lambda: None
        m = self.handles[i]

        def fire():
            try:
                m.release()
            except BufferError:
                pass
        return fire

    def obj(self, j, raw=False):
        """Returns (object,) or None for a dead handle. With `raw`, an exporter is the
        object itself, not the `Exporter` wrapper."""
        if j is None or isinstance(j, int):
            return (j,)
        if "bool" in j:
            return (j["bool"],)
        if "float" in j:
            return (_unfbits(j["float"]),)
        if "complex" in j:
            return (complex(_unfbits(j["complex"][0]), _unfbits(j["complex"][1])),)
        if "bytes" in j:
            return (bytes(j["bytes"]),)
        if "str" in j:
            return (j["str"],)
        if "list" in j:
            return ([0] * j["list"],)
        if "mv" in j:
            i = self.pick(j["mv"])
            return None if i is None else (self.handles[i],)
        fire = self.rel(j)
        if "exp" in j:
            ex = self.exps[j["exp"]]
            if "hook" in j:
                return (HookExporter(ex, fire, j.get("end"), self.rel({"rel": j["hook"]})),)
            return (ex if raw and "end" not in j else Exporter(ex, fire, j.get("end")),)
        if "idx" in j:
            return (Idx(j["idx"], fire),)
        if "flt" in j:
            return (Flt(j["flt"], fire),)
        if "lenobj" in j:
            return (Len(j["lenobj"], fire),)
        if "eqobj" in j:
            return (Eql(j["eqobj"], fire),)
        return (Bln(j["bln"], fire),)

    def key_elem(self, j):
        if isinstance(j, dict) and "slice" in j:
            a, b, c = j["slice"]
            if "fail" in j:
                f = j["fail"]
                parts = [a, b, c]
                parts[("start", "stop", "step").index(f["part"])] = (
                    "x" if "notindex" in f else Idx(f, self.rel(j)))
                return (slice(*parts),)
            if j.get("rel") is not None:
                fire = self.rel(j)
                if a is not None:
                    a = Idx(a, fire)
                elif b is not None:
                    b = Idx(b, fire)
                else:
                    c = Idx(c, fire)
            return (slice(a, b, c),)
        return self.obj(j)

    def key(self, j):
        if isinstance(j, dict) and "ellipsis" in j:
            return (...,)
        if isinstance(j, dict) and "tuple" in j:
            es = [self.key_elem(e) for e in j["tuple"]]
            if any(e is None for e in es):
                return None
            return (tuple(e[0] for e in es),)
        return self.key_elem(j)

    def step(self, op):
        name = op[0]
        skip = {"skip": True}
        py = common.py_result
        if name == "view":
            o = self.obj(op[1], raw=True)
            return skip if o is None else py(lambda: self.reg(memoryview(o[0])))
        if name == "fromflags":
            o = self.obj(op[1], raw=True)
            return skip if o is None else py(lambda: self.reg(memoryview._from_flags(o[0], op[2])))
        if name == "resize":
            ba = self.exps[op[1]]
            if op[1] in self.pinned:    # a raw view of its memory exists
                return skip
            try:
                ba.append(0)
                ba.pop()
                return {"ok": {"bool": True}}
            except BufferError:
                return {"ok": {"bool": False}}
        if name == "contig":
            o = self.obj(op[1])
            if o is None:
                return skip
            buffertype = _tb.PyBUF_WRITE if op[2] else _tb.PyBUF_READ

            def contig():
                v = _tb.get_contiguous(o[0], buffertype, op[3])
                # Keep its temporary alive: an exporter that releases this view during a
                # comparison would otherwise make CPython read freed memory, see
                # bugs/bytesobj-memoryview-eq-released-by-buffer.yaml.
                self.pinned_objs.append(v.obj)
                return self.reg(v)
            return py(contig)
        if name == "frommem":
            ba = self.exps[op[1]]
            self.pinned.add(op[1])
            holder = (_ct.c_char * len(ba)).from_buffer(ba)
            f = _ct.pythonapi.PyMemoryView_FromMemory
            f.restype = _ct.py_object
            f.argtypes = [_ct.c_void_p, _ct.c_ssize_t, _ct.c_int]
            m = f(_ct.addressof(holder), len(ba), 0x200 if op[2] else 0x100)
            del holder
            return {"ok": self.reg(m)}
        if name == "frombuffer":
            ex = self.exps[op[1]]
            self.pinned.add(op[1])
            info = _PyBuffer()
            get = _ct.pythonapi.PyObject_GetBuffer
            get.argtypes = [_ct.py_object, _ct.POINTER(_PyBuffer), _ct.c_int]
            get(ex, _ct.byref(info), op[2])
            f = _ct.pythonapi.PyMemoryView_FromBuffer
            f.restype = _ct.py_object
            f.argtypes = [_ct.POINTER(_PyBuffer)]
            res = py(lambda: self.reg(f(_ct.byref(info))))
            rel = _ct.pythonapi.PyBuffer_Release
            rel.argtypes = [_ct.POINTER(_PyBuffer)]
            rel(_ct.byref(info))
            return res
        if name == "restricted":
            return {"ok": _run_restricted(self.exps[op[1]])}
        if name == "fromnil":
            return {"ok": self.reg(self.exps[op[1]].view())}
        if name == "next":
            if not self.iters:
                return skip
            it = self.iters[op[1] % len(self.iters)]

            def nxt():
                try:
                    return _item_json(next(it))
                except StopIteration:
                    return {"stop": True}
            return py(nxt)
        i = self.pick(op[1])
        if i is None:
            return skip
        m = self.handles[i]
        if name == "get":
            k = self.key(op[2])
            if k is None:
                return skip

            def get():
                r = m[k[0]]
                return self.reg(r) if isinstance(r, memoryview) else _item_json(r)
            return py(get)
        if name == "set":
            k = self.key(op[2])
            v = self.obj(op[3])
            if k is None or v is None:
                return skip

            def st():
                m[k[0]] = v[0]
            return py(st)
        if name == "del":
            k = self.key(op[2])
            if k is None:
                return skip

            def de():
                del m[k[0]]
            return py(de)
        if name == "len":
            return py(lambda: len(m))
        if name == "tolist":
            return py(lambda: _item_json(m.tolist()))
        if name == "tobytes":
            return py(lambda: {"bytes": list(m.tobytes(op[2]))})
        if name == "hex":
            sep = None if op[2] is None else self.obj(op[2])[0]

            def hx():
                if op[2] is None:
                    return m.hex() if op[3] is None else m.hex(bytes_per_sep=op[3])
                return m.hex(sep) if op[3] is None else m.hex(sep, op[3])
            return py(hx)
        if name == "cast":
            sh = op[3]
            if sh == "notseq":
                sh_arg = (5,)
            elif sh is None:
                sh_arg = ()
            else:
                sh_arg = ([self.obj(x)[0] for x in sh],)
            return py(lambda: self.reg(m.cast(op[2], *sh_arg)))
        if name == "toreadonly":
            return py(lambda: self.reg(m.toreadonly()))
        if name == "release":
            return py(lambda: m.release())
        if name == "enter":
            return py(lambda: {"same": m.__enter__() is m})
        if name == "exit":
            return py(lambda: m.__exit__(None, None, None))
        if name == "cmp":
            w = self.obj(op[2])
            if w is None:
                return skip

            def cmp():
                f = {"eq": m.__eq__, "ne": m.__ne__, "lt": m.__lt__}[op[3]]
                r = f(w[0])
                return {"notimpl": True} if r is NotImplemented else {"bool": r}
            return py(cmp)
        if name == "hash":
            def hs():
                h = hash(m)
                if h not in self.hashed:
                    b = m.tobytes()
                    assert hash(b) == h
                    self.hashed[h] = list(b)
                return {"hash": self.hashed[h]}
            return py(hs)
        if name == "count":
            v = self.obj(op[2])
            return py(lambda: m.count(v[0]))
        if name == "index":
            v = self.obj(op[2])
            a = 0 if op[3] is None else op[3]
            b = _M if op[4] is None else op[4]
            return py(lambda: m.index(v[0], a, b))
        if name == "iter":
            def mk():
                self.iters.append(iter(m))
            return py(mk)
        if name == "attr":
            def at():
                r = getattr(m, op[2])
                if op[2] == "obj":
                    for x, e in enumerate(self.exps):
                        if r is e:
                            return {"exp": x}
                    for x, e in enumerate(self.handles):
                        if r is e:
                            return {"mv": x}
                    if isinstance(r, bytes):
                        return {"exp": 1000000}    # a temporary bytes object
                    return None if r is None else {"unknown": repr(r)}
                if isinstance(r, bool):
                    return {"bool": r}
                return list(r) if isinstance(r, tuple) else r
            return py(at)
        if name == "repr":
            return py(lambda: repr(m).split(" at ")[0])
        if name == "weak":
            fire = self.rel({"rel": op[2]})
            self.weak.append(weakref.ref(m, lambda _: fire()))
            return {"ok": None}
        if name == "drop":
            del m
            if sys.getrefcount(self.handles[i]) != 2:
                return skip
            self.handles[i] = _Gone()
            self.dropped.add(i)
            return {"ok": None}
        if name == "buffer":
            return py(lambda: self.reg(m.__buffer__(op[2])))
        if name == "toc":
            return py(lambda: {"bytes": list(_tb.py_buffer_to_contiguous(m, op[2], _tb.PyBUF_FULL_RO))})
        if name == "iscontig":
            return py(lambda: {"bool": bool(_tb.is_contiguous(m, op[2]))})
        raise KeyError(name)


def _run_restricted(ex):
    """What `__release_buffer__` of a subclass of a C exporter can do with its view, which
    is restricted when no Python `__buffer__` made it (Objects/typeobject.c:11535-11548)."""
    out = []

    def probe(f):
        def run():
            f()
            return True
        out.append(common.py_result(run))

    class R(bytearray):
        def __release_buffer__(self, view):
            probe(lambda: view.cast("B"))
            probe(view.toreadonly)
            probe(lambda: memoryview(view))
            probe(lambda: view[:])
            probe(lambda: view.__buffer__(0))
            out.append(common.py_result(lambda: len(view)))

    m = memoryview(R(bytes(ex)))
    m.release()
    return out


def run_mem(case):
    fn = case["fn"]
    if fn == "mem.script":
        s = _Script(case)
        saved = sys.modules.get("struct")
        if case.get("nostruct"):
            sys.modules["struct"] = None
        try:
            out = [s.step(op) for op in case["ops"]]
        finally:
            sys.modules["struct"] = saved
        for r in out:
            if r.get("exc") == "UnicodeEncodeError":
                r["msg"] = "~'ascii' codec can't encode"
        return {"ok": out}
    if fn == "mem.narrow32":
        return {"ok": struct.unpack("<I", bytes(_ct.c_float(_unfbits(case["d"]))))[0]}
    if fn == "mem.widen32":
        return {"ok": _fbits(_ct.c_float.from_buffer_copy(struct.pack("<I", case["x"])).value)}
    if fn == "mem.pack2":
        try:
            return {"ok": struct.unpack("<H", struct.pack("<e", _unfbits(case["d"])))[0]}
        except OverflowError:
            return {"exc": "OverflowError", "msg": "float too large to pack with 'e' format"}
    if fn == "mem.unpack2":
        return {"ok": _fbits(struct.unpack("<e", struct.pack("<H", case["x"]))[0])}
    if fn == "mem.long2d":
        return common.py_result(lambda: _fbits(float(case["n"])))
    if fn == "mem.deqint":
        return {"ok": _unfbits(case["d"]) == case["n"]}
    return _run_mem_fmt(fn, case["fmt"])


def _run_mem_fmt(fn, fmt):
    """`get_native_fmtchar` and `get_native_fmtstr` as `cast` shows them; a length that does not
    divide would fail, so the buffer has 16 bytes, the largest item."""
    m = memoryview(bytes(16))
    try:
        c = m.cast(fmt)
    except (ValueError, UnicodeEncodeError):
        return {"ok": None}
    return {"ok": [c.format.lstrip("@"), c.itemsize] if fn == "mem.fmtchar" else c.format}


# ===== end of family mem ==============================================


# ===== family bare: bytearray under callbacks that change it ===========
#
# lean/PyLean/BytesObj/Bytes/Heap.lean models a bytearray that Python callbacks change while a C
# function runs; HeapDiff.lean is the handler. A case has the initial bytes `s`, statements `prep`
# run first, the operation and its arguments. A statement acts on the target `BA_T[0]`:
# ["set", i, v] is `ba[i] = v`, ["resize", n] `ba.resize(n)`, ["del", k] `del ba[:k]`, ["grab"]
# keeps `memoryview(ba)`, ["drop"] releases the last kept view; each in try/except. The answer is
# the result and the object afterwards: contents, __alloc__(), ob_start - ob_bytes, ob_exports and
# the number of kept views. A strip whose __release_buffer__ resizes the object reads freed memory:
# it runs in a forked child, and a non-empty result or a signal is reported as undefined behaviour.

import json as _json
import os as _os


class _PyByteArrayObject(ctypes.Structure):
    _fields_ = [("ob_refcnt", ctypes.c_ssize_t), ("ob_type", ctypes.c_void_p),
                ("ob_size", ctypes.c_ssize_t), ("ob_alloc", ctypes.c_ssize_t),
                ("ob_bytes", ctypes.c_void_p), ("ob_start", ctypes.c_void_p),
                ("ob_exports", ctypes.c_ssize_t), ("ob_bytes_object", ctypes.c_void_p)]


def _raw(ba):
    return _PyByteArrayObject.from_address(id(ba))


BA_T = [None]
VIEWS = []
HAZARD = [False]
KEEP = []
CODEC = [None]


def _layout(ba):
    r = _raw(ba)
    return (len(ba), ba.__alloc__(), (r.ob_start or 0) - (r.ob_bytes or 0))


def run_acts(acts):
    ba = BA_T[0]
    for a in acts:
        try:
            k = a[0]
            if k == "set":
                ba[a[1]] = a[2]
            elif k == "resize":
                ba.resize(a[1])
            elif k == "del":
                del ba[:a[1]]
            elif k == "grab":
                VIEWS.append(memoryview(ba))
            elif k == "drop":
                if VIEWS:
                    VIEWS.pop().release()
        except Exception:
            pass


def _exc(e):
    return {"TypeError": TypeError, "ValueError": ValueError, "OverflowError": OverflowError,
            "TSub": TSub, "BBoom": BBoom, "StopIteration": StopIteration}[e[0]](e[1])


class RIdx:
    def __init__(self, acts, res):
        self.acts, self.res = acts, res

    def __index__(self):
        run_acts(self.acts)
        if self.res[0] == "exc":
            raise _exc(self.res[1:])
        return self.res[1]


class RBuf:
    def __init__(self, acts, res, rel):
        self.acts, self.res, self.rel = acts, res, rel

    def __buffer__(self, flags):
        run_acts(self.acts)
        if self.res[0] == "exc":
            raise _exc(self.res[1:])
        return memoryview(bytes(self.res[1]))

    def __release_buffer__(self, view):
        before = _layout(BA_T[0])
        run_acts(self.rel)
        if _layout(BA_T[0]) != before:
            HAZARD[0] = True


class RBool:
    def __init__(self, acts, res):
        self.acts, self.res = acts, res

    def __bool__(self):
        run_acts(self.acts)
        if self.res[0] == "exc":
            raise _exc(self.res[1:])
        return self.res[1]


class RLen(bytes):
    def __len__(self):
        run_acts(self.acts)
        if self.res[0] == "exc":
            raise _exc(self.res[1:])
        return self.res[1]


class RIt:
    def __init__(self, steps, fin_acts, fin):
        self.steps, self.fin_acts, self.fin, self.i = steps, fin_acts, fin, 0

    def __iter__(self):
        return self

    def __next__(self):
        if self.i < len(self.steps):
            acts, item = self.steps[self.i]
            self.i += 1
            run_acts(acts)
            return bare_build(item)
        run_acts(self.fin_acts)
        if self.fin is None:
            raise StopIteration
        raise _exc(self.fin)


def bare_build(a):
    t = a[0]
    if t == "obj":
        return b_build(a[1])
    if t == "idx":
        return RIdx(a[1], a[2])
    if t == "buf":
        return RBuf(a[1], a[2], a[3])
    if t == "slen":
        x = RLen(bytes(a[3]))
        x.acts, x.res = a[1], a[2]
        return x
    if t == "it":
        return RIt(a[1], a[2], a[3])
    if t == "me":
        return BA_T[0]
    raise ValueError(t)


def _rc_encode(s, errors="strict"):
    acts, res, unique = CODEC[0]
    run_acts(acts)
    if res[0] == "exc":
        raise _exc(res[1:])
    b = bytes(bytearray(res[1]))
    if not unique:
        KEEP.append(b)
    return (b, len(s))


def _rc_decode(b, errors="strict"):
    return (str(b, "latin-1"), len(b))


codecs.register(lambda name: codecs.CodecInfo(_rc_encode, _rc_decode, name="rcodec")
                if name == "rcodec" else None)

_PSSI = ctypes.pythonapi.PySequence_SetItem
_PSSI.argtypes = [ctypes.py_object, ctypes.c_ssize_t, ctypes.py_object]
_PSSI.restype = ctypes.c_int
_PSDI = ctypes.pythonapi.PySequence_DelItem
_PSDI.argtypes = [ctypes.py_object, ctypes.c_ssize_t]
_PSDI.restype = ctypes.c_int


class _Raw(list):
    """An answer already in JSON form."""


def bare_enc(v):
    if isinstance(v, _Raw):
        return list(v)
    if isinstance(v, (bytes, bytearray)):
        return list(v)
    if isinstance(v, str):
        return [ord(c) for c in v]
    if isinstance(v, (list, tuple)):
        return [bare_enc(x) for x in v]
    if v is NotImplemented:
        return "NotImplemented"
    return v


def _opt(c, k):
    v = c.get(k)
    return None if v is None else bare_build(v)


def bare_op(c, ba):
    op = c["fn"][5:]
    if op in ("find", "rfind", "index", "rindex", "count"):
        args = [bare_build(c["sub"])]
        if c.get("start") is not None or c.get("end") is not None:
            args.append(_opt(c, "start"))
        if c.get("end") is not None:
            args.append(_opt(c, "end"))
        return getattr(ba, op)(*args)
    if op in ("startswith", "endswith"):
        k, x = c["sub"]
        sub = bare_build(x) if k == "one" else tuple(bare_build(y) for y in x)
        args = [sub]
        if c.get("start") is not None or c.get("end") is not None:
            args.append(_opt(c, "start"))
        if c.get("end") is not None:
            args.append(_opt(c, "end"))
        return getattr(ba, op)(*args)
    if op == "contains":
        return bare_build(c["sub"]) in ba
    if op in ("strip", "lstrip", "rstrip"):
        return getattr(ba, op)(*([] if c.get("arg") is None else [bare_build(c["arg"])]))
    if op in ("getitem", "setsub"):
        k = c["key"]
        if k[0] == "one":
            key = bare_build(k[1])
        else:
            key = slice(*[None if x is None else bare_build(x) for x in k[1:]])
        if op == "getitem":
            r = ba[key]
            return _Raw(["slice", list(r)] if isinstance(r, bytearray) else ["byte", r])
        if c.get("value") is None:
            del ba[key]
        else:
            ba[key] = bare_build(c["value"])
        return None
    if op == "sqset":
        if c.get("value") is None:
            _PSDI(ba, c["i"])
        else:
            _PSSI(ba, c["i"], bare_build(c["value"]))
        return None
    if op == "insert":
        return ba.insert(bare_build(c["index"]), bare_build(c["item"]))
    if op == "append":
        return ba.append(bare_build(c["item"]))
    if op == "remove":
        return ba.remove(bare_build(c["item"]))
    if op == "pop":
        return ba.pop(*([] if c.get("index") is None else [bare_build(c["index"])]))
    if op == "take":
        return ba.take_bytes(*([] if c.get("n") is None else [bare_build(c["n"])]))
    if op == "iadd":
        ba.__iadd__(bare_build(c["other"]))
        return None
    if op == "add":
        return ba + bare_build(c["other"])
    if op == "extend":
        return ba.extend(bare_build(c["x"]))
    if op == "init":
        args = [] if c.get("x") is None else [bare_build(c["x"])]
        kw = {}
        if c.get("enc") is not None:
            e = c["enc"]
            kw["encoding"] = e[1]
            if e[0] == "py":
                CODEC[0] = (e[2], e[3], e[4])
        if c.get("err") is not None:
            kw["errors"] = c["err"]
        return ba.__init__(*args, **kw)
    if op == "translate":
        args = [bare_build(c["table"])]
        if c.get("del") is not None:
            args.append(bare_build(c["del"]))
        return ba.translate(*args)
    if op in ("split", "rsplit"):
        kw = {}
        if c.get("sep") is not None:
            kw["sep"] = bare_build(c["sep"])
        if c.get("maxsplit") is not None:
            kw["maxsplit"] = bare_build(c["maxsplit"])
        return getattr(ba, op)(**kw)
    if op in ("partition", "rpartition"):
        return getattr(ba, op)(bare_build(c["sep"]))
    if op == "hex":
        kw = {}
        if c.get("sep") is not None:
            kw["sep"] = bare_build(c["sep"])
        if c.get("bps") is not None:
            kw["bytes_per_sep"] = bare_build(c["bps"])
        return ba.hex(**kw)
    if op == "join":
        return ba.join(bare_build(c["it"]))
    if op == "rich":
        return getattr(ba, "__%s__" % c["cmp"])(bare_build(c["other"]))
    if op in ("center", "ljust", "rjust"):
        args = [bare_build(c["width"])]
        if c.get("fill") is not None:
            args.append(bare_build(c["fill"]))
        return getattr(ba, op)(*args)
    if op in ("pred", "map"):
        return getattr(ba, c["name"])()
    if op == "resize":
        return ba.resize(bare_build(c["n"]))
    if op == "zfill":
        return ba.zfill(bare_build(c["width"]))
    if op == "replace":
        args = [bare_build(c["old"]), bare_build(c["new"])]
        if c.get("count") is not None:
            args.append(bare_build(c["count"]))
        return ba.replace(*args)
    if op == "expandtabs":
        return ba.expandtabs(*([] if c.get("tabsize") is None else [bare_build(c["tabsize"])]))
    if op == "splitlines":
        k = c.get("keepends")
        if k is None:
            return ba.splitlines()
        if k[0] == "tobj":
            return ba.splitlines(k[1])
        if k[0] == "tcls":
            return ba.splitlines(RBool(k[1], k[2]))
        return ba.splitlines(ba)
    raise ValueError(op)


def _bare_once(c):
    ba = bytearray(c["s"])
    BA_T[0] = ba
    VIEWS.clear()
    KEEP.clear()
    HAZARD[0] = False
    run_acts(c["prep"])
    try:
        inner = {"ok": bare_enc(bare_op(c, ba))}
    except Exception as e:
        inner = {"exc": type(e).__name__, "msg": "~" if isinstance(e, UnicodeEncodeError) else str(e)}
    if HAZARD[0] and inner.get("ok") and c["fn"] in ("bare.strip", "bare.lstrip", "bare.rstrip"):
        return {"exc": "CUndefinedBehaviour", "msg": "read after a resize in __release_buffer__"}
    r = _raw(ba)
    st = [list(ba), ba.__alloc__(), (r.ob_start or 0) - (r.ob_bytes or 0), r.ob_exports, len(VIEWS)]
    for v in VIEWS:
        v.release()
    VIEWS.clear()
    KEEP.clear()
    return {"ok": [inner, st]}


def _in_child(c):
    rfd, wfd = _os.pipe()
    pid = _os.fork()
    if pid == 0:
        _os.close(rfd)
        try:
            out = _bare_once(c)
        except BaseException as e:
            out = {"exc": "Harness", "msg": repr(e)}
        _os.write(wfd, _json.dumps(out).encode())
        _os._exit(0)
    _os.close(wfd)
    data = b""
    while True:
        chunk = _os.read(rfd, 65536)
        if not chunk:
            break
        data += chunk
    _os.close(rfd)
    _, status = _os.waitpid(pid, 0)
    if _os.WIFSIGNALED(status):
        return {"exc": "CUndefinedBehaviour", "msg": "signal %d" % _os.WTERMSIG(status)}
    return _json.loads(data)


def run_bare(c):
    if c.get("fork"):
        return _in_child(c)
    return _bare_once(c)


# --- generation ---

_BARE_ALPHA = [32, 32, 9, 10, 97, 97, 98, 120, 0, 255, 122, 13, 43]


def _bseq(rng, lo=0, hi=10):
    return [rng.choice(_BARE_ALPHA) for _ in range(rng.randint(lo, hi))]


def _bact(rng, resize=True):
    k = rng.choice(["set", "set", "resize", "del", "grab", "drop"] if resize else ["set", "set", "grab", "drop"])
    if k == "set":
        return ["set", rng.randint(-3, 6), rng.choice([0, 32, 97, 120, 255, 256, -1])]
    if k == "resize":
        return ["resize", rng.choice([0, 0, 1, 2, 3, 5, 8, 13, 20, 40, -1, 2 ** 63])]
    if k == "del":
        return ["del", rng.randint(-2, 5)]
    return [k]


def _bacts(rng, resize=True, n=3):
    return [_bact(rng, resize) for _ in range(rng.randint(0, n))]


def _bexc(rng):
    return ["exc"] + rng.choice([["TypeError", "bad"], ["ValueError", "bad"], ["TSub", "sub"],
                                 ["BBoom", "boom"], ["OverflowError", "big"]])


def _bint_res(rng, vals):
    return _bexc(rng) if rng.random() < 0.12 else ["ok", rng.choice(vals)]


_SMALLV = [0, 1, 2, 3, -1, -2, 97, 120, 32, 255, 256, 2 ** 63, -2 ** 63 - 1, 5, 7]


def _barg(rng, kinds, vals=_SMALLV, bufs=None, resize=True):
    k = rng.choice(kinds)
    if k == "int":
        return ["obj", ["int", rng.choice(vals)]]
    if k == "none":
        return ["obj", ["none"]]
    if k == "bytes":
        return ["obj", ["bytes", rng.choice(bufs) if bufs else _bseq(rng, 0, 3)]]
    if k == "bytearray":
        return ["obj", ["bytearray", rng.choice(bufs) if bufs else _bseq(rng, 0, 3)]]
    if k == "str":
        return ["obj", ["str", rng.choice([[], [97], [97, 98], [32], [233], [0x263a]])]]
    if k == "float":
        return ["obj", b_bflt(rng.choice([1.5, 0.0]))]
    if k == "list":
        return ["obj", ["list", [["int", rng.choice([0, 97, 255, 256, -1])] for _ in range(rng.randint(0, 3))]]]
    if k == "idx":
        return ["idx", _bacts(rng, resize), _bint_res(rng, vals)]
    if k == "buf":
        res = _bexc(rng) if rng.random() < 0.1 else ["ok", rng.choice(bufs) if bufs else _bseq(rng, 0, 3)]
        return ["buf", _bacts(rng, resize), res, _bacts(rng, resize)]
    if k == "slen":
        return ["slen", _bacts(rng, resize), _bint_res(rng, [1, 1, 0, 2, -1]), rng.choice([[58], [32], [200], [], [58, 58]])]
    if k == "me":
        return ["me"]
    if k == "it":
        def item():
            j = rng.choice(["int", "int", "idx", "buf", "me", "bytes"])
            if j == "int":
                return ["obj", ["int", rng.choice([0, 97, 120, 255, 256, -1])]]
            if j == "bytes":
                return ["obj", ["bytes", _bseq(rng, 0, 3)]]
            if j == "idx":
                return ["idx", _bacts(rng, resize, 2), _bint_res(rng, [0, 97, 255, 256])]
            if j == "buf":
                return ["buf", _bacts(rng, resize, 2), ["ok", _bseq(rng, 0, 3)], _bacts(rng, resize, 2)]
            return ["me"]
        steps = [[_bacts(rng, resize, 2), item()] for _ in range(rng.randint(0, 4))]
        fin = None if rng.random() < 0.85 else rng.choice([["ValueError", "end"], ["StopIteration", ""], ["TSub", "t"]])
        return ["it", steps, _bacts(rng, resize, 2), fin]
    raise ValueError(k)


_BARE_OPS = ["find", "rfind", "index", "rindex", "count", "startswith", "endswith", "contains",
             "strip", "lstrip", "rstrip", "getitem", "setsub", "sqset", "insert", "append", "remove",
             "pop", "take", "iadd", "add", "extend", "init", "translate", "split", "rsplit",
             "partition", "rpartition", "hex", "join", "rich", "center", "ljust", "rjust", "zfill",
             "replace", "expandtabs", "splitlines", "pred", "map", "resize"]


def gen_bare(rng):
    op = rng.choice(_BARE_OPS)
    c = {"mod": "bytesobj", "fn": "bare." + op, "s": _bseq(rng),
         "prep": [rng.choice([["del", rng.randint(0, 4)], ["resize", rng.choice([0, 3, 12, 30])],
                              ["grab"], ["set", 0, 120], ["drop"]]) for _ in range(rng.choice([0, 0, 1, 2, 3]))]}
    idx_kinds = ["int", "int", "idx", "idx", "none", "bytes", "float"]
    sub_kinds = ["int", "bytes", "bytearray", "idx", "buf", "me", "str", "none", "slen"]
    if op in ("find", "rfind", "index", "rindex", "count"):
        c["sub"] = _barg(rng, sub_kinds, vals=[97, 32, 120, 0, 255, 256, -1, 2 ** 63])
        if rng.random() < 0.5:
            c["start"] = _barg(rng, idx_kinds, vals=[0, 1, -1, -3, 2, 100, 2 ** 63])
        if rng.random() < 0.4:
            c["end"] = _barg(rng, idx_kinds, vals=[0, 1, -1, 3, 100, -2 ** 63 - 1])
    elif op in ("startswith", "endswith"):
        if rng.random() < 0.3:
            c["sub"] = ["tuple", [_barg(rng, ["bytes", "buf", "me", "int", "slen"]) for _ in range(rng.randint(0, 3))]]
        else:
            c["sub"] = ["one", _barg(rng, ["bytes", "buf", "me", "int", "str", "bytearray", "slen"])]
        if rng.random() < 0.5:
            c["start"] = _barg(rng, idx_kinds, vals=[0, 1, -1, -3, 2, 100])
        if rng.random() < 0.4:
            c["end"] = _barg(rng, idx_kinds, vals=[0, 1, -1, 3, 100])
    elif op == "contains":
        c["sub"] = _barg(rng, sub_kinds, vals=[97, 32, 120, 0, 255, 256, -1, 2 ** 63])
    elif op in ("strip", "lstrip", "rstrip"):
        if rng.random() < 0.85:
            a = _barg(rng, ["buf", "buf", "buf", "bytes", "me", "none", "int", "bytearray"],
                      bufs=[[32], [32, 9], [97], [120, 32], [], [10, 32, 97]], resize=False)
            if a[0] == "buf" and rng.random() < 0.3:
                a[3] = a[3] + [["resize", 0]]
                c["fork"] = True
            c["arg"] = a
    elif op in ("getitem", "setsub"):
        if rng.random() < 0.5:
            c["key"] = ["one", _barg(rng, ["int", "idx", "idx", "str", "none"], vals=[0, 1, 2, -1, -2, 5, 2 ** 63])]
        else:
            c["key"] = ["slice"] + [None if rng.random() < 0.4 else
                                    _barg(rng, ["int", "idx", "str"], vals=[0, 1, 2, -1, -3, 5, 0, 2, -2])
                                    for _ in range(3)]
        if op == "setsub" and rng.random() < 0.85:
            c["value"] = _barg(rng, ["int", "idx", "bytes", "bytearray", "buf", "me", "it", "str", "list", "float"],
                               vals=[0, 97, 255, 256, -1])
    elif op == "sqset":
        c["i"] = rng.choice([0, 1, 2, -1, -2, 5, -20])
        if rng.random() < 0.8:
            c["value"] = _barg(rng, ["int", "idx", "idx", "float"], vals=[0, 97, 255, 256, -1])
    elif op == "insert":
        c["index"] = _barg(rng, ["int", "idx", "float"], vals=[0, 1, -1, 2, 100, -100, 2 ** 63])
        c["item"] = _barg(rng, ["int", "idx", "float"], vals=[0, 97, 255, 256, -1])
    elif op in ("append", "remove"):
        c["item"] = _barg(rng, ["int", "idx", "idx", "float", "bytes"], vals=[0, 97, 120, 32, 255, 256, -1])
    elif op == "pop":
        if rng.random() < 0.8:
            c["index"] = _barg(rng, ["int", "idx", "idx"], vals=[0, 1, -1, 2, 100, -100, 2 ** 63])
    elif op == "take":
        if rng.random() < 0.8:
            c["n"] = _barg(rng, ["int", "idx", "idx", "none", "str"], vals=[0, 1, 2, -1, -2, 3, 100, 2 ** 63])
    elif op in ("iadd", "add"):
        c["other"] = _barg(rng, ["bytes", "bytearray", "buf", "buf", "me", "int", "str", "idx"])
    elif op == "extend":
        c["x"] = _barg(rng, ["it", "it", "it", "buf", "me", "bytes", "list", "idx", "str", "int"])
    elif op == "init":
        k = rng.random()
        if k < 0.3:
            c["x"] = ["obj", ["str", rng.choice([[97, 98, 99], [97], [], [104, 105], [233, 97]])]]
            if rng.random() < 0.9:
                if rng.random() < 0.4:
                    c["enc"] = ["builtin", rng.choice(["ascii", "latin-1"])]
                else:
                    res = ["ok", _bseq(rng, 0, 4)] if rng.random() < 0.9 else _bexc(rng)
                    c["enc"] = ["py", "rcodec", _bacts(rng), res, rng.random() < 0.6]
        elif k < 0.95:
            c["x"] = _barg(rng, ["it", "it", "idx", "buf", "me", "bytes", "list", "int", "float", "none"],
                           vals=[0, 1, 3, -1, 2 ** 63])
            if rng.random() < 0.05:
                c["enc"] = ["builtin", "ascii"]
        if rng.random() < 0.05:
            c["err"] = "strict"
    elif op == "translate":
        tables = [list(range(256)), [(i + 1) % 256 for i in range(256)], [97] * 256, [1, 2]]
        c["table"] = rng.choice([["obj", ["none"]], ["obj", ["bytes", rng.choice(tables)]],
                                 _barg(rng, ["buf", "me", "int"], bufs=tables)])
        if rng.random() < 0.5:
            c["del"] = _barg(rng, ["bytes", "buf", "me", "int"], bufs=[[], [97], [32, 120]])
    elif op in ("split", "rsplit"):
        if rng.random() < 0.8:
            c["sep"] = _barg(rng, ["bytes", "buf", "buf", "me", "none", "int"], bufs=[[32], [97], [], [97, 98], [120]])
        if rng.random() < 0.4:
            c["maxsplit"] = _barg(rng, ["int", "idx"], vals=[-1, 0, 1, 2, 2 ** 63])
    elif op in ("partition", "rpartition"):
        c["sep"] = _barg(rng, ["bytes", "buf", "buf", "me", "int", "str"], bufs=[[32], [97], [], [97, 98], [120]])
    elif op == "hex":
        if rng.random() < 0.7:
            c["sep"] = rng.choice([["obj", ["str", [58]]], ["obj", ["bytes", [32]]], ["obj", ["str", [233]]],
                                   ["obj", ["none"]], ["obj", ["int", 1]],
                                   _barg(rng, ["slen", "slen", "me"])])
        if rng.random() < 0.5:
            c["bps"] = _barg(rng, ["int", "idx"], vals=[1, 2, -1, -2, 0, 3, 2 ** 63])
    elif op == "join":
        if rng.random() < 0.7:
            c["it"] = _barg(rng, ["it"])
        else:
            c["it"] = ["obj", ["list", [["bytes", _bseq(rng, 0, 2)] for _ in range(rng.randint(0, 3))]]]
    elif op == "rich":
        c["other"] = _barg(rng, ["bytes", "bytearray", "buf", "buf", "me", "int", "str"])
        c["cmp"] = rng.choice(["eq", "ne", "lt", "le", "gt", "ge"])
    elif op in ("center", "ljust", "rjust", "zfill"):
        c["width"] = _barg(rng, ["int", "idx", "idx", "float"], vals=[0, 1, 3, 5, 8, 12, -1, 2 ** 63])
        if op != "zfill" and rng.random() < 0.8:
            k = rng.random()
            if k < 0.4:
                c["fill"] = ["obj", ["bytes", [rng.choice([32, 42, 0, 255])]]]
            elif k < 0.5:
                c["fill"] = ["obj", ["bytearray", [rng.choice([42, 200])]]]
            elif k < 0.6:
                c["fill"] = ["obj", [rng.choice(["bytes", "bytearray"]), rng.choice([[], [42, 42], [1, 2, 3]])]]
            elif k < 0.75:
                c["fill"] = ["me"]
            elif k < 0.85:
                c["fill"] = ["slen", _bacts(rng), ["ok", rng.choice([1, 2])], rng.choice([[42], [], [42, 43]])]
            else:
                c["fill"] = rng.choice([["obj", ["none"]], ["obj", ["int", 42]], ["obj", ["str", [42]]],
                                        ["obj", ["memview", [42], []]]])
    elif op == "replace":
        c["old"] = _barg(rng, ["bytes", "buf", "buf", "me", "int"], bufs=[[32], [97], [], [97, 98], [120]])
        c["new"] = _barg(rng, ["bytes", "buf", "me", "int"], bufs=[[], [122], [122, 122]])
        if rng.random() < 0.4:
            c["count"] = _barg(rng, ["int", "idx"], vals=[-1, 0, 1, 2, 2 ** 63])
    elif op == "expandtabs":
        if rng.random() < 0.8:
            c["tabsize"] = _barg(rng, ["int", "idx", "idx", "float"], vals=[0, 1, 4, 8, -1, 2 ** 31, 2 ** 63])
    elif op == "splitlines":
        k = rng.random()
        if k < 0.25:
            pass
        elif k < 0.5:
            c["keepends"] = ["tobj", rng.random() < 0.5]
        elif k < 0.85:
            res = _bexc(rng) if rng.random() < 0.15 else ["ok", rng.random() < 0.5]
            c["keepends"] = ["tcls", _bacts(rng), res]
        else:
            c["keepends"] = ["me"]
        if rng.random() < 0.5:
            c["s"] = [rng.choice([10, 13, 97, 32]) for _ in range(rng.randint(0, 8))]
    elif op == "resize":
        c["n"] = _barg(rng, ["int", "int", "idx", "idx", "float"], vals=[0, 1, 2, 3, 5, 8, 9, 12, 20, 40, -1, 2 ** 63])
    elif op == "pred":
        c["name"] = rng.choice(["isalnum", "isalpha", "isascii", "isdigit", "islower", "isspace", "istitle",
                                "isupper"])
        c["s"] = [rng.choice([65, 97, 48, 32, 9, 200, 90, 122, 64, 91, 96, 123, 47, 58, 13, 11, 127, 128])
                  for _ in range(rng.randint(0, 6))]
    elif op == "map":
        c["name"] = rng.choice(["capitalize", "swapcase", "title", "upper", "lower"])
        c["s"] = [rng.choice([65, 97, 48, 32, 200, 90, 122, 64, 91, 96, 123, 39])
                  for _ in range(rng.randint(0, 6))]
    return c


# ===== end of family bare =============================================


FAMILIES = {"seq": (gen_seq, run_seq), "bytes": (gen_bytes, run_bytes), "mem": (gen_mem, run_mem),
            "bare": (gen_bare, run_bare)}
PREFIXES = {"tuple": "seq", "list": "seq", "bytes": "bytes", "bytearray": "bytes", "mem": "mem", "bare": "bare"}


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
