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
coll_gen = None  # replace with def coll_gen(rng) -> case dict with "fn": "coll.<name>"
coll_run = None  # replace with def coll_run(case) -> common.py_result-style dict
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


MISC_GENS = [misc_gen_graphlib, misc_gen_sched, misc_gen_queue, misc_gen_numbers,
             misc_gen_keyword, misc_gen_types]
MISC_RUNS = {"misc.graphlib": misc_run_graphlib, "misc.sched": misc_run_sched,
             "misc.queue": misc_run_queue, "misc.numbers": misc_run_numbers,
             "misc.keyword": misc_run_keyword, "misc.types": misc_run_types}


def misc_gen(rng):
    return rng.choice(MISC_GENS)(rng)


def misc_run(case):
    return MISC_RUNS[case["fn"]](case)
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
