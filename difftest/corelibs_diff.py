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
misc_gen = None  # replace with def misc_gen(rng) -> case dict with "fn": "misc.<name>"
misc_run = None  # replace with def misc_run(case) -> common.py_result-style dict
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
