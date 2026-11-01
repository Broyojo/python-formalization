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
