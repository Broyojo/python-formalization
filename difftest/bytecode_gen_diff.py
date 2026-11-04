"""Differential test for Objects/genobject.c.

Real generators, coroutines and async generators are built from small scripts
(lists of actions: yield, yield from/await, return, raise, try/except, try/finally,
loops, reentrant calls) and driven through random sequences of next, send, throw,
close, asend, athrow and aclose. After every operation the outcome, message and
state flags are compared with the Lean model running the same script
(lean/PyLean/Bytecode/GenObj/Script.lean), along with a trace of everything the
body and its sub-iterators did.
"""

import gc
import inspect
import json
import re
import sys
import threading
import types
import warnings
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import main


class MyGE(GeneratorExit):
    pass


class MySI(StopIteration):
    pass


class MySAI(StopAsyncIteration):
    pass


class Ctx:
    trace = []
    top = None
    held = []
    keep = []
    fib = 0
    finb = 0
    ncases = 0


C = Ctx()


def log(s):
    C.trace.append(s)


def r(x):
    if x is None:
        return "None"
    if isinstance(x, str):
        return x
    if isinstance(x, int):
        return str(x)
    if isinstance(x, (types.GeneratorType, types.CoroutineType, types.AsyncGeneratorType)):
        return "<gen>"
    if isinstance(x, type):
        return x.__name__
    if isinstance(x, BaseException):
        return type(x).__name__
    name = type(x).__name__
    if name == "It":
        return "<foreign>"
    if name == "async_generator_wrapped_value":
        return "<wrapped>"
    return name


def running(t):
    if isinstance(t, types.GeneratorType):
        return t.gi_running
    if isinstance(t, types.CoroutineType):
        return t.cr_running
    return t.ag_running


def rop(op, target):
    t = op[0]
    try:
        if t == "next":
            v = next(target)
        elif t == "send":
            v = target.send(op[1])
        elif t == "close":
            v = target.close()
        elif t == "throw":
            v = target.throw(CLS[op[1]])
        elif t == "flags":
            v = None
        elif t == "anext":
            v = target.__anext__().send(None)
        elif t == "asend":
            v = target.asend(op[1]).send(None)
        elif t == "aclose":
            v = target.aclose().send(None)
        elif t == "athrow":
            v = target.athrow(CLS[op[1]]).send(None)
        elif t == "hsend":
            v = C.held[op[1]].send(None) if op[1] < len(C.held) else None
        elif t == "hthrow":
            v = C.held[op[1]].throw(CLS[op[2]]) if op[1] < len(C.held) else None
        elif t == "hclose":
            v = C.held[op[1]].close() if op[1] < len(C.held) else None
        else:
            raise AssertionError(t)
        res = "ok:" + r(v)
    except BaseException as e:
        res = f"exc:{type(e).__name__}:{e}"
    log(f"re:{t}:{res}:{1 if running(target) else 0}")


class ReInit(Exception):
    """Its constructor, run by PyErr_NormalizeException when the class is thrown, calls next() on
    the top object: Python code inside gen_set_exception (Objects/genobject.c:566)."""

    def __init__(self, *a):
        t = C.top
        rop(["anext"] if isinstance(t, types.AsyncGeneratorType)
            else ["send", 1] if isinstance(t, types.CoroutineType) else ["next"], t)
        super().__init__(*a)


CLS = {c.__name__: c for c in [ReInit, 
    ValueError, KeyError, RuntimeError, StopIteration, StopAsyncIteration, GeneratorExit,
    MyGE, MySI, MySAI, BaseException, Exception, LookupError]}

try:
    raise ValueError
except ValueError as _e:
    TB = _e.__traceback__

REOPS = [["next"], ["send", 1], ["close"], ["throw", "ValueError"], ["flags"],
         ["anext"], ["aclose"], ["athrow", "ValueError"]]


def attr_raises(exc, msg):
    def get(self):
        raise exc(msg)
    return property(get)


def attr_reenters():
    """An attribute whose lookup runs Python code on the delegating generator and then
    says it is not there. On 3.15 the generator is FRAME_EXECUTING during the lookup."""
    def get(self):
        if self.reent is not None:
            rop(REOPS[self.reent], C.top)
        raise AttributeError("no")
    return property(get)


def make_it_class(has_send, throw_b, close_b):
    def __next__(self):
        log("f.next")
        return self.step()

    def step(self):
        if self.i < self.items:
            self.i += 1
            return 99 + self.i
        raise StopIteration(self.retv)

    def send(self, v):
        log("f.send:" + r(v))
        return self.step()

    def throw(self, typ, val=None, tb=None):
        log("f.throw:" + r(typ))
        if self.reent is not None:
            rop(REOPS[self.reent], C.top)
        if throw_b == 2:
            return 200
        if throw_b == 3:
            raise StopIteration(300)
        if throw_b == 4:
            raise RuntimeError("t")
        if isinstance(typ, type) and issubclass(typ, BaseException):
            raise typ() if val is None else typ(val)
        if isinstance(typ, BaseException):
            raise typ
        raise RuntimeError("bad typ")

    def close(self):
        log("f.close")
        if self.reent is not None:
            rop(REOPS[self.reent], C.top)
        if close_b == 2:
            raise ValueError("c")
        if close_b == 3:
            raise StopIteration(301)

    d = {"__iter__": lambda self: self, "__next__": __next__, "step": step}
    if has_send:
        d["send"] = send
    if throw_b in (1, 2, 3, 4):
        d["throw"] = throw
    elif throw_b == 5:
        d["throw"] = attr_raises(ValueError, "attr")
    elif throw_b == 6:
        d["throw"] = attr_raises(AttributeError, "no")
    elif throw_b == 7:
        d["throw"] = attr_reenters()
    if close_b in (1, 2, 3):
        d["close"] = close
    elif close_b == 4:
        d["close"] = attr_raises(ValueError, "attr")
    elif close_b == 5:
        d["close"] = attr_raises(AttributeError, "no")
    elif close_b == 6:
        d["close"] = attr_reenters()
    return type("It", (), d)


IT_CLASSES = {}


def make_it(spec):
    _, items, retv, hs, tb, cb, reent = spec
    key = (hs, tb, cb)
    cls = IT_CLASSES.get(key)
    if cls is None:
        cls = IT_CLASSES[key] = make_it_class(hs, tb, cb)
    o = cls()
    o.i = 0
    o.items = items
    o.retv = retv
    o.reent = reent
    return o


class Aw:
    def __init__(self, it):
        self.it = it

    def __await__(self):
        return self.it


async def _closed():
    pass


class Outer:
    """Nested, so that `%T` (Outer.BadAw) and `tp_name` (NoAw) differ in the messages of
    _PyCoro_GetAwaitableIter."""

    class BadAw:
        def __init__(self, k):
            self.k = k

        def __await__(self):
            if self.k == 1:
                c = _closed()
                c.close()
                return c
            if self.k == 2:
                return 3
            raise ValueError("aw")

    class NoAw:
        pass


def mk(spec, ctx):
    """Build the receiver of a `yield from` or `await`."""
    t = spec[0]
    if t == "s":
        cell = [None]
        o = compile_body(spec[1], "gen" if ctx == "gen" else "coro")(cell)
        cell[0] = o
    elif t == "c":
        cell = [None]
        o = types.coroutine(compile_body(spec[1], "gen"))(cell)
        cell[0] = o
    elif t == "f":
        it = make_it(spec)
        C.keep.append(it)
        return it if ctx == "gen" else Aw(it)
    else:
        o = 3 if spec[1] == 0 else Outer.NoAw() if spec[1] == 4 else Outer.BadAw(spec[1])
    C.keep.append(o)
    return o


G = dict(log=log, r=r, rop=rop, C=C, mk=mk, CLS=CLS, MyGE=MyGE, MySI=MySI, MySAI=MySAI)
FN_CACHE = {}


def emit(body, ind, ctx, out, subs):
    if not body:
        out.append(ind + "pass")
        return
    for a in body:
        t = a[0]
        if t == "y":
            out.append(f"{ind}x = yield {a[1]}")
            out.append(f"{ind}log('recv:'+r(x))")
        elif t == "yf":
            subs.append(a[1])
            kw = "yield from" if ctx == "gen" else "await"
            out.append(f"{ind}x = {kw} mk(SUBS[{len(subs) - 1}], {ctx!r})")
            out.append(f"{ind}log('yf:'+r(x))")
        elif t == "ret":
            out.append(f"{ind}return {'' if ctx == 'agen' or a[1] is None else a[1]}")
        elif t == "raise":
            out.append(f"{ind}raise {a[1]}('m')")
        elif t == "try":
            out.append(f"{ind}try:")
            emit(a[1], ind + "    ", ctx, out, subs)
            out.append(f"{ind}except {a[2]} as e:")
            out.append(f"{ind}    log('caught:'+type(e).__name__+':'+str(e))")
            emit(a[3], ind + "    ", ctx, out, subs)
        elif t == "fin":
            out.append(f"{ind}try:")
            emit(a[1], ind + "    ", ctx, out, subs)
            out.append(f"{ind}finally:")
            emit(a[2], ind + "    ", ctx, out, subs)
        elif t == "loop":
            out.append(f"{ind}for _ in range({a[1]}):")
            emit(a[2], ind + "    ", ctx, out, subs)
        elif t == "re":
            tgt = "(cell[0] if cell else C.top)" if a[2] else "C.top"
            out.append(f"{ind}rop({a[1]!r}, {tgt})")
        else:
            raise AssertionError(t)


def compile_body(body, ctx):
    key = json.dumps([body, ctx])
    fn = FN_CACHE.get(key)
    if fn is not None:
        return fn
    out, subs = [], []
    emit(body, "    ", ctx, out, subs)
    head = {"gen": "def", "coro": "async def", "agen": "async def"}[ctx]
    pre = "" if ctx == "coro" else "    if 0: yield\n"
    src = f"{head} f(cell):\n{pre}" + "\n".join(out) + "\n"
    g = dict(G, SUBS=subs)
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        exec(compile(src, "<script>", "exec"), g)
    FN_CACHE[key] = g["f"]
    return g["f"]


def enc_exc(e):
    return ["exc", type(e).__name__, str(e), r(getattr(e, "value", None))]


def pyarg(a):
    t = a[0]
    if t == "cls":
        return CLS[a[1]]
    if t == "inst":
        return CLS[a[1]](a[2])
    if t == "junk":
        return 42
    if t == "none":
        return None
    if t == "tb":
        return TB
    return a[1]


def enc(thunk):
    try:
        return ["ok", r(thunk())]
    except BaseException as e:
        return enc_exc(e)


def flags(o):
    if isinstance(o, types.GeneratorType):
        return [o.gi_running, o.gi_suspended, o.gi_frame is None, r(o.gi_yieldfrom),
                inspect.getgeneratorstate(o)]
    if isinstance(o, types.CoroutineType):
        return [o.cr_running, o.cr_suspended, o.cr_frame is None, r(o.cr_await),
                inspect.getcoroutinestate(o)]
    return [o.ag_running, o.ag_suspended, o.ag_frame is None, r(o.ag_await),
            inspect.getasyncgenstate(o)]


def apply(op, o, cw):
    t = op[0]
    if t == "next":
        return enc(lambda: next(o))
    if t == "send":
        return enc(lambda: o.send(op[1]))
    if t == "close":
        return enc(o.close)
    if t == "throw":
        return enc(lambda: o.throw(*[pyarg(a) for a in op[1]]))
    if t == "cw_next":
        return enc(lambda: next(cw))
    if t == "cw_send":
        return enc(lambda: cw.send(op[1]))
    if t == "cw_throw":
        return enc(lambda: cw.throw(*[pyarg(a) for a in op[1]]))
    if t == "cw_close":
        return enc(cw.close)
    if t.startswith("new_"):
        def make():
            if t == "new_anext":
                C.held.append(o.__anext__())
            elif t == "new_asend":
                C.held.append(o.asend(op[1]))
            elif t == "new_aclose":
                C.held.append(o.aclose())
            else:
                C.held.append(o.athrow(*[pyarg(a) for a in op[1]]))
            return "<aw>"
        return enc(make)
    if t.startswith("aw_"):
        i = op[1]
        if i >= len(C.held):
            return ["skip"]
        a = C.held[i]
        if t == "aw_next":
            return enc(lambda: next(a))
        if t == "aw_send":
            return enc(lambda: a.send(op[2]))
        if t == "aw_throw":
            return enc(lambda: a.throw(*[pyarg(x) for x in op[2]]))
        return enc(a.close)
    raise AssertionError(t)


def hook_firstiter(ag):
    log("hook:firstiter")
    if C.fib == 2:
        raise ValueError("h")


def hook_finalizer(ag):
    log("hook:finalizer")
    if C.finb == 2:
        raise ValueError("h")


def run_drive(c):
    C.trace = []
    C.held = []
    C.keep = []
    # finalize the cyclic garbage of earlier cases now, into a trace that is thrown away, so
    # that the collection at "del" below finalizes only this case's objects
    gc.collect()
    C.trace = []
    C.fib, C.finb = c["firstiter"], c["finalizer"]
    kind = c["kind"]
    if kind == "agen":
        sys.set_asyncgen_hooks(hook_firstiter if C.fib else None, hook_finalizer if C.finb else None)
    if c["warnerr"]:
        warnings.simplefilter("error", DeprecationWarning)
    o = compile_body(c["body"], kind)(None)
    C.top = o
    cw = o.__await__() if kind == "coro" else None
    steps = []
    for op in c["ops"]:
        if op[0] == "del":
            log_trace = C.trace
            C.held = []
            C.top = None
            cw = None
            o = None
            # A frame suspended in a handler holds the exception it is handling, whose traceback
            # holds the frame: such a generator is reached by the collector, not by its reference
            # count, and gen_finalize (the tp_finalize the model runs at "del") runs then.
            gc.collect()
            C.trace = log_trace
            steps.append([["ok", "None"], "gone"])
            break
        res = apply(op, o, cw)
        steps.append([res, flags(o)])
    trace = C.trace
    C.trace = []  # finalizers of this case's objects log here, not into the next case
    if c["warnerr"]:
        warnings.resetwarnings()
        warnings.simplefilter("always")
    C.top = None
    C.held = []
    o = cw = None
    C.keep = []
    C.ncases += 1
    if C.ncases % 500 == 0:
        gc.collect()
    C.trace = []
    return {"ok": {"steps": steps, "trace": trace}}


def run_names(c):
    def f():
        yield
    async def co():
        pass
    async def ag():
        yield
    fn = {"gen": f, "coro": co, "agen": ag}[c["kind"]]
    fn.__name__ = fn.__qualname__ = "f"
    o = fn()
    out = []
    for attr, v in c["ops"]:
        name = "__" + attr + "__"
        try:
            if v is None:
                delattr(o, name)
            else:
                setattr(o, name, v)
            out.append(["ok"])
        except BaseException as e:
            out.append(enc_exc(e))
        out.append([r(o.__name__), r(o.__qualname__)])
    if c["kind"] == "coro":
        o.close()
    return {"ok": out}


def run_origin(c):
    box = []

    async def co():
        pass

    def f(n):
        if n > 1:
            return f(n - 1)
        return co()

    def target():
        old = sys.get_coroutine_origin_tracking_depth()
        sys.set_coroutine_origin_tracking_depth(c["depth"])
        co_obj = f(c["frames"])
        sys.set_coroutine_origin_tracking_depth(old)
        origin = co_obj.cr_origin
        co_obj.close()
        box.append(None if origin is None else [x[2] for x in origin])

    t = threading.Thread(target=target)
    t.start()
    t.join()
    return {"ok": box[0]}


def run_make(c):
    def f():
        yield
    async def co():
        pass
    async def ag():
        yield
    fn = {"gen": f, "coro": co, "agen": ag}[c["kind"]]
    fn.__name__ = c["name"]
    fn.__qualname__ = c["qualname"]
    o = fn()
    if c["kind"] == "gen":
        fl = [o.gi_running, o.gi_suspended, o.gi_frame is None]
    elif c["kind"] == "coro":
        fl = [o.cr_running, o.cr_suspended, o.cr_frame is None]
    else:
        fl = [o.ag_running, o.ag_suspended, o.ag_frame is None]
    s = re.sub(r"0x[0-9a-f]+", "ADDR", repr(o))
    prefix = s[:s.index(c["qualname"])]
    res = [prefix, o.__name__, o.__qualname__] + fl + [s]
    if c["kind"] == "coro":
        o.close()
    return {"ok": res}


def run_sizeof(c):
    src = "def f(" + ",".join(f"a{i}" for i in range(c["nparams"])) + "):\n    yield 1\n"
    g = {}
    exec(src, g)
    o = g["f"](*range(c["nparams"]))
    a = o.__sizeof__()
    next(o)
    assert o.__sizeof__() == a
    return {"ok": a}


def run_python(c):
    return {"gen_drive": run_drive, "gen_names": run_names, "gen_origin": run_origin,
            "gen_make": run_make, "gen_sizeof": run_sizeof}[c["fn"]](c)


EXCS = ["ValueError", "KeyError", "RuntimeError", "StopIteration", "StopAsyncIteration",
        "GeneratorExit", "MyGE", "MySI", "MySAI"]
HANDLERS = ["ValueError", "GeneratorExit", "StopIteration", "StopAsyncIteration", "Exception",
            "BaseException", "RuntimeError", "LookupError"]


def gen_foreign(rng, kind):
    reent = None
    if rng.random() < 0.3:
        reent = rng.choice({"gen": [0, 1, 2, 3, 4], "coro": [1, 2, 3, 4],
                            "agen": [4, 5, 6, 7]}[TOPKIND[0]])
    return ["f", rng.choice([0, 1, 1, 2, 3]), rng.choice([None, None, 7]), rng.random() < 0.7,
            rng.choice([0, 1, 1, 2, 3, 4, 5, 6, 7]), rng.choice([0, 1, 1, 2, 3, 4, 5, 6]), reent]


def gen_reop(rng, kind, self_):
    if kind == "gen":
        op = rng.choice([["next"], ["send", 1], ["send", None], ["close"], ["throw", "ValueError"],
                         ["throw", "GeneratorExit"], ["flags"]])
    elif kind == "coro":
        op = rng.choice([["send", 1], ["close"], ["throw", "ValueError"], ["flags"]])
    else:
        op = rng.choice([["anext"], ["asend", 1], ["aclose"], ["athrow", "ValueError"], ["flags"],
                         ["hsend", 0], ["hthrow", 0, "ValueError"], ["hclose", 0], ["hsend", 1]])
    if op[0] == "send" and op[1] is None:
        op = ["next"]
    return op


def gen_act(rng, kind, d):
    top = TOPKIND[0]
    x = rng.random()
    val = rng.randint(0, 9)
    can_yield = kind != "coro"
    if x < 0.32 and can_yield:
        return ["y", val]
    if x < 0.32:
        return ["yf", gen_foreign(rng, kind)]
    if x < 0.48:
        if d < 2 and rng.random() < 0.5:
            if kind == "gen":
                return ["yf", ["s", gen_body(rng, "gen", d + 1)]]
            k = rng.random()
            if k < 0.5:
                return ["yf", ["s", gen_body(rng, "coro", d + 1)]]
            if k < 0.75:
                return ["yf", ["c", gen_body(rng, "gen", d + 1)]]
            return ["yf", ["bad", rng.randint(0, 4)]]
        return ["yf", gen_foreign(rng, kind)]
    if x < 0.55:
        return ["ret", None if kind == "agen" or rng.random() < 0.4 else val]
    if x < 0.64:
        return ["raise", rng.choice(EXCS)]
    if x < 0.82 and d < 3:
        h = rng.choice(HANDLERS + ["GeneratorExit"] * 3)
        return ["try", gen_body(rng, kind, d + 1), h, gen_body(rng, kind, d + 1, empty_ok=True)]
    if x < 0.90 and d < 3:
        return ["fin", gen_body(rng, kind, d + 1), gen_body(rng, kind, d + 1, empty_ok=True)]
    if x < 0.94 and d < 3:
        return ["loop", rng.randint(0, 3), gen_body(rng, kind, d + 1)]
    if rng.random() < 0.3:
        return ["re", gen_reop(rng, kind, True), True]
    return ["re", gen_reop(rng, top, False), False]


def gen_body(rng, kind, d=0, empty_ok=False):
    n = rng.randint(0 if empty_ok else 1, 3 if d else 4)
    return [gen_act(rng, kind, d) for _ in range(n)]


def has_reent(x):
    if isinstance(x, list):
        if x and x[0] == "re":
            return True
        if x and x[0] == "f" and len(x) == 7 and x[6] is not None:
            return True
        return any(has_reent(y) for y in x)
    return False


def gen_throw_args(rng):
    c0 = rng.choice(EXCS)
    # a class whose constructor re-enters; only where a class is thrown (an instance would be
    # built by this driver, before the throw)
    c = "ReInit" if rng.random() < 0.15 else c0
    k = rng.random()
    if k < 0.45:
        return [["cls", c]]
    if k < 0.6:
        return [["inst", c0, "x"]]
    if k < 0.66:
        return [["junk"]]
    if k < 0.72:
        return []
    if k < 0.78:
        return [["cls", c], ["str", "v"]]
    if k < 0.84:
        return [["cls", c], ["none"], ["none"]]
    if k < 0.88:
        return [["cls", c], ["none"], ["tb"]]
    if k < 0.92:
        return [["cls", c], ["none"], ["int", 1]]
    if k < 0.96:
        return [["inst", c0, "x"], ["str", "v"]]
    return [["cls", c], ["none"], ["none"], ["none"]]


def gen_ops(rng, kind):
    n = rng.randint(1, 9)
    ops = []
    if kind == "agen":
        held = 0
        for _ in range(n):
            x = rng.random()
            if held == 0 or x < 0.3:
                k = rng.random()
                if k < 0.45:
                    ops.append(["new_anext"])
                elif k < 0.6:
                    ops.append(["new_asend", rng.choice([None, 1, 2])])
                elif k < 0.8:
                    ops.append(["new_aclose"])
                else:
                    ops.append(["new_athrow", gen_throw_args(rng)])
                held += 1
            i = rng.randrange(held) if rng.random() < 0.3 else held - 1
            k = rng.random()
            if k < 0.5:
                ops.append(["aw_send", i, rng.choice([None, None, 1])])
            elif k < 0.7:
                ops.append(["aw_next", i])
            elif k < 0.88:
                ops.append(["aw_throw", i, gen_throw_args(rng)])
            else:
                ops.append(["aw_close", i])
        return ops
    for _ in range(n):
        x = rng.random()
        pre = "cw_" if kind == "coro" and rng.random() < 0.3 else ""
        if x < 0.4:
            if kind == "gen" or pre:
                ops.append([pre + "next"])
            else:
                ops.append(["send", None])
        elif x < 0.6:
            ops.append([pre + "send", rng.choice([None, 1, 2, "s"])])
        elif x < 0.8:
            ops.append([pre + "throw", gen_throw_args(rng)])
        else:
            ops.append([pre + "close"])
    return ops


TOPKIND = ["gen"]


def gen_case(rng):
    x = rng.random()
    if x < 0.94:
        kind = rng.choice(["gen", "gen", "coro", "agen", "agen"])
        TOPKIND[0] = kind
        body = gen_body(rng, kind)
        if kind == "agen" and not any(a[0] == "y" for a in body):
            body.append(["y", 1])
        ops = gen_ops(rng, kind)
        if not has_reent(body) and rng.random() < 0.3:
            ops.append(["del"])
        hooks = kind == "agen" and rng.random() < 0.3
        return {"mod": "bytecode", "fn": "gen_drive", "kind": kind, "body": body, "ops": ops,
                "warnerr": rng.random() < 0.05,
                "firstiter": rng.randint(0, 2) if hooks else 0,
                "finalizer": rng.randint(0, 2) if hooks else 0}
    if x < 0.96:
        ops = [[rng.choice(["name", "qualname"]), rng.choice(["a", "", "b.c", None, 1])]
               for _ in range(rng.randint(1, 5))]
        return {"mod": "bytecode", "fn": "gen_names", "kind": rng.choice(["gen", "coro", "agen"]),
                "ops": ops}
    if x < 0.97:
        return {"mod": "bytecode", "fn": "gen_origin", "depth": rng.randint(0, 9),
                "frames": rng.randint(1, 5)}
    if x < 0.985:
        return {"mod": "bytecode", "fn": "gen_make", "kind": rng.choice(["gen", "coro", "agen"]),
                "name": rng.choice(["f", "g", "h_1"]), "qualname": rng.choice(["q", "a.b.<locals>.q"])}
    nparams = rng.randint(0, 40)
    src = "def f(" + ",".join(f"a{i}" for i in range(nparams)) + "):\n    yield 1\n"
    g = {}
    exec(src, g)
    code = g["f"].__code__
    return {"mod": "bytecode", "fn": "gen_sizeof", "nparams": nparams, "nlocals": code.co_nlocals,
            "stacksize": code.co_stacksize}


if __name__ == "__main__":
    sys.unraisablehook = lambda u: log(f"unraisable:{type(u.exc_value).__name__}:{u.exc_value}")
    warnings.showwarning = lambda msg, cat, *a, **k: log("warn:" + cat.__name__)
    warnings.simplefilter("always")
    gc.disable()  # every collection happens between cases, in run_drive
    main(gen_case, run_python, default_cases=20000)
