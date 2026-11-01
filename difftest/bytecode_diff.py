"""Differential test of the bytecode machine against the running CPython.

Each case is a random small program. Python compiles it, the code objects are
dumped, and the Lean machine runs the bytecode from a fresh heap; real CPython
runs the same code object. They must agree on everything `print` wrote and on
the uncaught exception (class and message). `quicken` cases run the same program
twice in the model, the second time on a program rewritten to specialized forms
from a profile of the first run, so the specialized step rules and their deopts
are exercised too.

Whatever the model cannot run yet is not silently steered around: the generator
draws the case, `exclude` counts it under a name, and the run prints the counts. Each
name but `syntax-error` is a `.open` entry (`bytecode-gap-*`) in `lean/PyLean/Bytecode.lean`:

  str-percent-conversion    a `%` conversion in a str or bytes template
  float-pow-complex         `float ** float` with a complex result: no complex value
  huge-int-pow              int ** int with |base| > 1, exponent > 1000 (time, memory)
  huge-shift                nonzero int << 2**20 or more (memory)
  huge-seq-repeat           sequence * count > 1000 (memory, MemoryError paths)
  is-on-immediates          `is` on ints, floats, strs: CPython's identity of equal
                            immutable values depends on caching the model does not have
  set-iteration-order       printing a set: order depends on the table layout
  refcount-finalizer-order  when a finalizer prints depends on reference counts
  syntax-error              the generated source does not compile
"""

import atexit
import collections
import contextlib
import dis
import gc
import io
import random
import struct
import sys
import types
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from common import main

sys.unraisablehook = lambda u: None

EXCLUDED = collections.Counter()


def exclude(name):
    EXCLUDED[name] += 1


INTS = ["0", "1", "-1", "2", "3", "7", "10", "-3", "255", "256", "1000", "2**30-1", "2**30", "-(2**30)",
        "-(2**30)+1", "2**31", "2**62", "2**63-1", "2**63", "-(2**63)", "2**64", "10**20"]
FLOATS = ["0.0", "-0.0", "1.5", "-2.5", "0.1", "3.0", "1e16", "1e22", "1e-5", "1e300", "2.0**53"]
STRS = ["''", "'a'", "'abc'", "'é'", "'a b'", "'x'*3", "'10'", "'\\n'", "\"it's\"", "'%d'", "'%s %s'", "'100%'"]
ATOMS = ["None", "True", "False", "[]", "[1]", "[1, 2, 3]", "()", "(1,)", "(1, 2)", "{}", "{1: 2}", "{'a': 1}",
         "set()", "{1, 2}", "range(3)", "range(0)", "[[1], [2]]", "b'ab'", "b'%d'", "...", "NotImplemented"]
BINOPS = ["+", "-", "*", "/", "//", "%", "**", "&", "|", "^", "<<", ">>"]
CMPOPS = ["==", "!=", "<", "<=", ">", ">=", "is", "is not", "in", "not in"]


def value(r):
    k = r.random()
    if k < 0.4:
        return r.choice(INTS)
    if k < 0.55:
        return r.choice(FLOATS)
    if k < 0.75:
        return r.choice(STRS)
    return r.choice(ATOMS)


def unmodelled_binop(op, a, b):
    """The exclusion name for `a op b`, or None when the model runs it."""
    x, y = eval(a), eval(b)
    is_int = lambda v: isinstance(v, int)
    if op == "%" and ((isinstance(x, str) and "%" in x) or (isinstance(x, bytes) and b"%" in x)):
        return "str-percent-conversion"
    if op == "**":
        if is_int(x) and is_int(y) and abs(x) > 1 and y > 1000:
            return "huge-int-pow"
        if isinstance(x, (int, float)) and isinstance(y, (int, float)):
            try:
                if isinstance(x ** y, complex):
                    return "float-pow-complex"
            except (OverflowError, ZeroDivisionError):
                pass
    if op == "<<" and is_int(x) and x != 0 and is_int(y) and y >= 2**20:
        return "huge-shift"
    if op == "*":
        seqs = (str, bytes, list, tuple)
        if (isinstance(x, seqs) and is_int(y) and y > 1000) or (is_int(x) and isinstance(y, seqs) and x > 1000):
            return "huge-seq-repeat"
    return None


IDENTITY_SAFE = ("None", "True", "False", "[]")


def guarded(body, r=None):
    lines = body.split("\n")
    out = ["try:"] + ["    " + l for l in lines]
    out += ["except Exception as e:", "    print(type(e).__name__, e)"]
    return "\n".join(out)


def p_arith(r):
    out = []
    for _ in range(r.randint(2, 6)):
        a, b = value(r), value(r)
        k = r.random()
        if k < 0.45:
            op = r.choice(BINOPS)
            why = unmodelled_binop(op, a, b)
            if why:
                exclude(why)
                continue
            out.append(guarded(f"x = {a}\ny = {b}\nprint(x {op} y)"))
        elif k < 0.7:
            op = r.choice(CMPOPS)
            if op in ("is", "is not"):
                if a not in IDENTITY_SAFE or b not in IDENTITY_SAFE:
                    exclude("is-on-immediates")
                a, b = r.choice(["None", "True", "[]"]), r.choice(["None", "False", "x"])
                out.append(guarded(f"x = None\ny = {a}\nprint(y {op} {b})"))
            else:
                out.append(guarded(f"x = {a}\ny = {b}\nprint(x {op} y)"))
        elif k < 0.8:
            op = r.choice(["-", "~", "+", "not "])
            out.append(guarded(f"x = {a}\nprint({op}x)"))
        elif k < 0.9:
            op = r.choice(["+=", "-=", "*=", "|=", "&="])
            why = unmodelled_binop(op[:-1], a, b)
            if why:
                exclude(why)
                continue
            out.append(guarded(f"x = {a}\nx {op} {b}\nprint(x)"))
        else:
            fn = r.choice(["bool", "len", "str", "repr", "abs", "int", "list", "tuple", "sorted", "sum", "min", "max",
                           "iter", "hash"])
            if fn == "iter":
                out.append(guarded(f"print(list(iter({a})))"))
            elif fn == "hash":
                out.append(guarded(f"d = {{}}\nd[{a}] = 1\nprint(len(d), {a} in d)"))
            elif fn in ("str", "repr") and ("set" in a or "{1, 2}" in a):
                exclude("set-iteration-order")
                out.append(guarded(f"print(len({a}))"))
            else:
                out.append(guarded(f"print({fn}({a}))"))
    return "\n".join(out)


def p_seq(r):
    out = []
    seqs = ["[1, 2, 3, 4]", "(1, 2, 3)", "'abcd'", "b'xyz'", "range(5)", "range(10, 0, -3)", "[]", "()", "''"]
    idx = ["0", "1", "-1", "2", "3", "10", "-10", "2**31", "2**63", "-(2**63)", "'a'", "None", "1.5", "True"]
    for _ in range(r.randint(2, 5)):
        s = r.choice(seqs)
        k = r.random()
        if k < 0.35:
            out.append(guarded(f"s = {s}\nprint(s[{r.choice(idx)}])"))
        elif k < 0.7:
            a, b, c = [r.choice(["", "0", "1", "-1", "2", "10", "-10", "None"]) for _ in range(3)]
            st = r.choice(["", ":" + c, ":-1", ":2", ":0"])
            out.append(guarded(f"s = {s}\nv = s[{a}:{b}{st}]\nprint(list(v), len(v))"))
        elif k < 0.85:
            out.append(guarded(f"l = list({s})\nl[{r.choice(idx)}] = 9\nprint(l)"))
        else:
            out.append(guarded(f"l = list({s})\ndel l[{r.choice(idx)}]\nprint(l)"))
    d = r.choice(["{}", "{1: 'a'}", "{'x': 1, 'y': 2}", "{1: 1, 1.0: 2, True: 3}"])
    k = r.choice(["1", "'x'", "[]", "{}", "None", "(1, 2)", "1.0", "True", "(1, [])"])
    out.append(guarded(f"d = {d}\nprint(d[{k}])"))
    out.append(guarded(f"d = {d}\nd[{k}] = 5\nprint(d, len(d))"))
    out.append(guarded(f"d = {d}\ndel d[{k}]\nprint(d)"))
    out.append(guarded(f"s = {{1, 2}}\nprint({k} in s, {k} in {d})"))
    out.append(guarded(f"s = set()\ns.add({k})\nprint(sorted(s, key=repr))"))
    return "\n".join(out)


def p_unpack(r):
    out = []
    srcs = ["[1, 2]", "(1, 2)", "[1, 2, 3]", "(1,)", "[]", "'ab'", "'abc'", "{1: 2, 3: 4}", "range(2)", "5", "None",
            "iter([1, 2])", "(i for i in range(2))", "{1: 2, 3: 4, 5: 6}"]
    for _ in range(r.randint(3, 6)):
        s = r.choice(srcs)
        tgt = r.choice(["a, b", "a, *b", "*a, b", "a, b, *c", "a, *b, c", "a,", "[a, b]", "(a, (b, c))", "*a,"])
        out.append(guarded(f"{tgt} = {s}\nprint(a)"))
    return "\n".join(out)


def p_loops(r):
    it = r.choice(["[1, 2, 3]", "(4, 5)", "range(4)", "range(5, 0, -2)", "'xyz'", "{1: 2, 3: 4}", "[]", "()",
                   "{'a': 1}.items()", "enumerate([7, 8])", "zip([1, 2], 'ab')", "map(str, [1, 2])",
                   "filter(None, [0, 1, 2])", "reversed([1, 2, 3])", "(i * 2 for i in range(3))", "iter([1])"])
    brk = r.choice(["", "if i == 1:\n        break\n    ", "if i == 1:\n        continue\n    "])
    els = r.choice(["", "else:\n    print('else')\n"])
    n = r.randint(0, 4)
    return (f"t = 0\nfor i in {it}:\n    {brk}print(i)\n{els}"
            f"n = {n}\nwhile n > 0:\n    n -= 1\n    if n == 2:\n        continue\n    t += n\nelse:\n    print('w', t)\n"
            "l = [1, 2, 3]\nfor x in l:\n    if x == 1:\n        l.append(9)\n    print(x)\n"
            "l = [1, 2, 3]\nfor x in l:\n    l.pop()\n    print(x)\n"
            "d = {1: 1}\ntry:\n    for k in d:\n        d[k + 1] = 1\nexcept RuntimeError as e:\n    print(e)\n")


def p_calls(r):
    params = r.choice(["", "a", "a, b", "a, b=2", "a=1, b=2", "*a", "a, *b", "**k", "a, **k", "a, *, b", "a, *, b=1",
                       "a, /", "a, /, b", "a, b=2, *c, d, e=5, **f", "a, /, b=1, *, c=2"])
    calls = ["f()", "f(1)", "f(1, 2)", "f(1, 2, 3)", "f(a=1)", "f(b=1)", "f(1, a=1)", "f(1, b=2)", "f(1, c=3)",
             "f(d=4)", "f(1, d=4)", "f(*[1, 2])", "f(**{'a': 1})", "f(*(1,), **{'b': 2})", "f(1, **{'a': 2})",
             "f(*5)", "f(**5)", "f(**{1: 2})", "f(1, 2, d=1)", "f(a=1, b=2, c=3)", "f(*'ab')"]
    body = r.choice(["return locals()", "return 1", "return sorted(locals().items())"])
    if params == "" and "locals" in body:
        body = "return 1"
    out = [f"def f({params}):\n    {r.choice(['return (1, 2)', 'return None', 'pass'])}"]
    for c in r.sample(calls, min(len(calls), r.randint(3, 8))):
        out.append(guarded(f"print({c})"))
    out.append(guarded("print((lambda x, y=1: x + y)(1), (lambda *a: a)(1, 2))"))
    out.append(guarded(r.choice(["print(len(1, 2))", "print(1())", "print('a'())", "print([].append())",
                                 "print(int('x'))", "print(print.__name__)", "print(str.upper('a'))",
                                 "print(list.append(1, 2))", "print(len.__qualname__)"])))
    return "\n".join(out)


def p_scope(r):
    return r.choice([
        "def f():\n    print(x)\n    x = 1\n" + guarded("f()"),
        "def f():\n    x = 1\n    del x\n    print(x)\n" + guarded("f()"),
        "def f():\n    del x\n    x = 1\n" + guarded("f()"),
        "def f():\n    def g():\n        return y\n    r = g()\n    y = 1\n    return r\n" + guarded("f()"),
        "def f():\n    y = 1\n    def g():\n        return y\n    del y\n    return g()\n" + guarded("print(f())"),
        "def f():\n    global z\n    z = 1\n    del z\n    print(z)\n" + guarded("f()"),
        "def f():\n    n = 0\n    def g():\n        nonlocal n\n        n += 1\n        return n\n    g()\n    return g(), n\nprint(f())",
        "def f(a):\n    def g():\n        return a\n    a = a + 1\n    return g()\nprint(f(1))",
        "fs = [lambda: i for i in range(3)]\nprint([f() for f in fs])\n",
        "x = 10\nclass C:\n    x = x + 1\n    y = [x for _ in range(1)]\n    def m(self):\n        return x\nprint(C.x, C.y, C().m())",
        guarded("print(undefined)"),
        guarded("del undefined"),
        "x = 1\ndel x\n" + guarded("print(x)"),
        guarded("class C:\n    print(missing)"),
        "def f():\n    x = 1\n    return [x + i for i in range(3)], x\nprint(f())",
        "def f():\n    x = 5\n    r = [x for x in range(2)]\n    return x, r\nprint(f())",
        "def f():\n    try:\n        return [1 / i for i in [1, 0]]\n    except ZeroDivisionError:\n        return i\n" + guarded("f()"),
    ])


def p_exc(r):
    kinds = ["ValueError('v')", "KeyError('k')", "TypeError", "ZeroDivisionError('z')", "StopIteration(5)", "RuntimeError()",
             "1", "'x'", "None", "Exception('a', 'b')", "AttributeError('at')"]
    e = r.choice(kinds)
    h = r.choice(["ValueError", "(KeyError, TypeError)", "Exception", "BaseException", "ArithmeticError", "1", "(1, 2)", "()", "LookupError"])
    t = r.choice([
        f"try:\n    raise {e}\nexcept {h} as x:\n    print('h', repr(x))\nelse:\n    print('else')\nfinally:\n    print('f')\n",
        f"def f():\n    try:\n        raise {e}\n    finally:\n        return 1\nprint(f())\n",
        f"def f():\n    for i in range(2):\n        try:\n            raise {e}\n        except Exception:\n            continue\n        finally:\n            print('fin', i)\n    return 'done'\nprint(f())\n",
        f"def f():\n    try:\n        return 1\n    finally:\n        print('f')\nprint(f())\n",
        f"def f():\n    while True:\n        try:\n            raise {e}\n        finally:\n            break\n    return 2\nprint(f())\n",
        f"try:\n    try:\n        raise {e}\n    except Exception as a:\n        raise ValueError('second') from a\nexcept Exception as b:\n    print(repr(b), repr(b.__cause__), repr(b.__context__), b.__suppress_context__)\n",
        f"try:\n    try:\n        raise {e}\n    except Exception as a:\n        raise ValueError('second')\nexcept Exception as b:\n    print(repr(b), repr(b.__cause__), repr(b.__context__), b.__suppress_context__)\n",
        f"try:\n    try:\n        raise {e}\n    finally:\n        print('inner')\nexcept Exception as b:\n    print(repr(b))\n",
        "try:\n    raise\nexcept RuntimeError as e:\n    print(e)\n",
        f"try:\n    raise ValueError('a') from {r.choice(['None', '1', 'KeyError', 'KeyError(1)'])}\nexcept Exception as e:\n    print(repr(e), repr(e.__cause__), e.__suppress_context__)\n",
        f"def f():\n    try:\n        raise {e}\n    except Exception:\n        raise\n" + guarded("f()"),
        f"try:\n    raise {e}\nexcept Exception as x:\n    pass\n" + guarded("print(x)"),
        f"class E(Exception):\n    def __init__(self, a):\n        self.a = a\n    def __str__(self):\n        return 'E:' + str(self.a)\ntry:\n    raise E(1)\nexcept E as x:\n    print(x, x.args, x.a)\n",
        "class E(ValueError):\n    pass\nclass F(E):\n    pass\ntry:\n    raise F('x')\nexcept (KeyError, E) as x:\n    print(type(x).__name__, x)\n",
        "assert 1 == 1\n" + guarded("assert 1 == 2, 'msg'") + "\n" + guarded("assert False"),
    ])
    return guarded(t) if r.random() < 0.7 else t


def p_with(r):
    enter = r.choice(["return self", "return 1", "raise ValueError('enter')"])
    ret = r.choice(["True", "False", "None", "1", "0", "raise KeyError('exit')"])
    exit_body = f"print('x', t, repr(v))\n        {'return ' + ret if not ret.startswith('raise') else ret}"
    body = r.choice(["print('body')", "raise TypeError('b')", "return_"])
    cls = f"class C:\n    def __enter__(self):\n        print('e')\n        {enter}\n    def __exit__(self, t, v, tb):\n        {exit_body}\n"
    if body == "return_":
        t = cls + "def f():\n    with C() as a:\n        return 5\n" + guarded("print(f())")
    else:
        t = cls + guarded(f"with C() as a:\n    {body}\nprint('after')")
    extra = r.choice(["", guarded("with 1:\n    pass"),
                      "class D:\n    def __enter__(self):\n        return 1\n" + guarded("with D():\n    pass"),
                      "class A:\n    async def __aenter__(self):\n        pass\n    async def __aexit__(self, *a):\n        pass\n" + guarded("with A():\n    pass"),
                      "class E:\n    __enter__ = 1\n    __exit__ = 2\n" + guarded("with E():\n    pass"),
                      cls + guarded("with C() as a, C() as b:\n    print('both')\n"),
                      ])
    return t + "\n" + extra


def p_gen(r):
    body = r.choice([
        "x = yield 1\nprint('got', x)\ny = yield 2\nprint('got', y)\nreturn 3",
        "try:\n    yield 1\nfinally:\n    print('cleanup')",
        "try:\n    yield 1\nexcept ValueError as e:\n    print('caught', e)\n    yield 2\nyield 3",
        "try:\n    yield 1\nexcept GeneratorExit:\n    yield 2",
        "try:\n    yield 1\nexcept GeneratorExit:\n    return 7",
        "yield 1\nraise StopIteration('s')",
        "yield 1\nraise ValueError('g')",
        "yield from [1, 2]\nr = yield from sub()\nprint('r', r)\nyield r",
        "for i in range(3):\n    yield i",
        "return 1\nyield",
        "yield from sub()",
    ])
    sub = "def sub():\n    try:\n        x = yield 'a'\n        print('s', x)\n        return 'ret'\n    finally:\n        print('sub done')\n"
    indented = "\n".join("    " + l for l in body.split("\n"))
    ops = r.choices(["next(g)", "g.send(1)", "g.send(None)", "g.close()", "g.throw(ValueError('t'))", "g.throw(KeyError)",
                     "g.throw(GeneratorExit)", "g.throw(1)", "list(g)", "g.gi_running", "g.gi_suspended", "g.gi_yieldfrom is None", "g.__name__"],
                    k=r.randint(2, 7))
    out = [sub, f"def f():\n{indented}", "g = f()"]
    # `throw(1)` on a delegating generator drops the subiterator, and what its
    # finalizer prints depends on reference counts, which the model does not have.
    if "sub()" in body and "g.throw(1)" in ops:
        exclude("refcount-finalizer-order")
        ops = [o for o in ops if o != "g.throw(1)"]
    for o in ops:
        out.append(guarded(f"print({o})"))
    out.append(r.choice(["", "def h():\n    next(me)\n    yield\nme = h()\n" + guarded("next(me)"),
                         "def h():\n    me.close()\n    yield\nme = h()\n" + guarded("next(me)"),
                         "def h():\n    me.send(1)\n    yield\nme = h()\n" + guarded("next(me)\nprint(me.gi_running)"),
                         "print(sum(i * i for i in range(4)), list(x for x in 'ab' if x != 'a'))",
                         "def h():\n    yield from 1\n" + guarded("next(h())"),
                         "def h():\n    a = yield\n    yield a\n" + guarded("x = h()\nx.send(1)"),
                         ]))
    return "\n".join(out)


def p_class(r):
    pool = [
        "class V:\n    def __init__(self, x):\n        self.x = x\n    def __add__(self, o):\n        return V(self.x + (o.x if isinstance(o, V) else o))\n    def __radd__(self, o):\n        return V(o + self.x)\n    def __repr__(self):\n        return f'V({self.x})'\n    def __eq__(self, o):\n        return isinstance(o, V) and o.x == self.x\n    def __lt__(self, o):\n        return self.x < o.x\n    def __hash__(self):\n        return hash(self.x)\n    def __bool__(self):\n        return self.x != 0\n    def __len__(self):\n        return 3\n    def __getitem__(self, i):\n        if i > 2:\n            raise IndexError(i)\n        return i * self.x\n    def __call__(self, *a):\n        return a\n    def __contains__(self, o):\n        return o == 1\nv = V(2)\nprint(v + 1, 1 + v, v + v, v == V(2), v != V(3), v < V(3), V(3) > v, bool(v), len(v), list(v), v(1, 2), 1 in v, 2 in v)\nprint(sorted([V(3), V(1)]), {V(1): 1}[V(1)])\n" + guarded("print(v > 1)") + "\n" + guarded("print(v - 1)"),
        "class It:\n    def __init__(self):\n        self.n = 0\n    def __iter__(self):\n        return self\n    def __next__(self):\n        self.n += 1\n        if self.n > 2:\n            raise StopIteration\n        return self.n\nprint(list(It()), [x for x in It()])\na, b = It()\nprint(a, b)\n",
        "class S:\n    __slots__ = ('a', 'b')\ns = S()\ns.a = 1\nprint(s.a)\n" + guarded("print(s.b)") + "\n" + guarded("s.c = 1") + "\n" + guarded("del s.b"),
        "class D:\n    def __get__(self, o, t=None):\n        return 'got'\n    def __set__(self, o, v):\n        print('set', v)\nclass A:\n    d = D()\na = A()\nprint(a.d, A.d)\na.d = 1\n",
        "class A:\n    x = 1\n    def m(self):\n        return 'A.m'\na = A()\nprint(a.x, A.x, a.m(), A.m(a))\na.x = 2\nprint(a.x, A.x)\nA.x = 3\nprint(a.x, A.x)\ndel a.x\nprint(a.x)\n" + guarded("del a.x") + "\n" + guarded("print(a.nope)") + "\n" + guarded("print(A.nope)"),
        "class A:\n    def __getattr__(self, n):\n        return n + '!'\nprint(A().foo)\nclass B:\n    def __getattribute__(self, n):\n        return 'ga:' + n\nprint(B().foo)\nclass C:\n    def __setattr__(self, n, v):\n        print('sa', n, v)\n    def __delattr__(self, n):\n        print('da', n)\nc = C()\nc.x = 1\ndel c.x\n",
        "class A:\n    def f(self):\n        return 'A'\nclass B(A):\n    def f(self):\n        return 'B' + super().f()\nclass C(A):\n    def f(self):\n        return 'C' + super().f()\nclass D(B, C):\n    def f(self):\n        return 'D' + super().f()\nprint(D().f(), [k.__name__ for k in D.__mro__])\n",
        "class P:\n    @property\n    def x(self):\n        return 1\n    @x.setter\n    def x(self, v):\n        print('set', v)\n    @staticmethod\n    def s():\n        return 's'\n    @classmethod\n    def c(cls):\n        return cls\np = P()\nprint(p.x, p.s(), P.s(), p.c(), P.c())\np.x = 2\n" + guarded("del p.x"),
        "class I:\n    def __init__(self):\n        return 1\n" + guarded("I()") + "\nclass J:\n    pass\n" + guarded("J(1)") + "\nclass K:\n    def __new__(cls, a):\n        print('new', a)\n        return 5\nprint(K(1))\n",
        "class B:\n    def __bool__(self):\n        return 1\n" + guarded("print(not B())") + "\nclass L:\n    def __len__(self):\n        return -1\n" + guarded("print(len(L()))") + "\n" + guarded("print(bool(L()))") + "\nclass H:\n    __hash__ = None\n" + guarded("print({H(): 1})"),
        "class N(int):\n    pass\nn = N(3)\nprint(n, n + 1, str(n), isinstance(n, int), type(n).__name__)\nclass T(str):\n    pass\nt = T('ab')\nprint(t, len(t))\n",
        "class E:\n    def __eq__(self, o):\n        print('eq')\n        return True\nprint(E() == 1, 1 == E(), E() != 1, E() in [1], [E()] == [1])\n",
        "class G:\n    def __iter__(self):\n        yield 1\n        yield 2\nprint(list(G()), sum(G()))\nclass H:\n    def __iter__(self):\n        return 1\n" + guarded("iter(H())") + "\nclass Q:\n    __iter__ = None\n" + guarded("iter(Q())"),
        "class C:\n    pass\nc = C()\nc.a = 1\nc.b = 2\nfor _ in range(3):\n    print(c.a + c.b)\ndel c.a\n" + guarded("print(c.a)") + "\nC.z = 5\nprint(c.z)\ndel C.z\n" + guarded("print(c.z)"),
    ]
    return r.choice(pool)


def p_comp(r):
    pool = [
        "print([x * y for x in range(3) for y in range(x) if y])",
        "print({x: y for x, y in zip('ab', [1, 2])})",
        "print(sorted({x % 2 for x in range(5)}))",
        "print(list((x, y) for x in [1, 2] for y in 'ab'))",
        guarded("print([1 / x for x in [1, 0]])"),
        "def f():\n    x = 'o'\n    try:\n        [x for x in [1, 0] if 1 / x]\n    except ZeroDivisionError:\n        pass\n    return x\nprint(f())",
        "def f(g):\n    x = 'o'\n    try:\n        return [x for x in g()], x\n    except ValueError:\n        return x\ndef g():\n    yield 1\n    raise ValueError\nprint(f(g))",
        "print([[j for j in range(i)] for i in range(3)])",
        "print([f'{x}' for x in range(2)], [str(x) for x in 'a'])",
        "print(*[1, 2], *'ab', sep='-')\nprint([*range(2), *[3]], {**{'a': 1}, 'b': 2}, (*[1], 2))\n" + guarded("print([*1])") + "\n" + guarded("print({**1})") + "\n" + guarded("print({*1})"),
    ]
    return r.choice(pool) + "\n" + r.choice(pool)


def p_match(r):
    subj = r.choice(["1", "2", "'a'", "None", "[1, 2]", "(1, 2, 3)", "{'a': 1}", "{'a': 1, 'b': 2}", "P(1, 2)", "[]", "{}", "1.0", "True", "'ab'", "b'ab'", "range(2)"])
    pat = r.choice(["1", "'a'", "None", "True", "[a, b]", "(a, *b)", "{'a': x}", "{'a': x, **rest}", "P(x=1)", "P(a, b)", "P(1)", "int()", "int(q)", "str(q)", "list()", "dict()", "[1, _]", "1 | 2", "[a] | (a, _)", "float(q)", "bool()", "Q(1)", "tuple(z)"])
    g = r.choice(["", " if 1 > 0", " if 0 > 1"])
    return ("class P:\n    __match_args__ = ('x', 'y')\n    def __init__(self, x, y):\n        self.x = x\n        self.y = y\n"
            "class Q:\n    __match_args__ = 1\n"
            + guarded(f"match {subj}:\n    case {pat}{g}:\n        print('m')\n    case _:\n        print('nm')"))


def p_strs(r):
    return r.choice([
        "x = 3\nprint(f'{x}', f'{x!r}', f'{x:>4}', f'{x:04}', f'{\"a\":<3}|', f'{x}{x}', f'{x!s}')",
        "print('a' 'b', 'a' * 2, 'abc'[1], 'abc'[-1], 'a' in 'abc', 'x' + 'y')",
        "print(repr('a\\n'), repr(\"it's\"), repr('\"'), str(1.5), repr(1e22), 1e16, 1.0, 0.1 + 0.2, -0.0)",
        "print(', '.join(['a', 'b']), 'A'.lower(), 'a'.upper(), ' a '.strip(), 'a b'.split(), 'ab'.startswith('a'))\n" + guarded("print(', '.join([1]))"),
        "print(1 == 1.0, 2**53 == 2.0**53, 2**53 + 1 == 2.0**53, 1 < 1.5, True + 1, 3 / 2, 7 // 2, -7 // 2, -7 % 3, 2**-1)",
        "print(10**20 / 3, 1 / 3, 2**64 * 2**64, -(2**63) - 1, (2**31) * (2**31), 2**30 + 2**30, 1 << 40, -1 >> 3, 5 & -2, 5 | -2, 5 ^ -2)",
        "print(1e300 * 1e300, -1e300 * 1e300, 1.5 + 1, 2 * 1.5, 1.5 - 2, 1e16 + 1, 0.1 * 3)",
        "print(True and 1, False or 'x', None or [], not [], 1 if [] else 2, 0 or 0.0 or '' or None)",
        "print(isinstance(1, int), isinstance(True, int), isinstance('a', (int, str)), issubclass(bool, int))\n" + guarded("isinstance(1, 1)"),
        "print(type(1).__name__, type('').__name__, type(None).__name__, type([]).__name__, type(print).__name__)",
    ])


def p_async(r):
    drv = ("def drive(c):\n    try:\n        while True:\n            x = c.send(None)\n            print('y', x)\n    except StopIteration as e:\n        return e.value\n"
           "class A:\n    def __await__(self):\n        x = yield 'aw'\n        return 5\n")
    return drv + r.choice([
        "async def f():\n    a = await A()\n    return a + 1\nprint(drive(f()))\n",
        "async def f():\n    return 1\nasync def g():\n    return await f() + 1\nprint(drive(g()))\n",
        "async def f():\n    await 1\n" + guarded("drive(f())"),
        "class C:\n    async def __aenter__(self):\n        print('ae')\n        return 1\n    async def __aexit__(self, *a):\n        print('ax')\nasync def f():\n    async with C() as x:\n        print(x)\nprint(drive(f()))\n",
        "class I:\n    def __init__(self):\n        self.n = 0\n    def __aiter__(self):\n        return self\n    async def __anext__(self):\n        self.n += 1\n        if self.n > 2:\n            raise StopAsyncIteration\n        return self.n\nasync def f():\n    async for x in I():\n        print(x)\n    return 'd'\nprint(drive(f()))\n",
        "async def f():\n    async for x in 1:\n        pass\n" + guarded("drive(f())"),
        "async def f():\n    async with 1:\n        pass\n" + guarded("drive(f())"),
        "async def f():\n    return 1\nc = f()\ndrive(c)\n" + guarded("drive(c)"),
        "async def f():\n    await A()\nc = f()\nprint(c.send(None))\n" + guarded("c.close()\nprint('closed')") + "\n" + guarded("c.send(None)"),
    ])


FAMILIES = [p_arith, p_seq, p_unpack, p_loops, p_calls, p_scope, p_exc, p_with, p_gen, p_class, p_comp, p_match, p_strs, p_async]


def enc_const(c, table):
    if c is None:
        return ["n"]
    if c is Ellipsis:
        return ["e"]
    if c is True:
        return ["t"]
    if c is False:
        return ["F"]
    if isinstance(c, int):
        return ["i", str(c)]
    if isinstance(c, float):
        return ["f", str(struct.unpack("<Q", struct.pack("<d", c))[0])]
    if isinstance(c, str):
        return ["s", c]
    if isinstance(c, bytes):
        return ["b", list(c)]
    if isinstance(c, tuple):
        return ["T", [enc_const(x, table) for x in c]]
    if isinstance(c, frozenset):
        return ["Z", [enc_const(x, table) for x in c]]
    if isinstance(c, slice):
        return ["S", [enc_const(c.start, table), enc_const(c.stop, table), enc_const(c.step, table)]]
    if isinstance(c, types.CodeType):
        return ["c", dump(c, table)]
    raise TypeError(type(c))


def dump(co, table):
    idx = len(table)
    table.append(None)
    names = []
    n = 0
    while True:
        try:
            names.append(co._varname_from_oparg(n))
            n += 1
        except (IndexError, ValueError):
            break
    table[idx] = dict(name=co.co_name, qualname=co.co_qualname, flags=co.co_flags, argcount=co.co_argcount,
                      posonly=co.co_posonlyargcount, kwonly=co.co_kwonlyargcount, nlocalsplus=n,
                      ncellvars=len(co.co_cellvars), nfreevars=len(co.co_freevars), stacksize=co.co_stacksize,
                      consts=[enc_const(c, table) for c in co.co_consts], names=list(co.co_names),
                      localsplus=names, code=list(co.co_code), exctable=list(co.co_exceptiontable), index=idx)
    return idx


def gen_case(rng):
    fam = rng.choice(FAMILIES)
    src = fam(rng)
    try:
        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            co = compile(src, "<prog>", "exec")
    except SyntaxError:
        exclude("syntax-error")
        return None
    table = []
    main_idx = dump(co, table)
    fn = "quick" if rng.random() < 0.5 else "run"
    return dict(mod="bytecode", fn=fn, codes=table, main=main_idx, src=src, family=fam.__name__)


def run_python(case):
    import warnings
    buf = io.StringIO()
    exc = None
    g = {"__name__": "__main__"}
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        co = compile(case["src"], "<prog>", "exec")
        with contextlib.redirect_stdout(buf):
            try:
                exec(co, g)
            except BaseException as e:
                exc = [type(e).__name__, str(e)]
    # Finalizers of objects still alive at the end are not part of the program's
    # output, and must not run during a later case.
    with contextlib.redirect_stdout(io.StringIO()):
        g.clear()
        e = None
        gc.collect(1)
    return {"ok": {"out": buf.getvalue(), "exc": exc}}


if __name__ == "__main__":
    atexit.register(lambda: print("excluded", dict(sorted(EXCLUDED.items()))))
    main(gen_case, run_python)
