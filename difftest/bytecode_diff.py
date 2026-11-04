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
            "iter([1, 2])", "(i for i in range(2))", "{1: 2, 3: 4, 5: 6}", "It(1)", "It(2)", "It(3)", "It(4)",
            "L([1, 2, 3])", "Q()", "D()", "(1, 2, 3)", "[1, 2, 3, 4]", "{1: 2}", "{}", "'abcd'",
            "V(0)", "V(1)", "V(2)", "V(3)", "V(4)", "V(5)", "V(6)"]
    for _ in range(r.randint(3, 6)):
        s = r.choice(srcs)
        tgt = r.choice(["a, b", "a, *b", "*a, b", "a, b, *c", "a, *b, c", "a,", "[a, b]", "(a, (b, c))", "*a,",
                        "a, b, c", "a, *b, c, d", "a, b, *c, d"])
        out.append(guarded(f"{tgt} = {s}\nprint(a)"))
    # How many times `__next__` ran, the exhausting call included
    out.append("for n in range(4):\n    it = It(n)\n    try:\n        a, b = it\n    except ValueError as e:\n        print(e)\n    print(it.calls)\n"
               "    it = It(n)\n    try:\n        a, *b, c = it\n        print(a, b, c)\n    except ValueError as e:\n        print(e)\n    print(it.calls)\n")
    head = ("class It:\n    def __init__(self, n):\n        self.n, self.calls = n, 0\n    def __iter__(self):\n        return self\n"
            "    def __next__(self):\n        self.calls += 1\n        if self.calls > self.n:\n            raise StopIteration\n        return self.calls\n"
            "class L(list):\n    pass\nclass Q:\n    __iter__ = None\nclass D:\n    def __iter__(self):\n        raise TypeError('x')\n"
            # `PySequence_List(it)` goes through `_PyList_Extend`: `iter(it)` and `__length_hint__`
            # of the iterator run before the drain (`list_extend_iter_lock_held`)
            "class W:\n    def __init__(self, k):\n        self.k, self.n = k, 0\n    def __iter__(self):\n"
            "        if self.k == 1:\n            raise ValueError('w-iter')\n        if self.k == 2:\n            return iter([7, 8, 9])\n        return self\n"
            "    def __next__(self):\n        self.n += 1\n        if self.k == 6 and self.n == 3:\n            raise KeyError('w-next')\n"
            "        if self.n > 3:\n            raise StopIteration\n        return self.n\n"
            "    def __length_hint__(self):\n        if self.k == 3:\n            raise KeyError('w-lh')\n        if self.k == 4:\n            return 'x'\n"
            "        if self.k == 5:\n            return -1\n        if self.k == 0:\n            raise TypeError('w-lh-type')\n        return NotImplemented\n"
            "class V:\n    def __init__(self, k):\n        self.k = k\n    def __iter__(self):\n        return W(self.k)\n")
    return head + "\n".join(out)


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
        # `_PyEval_FormatExcCheckArg` sets `.name` on a NameError, not on an UnboundLocalError
        "def f():\n    return nope_q\ndef g():\n    y = y\ndef h():\n    def k():\n        return w\n    k()\n    w = 1\n"
        "for fn in (f, g, h):\n    try:\n        fn()\n    except NameError as e:\n        print(type(e).__name__, e.name)\n"
        "try:\n    del nope_r\nexcept NameError as e:\n    print(e.name)\nprint(NameError('m').name)",
        "def f():\n    x = 5\n    r = [x for x in range(2)]\n    return x, r\nprint(f())",
        "def f():\n    try:\n        return [1 / i for i in [1, 0]]\n    except ZeroDivisionError:\n        return i\n" + guarded("f()"),
    ])


def p_exc(r):
    kinds = ["ValueError('v')", "KeyError('k')", "TypeError", "ZeroDivisionError('z')", "StopIteration(5)", "RuntimeError()",
             "1", "'x'", "None", "Exception('a', 'b')", "AttributeError('at')"]
    e = r.choice(kinds)
    # `T(...)`: a tuple subclass, which `_PyEval_CheckExceptTypeValid` and
    # `PyErr_GivenExceptionMatches` take item by item (`PyTuple_Check`)
    h = r.choice(["ValueError", "(KeyError, TypeError)", "Exception", "BaseException", "ArithmeticError", "1", "(1, 2)", "()", "LookupError",
                  "T((KeyError, ValueError))", "T((ValueError,))", "T(())", "T((1,))", "T((KeyError, T((ValueError,))))"])
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
    t = "class T(tuple):\n    pass\n" + t
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
                      # `%T` is the qualified name; the suggestion needs `tp_descr_get` on both
                      "class O:\n    class I:\n        pass\n" + guarded("with O.I():\n    pass"),
                      "def mk():\n    class L:\n        pass\n    return L\n" + guarded("with mk()():\n    pass"),
                      "class NS:\n    __aenter__ = " + r.choice(["1", "len", "staticmethod(len)", "lambda s: 1"]) + "\n"
                      "    async def __aexit__(self, *a):\n        pass\n" + guarded("with NS():\n    pass"),
                      "class NA:\n    __enter__ = " + r.choice(["1", "len", "lambda s: 1"]) + "\n"
                      "    def __exit__(self, *a):\n        pass\n" + guarded("async def f():\n    async with NA():\n        pass\nf().send(None)"),
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
        # `_PyCoro_GetAwaitableIter`: the coroutine test comes first on 3.15
        "async def co():\n    return 1\nclass R:\n    def __await__(self):\n        return co()\nasync def f():\n    await R()\n" + guarded("drive(f())"),
        "class R:\n    def __await__(self):\n        return 1\nasync def f():\n    await R()\n" + guarded("drive(f())"),
        "class R:\n    def __await__(self):\n        return iter([1, 2])\nasync def f():\n    return await R()\nprint(drive(f()))\n",
        # `yield from` on a coroutine, and `await` on a coroutine that is already being awaited
        "async def co():\n    return 1\ndef g():\n    yield from co()\n" + guarded("next(g())"),
        "async def f():\n    await A()\nc = f()\nc.send(None)\nasync def g():\n    await c\n" + guarded("drive(g())") + "\n" + guarded("c.close()"),
        # `_PyEval_GetANext`: whatever `_PyCoro_GetAwaitableIter` raises becomes the cause and the
        # context of the TypeError, also inside a handler (`_PyErr_FormatFromCause`)
        "class W:\n    def __await__(self):\n        raise " + r.choice(["ValueError('w')", "TypeError('t')", "KeyError(1)"]) + "\n"
        "class AI:\n    def __aiter__(self):\n        return self\n    def __anext__(self):\n        return " + r.choice(["W()", "5", "None", "iter([1])"]) + "\n"
        "async def f():\n    async for x in AI():\n        pass\n"
        "def show():\n    try:\n        drive(f())\n    except Exception as e:\n"
        "        print(type(e).__name__, e, repr(e.__cause__), repr(e.__context__), e.__suppress_context__)\n"
        "show()\ntry:\n    raise OSError('handled')\nexcept OSError:\n    show()\n",
        "class NA:\n    def __aiter__(self):\n        return " + r.choice(["1", "self", "[]"]) + "\nasync def f():\n    async for x in NA():\n        pass\n" + guarded("drive(f())"),
    ])


def p_virtual(r):
    """`GET_ITER` on 3.15: the sequence and a tagged index for exact list, tuple, str and bytes
    (`_tp_iteritem`), the iterator and NULL for the rest, and the opcodes that read the two
    slots. The loop runs twice, so that `quick` has seen one type when it meets the other."""
    seqs = ["[1, 2, 3]", "(4, 5)", "'xé'", "b'ab'", "[]", "()", "''", "b''", "range(3)", "iter([1, 2])",
            "L([7, 8])", "(i for i in [1, 2])", "{'k': 1}", "{1}", "map(str, [1])"]
    a, b = r.choice(seqs), r.choice(seqs)
    head = "class L(list):\n    pass\n"
    k = r.random()
    if k < 0.3:
        return head + f"def f(s):\n    t = []\n    for x in s:\n        t.append(x)\n    return t\nprint(f({a}), f({b}), f({a}))\n"
    if k < 0.6:
        return (head + "def g(s):\n    r = yield from s\n    yield 'end', r\n"
                + f"print(list(g({a})), list(g({b})))\n"
                # what the exhausted path leaves on the stack shows only with values below it
                + "def h(s):\n    for n in [1, 2]:\n        yield from s\n        yield n\n    t = [0, (yield from s), 1]\n    yield t\n    yield [(yield from s), (yield from s)]\n"
                + f"print(list(h({a})), list(h({b})))\n"
                # a sub-iterator that ends on a throw: `CLEANUP_THROW` takes the value out of the `StopIteration`
                + "def inner():\n    try:\n        yield 1\n    except ValueError:\n        return 5\n"
                + "class T:\n    def __iter__(self):\n        return self\n    def __next__(self):\n        return 1\n    def throw(self, *a):\n        raise StopIteration(7)\n"
                + "def w(s):\n    q = [0, (yield from s), 2]\n    yield q\n"
                + guarded("x = w(inner())\nprint(next(x))\nprint(x.throw(ValueError('t')))") + "\n"
                + guarded("x = w(T())\nprint(next(x))\nprint(x.throw(ValueError('t')))") + "\n"
                + guarded("x = w(T())\nprint(next(x))\nprint(x.throw(KeyError('k')))") + "\n"
                + guarded(f"x = g({a})\nprint(next(x))\nprint(x.send({r.choice(['None', '5'])}))\nprint(x.gi_yieldfrom is None, x.gi_running, x.gi_suspended)")
                + "\n" + guarded(f"x = g({b})\nprint(next(x))\nprint(x.throw(ValueError('t')))")
                + "\n" + guarded(f"x = g({a})\nprint(next(x))\nprint(x.close(), x.gi_suspended)")
                + "\n" + guarded(f"x = g({b})\nprint(next(x))\nprint(x.throw(GeneratorExit))"))
    if k < 0.8:
        return ("l = [1, 2, 3, 4]\nfor x in l:\n    print(x)\n    if x == 1:\n        l.pop()\n    if x == 2:\n        l.append(9)\n"
                "l = [1, 2]\nfor x in l:\n    l.clear()\n    print(x)\n"
                "l = []\nfor x in l:\n    print(x)\nl.append(1)\nprint(list(l))\n"
                "def g(l):\n    yield from l\nl = [1, 2, 3]\nx = g(l)\nprint(next(x))\nl.pop()\nl.pop()\nprint(list(x))\n"
                "def h():\n    for a in [1, 2]:\n        for b in 'xy':\n            for c in (3,):\n                if b == 'y':\n                    break\n                yield a, b, c\nprint(list(h()))\n")
    return ("class I:\n    def __iter__(self):\n        return self\n    def __next__(self):\n"
            f"        {r.choice(['del I.__next__', 'I.__next__ = None', 'raise StopIteration'])}\n        return 1\n"
            + guarded("for x in I():\n    print('item', x)")
            + "\nclass J:\n    def __iter__(self):\n        return self\n    def __next__(self):\n        del J.__next__\n        return 1\n"
            + "def g():\n    yield from J()\n" + guarded("print(list(g()))"))


def p_fastpath(r):
    """The specialized forms whose bodies changed on 3.15, on both sides of their guards. Each
    runs twice with different operands, so `quick` deopts on the second."""
    big = ["2**30-1", "2**30", "-(2**30)+1", "-(2**30)", "2**31", "1", "0", "-1", "2**62", "10**20", "True"]
    a, b, c = r.choice(big), r.choice(big), r.choice(big)
    idx = ["0", "1", "-1", "-3", "-4", "3", "2**30", "-(2**30)", "2**63", "True", "'a'"]
    i, j = r.choice(idx), r.choice(idx)
    op = r.choice(["+", "-", "*"])
    s = r.choice(["'abc'", "'aé'", "'é'", "''"])
    pool = [
        f"def f(x, y):\n    return x {op} y\nprint(f({a}, {b}), f({b}, {c}), f({c}, {a}), f(1.5, 2.5), f(1, 2))\n",
        f"def f(l, i):\n    return l[i]\n" + guarded(f"print(f([1, 2, 3], {i}))") + "\n" + guarded(f"print(f([1, 2, 3], {j}))")
        + "\n" + guarded(f"print(f((1, 2), {i}))") + "\n" + guarded(f"print(f({s}, {j}))") + "\n" + guarded(f"print(f({s}, {i}))"),
        f"def f():\n    s = {s}\n    t = s\n    for x in 'ab':\n        s += x\n        s = s + 'c'\n    return s, t\nprint(f())\n",
        "def f(l, v):\n    l.append(v)\n    return l\nprint(f([], 1), f([1], 2), f(L(), 3))\n".replace("def f", "class L(list):\n    pass\ndef f", 1),
        "def f(*a, **k):\n    return a, sorted(k.items())\ndef g(x, *a):\n    return f(x, *a), f(*a, **{'k': x})\n"
        "print(g(1), g(1, 2), g(1, 2, 3), f(*(1, 2)), f(*[3], **{'z': 1}))\n"
        + guarded("print(len(*[1, 2]))") + "\n" + guarded("print(f(**{'a': 1}, **{'a': 2}))"),
        f"def f(o, c):\n    return isinstance(o, c)\nprint(f(1, int), f('a', int), f(1, (str, int)))\n" + guarded("print(f(1, 1))")
        + "\nclass C:\n    def m(self, c):\n        return isinstance(self, c)\nprint(C().m(C), C.m(C(), int))\n",
        "class P:\n    def __init__(self):\n        self.n = 0\n    @property\n    def p(self):\n        self.n += 1\n        return self.n\n"
        "def f(o):\n    return o.p\nx = P()\nprint(f(x), f(x), f(x))\n"
        "class Q:\n    def __getattribute__(self, n):\n        return 'ga:' + n\ndef g(o):\n    return o.p\nprint(g(Q()), g(Q()), g(x))\n",
        # TO_BOOL_INT and COMPARE_OP_INT exit on an int past one digit (3.15 `_GUARD_TOS_INT`);
        # `-x`/`~x` raising keeps the operand (`ERROR_NO_POP`); a raising `__next__` ends a loop
        f"def t(x):\n    return 1 if x else 0\ndef c(x, y):\n    return x < y, x == y, x >= y\n"
        f"print(t(0), t({a}), t({b}), t(0), t({c}))\nprint(c(1, 2), c({a}, {b}), c({b}, {c}), c(1, 2))\n"
        "class N:\n    def __neg__(self):\n        raise ValueError('neg')\n    def __invert__(self):\n        raise KeyError('inv')\n"
        + guarded("print(-N())") + "\n" + guarded("print(~N())") + "\n"
        + "class It:\n    def __init__(self):\n        self.n = 0\n    def __iter__(self):\n        return self\n    def __next__(self):\n"
        "        self.n += 1\n        if self.n > 2:\n            raise ValueError(self.n)\n        return self.n\n"
        + guarded("for v in It():\n    print(v)"),
        # one site per form: a site first reached by another type specializes to that type
        "def f(s, i):\n    return s[i]\n" + guarded(f"print(f('aé☃', {r.choice(['0', '1', '2', '3', '-1', 'True', '-4'])}))")
        + "\n" + guarded(f"print(f('aé☃', {j}))") + "\n" + guarded(f"print(f('abc', {i}))"),
        "class G:\n    def __getitem__(self, k):\n        return k * 2\nclass H(G):\n    def __getitem__(self, k):\n        return super().__getitem__(k) + 1\n"
        "class B:\n    def __getitem__(self, k, extra):\n        return k\n"
        "def f(o, k):\n    return o[k]\nprint(f(G(), 2), f(G(), 'a'))\n" + guarded("print(f(H(), 3))") + "\n" + guarded("print(f(B(), 3))")
        + "\n" + guarded(f"print(f([1], {i}))") + "\nG.__getitem__ = lambda self, k: 'new'\nprint(f(G(), 2))\n",
        "class M:\n    def __init__(self):\n        self.v = 1\n    def m(self, a, b=2):\n        return self.v + a + b\n    def n(self):\n        return self.v\n"
        "def f(o):\n    return o.n(), o.m(1), o.m(1, 2), o.m(a=1), o.m(1, b=3)\nprint(f(M()), f(M()))\n"
        "def t(o):\n    return 1 if o else 0\nclass E:\n    def __len__(self):\n        return 0\nprint(t(M()), t(M()), t(E()))\n"
        "b = M().m\nprint(b(1), b(1, 2), b(a=1), b(1, b=3))\n"
        "M.__len__ = lambda self: 0\nprint(t(M()))\n",
        # `fixup_getiter`: a coroutine is fine in an iterable coroutine and refused in a plain generator
        "async def c():\n    return 1\ndef itercoro_g(x):\n    r = yield from x\n    yield r\ndef plain(x):\n    r = yield from x\n    yield r\n"
        + guarded("print(list(itercoro_g(c())))") + "\n" + guarded("print(list(plain(c())))") + "\n" + guarded("print(list(itercoro_g([1, 2])))") + "\n"
        + "def drive(o):\n    out = []\n    try:\n        while True:\n            out.append(o.send(None))\n    except StopIteration as e:\n        return out, e.value\n"
        + "def itercoro_h():\n    yield 7\n    return 8\nasync def a():\n    return await itercoro_h()\n" + guarded("print(drive(a()))") + "\n",
        # `LOAD_COMMON_CONSTANT` only feeds the `is` test that picks the inlined call for a
        # generator argument, so a wrong constant shows only with the name rebound
        "def f(x):\n    return set(i for i in x), list(i for i in x), tuple(i for i in x), all(i for i in x), any(i for i in x)\n"
        "a, *c = f([1, 1, 0])\nprint(sorted(a), c)\n"
        "set = list\nlist = tuple\ntuple = sorted\nall = any\nany = len\n" + guarded("print(f([1, 1, 0]))") + "\n",
    ]
    return r.choice(pool)


def p_messages(r):
    """Error messages that moved to the `%T...must return` form on 3.15, and the `**` and
    `%` paths around them."""
    bad = ["1", "None", "[]"]
    v = r.choice(bad)
    pool = [
        f"class A:\n    def __str__(self):\n        return {v}\n" + guarded("print(str(A()))"),
        f"class A:\n    def __repr__(self):\n        return {v}\n" + guarded("print(repr(A()))") + "\n" + guarded("print(str(A()))"),
        f"class A:\n    def __index__(self):\n        return {r.choice(['None', '[]', chr(39) + 'a' + chr(39)])}\n" + guarded("print([1, 2][A()])"),
        f"class A:\n    def __format__(self, s):\n        return {v}\n" + guarded("print(f'{A()}')") + "\n" + guarded("print(f'{A():>3}')") + "\n" + guarded("print(format(A()))"),
        f"class A:\n    def __iter__(self):\n        return {v}\n" + guarded("print(list(A()))") + "\n" + guarded("for x in A():\n    pass"),
        f"class A:\n    def __bool__(self):\n        return {v}\n" + guarded("print(not A())") + "\n" + guarded("print(bool(A()))"),
        "class K:\n    def keys(self):\n        raise AttributeError('inner')\ndef f(**k):\n    return k\n" + guarded("print(f(**K()))") + "\n" + guarded("print(f(**1))") + "\n" + guarded("print(f(*1))"),
        "class K:\n    @property\n    def keys(self):\n        raise AttributeError('p')\ndef f(**k):\n    return k\n" + guarded("print(f(**K()))"),
        f"print('a' % ())\n" + guarded(f"print('a' % ({r.choice(['1', 'None', chr(39) + 'x' + chr(39)])}))") + "\n" + guarded("print('a' % (1, 2))") + "\n"
        + guarded("print(b'a' % (1, 2, 3))") + "\n" + guarded("print(b'a' % 1)") + "\n" + guarded("print('a' % {})") + "\n" + guarded("print('a' % [])"),
    ]
    return r.choice(pool)


def p_builders(r):
    """`DICT_MERGE`/`DICT_UPDATE`/`LIST_EXTEND`/`SET_ADD` on 3.15: the `dupkey` of
    `_PyDict_MergeUniq` and `_PyObject_FunctionStr` (a `KeyError` from the mapping is no longer a
    duplicate), the `keys` probe that decides whether an `AttributeError` becomes the `TypeError`,
    the `__context__` it leaves, and the exact-set check of `SET_ADD` (gh-154902)."""
    head = (
        "def f(**k):\n    return sorted(k.items())\n"
        "class C:\n    def m(self, **k):\n        return k\n"
        "class M:\n    def keys(self):\n        return ['a']\n    def __getitem__(self, k):\n        raise KeyError('zz')\n"
        "class N:\n    def keys(self):\n        raise AttributeError('inner')\n"
        "class P:\n    @property\n    def keys(self):\n        raise ValueError('vk')\n"
        "class Q:\n    def __getattr__(self, n):\n        raise AttributeError(n)\n"
        "class T:\n    n = 0\n    @property\n    def keys(self):\n        T.n += 1\n        if T.n % 2:\n            raise AttributeError('first')\n        raise ValueError('second')\n"
        "class G:\n    def keys(self):\n        return ['a', 'b']\n    def __getitem__(self, k):\n        return k * 2\n"
        "class FQ:\n    def __getattribute__(self, n):\n        if n == '__qualname__':\n            raise ValueError('q')\n        return object.__getattribute__(self, n)\n    def __call__(self, **k):\n        return k\n"
        "class NoQ:\n    def __getattribute__(self, n):\n        if n == '__qualname__':\n            raise AttributeError('q')\n        return object.__getattribute__(self, n)\n    def __call__(self, **k):\n        return k\n    def __str__(self):\n        return 'NOQ'\n"
        "class StrQ:\n    def __getattribute__(self, n):\n        if n == '__qualname__':\n            return 5\n        if n == '__module__':\n            return 'builtins'\n        return object.__getattribute__(self, n)\n    def __call__(self, **k):\n        return k\n"
        "class Inner:\n    class K:\n        pass\n"
    )
    exprs = ["f(a=1, **{'a': 2})", "f(**{'a': 1}, **{'a': 2})", "C().m(**{'a': 1}, **{'a': 2})",
             "(lambda **k: k)(**{'a': 1}, **{'a': 2})", "print(**{'sep': 1}, **{'sep': 2})",
             "f(**M())", "f(a=1, **M())", "f(**N())", "f(**P())", "f(**Q())", "f(**1)", "f(**Inner.K())",
             "{**1}", "{**N()}", "{**P()}", "{**Inner.K()}", "{**M()}", "[*1]", "{*1}", "f(**G())",
             "f(**G(), **{'c': 1})", "f(**G(), **{'a': 1})", "{**G(), 'z': 0}", "FQ()(**{'a': 1}, **{'a': 2})",
             "NoQ()(**{'a': 1}, **{'a': 2})", "StrQ()(**{'a': 1}, **{'a': 2})", "f(**{'a': 1}, b=2, **{'b': 3})",
             "[*[1], *(2,), *'ab', *range(2)]", "{*[1], *{2: 3}, *(1,)}"]
    out = [head]
    for x in r.sample(exprs, r.randint(4, 10)):
        out.append(guarded(f"print({x})"))
    # `_PyObject_FunctionStr`: both lookups and the comparison come before `str()`, the module first
    fs = r.choice(["raise ValueError('m')", "raise AttributeError('m')", "return QS('m')", "return 'builtins'",
                   "return None", "return QS('builtins')", "return NE(0)", "return NE(1)", "return NE(2)",
                   "return NE(3)", "return QS('bad')"])
    qn = r.choice(["QS('q')", "QS('q')", "QS('bad')"])
    # `PyObject_RichCompareBool(module, "builtins", Py_NE)` raising or its result's truth test
    # raising, `str(qualname)` raising, `str(x)` raising with no `__qualname__`: all NULL, so
    # 'function'; a raising `str(dupkey)` is the exception DICT_MERGE raises
    out.append("class QS:\n    def __init__(self, t):\n        self.t = t\n    def __str__(self):\n        print('str', self.t)\n"
               "        if self.t == 'bad':\n            raise KeyError('str-bad')\n"
               "        return self.t\n"
               "class TB:\n    def __bool__(self):\n        raise KeyError('tb')\n"
               "class NE:\n    def __init__(self, k):\n        self.k = k\n    def __ne__(self, o):\n        print('ne', o)\n"
               "        if self.k == 0:\n            raise ValueError('ne')\n        if self.k == 1:\n            return TB()\n"
               "        return self.k == 2\n    def __str__(self):\n        return 'NE' + str(self.k)\n"
               "class NoQS:\n    def __getattribute__(self, n):\n        if n == '__qualname__':\n            raise AttributeError('q')\n"
               "        return object.__getattribute__(self, n)\n    def __call__(self, **k):\n        return k\n"
               "    def __str__(self):\n        raise KeyError('nostr')\n"
               "class SS(str):\n    def __str__(self):\n        print('dupkey str')\n        raise ValueError('dup-str')\n"
               "class SK(str):\n    pass\n"
               + guarded("print(NoQS()(**{'a': 1}, **{'a': 2}))") + "\n"
               + guarded(f"print(f(**{{'a': 1}}, **{{{r.choice(['SS', 'SK'])}('a'): 2}}))") + "\n"
               + guarded(f"print(f(**{{{r.choice(['SS', 'SK'])}('a'): 1}}, a=2))") + "\n"
               "class FX:\n    def __getattribute__(self, n):\n        if n == '__qualname__':\n"
               f"            return {qn}\n"
               f"        if n == '__module__':\n            {fs}\n        return object.__getattribute__(self, n)\n"
               "    def __call__(self, **k):\n        return k\n" + guarded("print(FX()(**{'a': 1}, **{'a': 2}))"))
    # a failed SET_ADD / MAP_ADD / LIST_APPEND leaves the container for the cleanup handler
    out.append(r.choice([
        "def h():\n    x = 'keep'\n    try:\n        {[] for x in range(1)}\n    except TypeError as e:\n        print(e)\n    return x\nprint(h())",
        "def h():\n    x = 'keep'\n    try:\n        {x: [] for x in [1, []]}\n    except TypeError as e:\n        print(e)\n    return x\nprint(h())",
        "def h():\n    x = 'keep'\n    try:\n        {[]: x for x in range(2)}\n    except TypeError as e:\n        print(e)\n    return x\nprint(h())",
        "def h(n):\n    try:\n        return [{y for y in [x, []]} for x in range(n)]\n    except TypeError as e:\n        return str(e)\nprint(h(0), h(2))",
        guarded("print({x for x in [1, [], 2]})"),
        guarded("print({k: v for k, v in [(1, 2), ([], 3)]})"),
        "class G:\n    def __init__(self):\n        self.n = 0\n    def __iter__(self):\n        return self\n    def __next__(self):\n"
        "        self.n += 1\n        if self.n > 2:\n            raise ValueError('g')\n        return self.n\nl = [0]\n"
        + guarded("l.extend(G())") + "\nprint(l)\nl += [5]\nl.extend(l)\nprint(l)\nl.extend((7,))\nl.extend({8: 9})\nl.extend({8: 9}.items())\nprint(l)",
    ]))
    out.append(r.choice([
        "for _ in range(2):\n    try:\n        f(**T())\n    except Exception as e:\n        print(type(e).__name__, e, repr(e.__context__))\n",
        "for _ in range(2):\n    try:\n        {**T()}\n    except Exception as e:\n        print(type(e).__name__, e, repr(e.__context__))\n",
        "__conditional_annotations__ = " + r.choice(["[]", "{}", "1", "frozenset()", "set()"]) + "\n"
        + guarded("if True:\n    x: int = 1\nprint('annotated')"),
        "print({x for x in [1, 2, 1]} == {1, 2}, {k: v for k, v in [(1, 2), (1, 3)]})",
    ]))
    return "\n".join(out)


def p_call_generic(r):
    """`CALL`, `CALL_KW`, `CALL_FUNCTION_EX` on every kind of callable: a bound method object
    (expanded by `_MAYBE_EXPAND_METHOD`), a function (inlined, the frame failing on bad arguments),
    a builtin, a class, an instance with `__call__` (`tp_call`: `PyObject_Call` hands it the dict),
    `*` of a non-tuple iterable (`_MAKE_CALLARGS_A_TUPLE`), and `**` with a non-str key."""
    head = ("class P:\n    def __init__(self):\n        self.v = 1\n    def m(self, a=0, *r, k=0, **kw):\n"
            "        return (self.v, a, r, k, sorted(kw.items()))\n"
            "class D:\n    @property\n    def __call__(self):\n        print('lookup')\n        return lambda *a, **k: (a, sorted(k.items()))\n"
            "class E:\n    def __call__(self, *a, **k):\n        return ('E', a, sorted(k.items()))\n"
            "class It:\n    def __iter__(self):\n        print('iter')\n        return iter([1, 2])\n"
            "class Bad:\n    def __iter__(self):\n        raise " + r.choice(["TypeError('inner')", "ValueError('v')"]) + "\n"
            "def f(a, b=2, *c, d=4, **e):\n    return (a, b, c, d, sorted(e.items()))\n"
            "def g(x, /, y):\n    return (x, y)\n"
            "class K:\n    def __init__(self, *a, **k):\n        self.a = (a, sorted(k.items()))\n"
            # `_PyStack_UnpackDict` takes any key whose type has Py_TPFLAGS_UNICODE_SUBCLASS
            "class S(str):\n    pass\n"
            "class S2(S):\n    pass\n"
            "class NS:\n    def __hash__(self):\n        return 1\n")
    # builtins only where the model's argument parsing is CPython's: their messages for bad
    # arguments belong to the builtins, not to the call instructions
    callees = ["P().m", "bm", "f", "g", "D()", "E()", "K", "(lambda *a, **k: (a, k))", "P.m"]
    argss = ["", "1", "1, 2", "1, 2, 3", "a=1", "k=5", "1, k=5", "1, d=5", "x=1", "1, y=2", "*[1, 2]", "*It()",
             "*(1,)", "*Bad()", "*5", "**{'a': 1}", "**{1: 2}", "*[1], **{'k': 3}", "*It(), **{'zz': 0}",
             "1, *[2], **{'b': 3}", "**{'d': 1, 'k': 2}", "**{S('a'): 1}", "**{S('k'): 1}", "1, **{S2('d'): 7}",
             "**{S('zz'): 1}", "**{'a': 1, NS(): 2}", "**{S('a'): 1, 3: 2}", "**{b'a': 1}", "1, **{S('x'): 0}"]
    out = [head, "bm = P().m", guarded("print(*It(), sep='-')"), guarded("print(len(*[[1, 2]]), dict(**{'a': 1}))"),
           guarded("print(*Bad())"), guarded("print(**{1: 2})")]
    for _ in range(r.randint(4, 10)):
        c, a = r.choice(callees), r.choice(argss)
        out.append(guarded(f"print(K({a}).a if {c!r} == 'K' else {c}({a}))"))
    # the specialized Python calls: exact-args functions and methods, defaults, keyword-only
    # parameters (never EXACT_ARGS), *args, keywords to a bound method, f(*t, **d)
    out.append("def x2(a, b):\n    return (a, b)\n"
               "def xd(a, b=7):\n    return (a, b)\n"
               "def xk(a, *, b=3):\n    return (a, b)\n"
               "def xv(a, *r):\n    return (a, r)\n"
               "class XM:\n    def m(self, a):\n        return ('m', a)\n    def n(self, a, b=1):\n        return ('n', a, b)\n"
               "xo = XM()\n"
               "for _ in range(4):\n"
               "    print(x2(1, 2), xd(1), xd(1, 2), xk(1), xk(1, b=4), xv(1), xv(1, 2), xo.m(5), xo.n(5), xo.n(a=5, b=6),\n"
               "          x2(*(1, 2)), xd(*[1], **{'b': 9}), xo.m(*(3,)), xk(*(1,), **{S('b'): 8}))\n")
    out.append(guarded("for _ in range(3):\n    print(x2(1))") + "\n" + guarded("for _ in range(3):\n    print(xo.m(a=1, z=2))"))
    # a site that specialized to CALL_EX_PY, then gets a non-function: `_MAKE_CALLARGS_A_TUPLE` has
    # already converted the iterable when `_CHECK_IS_PY_CALLABLE_EX` exits, and CALL_FUNCTION_EX
    # does not iterate it again
    out.append("def site(h, x):\n    return h(*x)\n"
               "for _ in range(4):\n    print(site(x2, It()), site(x2, [3, 4]))\n"
               + guarded("print(site(" + r.choice(["E()", "max", "bm", "P().m"]) + ", " + r.choice(["It()", "[5, 6]", "Bad()", "5", "(7, 8)"]) + "))"))
    out.append(guarded("print(dict(**{S('a'): 1}), sorted(dict(**{S('b'): 2, 'c': 3}).items()))"))
    out.append(guarded("print(dict(**{S('a'): 1, 2: 3}))"))
    out.append("def loop(h):\n    for _ in range(3):\n        print(h(1), h(1, k=2), h(*[1]), h(*(1,), **{'k': 2}), h(1, **{S('k'): 3}))\n"
               + guarded("loop(" + r.choice(["bm", "P().m", "E()", "f", "(lambda *a, **k: (a, sorted(k.items())))"]) + ")"))
    return "\n".join(out)


def p_float_repr(r):
    """`repr` around powers of two, where the rounding interval is uneven."""
    lines = []
    for _ in range(6):
        e = r.choice([r.randint(-1074, 1023), r.randint(-60, 60), -24, -44])
        lines.append(f"x = 2.0 ** {e}\nprint(x, -x, x * 3, x / 3, x + x)")
    return "\n".join(lines)


# Identifiers around the 200 bytes of `%.200s`, which cuts UTF-8 bytes, not characters:
# 2-, 3- and 4-byte characters, a cut that falls inside one, and ASCII on both sides of it.
LONG_NAMES = ["é" * 101, "a" + "é" * 100, "é" * 100, "中" * 67, "ab" + "中" * 66,
              "\U00010000" * 51, "x" * 199 + "é", "x" * 201, "ж" * 99 + "xyz"]


def p_long_names(r):
    """`%.200s` of a name or a `tp_name` (NameError, unpack, `*`), and `%T` (`**`), with long
    non-ASCII identifiers."""
    n = r.choice(LONG_NAMES)
    return r.choice([
        guarded(f"print({n})"),
        f"def f():\n    return {n}\n" + guarded("f()"),
        f"class {n}:\n    pass\n" + guarded(f"a, b = {n}()"),
        f"class {n}:\n    pass\n" + guarded(f"print(*{n}())"),
        f"class {n}:\n    pass\n" + guarded(f"print([*{n}()])"),
        f"class {n}:\n    pass\n" + guarded(f"print({{**{n}()}})"),
        f"class {n}:\n    pass\n" + guarded(f"print(type({n}()).__name__ == {n!r})"),
    ])


FAMILIES = [p_arith, p_seq, p_unpack, p_loops, p_calls, p_scope, p_exc, p_with, p_gen, p_class, p_comp, p_match, p_strs, p_async,
            p_virtual, p_fastpath, p_messages, p_float_repr, p_long_names, p_builders, p_call_generic]


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


def mark_iterable_coroutines(co):
    """Set `CO_ITERABLE_COROUTINE` on every function named `itercoro_*`, as `types.coroutine`
    does: these programs cannot import. Both sides run the marked code."""
    consts = tuple(mark_iterable_coroutines(c) if isinstance(c, types.CodeType) else c for c in co.co_consts)
    flags = co.co_flags | 0x100 if co.co_name.startswith("itercoro_") else co.co_flags
    return co.replace(co_consts=consts, co_flags=flags)


def gen_case(rng):
    fam = rng.choice(FAMILIES)
    src = fam(rng)
    try:
        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            co = mark_iterable_coroutines(compile(src, "<prog>", "exec"))
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
        co = mark_iterable_coroutines(compile(case["src"], "<prog>", "exec"))
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
