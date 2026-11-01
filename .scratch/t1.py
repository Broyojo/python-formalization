"""Smoke test: run a handful of programs through the machine and CPython."""
import sys, json, io, contextlib, types, struct, subprocess
sys.path.insert(0, 'difftest')
from common import PYDIFF

def enc_const(c, table):
    if c is None: return ["n"]
    if c is Ellipsis: return ["e"]
    if c is True: return ["t"]
    if c is False: return ["F"]
    if isinstance(c, int): return ["i", str(c)]
    if isinstance(c, float): return ["f", str(struct.unpack('<Q', struct.pack('<d', c))[0])]
    if isinstance(c, str): return ["s", c]
    if isinstance(c, bytes): return ["b", list(c)]
    if isinstance(c, tuple): return ["T", [enc_const(x, table) for x in c]]
    if isinstance(c, frozenset): return ["Z", [enc_const(x, table) for x in c]]
    if isinstance(c, slice): return ["S", [enc_const(c.start, table), enc_const(c.stop, table), enc_const(c.step, table)]]
    if isinstance(c, types.CodeType): return ["c", dump(c, table)]
    raise TypeError(type(c))

def dump(co, table):
    idx = len(table)
    table.append(None)
    names = []
    n = 0
    while True:
        try:
            names.append(co._varname_from_oparg(n)); n += 1
        except (IndexError, ValueError):
            break
    table[idx] = dict(name=co.co_name, qualname=co.co_qualname, flags=co.co_flags, argcount=co.co_argcount,
        posonly=co.co_posonlyargcount, kwonly=co.co_kwonlyargcount, nlocalsplus=n,
        ncellvars=len(co.co_cellvars), nfreevars=len(co.co_freevars), stacksize=co.co_stacksize,
        consts=[enc_const(c, table) for c in co.co_consts], names=list(co.co_names), localsplus=names,
        code=list(co.co_code), exctable=list(co.co_exceptiontable), index=idx)
    return idx

def case(src):
    co = compile(src, "<prog>", "exec")
    table = []
    main = dump(co, table)
    return dict(mod="bytecode", fn="run", codes=table, main=main)

def run_py(src):
    co = compile(src, "<prog>", "exec")
    buf = io.StringIO()
    exc = None
    with contextlib.redirect_stdout(buf):
        try:
            exec(co, {"__name__": "__main__"})
        except Exception as e:
            exc = [type(e).__name__, str(e)]
    return dict(out=buf.getvalue(), exc=exc)

PROGS = [
 "print(1+2)",
 "x=[1,2,3]\nfor i in x:\n    print(i*2)\n",
 "def f(a,b=2,*c,d=3,**e):\n    return (a,b,c,d,sorted(e.items()))\nprint(f(1))\nprint(f(1,2,3,4,d=5,z=6))\n",
 "def g():\n    yield 1\n    yield 2\n    return 3\nprint(list(g()))\nit=g()\nprint(next(it),next(it))\ntry:\n    next(it)\nexcept StopIteration as e:\n    print(e.value)\n",
 "class A:\n    def __init__(self,x):\n        self.x=x\n    def m(self):\n        return self.x+1\nclass B(A):\n    def m(self):\n        return super().m()*2\nprint(B(3).m())\n",
 "try:\n    1/0\nexcept ZeroDivisionError as e:\n    print('caught',e)\nfinally:\n    print('fin')\n",
 "class C:\n    def __enter__(self):\n        print('in');return 1\n    def __exit__(self,t,v,tb):\n        print('out',t);return True\nwith C() as x:\n    print(x)\n    raise ValueError('e')\nprint('after')\n",
 "print([i*i for i in range(5) if i%2])\nprint({i:str(i) for i in range(3)})\nprint(sorted({i%3 for i in range(9)}))\n",
 "def outer():\n    n=0\n    def inc():\n        nonlocal n\n        n+=1\n        return n\n    return inc\nf=outer()\nf();print(f())\n",
 "def f():\n    yield from range(3)\n    r=yield from g()\n    print('r',r)\ndef g():\n    x=yield 1\n    print('x',x)\n    return 5\nit=f()\nprint(list(it))\n",
 "match (1,[2,3]):\n    case (a,[b,*c]):\n        print(a,b,c)\n",
 "print(f'{1+1} {\"a\"!r} {3:>4}')\nprint(1.5+2,2**10,7//2,-7%3,3/2,1e300*1e10)\n",
 "raise ValueError('boom')\n",
 "print(undefined_name)\n",
 "a,*b,c=[1,2,3,4]\nprint(a,b,c)\nx,y=1,2\nx,y=y,x\nprint(x,y)\n",
 "def f(x):\n    return 1 if x else 2\nprint(f(0),f(1),not 1, None is None, 1 in [1], 'a' not in 'abc')\n",
 "d={'a':1}\nd['b']=2\ndel d['a']\nprint(d,len(d),list(d.items()))\nl=[3,1,2]\nl.sort()\nl.append(4)\nprint(l,l[1:3],l[::-1])\n",
 "class P:\n    @property\n    def x(self):\n        return 42\n    @staticmethod\n    def s(a):\n        return a\n    @classmethod\n    def c(cls):\n        return cls.__name__\nprint(P().x,P.s(1),P.c(),P().c())\n",
 "import_ok=1\ntry:\n    try:\n        raise KeyError('k')\n    except KeyError as e:\n        raise ValueError('v') from e\nexcept ValueError as e2:\n    print(repr(e2),repr(e2.__cause__),e2.__context__ is e2.__cause__)\n",
]

cases = [case(p) for p in PROGS]
proc = subprocess.run([str(PYDIFF)], input="".join(json.dumps(c) + "\n" for c in cases), capture_output=True, text=True)
print(proc.stderr[:2000])
out = proc.stdout.splitlines()
good = 0
for p, line in zip(PROGS, out):
    lo = json.loads(line)
    py = run_py(p)
    if lo.get('ok') == py:
        good += 1
    else:
        print("MISMATCH", repr(p)); print("  py  ", py); print("  lean", lo)
print(good, '/', len(PROGS))
