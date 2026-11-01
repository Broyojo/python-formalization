"""Reproducers to run once the pod is back."""
import sys

# --- anext(x, default) restarts __await__ on every resume
class Aw:
    calls = 0
    def __await__(self):
        Aw.calls += 1
        yield 1
        yield 2
        return 'done'
class A:
    def __aiter__(self): return self
    def __anext__(self): return Aw()
async def direct():
    return await Aw()
async def via_anext():
    return await anext(A(), 'default')
def drive(c, limit=8):
    seen = []
    try:
        for _ in range(limit):
            seen.append(c.send(None))
    except StopIteration as e:
        return seen, e.value
    c.close()
    return seen, 'did not finish'
print('direct', drive(direct()), Aw.calls)
Aw.calls = 0
print('anext ', drive(via_anext()), Aw.calls)

# the same through the proxy methods
class Aw2:
    def __await__(self):
        x = yield 'a'
        y = yield 'b'
        return (x, y)
class A2:
    def __anext__(self): return Aw2()
it = anext(A2(), 'dflt').__await__()
out = [next(it)]
for v in (1, 2, 3, 4):
    try:
        out.append(it.send(v))
    except StopIteration as e:
        out.append(('stop', e.value)); break
print('send', out)

# --- recursion limit
sys.setrecursionlimit(150)
depth = 0
def probe(f):
    global depth
    r = []
    for k in range(6):
        depth = 0
        try:
            f()
        except RecursionError:
            r.append(depth)
    return r

class C:
    def __getitem__(self, i):
        global depth; depth += 1
        return self[i + 1]
class D:
    @property
    def x(self):
        global depth; depth += 1
        return self.x
class B:
    def m(self, *, value):
        global depth; depth += 1
        return BM(value=value)
BM = B().m
def plain():
    global depth; depth += 1
    return plain()
c, d = C(), D()
print('limit', sys.getrecursionlimit())
print('plain', probe(plain))
print('getitem', probe(lambda: c[0]))
print('property', probe(lambda: d.x))
print('kw bound', probe(lambda: BM(value=1)))

# generators: no call at each level, a prebuilt chain of `yield from`
def link(inner):
    global depth
    depth += 1
    r = yield from inner
    return r
def leaf():
    global depth
    depth += 1
    yield 1
def build(n):
    g = leaf()
    for _ in range(n):
        g = link(g)
    return g
for n in (100, 140, 145, 148, 150, 160, 200, 260, 400):
    depth = 0
    for warm in range(3):
        pass
    res = []
    for k in range(4):
        g = build(n)
        depth = 0
        try:
            res.append(next(g))
        except RecursionError:
            res.append('RecursionError')
    print('chain', n, res)
