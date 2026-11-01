import sys
sys.setrecursionlimit(200)
depth = 0

def probe(name, setup):
    global depth
    res = []
    thunk = setup()
    for k in range(50):
        depth = 0
        try:
            thunk()
            res.append('noerr')
        except RecursionError as e:
            res.append(depth)
    print(name, res[:3], res[-3:])

def s_getitem():
    class C:
        def __getitem__(self, i):
            global depth; depth += 1
            return self[i + 1]
    c = C()
    return lambda: c[0]

def s_prop():
    class D:
        @property
        def x(self):
            global depth; depth += 1
            return self.x
    d = D()
    return lambda: d.x

def s_init():
    class E:
        def __init__(self, n):
            global depth; depth += 1
            E(n + 1)
    return lambda: E(0)

def s_getattribute():
    class G:
        def __getattribute__(self, n):
            global depth; depth += 1
            return self.foo
    g = G()
    return lambda: g.a

def s_gen():
    def g(n):
        global depth; depth += 1
        yield from g(n + 1)
    return lambda: list(g(0))

def s_plain():
    def f(n):
        global depth; depth += 1
        return f(n + 1)
    return lambda: f(0)

probe("getitem", s_getitem)
probe("property", s_prop)
probe("init", s_init)
probe("getattribute", s_getattribute)
probe("genfrom", s_gen)
probe("plain", s_plain)
