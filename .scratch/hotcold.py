"""Hot vs cold: run a one-line operation cold, then warm it up on benign inputs so
it specializes, then run it on the edge input; compare value/exception/message."""
import dis, sys, types, collections

class Sub(int): pass
class SubS(str): pass
class SubL(list): pass
class SubD(dict): pass
class SubT(tuple): pass
class WithEq:
    def __eq__(self, o): return True
    def __hash__(self): raise TypeError("nohash")
class Unh:
    __hash__ = None
class H:
    def __init__(s, v): s.v = v
    def __hash__(s): return hash(s.v)
    def __eq__(s, o): raise ValueError("eq")
class BadBool:
    def __bool__(s): raise ValueError("bool")
class Getitem:
    def __getitem__(s, i): return i
    def __len__(s): return 3
class Attrs:
    __slots__ = ('a',)
class P:
    @property
    def x(s): raise AttributeError("from prop")
    def __getattr__(s, n): return 'getattr:' + n
class Q:
    def __init__(s): s.x = 1
class M(type):
    def __call__(c, *a): return 'meta'
class WithMeta(metaclass=M): pass
def gen(): yield 1

EDGE = [0, 1, -1, 2**30-1, 2**30, -2**30, -2**30+1, 2**31, 2**63, -2**63, 2**64, 1.5, float('nan'), float('inf'), -0.0, True, False,
        None, 'a', '', 'é', '\U0001F600', b'a', [], [1], [1, 2, 3], (), (1,), (1, 2), {}, {1: 2}, {'a': 1}, set(), {1}, frozenset({1}),
        Sub(3), SubS('s'), SubL([1]), SubD(a=1), SubT((1, 2)), WithEq(), Unh(), H(1), BadBool(), Getitem(), slice(0, 1), slice(None), range(3), [[]], ({},), [[1]]]

BIN = ['a + b','a - b','a * b','a / b','a // b','a % b','a ** b','a & b','a | b','a ^ b','a << b','a >> b',
       'a[b]','a == b','a != b','a < b','a <= b','a > b','a >= b','a is b','a in b','a not in b',
       'c = a; c += b; c', 'c = a; c *= b; c','c = a; c -= b; c',
       'x = [0, 1, 2]; x[a] = b; x', 'x = {}; x[a] = b; x', 'a[b] = 1; a', 'del a[b]; a']
UN = ['not a','-a','~a','+a','bool(a)','len(a)','str(a)','tuple(a)','type(a)','list(a)','iter(a)','[*a]','{*a}','(*a,)',
      'x, y = a; (x, y)', 'x, = a; x', 'x, *y = a; (x, y)', 'isinstance(a, int)', 'isinstance(1, a)', 'a()', 'a.x', 'a.real','a.append(1)',
      '[q for q in a]', 'list.append(a, 1)', 'str.upper(a)', 'len(*a)', 'dict(a)']
WARM = [(1, 2), (3, 4), ('a', 'b'), ([1,2,3], 1), ((1,2,3), 1), ({1:2}, 1), (1.5, 2.5), ('abc', 1), ({1}, 1)]
WARM1 = [1, 2, 'a', [1, 2], (1, 2), {1: 2}, {1}, None, 1.5, True, Q()]

def make(src):
    body = src.split(';')
    last = body[-1].strip()
    lines = [s.strip() for s in body[:-1]]
    code = "def f(a, b):\n"
    for l in lines:
        code += "    " + l + "\n"
    try:
        compile("(" + last + ")", "x", "eval")
        code += "    return " + last + "\n"
    except SyntaxError:
        code += "    " + last + "\n"
    ns = dict(globals())
    exec(compile(code, "<hc>", "exec"), ns)
    return ns['f']

def outcome(f, a, b):
    try:
        import copy
        r = f(a, b)
        s = repr(r)
        return ('ok', s[:200])
    except BaseException as e:
        return ('exc', type(e).__name__, str(e)[:200])

def norm(o):
    import re
    return tuple(re.sub(r'0x[0-9a-f]+', 'ADDR', x) for x in o)

import copy
def fresh(v):
    try:
        return copy.deepcopy(v)
    except Exception:
        return v

bad = collections.Counter()
samples = {}
n = 0
for src in BIN + UN:
    for ea in EDGE:
        for eb in (EDGE if src in BIN else [0]):
            for warm in (WARM if src in BIN else [(w, 0) for w in WARM1]):
                try:
                    if len(repr(ea)) + len(repr(eb)) > 1000: continue
                except Exception: pass
                if src in ('a ** b','a << b') and isinstance(eb, int) and abs(eb) > 1000: continue
                if isinstance(ea, int) and abs(ea) > 2**20 and '*' in src and isinstance(eb, (str,bytes,list,tuple)): continue
                if isinstance(eb, int) and abs(eb) > 2**20 and '*' in src and isinstance(ea, (str,bytes,list,tuple)): continue
                n += 1
                cold = make(src)
                c = norm(outcome(cold, fresh(ea), fresh(eb)))
                hot = make(src)
                for _ in range(8):
                    try:
                        outcome(hot, fresh(warm[0]), fresh(warm[1]))
                    except BaseException:
                        pass
                h = norm(outcome(hot, fresh(ea), fresh(eb)))
                if c != h:
                    key = (src, repr(ea)[:30], repr(eb)[:30])
                    if key not in samples:
                        samples[key] = (c, h, [str(i.opname) for i in dis.get_instructions(hot, adaptive=True) if i.opname not in ('RESUME_CHECK','LOAD_FAST_BORROW','RETURN_VALUE')][:8])
print(n, 'pairs;', len(samples), 'divergences')
for k, v in list(samples.items())[:60]:
    print(k, v)
