"""Hot vs cold on real CPython: same operation on the same edge input, once before
and once after warming the call site up on benign inputs. Divergence in value,
exception class or message is a candidate finding."""
import dis, sys, re, copy, collections, multiprocessing as mp

class Sub(int): pass
class SubS(str): pass
class SubL(list): pass
class SubD(dict): pass
class SubT(tuple): pass
class EqAll:
    def __eq__(self, o): return True
    def __hash__(self): return 1
class Unh:
    __hash__ = None
class BadHash:
    def __hash__(s): raise ValueError("hash")
class BadBool:
    def __bool__(s): raise ValueError("bool")
class GI:
    def __getitem__(s, i): return i
    def __len__(s): return 3
class Q:
    def __init__(s): s.x = 1
class Slots:
    __slots__ = ('x',)
class Prop:
    @property
    def x(s): raise AttributeError("from prop")
    def __getattr__(s, n): return 'ga:' + n
class Cl:
    x = 5
    def m(s): return 'm'
class Meta(type):
    def __getattribute__(c, n): return 'meta:' + n
class WM(metaclass=Meta):
    x = 1

EDGE = [0, 1, -1, 2**30-1, 2**30, -2**30, 2**31, 2**63, 2**64, 1.5, float('nan'), float('inf'), -0.0, True, False,
        None, 'a', '', 'é', '\U0001F600', b'a', [], [1], [1, 2, 3], (), (1, 2), {}, {1: 2}, {'a': 1}, set(), {1}, frozenset({1}),
        Sub(3), SubS('s'), SubL([1]), SubD(a=1), SubT((1, 2)), EqAll(), Unh(), BadHash(), BadBool(), GI(), slice(0, 1), range(3), [[]]]

BIN = ['a + b','a - b','a * b','a / b','a // b','a % b','a ** b','a & b','a | b','a ^ b','a << b','a >> b',
       'a[b]','a == b','a != b','a < b','a <= b','a > b','a >= b','a in b','a not in b',
       'x = a; x += b; return x', 'x = a; x *= b; return x',
       'x = [0, 1, 2]; x[a] = b; return x', 'x = {}; x[a] = b; return x', 'a[b] = 1; return a', 'del a[b]; return a']
UN = ['not a','-a','~a','+a','bool(a)','len(a)','str(a)','tuple(a)','type(a)','list(a)','[*a]','{*a}','(*a,)',
      'x, y = a; return (x, y)', 'x, *y = a; return (x, y)', 'isinstance(a, int)', 'isinstance(1, a)', 'a()', 'a.x', 'a.real',
      '[q for q in a]', 'list.append(a, 1)', 'str.upper(a)', 'a.append(1)', 'a.upper()', 'a.x = 1; return a.x', 'del a.x; return a']
WARM2 = [(1, 2), ('a', 'b'), ([1, 2, 3], 1), ((1, 2, 3), 1), ({1: 2}, 1), (1.5, 2.5), ('abc', 1), ({1}, 1), (1, {1}), (1, {1: 2})]
WARM1 = [1, 'a', [1, 2], (1, 2), {1: 2}, {1}, None, 1.5, True, Q(), Slots(), Prop(), Cl(), Cl, WM, str, list]

def make(src):
    body = [s.strip() for s in src.split(';')]
    code = "def f(a, b):\n"
    for l in body[:-1]:
        code += "    " + l + "\n"
    last = body[-1]
    code += "    " + (last if last.startswith('return') or last.startswith('del') else "return " + last) + "\n"
    ns = dict(globals())
    exec(compile(code, "<hc>", "exec"), ns)
    return ns['f']

def fresh(v):
    try:
        return copy.deepcopy(v)
    except Exception:
        return v

def outcome(f, a, b):
    try:
        r = f(a, b)
        s = repr(r)
        return ('ok', re.sub(r'0x[0-9a-f]+', 'ADDR', s)[:200])
    except BaseException as e:
        return ('exc', type(e).__name__, re.sub(r'0x[0-9a-f]+', 'ADDR', str(e))[:200])

def adaptive(f):
    return [i.opname for i in dis.get_instructions(f, adaptive=True)
            if i.opname not in ('RESUME_CHECK', 'RESUME', 'LOAD_FAST_BORROW', 'LOAD_FAST', 'RETURN_VALUE', 'LOAD_FAST_BORROW_LOAD_FAST_BORROW', 'NOT_TAKEN')][:6]

def work(src):
    res = []
    two = src in BIN
    warms = WARM2 if two else [(w, 0) for w in WARM1]
    n = 0
    for warm in warms:
        hotf = make(src)
        for _ in range(30):
            outcome(hotf, fresh(warm[0]), fresh(warm[1]))
        spec = adaptive(hotf)
        for ea in EDGE:
            for eb in (EDGE if two else [0]):
                if src in ('a ** b', 'a << b') and isinstance(eb, int) and abs(eb) > 1000: continue
                if '*' in src and isinstance(ea, (int,)) and abs(ea) > 2**20 and isinstance(eb, (str, bytes, list, tuple, SubS, SubL, SubT)): continue
                if '*' in src and isinstance(eb, (int,)) and abs(eb) > 2**20 and isinstance(ea, (str, bytes, list, tuple, SubS, SubL, SubT)): continue
                n += 1
                c = outcome(make(src), fresh(ea), fresh(eb))
                # re-warm so that a deopt on the previous edge input does not hide this one
                h = outcome(hotf, fresh(ea), fresh(eb))
                if c != h:
                    res.append(((src, repr(ea)[:30], repr(eb)[:30]), c, h, spec))
    return n, res

if __name__ == '__main__':
    with mp.Pool(16) as pool:
        total = 0
        seen = set()
        for n, res in pool.imap_unordered(work, BIN + UN):
            total += n
            for k, c, h, spec in res:
                if (k, c, h) in seen:
                    continue
                seen.add((k, c, h))
                print(k, c, h, spec, flush=True)
            print('done', total, len(seen), flush=True)
