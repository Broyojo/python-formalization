"""Abstract classes after specialization of CALL_ALLOC_AND_ENTER_INIT."""
import dis, sys
class C:
    def __init__(self):
        self.ok = True
C.__abstractmethods__ = frozenset({'f'})
def mk():
    return C()
res = []
for i in range(30):
    try:
        mk()
        res.append('created')
    except TypeError as e:
        res.append(str(e)[:40])
print(res[0], '...', res[-1])
print('created count', res.count('created'))
print([i.opname for i in dis.get_instructions(mk, adaptive=True) if 'CALL' in i.opname])
print(sys.version)
# with an ABC-free helper: inherits from a plain base
class Base:
    def __init__(self):
        pass
class D(Base):
    pass
D.__abstractmethods__ = frozenset({'g'})
def mk2():
    return D()
res = []
for i in range(30):
    try:
        mk2(); res.append(1)
    except TypeError:
        res.append(0)
print(res)
