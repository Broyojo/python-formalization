p = 'lean/PyLean/Bytecode/IterObj.lean'
s = open(p).read()


def cut(a_anchor, b_anchor):
    global s
    a = s.index(a_anchor)
    b = s.index(b_anchor)
    assert a < b, (a_anchor, b_anchor)
    s = s[:a] + s[b:]


cut('theorem iterSetstate_proven', '/-- `__length_hint__` is never negative')
cut('theorem iterLenReduce_proven', '/-- A sentinel match ends')
cut('theorem anextCoroutine_proven', '/-- The fast `Py_ssize_t` counter')
cut('theorem enumReduce_fold', '/-- `reversed(list)` yields the list backwards')
cut('theorem revSetstate_proven', '/-- `cell` order:')
a = s.index('theorem enumArgs_proven')
b = s.index('end PyLean.Bytecode.IterObj')
s = s[:a] + s[b:]
open(p, 'w').write(s)
print('IterObj theorems left:', s.count('theorem '))

p = 'lean/PyLean/Bytecode.lean'
s = open(p).read()


def rmentry(idv, nxt):
    global s
    pre = s.index('  { id := "' + idv + '"')
    nx = s.index('  { id := "' + nxt + '"')
    s = s[:pre] + s[nx:]


for idv, nxt in [("bytecode-iter-setstate", "bytecode-iter-len-reduce"),
                 ("bytecode-iter-len-reduce", "bytecode-calliter-ends"),
                 ("bytecode-anext-coroutine", "bytecode-enum-counts"),
                 ("bytecode-enum-reduce", "bytecode-enum-args"),
                 ("bytecode-enum-args", "bytecode-reversed-setstate"),
                 ("bytecode-reversed-setstate", "bytecode-cell-order"),
                 ("bytecode-frame-push-pop", "bytecode-frame-overflowed")]:
    try:
        rmentry(idv, nxt)
    except ValueError as e:
        print("skip", idv, e)
open(p, 'w').write(s)
print('registry entries:', s.count('id :='))

p = 'lean/PyLean/Bytecode/FrameProps.lean'
s = open(p).read()
a = s.index('theorem pushPop_proven')
b = s.index('/-- A stack that went to `OVERFLOWED`')
s = s[:a] + s[b:]
open(p, 'w').write(s)
print('done')
