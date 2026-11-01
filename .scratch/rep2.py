"""f_lineno jump leaves NULL on the stack: run in a child so a crash is reported."""
import subprocess, sys, textwrap

WITH_NULL = r'''
import sys, inspect
class CM:
    __enter__ = staticmethod(lambda: None)
    __exit__ = staticmethod(lambda *a: None)

def victim(a, b, c):
    with CM():
        x = 1
        pass
    y = (a, b,
         c)
    return y

first = victim.__code__.co_firstlineno
LINE_A = first + 2      # inside the with body
LINE_B = first + 5      # second line of the tuple display: stack is [a, b]
done = False
def tracer(frame, event, arg):
    global done
    if frame.f_code is victim.__code__ and event == 'line' and not done and frame.f_lineno == LINE_A:
        done = True
        frame.f_lineno = LINE_B
    return tracer
sys.settrace(tracer)
r = victim(1, 2, 3)
sys.settrace(None)
print('len', len(r))
print('second item is NULL?', flush=True)
print(r, flush=True)
'''

SWAP_TRUNC = r'''
import sys
# 12 nested for loops: 12 iterators on the stack, then a SWAP at that depth
src = "def victim():\n    n = 0\n"
ind = "    "
for i in range(12):
    src += ind + f"for i{i} in [1]:\n"
    ind += "    "
src += ind + "a, b, c = 1, 2, 3\n"           # marker line: not needed
src += ind + "p, q = n, n + 1\n"             # SWAP
src += ind + "n += 1\n"                      # jump from here: analysis is truncated
src += "    return n\n"
ns = {}
exec(compile(src, "<v>", "exec"), ns)
victim = ns["victim"]
import dis
print([i.opname for i in dis.get_instructions(victim) if i.opname == 'SWAP'][:3])
first = victim.__code__.co_firstlineno
LINE_FROM = first + 2 + 12 + 2
LINE_TO = first + 13 + 2 + 1
print('stacksize', victim.__code__.co_stacksize)
jumps = 0
def tracer(frame, event, arg):
    global jumps
    if frame.f_code is victim.__code__ and event == 'line' and frame.f_lineno == LINE_FROM and jumps < 1:
        jumps += 1
        frame.f_lineno = LINE_TO
    return tracer
sys.settrace(tracer)
print(victim())
sys.settrace(None)
print('jumps', jumps)
'''

for name, code in [('with-null', WITH_NULL), ('swap-trunc', SWAP_TRUNC)]:
    for exe in [sys.executable, '/Users/broyojo/code/projects/python-formalization/vendor/cpython-main/python.exe']:
        try:
            p = subprocess.run([exe, '-c', code], capture_output=True, text=True, timeout=60)
            print(name, exe.split('/')[-1], 'rc', p.returncode, repr(p.stdout[-400:]), repr(p.stderr[-500:]))
        except Exception as e:
            print(name, exe, e)
