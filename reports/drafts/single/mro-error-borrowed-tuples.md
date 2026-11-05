<!-- title: MRO conflict formatting reads a freed base MRO if metaclass __hash__ changes __bases__ -->
### Bug report

MRO merging borrows each base's MRO tuple. While constructing a conflict error, it hashes candidate classes, which can run a metaclass's `__hash__`. That callback can replace a base's `__bases__` and free an MRO tuple the error formatter still uses. The recorded result names a bytes object as an MRO candidate.

```python
import subprocess, sys
code = r'''
state = {'armed': False}
junk = []
class M(type):
    def __hash__(cls):
        if state['armed'] and cls.__name__ == 'X':
            state['armed'] = False
            B.__bases__ = (X, Y)
            junk.extend(bytes([0x41]) * 230 for _ in range(20000))
        return type.__hash__(cls)
base = object
for i in range(30):
    base = M('Z%d' % i, (base,), {})
class X(base, metaclass=M): pass
class Y(metaclass=M): pass
class A(X, Y): pass
class B(Y, X): pass
state['armed'] = True
try:
    class C(A, B): pass
except TypeError as e:
    print('MSG', str(e)[:120])
'''
p = subprocess.run([sys.executable, '-c', code], capture_output=True, text=True)
out = p.stdout.strip()
print(out[:160], 'returncode', p.returncode)
```

Recorded on 3.15.2 and main: the TypeError names `X, b'AAAA...` as the conflicting bases, rather than the classes `X, Y`. The exact output depends on reuse of the freed memory. The record reports this incorrect message, not a measured segfault.

Cause: Objects/typeobject.c:3537-3539 puts borrowed `lookup_tp_mro(base)` pointers into `to_merge`. `set_mro_error` reads one tuple and calls `PyDict_SetItem` on its candidate (:3359-3362), then reads subsequent tuples after the metaclass callback has run. Take strong references to the MRO tuples for the merge, or snapshot and retain the candidate classes before invoking Python code during error construction.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare these drafts. The code blocks were rerun on 3.15.2 and main during technical review; the human submitter must review the report before filing. Record: [typeobj-set-mro-error-borrowed-mro](https://github.com/Broyojo/python-formalization/blob/main/bugs/typeobj-set-mro-error-borrowed-mro.yaml)
