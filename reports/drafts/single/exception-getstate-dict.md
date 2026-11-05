<!-- title: AttributeError and ImportError copy a borrowed instance dict during __reduce__, allowing it to be freed by a key comparison -->
### Bug report

`AttributeError.__reduce__()` copies the instance dict without keeping it alive across key comparisons. If a key's `__eq__` replaces `e.__dict__`, the dict being copied loses its last reference. The copy then reads the freed dict. Keeping an extra reference makes the same copy succeed.

```python
import subprocess, sys
child = r'''
import sys
keep = sys.argv[1] == "keep"
armed = False
class K:
    def __init__(self, n): self.n = n
    def __hash__(self): return 1
    def __eq__(self, other):
        global armed
        if armed:
            armed = False
            e.__dict__ = {}
            junk = [{"a%d" % i: [i] * 8} for i in range(50)]
        return False
e = AttributeError("x", name="n")
d = {}
for i in range(6):
    d["p%d" % i] = i
d[K(1)] = 1
d[K(2)] = 2
for i in range(6):
    del d["p%d" % i]
e.__dict__ = d
if not keep:
    del d
armed = True
try:
    e.__reduce__()
    print("ok")
except RuntimeError as ex:
    print("RuntimeError:", ex)
'''
out = {}
for mode in ("keep", "free"):
    p = subprocess.run([sys.executable, "-c", child, mode], capture_output=True, text=True)
    out[mode] = (p.returncode, p.stdout.strip())
    print(mode, out[mode])
```

Recorded on 3.15.2 and main:

```text
keep (0, 'ok')
free (0, 'RuntimeError: dict mutated during update')
```

No code mutates the source dict: the callback replaces the exception's reference to it. Both modes should copy the original dict safely. The record reports the same result for ImportError and under `PYTHONMALLOC=debug`; it does not report a segfault.

Cause: Objects/exceptions.c:2723-2725 and :1883-1885 pass borrowed `self->dict` to `PyDict_Copy`. A sparse dict takes the merge-based copy path (Objects/dictobject.c:4535-4539), whose insertion loop can invoke `__eq__` and then read the source's `ma_used` (:4223-4249). Take a strong reference to the source across the copy in both getstate functions, or protect the source lifetime in the copying routine.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare this report. The examples were rerun on CPython 3.15.2 and main, and the report received technical review. Record: [typeobj-exc-getstate-borrowed-dict](https://github.com/Broyojo/python-formalization/blob/main/bugs/typeobj-exc-getstate-borrowed-dict.yaml)
