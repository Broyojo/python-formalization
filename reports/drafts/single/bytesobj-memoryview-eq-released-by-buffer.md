<!-- title: memoryview == reads freed memory when __buffer__ releases the view -->
# Bug report

### Bug description

memory_richcompare tests BASE_INACCESSIBLE(v) and then calls PyObject_GetBuffer(w). For a class with __buffer__ that is Python code, which can release v and free its buffer. Nothing tests v again, so the comparison reads the buffer of a released view: ba = bytearray(N); m = memoryview(ba) class W: def __buffer__(self, flags): m.release(); ba.clear(); return memoryview(other) m == W() With a large buffer the process dies with SIGSEGV. With a small buffer that is not freed, the released view compares by content and gives True, where a released view compares by identity (:3113-3116). Lean: CmpReleasedIdentity is refuted on a 1-byte view; CmpSpecialCases (a view already released on entry compares by identity, for all states) is proven. The difftest met this independently, without a crash: for a view from PyMemoryView_GetContiguous, `v != E(v.release)` is True when the release frees the temporary bytes and False, the model's answer, when the temporary is kept alive. So it can also give a silently wrong result.

```python
import subprocess, sys
crash = '''
N = 1 << 27
other = bytes(N)
ba = bytearray(N)
m = memoryview(ba)
class W:
    def __buffer__(self, flags):
        m.release()
        ba.clear()
        return memoryview(other)
print(m == W())
'''
r = subprocess.run([sys.executable, "-I", "-c", crash], capture_output=True, text=True)
print("freed buffer: exit status", r.returncode, r.stdout.strip())
ba = bytearray(b"abc")
m = memoryview(ba)
class W:
    def __buffer__(self, flags):
        m.release()
        return memoryview(b"abc")
result = m == W()
print("released during ==:", m, result)
```

**Expected:** m == W() is False: a released view is equal only to itself. The buffer is never read.

**Actual:** python3 3.15.2: True for the small case; SIGSEGV (status -11) for a 128 MB buffer freed in __buffer__. main (python.exe 3.16.0a1+dev): identical, SIGSEGV included.

**Cause:** Objects/memoryobject.c:3216 tests v; :3254 PyObject_GetBuffer(w, &wbuf, PyBUF_FULL_RO) may run __buffer__; :3290-3304 read vv->buf. struct_get_unpacker (:2158) can also run Python code if sys.modules['struct'] was replaced, with the same effect. main: Objects/memoryobject.c:3414.

**Possible fix:** Hold an export on v across the call (FT_ATOMIC_ADD_SSIZE(self->exports, 1), as memory_hash and memoryview_hex_impl do since gh-142664 and gh-143195), or repeat the BASE_INACCESSIBLE test after PyObject_GetBuffer and take the identity branch.

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/bytesobj-memoryview-eq-released-by-buffer.yaml
