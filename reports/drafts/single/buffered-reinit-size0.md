<!-- title: A reentrant BufferedReader/Writer.__init__(raw, 0) leaves a zero buffer size: division by zero or an endless write loop -->
### Crash report

A raw stream callback can call its wrapper's `__init__(raw, 0)` and catch the expected `ValueError`. The failed initialization has already stored the zero size. The running buffered method resumes using it: the reader divides by zero on the recorded x86-64 build, and the writer repeatedly calls `raw.write(b'')` without returning.

This uses subprocesses so that the write hang has a timeout:

```python
import subprocess, sys
child = r'''
import io, sys
class Raw(io.RawIOBase):
    buf = None
    def readable(self): return True
    def writable(self): return True
    def reinit(self):
        if self.buf is not None:
            buf, self.buf = self.buf, None
            try:
                buf.__init__(self, 0)
            except ValueError:
                pass
    def readinto(self, b):
        self.reinit()
        b[:1] = b"x"
        return 1
    def write(self, b):
        self.reinit()
        return len(b)
raw = Raw()
if sys.argv[1] == "read":
    f = io.BufferedReader(raw, 3)
    raw.buf = f
    print(f.read(10))
else:
    f = io.BufferedWriter(raw, 5)
    raw.buf = f
    f.write(b"abcdefghij")
print("survived")
'''
out = {}
for which in ("read", "write"):
    try:
        p = subprocess.run([sys.executable, "-c", child, which], capture_output=True, text=True, timeout=10)
        out[which] = p.returncode
    except subprocess.TimeoutExpired:
        out[which] = "timeout"
print(out)
```

Recorded on 3.15.2 and main (x86-64): `{'read': -8, 'write': 'timeout'}`. `-8` is SIGFPE. A failed initialization should not leave a running method dividing by zero or looping forever.

Cause: Modules/_io/bufferedio.c:1605 and :1961 store `buffer_size` before `_buffered_init` rejects it at :841-845. `MINUS_LAST_BLOCK` (:408-411) divides by the live size for a non-power-of-two original size; the writer loop at :2186 compares against it. Validate before storing, and reject reinitialization while a buffered method holds the lock.

The record additionally reports uninitialized output with an original power-of-two size and an out-of-bounds copy after a refused negative size. Those variants are not exercised by the code above. This should be reviewed together with `pyio-buffered-reentrant-init-free`, which covers successful reinitialization freeing the active buffer and lock.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

### Output from running 'python -VV' on the command line:

Python 3.15.2 (tags/v3.15.2:5e58eaa, Nov  5 2026, 20:20:36) [GCC 11.4.0]

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare these drafts. Results in the body are taken from the bug records; final interpreter reruns and human review are pending. Record: [pyio-buffered-reentrant-init-size0](https://github.com/Broyojo/python-formalization/blob/main/bugs/pyio-buffered-reentrant-init-size0.yaml)
