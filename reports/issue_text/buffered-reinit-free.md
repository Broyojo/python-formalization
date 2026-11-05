<!-- title: Reentrant BufferedReader/Writer initialization frees active storage or leaves an invalid buffer size -->
<!-- form: crash -->
<!-- records: pyio-buffered-reentrant-init-free pyio-buffered-reentrant-init-size0 -->
Calling `BufferedReader.__init__()` from its raw stream's `readinto()` callback frees the buffer backing the callback's memoryview and replaces the lock held by the outer read. The callback then writes through the old view, and the outer read eventually tries to release the new, unlocked mutex.

```python
import io
class Raw(io.RawIOBase):
    def readable(self): return True
    def readinto(self, b):
        if not getattr(self, "done", False):
            self.done = True
            buf.__init__(Plain(), 8)
        b[:1] = b"x"
        return 1
class Plain(io.RawIOBase):
    def readable(self): return True
    def readinto(self, b):
        b[:1] = b"y"; return 1
buf = io.BufferedReader(Raw(), 8)
print("read ->", buf.read(1), flush=True)
print("survived", flush=True)
```

Recorded on 3.15.2 and main: SIGABRT, with `Fatal Python error: PyMutex_Unlock: unlocking mutex that is not locked`. Expected: refuse the reentrant initialization, or complete without using freed memory.

Cause: Modules/_io/bufferedio.c:846-860 frees the existing buffer and lock and clears `owner`, without checking whether a method is using them. `_bufferedreader_raw_read` has lent a view of that buffer to Python while the outer read holds the lock. Reinitialization needs the same protection as other buffered methods, before changing any live state.

The record also reports a NULL-buffer read if reinitialization frees the buffer and then allocation fails. The separate `pyio-buffered-reentrant-init-size0` record covers invalid sizes stored before initialization fails; the records recommend reporting these reinitialization cases together. gh-154997 instead concerns reentrant detach leaving the raw pointer NULL.


**Failed initialization with a zero size.**

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

Both cases require initialization to validate its arguments before changing state and to protect active operations from reinitialization.
