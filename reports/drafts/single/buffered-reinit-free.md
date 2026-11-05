<!-- title: Reinitializing BufferedReader from a raw callback frees the active buffer and lock, then aborts -->
### Crash report

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

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

### Output from running 'python -VV' on the command line:

Python 3.15.2 (tags/v3.15.2:5e58eaa, Nov  5 2026, 20:20:36) [GCC 11.4.0]

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare these drafts. Results in the body are taken from the bug records; final interpreter reruns and human review are pending. Record: [pyio-buffered-reentrant-init-free](https://github.com/Broyojo/python-formalization/blob/main/bugs/pyio-buffered-reentrant-init-free.yaml)
