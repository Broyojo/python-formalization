<!-- title: io.BufferedReader: calling __init__ from inside a raw stream callback … -->
# Bug report

### Bug description

`_buffered_init` (Modules/_io/bufferedio.c:837-) frees and reallocates `self->buffer` (:846-848)
and `self->lock` (:853-858) whenever they already exist, and resets `self->owner = 0` (:860). It
does not check whether a method of the same object is running and holds that lock or is about to
write into that buffer. `BufferedReader.__init__` can be called again on a live object from Python
(it is an ordinary method), including from inside a raw-stream callback such as `readinto`, which
`_bufferedreader_raw_read` calls with a memoryview over `self->buffer` while `ENTER_BUFFERED` holds
`self->lock`.

```python
import subprocess, sys
child = r'''
import io
class Raw(io.RawIOBase):
    def readable(self): return True
    def readinto(self, b):
        if not getattr(self, "done", False):
            self.done = True
            buf.__init__(Plain(), 8)   # re-initialize the BufferedReader that is calling us
        b[:1] = b"x"
        return 1
class Plain(io.RawIOBase):
    def readable(self): return True
    def readinto(self, b):
        b[:1] = b"y"; return 1
buf = io.BufferedReader(Raw(), 8)
print("read ->", buf.read(1), flush=True)
print("survived", flush=True)
'''
p = subprocess.run([sys.executable, "-c", child], capture_output=True, text=True)
print("child returncode:", p.returncode)
print("child stderr:", p.stderr.strip().splitlines()[0] if p.stderr.strip() else "")
```

**Expected:** Either the inner `__init__` is refused while a method holds the lock (as other re-entrant calls are, with RuntimeError "reentrant call inside <_io.BufferedReader>"), or `read(1)` completes on a consistent object. No abort, no access to freed memory.

**Actual:** python3 3.15.2 (release build): child exits with SIGABRT (-6), stderr "Fatal Python error: PyMutex_Unlock: unlocking mutex that is not locked". REPRODUCED. main (3.16.0a1+dev, ef1fce0): identical. REPRODUCED. Found by the buffered I/O re-review (2026-11-03) and re-run independently.

**Cause:** Modules/_io/bufferedio.c:846-860: `PyMem_Free(self->buffer)` and `PyThread_free_lock(self->lock)` on a live object, with no check of `self->owner` / whether the lock is held. The outer method (`_io__Buffered_read_impl` → `_bufferedreader_read_generic` → `_bufferedreader_raw_read`) still uses the old buffer and then releases a lock it did not acquire (`LEAVE_BUFFERED`).

**Possible fix:** In `_io_BufferedReader___init___impl` (and the Writer/Random/RWPair equivalents), refuse re-initialization while the object's lock is held: check `self->lock != NULL && self->owner != 0` (or try-acquire the lock without blocking) and raise RuntimeError("reentrant call inside %R"), as `_enter_buffered_busy` does. Alternatively take the lock in `_buffered_init` before freeing.

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance; I reproduced it on 3.15.2 and on main and reviewed it before filing.
