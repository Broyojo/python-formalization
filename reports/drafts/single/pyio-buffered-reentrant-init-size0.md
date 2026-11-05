<!-- title: io.BufferedReader/Writer: a failed __init__(raw, 0) re-entered from a … -->
# Bug report

### Bug description

The constructors store `self->buffer_size = buffer_size` before `_buffered_init` checks it, and
a refused size (`<= 0`, "buffer size must be strictly positive") leaves it stored. Called again
on a live object from inside a raw-stream callback (the raw's `readinto` or `write` calls
`buf.__init__(raw, 0)`, catching the ValueError), it changes `buffer_size` under the method that
is running, which goes on using it:
- `BufferedReader.read(10)` on a reader whose size is not a power of two: the next
  `MINUS_LAST_BLOCK` computes `self->buffer_size * (size / self->buffer_size)` with
  `buffer_size == 0` and the process dies of SIGFPE (integer division by zero: undefined
  behaviour in C, which traps on x86-64, where this was measured; AArch64 gives 0);
- `BufferedWriter.write(b)` with `len(b) >= buffer_size`: `while (remaining >= self->buffer_size)`
  becomes `while (0 >= 0)` once everything is written, and the method calls `raw.write(b'')`
  forever.
- with a power-of-two size (the default 8192 included) `MINUS_LAST_BLOCK` uses `buffer_mask`
  and does not trap: the fill loop stops (`read_end < buffer_size` is false) and
  `PyBytesWriter_Finish` returns the requested length, its tail bytes nobody wrote (an
  uninitialized read);
- a negative size is stored too (`Py_ssize_t`): `__init__(raw, -1)` makes `MINUS_LAST_BLOCK`
  compute `-1 * (n / -1) = n` and the read completes, but in `write`, with `raw.write`
  answering None, `memcpy(self->buffer, ..., self->buffer_size)` gets `(size_t)-1`: undefined
  behaviour whose result depends on the heap layout (SIGSEGV for our writer; a reviewer's raw
  got BlockingIOError with characters_written -1; a BufferedRandom ran on with a corrupted heap).
Same family as pyio-buffered-reentrant-init-free (an `__init__` that bypasses the method lock),
but a different mechanism: here `_buffered_init` refuses and frees nothing.

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

**Expected:** The refused re-initialization leaves the running method alone (or is itself refused as a re-entrant call); read(10) and write() complete or raise.

**Actual:** python3 3.15.2: read exits with SIGFPE (-8); write never returns (timeout). REPRODUCED. main (python.exe 3.16.0a1+dev): identical. REPRODUCED.

**Cause:** Modules/_io/bufferedio.c:1605 (reader) and :1961 (writer) store buffer_size before `_buffered_init` refuses it at :841-845, and nothing checks `self->ok` again in the running method. MINUS_LAST_BLOCK (:408-411) divides by buffer_size when buffer_mask is 0 (:1834 in _bufferedreader_read_generic); `_io_BufferedWriter_write_impl` loops on `remaining >= self->buffer_size` (:2186).

**Possible fix:** Validate buffer_size before storing it in the constructors, and refuse re-initialization while the object's lock is held (the fix proposed for pyio-buffered-reentrant-init-free).

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance; I reproduced it on 3.15.2 and on main and reviewed it before filing.
