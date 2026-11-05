<!-- title: BufferedReader.read() crashes if the raw stream's closed property detaches the reader -->
<!-- form: crash -->
<!-- records: pyio-buffered-reentrant-detach-crash -->
**Triage:** the record identifies this as a duplicate of gh-154997. This draft is an additional trigger for review alongside that issue, rather than a claim of a new defect.

The raw stream's `closed` property runs before `BufferedReader.read()` takes its lock. That property can detach the reader; the outer read then continues with a NULL raw pointer.

```python
import io
class Raw(io.RawIOBase):
    buf = None
    done = False
    def readable(self):
        return True
    @property
    def closed(self):
        if self.buf is not None and not self.done:
            self.done = True
            self.buf.detach()
        return False
    def readinto(self, b):
        b[:1] = b"x"
        return 1
raw = Raw()
f = io.BufferedReader(raw)
raw.buf = f
print(f.read(1))
```

Recorded on 3.15.2 and main: SIGSEGV. Expected: an exception for the detached stream. The record reports that the pure-Python twin raises `AttributeError` rather than crashing.

Cause: Modules/_io/bufferedio.c:1004 runs `CHECK_CLOSED`, which reads `raw.closed` through `buffered_closed` (:520-532), before taking the lock at :1017. `detach()` (:616-630) clears `self->raw` and the outer read does not recheck it before the raw call at :1640. The record recommends rechecking state after Python callbacks, or protecting this window and detach with the same lock.
