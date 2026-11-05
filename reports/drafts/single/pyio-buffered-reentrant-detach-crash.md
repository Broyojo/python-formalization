<!-- title: BufferedReader.read() crashes if raw.closed detaches the buffer -->
# Bug report

### Bug description

Most methods of io.BufferedReader/Writer/Random run CHECK_CLOSED before they take the lock. CHECK_CLOSED reads raw.closed (buffered_closed), which is Python code when the raw stream is a Python class. If that code calls detach() on the buffered object, detach succeeds (it takes no lock, and a reader's flush only forwards to raw.flush) and sets self->raw to NULL. The method then goes on: read(1) on an empty buffer enters _bufferedreader_read_generic, whose _bufferedreader_fill_buffer calls PyObject_CallMethodOneArg(self->raw, readinto, ...) with self->raw == NULL, which reads Py_TYPE(NULL). The process dies with SIGSEGV. peek, read1, readinto, readline, seek and truncate have the same shape. The same unlocked window lets raw.closed close() the object instead: the buffer is freed and set to NULL, and the next fill then fails with "ValueError: PyMemoryView_FromBuffer(): info->buf must not be NULL" (an internal error leaking), or, for a writer whose close() could not flush everything, hands raw.write a view of address NULL + write_pos, which crashes (the shape of gh-143375).

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

**Expected:** An exception such as "ValueError: raw stream has been detached", as _pyio raises ("AttributeError: 'NoneType' object has no attribute 'read'").

**Actual:** python3 3.15.2: exit status -11 (SIGSEGV). main (python.exe 3.16.0a1+dev): exit status -11 (SIGSEGV). With raw.closed calling close() instead of detach(), both raise ValueError "PyMemoryView_FromBuffer(): info->buf must not be NULL".

**Cause:** Modules/_io/bufferedio.c:1004 CHECK_CLOSED in _io__Buffered_read_impl expands (:370-382) to IS_CLOSED (:364-368), which calls buffered_closed (:520-532); :526 PyObject_GetAttr(self->raw, "closed") runs Python code before the lock is taken at :1017. _io__Buffered_detach_impl (:616-630) takes no lock and sets self->raw = NULL at :626. Nothing re-checks self->ok after CHECK_CLOSED, and :1640 in _bufferedreader_raw_read calls through the NULL pointer. The other methods with CHECK_CLOSED before ENTER_BUFFERED are at :941, :966, :1042, :1101, :1213, :1386, :1471. For close() in the same window, :593-596 free the buffer and :1681 builds a view of self->buffer + start.

**Possible fix:** After every call that can run Python code (IS_CLOSED, _PyIOBase_check_seekable, the raw callbacks), check self->ok and self->buffer again before using them, as textio.c does with buffer_access_safe (gh-143008); or take the lock before CHECK_CLOSED and make detach() take it.

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/pyio-buffered-reentrant-detach-crash.yaml
