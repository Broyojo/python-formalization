<!-- title: pyio: 15 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. io.Buffered* constructors refuse a raw whose readable()/writable()/seekable() returns a truthy non-bool; _pyio accepts it

The C constructors check the raw stream with _PyIOBase_check_readable/_writable/_seekable,
which accept only the object True (`res != Py_True` refuses everything else). The _pyio
constructors test `if not raw.readable():` and `raw._checkSeekable()`, which accept any truthy
value. A raw stream whose readable() returns 1 is refused by io.BufferedReader with
"UnsupportedOperation: File or stream is not readable." and accepted by _pyio.BufferedReader;
the same holds for writable() and BufferedWriter, and seekable() and BufferedRandom. The same
exact check guards io.BufferedReader.seek (via _PyIOBase_check_seekable at every call).

<details><summary>Reproducer</summary>

```python
import io, _pyio
out = {}
for mod in (io, _pyio):
    class Raw(mod.RawIOBase):
        def readable(self):
            return 1
        def readinto(self, b):
            return 0
    try:
        mod.BufferedReader(Raw())
        out[mod.__name__] = "accepted"
    except Exception as e:
        out[mod.__name__] = f"{type(e).__name__}: {e}"
print(out)
```

</details>

#### 2. _pyio.BufferedReader/Writer deadlock on a re-entrant call where io raises RuntimeError

_pyio.BufferedReader and BufferedWriter guard their methods with `_read_lock` and
`_write_lock`, which are `_thread.allocate_lock()` objects and not re-entrant. If code running
inside a raw stream callback (or a signal handler, the case bpo-10478 was about) calls back into
the same buffered object, the second `with self._read_lock:` blocks forever: the thread
deadlocks on itself. io.BufferedReader detects the same situation in _enter_buffered_busy and
raises RuntimeError("reentrant call inside <_io.BufferedReader>"), and the outer call completes.

<details><summary>Reproducer</summary>

```python
import _pyio, io, threading
def make(mod):
    class Raw(mod.RawIOBase):
        buf = None
        def readable(self):
            return True
        def readinto(self, b):
            if self.buf is not None:
                inner, self.buf = self.buf, None
                try:
                    inner.read(1)
                except RuntimeError as e:
                    print(mod.__name__, "inner:", e)
            b[:1] = b"x"
            return 1
    raw = Raw()
    f = mod.BufferedReader(raw, 4)
    raw.buf = f
    return f
print("io outer:", make(io).read(1))
f = make(_pyio)
t = threading.Thread(target=lambda: print("_pyio outer:", f.read(1)), daemon=True)
t.start()
t.join(2)
if t.is_alive():
    print("_pyio still blocked after 2 s")
```

</details>

#### 3. _pyio.BufferedRandom: after a seek() that fails, tell() is wrong and read() returns data twice

BufferedRandom.seek first undoes the read-ahead by seeking the raw stream back over the unread
part of the read buffer, then calls raw.seek(pos, whence), and only then empties the read
buffer. If raw.seek raises (for example OSError EINVAL for a negative position on a real file),
the read buffer is kept while the raw position has already been moved back to the logical
position. tell() then subtracts the buffered bytes a second time, and the next reads return the
buffered bytes followed by the same bytes again from the raw stream. io.BufferedRandom leaves
everything unchanged when the raw seek fails.

<details><summary>Reproducer</summary>

```python
import io, _pyio, os, tempfile
fd, path = tempfile.mkstemp()
os.write(fd, b"0123456789")
os.close(fd)
out = {}
for mod in (io, _pyio):
    with mod.open(path, "rb+") as f:
        f.read(2)
        try:
            f.seek(-1)
        except OSError:
            pass
        out[mod.__name__] = (f.tell(), f.read())
os.unlink(path)
print(out)
```

</details>

#### 4. _pyio.BufferedReader.readinto raises ValueError when refilled data exceeds the space left in the buffer

BufferedReader._readinto copies from its internal buffer in a loop. Each pass computes
avail = min(len(self._read_buf) - self._read_pos, len(buf)), bounded by the size of the whole
destination and not by the space left in it, then assigns to buf[written:written+avail]. Once
part of the destination is filled and the internal buffer has been refilled, avail can exceed
the space left. The memoryview slice is then shorter than the bytes assigned to it, and the
assignment raises ValueError. io.BufferedReader returns the data.

<details><summary>Reproducer</summary>

```python
import _pyio
import io
results = {}
for mod in (io, _pyio):
    f = mod.BufferedReader(mod.BytesIO(b'abcdefghij'), 3)
    f.read(1)
    b = bytearray(3)
    try:
        results[mod.__name__] = (f.readinto(b), bytes(b))
    except ValueError as e:
        results[mod.__name__] = e
print(results)
```

</details>

#### 5. io.BufferedReader returns uninitialized heap memory when raw.readinto() reports bytes it did not store

_bufferedreader_raw_read passes raw.readinto() a memoryview of the internal buffer (or of the
PyBytesWriter being filled) and trusts any count between 0 and the view's length. The buffer
comes from PyMem_Malloc in _buffered_init and is never cleared, so a raw stream that returns a
count without writing that many bytes makes read(), peek(), read1() and readinto() return
whatever the buffer held: bytes of an earlier read, or uninitialized heap memory (on the first
fill, typically heap pointers). _pyio.BufferedReader reads through RawIOBase.read, which
allocates a zeroed bytearray, so it returns zero bytes for the same raw stream. The C
RawIOBase.read (Modules/_io/iobase.c) has the same exposure: PyByteArray_FromStringAndSize(NULL,
n) does not clear the bytes either.

<details><summary>Reproducer</summary>

```python
import io, _pyio
def run(mod, size):
    class Raw(mod.RawIOBase):
        calls = 0
        def readable(self):
            return True
        def readinto(self, b):
            self.calls += 1
            if self.calls == 1:
                b[:4] = b"abcd"
                return 4
            return len(b)      # claims a full read, stores nothing
    f = mod.BufferedReader(Raw(), size)
    return f.read(1), f.read(3), f.read(1)
c, p = run(io, 4), run(_pyio, 4)
print("io   ", c)
print("_pyio", p)
class Liar(io.RawIOBase):
    def readable(self):
        return True
    def readinto(self, b):
        return len(b)
print("fresh buffer:", io.BufferedReader(Liar(), 16).peek())
# read1(n) reads straight into a fresh PyBytesWriter of n bytes
read1_dirty = []
for n in (16, 300, 4000):
    for _ in range(5):
        r1 = io.BufferedReader(Liar()).read1(n)
        if r1 != bytes(n):
            read1_dirty.append(n)
            break
print("read1 returned bytes nobody wrote for n in", read1_dirty)
```

</details>

#### 6. With a live getbuffer() view, io.BytesIO refuses every write; _pyio.BytesIO refuses only resizes

The docs say the object "cannot be resized or closed" while a view exists. C goes further: it
raises BufferError for every write, including an in-place overwrite, write(b'') and a
truncate(n) that removes nothing. _pyio does what the sentence says: it only fails when the
bytearray would change size. In the other direction, _pyio.BytesIO() with an empty buffer closes
successfully with a live view, because bytearray.clear() on an empty array does not check
exports, and that contradicts the same sentence.

<details><summary>Reproducer</summary>

```python
import io, _pyio
def attempt(f):
    try:
        return f()
    except Exception as e:
        return type(e).__name__
r = {}
for m in (io, _pyio):
    b = m.BytesIO(b'ab')
    v = b.getbuffer()
    w = attempt(lambda: b.write(b'x'))
    e = attempt(lambda: b.write(b''))
    t = attempt(lambda: b.truncate(5))
    v.release()
    del v
    r[m.__name__] = (w, e, t)
    print(m.__name__, 'overwrite:', w, 'write(b""):', e, 'truncate(5):', t)
    b2 = m.BytesIO()
    v2 = b2.getbuffer()
    c = attempt(b2.close)
    print(m.__name__, 'close empty with live view:', c, 'closed:', b2.closed)
    v2.release()
    del v2
```

</details>

#### 7. _pyio.BytesIO.truncate deadlocks when __index__ touches the stream, because it holds self._lock across the call

3.15 gave _pyio.BytesIO a threading.Lock around its state. In read, write and seek the argument
is converted before the lock is taken, but truncate converts it inside `with self._lock:`, so
`pos.__index__()` runs with the lock held. The lock is not re-entrant: an __index__ that calls
seek(0, 1), seek(0, 2), read, a non-empty write or truncate on the same stream blocks the thread
forever. io.BytesIO runs the same __index__ and returns. Separately, truncate does not look at
the stream again afterwards, so an __index__ that closes the stream makes truncate return
normally on a closed stream, where io.BytesIO raises ValueError.

<details><summary>Reproducer</summary>

```python
import _pyio, io, threading
class Seeks:
    def __init__(self, f):
        self.f = f
    def __index__(self):
        self.f.seek(0, 1)
        return 1
def finishes(m):
    f = m.BytesIO(b'abc')
    t = threading.Thread(target=f.truncate, args=(Seeks(f),), daemon=True)
    t.start()
    t.join(3)
    return not t.is_alive()
c, p = finishes(io), finishes(_pyio)
print('io finishes:', c, ' _pyio finishes:', p)
```

</details>

#### 8. readlines(hint) stops one line early in io.BytesIO and all of _pyio, unlike every other C stream and the docs

The docs say no more lines are read once the total size of the lines so far *exceeds* hint. The
C _IOBase.readlines (used by io.StringIO, io.TextIOWrapper, io.BufferedReader, real files)
stops when the total is greater than hint. io.BytesIO.readlines and _pyio's IOBase.readlines
stop when the total is greater than or equal to hint. So when the lines read so far add up to
exactly hint, the same content gives different results:
io.BytesIO(b'a\nb\nc').readlines(2) is [b'a\n'], but
io.BufferedReader(io.BytesIO(b'a\nb\nc')).readlines(2) is [b'a\n', b'b\n'], and in _pyio every
class returns one line. The result of a program can change when a file is replaced by a BytesIO
or when io is replaced by _pyio.

<details><summary>Reproducer</summary>

```python
import io, _pyio
data = b'a\nb\nc'
text = data.decode()
got = {
    'io.BytesIO': io.BytesIO(data).readlines(2),
    'io.BufferedReader': io.BufferedReader(io.BytesIO(data)).readlines(2),
    'io.StringIO': io.StringIO(text).readlines(2),
    'io.TextIOWrapper': io.TextIOWrapper(io.BytesIO(data), encoding='ascii').readlines(2),
    '_pyio.BytesIO': _pyio.BytesIO(data).readlines(2),
    '_pyio.BufferedReader': _pyio.BufferedReader(_pyio.BytesIO(data)).readlines(2),
    '_pyio.StringIO': _pyio.StringIO(text).readlines(2),
}
for k, v in got.items():
    print('%-22s %r' % (k, v))
stop_at_reach = ['io.BytesIO', '_pyio.BytesIO', '_pyio.BufferedReader', '_pyio.StringIO']
stop_at_exceed = ['io.BufferedReader', 'io.StringIO', 'io.TextIOWrapper']
```

</details>

#### 9. io.StringIO accepts a newline argument with an embedded NUL and silently truncates it at the NUL

The StringIO constructor gets the UTF-8 bytes of `newline` with PyUnicode_AsUTF8() and validates
them as a NUL-terminated C string, so everything after the first NUL is ignored. The value is
then stored from the same C string, so the object behaves as if the prefix had been passed:
newline='\n\x00' is '\n', '\r\x00junk' is '\r', '\r\n\x00x' is '\r\n', and '\x00' or '\x00\n'
is '' (universal newlines without translation, `newlines` reported). io.TextIOWrapper and both
_pyio classes reject all of these with ValueError, so the C StringIO is the only one of the four
that accepts them. `_pyio.StringIO` raises "illegal newline value", `io.TextIOWrapper` raises
"embedded null character".

<details><summary>Reproducer</summary>

```python
import io, _pyio
bad = ['\x00', '\n\x00', '\r\x00', '\r\n\x00', '\x00\n', '\r\x00junk']
accepted = 0
for nl in bad:
    try:
        s = io.StringIO('a\nb\r\nc\rd', newline=nl)
        r = repr(s.getvalue()), s.readlines(), s.newlines
        accepted += 1
    except ValueError as e:
        r = 'ValueError: %s' % e
    print('io.StringIO     ', repr(nl), r)
    for name, make in (('_pyio.StringIO  ', lambda: _pyio.StringIO(newline=nl)),
                       ('io.TextIOWrapper', lambda: io.TextIOWrapper(io.BytesIO(), encoding='ascii', newline=nl))):
        try:
            make()
            print(name, repr(nl), 'accepted')
            accepted = -100
        except ValueError as e:
            print(name, repr(nl), 'ValueError:', e)
```

</details>

#### 10. io.StringIO(newline=None) turns a \\r\\n split across two writes into two newlines

With newline=None the C StringIO translates line endings on write, once per write() call, with
the decoder's `final` flag always set. A '\r' at the end of one write is therefore translated to
'\n' immediately, and a '\n' at the start of the next write stays, so 'a\r' + '\nb' gives
'a\n\nb'. Written as one string the same text gives 'a\nb'. The stored text and the number of
lines depend on how the text was split into write() calls, and `newlines` reports
('\r', '\n') for text that only has a CRLF. _pyio.StringIO stores the raw text and translates
it as a whole on read and getvalue(), so it returns 'a\nb' for both, as does a real text file
written in two pieces and read back with newline=None.

<details><summary>Reproducer</summary>

```python
import io, _pyio
res = {}
for m in (io, _pyio):
    s = m.StringIO(newline=None)
    s.write('a\r')
    s.write('\nb')
    one = m.StringIO(newline=None)
    one.write('a\r\nb')
    s.seek(0)
    lines = s.readlines()
    res[m.__name__] = (s.getvalue(), one.getvalue(), lines)
    print(m.__name__, 'two writes:', repr(s.getvalue()), 'one write:', repr(one.getvalue()),
          'lines:', lines, 'newlines:', s.newlines)
b = io.BytesIO()
f = io.TextIOWrapper(b, encoding='ascii', newline='')
f.write('a\r'); f.write('\nb'); f.flush()
back = io.TextIOWrapper(io.BytesIO(b.getvalue()), encoding='ascii', newline=None).read()
print('file written in two pieces, read with newline=None:', repr(back))
```

</details>

#### 11. _pyio.StringIO positions are UTF-8 byte offsets: writing over non-ASCII text corrupts the stream

_pyio.StringIO stores UTF-8 in a BytesIO and its positions are byte offsets. io.StringIO's
positions are code points. Most of the difference is allowed (tell() is opaque), but it also
loses data in operations with no explicit position: _pyio.StringIO('éa').write('x') overwrites
the first *byte* of 'é' and getvalue() then raises UnicodeDecodeError, where io.StringIO gives
'xa'. truncate() after seek(0, 2) style use has the same effect (truncate(1) cuts inside 'é').

<details><summary>Reproducer</summary>

```python
import io, _pyio
def overwrite(m):
    s = m.StringIO('éa')
    s.write('x')
    try:
        return s.getvalue()
    except UnicodeDecodeError as e:
        return 'UnicodeDecodeError: %s' % e
c, p = overwrite(io), overwrite(_pyio)
print('io   ', repr(c))
print('_pyio', repr(p))
```

</details>

#### 12. _pyio.TextIOWrapper.newlines raises AttributeError once a non-universal stream has been read, and is None before the first read where C reports the written newlines

_pyio's `newlines` property returns `self._decoder.newlines if self._decoder else None`. With
newline set to '\n' (the StringIO default), '\r' or '\r\n' the decoder is the plain codec
decoder, which has no `newlines` attribute, so reading the property raises AttributeError as soon
as a read has created the decoder. It works before the first read (None), so the failure depends
on the stream's history. The C property uses PyObject_GetOptionalAttr and returns None. The same
happens for _pyio.TextIOWrapper over a file, not only StringIO.
(2) In the universal modes the twins also disagree before the first read: io.StringIO('a\n',
newline=None).newlines is '\n', because the C StringIO runs its IncrementalNewlineDecoder on
every write (stringio.c:198-200), while _pyio returns None until a read creates its decoder
(_pyio.py:2732-2733). After a read() both report the kinds of the whole value.

<details><summary>Reproducer</summary>

```python
import io, _pyio
def show(m):
    s = m.StringIO('a\nb')
    before = s.newlines
    s.read()
    try:
        return before, repr(s.newlines)
    except AttributeError as e:
        return before, 'AttributeError: %s' % e
c = show(io)
p = show(_pyio)
print('io   ', c)
print('_pyio', p)
before = (io.StringIO('a\n', None).newlines, _pyio.StringIO('a\n', None).newlines)
print('universal, before a read: io %r, _pyio %r' % before)
```

</details>

#### 13. tell() raises OSError after readlines(hint) stops early (_pyio.StringIO and every TextIOWrapper)

TextIOWrapper.__next__ clears `_telling` and only restores it at StopIteration. IOBase.readlines
iterates with `for line in self` and breaks out when the hint is reached, so `_telling` stays
false and tell() raises OSError('telling position disabled by next() call') although the caller
never used iteration. A plain f.readlines(1000) on a text file followed by f.tell() fails, and
seek(0, 1) too. _pyio.StringIO inherits this (also after a plain next()), while io.StringIO does
not. A later read does not re-enable tell(); flush(), getvalue() or truncate() do, after which
_pyio raises AssertionError('pending decoded text') from tell() instead.

<details><summary>Reproducer</summary>

```python
import io, _pyio
def attempt(f):
    try:
        return f.tell()
    except Exception as e:
        return '%s: %s' % (type(e).__name__, e)
data = 'a\nb\nc\n'
r = {}
for name, make in (('io.StringIO', lambda: io.StringIO(data)),
                   ('_pyio.StringIO', lambda: _pyio.StringIO(data)),
                   ('io.TextIOWrapper', lambda: io.TextIOWrapper(io.BytesIO(data.encode()), encoding='ascii'))):
    f = make()
    lines = f.readlines(1)
    r[name] = attempt(f)
    print(name, lines, '-> tell():', r[name])
s = _pyio.StringIO(data)
s.readlines(1)
s.getvalue()
after = attempt(s)
print('_pyio.StringIO readlines(1), getvalue(), tell():', after)
if r['io.StringIO'] == 2 and str(r['_pyio.StringIO']).startswith('OSError') \
   and str(r['io.TextIOWrapper']).startswith('OSError') and after.startswith('AssertionError'):
```

</details>

#### 14. _pyio.StringIO: write and truncate after a read act on the read-ahead position, not the logical one

_pyio.StringIO is a TextIOWrapper, which reads 2048-byte chunks ahead. After read(1) the
underlying BytesIO is already at the end, and write() does not move it back, so
StringIO('abcdef') + read(1) + write('X') gives 'abcdefX' where io.StringIO gives 'aXcdef'.
truncate() has the matching problem: after read(1), truncate(2) really cuts the buffer, but the
decoded read-ahead stays, so read() returns 'bcdef' (data past the truncation) where C returns
'b'. The same behaviour exists in the C and Python TextIOWrapper over 'r+' files, where it is a
long-known issue; here it makes the two StringIO implementations disagree on ASCII text with no
seek involved.

<details><summary>Reproducer</summary>

```python
import io, _pyio
def rw(m):
    s = m.StringIO('abcdef')
    s.read(1)
    s.write('X')
    return s.getvalue()
def rt(m):
    s = m.StringIO('abcdef')
    s.read(1)
    s.truncate(2)
    return s.read(), s.getvalue()
print('read(1), write(X):      io', rw(io), ' _pyio', rw(_pyio))
print('read(1), truncate(2):   io', rt(io), ' _pyio', rt(_pyio))
```

</details>

#### 15. io.TextIOWrapper.tell() after next() and flush() returns a position past the end, reading past its stale snapshot

next() on a TextIOWrapper clears `telling` (textio.c:3291), so read_chunk stops updating the
snapshot (:1957, :2036) but does update b2cratio (:2029-2032). flush() sets `telling` back
(:3223) without dropping the snapshot or the decoded characters. A tell() after next() and
flush() then rebuilds the position from a snapshot taken before the read, with the ratio of the
read: skip_bytes = b2cratio * decoded_chars_used (:2949) exceeds the snapshot, and only an
assert bounds it (:2951). Release builds hand the decoder bytes past the end of next_input
(:2957). With the empty snapshot that seek() leaves, one byte past is the bytes object's
terminating NUL, which decodes as a character; more is memory outside the object (the static
empty-bytes singleton here).

<details><summary>Reproducer</summary>

```python
import io
data = b'\nb\xe2\x82\xac'
f = io.TextIOWrapper(io.BytesIO(data), encoding='utf-8')
f.seek(f.tell())
line = next(f)
f.flush()
pos = f.tell()
f.seek(pos)
rest = f.read()
print('line', repr(line), 'tell', pos, 'len', len(data), 'rest', repr(rest))
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
