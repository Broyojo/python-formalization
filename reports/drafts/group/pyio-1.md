<!-- title: Small inconsistencies in io and _pyio found by a formal model -->
### Bug report

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. _pyio.BufferedRandom: after a seek() that fails, tell() is wrong and read() returns data twice

BufferedRandom.seek first undoes the read-ahead by seeking the raw stream back over the unread part of the read buffer, then calls raw.seek(pos, whence), and only then empties the read buffer. If raw.seek raises (for example OSError EINVAL for a negative position on a real file), the read buffer is kept while the raw position has already been moved back to the logical position. tell() then subtracts the buffered bytes a second time, and the next reads return the buffered bytes followed by the same bytes again from the raw stream. io.BufferedRandom leaves everything unchanged when the raw seek fails.

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
if out["io"] == (2, b"23456789") and out["_pyio"] != out["io"]:
    print("Observed the reported behavior.")
```

</details>

#### 2. _pyio.BufferedReader.readinto raises ValueError when refilled data exceeds the space left in the buffer

BufferedReader._readinto copies from its internal buffer in a loop. Each pass computes avail = min(len(self._read_buf) - self._read_pos, len(buf)), bounded by the size of the whole destination and not by the space left in it, then assigns to buf[written:written+avail]. Once part of the destination is filled and the internal buffer has been refilled, avail can exceed the space left. The memoryview slice is then shorter than the bytes assigned to it, and the assignment raises ValueError. io.BufferedReader returns the data.

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
if results['io'] == (3, b'bcd') and isinstance(results['_pyio'], ValueError):
    print("Observed the reported behavior.")
```

</details>

#### 3. readlines(hint) stops one line early in io.BytesIO and all of _pyio, unlike every other C stream and the docs

The docs say no more lines are read once the total size of the lines so far *exceeds* hint. The C _IOBase.readlines (used by io.StringIO, io.TextIOWrapper, io.BufferedReader, real files) stops when the total is greater than hint. io.BytesIO.readlines and _pyio's IOBase.readlines stop when the total is greater than or equal to hint. So when the lines read so far add up to exactly hint, the same content gives different results: io.BytesIO(b'a\nb\nc').readlines(2) is [b'a\n'], but io.BufferedReader(io.BytesIO(b'a\nb\nc')).readlines(2) is [b'a\n', b'b\n'], and in _pyio every class returns one line. The result of a program can change when a file is replaced by a BytesIO or when io is replaced by _pyio.

*May be intended:* Partly. "hint" is a hint, and BytesIO.readlines's docstring calls it "an approximate bound" (bytesio.c:582). No test pins the boundary (test_memoryio's only hint case, readlines(15) over 11-character lines, passes under both rules). A maintainer would likely accept aligning the code as a cleanup, with low urgency, and could equally choose to soften the docs.

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
if all(len(got[k]) == 1 for k in stop_at_reach) and all(len(got[k]) == 2 for k in stop_at_exceed):
    print("Observed the reported behavior.")
```

</details>

#### 4. io.StringIO accepts a newline argument with an embedded NUL and silently truncates it at the NUL

The StringIO constructor gets the UTF-8 bytes of `newline` with PyUnicode_AsUTF8() and validates them as a NUL-terminated C string, so everything after the first NUL is ignored. The value is then stored from the same C string, so the object behaves as if the prefix had been passed: newline='\n\x00' is '\n', '\r\x00junk' is '\r', '\r\n\x00x' is '\r\n', and '\x00' or '\x00\n' is '' (universal newlines without translation, `newlines` reported). io.TextIOWrapper and both _pyio classes reject all of these with ValueError, so the C StringIO is the only one of the four that accepts them. `_pyio.StringIO` raises "illegal newline value", `io.TextIOWrapper` raises "embedded null character".

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
if accepted == len(bad):
    print("Observed the reported behavior.")
```

</details>

#### 5. io.StringIO(newline=None) turns a \\r\\n split across two writes into two newlines

With newline=None the C StringIO translates line endings on write, once per write() call, with the decoder's `final` flag always set. A '\r' at the end of one write is therefore translated to '\n' immediately, and a '\n' at the start of the next write stays, so 'a\r' + '\nb' gives 'a\n\nb'. Written as one string the same text gives 'a\nb'. The stored text and the number of lines depend on how the text was split into write() calls, and `newlines` reports ('\r', '\n') for text that only has a CRLF. _pyio.StringIO stores the raw text and translates it as a whole on read and getvalue(), so it returns 'a\nb' for both, as does a real text file written in two pieces and read back with newline=None.

*May be intended:* The "always final" comment shows that the one-shot translation was deliberate, but not that this outcome was. bpo-5265 (test_issue5265, "StringIO can duplicate newlines in universal newlines mode") fixed the same symptom for a different path, which suggests maintainers consider it a bug. A fix would have to keep a pending \r across writes and flush it on reads and seeks, so it may be judged not worth it, in which case a docs note is the alternative. bpo-20435 (gh-64634) fixed _pyio.getvalue() to match C on translation, so twin mismatches here are in scope.

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
if res['io'][0] == 'a\n\nb' and res['io'][1] == 'a\nb' and res['_pyio'][0] == 'a\nb' and back == 'a\nb':
    print("Observed the reported behavior.")
```

</details>

#### 6. io.TextIOWrapper.tell() after next() and flush() returns a position past the end, reading past its stale snapshot

next() on a TextIOWrapper clears `telling` (textio.c:3291), so read_chunk stops updating the snapshot (:1957, :2036) but does update b2cratio (:2029-2032). flush() sets `telling` back (:3223) without dropping the snapshot or the decoded characters. A tell() after next() and flush() then rebuilds the position from a snapshot taken before the read, with the ratio of the read: skip_bytes = b2cratio * decoded_chars_used (:2949) exceeds the snapshot, and only an assert bounds it (:2951). Release builds hand the decoder bytes past the end of next_input (:2957). With the empty snapshot that seek() leaves, one byte past is the bytes object's terminating NUL, which decodes as a character; more is memory outside the object (the static empty-bytes singleton here).

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
if pos > len(data) and rest == '':
    print("Observed the reported behavior.")
```

</details>

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
AI tools (Claude and Codex) helped investigate the findings and prepare this report. The examples were rerun on CPython 3.15.2 and main, and the report received technical review. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
