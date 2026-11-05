<!-- title: pickle: 13 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. pickle: a BINBYTES or BYTEARRAY8 payload may run past its frame when the frame ends on a chunk boundary, unlike Python for BINBYTES (new in 3.15)

`load_counted_binbytes` and `load_counted_bytearray` now read a payload above 1 MiB in doubling chunks,
each its own `_Unpickler_ReadInto`. That function refuses a read that crosses the end of a frame only
if the frame still held data when the read began. So a frame that ends exactly at a chunk boundary (1,
2, 4 ... MiB into the payload) is left silently, and the payload goes on outside it. With the frame
ending anywhere else C raises "pickle exhausted before end of frame". For BINBYTES and BINBYTES8
Python raises at every frame end, so the twins differ. `_Unpickler.load_bytearray8` has the same
chunks, through `_Unframer.read`, so for BYTEARRAY8 both twins accept.

<details><summary>Reproducer</summary>

```python
import pickle, struct
K = 1 << 20
def stream(op, cut):
    head = op + (struct.pack('<I', 2 * K) if op == b'B' else struct.pack('<Q', 2 * K))
    body = head + b'a' * cut
    return b'\x95' + struct.pack('<Q', len(body)) + body + b'b' * (2 * K - cut) + b'.'
def r(f, s):
    try: return ('ok', len(f(s)))
    except Exception as e: return (type(e).__name__, str(e))
results = []
for op in (b'B', b'\x8e', b'\x96'):
    for cut in (K, K + 5):
        s = stream(op, cut)
        results.append((op, cut, r(pickle.loads, s), r(pickle._loads, s)))
        print(*results[-1])
exhausted = ('UnpicklingError', 'pickle exhausted before end of frame')
done = ('ok', 2 * K)
on_chunk = [x for x in results if x[1] == K]
off_chunk = [x for x in results if x[1] != K]
if (all(x[2] == done and x[3] == (done if x[0] == b'\x96' else exhausted) for x in on_chunk)
        and all(x[2] == exhausted and x[3] == exhausted for x in off_chunk)):
```

</details>

#### 2. _pickle: INT opcode skips the 4300-digit limit when the value fits a C long

`load_int` tries strtol before PyLong_FromString, so a long run of leading zeros parses even past
`sys.get_int_max_str_digits()`: `pickle.loads(b'I' + b'0'*5000 + b'1\n.')` is 1. The same stream
raises ValueError in `pickle._loads`, because `int(bytes)` counts every digit, and the C unpickler
itself raises for the same digits under LONG, GET and PUT, and under INT once the value overflows
a C long. So the limit is not applied consistently, even within `_pickle`.

<details><summary>Reproducer</summary>

```python
import pickle
data = b'I' + b'0' * 5000 + b'1\n.'
def r(f, s):
    try: return ('ok', f(s))
    except Exception as e: return (type(e).__name__, str(e)[:60])
c, p = r(pickle.loads, data), r(pickle._loads, data)
ls = b'L' + b'0' * 5000 + b'1L\n.'
l = r(pickle.loads, ls)
print('INT C', c, 'INT Python', p, 'LONG C', l)
```

</details>

#### 3. _pickle: save_long checks the LONG4 size before trimming the sign byte, so it refuses an int that fits

LONG4 stores a signed 32-bit byte count, so at most 2**31 - 1 bytes. `save_long` computes
`nbytes = nbits / 8 + 1` and raises OverflowError "int too large to pickle" when that exceeds
0x7fffffff, before dropping the redundant sign byte of an int of the form -(2**(8*j - 1)). For
j = 2**31 - 1 the trimmed encoding has exactly 2**31 - 1 bytes and is valid; the Python pickler
writes it, the C pickler refuses it. Off by one in an error check, at a 2 GiB int.
Other oversized ints differ only in class: C OverflowError, Python struct.error.

<details><summary>Reproducer</summary>

```python
# Needs about 7 GiB of memory and a few seconds.
import pickle
class Sink:
    n = 0
    def write(self, b): self.n += len(b)
x = -(1 << (8 * (2**31 - 1) - 1))
c, p = Sink(), Sink()
try:
    pickle.Pickler(c, 2).dump(x); cres = 'ok'
except Exception as e:
    cres = type(e).__name__ + ': ' + str(e)
try:
    pickle._Pickler(p, 2).dump(x); pres = 'ok'
except Exception as e:
    pres = type(e).__name__ + ': ' + str(e)
print('C     :', cres)
print('Python:', pres, p.n, 'bytes')
```

</details>

#### 4. pickle: C Unpickler's memo_dict is unknown to MEMOIZE, memo.copy() and the memo setter (new in 3.15)

gh-115952 sends sparse memo keys to a new `memo_dict`. The rest of the unpickler still treats the
array as the whole memo. Three results, on 3.15.2:
- `memo_len` does not count dict keys, and MEMOIZE writes at `memo_len`. After `BINPUT 200`,
  `MEMOIZE` stores at index 0 in C and at index 1 in Python, so `b'Nq\xc8K\x07\x940h\x01.'` raises
  UnpicklingError in C and returns 7 in Python, and `h\x00` instead of `h\x01` does the reverse.
- `Unpickler.memo.copy()` and `__reduce__` read only the array: after `BINPUT 200`, C gives `{}` and
  `_Unpickler.memo` is `{200: None}`.
- `u.memo = {}` does not clear `memo_dict`: a following `BINGET 200` finds the old object in C and
  raises UnpicklingError in Python.

<details><summary>Reproducer</summary>

```python
import io, pickle
def r(f, s):
    try: return ('ok', f(s))
    except Exception as e: return (type(e).__name__, str(e))
s = b'Nq\xc8K\x07\x940h\x01.'
c, p = r(pickle.loads, s), r(pickle._loads, s)
print('MEMOIZE after BINPUT 200: C', c, 'Python', p)
u = pickle.Unpickler(io.BytesIO(b'Nq\xc8.')); u.load()
v = pickle._Unpickler(io.BytesIO(b'Nq\xc8.')); v.load()
print('memo after BINPUT 200: C', u.memo.copy(), 'Python', v.memo)
w = pickle.Unpickler(io.BytesIO(b'K\x07q\xc8.h\xc8.')); w.load(); w.memo = {}
x = pickle._Unpickler(io.BytesIO(b'K\x07q\xc8.h\xc8.')); x.load(); x.memo = {}
a, b = r(lambda _: w.load(), None), r(lambda _: x.load(), None)
print('BINGET 200 after memo = {}: C', a, 'Python', b)
if (c[0] == 'UnpicklingError' and p == ('ok', 7) and u.memo.copy() == {} and v.memo == {200: None}
        and a == ('ok', 7) and b[0] == 'UnpicklingError'):
```

</details>

#### 5. _pickle: INT, LONG, GET and PUT stop at an embedded NUL and ignore the rest of the line

The text opcodes pass the line to strtol / PyLong_FromString, which treat NUL as the end of the
string, so `b'I12\x00junk\n.'` is 12 and `b'L5\x00junkL\n.'` is 5 in C. `pickle._loads` calls
`int(bytes)`, which rejects embedded NUL. GET and PUT behave the same way.

<details><summary>Reproducer</summary>

```python
import pickle
def r(f, s):
    try: return ('ok', f(s))
    except Exception as e: return (type(e).__name__, str(e))
results = []
for s in (b'I12\x00junk\n.', b'L5\x00junkL\n.', b'Np0\x00x\ng0\n.'):
    c, p = r(pickle.loads, s), r(pickle._loads, s)
    print(s, 'C', c, 'Python', p)
    results.append(c[0] == 'ok' and p[0] == 'ValueError')
```

</details>

#### 6. _pickle: PUT with an index of 2**63 or more raises OverflowError; the pickle.py memo is a dict

`load_put` converts the text index with PyLong_AsSsize_t, so `b'Np9223372036854775808\n.'` raises
OverflowError in C and returns None in Python. GET with such an index raises OverflowError in C and
UnpicklingError in Python.

<details><summary>Reproducer</summary>

```python
import pickle
data = b'Np9223372036854775808\n.'
def r(f, s):
    try: return ('ok', f(s))
    except Exception as e: return (type(e).__name__, str(e))
c, p = r(pickle.loads, data), r(pickle._loads, data)
print('C', c, 'Python', p)
```

</details>

#### 7. pickle: pickle._dumps accepts a float protocol and truncates it, pickle.dumps raises TypeError

`_Pickler.__init__` compares `protocol` with 0 and 5 and stores `int(protocol)`, so any float in
[0, 5] is accepted and truncated (`pickle._dumps(None, 2.5)` is `b'\x80\x02N.'`, 4.999 is
protocol 4, 0.5 is protocol 0) and any negative float selects protocol 5. The C pickler converts
the argument with `PyLong_AsLong`, which refuses floats: `pickle.dumps(None, 2.5)` raises
TypeError "'float' object cannot be interpreted as an integer". Floats above 5 and NaN are
ValueError in Python, TypeError in C.

<details><summary>Reproducer</summary>

```python
import pickle
def r(f, p):
    try: return ('ok', f(None, p))
    except Exception as e: return (type(e).__name__, str(e))
c, py = r(pickle.dumps, 2.5), r(pickle._dumps, 2.5)
print('C', c, '| Python', py)
```

</details>

#### 8. pickle: a protocol outside C long raises OverflowError in C, while pickle.py accepts huge negatives and raises ValueError for huge positives

`pickle.py` documents that any negative protocol selects the highest one, and `_Pickler.__init__`
implements that for every int. The C pickler converts the argument with `PyLong_AsLong` first, so
`pickle.dumps(None, -2**63 - 1)` raises OverflowError where `pickle._dumps` succeeds, and
`pickle.dumps(None, 2**63)` raises OverflowError where `pickle._dumps` raises the documented
ValueError "pickle protocol must be <= 5".

<details><summary>Reproducer</summary>

```python
import pickle
def r(f, *a):
    try: return ('ok', f(*a))
    except Exception as e: return (type(e).__name__, str(e))
neg = -2**63 - 1
big = 2**63
a, b = r(pickle.dumps, None, neg), r(pickle._dumps, None, neg)
c, d = r(pickle.dumps, None, big), r(pickle._dumps, None, big)
print('protocol', neg, 'C', a, 'Python', b)
print('protocol', big, 'C', c, 'Python', d)
```

</details>

#### 9. pickle.py: bytes over 4 GiB at protocol 3 raise a bare struct.error where C explains the limit with OverflowError

At protocol 3 a `bytes` object of 2**32 bytes or more cannot be encoded: BINBYTES has a 4-byte
length and BINBYTES8 needs protocol 4. The C pickler raises OverflowError "serializing a bytes
object larger than 4 GiB requires pickle protocol 4 or higher". `pickle._dumps` falls through to
`pack("<I", n)` and leaks `struct.error: 'I' format requires 0 <= number <= 4294967295`, which
names neither the problem nor the fix. The same holds for `str` at protocols 1-3 (BINUNICODE), and
for memo indices of 2**32 or more (C PicklingError, Python struct.error).

<details><summary>Reproducer</summary>

```python
import pickle
b = bytes(2**32)   # calloc'd: no memory is touched, neither twin reads the data
def r(f):
    try: f(b, 3); return ('ok', '')
    except Exception as e: return (type(e).__name__, str(e))
c, p = r(pickle.dumps), r(pickle._dumps)
print('C     :', c)
print('Python:', p)
```

</details>

#### 10. pickle.py: malformed streams raise raw IndexError, KeyError and struct.error where _pickle raises UnpicklingError

On a malformed stream the C unpickler raises UnpicklingError, with a message such as "unpickling
stack underflow", "could not find MARK", "invalid load key" or "pickle data was truncated". The
Python unpickler lets the underlying error through: `b'0'` gives IndexError "pop from empty list",
`b'\xff'` gives KeyError 255, `b'J\x01\x02'` gives struct.error. Across the difftest's hand-made
streams this is by far the most common twin difference, in class and in message. An empty input is
EOFError in both, but with no message in Python.

<details><summary>Reproducer</summary>

```python
import pickle
def r(f, s):
    try: return ('ok', f(s))
    except Exception as e: return (type(e).__name__, str(e))
ok = []
for s, want in ((b'0', 'IndexError'), (b'\xff', 'KeyError'), (b'J\x01\x02', 'error')):
    c, p = r(pickle.loads, s), r(pickle._loads, s)
    print(s, 'C', c, 'Python', p)
    ok.append(c[0] == 'UnpicklingError' and p[0] == want)
```

</details>

#### 11. pickletools.dis: IndexError instead of ValueError when an opcode that does not expect a mark consumes one

`dis` tracks marks twice, on the emulated `stack` and in `markstack`. An opcode such as TUPLE1 or DUP
has no mark in `stack_before`, so it can delete a mark from `stack` while its `markstack` entry stays.
The next opcode that does expect a mark passes the `if markstack` test and runs
`while stack[-1] is not markobject`, which walks off the end of the list.
`pickletools.dis(b'(\x85t.')` raises IndexError "list index out of range".

<details><summary>Reproducer</summary>

```python
import io, pickle, pickletools
data = b'(\x85t.'
def r(f):
    try:
        return ('ok', f())
    except Exception as e:
        return (type(e).__name__, str(e))
d = r(lambda: pickletools.dis(data, out=io.StringIO()))
c, p = r(lambda: pickle.loads(data)), r(lambda: pickle._loads(data))
print('dis', d, 'C', c, 'Python', p)
```

</details>

#### 12. pickletools: read_stringnl_noescape undoes escapes, so GLOBAL and PERSID arguments differ from what pickle reads, and valid pickles are rejected

`read_stringnl_noescape` calls `read_stringnl(f, stripquotes=False, encoding='utf-8')`, which leaves
`decode=True`, so `codecs.escape_decode` runs on the line. The descriptor says "without embedded
escapes", and both unpicklers read these lines verbatim.

<details><summary>Reproducer</summary>

```python
import io, pickle, pickletools
class P(pickle.Pickler):
    def persistent_id(self, obj):
        return obj if isinstance(obj, str) and obj.startswith('pid') else None
class U(pickle.Unpickler):
    def persistent_load(self, pid):
        return ('loaded', pid)
class PyU(pickle._Unpickler):
    def persistent_load(self, pid):
        return ('loaded', pid)
def dump(pid):
    f = io.BytesIO()
    P(f, 0).dump(pid)
    return f.getvalue()
s = dump('pid\\')
ok = U(io.BytesIO(s)).load() == PyU(io.BytesIO(s)).load() == ('loaded', 'pid\\')
try:
    list(pickletools.genops(s))
    rejected = False
except ValueError as e:
    print('genops', e)
    rejected = True
t = dump('pid\\x41')
shown = [a for _, a, _ in pickletools.genops(t)][0]
loaded = U(io.BytesIO(t)).load()[1]
print('stream', t, 'pickletools', shown, 'unpickler', loaded)
```

</details>

#### 13. pickle: the C and pure-Python picklers stop at different nesting depths (C stack vs sys.getrecursionlimit())

`_Py_EnterRecursiveCall` in `_pickle` is a check of the machine stack pointer since 3.14, so
`pickle.dumps` nests as deep as the C stack allows (10000 lists pickle, 100000 raise "Stack
overflow (used 8160 kB) while pickling an object" on Linux with an 8 MB stack), while
`pickle._dumps` pushes three Python frames per list level (`save`, `save_list`,
`_batch_appends`) and raises RecursionError at `sys.getrecursionlimit()`: at the default limit
of 1000, lists 331 deep fail at protocols 0, 2 and 5, and `pickle.dumps` of the same object
succeeds. The Lean model has both limits as parameters (C stack room in levels, Python frames
left): the twins agree with `4 * depth + 4` levels and `10 * depth + 18` frames
(pickle-dumps-twins-narrow) and whenever neither raises its RecursionError
(pickle-dumps-twins-norec); the statement for every limit is refuted with `[[]]`, 100 levels
and 5 frames (pickle-dumps-twins-rec).

<details><summary>Reproducer</summary>

```python
import pickle
v = []
for _ in range(400):
    v = [v]
def r(f):
    try:
        f(v, 5)
        return 'ok'
    except RecursionError as e:
        return 'RecursionError: ' + str(e)
c, py = r(pickle.dumps), r(pickle._dumps)
print('C', c, '| Python', py)
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
