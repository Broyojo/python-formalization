<!-- title: sequences: 9 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. a[i:j:k] = array() with k != 1 deletes the slice instead of raising ValueError like list

Assigning an empty array to an extended slice (step other than 1) of an array.array
silently deletes the selected items:
a = array('b', [1, 2, 3, 4, 5]); a[::2] = array('b')  ->  array('b', [2, 4]).
The documented rule (Doc/library/stdtypes.rst note (1): "If k is not equal to 1, t must
have the same length as the slice it is replacing") and list behave differently:
l = [1, 2, 3, 4, 5]; l[::2] = []  ->  ValueError: attempt to assign sequence of size 0 to
extended slice of size 3. A non-empty right-hand side of the wrong length does raise
ValueError for arrays too (a[::2] = array('b', [9]) -> "attempt to assign array of size 1 to
extended slice of size 3"), so only the empty case is special. bytearray has the same code
shape and the same behaviour (b[::2] = b'' deletes).
Lean: ArraySliceAssignAgree (array slice assignment agrees with list slice assignment up to
the exception message) is refuted by this input; ArraySliceAssignAgreeNonempty (the same for
a non-empty right-hand side) and ListSliceAssign (list slice assignment equals the
language-reference semantics computed with slice.indices, for all int bounds and steps) are
proven.

<details><summary>Reproducer</summary>

```python
from array import array
a = array('b', [1, 2, 3, 4, 5])
a[::2] = array('b')
l = [1, 2, 3, 4, 5]
try:
    l[::2] = []
    lr = repr(l)
except ValueError as e:
    lr = 'ValueError: %s' % e
try:
    a2 = array('b', [1, 2, 3, 4, 5]); a2[::2] = array('b', [9])
    ar = repr(a2)
except ValueError as e:
    ar = 'ValueError: %s' % e
b = bytearray(b'\x01\x02\x03\x04\x05')
b[::2] = b''
print('array  a[::2] = array("b")      ->', a)
print('list   l[::2] = []              ->', lr)
print('array  a[::2] = array("b", [9]) ->', ar)
print('bytearray b[::2] = b""          ->', b)
```

</details>

#### 2. array.fromfile() raises ValueError and inserts nothing when the file ends inside an item, though the docs promise EOFError with the available items inserted

fromfile(f, n) reads n * itemsize bytes and hands whatever read() returned to frombytes
(Modules/arraymodule.c:1778). When the file ends in the middle of an item, read() returns a
length that is not a multiple of the item size, frombytes raises
ValueError("bytes length not a multiple of item size") (:1924-1929), and fromfile returns
before its EOFError check (:1783-1788). So for a file holding 6 bytes,
array('i').fromfile(f, 2) raises ValueError and the array stays empty, while the whole item
that was available is lost and the 6 bytes are consumed from the file. With 4 bytes the same
call raises EOFError and inserts the item, as documented. Python 2 truncated the partial item
and inserted the whole ones.
The same check uses `!=` (:1776), so a read() that returns more bytes than asked appends all of
them and then raises EOFError("read() didn't return enough bytes").
Lean (lean/PyLean/Sequences/ArrayFile.lean): ArrayFromFileDoc is refuted by a file of 6 bytes
and n = 2 on an 'i' array; ArrayFromFile states the exact behaviour for every read() callback.

<details><summary>Reproducer</summary>

```python
import io
from array import array
a = array('i')
f = io.BytesIO(b'\x01\x00\x00\x00\x02\x00')
try:
    a.fromfile(f, 2)
    exc = None
except Exception as e:
    exc = type(e).__name__
b = array('i')
try:
    b.fromfile(io.BytesIO(b'\x01\x00\x00\x00'), 2)
    exc2 = None
except EOFError:
    exc2 = 'EOFError'
print(exc, list(a), f.tell(), exc2, list(b))
```

</details>

#### 3. array._array_reconstructor rejects odd-length unicode arrays in the other byte order: mformat_descriptors has UTF sizes 4 and 8

mformat_descriptors lists the UTF-16 machine formats with size 4 and the UTF-32 ones with
size 8, while the units are 2 and 4 bytes. The reconstructor's slow path checks
`Py_SIZE(items) % mf_descr.size`, so a pickle of a 'w' array with an odd number of
characters from a machine of the other byte order fails with
ValueError: string length not a multiple of item size. Even lengths work, and so does the
native format, which takes the fast path. The same holds for UTF-16 with 'u' pickles.
Lean: ArrayReconstructUTF is refuted by the one-character string.

<details><summary>Reproducer</summary>

```python
import array
odd = 'abc'.encode('utf-32-be')
even = 'ab'.encode('utf-32-be')
try:
    array._array_reconstructor(array.array, 'w', 21, odd)
    err = None
except ValueError as e:
    err = str(e)
ok = array._array_reconstructor(array.array, 'w', 21, even)
print(err, ok)
```

</details>

#### 4. repr() of a 'Zd' or 'Zf' array with an infinite or NaN imaginary part is not eval()-able: it contains infj and nanj

array_repr writes the repr of tolist() (Modules/arraymodule.c:2715-2723). For the complex
typecodes new in 3.15 the items are complex numbers, and complex_repr writes an infinite or NaN
imaginary part as `infj` / `nanj`: repr(array('Zd', [complex(0, inf)])) is
"array('Zd', [infj])" and complex(1, nan) gives "array('Zd', [(1+nanj)])". The documentation
promises that repr can be passed to eval() once `array`, `inf` and `nan` are defined; with
those defined, eval raises NameError: name 'infj' is not defined. The float typecodes are fine,
because a float repr uses only `inf` and `nan`.
Lean (lean/PyLean/Sequences/ArrayRepr.lean): ArrayReprNames (the only names in repr(a) are the
type, `inf` and `nan`) is refuted by array('Zd', [infj]); arrRepr mirrors array_repr with the
exact float_repr and complex_repr of Binary64.Dtoa and Binary64.Complex.

<details><summary>Reproducer</summary>

```python
from array import array
inf, nan = float('inf'), float('nan')
r1 = repr(array('Zd', [complex(0, inf)]))
r2 = repr(array('Zf', [complex(1, nan)]))
try:
    eval(r1)
    e1 = None
except NameError as e:
    e1 = str(e)
print(r1, r2, e1)
```

</details>

#### 5. array('w').tounicode() and repr() drop a leading U+FEFF and raise UnicodeDecodeError on surrogates, because they decode UTF-32 with byteorder 0

array('w', s).tounicode() should give s back, and the docs say it does. It calls
PyUnicode_DecodeUTF32 with byteorder = 0, which is the "detect a byte order mark" mode, not
native order. So array('w', '\ufeffabc').tounicode() is 'abc', and repr shows
array('w', 'abc'), which is a different array. Storing a mark in the other byte order with
frombytes reinterprets everything after it. Surrogates, which str allows and 'w' stores,
raise UnicodeDecodeError, from repr too, so such an array cannot be printed. The deprecated
'u' typecode has none of these problems, as it uses PyUnicode_FromWideChar.
Lean: ArrayToUnicodeW is refuted by [U+FEFF, 'a']; ArrayToUnicodeChecked (no surrogates, no
leading U+FEFF, and every str for 'u') is proven.
ArrayReprWInjective (two 'w' arrays with equal reprs hold the same characters,
lean/PyLean/Sequences/ArrayRepr.lean) is refuted by array('w', '\ufeffa') and array('w', 'a').

<details><summary>Reproducer</summary>

```python
import array
s = '\ufeffabc'
a = array.array('w', s)
t = a.tounicode()
print(ascii(t), repr(a), list(map(hex, map(ord, a))))
try:
    repr(array.array('w', '\ud800'))
    err = None
except UnicodeDecodeError as e:
    err = type(e).__name__
```

</details>

#### 6. deque.extend/extendleft keep applying the old maxlen after the iterator re-initialises the deque, leaving len(d) > d.maxlen for good

deque_extend_impl and deque_extendleft_impl read `Py_ssize_t maxlen = deque->maxlen` once on entry and pass that
local to deque_append_lock_held for every item. An iterator (its __iter__ or __next__)
may call d.__init__(maxlen=m) on the deque being extended; __init__ clears the deque and
stores the new bound, but the loop goes on trimming with the old one. Starting from an
unbounded deque, every later item is kept, so the deque ends up longer than its own
maxlen: deque([2, 3], maxlen=1) or even deque([1, 2, 3], maxlen=0). The state is
permanent: append/appendleft trim only one item each (NEEDS_TRIM pops once), so the
length never comes back below maxlen, d.copy() (which re-applies maxlen) is no longer
equal to d, and pickling/copy.copy silently drop items. In the other direction, a bounded
deque re-initialised as unbounded keeps being trimmed to the old bound during that extend:
deque(maxlen=2) extended by an iterator that calls d.__init__() after its first item
holds only the last two items with maxlen None. extendleft is the same (:539). Nothing
notices: unlike iteration, extend has no mutation check.
Lean: DequeExtendKeepsBound ("for every iterator whose __iter__/__next__ calls each keep
the deque's invariant len(d) <= maxlen, __init__ included, extend and extendleft leave a
deque that satisfies it") is refuted with the __iter__ form below, and
dequeExtendKeepsBound_neither shows each of extend and extendleft fails on it
(deque([1, 2, 3], maxlen=1) and deque([3, 2, 1], maxlen=1)). DequeExtendStaleBound
(proven) states the exact outcome for every entry bound and every re-init bound m': the
items are cut to the entry bound, maxlen is m', and the block layout stays valid.
DequeExtendRe (the invariant and maxlen kept when the calls do not change maxlen, and
the exact outcome) is proven.

<details><summary>Reproducer</summary>

```python
import copy
from collections import deque
d = deque()
def g():
    yield 1
    d.__init__(maxlen=1)
    yield 2
    yield 3
d.extend(g())
r1 = (list(d), d.maxlen)
d.append(4)
r2 = (list(d), d.maxlen)
c = d.copy()
e = deque()
class X:
    def __iter__(self):
        e.__init__(maxlen=0)
        return iter([1, 2, 3])
e.extend(X())
r3 = (list(e), e.maxlen)
f = deque()
def h():
    yield 1
    f.__init__(maxlen=1)
    yield 2
    yield 3
f.extendleft(h())
r4 = (list(f), f.maxlen)
b = deque(maxlen=2)
def k():
    yield 1
    b.__init__()
    yield 2
    yield 3
    yield 4
b.extend(k())
r5 = (list(b), b.maxlen)
g2 = deque()
class Y:
    def __iter__(self):
        g2.__init__(maxlen=1)
        return iter([1, 2, 3])
g2.extendleft(Y())
r6 = (list(g2), g2.maxlen)
print('extend, __next__ re-inits to maxlen=1 :', r1)
print('then append(4)                        :', r2)
print('d.copy() == d                         :', c == d, list(c))
print('extend, __iter__ re-inits to maxlen=0 :', r3)
print('extendleft, __next__ re-inits         :', r4)
print('bounded, __next__ re-inits unbounded  :', r5)
print('extendleft, __iter__ re-inits to 1    :', r6)
if (r1 == ([2, 3], 1) and r2 == ([3, 4], 1) and c != d and len(c) == 1
        and r3 == ([1, 2, 3], 0) and r4 == ([3, 2], 1) and r5 == ([3, 4], None)
        and r6 == ([3, 2, 1], 1)):
```

</details>

#### 7. deque *= n / deque * n raise MemoryError for a bounded deque of 2+ items although the result has at most maxlen items

For a bounded deque, d *= n keeps the last maxlen items of list(d) * n, and the code
deliberately shortens the work to ceil(maxlen / len(d)) repetitions (bpo-29634). But for
len(d) >= 2 the overflow guard `size > PY_SSIZE_T_MAX / n` runs *before* that maxlen
reduction, so a large n raises MemoryError even though the result has at most maxlen items
and no large allocation is ever needed. The single-item fast path applies maxlen first and
succeeds: deque([1], maxlen=3) *= 2**62 gives deque([1, 1, 1]), while
deque([1, 2], maxlen=3) *= 2**62 (and deque([1, 2], maxlen=3) * 2**62) raise MemoryError.
Small factors work: deque([1, 2], maxlen=3) * 4 == deque([2, 1, 2], maxlen=3).
Lean: DequeIRepeat (keepLast maxlen (items * n) for every bounded deque) is refuted by this
input; DequeIRepeatChecked (same statement when len(d) <= 1 or len(d) * n <= sys.maxsize)
is proven, including the ceil(maxlen / size) reduction and the block-filling fast path.
The same pair for `d * n` (deque_repeat): DequeMul refuted, DequeMulChecked proven.

<details><summary>Reproducer</summary>

```python
from collections import deque
def run(f):
    try:
        return repr(f())
    except Exception as e:
        return type(e).__name__
d1 = deque([1], maxlen=3)
r1 = run(lambda: d1.__imul__(2**62))
d2 = deque([1, 2], maxlen=3)
r2 = run(lambda: d2.__imul__(2**62))
r3 = run(lambda: deque([1, 2], maxlen=3) * 2**62)
small = deque([1, 2], maxlen=3) * 4
print('deque([1], maxlen=3) *= 2**62    ->', r1)
print('deque([1, 2], maxlen=3) *= 2**62 ->', r2)
print('deque([1, 2], maxlen=3) * 2**62  ->', r3)
print('deque([1, 2], maxlen=3) * 4      ->', small, '(expected tail of [1, 2] * n:', ([1, 2] * 4)[-3:], ')')
if r1.startswith('deque([1, 1, 1]') and r2 == 'MemoryError' and r3 == 'MemoryError' \
        and list(small) == ([1, 2] * 4)[-3:]:
```

</details>

#### 8. type(iter(deque))() and type(reversed(deque))() silently ignore keyword arguments

The deque iterator types are constructible from Python (pickle uses them:
it.__reduce__() returns (type(it), (d, index))). Their tp_new, dequeiter_new and
dequereviter_new, parse `args` with PyArg_ParseTuple(args, "O!|n", ...) and never look at
`kwds`, so any keyword argument is accepted and dropped. type(iter(d))(d, index=3) returns
a fresh iterator over all of d instead of raising TypeError (or honouring index), and
type(iter(d))(d, 2, index=4) or type(iter(d))(d, bogus=1) are accepted too. Every other
argument error is reported (a non-deque first argument, a non-int index, an index outside
Py_ssize_t), and calling without the positional deque fails with "function takes at least
1 argument (0 given)" even when deque= is passed as a keyword.
Lean: DequeIterNewKw ("both constructors raise TypeError when given keyword arguments") is
refuted (dequeIterNewKw_neither breaks each); DequeIterNew (positional use, the
consumption count, __length_hint__ and the __reduce__ round trip) is proven.

<details><summary>Reproducer</summary>

```python
from collections import deque
d = deque(range(5))
IT, RIT = type(iter(d)), type(reversed(d))
r1 = list(IT(d, index=3))
r2 = list(RIT(d, index=3))
r3 = list(IT(d, 2, index=4))
r4 = list(IT(d, bogus=1))
try:
    IT(deque=d)
    r5 = 'accepted'
except TypeError as e:
    r5 = str(e)
print('IT(d, index=3)       :', r1)
print('RIT(d, index=3)      :', r2)
print('IT(d, 2, index=4)    :', r3)
print('IT(d, bogus=1)       :', r4)
print('IT(deque=d)          :', r5)
if (r1 == [0, 1, 2, 3, 4] and r2 == [4, 3, 2, 1, 0] and r3 == [2, 3, 4]
        and r4 == [0, 1, 2, 3, 4] and 'at least 1 argument' in r5):
```

</details>

#### 9. list.insert(i, x) raises OverflowError for |i| >= 2**63 although it is documented as equivalent to s[i:i] = [x], which clips

The docs define sequence.insert(index, value) as "equivalent to writing
sequence[index:index] = [value]" (Doc/builtins/stdtypes.rst:1612-1615). Slice bounds are
clipped for any int (PySlice_Unpack saturates to Py_ssize_t), so l[2**63:2**63] = [9]
appends and l[-2**63-1:-2**63-1] = [9] prepends. list.insert converts its index with the
Argument Clinic Py_ssize_t converter and raises "OverflowError: Python int too large to
convert to C ssize_t" for the same indices, before the identical clipping in ins1().
array.array.insert and collections.deque.insert behave like list.insert.
Lean: InsertIsSliceAssign (list.insert(i, x) == (l[i:i] = [x]) for every int i) is refuted
at i = 2**63; InsertIsSliceAssignSsize (the same for i inside Py_ssize_t) and InsertAgree
(list/array/deque insert agree for every int i, deque's documented full-deque IndexError
aside) are proven.

<details><summary>Reproducer</summary>

```python
from array import array
from collections import deque
def run(f):
    try:
        return repr(f())
    except Exception as e:
        return '%s: %s' % (type(e).__name__, e)
l1 = [1, 2, 3]
r1 = run(lambda: l1.insert(2**63, 9))
l2 = [1, 2, 3]
l2[2**63:2**63] = [9]
l3 = [1, 2, 3]
l3[-2**63 - 1:-2**63 - 1] = [9]
r4 = run(lambda: l3.copy().insert(-2**63 - 1, 9))
ra = run(lambda: array('b', [1, 2, 3]).insert(2**63, 9))
rd = run(lambda: deque([1, 2, 3]).insert(2**63, 9))
print('l.insert(2**63, 9)         ->', r1)
print('l[2**63:2**63] = [9]       ->', l2)
print('l[-2**63-1:-2**63-1] = [9] ->', l3, '| insert:', r4)
print('array.insert / deque.insert ->', ra, '|', rd)
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
