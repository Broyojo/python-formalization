<!-- title: Small inconsistencies in array and collections found by a formal model -->
### Bug report

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. a[i:j:k] = array() with k != 1 deletes the slice instead of raising ValueError like list

Assigning an empty array to an extended slice (step other than 1) of an array.array silently deletes the selected items: a = array('b', [1, 2, 3, 4, 5]); a[::2] = array('b') -> array('b', [2, 4]). The documented rule (Doc/library/stdtypes.rst note (1): "If k is not equal to 1, t must have the same length as the slice it is replacing") and list behave differently: l = [1, 2, 3, 4, 5]; l[::2] = [] -> ValueError: attempt to assign sequence of size 0 to extended slice of size 3. A non-empty right-hand side of the wrong length does raise ValueError for arrays too (a[::2] = array('b', [9]) -> "attempt to assign array of size 1 to extended slice of size 3"), so only the empty case is special. bytearray has the same code shape and the same behaviour (b[::2] = b'' deletes).

*May be intended:* Possibly an old deliberate shortcut: the branch is commented "Delete slice" and shares the deletion loop with `del a[i:j:k]`. But it contradicts the documented rule and the list type, which the array docs say arrays "behave very much like". A maintainer might fix it (raise ValueError when needed == 0 and slicelength != 0 for step != 1, in array and bytearray) or decide it is not worth a behaviour change; either way the inconsistency is undocumented.

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
if list(a) == [2, 4] and lr.startswith('ValueError') and ar.startswith('ValueError'):
    print("Observed the reported behavior.")
```

</details>

#### 2. array.fromfile() raises ValueError and inserts nothing when the file ends inside an item, though the docs promise EOFError with the available items inserted

fromfile(f, n) reads n * itemsize bytes and hands whatever read() returned to frombytes (Modules/arraymodule.c:1778). When the file ends in the middle of an item, read() returns a length that is not a multiple of the item size, frombytes raises ValueError("bytes length not a multiple of item size") (:1924-1929), and fromfile returns before its EOFError check (:1783-1788). So for a file holding 6 bytes, array('i').fromfile(f, 2) raises ValueError and the array stays empty, while the whole item that was available is lost and the 6 bytes are consumed from the file. With 4 bytes the same call raises EOFError and inserts the item, as documented. Python 2 truncated the partial item and inserted the whole ones. The same check uses `!=` (:1776), so a read() that returns more bytes than asked appends all of them and then raises EOFError("read() didn't return enough bytes").

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
if exc == 'ValueError' and len(a) == 0 and f.tell() == 6 and exc2 == 'EOFError' and list(b) == [1]:
    print("Observed the reported behavior.")
```

</details>

#### 3. array._array_reconstructor rejects odd-length unicode arrays in the other byte order: mformat_descriptors has UTF sizes 4 and 8

mformat_descriptors lists the UTF-16 machine formats with size 4 and the UTF-32 ones with size 8, while the units are 2 and 4 bytes. The reconstructor's slow path checks `Py_SIZE(items) % mf_descr.size`, so a pickle of a 'w' array with an odd number of characters from a machine of the other byte order fails with ValueError: string length not a multiple of item size. Even lengths work, and so does the native format, which takes the fast path. The same holds for UTF-16 with 'u' pickles.

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
if err == 'string length not a multiple of item size' and ok.tounicode() == 'ab':
    print("Observed the reported behavior.")
```

</details>

#### 4. array('w').tounicode() and repr() drop a leading U+FEFF and raise UnicodeDecodeError on surrogates, because they decode UTF-32 with byteorder 0

array('w', s).tounicode() should give s back, and the docs say it does. It calls PyUnicode_DecodeUTF32 with byteorder = 0, which is the "detect a byte order mark" mode, not native order. So array('w', '\ufeffabc').tounicode() is 'abc', and repr shows array('w', 'abc'), which is a different array. Storing a mark in the other byte order with frombytes reinterprets everything after it. Surrogates, which str allows and 'w' stores, raise UnicodeDecodeError, from repr too, so such an array cannot be printed. The deprecated 'u' typecode has none of these problems, as it uses PyUnicode_FromWideChar.

*May be intended:* The comment says `// native byteorder`, and PyUnicode_DecodeUTF32's convention is that *byteorder == 0 means detect, native being the fallback. The caller's intent was a plain native decoding, so the mark is not intended. Refusing surrogates could be defended as strictness, but it makes repr fail, and 'u' accepts them.

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
if t == 'abc' and len(a) == 4 and err == 'UnicodeDecodeError':
    print("Observed the reported behavior.")
```

</details>

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
AI tools (Claude and Codex) helped investigate the findings and prepare this report. The examples were rerun on CPython 3.15.2 and main, and the report received technical review. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
