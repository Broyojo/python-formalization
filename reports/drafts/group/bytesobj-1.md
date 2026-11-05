<!-- title: Small inconsistencies in bytes, bytearray and memoryview found by a formal model -->
### Bug report

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. b += b raises BufferError for a bytearray, while b.extend(b) and b[len(b):] = b work

bytearray_iconcat_lock_held takes the buffer of its argument (:407) and then resizes self (:419). When the argument is self, the buffer is an export of self, so bytearray_resize_lock_held refuses with "Existing exports of data: object cannot be re-sized". bytearray_setslice copies a self argument first (:697-707), and so does bytearray_ass_subscript (:848-862), so b.extend(b) and b[len(b):] = b double the object. Only a non-empty bytearray fails: for an empty one the resize is to the same size, which bytearray_resize_lock_held accepts before its export check (:287-289). The documentation describes s += t as extending s with the contents of t. Lean: IAddIsExtend (b += x is b.extend(x) for every bytes-like x) is refuted on b = bytearray(b"a"), x = b (iadd_self).

*May be intended:* Possibly tolerated: the error has been there since the export check existed, and an open issue mentions it.

<details><summary>Reproducer</summary>

```python
b = bytearray(b"a")
try:
    b += b
    r = None
except BufferError as e:
    r = str(e)
c = bytearray(b"a")
c.extend(c)
print("b += b:", r, "/ c.extend(c):", c)
```

</details>

#### 2. bytearray(str, encoding) with a Python codec installs the encoded bytes over what the codec did to self: a leak, and storage replaced under an export

Since gh-139871 (3.15), bytearray___init___impl takes a uniquely referenced result of the codec as its storage: `self->ob_bytes_object = encoded; bytearray_reinit_from_bytes(self, size)` (:1031-1038). The checks for exports and the empty state are made before the codec runs (:993-1002), but a codec written in Python (codecs.register) runs while `self` is reachable. If it adds to `self`, the old ob_bytes_object is overwritten without a Py_DECREF, so its memory leaks and the bytes the codec added are dropped; if it keeps memoryview(self), the storage is replaced under the export (writes through the view no longer reach the object). When the codec keeps a reference to its result the other path, bytearray_iconcat (:1040), runs: it appends after the codec's bytes, and refuses with BufferError while the view exists. So the result depends on the reference count of an object the codec returned. Lean: InitPathsAgree (the two paths leave the same object) is refuted: with `self.resize(2)` in the codec the unique path gives b"hi" and the shared one b"\x00\x00hi" (init_steal_drops); with a kept view the unique path succeeds with ob_exports 1 and the shared one raises BufferError (init_steal_exported).

<details><summary>Reproducer</summary>

```python
import codecs, tracemalloc
T = [None]; V = []; MODE = {"unique": True, "export": False}; KEEP = []
def enc(s, errors="strict"):
    T[0].extend(b"Q" * 1000)
    if MODE["export"]:
        V.append(memoryview(T[0]))
    r = bytes(bytearray(s.encode("ascii")))
    if not MODE["unique"]:
        KEEP.append(r)
    return (r, len(s))
codecs.register(lambda n: codecs.CodecInfo(enc, lambda b, e="strict": (str(b, "ascii"), len(b)), name="steal")
                if n == "steal" else None)
res = {}
for unique in (True, False):
    MODE["unique"] = unique
    ba = bytearray(); T[0] = ba
    ba.__init__("hello", "steal")
    res[unique] = len(ba)
print("unique result: len", res[True], "/ shared result: len", res[False])
MODE["unique"] = True
tracemalloc.start()
ba = bytearray(); T[0] = ba
before = tracemalloc.get_traced_memory()[0]
for _ in range(2000):
    ba.__init__("hello", "steal")
grown = tracemalloc.get_traced_memory()[0] - before
print("traced memory grew by", grown)
MODE["export"] = True
ba = bytearray(); T[0] = ba
ba.__init__("hello", "steal")
V[-1][0] = ord("Z")
print("exported: ba", bytes(ba), "view", bytes(V[-1][:3]))
```

</details>

#### 3. del b[:k] whose shrinking realloc fails leaves ob_start before the buffer: MemoryError, then out-of-bounds reads and writes

A front deletion that drops below half the allocation goes through bytearray_setslice_linear with lo == 0: it advances ob_start by the deleted count, then bytearray_resize_lock_held takes the major downsize and calls bytearray_resize_storage. That function moves the data to ob_bytes and sets ob_start = ob_bytes before _PyBytes_ResizeKeepOnError. If the resize fails, the failure path of bytearray_setslice_linear undoes the advance with ob_start += growth, written for an ob_start that had not moved. ob_start is now k bytes before the allocation and Py_SIZE is the old size, so every later read or write of the object is out of bounds. On the way, the "move remaining bytes" memmove reads k bytes past the logical end of the data. Lean: ShrinkFailureKeepsLayout, the BA.WF invariant after that failure, is refuted.

<details><summary>Reproducer</summary>

```python
import _testcapi
found = False
for fail_at in range(0, 6):
    b = bytearray(b'A' * 2000)
    try:
        _testcapi.set_nomemory(fail_at, fail_at + 1)
        del b[:1500]
    except MemoryError:
        _testcapi.remove_mem_hooks()
        data = bytes(b)
        print('fail_at', fail_at, 'len', len(b), 'bytes that are still A:', data.count(b'A'))
        found = found or (len(b) == 2000 and data != b'A' * 2000)
    finally:
        _testcapi.remove_mem_hooks()
```

</details>

#### 4. An exhausted reversed(list) iterator keeps the list alive, unlike iter(list)

list iterators release their list when exhausted, and the field says so: `it_seq` is "Set to NULL when iterator is exhausted" (listobject.c:4154). reversed(l) does not do this on normal exhaustion. Yielding the item at index 0 stores it_index = -1, and the next call then returns at the early `if (index < 0) return NULL;` (:4248), so the code that clears it_seq (:4259-4263) never runs. That code is reached only when the list has shrunk below the index. An exhausted reversed iterator therefore holds a strong reference to the list for as long as the iterator lives, however many more times next() is called. iter(l), iter(t) and the generic reversed(seq) all release theirs. Lean: ListRevIterReleases is refuted; ListIterReleases (the forward iterator, for every list and any number of next calls) is proven, and so is ListRevIterStops, the one path that does release. The difftest compares gc.get_referents(it) against the model after next calls.

<details><summary>Reproducer</summary>

```python
import gc
import weakref
class L(list):
    pass
def still_alive(make):
    l = L([1, 2, 3])
    r = weakref.ref(l)
    it = make(l)
    for _ in it:
        pass
    next(it, None)
    del l
    gc.collect()
    return r() is not None
rev = still_alive(reversed)
fwd = still_alive(iter)
print('reversed(l) keeps the list after exhaustion:', rev)
print('iter(l) keeps the list after exhaustion:', fwd)
```

</details>

#### 5. m.__buffer__(flags) without PyBUF_FORMAT gives a view with format 'B' and the old itemsize, whose items are wrong

memory_getbuf without PyBUF_FORMAT sets view->format = NULL and keeps view->itemsize (its comment says the equality calcsize(format) = itemsize does not hold from there on). That is fine for a consumer that treats the buffer as bytes. But _PyMemoryView_FromBufferProc then builds a new memoryview from it, and init_shared_values fills in format "B" next to the old itemsize: a = array('i', [256, 2, 3]) y = memoryview(a).__buffer__(0) y.format, y.itemsize, y.shape, y.nbytes # 'B', 4, (3,), 12 y.tolist() # [0, 2, 3] struct.calcsize(y.format) == y.itemsize # False The view reads one byte every four, so 256 comes back as 0, and y != memoryview(a). memoryview._from_flags(a, 0) (the private route, used for buffer flags in PEP 688) does the same. Lean: BufferKeepsItemsize is refuted on a 1-item 'i' view.

<details><summary>Reproducer</summary>

```python
import struct
from array import array
a = array('i', [256, 2, 3])
y = memoryview(a).__buffer__(0)
print(y.format, y.itemsize, y.shape, y.nbytes, y.tolist())
print(memoryview._from_flags(a, 0).tolist())
```

</details>

#### 6. An empty memoryview slice with a step is reported non-contiguous, so cast, join and hashlib reject it

init_flags uses a fast test for 1-D views, MV_CONTIGUOUS_NDIM1: shape[0] == 1 or strides[0] == itemsize. For an empty view with a step it says no, while PyBuffer_IsContiguous, which tests "len == 0" first, says yes: m = memoryview(b'abc') m[1:1].contiguous, m[1:1:2].contiguous # True, False _testbuffer.is_contiguous(m[1:1:2], 'C') # True m[1:1].cast('B') # works m[1:1:2].cast('B') # TypeError b''.join([m[1:1:2]]) # TypeError hashlib.sha256(m[1:1:2]) # BufferError Two-dimensional empty views go through PyBuffer_IsContiguous and are contiguous, so the same question has two answers depending on ndim. Lean: Ndim1ContigAgree is refuted; Ndim1ContigNonempty (the fast test agrees with the general one for every non-empty 1-D view, in C and Fortran order) is proven.

<details><summary>Reproducer</summary>

```python
m = memoryview(b'abc')
def attempt(f):
    try:
        return repr(f())
    except Exception as e:
        return type(e).__name__
print('contiguous', m[1:1].contiguous, m[1:1:2].contiguous)
print('cast', attempt(lambda: m[1:1].cast('B').nbytes), attempt(lambda: m[1:1:2].cast('B').nbytes))
print('join', attempt(lambda: b''.join([m[1:1]])), attempt(lambda: b''.join([m[1:1:2]])))
```

</details>

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
I used AI tools (Claude) to find these and draft the report; each case was reproduced on 3.15.2 and on main and the text checked before filing. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
