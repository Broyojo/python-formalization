<!-- title: Small inconsistencies in bytes, bytearray and memoryview found by a formal model -->
### Bug report

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. bytearray(str, encoding) with a Python codec installs the encoded bytes over what the codec did to self: a leak, and storage replaced under an export

Since gh-139871 (3.15), bytearray___init___impl takes a uniquely referenced result of the codec as its storage: `self->ob_bytes_object = encoded; bytearray_reinit_from_bytes(self, size)` (:1031-1038). The checks for exports and the empty state are made before the codec runs (:993-1002), but a codec written in Python (codecs.register) runs while `self` is reachable. If it adds to `self`, the old ob_bytes_object is overwritten without a Py_DECREF, so its memory leaks and the bytes the codec added are dropped; if it keeps memoryview(self), the storage is replaced under the export (writes through the view no longer reach the object). When the codec keeps a reference to its result the other path, bytearray_iconcat (:1040), runs: it appends after the codec's bytes, and refuses with BufferError while the view exists. So the result depends on the reference count of an object the codec returned. The two paths leave different objects: with `self.resize(2)` in the codec the unique path gives b"hi" and the shared one b"\x00\x00hi"; with a kept view the unique path succeeds with ob_exports 1 and the shared one raises BufferError.

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
if res[True] == 5 and res[False] == 1005 and grown > 1000000 and bytes(ba) == b"hello":
    print("Observed the reported behavior.")
```

</details>

#### 2. An exhausted reversed(list) iterator keeps the list alive, unlike iter(list)

list iterators release their list when exhausted, and the field says so: `it_seq` is "Set to NULL when iterator is exhausted" (listobject.c:4154). reversed(l) does not do this on normal exhaustion. Yielding the item at index 0 stores it_index = -1, and the next call then returns at the early `if (index < 0) return NULL;` (:4248), so the code that clears it_seq (:4259-4263) never runs. That code is reached only when the list has shrunk below the index. An exhausted reversed iterator therefore holds a strong reference to the list for as long as the iterator lives, however many more times next() is called. iter(l), iter(t) and the generic reversed(seq) all release theirs.

*May be intended:* Not intended, as far as the source shows: it contradicts the comment on the field and the behaviour of the forward iterator, and 3.12 cleared it_seq on this path. The early return looks like a side effect of the free-threading rewrite, which leaves it_seq set under Py_GIL_DISABLED on purpose. What the default build gains from skipping the clear is not apparent.

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
if rev and not fwd:
    print("Observed the reported behavior.")
```

</details>

#### 3. m.__buffer__(flags) without PyBUF_FORMAT gives a view with format 'B' and the old itemsize, whose items are wrong

memory_getbuf without PyBUF_FORMAT sets view->format = NULL and keeps view->itemsize (its comment says the equality calcsize(format) = itemsize does not hold from there on). That is fine for a consumer that treats the buffer as bytes. But _PyMemoryView_FromBufferProc then builds a new memoryview from it, and init_shared_values fills in format "B" next to the old itemsize: a = array('i', [256, 2, 3]) y = memoryview(a).__buffer__(0) y.format, y.itemsize, y.shape, y.nbytes # 'B', 4, (3,), 12 y.tolist() # [0, 2, 3] struct.calcsize(y.format) == y.itemsize # False The view reads one byte every four, so 256 comes back as 0, and y != memoryview(a). memoryview._from_flags(a, 0) (the private route, used for buffer flags in PEP 688) does the same.

*May be intended:* Partly. The comment in memory_getbuf knows the invariant breaks for C consumers. The result of turning such a Py_buffer back into a memoryview looks unconsidered: a maintainer might set itemsize to 1 and rebuild shape, or say that __buffer__(0) has no format promise.

<details><summary>Reproducer</summary>

```python
import struct
from array import array
a = array('i', [256, 2, 3])
y = memoryview(a).__buffer__(0)
print(y.format, y.itemsize, y.shape, y.nbytes, y.tolist())
print(memoryview._from_flags(a, 0).tolist())
if y.format == 'B' and y.itemsize == 4 and struct.calcsize(y.format) != y.itemsize and y.tolist() == [0, 2, 3]:
    print("Observed the reported behavior.")
```

</details>

#### 4. An empty memoryview slice with a step is reported non-contiguous, so cast, join and hashlib reject it

init_flags uses a fast test for 1-D views, MV_CONTIGUOUS_NDIM1: shape[0] == 1 or strides[0] == itemsize. For an empty view with a step it says no, while PyBuffer_IsContiguous, which tests "len == 0" first, says yes: m = memoryview(b'abc') m[1:1].contiguous, m[1:1:2].contiguous # True, False _testbuffer.is_contiguous(m[1:1:2], 'C') # True m[1:1].cast('B') # works m[1:1:2].cast('B') # TypeError b''.join([m[1:1:2]]) # TypeError hashlib.sha256(m[1:1:2]) # BufferError Two-dimensional empty views go through PyBuffer_IsContiguous and are contiguous, so the same question has two answers depending on ndim.

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
if m[1:1].contiguous and not m[1:1:2].contiguous and attempt(lambda: m[1:1:2].cast('B').nbytes) == 'TypeError':
    print("Observed the reported behavior.")
```

</details>

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
AI tools (Claude and Codex) helped investigate the findings and prepare this report. The examples were rerun on CPython 3.15.2 and main, and the report received technical review. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
