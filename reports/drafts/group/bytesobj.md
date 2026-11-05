<!-- title: bytesobj: 16 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. bytearray().__buffer__(inspect.BufferFlags.READ) raises SystemError (bad argument to internal function)

inspect.BufferFlags is documented as "the flags that can be passed to the __buffer__ method" and has the
members READ (0x100) and WRITE (0x200). bytearray_getbuffer_lock_held (Objects/bytearrayobject.c:69-86)
passes the request flags to PyBuffer_FillInfo (:81), which treats flags == PyBUF_READ or PyBUF_WRITE as a
misuse by C code and calls PyErr_BadInternalCall (Objects/abstract.c:784-786). Python code calling
bytearray(b"ab").__buffer__(inspect.BufferFlags.READ) therefore gets
SystemError: Objects/abstract.c:785: bad argument to internal function. bytes.__buffer__ fails the same
way (bytes_buffer_getbuffer also goes through PyBuffer_FillInfo); memoryview(b"ab").__buffer__ of the same
flags succeeds. A SystemError is the exception of an interpreter-internal error and should not be
reachable from a documented call.
Lean: BufferFlagsNoSystemError (no flag of inspect.BufferFlags makes a bytearray buffer request fail with
SystemError) is refuted at flags = 0x100 (bufferFlagsNoSystemError_refuted), through baGetBufferC, the
model of bytearray_getbuffer_lock_held with PyBuffer_FillInfo.

<details><summary>Reproducer</summary>

```python
import inspect
got = {}
for name, obj in [("bytearray", bytearray(b"ab")), ("bytes", b"ab"), ("memoryview", memoryview(b"ab"))]:
    for flag in (inspect.BufferFlags.READ, inspect.BufferFlags.WRITE):
        try:
            obj.__buffer__(flag)
            got[(name, flag.name)] = "ok"
        except Exception as e:
            got[(name, flag.name)] = "%s: %s" % (type(e).__name__, e)
for k, v in got.items():
    print(k, v)
r = got[("bytearray", "READ")]
```

</details>

#### 2. b += b raises BufferError for a bytearray, while b.extend(b) and b[len(b):] = b work

bytearray_iconcat_lock_held takes the buffer of its argument (:407) and then resizes self (:419). When the
argument is self, the buffer is an export of self, so bytearray_resize_lock_held refuses with
"Existing exports of data: object cannot be re-sized". bytearray_setslice copies a self argument first
(:697-707), and so does bytearray_ass_subscript (:848-862), so b.extend(b) and b[len(b):] = b double the
object. Only a non-empty bytearray fails: for an empty one the resize is to the same size, which
bytearray_resize_lock_held accepts before its export check (:287-289). The documentation describes s += t as extending s with the contents of t.
Lean: IAddIsExtend (b += x is b.extend(x) for every bytes-like x) is refuted on b = bytearray(b"a"),
x = b (iadd_self).

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

#### 3. bytearray(str, encoding) with a Python codec installs the encoded bytes over what the codec did to self: a leak, and storage replaced under an export

Since gh-139871 (3.15), bytearray___init___impl takes a uniquely referenced result of the codec as its
storage: `self->ob_bytes_object = encoded; bytearray_reinit_from_bytes(self, size)` (:1031-1038). The
checks for exports and the empty state are made before the codec runs (:993-1002), but a codec written in
Python (codecs.register) runs while `self` is reachable. If it adds to `self`, the old ob_bytes_object is
overwritten without a Py_DECREF, so its memory leaks and the bytes the codec added are dropped; if it
keeps memoryview(self), the storage is replaced under the export (writes through the view no longer
reach the object). When the codec keeps a reference to its result the other path, bytearray_iconcat
(:1040), runs: it appends after the codec's bytes, and refuses with BufferError while the view exists.
So the result depends on the reference count of an object the codec returned.
Lean: InitPathsAgree (the two paths leave the same object) is refuted: with `self.resize(2)` in the
codec the unique path gives b"hi" and the shared one b"\x00\x00hi" (init_steal_drops); with a kept view
the unique path succeeds with ob_exports 1 and the shared one raises BufferError (init_steal_exported).

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

#### 4. del b[:k] whose shrinking realloc fails leaves ob_start before the buffer: MemoryError, then out-of-bounds reads and writes

A front deletion that drops below half the allocation goes through bytearray_setslice_linear with
lo == 0: it advances ob_start by the deleted count, then bytearray_resize_lock_held takes the major
downsize and calls bytearray_resize_storage. That function moves the data to ob_bytes and sets
ob_start = ob_bytes before _PyBytes_ResizeKeepOnError. If the resize fails, the failure path of
bytearray_setslice_linear undoes the advance with ob_start += growth, written for an ob_start that
had not moved. ob_start is now k bytes before the allocation and Py_SIZE is the old size, so every
later read or write of the object is out of bounds. On the way, the "move remaining bytes" memmove
reads k bytes past the logical end of the data.
Lean: ShrinkFailureKeepsLayout, the BA.WF invariant after that failure, is refuted.

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

#### 5. Docs say PyByteArray_Size checks for a NULL pointer; the body only asserts, so NULL crashes a release build

Doc/c-api/bytearray.rst:76-78 says PyByteArray_Size "Return[s] the size of bytearray after checking for a
NULL pointer" (the entry for PyByteArray_AsString, :81-84, says the same). The body,
Objects/bytearrayobject.c:208-215, is `assert(self != NULL); assert(PyByteArray_Check(self)); return
PyByteArray_GET_SIZE(self);`: there is no check in a release build, and PyByteArray_Size(NULL)
dereferences NULL (SIGSEGV on 3.15.2 and on main). The wording looks like it was written for an earlier
implementation; either the doc or the code should change.
Lean: SizeChecksNull (NULL gives an error rather than undefined behaviour) is refuted on baSizeC, the
model of PyByteArray_Size on a possibly NULL pointer (sizeChecksNull_refuted).

<details><summary>Reproducer</summary>

```python
import subprocess, sys
child = r'''
import ctypes
f = ctypes.pythonapi.PyByteArray_Size
f.argtypes = [ctypes.c_void_p]
f.restype = ctypes.c_ssize_t
try:
    r = f(None)
    print("returned", r, flush=True)
except Exception as e:
    print("raised", type(e).__name__, e, flush=True)
'''
p = subprocess.run([sys.executable, "-c", child], capture_output=True, text=True)
print("child output:", p.stdout.strip(), "| returncode:", p.returncode)
```

</details>

#### 6. x in b replaces an exception raised by x.__index__ with 'a bytes-like object is required'

_Py_bytes_contains calls PyNumber_AsSsize_t and, on any failure, clears the exception and tries the
buffer protocol. That is right for an object with no __index__, which is what the fallback is for.
But it also runs when __index__ exists and raises: the exception is lost and the caller sees
TypeError: a bytes-like object is required, not 'I'. The other search methods pass it on, because
parse_args_finds_byte tests _PyIndex_Check first and then returns the error, so b.find(x) raises the
original exception and x in b does not.
Lean: ContainsKeepsIndexError is refuted; IndexRaisesRules records each caller's behaviour.

<details><summary>Reproducer</summary>

```python
class I:
    def __index__(self):
        raise KeyError('boom')

def err(f):
    try:
        f()
    except Exception as e:
        return type(e).__name__

a = err(lambda: I() in b'abc')
b = err(lambda: b'abc'.find(I()))
print('in:', a, ' find:', b)
```

</details>

#### 7. b'%x' % n succeeds but b'%5x' % n raises 'string too large in _PyUnicode_FormatLong' once the text passes INT_MAX

printf-style formatting of an exact int takes one of two paths. With no width, precision, '+' or ' '
flag and a conversion other than X, _PyBytes_FormatEx calls _PyLong_FormatBytesWriter directly
(Objects/bytesobject.c:924-957); otherwise it goes through formatlong (:959-968), which calls
_PyUnicode_FormatLong. That function first builds PyNumber_ToBase(v, base) and refuses a result of
more than INT_MAX characters with ValueError('string too large in _PyUnicode_FormatLong')
(Objects/unicode_format.c:247-251), because the rest of it works in int. The fast path has no such
limit. So for an int whose hex text has 2**31 + 1 digits, b'%x' % v returns the 2 GiB result while
b'%5x' % v (a width of 5, which changes nothing in the output) raises ValueError. str % has the same
two paths (unicode_format.c:354-375) and the same split; format(v, '5x') succeeds.
Lean: FastSlowLong (fast path and formatlong agree for %d %i %u %o %x) is proven only under the
hypothesis that the text has at most INT_MAX bytes; FastSlowLongAll, the same without that
hypothesis, is refuted at v = 16 ** 2**31 (fastSlowLongAll_refuted).

<details><summary>Reproducer</summary>

```python
v = 1 << (4 * 2**31)          # 16 ** 2**31: 2**31 + 1 hex digits (a 1 GiB int)
got = {}
for name, f in [("b'%x' % v", lambda: b'%x' % v), ("b'%5x' % v", lambda: b'%5x' % v),
                ("'%x' % v", lambda: '%x' % v), ("'%5x' % v", lambda: '%5x' % v),
                ("format(v, '5x')", lambda: format(v, '5x'))]:
    try:
        r = f()
        got[name] = "ok, %d characters" % len(r)
        del r
    except ValueError as e:
        got[name] = "ValueError: %s" % e
for k, x in got.items():
    print(k, "->", x)
```

</details>

#### 8. list(x) raises MemoryError for an over-estimating __length_hint__, and overflows Py_ssize_t at sys.maxsize

list_extend_iter_lock_held allocates from PyObject_LengthHint before it iterates, and an allocation
failure ends the call. So an iterable that yields one item but reports a huge hint fails:
list(x) and [].extend(x) raise MemoryError for a hint of 2**60, sys.maxsize - 1 or sys.maxsize.
The outcome also depends on the list being extended, through the overflow test at :1317: with
hint sys.maxsize, [0].extend(x) succeeds where [].extend(x) raises, and with sys.maxsize - 1,
[0, 0].extend(x) succeeds where [0].extend(x) raises. Separately, at hint sys.maxsize
list_preallocate_exact computes `size + 1` on a Py_ssize_t (:230), which is signed overflow,
reachable from pure Python. The wrapped value then fails PyMem_New's size test, so the visible
result is the same MemoryError.
Lean: ListHintInert (any legal hint leaves extend succeeding) is refuted; ListExtendIterContents
(for a hint with len + hint + items <= sys.maxsize / 16 the contents are exact) and
ListHintIgnoredWhenOverflowing are proven.

<details><summary>Reproducer</summary>

```python
import sys
class X:
    def __init__(self, h):
        self.h = h
    def __iter__(self):
        return iter([1])
    def __length_hint__(self):
        return self.h
def outcome(f):
    try:
        f()
        return 'ok'
    except MemoryError:
        return 'MemoryError'
a = outcome(lambda: list(X(sys.maxsize)))
b = outcome(lambda: [].extend(X(sys.maxsize)))
c = outcome(lambda: [0].extend(X(sys.maxsize)))
print('list(x):', a, ' [].extend(x):', b, ' [0].extend(x):', c)
```

</details>

#### 9. An exhausted reversed(list) iterator keeps the list alive, unlike iter(list)

list iterators release their list when exhausted, and the field says so: `it_seq` is
"Set to NULL when iterator is exhausted" (listobject.c:4154). reversed(l) does not do this on
normal exhaustion. Yielding the item at index 0 stores it_index = -1, and the next call then
returns at the early `if (index < 0) return NULL;` (:4248), so the code that clears it_seq
(:4259-4263) never runs. That code is reached only when the list has shrunk below the index. An
exhausted reversed iterator therefore holds a strong reference to the list for as long as the
iterator lives, however many more times next() is called. iter(l), iter(t) and the generic
reversed(seq) all release theirs.
Lean: ListRevIterReleases is refuted; ListIterReleases (the forward iterator, for every list and
any number of next calls) is proven, and so is ListRevIterStops, the one path that does release.
The difftest compares gc.get_referents(it) against the model after next calls.

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

#### 10. list.__sizeof__() returns 32, less than an empty list, while the list is being sorted

While list.sort runs, list_sort_impl sets self->allocated to -1 (listobject.c:2994).
list___sizeof___impl then computes `(size_t)self->allocated * sizeof(PyObject *)` with no check
for that sentinel, which wraps: 40 + (2**64 - 1) * 8 modulo 2**64 is 32. So l.__sizeof__(), called
from a key function or a comparison during l.sort(), reports 32 bytes, which is less than the
40 bytes of an empty list and less than the object header. sys.getsizeof(l) is affected the same
way, since it adds to this value. The value is a wrong answer, not a crash, and the list itself
is unharmed.
Lean: ListSizeofBase (40 <= __sizeof__ in every state) is refuted at the sort state;
ListSizeofExact (outside sort, __sizeof__ is exactly 40 + 8 * allocated, with no wraparound) is
proven for every list satisfying the invariant.

<details><summary>Reproducer</summary>

```python
import sys
seen = []
l = [3, 2, 1]
l.sort(key=lambda x: (seen.append(l.__sizeof__()), x)[1])
empty = [].__sizeof__()
print('during sort:', seen[0], ' empty list:', empty)
```

</details>

#### 11. m.__buffer__(flags) without PyBUF_FORMAT gives a view with format 'B' and the old itemsize, whose items are wrong

memory_getbuf without PyBUF_FORMAT sets view->format = NULL and keeps view->itemsize (its comment
says the equality calcsize(format) = itemsize does not hold from there on). That is fine for a
consumer that treats the buffer as bytes. But _PyMemoryView_FromBufferProc then builds a new
memoryview from it, and init_shared_values fills in format "B" next to the old itemsize:
    a = array('i', [256, 2, 3])
    y = memoryview(a).__buffer__(0)
    y.format, y.itemsize, y.shape, y.nbytes     # 'B', 4, (3,), 12
    y.tolist()                                  # [0, 2, 3]
    struct.calcsize(y.format) == y.itemsize     # False
The view reads one byte every four, so 256 comes back as 0, and y != memoryview(a).
memoryview._from_flags(a, 0) (the private route, used for buffer flags in PEP 688) does the same.
Lean: BufferKeepsItemsize is refuted on a 1-item 'i' view.

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

#### 12. memoryview.cast accepts a format with an embedded NUL: 'B\\0anything' is taken for 'B'

memoryview.cast's format is a str, converted with PyUnicode_AsASCIIString, and then
get_native_fmtchar and get_native_fmtstr receive PyBytes_AS_STRING(asciifmt) as a C string. They
stop at the first NUL, so memoryview(b'ab').cast('B\0xyz') succeeds with format 'B', although the
documented rule is a single native character with an optional '@'. Every other malformed
format raises ValueError.
Lean: CastWholeFormat is refuted; NativeFormatAgree (the two format functions agree on every
string) is proven.

<details><summary>Reproducer</summary>

```python
m = memoryview(b'ab').cast('B\0xyz')
print(repr(m.format), m.itemsize)
try:
    memoryview(b'ab').cast('Bxyz')
    other = 'accepted'
except ValueError as e:
    other = 'ValueError'
print('without the NUL:', other)
```

</details>

#### 13. An empty memoryview slice with a step is reported non-contiguous, so cast, join and hashlib reject it

init_flags uses a fast test for 1-D views, MV_CONTIGUOUS_NDIM1: shape[0] == 1 or strides[0] ==
itemsize. For an empty view with a step it says no, while PyBuffer_IsContiguous, which tests
"len == 0" first, says yes:
    m = memoryview(b'abc')
    m[1:1].contiguous, m[1:1:2].contiguous            # True, False
    _testbuffer.is_contiguous(m[1:1:2], 'C')          # True
    m[1:1].cast('B')                                  # works
    m[1:1:2].cast('B')                                # TypeError
    b''.join([m[1:1:2]])                              # TypeError
    hashlib.sha256(m[1:1:2])                          # BufferError
Two-dimensional empty views go through PyBuffer_IsContiguous and are contiguous, so the same
question has two answers depending on ndim.
Lean: Ndim1ContigAgree is refuted; Ndim1ContigNonempty (the fast test agrees with the general
one for every non-empty 1-D view, in C and Fortran order) is proven.

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

#### 14. m[::k] with a huge step overflows Py_ssize_t in init_slice; m.strides reports a wrapped value

init_slice computes base->strides[dim] * step with no range check. For a step past
sys.maxsize / itemsize that is signed overflow: on a 64-bit build
    memoryview(bytes(16)).cast('q')[::sys.maxsize].strides    # (-8,)
where the product is 8 * (2**63 - 1). Such a slice has at most one item, so the wrong stride is
never used to reach memory, but it is visible in .strides, and it is undefined behaviour in C that
a -fsanitize=undefined build reports.
Lean: SliceStrideExact is refuted; SliceItems (every item of m[s] is at the address of item
range(*s.indices(n))[k] of m, for every slice) is proven with the same wrapping multiplication, so
the overflow cannot misdirect a read.

<details><summary>Reproducer</summary>

```python
import sys
m = memoryview(bytes(16)).cast('q')
s = m[::sys.maxsize]
print(s.shape, s.strides, s.tolist())
```

</details>

#### 15. bytes, tuple and str times a huge int change their OverflowError message once the BINARY_OP site is specialized

3.15 specializes sequence * int to BINARY_OP_EXTEND. Its helper seq_int_multiply converts the count
with PyLong_AsSsize_t, where the generic path, sequence_repeat, uses PyNumber_AsSsize_t(n,
PyExc_OverflowError). The guard only checks the two types, so an int outside Py_ssize_t reaches the
helper. The same expression then raises OverflowError("cannot fit 'int' into an index-sized integer")
while the site is cold and OverflowError("Python int too large to convert to C ssize_t") once it is
hot. list and bytearray have no such specialization and keep the first message.
Lean: SpecializedRepeatAgrees, the helper against bytesMul, is refuted at 2**63.

<details><summary>Reproducer</summary>

```python
def f(s, n):
    return s * n

def msg(s, n):
    try:
        f(s, n)
    except OverflowError as e:
        return str(e)

cold = msg(b'ab', 2 ** 63)
for _ in range(5000):
    f(b'ab', 2)
hot = msg(b'ab', 2 ** 63)
print('cold:', cold)
print('hot: ', hot)
```

</details>

#### 16. PyTuple_SetItem() and _PyTuple_Resize() keep a cached hash: a tuple hashed before the change keeps the old hash

Since tuple hashes are cached in ob_hash (gh-131525, PR 131529, 3.14), tuple_hash() returns the cached
value whenever ob_hash != -1 (tupleobject.c:376-379). PyTuple_SetItem() (:117-135) replaces an item of a
uniquely referenced tuple without resetting ob_hash, and _PyTuple_Resize() (:1045-1123) reallocates the
tuple in place without resetting it either. So C code that hashes a refcount-1 tuple and then stores a
different item gets a tuple that compares equal to (2,) but hashes like (1,): `t in {(2,)}` is False and
a dict keyed by (2,) does not find it. Same for a resize: (1, 2) hashed, then resized to one item, still
hashes as (1, 2).
Lean: TupleSetItemHashFresh (after SetItem, hash agrees with a fresh tuple of the same items) is refuted
with the reproducer's tuple; CApiTupleObj states the kept ob_hash of both functions as proven behaviour.

<details><summary>Reproducer</summary>

```python
import importlib.machinery, importlib.util, os, subprocess, sys, sysconfig, tempfile
SRC = r'''
#include <Python.h>
static PyObject *
probe(PyObject *self, PyObject *noargs)
{
    PyObject *t = PyTuple_New(1);
    if (t == NULL) return NULL;
    if (PyTuple_SetItem(t, 0, PyLong_FromLong(1)) < 0) return NULL;
    Py_hash_t h1 = PyObject_Hash(t);
    if (PyTuple_SetItem(t, 0, PyLong_FromLong(2)) < 0) { Py_DECREF(t); return NULL; }
    Py_hash_t h2 = PyObject_Hash(t);
    return Py_BuildValue("nnN", (Py_ssize_t)h1, (Py_ssize_t)h2, t);
}
static PyObject *
probe_resize(PyObject *self, PyObject *noargs)
{
    PyObject *t = PyTuple_New(2);
    if (t == NULL) return NULL;
    PyTuple_SetItem(t, 0, PyLong_FromLong(1));
    PyTuple_SetItem(t, 1, PyLong_FromLong(2));
    Py_hash_t h1 = PyObject_Hash(t);
    if (_PyTuple_Resize(&t, 1) < 0) return NULL;
    Py_hash_t h2 = PyObject_Hash(t);
    return Py_BuildValue("nnN", (Py_ssize_t)h1, (Py_ssize_t)h2, t);
}
static PyMethodDef methods[] = {{"probe", probe, METH_NOARGS, NULL},
  {"probe_resize", probe_resize, METH_NOARGS, NULL}, {NULL}};
static struct PyModuleDef mod = {PyModuleDef_HEAD_INIT, "_th_probe", NULL, -1, methods};
PyMODINIT_FUNC PyInit__th_probe(void) { return PyModule_Create(&mod); }
'''
d = tempfile.mkdtemp()
src = os.path.join(d, "thp.c")
out = os.path.join(d, "_th_probe" + importlib.machinery.EXTENSION_SUFFIXES[0])
open(src, "w").write(SRC)
cc = (sysconfig.get_config_var("CC") or "cc").split()
incs = {sysconfig.get_paths()["include"], os.path.dirname(sysconfig.get_config_h_filename())}
link = ["-bundle", "-undefined", "dynamic_lookup"] if sys.platform == "darwin" else ["-shared", "-fPIC"]
subprocess.run(cc + [f"-I{i}" for i in incs] + link + [src, "-o", out], check=True)
spec = importlib.util.spec_from_file_location("_th_probe", out)
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
print(sys.version)
h1, h2, t = m.probe()
print("SetItem: hash((1,)) =", hash((1,)), " h1 =", h1, " after SetItem t =", t, " h2 =", h2, " hash((2,)) =", hash((2,)))
print("  t == (2,):", t == (2,), " hash(t) == hash((2,)):", hash(t) == hash((2,)),
      " {(2,): 'v'}.get(t):", {(2,): 'v'}.get(t), " t in {(2,)}:", t in {(2,)})
r1, r2, r = m.probe_resize()
print("Resize: hash((1,2)) =", hash((1, 2)), " r1 =", r1, " after resize r =", r, " r2 =", r2, " hash((1,)) =", hash((1,)))
print("  {(1,): 'v'}.get(r):", {(1,): 'v'}.get(r))
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
