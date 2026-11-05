<!-- title: typeobj: 13 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. PyObject_CopyData compares only total byte lengths, then walks the source's indices over the destination: wrong data, and writes outside the destination view, when the shapes differ

The only size check in `PyObject_CopyData` is `view_dest.len < view_src.len`
(abstract.c:690). If both views are contiguous in one order it does a memcpy, which is
fine. Otherwise it walks an index vector over `view_src.shape` and hands the same vector to
`PyBuffer_GetPointer` for the destination (abstract.c:727-732). Nothing checks that the two
views have the same ndim or shape, so:

<details><summary>Reproducer</summary>

```python
import ctypes
import _testbuffer as tb
api = ctypes.pythonapi
api.PyObject_CopyData.argtypes = [ctypes.py_object, ctypes.py_object]
api.PyObject_CopyData.restype = ctypes.c_int
class Py_buffer(ctypes.Structure):
    _fields_ = [("buf", ctypes.c_void_p), ("obj", ctypes.c_void_p),
                ("len", ctypes.c_ssize_t), ("itemsize", ctypes.c_ssize_t),
                ("readonly", ctypes.c_int), ("ndim", ctypes.c_int),
                ("format", ctypes.c_char_p), ("shape", ctypes.c_void_p),
                ("strides", ctypes.c_void_p), ("suboffsets", ctypes.c_void_p),
                ("internal", ctypes.c_void_p)]
api.PyObject_GetBuffer.argtypes = [ctypes.py_object, ctypes.POINTER(Py_buffer), ctypes.c_int]
api.PyObject_GetBuffer.restype = ctypes.c_int
api.PyBuffer_Release.argtypes = [ctypes.POINTER(Py_buffer)]
api.PyBuffer_Release.restype = None
# A 3x2 Fortran-ordered view of a 32-byte block, so offsets past the view are still ours.
dest = tb.ndarray([0] * 32, shape=[3, 2], strides=[1, 3], format='B', flags=tb.ND_WRITABLE)
src = tb.ndarray(list(b'abcdef'), shape=[2, 3], format='B')
view = Py_buffer()
assert api.PyObject_GetBuffer(dest, ctypes.byref(view), 0x11d) == 0
in_view = {i + 3 * j for i in range(3) for j in range(2)}
rc = api.PyObject_CopyData(dest, src)
after = ctypes.string_at(view.buf, 32)
api.PyBuffer_Release(ctypes.byref(view))
written = {i for i in range(32) if after[i]}
print('dest', dest.nbytes, 'bytes, src', src.nbytes, 'bytes, rc', rc)
print('view offsets', sorted(in_view), 'written', sorted(written))
```

</details>

#### 2. A note added in an except* handler is lost on re-raise: is_same_exception_metadata compares an unused field

`_PyExc_PrepReraiseStar` tells a re-raised subgroup from a newly raised exception with
`is_same_exception_metadata`, which compares `notes`, `traceback`, `cause` and `context` of
the two objects. `notes` there is the C field `PyBaseExceptionObject.notes`, which nothing
writes: `add_note` stores `__notes__` as an ordinary instance attribute. The comparison is
always NULL with NULL.

<details><summary>Reproducer</summary>

```python
try:
    try:
        raise ExceptionGroup('g', [ValueError(1), TypeError(2)])
    except* ValueError as e:
        e.add_note('while loading config')
        raise
except ExceptionGroup as x:
    got = [getattr(x, '__notes__', None)] + [getattr(s, '__notes__', None) for s in x.exceptions]
    print(repr(x), got)
    plain = None
    try:
        try:
            raise ValueError(1)
        except ValueError as e:
            e.add_note('while loading config')
            raise
    except ValueError as y:
        plain = y.__notes__
    print('except keeps', plain)
```

</details>

#### 3. MemoryError freelist keeps __suppress_context__ from the previous object and drops __new__ arguments

`MemoryError` objects are recycled through a freelist of 16. `MemoryError_dealloc` runs
`BaseException_clear`, which clears the references but not the flag `suppress_context`, and
`get_memory_error` sets `dict` and `args` on the way out and nothing else. So the flag of a
dead `MemoryError` shows up on the next one:

<details><summary>Reproducer</summary>

```python
e = MemoryError()
e.__cause__ = None
del e
f = MemoryError()
flag = f.__suppress_context__
args = MemoryError.__new__(MemoryError, 'x').args
class M(MemoryError): pass
sub = M.__new__(M, 'x').args
print(flag, args, sub, BaseException.__new__(BaseException, 'x').args)
```

</details>

#### 4. NameError.name is lost by pickle and copy, unlike AttributeError.name and ImportError.name

`NameError` gained a keyword-only `name` in 3.10. `NameError` has no `__reduce__`, so
`BaseException.__reduce__` is used, which carries `args` and the instance dict, and `name`
is a C member:

<details><summary>Reproducer</summary>

```python
import copy, pickle
rows = [(c, pickle.loads(pickle.dumps(c('x', name='y'))).name, copy.copy(c('x', name='y')).name)
        for c in (ImportError, AttributeError, NameError, UnboundLocalError)]
for r in rows:
    print(r)
```

</details>

#### 5. split() and subgroup() set __suppress_context__ on their results, which hides __context__ in tracebacks

`exceptiongroup_subset` copies the metadata of the original group to each part it builds:
traceback, context, cause and notes. It copies the cause with
`PyException_SetCause(eg, PyException_GetCause(orig))`, and `PyException_SetCause` always
sets `suppress_context`, also when the cause is NULL. So every group built by `split()`,
`subgroup()` or `except*` has `__suppress_context__ == True` whatever the original has, and
it keeps `__context__`, which the traceback printer then skips:

<details><summary>Reproducer</summary>

```python
import traceback
try:
    try:
        raise ValueError('ctx')
    except ValueError:
        raise ExceptionGroup('g', [TypeError(1), KeyError(2)])
except ExceptionGroup as e:
    m, r = e.split(TypeError)
    full = ''.join(traceback.format_exception(e))
    part = ''.join(traceback.format_exception(m))
    print('original', e.__suppress_context__, 'part', m.__suppress_context__, repr(m.__context__))
    print('context shown: original', 'ctx' in full, 'part', 'ctx' in part)
    if not e.__suppress_context__ and m.__suppress_context__ and m.__context__ is e.__context__ \
            and 'ctx' in full and 'ctx' not in part:
```

</details>

#### 6. x *= seq raises TypeError for instances of Python classes although x * seq works: the sq_repeat fallback in PyNumber_InPlaceMultiply tests tp_as_sequence, which every heap type has

`PyNumber_Multiply` repeats a sequence on either side: if the left operand has no
`sq_repeat`, it uses the right operand's (abstract.c:1173-1178), so `n * seq` works for any
`n` with `__index__`. `PyNumber_InPlaceMultiply` is meant to do the same, and its comment
says so ("the right hand operand should not be mutated in this case so sq_inplace_repeat
is not used"), but it writes the test as `if (mv != NULL) { ... } else if (mw != NULL)`
(abstract.c:1329, @3.14.7:1336). `mv` is `Py_TYPE(v)->tp_as_sequence`, and `type_new_alloc` sets
that pointer on every heap type (typeobject.c:4488). So for an instance of any Python
class, including a subclass of int, the right operand is never consulted:

<details><summary>Reproducer</summary>

```python
class Index:
    def __index__(self):
        return 2
class I(int):
    pass
print('Index() * [1] =', Index() * [1])
print('I(2) * [1] =', I(2) * [1])
n = 2
n *= [1]
print('2 *= [1] ->', n)
errors = []
for v in (Index(), I(2)):
    try:
        v *= [1]
    except TypeError as e:
        errors.append(str(e))
print(errors)
if (Index() * [1] == [1, 1] and I(2) * [1] == [1, 1] and n == [1, 1]
        and len(errors) == 2 and all("*=" in e for e in errors)):
```

</details>

#### 7. property subclass: .setter/.getter/.deleter drop an explicit doc=, because property_copy reads prop_doc, which __init__ leaves NULL for subclasses

`property_init_impl` stores the docstring in `prop_doc` only for exact `property`. For a
subclass it stores it in the instance `__dict__` instead (descrobject.c:1902-1933), so that
it is not shadowed by `__doc__` in the class dict, and `prop_doc` stays NULL.
`property_copy`, used by `.getter`, `.setter` and `.deleter`, still takes the doc from
`pold->prop_doc` (:1809), passes None, and the new object has no docstring:

<details><summary>Reproducer</summary>

```python
class P(property):
    pass
def setter(self, value):
    pass
plain = property(None, None, None, "doc")
sub = P(None, None, None, "doc")
print(plain.__doc__, plain.setter(setter).__doc__)
print(sub.__doc__, sub.setter(setter).__doc__)
if (sub.__doc__ == "doc" and plain.setter(setter).__doc__ == "doc"
        and sub.setter(setter).__doc__ is None):
```

</details>

#### 8. PyStructSequence_InitType2 frees tp_members after PyType_Ready has created the member descriptors, so a failure leaves the (immortal, sometimes ready) type with descriptors pointing at freed memory

`PyStructSequence_InitType2` (structseq.c:672-704) allocates `members`, stores it as
`type->tp_members` (`initialize_static_fields`, :592), and calls `initialize_static_type`
(:595-611), which runs `PyType_Ready` and then `initialize_structseq_dict`. If either fails,
:699-701 does `PyMem_Free(members)` and returns -1. But by then `PyType_Ready` has made the
type immutable and immortal (Objects/typeobject.c:9719-9724) and created a member descriptor
for every field, each holding a pointer into `members`; when the failure is in
`initialize_structseq_dict`, the type is also `Py_TPFLAGS_READY`. The type stays reachable
(it is the caller's static object, and it is in `tuple.__subclasses__()`), and every member
descriptor reads freed memory.

<details><summary>Reproducer</summary>

```python
import subprocess, sys
CODE = (
    "import ctypes, os, sys\n"
    "api = ctypes.pythonapi\n"
    "class Field(ctypes.Structure):\n"
    "    _fields_ = [('name', ctypes.c_char_p), ('doc', ctypes.c_char_p)]\n"
    "class Desc(ctypes.Structure):\n"
    "    _fields_ = [('name', ctypes.c_char_p), ('doc', ctypes.c_char_p),\n"
    "                ('fields', ctypes.POINTER(Field)), ('n_in_sequence', ctypes.c_int)]\n"
    "api.PyStructSequence_InitType2.restype = ctypes.c_int\n"
    "api.PyStructSequence_InitType2.argtypes = [ctypes.c_void_p, ctypes.POINTER(Desc)]\n"
    "fields = (Field * 3)((b'a', b'doc of a'), (b'b', b'doc of b'), (None, None))\n"
    "buf = ctypes.create_string_buffer(type.__basicsize__ + 64)\n"
    "d = Desc(b'm.S', None, fields, int(sys.argv[1]))\n"
    "try:\n"
    "    api.PyStructSequence_InitType2(ctypes.addressof(buf), ctypes.byref(d))\n"
    "    print('initialised', flush=True)\n"
    "except SystemError as e:\n"
    "    print('SystemError:', e, flush=True)\n"
    "T = ctypes.cast(ctypes.addressof(buf), ctypes.py_object).value\n"
    "print('ready:', bool(T.__flags__ & (1 << 12)), flush=True)\n"
    "descr = T.__dict__['a']\n"
    "print('descriptor:', descr, flush=True)\n"
    "print('doc:', repr(descr.__doc__), flush=True)\n"
    "os._exit(0)\n")
res = {}
for nseq in (1, -1, 7):
    r = subprocess.run([sys.executable, "-I", "-c", CODE, str(nseq)], capture_output=True, text=True, timeout=60)
    res[nseq] = (r.returncode, r.stdout)
    print(f"n_in_sequence = {nseq}: return code {r.returncode}: {r.stdout.strip()!r}")
ok_rc, ok_out = res[1]
bad_rc, bad_out = res[-1]
nr_rc, nr_out = res[7]
if (ok_rc == 0 and "doc: 'doc of a'" in ok_out and "SystemError" in bad_out
        and "ready: True" in bad_out and "descriptor:" in bad_out and "doc: 'doc of a'" not in bad_out
        and "tp_dictoffset that is too small" in nr_out and "ready: False" in nr_out
        and "descriptor:" in nr_out and "doc: 'doc of a'" not in nr_out):
```

</details>

#### 9. A negative n_fields, n_sequence_fields or n_unnamed_fields makes PyStructSequence_New, the constructor, __reduce__ and __replace__ return NULL with no exception set

`get_type_attr_as_size` (structseq.c:27-42) returns `PyLong_AsSsize_t(v)` of the int stored in
the type's dict. A stored negative int converts without an error. Every caller then tests
`if (n < 0) return NULL;` (:69, :73, :174, :178, :182, :357, :404), treating the negative
value as "an exception is set". None is, so:

<details><summary>Reproducer</summary>

```python
import copy, ctypes, os
T = os.terminal_size
t = T((1, 2))
errors = []
T.n_fields = -1
try:
    T((1, 2))
except SystemError as e:
    errors.append(str(e))
T.n_fields = 2
T.n_unnamed_fields = -1
for f in (t.__reduce__, lambda: copy.replace(t)):
    try:
        f()
    except SystemError as e:
        errors.append(str(e))
T.n_unnamed_fields = 0
api = ctypes.pythonapi
api.PyStructSequence_New.restype = ctypes.c_void_p
api.PyStructSequence_New.argtypes = [ctypes.py_object]
api.PyErr_Occurred.restype = ctypes.c_void_p
T.n_sequence_fields = -1
p = api.PyStructSequence_New(T)
occurred = api.PyErr_Occurred()
T.n_sequence_fields = 2
print(errors)
print("PyStructSequence_New returned", p, "with exception set:", occurred is not None)
if (len(errors) == 3 and all("without" in m and "exception" in m for m in errors)
        and p is None and occurred is None):
```

</details>

#### 10. PyStructSequence_NewType and PyStructSequence_InitType2 do not validate their desc: n_in_sequence = #fields + 4 (InitType2: + 1 to + 4) reads past the field array, unnamed hidden fields make __reduce__ and the constructor read tp_members[-1], and 2^29 hidden fields wrap NewType's tp_basicsize

`_PyStructSequence_NewType` (structseq.c:744-793) checks nothing about the desc it is given.
Three consequences, all from C (or ctypes), all one cause:

<details><summary>Reproducer</summary>

```python
import subprocess, sys
HELPER = (
    "import ctypes, sys\n"
    "api = ctypes.pythonapi\n"
    "class Field(ctypes.Structure):\n"
    "    _fields_ = [('name', ctypes.c_void_p), ('doc', ctypes.c_char_p)]\n"
    "class Desc(ctypes.Structure):\n"
    "    _fields_ = [('name', ctypes.c_char_p), ('doc', ctypes.c_char_p),\n"
    "                ('fields', ctypes.c_void_p), ('n_in_sequence', ctypes.c_int)]\n"
    "api.PyStructSequence_NewType.restype = ctypes.py_object\n"
    "api.PyStructSequence_NewType.argtypes = [ctypes.POINTER(Desc)]\n"
    "UNNAMED = ctypes.c_void_p.in_dll(api, 'PyStructSequence_UnnamedField').value\n"
    "keep = []\n"
    "def mk(names, nseq):\n"
    "    arr = (Field * (len(names) + 1))()\n"
    "    for i, nm in enumerate(names):\n"
    "        if nm is None:\n"
    "            arr[i].name = UNNAMED\n"
    "        else:\n"
    "            b = ctypes.create_string_buffer(nm); keep.append(b)\n"
    "            arr[i].name = ctypes.cast(b, ctypes.c_void_p).value\n"
    "    arr[len(names)].name = None\n"
    "    d = Desc(b'm.T', None, ctypes.cast(arr, ctypes.c_void_p).value, nseq); keep.append((arr, d))\n"
    "    return api.PyStructSequence_NewType(ctypes.byref(d))\n")
NSEQ = HELPER + (
    "try:\n"
    "    mk([b'a'], int(sys.argv[1]))\n"
    "    print('built')\n"
    "except Exception as e:\n"
    "    print(type(e).__name__)\n")
out = {}
for nseq in (2, 3, 4, 5, 6, 9):
    r = subprocess.run([sys.executable, "-I", "-c", NSEQ, str(nseq)], capture_output=True, text=True, timeout=60)
    out[nseq] = r.stdout.strip() if r.returncode == 0 else f"crash {r.returncode}"
    print(f"1 field, n_in_sequence = {nseq}: {out[nseq]}")
case1 = (out[2] == out[3] == out[4] == "TypeError" and out[5].startswith("crash")
         and out[6] == out[9] == "SystemError")
HIDDEN = HELPER + (
    "T = mk([b'x', None, None], 1)\n"
    "print(sorted(T((1,)).__reduce__()[1][1]))\n")
r = subprocess.run([sys.executable, "-I", "-c", HIDDEN], capture_output=True, text=True, timeout=60)
print("fields x, unnamed, unnamed, n_in_sequence = 1: __reduce__ dict keys", r.stdout.strip() or f"crash {r.returncode}")
case2 = r.returncode != 0 or r.stdout.strip() != "[]"
WIDE = (
    "import ctypes, mmap, os\n"
    "libc = ctypes.CDLL(None, use_errno=True)\n"
    "libc.mmap.restype = ctypes.c_void_p\n"
    "libc.mmap.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_long]\n"
    "api = ctypes.pythonapi\n"
    "UNNAMED = ctypes.c_void_p.in_dll(api, 'PyStructSequence_UnnamedField').value\n"
    "CHUNK = 2 * 1024 * 1024\n"
    "N = 2 ** 29\n"
    "chunks = N * 16 // CHUNK\n"
    "fd = os.memfd_create('fields'); os.ftruncate(fd, CHUNK)\n"
    "m = mmap.mmap(fd, CHUNK); m.write(bytes((ctypes.c_void_p * 2)(UNNAMED, None)) * (CHUNK // 16))\n"
    "fd2 = os.memfd_create('end'); os.ftruncate(fd2, CHUNK)\n"
    "base = libc.mmap(None, (chunks + 1) * CHUNK, 0, 0x22, -1, 0)\n"
    "for i in range(chunks + 1):\n"
    "    r = libc.mmap(base + i * CHUNK, CHUNK, 1, 0x11, fd if i < chunks else fd2, 0)\n"
    "    assert r == base + i * CHUNK\n"
    "class Desc(ctypes.Structure):\n"
    "    _fields_ = [('name', ctypes.c_char_p), ('doc', ctypes.c_char_p),\n"
    "                ('fields', ctypes.c_void_p), ('n_in_sequence', ctypes.c_int)]\n"
    "api.PyStructSequence_NewType.restype = ctypes.py_object\n"
    "api.PyStructSequence_NewType.argtypes = [ctypes.POINTER(Desc)]\n"
    "d = Desc(b'm.Wide', None, base, 0)\n"
    "T = api.PyStructSequence_NewType(ctypes.byref(d))\n"
    "print(T.n_fields, T.n_sequence_fields, T.__basicsize__)\n")
r = subprocess.run([sys.executable, "-I", "-c", WIDE], capture_output=True, text=True, timeout=120)
print("2^29 unnamed fields, n_in_sequence = 0: n_fields, n_sequence_fields, __basicsize__ =", r.stdout.strip() or r.stderr.strip()[-200:])
case3 = r.stdout.split() == [str(2 ** 29), "0", "32"]
STATIC = HELPER + (
    "arr = (Field * 2)()\n"
    "b = ctypes.create_string_buffer(b'a'); keep.append(b)\n"
    "arr[0].name = ctypes.cast(b, ctypes.c_void_p).value\n"
    "d = Desc(b'm.T', None, ctypes.cast(arr, ctypes.c_void_p).value, int(sys.argv[1]))\n"
    "api.PyStructSequence_InitType2.restype = ctypes.c_int\n"
    "api.PyStructSequence_InitType2.argtypes = [ctypes.c_void_p, ctypes.POINTER(Desc)]\n"
    "buf = ctypes.create_string_buffer(type.__basicsize__ + 64)\n"
    "try:\n"
    "    api.PyStructSequence_InitType2(ctypes.addressof(buf), ctypes.byref(d))\n"
    "    print('built', flush=True)\n"
    "except Exception as e:\n"
    "    print(type(e).__name__, flush=True)\n"
    "import os; os._exit(0)\n")
sout = {}
for nseq in (1, 2, 6):
    r = subprocess.run([sys.executable, "-I", "-c", STATIC, str(nseq)], capture_output=True, text=True, timeout=60)
    sout[nseq] = r.stdout.strip() if r.returncode == 0 else f"crash {r.returncode}"
    print(f"InitType2, 1 field, n_in_sequence = {nseq}: {sout[nseq]}")
case4 = sout[1] == "built" and sout[2].startswith("crash") and sout[6] == "SystemError"
```

</details>

#### 11. structseq_repr labels visible item i with tp_members[i].name, which skips unnamed fields: os.stat_result prints st_atime=<int slot 7>, and a named field after an unnamed one turns repr into SystemError

`initialize_members` (structseq.c:539-570) builds `tp_members` from the named fields only,
member `k` pointing at the slot of field `i` (:559-562), so after an unnamed field `k < i`.
`structseq_repr` (:296-327) prints visible item `i` as `tp_members[i].name` `=` `repr(item i)`
(:308, :323), using the visible index as a member index. After the first unnamed visible field
every label is the name of a later field:

<details><summary>Reproducer</summary>

```python
import ctypes, os
s = os.stat_result(range(19))
r = repr(s)
print(r)
print("s.st_atime =", s.st_atime)
api = ctypes.pythonapi
class Field(ctypes.Structure):
    _fields_ = [("name", ctypes.c_void_p), ("doc", ctypes.c_char_p)]
class Desc(ctypes.Structure):
    _fields_ = [("name", ctypes.c_char_p), ("doc", ctypes.c_char_p),
                ("fields", ctypes.POINTER(Field)), ("n_in_sequence", ctypes.c_int)]
UNNAMED = ctypes.c_void_p.in_dll(api, "PyStructSequence_UnnamedField").value
api.PyStructSequence_NewType.restype = ctypes.py_object
api.PyStructSequence_NewType.argtypes = [ctypes.POINTER(Desc)]
names = [ctypes.create_string_buffer(b"a"), None, ctypes.create_string_buffer(b"b")]
fields = (Field * 4)()
for i, nm in enumerate(names):
    fields[i].name = UNNAMED if nm is None else ctypes.cast(nm, ctypes.c_void_p).value
fields[3].name = None
desc = Desc(b"m.T", None, fields, 3)
T = api.PyStructSequence_NewType(ctypes.byref(desc))
t = T((1, 2, 3))
print("t.a, t.b =", t.a, t.b)
try:
    print(repr(t))
    err = None
except SystemError as e:
    err = str(e)
    print("SystemError:", err)
if ("st_atime=7" in r and s.st_atime == 10 and t.b == 3
        and err is not None and "member 2 name is NULL" in err):
```

</details>

#### 12. A struct sequence field named __dictoffset__, __weaklistoffset__ or __vectorcalloffset__ makes PyStructSequence_NewType raise SystemError, while PyStructSequence_InitType2 builds the type

`_PyStructSequence_NewType` passes the fields to `PyType_FromSpecWithBases` as `Py_tp_members`.
`PyType_FromMetaclass` treats members named `__weaklistoffset__`, `__dictoffset__` and
`__vectorcalloffset__` as special offsets (Objects/typeobject.c:5443-5451) and
`special_offset_from_member` (:5272-5297, called at :5651-5665) refuses them unless they are
`Py_T_PYSSIZET`; the struct sequence members are `_Py_T_OBJECT` (structseq.c:560), so NewType
raises `SystemError: type of __dictoffset__ must be Py_T_PYSSIZET`. The static twin
`PyStructSequence_InitType2` goes through `PyType_Ready`, which never looks at member names,
and builds a working type with a field of that name (`m.S(a=1, __dictoffset__=2)`).

<details><summary>Reproducer</summary>

```python
import subprocess, sys
CODE = (
    "import ctypes, os\n"
    "api = ctypes.pythonapi\n"
    "libc = ctypes.CDLL(None)\n"
    "libc.calloc.restype = ctypes.c_void_p\n"
    "libc.calloc.argtypes = [ctypes.c_size_t, ctypes.c_size_t]\n"
    "class Field(ctypes.Structure):\n"
    "    _fields_ = [('name', ctypes.c_char_p), ('doc', ctypes.c_char_p)]\n"
    "class Desc(ctypes.Structure):\n"
    "    _fields_ = [('name', ctypes.c_char_p), ('doc', ctypes.c_char_p),\n"
    "                ('fields', ctypes.POINTER(Field)), ('n_in_sequence', ctypes.c_int)]\n"
    "api.PyStructSequence_InitType2.restype = ctypes.c_int\n"
    "api.PyStructSequence_InitType2.argtypes = [ctypes.c_void_p, ctypes.POINTER(Desc)]\n"
    "api.PyStructSequence_NewType.restype = ctypes.py_object\n"
    "api.PyStructSequence_NewType.argtypes = [ctypes.POINTER(Desc)]\n"
    "arr = (Field * 3)((b'a', None), (b'__dictoffset__', None), (None, None))\n"
    "d = Desc(b'm.S', None, arr, 2)\n"
    "try:\n"
    "    api.PyStructSequence_NewType(ctypes.byref(d)); print('NewType built')\n"
    "except SystemError as e:\n"
    "    print('NewType SystemError:', e)\n"
    "buf = libc.calloc(1, type.__basicsize__ + 64)\n"
    "api.PyStructSequence_InitType2(buf, ctypes.byref(d))\n"
    "T = ctypes.cast(buf, ctypes.py_object).value\n"
    "print('InitType2 built', repr(T((1, 2))), flush=True)\n"
    "os._exit(0)\n")
r = subprocess.run([sys.executable, "-I", "-c", CODE], capture_output=True, text=True, timeout=60)
print(r.stdout.strip())
if ("NewType SystemError: type of __dictoffset__ must be Py_T_PYSSIZET" in r.stdout
        and "InitType2 built m.S(a=1, __dictoffset__=2)" in r.stdout):
```

</details>

#### 13. TypeError for too many arguments can report a negative minimum: 'takes from -2 to 1 positional arguments'

`__defaults__` accepts a tuple of any length (funcobject.c:827). The rest of the call path
copes with more defaults than parameters, using the last ones (ceval.c:1915, m < 0), but
`too_many_positional` prints `co_argcount - defcount` unchecked:

<details><summary>Reproducer</summary>

```python
def f(a):
    return a
f.__defaults__ = (1, 2, 3)
try:
    f(1, 2)
except TypeError as e:
    msg = str(e)
print(msg)
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
