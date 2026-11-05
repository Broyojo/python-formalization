<!-- title: Small inconsistencies in type objects found by a formal model -->
### Bug report

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. PyObject_CopyData compares only total byte lengths, then walks the source's indices over the destination: wrong data, and writes outside the destination view, when the shapes differ

The only size check in `PyObject_CopyData` is `view_dest.len < view_src.len` (abstract.c:690). If both views are contiguous in one order it does a memcpy, which is fine. Otherwise it walks an index vector over `view_src.shape` and hands the same vector to `PyBuffer_GetPointer` for the destination (abstract.c:727-732). Nothing checks that the two views have the same ndim or shape, so:

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

`_PyExc_PrepReraiseStar` tells a re-raised subgroup from a newly raised exception with `is_same_exception_metadata`, which compares `notes`, `traceback`, `cause` and `context` of the two objects. `notes` there is the C field `PyBaseExceptionObject.notes`, which nothing writes: `add_note` stores `__notes__` as an ordinary instance attribute. The comparison is always NULL with NULL.

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

#### 3. split() and subgroup() set __suppress_context__ on their results, which hides __context__ in tracebacks

`exceptiongroup_subset` copies the metadata of the original group to each part it builds: traceback, context, cause and notes. It copies the cause with `PyException_SetCause(eg, PyException_GetCause(orig))`, and `PyException_SetCause` always sets `suppress_context`, also when the cause is NULL. So every group built by `split()`, `subgroup()` or `except*` has `__suppress_context__ == True` whatever the original has, and it keeps `__context__`, which the traceback printer then skips:

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

#### 4. x *= seq raises TypeError for instances of Python classes although x * seq works: the sq_repeat fallback in PyNumber_InPlaceMultiply tests tp_as_sequence, which every heap type has

`PyNumber_Multiply` repeats a sequence on either side: if the left operand has no `sq_repeat`, it uses the right operand's (abstract.c:1173-1178), so `n * seq` works for any `n` with `__index__`. `PyNumber_InPlaceMultiply` is meant to do the same, and its comment says so ("the right hand operand should not be mutated in this case so sq_inplace_repeat is not used"), but it writes the test as `if (mv != NULL) { ... } else if (mw != NULL)` (abstract.c:1329, :1336). `mv` is `Py_TYPE(v)->tp_as_sequence`, and `type_new_alloc` sets that pointer on every heap type (typeobject.c:4488). So for an instance of any Python class, including a subclass of int, the right operand is never consulted:

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

#### 5. property subclass: .setter/.getter/.deleter drop an explicit doc=, because property_copy reads prop_doc, which __init__ leaves NULL for subclasses

`property_init_impl` stores the docstring in `prop_doc` only for exact `property`. For a subclass it stores it in the instance `__dict__` instead (descrobject.c:1902-1933), so that it is not shadowed by `__doc__` in the class dict, and `prop_doc` stays NULL. `property_copy`, used by `.getter`, `.setter` and `.deleter`, still takes the doc from `pold->prop_doc` (:1809), passes None, and the new object has no docstring:

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

#### 6. structseq_repr labels visible item i with tp_members[i].name, which skips unnamed fields: os.stat_result prints st_atime=<int slot 7>, and a named field after an unnamed one turns repr into SystemError

`initialize_members` (structseq.c:539-570) builds `tp_members` from the named fields only, member `k` pointing at the slot of field `i` (:559-562), so after an unnamed field `k < i`. `structseq_repr` (:296-327) prints visible item `i` as `tp_members[i].name` `=` `repr(item i)` (:308, :323), using the visible index as a member index. After the first unnamed visible field every label is the name of a later field:

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

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
I used AI tools (Claude) to find these and draft the report; each case was reproduced on 3.15.2 and on main and the text checked before filing. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
