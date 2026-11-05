<!-- title: rangeslice: 2 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. range_iterator.__setstate__ raises OverflowError for big states while longrange_iterator.__setstate__ clips them

The two range iterator types disagree on out-of-range __setstate__ arguments. The PyLong
iterator (longrange_iterator) clips any int state into [0, len]. The C long iterator
(range_iterator) first converts with PyLong_AsLong() and raises OverflowError for any state
outside the C long range, so iter(range(10)).__setstate__(2**64) raises while
iter(range(2**64, 2**64 + 10)).__setstate__(2**64) silently exhausts the iterator; the same
holds for -2**64 (OverflowError vs. clipping to 0). Which iterator you get depends only on
whether start/stop/step and the length fit in a C long.

<details><summary>Reproducer</summary>

```python
fast = iter(range(10))
slow = iter(range(2**64, 2**64 + 10))
try:
    fast.__setstate__(2**64)
    f = 'clipped'
except OverflowError as e:
    f = 'OverflowError: %s' % e
slow.__setstate__(2**64)
print(type(fast).__name__, '__setstate__(2**64) ->', f)
print(type(slow).__name__, '__setstate__(2**64) -> clipped, remaining', slow.__length_hint__())
try:
    iter(range(10)).__setstate__(-2**64)
    g = 'clipped'
except OverflowError:
    g = 'OverflowError'
s2 = iter(range(2**64, 2**64 + 10)); s2.__setstate__(-2**64)
print('__setstate__(-2**64):', g, 'vs clipped, next ->', next(s2))
```

</details>

#### 2. PySlice_GetIndices() returns 0 (success) with OverflowError set when a slice index does not fit in Py_ssize_t

PySlice_GetIndices() converts the step, start and stop with PyLong_AsSsize_t() but never
checks for the -1/OverflowError failure return. The -1 is used as an ordinary index, the
bounds checks that follow usually pass, and the function returns 0 ("success") with the
OverflowError still pending. For slice(None, None, 2**64) and length 10 it returns 0 with
(start, stop, step) = (9, -1, -1), i.e. a reversed slice nobody asked for, plus a pending
exception; for slice(2**64, 5) it returns 0 with start = -1 + 10 = 9. A caller that trusts
the documented contract continues with garbage indices and then trips
"SystemError: ... returned a result with an exception set" (release builds) or an
assertion (debug builds).

<details><summary>Reproducer</summary>

```python
import importlib.machinery, importlib.util, os, subprocess, sys, sysconfig, tempfile
SRC = r'''
#include <Python.h>
static PyObject *
getindices(PyObject *self, PyObject *args)
{
    PyObject *slice;
    Py_ssize_t length, start = -7, stop = -7, step = -7;
    if (!PyArg_ParseTuple(args, "On", &slice, &length)) return NULL;
    int ret = PySlice_GetIndices(slice, length, &start, &stop, &step);
    PyObject *exc = PyErr_GetRaisedException();   /* clear it, report its type */
    PyObject *name = exc ? PyUnicode_FromString(Py_TYPE(exc)->tp_name) : Py_NewRef(Py_None);
    Py_XDECREF(exc);
    return Py_BuildValue("iNnnn", ret, name, start, stop, step);
}
static PyMethodDef methods[] = {{"getindices", getindices, METH_VARARGS, NULL}, {NULL}};
static struct PyModuleDef mod = {PyModuleDef_HEAD_INIT, "_gi_repro", NULL, -1, methods};
PyMODINIT_FUNC PyInit__gi_repro(void) { return PyModule_Create(&mod); }
'''
d = tempfile.mkdtemp()
src = os.path.join(d, "gi.c")
out = os.path.join(d, "_gi_repro" + importlib.machinery.EXTENSION_SUFFIXES[0])
open(src, "w").write(SRC)
cc = (sysconfig.get_config_var("CC") or "cc").split()
incs = {sysconfig.get_paths()["include"], os.path.dirname(sysconfig.get_config_h_filename())}
link = ["-bundle", "-undefined", "dynamic_lookup"] if sys.platform == "darwin" else ["-shared", "-fPIC"]
subprocess.run(cc + [f"-I{i}" for i in incs] + link + [src, "-o", out], check=True)
spec = importlib.util.spec_from_file_location("_gi_repro", out)
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
r1 = m.getindices(slice(None, None, 2**64), 10)
r2 = m.getindices(slice(2**64, 5), 10)
print("PySlice_GetIndices(slice(None, None, 2**64), 10) ->", r1)
print("PySlice_GetIndices(slice(2**64, 5), 10)          ->", r2)
# Documented: -1 whenever an exception is set. Observed: 0 (success) with OverflowError set.
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
