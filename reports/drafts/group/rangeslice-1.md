<!-- title: Small inconsistencies in range and slice found by a formal model -->
### Bug report

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. PySlice_GetIndices() returns 0 (success) with OverflowError set when a slice index does not fit in Py_ssize_t

PySlice_GetIndices() converts the step, start and stop with PyLong_AsSsize_t() but never checks for the -1/OverflowError failure return. The -1 is used as an ordinary index, the bounds checks that follow usually pass, and the function returns 0 ("success") with the OverflowError still pending. For slice(None, None, 2**64) and length 10 it returns 0 with (start, stop, step) = (9, -1, -1), i.e. a reversed slice nobody asked for, plus a pending exception; for slice(2**64, 5) it returns 0 with start = -1 + 10 = 9. A caller that trusts the documented contract continues with garbage indices and then trips "SystemError: ... returned a result with an exception set" (release builds) or an assertion (debug builds).

*May be intended:* The function is legacy ("XXX support long ints", sliceobject.c:191) and indices that do not fit are expected to be rejected; returning success with an exception set is not a plausible design choice. A very similar typo-level bug in the same function (checking r->step instead of r->start, bpo-34229 / gh-78410) was fixed by maintainers as a "good catch".

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
if r1[:2] == (0, "OverflowError") and r2[:2] == (0, "OverflowError"):
    print("Observed the reported behavior.")
```

</details>

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
AI tools (Claude and Codex) helped investigate the findings and prepare this report. The examples were rerun on CPython 3.15.2 and main, and the report received technical review. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
