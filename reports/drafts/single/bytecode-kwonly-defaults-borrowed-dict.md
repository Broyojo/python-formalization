<!-- title: Use-after-free when __eq__ replaces f.__kwdefaults__ during a call -->
# Bug report

### Bug description

When a call leaves a keyword-only parameter unbound, `initialize_locals` looks its default up with `PyDict_GetItemRef(func->func_kwdefaults, varname, &def)` (Python/ceval.c:1949-1951 in 3.15.2), passing the function's `__kwdefaults__` dict as a borrowed reference. `__kwdefaults__` can be any dict, with any keys. If it holds a non-str key whose hash equals the parameter name's, the dict's keys are DICT_KEYS_GENERAL and `compare_generic` calls that key's `__eq__` (Objects/dictobject.c:1193). That `__eq__` is Python code and can run `f.__kwdefaults__ = None`; `func_set_kwdefaults` (Objects/funcobject.c:875-906) then drops the function's reference, the last one, and the dict and its keys object are freed. After the comparison returns, `compare_generic` reads `mp->ma_keys` of the freed dict (:1198) and, on a mismatch, `_Py_dict_lookup` restarts on it (`goto start`, :1380).

```python
import os, subprocess, sys
child = r'''
class K:
    def __hash__(self):
        return hash('b')
    def __eq__(self, other):
        f.__kwdefaults__ = None
        return False
def f(*, b):
    return b
f.__kwdefaults__ = {K(): 1}
try:
    f()
except TypeError as e:
    print("TypeError", e, flush=True)
print("survived", flush=True)
'''
env = dict(os.environ, PYTHONMALLOC="debug")
p = subprocess.run([sys.executable, "-c", child], capture_output=True, text=True, env=env)
print("child returncode:", p.returncode, "stdout:", p.stdout.strip().replace("\n", " | "))
```

**Expected:** f() raises TypeError: f() missing 1 required keyword-only argument: 'b' (K() == 'b' is False), and the process continues.

**Actual:** python3 3.15.2 (release build) with PYTHONMALLOC=debug: SIGSEGV (rc -11); faulthandler's C stack is _Py_dict_lookup <- PyDict_GetItemRef <- (initialize_locals) <- _PyEvalFramePushAndInit <- _PyEval_EvalFrameDefault. Without PYTHONMALLOC=debug it prints the TypeError and survives (stale memory). A control whose __eq__ does not touch __kwdefaults__ survives under PYTHONMALLOC=debug. main (vendor/cpython-main/python.exe, 3.16.0a1+dev ef1fce0, release build): same, SIGSEGV with PYTHONMALLOC=debug. The code is unchanged there (Python/ceval.c:2027-2029).

**Cause:** Python/ceval.c:1949-1951 (3.15.2): `PyDict_GetItemRef(func->func_kwdefaults, ...)` with a borrowed dict. The generic lookup runs a stored key's `__eq__` (Objects/dictobject.c:1193) and then dereferences `mp` (:1198), relying on the caller to keep `mp` alive, which nothing does once func_set_kwdefaults (Objects/funcobject.c:901-904) has dropped the reference.

**Possible fix:** Take a strong reference for the lookup: `PyObject *kwdefs = Py_XNewRef(func->func_kwdefaults);` before the keyword-only loop (or per iteration), use it in `PyDict_GetItemRef`, and `Py_XDECREF(kwdefs)` on every exit path.

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/bytecode-kwonly-defaults-borrowed-dict.yaml
