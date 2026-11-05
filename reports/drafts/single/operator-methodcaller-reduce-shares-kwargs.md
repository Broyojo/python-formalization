<!-- title: operator.methodcaller.__reduce__ exposes its private kwargs dict -->
# Bug report

### Bug description

`methodcaller_reduce` (Modules/_operator.c:1876-1908) builds its constructor with `PyObject_VectorcallDict(partial, newargs, 2, mc->kwds)` (:1903). `functools.partial` has no vectorcall, so `_PyObject_VectorcallDictTstate` falls back to `_PyObject_MakeTpCall` (Objects/call.c:127-131), which passes a dict through unchanged (:222-223), and `type_call` hands it to `partial_new` (Objects/typeobject.c:2512). `partial_new` adopts a uniquely referenced keyword dict instead of copying it: `else if (_PyObject_IsUniquelyReferenced(kw)) { pto->kw = Py_NewRef(kw); }` (Modules/_functoolsmodule.c:299-300). The methodcaller is the only holder of `mc->kwds` (`methodcaller_new` takes the dict `_PyObject_MakeTpCall` built, :1717, and the caller drops its own reference), so `partial.keywords` *is* the methodcaller's internal dict.

```python
import subprocess, sys
alias = r'''
import operator
class O:
    def f(self, **kw): return kw
mc = operator.methodcaller('f', a=1)
p, args = mc.__reduce__()
p.keywords['a'] = 2
print("repr:", repr(mc), "| call:", mc(O()))
'''
crash = r'''
import operator
mc = operator.methodcaller('f', a=1)
p, _ = mc.__reduce__()
p.keywords[1] = 2
print("before", flush=True)
repr(mc)
print("survived", flush=True)
'''
a = subprocess.run([sys.executable, "-c", alias], capture_output=True, text=True)
c = subprocess.run([sys.executable, "-c", crash], capture_output=True, text=True)
print("alias child:", a.stdout.strip(), a.stderr.strip()[-200:])
print("crash child returncode:", c.returncode, "stdout:", c.stdout.strip().replace("\n", " | "))
aliased = "a=2)" in a.stdout and a.stdout.rsplit("| call:", 1)[-1].strip() == "{'a': 1}"
crashed = c.returncode < 0 and "before" in c.stdout and "survived" not in c.stdout
```

**Expected:** `p.keywords` is a dict of the partial's own: writing to it leaves `mc` unchanged, so `repr(mc)` keeps printing `a=1` and no key written there can reach `methodcaller_repr`.

**Actual:** python3 3.15.2: alias child prints `repr: operator.methodcaller('f', a=2) | call: {'a': 1}`; crash child prints "before" and dies with SIGSEGV (rc -11), also under PYTHONMALLOC=debug. main (3.16.0a1+dev, vendor/cpython-main/python.exe): identical. Variant use_after_free_repr: in a release build an ordinary uncaught TypeError (rc 1) whose message was formatted from the freed object's type, "V.__repr__() must return a str, not int"; rc -11 under PYTHONMALLOC=debug on 3.15.2 and on main. Variant call_route: rc -11 on 3.15.2 and on main. A second `__reduce__` while the first partial is alive copies (refcount 2), and `methodcaller('f', **d)` gets a fresh dict, so the sharing needs exactly the paths above.

**Cause:** Modules/_operator.c:1903 passes `mc->kwds` itself as the keyword dict of a call to `functools.partial`, and :1793 does the same in `methodcaller_call`. Objects/call.c:222-223 forwards a dict unchanged to `tp_call`. Modules/_functoolsmodule.c:299-300 adopts a keyword dict whose refcount is 1 instead of copying it; the refcount is 1 because the methodcaller is its only owner, not because it is a temporary. The adoption dates from the original `Py_REFCNT(kw) == 1` test; PR #140062 (merged 2025-10-15) only renamed it to `_PyObject_IsUniquelyReferenced`.

**Possible fix:** In `methodcaller_reduce`, pass a copy: `PyObject *kw = PyDict_Copy(mc->kwds); constructor = PyObject_VectorcallDict(partial, newargs, 2, kw); Py_XDECREF(kw);`, or call `partial` with the stored `vectorcall_kwnames` and values (`PyObject_Vectorcall` with kwnames) so the call machinery builds a temporary dict. In `methodcaller_call`, pass `PyDict_Copy(mc->kwds)` (or a dict built from it) to `PyObject_Call`. The root, and the fix that covers other callers, is `partial_new`: only adopt `kw` when it is known to be a temporary (for example, never adopt in `tp_new`, and keep the shortcut in the vectorcall path, which builds its own dict).

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/operator-methodcaller-reduce-shares-kwargs.yaml
