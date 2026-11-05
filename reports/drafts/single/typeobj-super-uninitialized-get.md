<!-- title: super.__new__(super).__get__(1) segfaults -->
# Bug report

### Bug description

`super` keeps its fields NULL until `super_init` runs, and `__new__` can be called on its own. `super_getattro` and `super_repr` tolerate the NULL type, but `super_descr_get` does not: when `su->obj` is NULL it calls `supercheck(su->type, obj)` (typeobject.c:12902). `PyType_IsSubtype(x, NULL)` answers no without dereferencing, so `supercheck` falls through to its error message, which reads `type->tp_name` (:12868).

```python
import subprocess, sys
cases = ["super.__new__(super).__get__(1)",
         "class A:\n    s = super.__new__(super)\nA().s"]
codes = [subprocess.run([sys.executable, '-c', c], capture_output=True).returncode
         for c in cases]
print('return codes', codes)
```

**Expected:** A TypeError, or `self` returned unbound, as a super subclass gets a clean exception.

**Actual:** python3 3.14.7: both cases die with SIGSEGV (return code -11). python3 (3.15.2): by scripts/check_bugs.py main (3.16.0a1+dev, vendor/cpython-main/python.exe): both cases SIGSEGV. by scripts/check_bugs.py.

**Cause:** Objects/typeobject.c:12891 tests `su->obj` but not `su->type`; :12902 passes the NULL on; :12868 dereferences it. :12911 would also `Py_NewRef(su->type)` if control got that far.

**Possible fix:** Treat a NULL `su->type` like an already-bound object at :12891 and return `self`, or raise TypeError. Open PR #155379 addresses the dereference.

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/typeobj-super-uninitialized-get.yaml
