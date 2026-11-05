<!-- title: dict.fromkeys() on a subclass GC-tracks a non-GC object -->
# Bug report

### Bug description

`_PyDict_FromKeys` (Objects/dictobject.c:3417) calls `cls()` for a dict subclass (:3430) and uses whatever it returns as `d`. When the iterable is empty, or `d` is neither an exact dict nor a frozendict, nothing checks that `d` is a dict at all before the exit path at :3596-3597:

```python
import subprocess, sys
child = r'''
import gc
xs = [bytes(40) for _ in range(2000)]
class D(dict):
    __new__ = lambda cls, *a: xs[1000]
r = D.fromkeys([])
assert r is xs[1000]
print("fromkeys returned", type(r).__name__, flush=True)
gc.collect()
print("survived gc.collect()", flush=True)
'''
p = subprocess.run([sys.executable, "-c", child], capture_output=True, text=True)
print("child stdout:", p.stdout.strip().replace("\n", " | "))
print("child returncode:", p.returncode)
```

**Expected:** `D.fromkeys([])` returns `xs[1000]` unchanged (as 3.14.7 does) and `gc.collect()` completes.

**Actual:** python3 3.15.2 (tags/v3.15.2:5e58eaa, GCC 11.4.0, release build): `fromkeys returned bytes`, then SIGSEGV (exit 139) inside `gc.collect()`. main (3.16.0a1+dev, ef1fce0): identical, SIGSEGV. Found by the dictobject.c review (coverage/review/Objects__dictobject.c.tsv, row `_PyDict_FromKeys`) and re-run independently.

**Cause:** Objects/dictobject.c:3430 `d = _PyObject_CallNoArgs(cls)` accepts any object. Only the `PyDict_CheckExact(d)` fast paths and the frozendict copy (:3443) look at its type; for an empty iterable the insertion loop never runs (so no `PyObject_SetItem` raises TypeError first), and control reaches `Done:` (:3587) with `need_copy == 0`, where :3596-3597 GC-track `d` unconditionally. With a non-empty iterable and a non-dict `d` without `__setitem__`, `PyObject_SetItem` raises and the Fail path is taken, so the trigger is an empty iterable, or a non-GC `d` whose `__setitem__` succeeds.

**Possible fix:** Only track what this function created untracked: guard :3596 with `PyObject_IS_GC(d)` at least, or better, track only when `d` is an any-dict (`PyAnyDict_Check(d)`) that was created untracked here (remember that in a flag where `frozendict_new_untracked` is called), leaving objects returned by `cls()` alone.

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/dictset-fromkeys-gc-track-non-gc.yaml
