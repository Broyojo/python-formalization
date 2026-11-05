<!-- title: AttributeError.__reduce__ uses a __dict__ that __eq__ can free -->
# Bug report

### Bug description

`AttributeError_getstate` (Objects/exceptions.c:2723-2725) and `ImportError_getstate` (:1883-1885) read `PyObject *dict = self->dict` without a reference and call `PyDict_Copy(dict)`. For a dict with many deleted entries (`ma_used < 2/3 * dk_nentries`), `copy_lock_held_untracked` (Objects/dictobject.c:4490-4539) does not clone the table but calls `dict_merge(copy, o)`, and `dict_dict_merge` (:4223-4249) inserts each item with `insertdict`, which runs a key's `__eq__` when two keys share a hash. Nothing in this chain holds a reference to `o` (`dict_merge` and `PyDict_Copy` take it borrowed). If that `__eq__` runs `e.__dict__ = {}`, the last reference to the instance dict is dropped and the dict is freed; `dict_dict_merge` then reads `other->ma_used` (:4249) and calls `_PyDict_Next(other)` on the freed object.

```python
import subprocess, sys
child = r'''
import sys
keep = sys.argv[1] == "keep"
armed = False
class K:
    def __init__(self, n): self.n = n
    def __hash__(self): return 1
    def __eq__(self, other):
        global armed
        if armed:
            armed = False
            e.__dict__ = {}
            # allocate dicts so the freed one is reused
            junk = [{"a%d" % i: [i] * 8} for i in range(50)]
        return False
e = AttributeError("x", name="n")
d = {}
for i in range(6):
    d["p%d" % i] = i
d[K(1)] = 1
d[K(2)] = 2
for i in range(6):
    del d["p%d" % i]
e.__dict__ = d
if not keep:
    del d
armed = True
try:
    e.__reduce__()
    print("ok")
except RuntimeError as ex:
    print("RuntimeError:", ex)
'''
out = {}
for mode in ("keep", "free"):
    p = subprocess.run([sys.executable, "-c", child, mode], capture_output=True, text=True)
    out[mode] = (p.returncode, p.stdout.strip())
    print(mode, out[mode])
```

**Expected:** Both modes copy the dict: the instance dict that was replaced is not mutated, so __reduce__ returns its state.

**Actual:** python3 3.15.2: keep -> ok; free -> "RuntimeError: dict mutated during update" (also under PYTHONMALLOC=debug, and for ImportError). main (3.16.0a1+dev): the same.

**Cause:** Objects/exceptions.c:2723-2725 and :1883-1885 pass the borrowed `self->dict` to PyDict_Copy; Objects/dictobject.c:4535-4539 (dict_merge into the copy) and :4223-4249 (dict_dict_merge's insert loop, which runs __eq__ and then reads other->ma_used) hold no reference to the source.

**Possible fix:** Take a strong reference: `PyObject *dict = Py_XNewRef(self->dict);` and release it after the copy (in both getstate functions); or have PyDict_Copy/dict_merge hold `other` for the slow path.

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/typeobj-exc-getstate-borrowed-dict.yaml
