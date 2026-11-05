<!-- title: array('e').append(65536.0) raises but keeps an uninitialised item -->
# Bug report

### Bug description

ins1 checks a value with setitem(self, -1, v), grows the array, shifts, and stores with setitem(self, where, v). Every other setitem validates before its `if (i >= 0)`, so the first call catches what the second would refuse. e_setitem, new in 3.15, calls PyFloat_Pack2 inside `if (i >= 0)`, and Pack2 is what raises OverflowError for a finite value outside binary16. The check passes, the array grows, the store raises, and ins1 returns -1 without undoing anything. So a failed append, insert or extend leaves len(a) one larger, and for a position at or past the end the new item is whatever realloc left there: a read of uninitialised heap memory from Python. On 3.15.2, array('e') followed by a failed append gave the item 3.25 (b'\x80B') in our run. An insert before the end leaves the item at that position duplicated. Lean: ArrayIns1Atomic and ArrayIterExtend are refuted by this input (array('e'), 65536.0); ArrayIns1Failure and ArrayIterExtendExact state what happens, for every typecode.

```python
from array import array
a = array('e', [1.0, 2.0])
try:
    a.append(65536.0)
    raised = False
except OverflowError:
    raised = True
b = array('e', [1.0, 2.0])
try:
    b.insert(0, 65536.0)
except OverflowError:
    pass
print(raised, len(a), list(b))
```

**Expected:** OverflowError with the array unchanged, as for 'b', 'h', 'i' and the others.

**Actual:** python3 3.15.2: True 3 [1.0, 1.0, 2.0]. On the pod's build, a failed array('e').append(1e6) left the slot b'\x80B' on each of five tries in one process, bytes the array never held. main (python.exe 3.16.0a1+dev heads/main:ef1fce0): identical. Its e_setitem (Modules/arraymodule.c:585-599) parses a double since gh-156864 and still packs under `if (i >= 0)`.

**Cause:** Modules/arraymodule.c:636-640 (e_setitem) packs only for i >= 0, and PyFloat_Pack2 (Objects/floatobject.c:1944-1946, 1973-1974, 1996-1999) is the only range check. Modules/arraymodule.c:870 (first setitem), :873 (array_resize) and :888 (second setitem, whose failure ins1 passes on with the array already grown).

**Possible fix:** In e_setitem, pack into a local `unsigned char buf[2]` before CHECK_ARRAY_BOUNDS, return -1 on failure, and memcpy to ob_item under `if (i >= 0)`.

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/sequences-array-e-ins1-overflow-keeps-slot.yaml
