<!-- title: array('e'): append() or insert() of an out-of-range float raises OverflowError but still grows the array (new in 3.15) -->
### Bug report

`ins1` (used by `append`, `insert` and `extend`) first checks the value with a trial `setitem(self, -1, v)`, then grows the array and stores it. For every other typecode the trial call rejects a bad value. For the new `'e'` typecode, `e_setitem` does its range check (`PyFloat_Pack2`) only inside `if (i >= 0)`, so the trial passes, the array grows, and the real store raises. `ins1` returns the error without undoing the growth.

```python
from array import array

a = array('e', [1.0, 2.0])
try:
    a.append(65536.0)         # OverflowError, as expected
except OverflowError:
    pass
print(len(a))                 # 3, expected 2

b = array('e', [1.0, 2.0])
try:
    b.insert(0, 65536.0)
except OverflowError:
    pass
print(list(b))                # [1.0, 1.0, 2.0], expected [1.0, 2.0]
```

When the extra slot is at the end, its value is whatever the reallocation left there, not a value the array ever held.

Cause: Modules/arraymodule.c:636-640 (`e_setitem`) packs only for `i >= 0`. `ins1` checks at :870, resizes at :873, and passes on the failure of the store at :888 with the array already grown. Doing the range check before `if (i >= 0)`, as the other `*_setitem` functions do, would fix it.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). I used AI tools (Claude) to find this and draft the report, then reproduced it on 3.15.2 and on main and checked the text myself. Record: [sequences-array-e-ins1-overflow-keeps-slot](https://github.com/Broyojo/python-formalization/blob/main/bugs/sequences-array-e-ins1-overflow-keeps-slot.yaml)
