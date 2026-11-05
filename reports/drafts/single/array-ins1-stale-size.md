<!-- title: array.append/insert/extend use a size saved before item conversion, exposing uninitialized items after a callback clears the array -->
### Bug report

`ins1()` saves the array length before its first item conversion. If `__index__` clears the array, it then grows the array using that saved length. The append succeeds with the original number of leading items plus the new value, but those leading items were never initialized when clearing freed the buffer.

```python
from array import array
a = array('q', range(64))
class V:
    calls = 0
    def __index__(self):
        V.calls += 1
        if V.calls == 1:
            a.clear()
        return 7
a.append(V())
changed = sum(1 for x, y in zip(a[:64], range(64)) if x != y)
print("len", len(a), "last", a[-1], "items differing from range(64):", changed)
```

Recorded on 3.15.2 and main: `len 65 last 7 items differing from range(64): 64`. Under `PYTHONMALLOC=debug`, the leading items all contain the allocator's `0xCD` fill. Their actual values depend on the heap. Expected: append to the array left by conversion, or reject the mutation; do not return uninitialized items.

Cause: Modules/arraymodule.c:865 saves `n` before `setitem(self, -1, v)` at :870 can run Python. The resize at :873 and insertion positions at :876-888 use that stale `n`. The bounds checks inside setitem do not help: the stale resize itself created the in-bounds, uninitialized slots. Re-read the size after conversion, or restructure insertion so conversion cannot invalidate the saved state. `insert()` and iterable `extend()` share this helper; a growing callback can also lose appended items.

The record identifies gh-158345 as a different error path in `ins1`, and notes that its PR gh-158348 would also remove this stale read by restructuring insertion. Recheck that change before filing this as a separate issue.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare these drafts. Results in the body are taken from the bug records; final interpreter reruns and human review are pending. Record: [sequences-array-ins1-stale-size](https://github.com/Broyojo/python-formalization/blob/main/bugs/sequences-array-ins1-stale-size.yaml)
