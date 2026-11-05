<!-- title: array.append/insert/extend: ins1 resizes to a size read before … -->
# Bug report

### Bug description

ins1 (Modules/arraymodule.c:862-889) reads `n = Py_SIZE(self)` at :865, then calls
`setitem(self, -1, v)` at :870 to check the value. For every typecode but u and w that setitem
converts v with PyArg_Parse or _PyNumber_Index, which runs `__index__`, `__float__` or
`__complex__`. After that call ins1 resizes with the stale size, `array_resize(self, n+1)`
(:873), clips `where` against the stale n (:876-882), shifts n - where items (:884-887) and stores
(:888). Nothing re-reads Py_SIZE(self) after the Python code ran.
* If the code cleared the array (16 or more items, so `array_resize(self, 0)` frees the buffer,
  :163-169), the resize reallocates a NULL buffer to n + 1 items (:183-198) and the append succeeds
  with n + 1 items, the first n never written: uninitialised memory becomes array items readable
  from Python. With fewer than 16 items the buffer is kept (:156-161) and the "cleared" items
  reappear instead.
* If the code grew the array, the resize truncates it to n + 1 and the grown items are dropped
  silently.
CHECK_ARRAY_BOUNDS, added for gh-142555/gh-142882, re-checks the index inside each setitem after the
conversion; it cannot help here, because the stale value is ins1's own `n`, and the store at
`where < n + 1` is in bounds of the array ins1 itself just resized.
Lean: ArrayIns1Reentrant (an append leaves one item more than the conversion code left) is refuted
by a 16-item 'q' array whose `__index__` clears it; ArrayIns1Stale states the exact outcome for every
integer typecode and every array of at least 16 items.

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
# Correct behaviour: the conversion cleared the array, so the append leaves [7].
changed = sum(1 for x, y in zip(a[:64], range(64)) if x != y)
print("len", len(a), "last", a[-1], "items differing from range(64):", changed)
```

**Expected:** The append acts on the array the conversion left: a cleared array becomes [7]; a grown array keeps the grown items and gets 7 appended.

**Actual:** python3 3.15.2 (pod): `len 65 last 7`, all 64 leading items differing from range(64). REPRODUCED. Under PYTHONMALLOC=debug every exposed item is -3617008641903833651 (0xCDCD... fill of fresh memory), which confirms the items were never written. main (3.16.0a1+dev, vendor/cpython-main/python.exe): identical. REPRODUCED. Variants on both: grow_loses_items prints [0, 1, 2, 3, 7]; small_array_stale_items prints [7, 0, 1, 2, 3, 4, 5, 6, 7].

**Cause:** Modules/arraymodule.c:865 reads `n` before the conversion at :870 can run Python code; :873 (`array_resize(self, n+1)`), :876-882 and :884-887 use the stale n. array_resize (:140-199) does not initialise new items, so growing a freed buffer (:183-198) exposes uninitialised memory.

**Possible fix:** Re-read the size after the first setitem: `if (setitem(self, -1, v) < 0) return -1; n = Py_SIZE(self);` before the resize. Or resize before running user code, as open PR #158348 does for gh-158345 (it drops the first setitem and deletes the slot again if the store fails); that change would also remove this stale read, and a test with a clearing `__index__` should be added to it.

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance; I reproduced it on 3.15.2 and on main and reviewed it before filing.
