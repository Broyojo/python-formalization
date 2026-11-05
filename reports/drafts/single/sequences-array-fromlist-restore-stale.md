<!-- title: array.fromlist: after an item's __index__ clears the array, the error … -->
# Bug report

### Bug description

array_array_fromlist_impl (Modules/arraymodule.c:1852-1883) grows the array to old_size + n
(:1864), then stores item i with `setitem(self, Py_SIZE(self) - n + i, v)` (:1869-1870). The
setitem converts v first (__index__ for the integer typecodes), and that code may clear the array.
CHECK_ARRAY_BOUNDS (:217-225) then refuses the store with IndexError, and fromlist restores with
`array_resize(self, old_size)` (:1871). That call does not undo fromlist's growth: it resizes
whatever array the code left. When the array had 16 or more items at the clear (old_size + n >= 16),
array_resize(self, 0) freed the buffer (:163-169), so the restore reallocates a NULL buffer to
old_size items (:183-198) that nobody writes. fromlist raises IndexError and the array holds
old_size items of uninitialised memory. With fewer than 16 items the buffer is kept (:156-161) and
the "cleared" items come back instead.
Lean (lean/PyLean/Sequences/ArrayFromListRe.lean): ArrayFromListRestore (a fromlist whose first
store fails leaves no more items than the conversion code left) is refuted by a 16-item 'q' array
and an item whose __index__ clears it; ArrayFromListClear states the exact outcome for every
integer typecode and every array and list with old_size + n >= 16; ArrayFromListLive states the
live-size store index for every conversion that leaves a larger array (python/cpython#152166).

```python
from array import array
a = array('q', range(100, 164))
class V:
    def __index__(self):
        a.clear()
        return 7
try:
    a.fromlist([V()])
except IndexError as e:
    print("IndexError:", e)
print("len", len(a), "first items", list(a[:4]))
# Expected: the array the conversion left (empty), or the 64 old items; not 64 never-written cells.
```

**Expected:** fromlist raises IndexError (the conversion emptied the array under the store) and leaves either the empty array the conversion left or the old items; it never creates items nobody wrote.

**Actual:** python3 3.15.2 (pod): IndexError: array assignment index out of range; len 64, the items heap-address values (e.g. 134979994222352). REPRODUCED. Under PYTHONMALLOC=debug every item is -3617008641903833651 (0xCDCD... fill of fresh memory), which confirms they were never written. With array('q', range(100, 115)) and one item (15 + 1 = 16 items at the clear) the same happens; with array('q', range(100, 108)) the old items come back unchanged. main (3.16.0a1+dev, vendor/cpython-main/python.exe): identical. REPRODUCED (scripts/check_bugs.py on both).

**Cause:** Modules/arraymodule.c:1871 (and :1877 on the list-size path) calls array_resize(self, old_size) without checking that the array still has at least old_size items whose first old_size are the old ones; after a clear, array_resize (:140-199) grows a NULL buffer and does not initialise it.

**Possible fix:** Hold an export (or a "resizing" flag) on self while fromlist converts items, so the conversion's clear() raises BufferError, as Serhiy suggested for tofile (gh-142884); or convert every item into a temporary buffer first and resize/copy only once all conversions succeeded, which also removes the live-size store index of gh-152166. Merely re-checking Py_SIZE(self) before the restore is not enough: the old items are gone after a clear, so the only consistent states are "empty" or "error before any user code".

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance; I reproduced it on 3.15.2 and on main and reviewed it before filing.
