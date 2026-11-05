<!-- title: __class__ assignment decrefs a stale old type when a str-subclass … -->
# Bug report

### Bug description

`object_set_class` reads `oldto = Py_TYPE(self)` (typeobject.c:7881) before calling
`object_set_class_world_stopped` (:7882), and after a successful assignment drops one
reference to that `oldto` (:7888). In between, `compatible_for_assignment` calls
`same_slots_added` (:7739), which compares the two classes' `__slots__` tuples with
`PyObject_RichCompareBool` (:7665). `type_new` keeps `__slots__` names that are instances of
a `str` subclass as they are, so that comparison runs the subclass's `__eq__`. If that
`__eq__` assigns `self.__class__` itself, the inner assignment changes the type and drops
the reference to the old class; the outer one then sets the type again and drops a second
reference to the same old class. Each round leaves the old class one reference short (and
the new class one reference too many):

```python
import sys
class S(str):
    armed = False
    def __eq__(self, other):
        if S.armed:
            S.armed = False
            inst.__class__ = B
        return str.__eq__(self, other)
    __hash__ = str.__hash__
class A: __slots__ = (S('x'),)
class B: __slots__ = (S('x'),)
inst = A()
ra, rb = sys.getrefcount(A), sys.getrefcount(B)
S.armed = True
inst.__class__ = B
print('delta', ra - sys.getrefcount(A), sys.getrefcount(B) - rb, flush=True)
for i in range(20):
    inst = A()
    S.armed = True
    inst.__class__ = B
    del inst
print(A.__name__, A.__mro__, flush=True)
```

**Expected:** `A` loses exactly one reference and `B` gains one per assignment, as when `__eq__` does nothing; no crash.

**Actual:** python3 3.15.2: the first assignment moves A's count 5 -> 3 and B's 4 -> 6 (delta 2 2); the loop then dies with SIGSEGV in _Py_Dealloc (return code -11). REPRODUCED. main (3.16.0a1+dev, vendor/cpython-main/python.exe): same deltas, SIGSEGV. REPRODUCED.

**Cause:** Objects/typeobject.c:7881 captures `oldto` before :7882, which can run Python code through compatible_for_assignment -> same_slots_added -> PyObject_RichCompareBool (:7739, :7665); :7888 then drops a reference to that captured type although the inner assignment already dropped it. object_set_class_world_stopped also re-reads nothing after the comparison: it sets the type (:7846) and increfs `newto` regardless of what the comparison did.

**Possible fix:** Compare the slot names without running Python code (they are `str` instances, so an exact unicode comparison such as `_PyUnicode_Equal` on each item after checking the tuple sizes), or hold a strong reference to `oldto` across the call and re-check `Py_TYPE(self) == oldto` after `compatible_for_assignment` returns, failing or retrying if it changed.

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance; I reproduced it on 3.15.2 and on main and reviewed it before filing.
