<!-- title: Reentrant __class__ assignment from a __slots__ name comparison decrefs the old class twice and crashes -->
<!-- form: crash -->
<!-- records: typeobj-set-class-reentrant-slot-eq -->
`__class__` assignment compares slot-name tuples using Python equality. A str-subclass slot name can assign `__class__` again during this comparison. The outer assignment then decrements the original class a second time, eventually freeing a class that is still referenced.

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

Recorded on 3.15.2 and main: prints `delta 2 2`, then SIGSEGV in `_Py_Dealloc`. The net transition from A to B should transfer one instance-owned reference, even if the inner assignment already performed that transition.

Cause: Objects/typeobject.c:7881 saves the borrowed old type before the compatibility checks. `same_slots_added` invokes `PyObject_RichCompareBool` on slot tuples at :7665; the callback can change the instance type. The outer code still assigns the new type (:7846) and decrements the saved old type (:7888). Compare slot-name string contents without Python callbacks, or retain the old type and recheck the instance type after compatibility checks before committing.

The record relates this to gh-159098, which concerns a stale type during attribute lookup; this path is inside `__class__` assignment itself.
