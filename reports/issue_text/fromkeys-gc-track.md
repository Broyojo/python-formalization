<!-- title: dict.fromkeys() GC-tracks a non-GC object returned by a subclass constructor (3.15 regression) -->
<!-- form: crash -->
<!-- records: dictset-fromkeys-gc-track-non-gc -->
When a dict subclass's `__new__` returns a non-GC object, `fromkeys([])` returns it but also attempts to link it into the garbage collector. The call appears to succeed; the next collection segfaults.

```python
import gc
xs = [bytes(40) for _ in range(2000)]
class D(dict):
    __new__ = lambda cls, *a: xs[1000]
r = D.fromkeys([])
assert r is xs[1000]
print("fromkeys returned", type(r).__name__, flush=True)
gc.collect()
print("survived gc.collect()", flush=True)
```

Recorded on 3.15.2 and main: prints `fromkeys returned bytes`, then SIGSEGV in `gc.collect()`. The final print is not reached. The record reports that 3.14.7 returns the object and completes the collection normally.

Cause: Objects/dictobject.c:3430 accepts any object returned by `cls()`. With an empty iterable there is no insertion to reject a non-mapping. At :3596-3597, `_PyObject_GC_IS_TRACKED(d)` and `_PyObject_GC_TRACK(d)` assume that this arbitrary object has a GC header. For bytes it does not, so the macros read and write memory preceding the object. This exit-time tracking was added for gh-151722 in 3.15. Tracking should be restricted to suitable objects created untracked by this function; at minimum it needs a `PyObject_IS_GC` check.
