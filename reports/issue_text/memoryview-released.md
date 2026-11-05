<!-- title: memoryview: a view released by __buffer__ or __index__ in the middle of == or item assignment is still used -->
<!-- form: crash -->
<!-- records: bytesobj-memoryview-eq-released-by-buffer bytesobj-memoryview-setitem-c-released -->
gh-92888 added checks so that a memoryview released by Python code during an operation is not used afterwards. Two paths still miss the check: both run Python code after the "released?" test and then use the buffer.

**1. `==` with an object whose `__buffer__` releases the view.** `memory_richcompare` tests the left view, then calls `PyObject_GetBuffer` on the right operand, which can release the left view and free its buffer.

```python
N = 1 << 27
other = bytes(N)
ba = bytearray(N)
m = memoryview(ba)

class W:
    def __buffer__(self, flags):
        m.release()
        ba.clear()
        return memoryview(other)

m == W()   # segfault
```

With a small buffer that is not freed, the released view compares by content and returns `True`.

**2. Item assignment with format `'c'` and a key whose `__index__` releases the view.** `memory_ass_sub` converts the key, which runs `__index__`, then writes. The other formats raise `ValueError: operation forbidden on released memoryview object` because their conversion is followed by `CHECK_RELEASED_INT_AGAIN`. The `'c'` arm of `pack_single` converts nothing and has no check.

```python
N = 1 << 27
ba = bytearray(b"a" * N)
m = memoryview(ba).cast("c")

class K:
    def __index__(self):
        m.release()
        ba.clear()
        return N // 2

m[K()] = b"x"   # segfault: write into freed memory
```

With a small buffer, the write goes into the released buffer silently (format `'c'`: no exception, the byte changes; format `'B'`: `ValueError`).

Cause: Objects/memoryobject.c:3216 tests the view and :3254 then calls `PyObject_GetBuffer(w, ...)`, which can run `__buffer__`, before :3290-3304 read the buffer. In `memory_ass_sub`, `PyNumber_AsSsize_t(key)` at :2765 runs before `pack_single`, whose `'c'` arm (:2071-2077) has no re-check. The tuple-index path (:2800-2810, `ptr_from_tuple`) has the same shape.
