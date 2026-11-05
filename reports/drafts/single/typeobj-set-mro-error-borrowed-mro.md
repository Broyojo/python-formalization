<!-- title: MRO conflict message reads freed memory: set_mro_error hashes candidate … -->
# Bug report

### Bug description

`mro_implementation_unlocked` fills `to_merge` with *borrowed* references to each base's
`tp_mro` (typeobject.c:3537-3539). When `pmerge` finds no candidate it calls
`set_mro_error`, which walks `to_merge` and inserts each remaining head into a dict
(`PyDict_SetItem`, :3359-3362). Inserting hashes the class, so a metaclass `__hash__` runs
between reads of `to_merge[i]`. If it assigns `__bases__` of one of the bases, that base gets
a new `tp_mro` and its old tuple, still in `to_merge`, is freed; the next iteration reads
`PyTuple_GET_SIZE` and `PyTuple_GET_ITEM` of freed memory.

```python
state = {'armed': False}
junk = []
class M(type):
    def __hash__(cls):
        if state['armed'] and cls.__name__ == 'X':
            state['armed'] = False
            B.__bases__ = (X, Y)
            junk.extend(bytes([0x41]) * 230 for _ in range(20000))
        return type.__hash__(cls)
base = object
for i in range(30):
    base = M('Z%d' % i, (base,), {})
class X(base, metaclass=M): pass
class Y(metaclass=M): pass
class A(X, Y): pass
class B(Y, X): pass
state['armed'] = True
try:
    class C(A, B): pass
except TypeError as e:
    print('MSG', str(e)[:120])
```

**Expected:** `TypeError: Cannot create a consistent method resolution order (MRO) for bases X, Y` (the heads of the lists as they were), or the new hierarchy's error; no read of freed memory.

**Actual:** python3 3.15.2: "Cannot create a consistent method resolution order (MRO) for bases X, b'AAAAAAAA...'" (a bytes object allocated in the freed tuple's memory). REPRODUCED. main (3.16.0a1+dev, vendor/cpython-main/python.exe): the same message. REPRODUCED. With a short B.__mro__ the freed tuple goes to the free list and is reused by the next 4-tuple, so the message names an `object()` instance instead.

**Cause:** Objects/typeobject.c:3537-3539 stores borrowed `lookup_tp_mro(base)` pointers in `to_merge`; :3359-3362 reads `to_merge[i]` on each iteration after a `PyDict_SetItem` that can run `__hash__`/`__eq__` of the metaclass. `type_set_bases` replaces and frees `tp_mro` of the base.

**Possible fix:** Take strong references in `to_merge` (`Py_NewRef` at :3539 and decref after `pmerge`), or collect the candidate classes into a new tuple before any `PyDict_SetItem`, so no Python code runs while `to_merge` is read.

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance; I reproduced it on 3.15.2 and on main and reviewed it before filing.
