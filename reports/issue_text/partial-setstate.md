<!-- title: functools.partial.__setstate__ with a tuple subclass as args miscounts placeholders, then crashes when called -->
<!-- form: crash -->
<!-- records: corelibs-partial-setstate-phcount -->
`partial.__setstate__` counts the `Placeholder`s in the state's `args` by reading the tuple's storage, and only then converts a tuple subclass to a plain tuple with `PySequence_Tuple`, which runs the subclass's `__iter__`. The stored args and the stored placeholder count then describe two different tuples, and the call trusts the count.

```python
from functools import Placeholder, partial

class T(tuple):
    def __iter__(self):
        return iter((Placeholder,) * 40 + (1,))

def f(*a):
    return a

p = partial(f)
p.__setstate__((f, T((Placeholder, 1)), {}, None))
p(10)   # segfault in partial_vectorcall
```

With `__iter__` returning `iter((1, 2))` instead, `p(10)` returns `(1, 2)` and silently drops the argument. A state with keywords crashes through `partial_call` the same way.

I'd expect the count to be taken from the tuple that is stored, or a `TypeError` for an args tuple that changes on iteration.

Cause: Modules/_functoolsmodule.c:821-832 count placeholders in the raw tuple, and :834-838 call `PySequence_Tuple` afterwards. `partial_vectorcall` (:535-548) and `partial_call` (:645-660) index and copy by that count.
