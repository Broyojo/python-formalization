<!-- title: except* crashes when an ExceptionGroup subclass's split() returns a non-exception -->
<!-- form: crash -->
<!-- records: bytecode-eg-match-split-items-unchecked -->
An `ExceptionGroup` subclass can override `split()`. `except*` checks that the result is a tuple of two items (gh-128049) but not that the items are exceptions or `None`. The match becomes the handled exception, so `sys.exception()` returns `1`, and the next `raise` in the handler crashes while it sets `__context__`.

```python
import sys

class EG(ExceptionGroup):
    def split(self, t):
        return (1, None)

try:
    raise EG('x', [ValueError()])
except* TypeError:
    print(sys.exception())   # 1
    raise KeyError('k')      # segfault
```

Output: `1`, then `Segmentation fault`. With `split()` returning `(None, 1)` the int is re-raised instead and the top level reports `print_exception(): Exception expected for value, int found`.

I'd expect a `TypeError`, as for a `split()` that returns a non-tuple.

Cause: `_PyEval_ExceptionGroupMatch` (Python/ceval.c:2339-2340) takes both items without a type check, and `CHECK_EG_MATCH` (Python/bytecodes.c:3434-3436) passes the match to `PyErr_SetHandledException`.
