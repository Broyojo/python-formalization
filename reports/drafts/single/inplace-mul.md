<!-- title: x *= [1] raises TypeError for an int subclass, although x * [1] works -->
### Bug report

For a left operand whose class has no `__imul__` and no `__mul__` for lists, `x * seq` falls back to the sequence's repeat, but `x *= seq` does not when `x` is an instance of a Python class, such as an `int` subclass or an `IntEnum` member. With a plain `int` both work.

```python
import enum, operator

class I(int):
    pass
class E(enum.IntEnum):
    TWO = 2

def inplace(x):
    x *= [1]
    return x

for x in (2, I(2), E.TWO):
    print(type(x).__name__, "multiply:", x * [1])
    for name, f in (("*=", inplace), ("operator.imul", lambda x: operator.imul(x, [1]))):
        try:
            print(name, f(x))
        except TypeError as e:
            print(name, type(e).__name__, str(e))
```

I'd expect `x *= [1]` to give `[1, 1]`, as `x * [1]` does and as it does for `x = 2`.

Cause: `PyNumber_InPlaceMultiply` (Objects/abstract.c:1337-1349) tests `else if (mw != NULL)`, whether the right type has `tp_as_sequence` at all, only when the left type has none. Every heap type has a `tp_as_sequence`, so for a Python class on the left the right operand's `sq_repeat` is never tried. `PyNumber_Multiply` tests for `mw->sq_repeat` instead.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare these drafts. The code blocks were rerun on 3.15.2 and main during technical review; the human submitter must review the report before filing. Record: [corelibs-inplace-mul-heap-left](https://github.com/Broyojo/python-formalization/blob/main/bugs/corelibs-inplace-mul-heap-left.yaml)
