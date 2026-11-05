<!-- title: x *= [1] raises TypeError where x * [1] works for __index__ objects -->
# Bug report

### Bug description

PyNumber_Multiply falls back to the right operand's sq_repeat with `else if (mw && mw->sq_repeat)`. PyNumber_InPlaceMultiply has `if (mv != NULL) {...} else if (mw != NULL)`: it tests whether the left type has a tp_as_sequence at all, and not whether it has a repeat slot. Every heap class has tp_as_sequence, so for a left operand of a Python class, with no __imul__, no __mul__ and an __index__, the right operand's repeat is never tried. class I(int): pass; x = I(2); then x * [1] is [1, 1], and x *= [1] is a TypeError. With a plain int on the left it works, because int has no tp_as_sequence. So int subclasses, IntEnum members and any index-like class behave differently from int, and `x *= y` from `x = x * y`.

```python
import enum
import operator
class I(int):
    pass
x = I(2)
print(x * [1])
try:
    x *= [1]
    print(x)
    r = 'ok'
except TypeError as e:
    print('TypeError', e)
    r = 'TypeError'
class E(enum.IntEnum):
    TWO = 2
y = E.TWO
try:
    y *= [1]
    r2 = 'ok'
except TypeError as e:
    r2 = 'TypeError'
def t(f):
    try:
        return f()
    except TypeError:
        return 'TypeError'
r3 = t(lambda: operator.imul(I(2), [1]))
print(r, r2, r3)
```

**Expected:** x *= [1] gives [1, 1], as x = x * [1] does and as it does for an int.

**Actual:** python3 3.14.7: [1, 1], then TypeError: unsupported operand type(s) for *=: 'I' and 'list'; also for IntEnum and operator.imul. main (3.16.0a1+dev): python3 3.15.2: main (3.16.0a1+dev):

**Cause:** Objects/abstract.c:1337-1349, the `else if (mw != NULL)`.

**Possible fix:** Make the second branch independent of the first, as in PyNumber_Multiply: after trying the left operand's slots, try `mw && mw->sq_repeat`.

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/corelibs-inplace-mul-heap-left.yaml
