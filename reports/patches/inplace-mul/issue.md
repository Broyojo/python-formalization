<!-- title: `x *= seq` raises TypeError for int subclasses and IntEnum where `x * seq` works -->
### Bug report

When the left operand is an instance of a Python class that supports `__index__` but has no `__mul__`/`__imul__` that handles sequences (an `int` subclass, an `IntEnum` member, or any class with `__index__`), `x *= [1]` raises `TypeError`, while `x * [1]` and `x = x * [1]` work. With a plain `int` on the left it works.

```python
import enum, operator

class MyInt(int):
    pass

class Number(enum.IntEnum):
    TWO = 2

x = MyInt(2)
print(x * [1])              # [1, 1]
x *= [1]                    # TypeError: unsupported operand type(s) for *=: 'MyInt' and 'list'

y = Number.TWO
y *= [1]                    # TypeError: unsupported operand type(s) for *=: 'Number' and 'list'

operator.imul(MyInt(2), [1])  # same TypeError
```

Expected: `[1, 1]` in each case, the same as `x * [1]`.

The cause is in `PyNumber_InPlaceMultiply` (Objects/abstract.c): the right operand's `sq_repeat` is only tried in an `else if (mw != NULL)` branch, which is skipped whenever the left operand's type has a `tp_as_sequence` at all, even if that has no repeat slot. Every heap type has `tp_as_sequence`, so for these classes the list's repeat is never reached. `PyNumber_Multiply` does not have this problem because it checks the right operand independently.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux
