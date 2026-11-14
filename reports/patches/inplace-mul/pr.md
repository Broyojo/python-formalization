# gh-XXXXXX: Fix `x *= seq` when `x` is an instance of a Python class with `__index__`

`PyNumber_InPlaceMultiply` only fell back to the right operand's `sq_repeat` when the left operand's type had no `tp_as_sequence` at all. Heap types always have one, so `x *= [1]` raised `TypeError` for `int` subclasses, `IntEnum` members and other classes with `__index__`, although `x * [1]` worked. The right operand's repeat is now tried whenever the left operand provides no repeat slot, as `PyNumber_Multiply` does. The right operand is still not repeated in place.

Note: one error message changes. For a left operand with sequence methods but no `__index__`, such as `{} *= [1]`, the message now matches `{} * [1]` ("can't multiply sequence by non-int of type 'dict'"). This also matters for gh-149180: if every type gets a `tp_as_sequence`, plain `int *= list` would hit the same bug without this fix.
