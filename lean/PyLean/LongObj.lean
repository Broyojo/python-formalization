import PyLean.Registry
import PyLean.LongObj.Diff
import PyLean.LongObj.EntriesArith
import PyLean.LongObj.EntriesConv
import PyLean.LongObj.Methods
import PyLean.LongObj.Conv2
import PyLean.LongObj.IntNew
import PyLean.LongObj.EntriesComplex
import PyLean.LongObj.LongFloat
import PyLean.LongObj.EntriesStr
import PyLean.LongObj.Binop

/-!
All of `Objects/longobject.c`, `Objects/boolobject.c`, `Objects/complexobject.c`, CPython 3.15.2.

Digit-level model: `LongObj/Digits.lean` (vectors, C widths, the sign-magnitude object),
`AddSub`, `Mul`, `Karatsuba`, `Knuth`, `Div`, `DivOps`, `Shift`, `Bitwise`, `Pow`.
Conversions and methods: `Conv`, `Conv2`, `Methods`, `IntNew`, `BoolObj`, `LongFloat`.
String conversion and `_pylong`: `Format`, `FromString`, `Pylong*`. Complex: `Complex*`.
Registry statements: `LongObj/Props.lean`; entries in `LongObj/Entries*.lean`.
Difftests: `difftest/longobj_diff.py`, `longobj_str_diff.py`, `longobj_complex_diff.py`.
-/

namespace PyLean.LongObj

open PyLean.Registry

def entries : List Entry := entriesArith ++ entriesConv ++ entriesMethods ++ entriesConv2 ++ entriesIntNew ++ entriesComplex ++ entriesFloat ++ entriesStr ++ entriesBinop

end PyLean.LongObj
