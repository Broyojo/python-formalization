import PyLean.Registry
import PyLean.LongObj.Diff
import PyLean.LongObj.EntriesArith
import PyLean.LongObj.EntriesConv
import PyLean.LongObj.Methods
import PyLean.LongObj.Conv2
import PyLean.LongObj.IntNew

/-!
All of `Objects/longobject.c`, `Objects/boolobject.c`, `Objects/complexobject.c`, CPython 3.14.7.

Digit-level model: `LongObj/Digits.lean` (vectors, C widths, the sign-magnitude object),
`AddSub`, `Mul`, `Karatsuba`, `Knuth`, `Div`, `DivOps`, `Shift`, `Bitwise`, `Pow`.
Registry statements: `LongObj/Props.lean`, entries in `LongObj/EntriesArith.lean`.
Difftest: `difftest/longobj_diff.py`.
-/

namespace PyLean.LongObj

open PyLean.Registry

def entries : List Entry := entriesArith ++ entriesConv ++ entriesMethods ++ entriesConv2 ++ entriesIntNew

end PyLean.LongObj
