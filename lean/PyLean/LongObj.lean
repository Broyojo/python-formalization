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
import PyLean.LongObj.SignApi

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


def entriesSign : List Entry := [
  { id := "longobj-sign-api-agree", pyFile := "Objects/longobject.c"
    pyFns := ["PyLong_GetSign", "PyLong_IsPositive", "PyLong_IsNegative", "PyLong_IsZero"]
    statement := "PyLong_GetSign gives the sign of the value and PyLong_IsPositive/IsNegative/IsZero agree with it for every int; every other object makes all four raise TypeError."
    source := "the implementation disagreeing with itself (method vs equivalent method)", status := .proven
    prop := ``SignApi.SignApiAgree, thm := some ``SignApi.signApiAgree_proven
    notes := "Checked through _testcapi.pylong_* on 3.15.2. PyLong_GetSign's message says 'expect int', the others 'expected int'." }
]

def entries : List Entry := entriesArith ++ entriesConv ++ entriesMethods ++ entriesConv2 ++ entriesIntNew ++ entriesComplex ++ entriesFloat ++ entriesStr ++ entriesBinop ++ entriesSign

end PyLean.LongObj
