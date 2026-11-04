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
import PyLean.LongObj.Compare
import PyLean.LongObj.AsByteArray
import PyLean.LongObj.RoundNear

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

def entriesCompare : List Entry := [
  { id := "longobj-compare", pyFile := "Objects/longobject.c", pyFns := ["long_compare"]
    statement := "long_compare(a, b) is negative exactly when a < b, zero exactly when a == b and positive exactly when a > b, for all ints of every size, on the compact path and on the digit path."
    source := "comment at longobject.c:3600-3602", status := .proven
    prop := ``LongCompareExact, thm := some ``longCompareExact_proven },
  { id := "longobj-richcompare", pyFile := "Objects/longobject.c", pyFns := ["long_richcompare", "long_compare"]
    statement := "For two ints, each of <, <=, ==, !=, >, >= gives the comparison of the values (through the identity shortcut or long_compare); a non-int operand on either side gives NotImplemented."
    source := "stdtypes: comparisons; CHECK_BINOP at longobject.c:1843-1847", status := .proven
    prop := ``LongRichcompareExact, thm := some ``longRichcompareExact_proven
    notes := "Smoke-tested through int.__lt__ ... int.__ge__ on 3.15.2, with bool and int subclasses, float and str operands, and the same object on both sides." },
  { id := "longobj-negate", pyFile := "Objects/longobject.c", pyFns := ["_PyLong_Negate"]
    statement := "_PyLong_Negate gives the canonical object of -v; a shared object (a cached small int) is never modified in place but replaced through _PyLong_FromSTwoDigits."
    source := "comment at longobject.c:353-354", status := .proven
    prop := ``LongNegateExact, thm := some ``longNegateExact_proven
    notes := "longNegate_fst shows that on every caller's argument the result is Long.flip, which is how the models of long_mul, long_divrem and long_rem write the call." },
  { id := "longobj-divmod-near", pyFile := "Objects/longobject.c", pyFns := ["_PyLong_DivmodNear"]
    statement := "_PyLong_DivmodNear raises TypeError('non-integer arguments in division') for a non-int argument and ZeroDivisionError for b == 0, and otherwise returns (q, r) with a == q*b + r, 2*abs(r) <= abs(b) and q even on a tie, for every sign of a and b."
    source := "comment at longobject.c:6112-6115", status := .proven
    prop := ``DivmodNearExact, thm := some ``divmodNearExact_proven
    notes := "Smoke-tested through ctypes on 3.15.2 against the Python reference in the comment at :6127-6137, 300k cases with negative divisors. The fix-up is MathInt.divmodNear, a value-level mirror of :6146-6185." },
  { id := "longobj-int-round", pyFile := "Objects/longobject.c", pyFns := ["int___round___impl"]
    statement := "round(x, ndigits) for an int returns x for None; ndigits goes through _PyNumber_Index (an int directly, another object's __index__, whose exception or TypeError passes through); the value is the multiple of 10**-ndigits nearest x, ties to even, and x for ndigits >= 0."
    source := "built-in round() docs", status := .proven
    prop := ``IntRoundExact, thm := some ``intRoundExact_proven },
  { id := "longobj-as-byte-array-stores", pyFile := "Objects/longobject.c", pyFns := ["_PyLong_AsByteArray"]
    statement := "When v >= 0 or the conversion is signed, _PyLong_AsByteArray stores exactly n bytes holding v mod 256**n whether or not it succeeds, returns 0 exactly when v fits, and sets OverflowError only with with_exceptions; a negative v converted unsigned stores nothing."
    source := "comment at longobject.c:1154-1157; int.to_bytes docs", status := .open
    prop := ``AsByteArrayStores
    notes := "Open: asByteArrayW mirrors the partial stores and with_exceptions = 0, and the difftest (fn byte_array_w, through PyLong_AsNativeBytes on a 0xAA-filled buffer) agrees, but the proof needs a simulation of the bounded store loop by the unbounded one; MathInt.asByteArray_spec covers only the raising form without the buffer." }
]

def entries : List Entry := entriesArith ++ entriesConv ++ entriesMethods ++ entriesConv2 ++ entriesIntNew ++ entriesComplex ++ entriesFloat ++ entriesStr ++ entriesBinop ++ entriesSign ++ entriesCompare

end PyLean.LongObj
