import PyLean.Decimal.Context
import PyLean.Binary64.Float

/-!
What `_pydecimal` takes from outside the module: `Decimal.from_float`, the float branch
and the `ConversionSyntax` path of `Decimal.__new__`, `Decimal.from_number`, and
`_convert_for_comparison` with the rich comparisons built on it.

Floats are `Binary64.F64`, exact IEEE-754 doubles. A `numbers.Rational` operand (an int,
a bool, a `Fraction`) is its `numerator` and `denominator` (`d > 0`, a type invariant of
`numbers.Rational`); `Fraction` keeps them in lowest terms, and for an int `d = 1`.
The operators are called as `a == b`, `a < b`, ...: `context` is `None`, so every
context read is `getcontext()`, here `c`.
-/

namespace PyLean.Decimal

open PyLean
open PyLean.Binary64

/-! ## `from_float` -/

/-- `Decimal.from_float(f)` for a float `f`, with `cls` = `Decimal`,
_pydecimal.py:736-760. An infinity or NaN goes through `cls(repr(f))`, whose
`repr` is `'inf'`, `'-inf'` or `'nan'` (a NaN's sign is not printed). -/
def fromFloat (f : F64) : Py Dec := do
  if f.isInf || f.isNaN then
    return ← pyParse (if f.isNaN then "nan" else if f.sign then "-inf" else "inf").toList
  -- if _math.copysign(1.0, f) == 1.0: sign = 0 else: sign = 1
  let sign := !(F64.eq (F64.copysign F64.one f) F64.one)
  let (n, d) ← float_as_integer_ratio (F64.abs f)
  let k := bitLen d.toNat - 1
  -- coeff = str(n*5**k)
  let coeff := n.toNat * 5 ^ k
  strLimit coeff
  return .fin sign coeff (-(k : Int))

/-! ## `Decimal.__new__` -/

/-- An argument of `Decimal(value)`: a str, an int (or bool), a Decimal, a tuple
`(sign, digits, exp)` (`digits = none`: not iterable), a float, or anything else. -/
inductive NewArg where
  | str (s : List Char)
  | int (n : Int)
  | dec (d : Dec)
  | tuple (s : PyVal) (digits : Option (List PyVal)) (e : PyVal)
  | float (f : F64)
  | other
  deriving Inhabited

/-- `Decimal(value, context)`, _pydecimal.py:552-700, with `c` the context argument or
`getcontext()`. A str that does not match `_parser` (:579-585) goes through
`context._raise_error(ConversionSyntax, ...)`, whose handler gives `_NaN`; a float
(:687-698) flags (or traps) FloatOperation, then copies `Decimal.from_float(value)`.
The `_WorkRep` branch (:636-641) is internal and has no `NewArg`. -/
def pyNew (c : Ctx) : NewArg → DM PyObj
  | .str s => do
    match pyMatch ((strip s).filter (· ≠ '_')) with
    | none =>
      let r ← raiseError c [] .conversionSyntax
      return (r.getD nanD).toPyObj
    | some _ => return (← liftPy (pyParse s)).toPyObj
  | .int n => do return (← liftPy (pyFromInt n)).toPyObj
  | .dec d => return d.toPyObj
  | .tuple s ds e => liftPy (pyFromTuple s ds e)
  | .float f => do
    let _ ← raiseError c [] (.plain .floatOperation)
    return (← liftPy (fromFloat f)).toPyObj
  | .other => throw (.typeError "~Cannot convert to Decimal")

/-- `Decimal.from_number(number)`, _pydecimal.py:703-715: `cls(number)` for an int,
Decimal or float, else TypeError. -/
def fromNumber (c : Ctx) : NewArg → DM PyObj
  | .int n => pyNew c (.int n)
  | .dec d => pyNew c (.dec d)
  | .float f => pyNew c (.float f)
  | _ => throw (.typeError "~Cannot convert to Decimal")

/-! ## `_convert_for_comparison` and the rich comparisons -/

/-- The right operand of a rich comparison as `_convert_for_comparison` sees it: a
Decimal, a `numbers.Rational` `n / d` (int, bool, Fraction), a float, a complex, or
anything else. -/
inductive CmpArg where
  | dec (d : Dec)
  | rat (n : Int) (d : Nat)
  | float (f : F64)
  | complex (re im : F64)
  | other
  deriving Inhabited

/-- `context.flags[FloatOperation] = 1` (_pydecimal.py:6144): the flag is set and no trap
is consulted. -/
def setFlag (s : Signal) : DM Unit := modify (fun fl => if s ∈ fl then fl else fl ++ [s])

/-- `_convert_for_comparison(self, other, equality_op)`, _pydecimal.py:6115-6149, with
`getcontext()` = `c`. `none` is `(NotImplemented, NotImplemented)`. For a Rational the
finite `self` is scaled by the denominator, `str(int(self._int) * other.denominator)`,
and `other` becomes `Decimal(other.numerator)`. -/
def convertForComparison (c : Ctx) (eqOp : Bool) (a : Dec) : CmpArg → DM (Option (Dec × Dec))
  | .dec d => return some (a, d)
  | .rat n den => do
    let a' ← match a with
      | .fin s co e => do
        liftPy (intLimit (numDigits co))
        liftPy (strLimit (co * den))
        pure (Dec.fin s (co * den) e)
      | d => pure d
    let b ← liftPy (pyFromInt n)
    return some (a', b)
  | .float f => floatCase f
  | .complex re im =>
    -- if equality_op and isinstance(other, Complex) and other.imag == 0: other = other.real
    if eqOp && F64.eq im (F64.zero false) then floatCase re else return none
  | .other => return none
where
  /-- :6141-6148. -/
  floatCase (f : F64) : DM (Option (Dec × Dec)) := do
    if eqOp then setFlag .floatOperation else raiseSig c .floatOperation
    return some (a, ← liftPy (fromFloat f))

/-- `Decimal.__eq__`, _pydecimal.py:926-932, as `a == b`. `none` is NotImplemented. -/
def richEq (c : Ctx) (a : Dec) (b : CmpArg) : DM (Option Bool) := do
  match ← convertForComparison c true a b with
  | none => return none
  | some (x, y) => return some (← dunderEq c x y)

/-- `Decimal.__lt__`, `__le__`, `__gt__`, `__ge__`, _pydecimal.py:934-968, as `a < b` etc. -/
def richOrd (test : Int → Bool) (c : Ctx) (a : Dec) (b : CmpArg) : DM (Option Bool) := do
  match ← convertForComparison c false a b with
  | none => return none
  | some (x, y) => return some (← dunderOrd test c x y)

def richLt := richOrd (fun x => decide (x < 0))
def richLe := richOrd (fun x => decide (x ≤ 0))
def richGt := richOrd (fun x => decide (x > 0))
def richGe := richOrd (fun x => decide (x ≥ 0))

end PyLean.Decimal
