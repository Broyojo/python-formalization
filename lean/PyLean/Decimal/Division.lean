import PyLean.Decimal.Ops
import PyLean.Binary64.Model

/-!
The division family of `_pydecimal`: `__truediv__`, `_divide`, `__divmod__`,
`__mod__`, `__floordiv__`, `remainder_near`.

The conditions `DivisionUndefined` and `DivisionImpossible` map to the signal
InvalidOperation (`_condition_map`, _pydecimal.py:336-339) and their handlers
return `_NaN` (:198-199, :209-210), which is `invalid`. `DivisionByZero.handle`
returns `_SignedInfinity[sign]` (:187-188).
-/

namespace PyLean.Decimal

open PyLean

/-- `_WorkRep(value)` of a finite Decimal, _pydecimal.py:5703-5716: `int(value._int)`. -/
def workRep : Dec → Py (Bool × Nat × Int)
  | .fin neg co e => do
    intLimit (numDigits co)
    return (neg, co, e)
  | _ => .ok (false, 0, 0)

/-- `return context._raise_error(DivisionByZero, msg, sign)` (_pydecimal.py:1399, :1502,
:1648): the flag, the trap, then `DivisionByZero.handle` (:187-188), which always
returns a value (the `getD` default is never taken). -/
def divByZero (c : Ctx) (sign : Bool) : DM Dec := do
  let r ← raiseError c [] (.divisionByZero sign)
  return r.getD nanD

/-- `while exp < ideal_exp and coeff % 10 == 0: coeff //= 10; exp += 1`,
_pydecimal.py:1421-1423, with the iteration bound `ideal_exp - exp`. -/
def stripIdeal (coeff : Nat) (exp ideal : Int) : Nat → Nat × Int
  | 0 => (coeff, exp)
  | f + 1 =>
    if exp < ideal ∧ coeff % 10 = 0 then stripIdeal (coeff / 10) (exp + 1) ideal f
    else (coeff, exp)

/-- The integer division of `__truediv__`, _pydecimal.py:1401-1423, for finite
operands with a non-zero divisor. The result carries one digit more than `prec`;
`coeff % 5 == 0` with a remainder bumps the last digit so that `_fix` sees an
inexact tail. -/
def truedivFin (c : Ctx) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int) :
    Py (Nat × Int) := do
  if ca = 0 then return (0, ea - eb)
  let shift : Int := (numDigits cb : Int) - numDigits ca + c.prec + 1
  let exp := ea - eb - shift
  let op1 ← workRep (.fin sa ca ea)
  let op2 ← workRep (.fin sb cb eb)
  let num := if shift ≥ 0 then op1.2.1 * 10 ^ shift.toNat else op1.2.1
  let den := if shift ≥ 0 then op2.2.1 else op2.2.1 * 10 ^ (-shift).toNat
  let coeff := num / den
  let remainder := num % den
  if remainder ≠ 0 then
    return (if coeff % 5 = 0 then coeff + 1 else coeff, exp)
  else
    let ideal := ea - eb
    return stripIdeal coeff exp ideal (ideal - exp).toNat

/-- `Decimal.__truediv__`, _pydecimal.py:1369-1426. -/
def truediv (c : Ctx) (a b : Dec) : DM Dec := do
  let sign := a.neg != b.neg
  if isSpecial a || isSpecial b then
    if let some ans ← checkNans c a (some b) then return ans
    if isinfinity a ≠ 0 ∧ isinfinity b ≠ 0 then return ← invalid c
    if isinfinity a ≠ 0 then return .inf sign
    if isinfinity b ≠ 0 then
      raiseSig c .clamped
      return .fin sign 0 c.etiny
  if !decBool b then
    if !decBool a then return ← invalid c
    return ← divByZero c sign
  match a, b with
  | .fin sa ca ea, .fin sb cb eb =>
    let r ← liftPy (truedivFin c sa ca ea sb cb eb)
    liftPy (strLimit r.1)
    fix c (.fin sign r.1 r.2)
  | _, _ => return a

/-- `op1.int *= 10**(op1.exp - op2.exp)` or `op2.int *= 10**(op2.exp - op1.exp)`,
_pydecimal.py:1447-1450 and :1601-1604: both operands as integers at the lower exponent. -/
def scaled (ca : Nat) (ea : Int) (cb : Nat) (eb : Int) : Nat × Nat :=
  if ea ≥ eb then (ca * 10 ^ (ea - eb).toNat, cb) else (ca, cb * 10 ^ (eb - ea).toNat)

/-- `_LOG_10_BASE_2_LO`, _pydecimal.py:458: the double just below `log2(10)`. -/
def log10Base2Lo : Binary64.F64 := .ofBits 0x400a934f0979a371

/-- `_LOG_10_BASE_2_HI`, _pydecimal.py:461: the double just above `log2(10)`. -/
def log10Base2Hi : Binary64.F64 := .ofBits 0x400a934f0979a372

/-- `q.bit_length()`. -/
def bitLen (q : Nat) : Nat := if q = 0 then 0 else Nat.log2 q + 1

/-- `n < x` for an int `n` and a non-NaN double `x` (`float_richcompare`, exact): an infinity
compares by its sign. -/
def intLtF (n : Nat) (x : Binary64.F64) : Bool :=
  if x.isInf then !x.sign else decide ((n : Rat) < x.toRat)

/-- `n >= x` for an int `n` and a non-NaN double `x`. -/
def intGeF (n : Nat) (x : Binary64.F64) : Bool :=
  if x.isInf then x.sign else decide (x.toRat ≤ (n : Rat))

/-- `_is_less_than_pow10a_use_str(q, a)`, _pydecimal.py:470-501: `is_valid`, and whether
`str(q)` was computed. `a * _LOG_10_BASE_2_LO` converts `a` to a double first, which raises
OverflowError when `a` rounds to infinity (`PyLong_AsDouble`, Objects/longobject.c); Python
then compares the int `q.bit_length()` with the rounded product exactly. In the band the two
tests leave open, `str(q)` runs whatever `q` is, so the integer string limit can raise where
3.14 only compared integers. -/
def isLessThanPow10aUseStr (q a : Nat) : Py (Bool × Bool) :=
  let fa := Binary64.F64.ofInt a
  if fa.isInf then .error (.overflowError "int too large to convert to float") else
  if intLtF (bitLen q) (Binary64.F64.mul fa log10Base2Lo) then .ok (true, false)
  else if intGeF (bitLen q) (Binary64.F64.add Binary64.F64.one (Binary64.F64.mul fa log10Base2Hi)) then
    .ok (false, false)
  else do
    strLimit q
    return (decide (numDigits q ≤ a), true)

/-- `Decimal._divide`, _pydecimal.py:1428-1464: `(self // other, self % other)`
for finite `self` and non-zero `other`. -/
def divideD (c : Ctx) (a b : Dec) : DM (Dec × Dec) := do
  let sign := a.neg != b.neg
  let idealExp := if isinfinity b ≠ 0 then expOf a else min (expOf a) (expOf b)
  let expdiff := a.adjusted - b.adjusted
  if !decBool a || decide (isinfinity b ≠ 0) || decide (expdiff ≤ -2) then
    return (.fin sign 0 0, ← liftPy (rescale a idealExp c.rounding))
  if expdiff ≤ c.prec then
    match a, b with
    | .fin sa ca ea, .fin sb cb eb =>
      let _ ← liftPy (workRep (.fin sa ca ea))
      let _ ← liftPy (workRep (.fin sb cb eb))
      let p := scaled ca ea cb eb
      let q := p.1 / p.2
      let r := p.1 % p.2
      let res ← liftPy (isLessThanPow10aUseStr q c.prec)
      if res.1 then
        liftPy (if res.2 then .ok () else strLimit q)
        liftPy (strLimit r)
        return (.fin sign q 0, .fin sa r idealExp)
    | _, _ => pure ()
  let ans ← invalid c
  return (ans, ans)

/-- `Decimal.__divmod__`, _pydecimal.py:1473-1507. -/
def divmodD (c : Ctx) (a b : Dec) : DM (Dec × Dec) := do
  if let some ans ← checkNans c a (some b) then return (ans, ans)
  let sign := a.neg != b.neg
  if isinfinity a ≠ 0 then
    if isinfinity b ≠ 0 then
      let ans ← invalid c
      return (ans, ans)
    else
      return (.inf sign, ← invalid c)
  if !decBool b then
    if !decBool a then
      let ans ← invalid c
      return (ans, ans)
    else
      let q ← divByZero c sign
      let r ← invalid c
      return (q, r)
  let qr ← divideD c a b
  let r ← fix c qr.2
  return (qr.1, r)

/-- `Decimal.__mod__`, _pydecimal.py:1516-1541. -/
def modD (c : Ctx) (a b : Dec) : DM Dec := do
  if let some ans ← checkNans c a (some b) then return ans
  if isinfinity a ≠ 0 then return ← invalid c
  else if !decBool b then return ← invalid c
  let qr ← divideD c a b
  fix c qr.2

/-- `Decimal.__floordiv__`, _pydecimal.py:1627-1653. -/
def floordivD (c : Ctx) (a b : Dec) : DM Dec := do
  if let some ans ← checkNans c a (some b) then return ans
  if isinfinity a ≠ 0 then
    if isinfinity b ≠ 0 then return ← invalid c
    else return .inf (a.neg != b.neg)
  if !decBool b then
    if decBool a then return ← divByZero c (a.neg != b.neg)
    else return ← invalid c
  let qr ← divideD c a b
  return qr.1

/-- The adjustment of `remainder_near`, _pydecimal.py:1605-1611: `q, r = divmod(x, y)`,
then `if 2*r + (q&1) > y: r -= y; q += 1`. -/
def nearestQR (x y : Nat) : Nat × Int :=
  let q := x / y
  let r := x % y
  if 2 * r + q % 2 > y then (q + 1, (r : Int) - y) else (q, r)

/-- `Decimal.remainder_near`, _pydecimal.py:1550-1625. `_is_less_than_pow10a(q, prec)`
(:504-536), which replaced the test `q >= 10**prec` in 3.15, is taken as that test: it
rests on `math.log10` of a big int, which is not modelled. -/
def remainderNear (c : Ctx) (a b : Dec) : DM Dec := do
  if let some ans ← checkNans c a (some b) then return ans
  if isinfinity a ≠ 0 then return ← invalid c
  if !decBool b then return ← invalid c
  if isinfinity b ≠ 0 then return ← fix c a
  let idealExponent := min (expOf a) (expOf b)
  if !decBool a then return ← fix c (.fin a.neg 0 idealExponent)
  let expdiff := a.adjusted - b.adjusted
  if expdiff ≥ c.prec + 1 then return ← invalid c
  if expdiff ≤ -2 then
    return ← fix c (← liftPy (rescale a idealExponent c.rounding))
  match a, b with
  | .fin sa ca ea, .fin sb cb eb =>
    let _ ← liftPy (workRep (.fin sa ca ea))
    let _ ← liftPy (workRep (.fin sb cb eb))
    let p := scaled ca ea cb eb
    let qr := nearestQR p.1 p.2
    if qr.1 ≥ 10 ^ c.prec then return ← invalid c
    let sign := if qr.2 < 0 then !sa else sa
    liftPy (strLimit qr.2.natAbs)
    fix c (.fin sign qr.2.natAbs idealExponent)
  | _, _ => return a

end PyLean.Decimal
