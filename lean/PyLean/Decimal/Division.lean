import PyLean.Decimal.Ops

/-!
The division family of `_pydecimal`: `__truediv__`, `_divide`, `__divmod__`,
`__mod__`, `__floordiv__`, `remainder_near`.

The conditions `DivisionUndefined` and `DivisionImpossible` map to the signal
InvalidOperation (`_condition_map`, _pydecimal.py:333-336) and their handlers
return `_NaN` (:195-196, :206-207), which is `invalid`. `DivisionByZero.handle`
returns `_SignedInfinity[sign]` (:184-185).
-/

namespace PyLean.Decimal

open PyLean

/-- `_WorkRep(value)` of a finite Decimal, _pydecimal.py:5603-5616: `int(value._int)`. -/
def workRep : Dec → Py (Bool × Nat × Int)
  | .fin neg co e => do
    intLimit (numDigits co)
    return (neg, co, e)
  | _ => .ok (false, 0, 0)

/-- `context._raise_error(DivisionByZero, msg, sign)`, _pydecimal.py:184-185. -/
def divByZero (c : Ctx) (sign : Bool) : DM Dec := do
  raiseSig c .divisionByZero
  return .inf sign

/-- `while exp < ideal_exp and coeff % 10 == 0: coeff //= 10; exp += 1`,
_pydecimal.py:1329-1331, with the iteration bound `ideal_exp - exp`. -/
def stripIdeal (coeff : Nat) (exp ideal : Int) : Nat → Nat × Int
  | 0 => (coeff, exp)
  | f + 1 =>
    if exp < ideal ∧ coeff % 10 = 0 then stripIdeal (coeff / 10) (exp + 1) ideal f
    else (coeff, exp)

/-- The integer division of `__truediv__`, _pydecimal.py:1309-1331, for finite
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

/-- `Decimal.__truediv__`, _pydecimal.py:1277-1334. -/
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
_pydecimal.py:1355-1358 and :1504-1507: both operands as integers at the lower exponent. -/
def scaled (ca : Nat) (ea : Int) (cb : Nat) (eb : Int) : Nat × Nat :=
  if ea ≥ eb then (ca * 10 ^ (ea - eb).toNat, cb) else (ca, cb * 10 ^ (eb - ea).toNat)

/-- `Decimal._divide`, _pydecimal.py:1336-1367: `(self // other, self % other)`
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
      if q < 10 ^ c.prec then
        liftPy (strLimit q)
        liftPy (strLimit r)
        return (.fin sign q 0, .fin sa r idealExp)
    | _, _ => pure ()
  let ans ← invalid c
  return (ans, ans)

/-- `Decimal.__divmod__`, _pydecimal.py:1376-1410. -/
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

/-- `Decimal.__mod__`, _pydecimal.py:1419-1444. -/
def modD (c : Ctx) (a b : Dec) : DM Dec := do
  if let some ans ← checkNans c a (some b) then return ans
  if isinfinity a ≠ 0 then return ← invalid c
  else if !decBool b then return ← invalid c
  let qr ← divideD c a b
  fix c qr.2

/-- `Decimal.__floordiv__`, _pydecimal.py:1528-1554. -/
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

/-- The adjustment of `remainder_near`, _pydecimal.py:1508-1514: `q, r = divmod(x, y)`,
then `if 2*r + (q&1) > y: r -= y; q += 1`. -/
def nearestQR (x y : Nat) : Nat × Int :=
  let q := x / y
  let r := x % y
  if 2 * r + q % 2 > y then (q + 1, (r : Int) - y) else (q, r)

/-- `Decimal.remainder_near`, _pydecimal.py:1453-1526. -/
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
