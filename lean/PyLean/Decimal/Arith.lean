import PyLean.Decimal.Basic
import PyLean.Fractions.Hash

/-!
Context-dependent operations of `_pydecimal`: rounding (`_round_*`,
`_rescale`, `_fix`), `quantize`, `to_integral_*`, `__round__`, the integer
conversions, `normalize`, `+`, `-`, `*`, `compare_total`, `copy_sign`,
`as_integer_ratio`, `__hash__`, `Decimal(int)`, plus the C twin's versions of
the conversions whose code differs structurally (`hash`, `int`, `floor`,
`ceil`, `round`, `as_integer_ratio`, `Decimal(int)`).

`_pydecimal` keeps the coefficient as a digit string `_int`. Slicing it is
modelled arithmetically: for a coefficient `c` and `k ≥ 1` dropped digits,
`_int[:len-k]` is `c / 10^k`, the dropped digits read as a number are
`c % 10^k`, and the string `'5' + '0'*(k-1)` (`_exact_half`) is `5·10^(k-1)`.
Every `int(s)` / `str(i)` / `len(str(i))` on a coefficient goes through
`intLimit` / `strLimit`, which raise `ValueError` past 4300 digits.

Signals (`Context._raise_error`, _pydecimal.py:4005-4025) set a flag and
raise when the signal is trapped; the monad `DM` threads the flags and the
exception. When a trap fires the flags are not compared (the C twin sets all
of an operation's flags before raising; `_pydecimal` stops at the first
trapped one, a difference `Modules/_decimal/tests/deccheck.py:293-297`
deliberately excludes).
-/

namespace PyLean.Decimal

open PyLean

inductive Rounding where
  | up | down | ceiling | floor | halfUp | halfDown | halfEven | r05up
  deriving Repr, DecidableEq, Inhabited

inductive Signal where
  | clamped | invalidOperation | divisionByZero | inexact | rounded | subnormal | overflow | underflow
  | floatOperation
  deriving Repr, DecidableEq, Inhabited

def Signal.name : Signal → String
  | .clamped => "Clamped" | .invalidOperation => "InvalidOperation"
  | .divisionByZero => "DivisionByZero" | .inexact => "Inexact" | .rounded => "Rounded"
  | .subnormal => "Subnormal" | .overflow => "Overflow" | .underflow => "Underflow"
  | .floatOperation => "FloatOperation"

/-- A `Context` (only the fields the modelled operations read). Type
invariant (enforced by `Context.__init__`/`_set_integer_check`,
_pydecimal.py:3905-3953): `prec ≥ 1`, `emin ≤ 0 ≤ emax`. -/
structure Ctx where
  prec : Nat := 28
  rounding : Rounding := .halfEven
  emin : Int := -999999
  emax : Int := 999999
  capitals : Bool := true
  clamp : Bool := false
  traps : List Signal := [.divisionByZero, .overflow, .invalidOperation]
  deriving Repr, Inhabited

def Ctx.etiny (c : Ctx) : Int := c.emin - c.prec + 1
def Ctx.etop (c : Ctx) : Int := c.emax - c.prec + 1

/-- Computations that set context flags and may raise. -/
abbrev DM := StateT (List Signal) Py

def liftPy {α : Type} (x : Py α) : DM α := fun fl => (·, fl) <$> x

/-- `context._raise_error(s)`: set the flag; raise if trapped. -/
def raiseSig (c : Ctx) (s : Signal) : DM Unit := do
  modify (fun fl => if s ∈ fl then fl else fl ++ [s])
  if s ∈ c.traps then throw (.named s.name "~")

/-! ## Rounding -/

/-- The rounding functions `_round_down` ... `_round_05up`
(_pydecimal.py:1716-1781) on a coefficient whose kept prefix is `q`, whose
dropped digits read as `r`, with `h = 5·10^(k-1)` for `k` dropped digits.
`1`: round away from zero; `0`: exact; `-1`: truncate inexactly. -/
def roundDir (m : Rounding) (neg : Bool) (q r h : Nat) : Int :=
  let down : Int := if r = 0 then 0 else -1         -- _all_zeros(_int, prec)
  let halfUp : Int := if r ≥ h then 1 else down       -- _int[prec] in '56789'
  match m with
  | .down => down
  | .up => -down
  | .halfUp => halfUp
  | .halfDown => if r = h then -1 else halfUp          -- _exact_half
  | .halfEven => if r = h ∧ q % 2 = 0 then -1 else halfUp
  | .ceiling => if neg then down else -down
  | .floor => if !neg then down else -down
  | .r05up => if q % 5 ≠ 0 then down else -down       -- _int[prec-1] not in '05'

/-- Keep `digits` leading digits of `co` (Python's `self._int[:digits]`)
under rounding `m`: `(q, changed)` with `q = int(_int[:digits] or '0')`. -/
def roundKeep (m : Rounding) (neg : Bool) (co digits : Nat) : Nat × Int :=
  let k := numDigits co - digits
  let q := co / 10 ^ k
  (q, roundDir m neg q (co % 10 ^ k) (5 * 10 ^ (k - 1)))

/-- `coeff = str(int(coeff) + 1)` for `coeff = _int[:digits] or '0'`. -/
def incr (q digits : Nat) : Py Nat := do
  intLimit (max digits 1)
  strLimit (q + 1)
  return q + 1

/-- `Decimal._rescale(exp, rounding)`, _pydecimal.py:2576-2608. Quiet. -/
def rescale (d : Dec) (exp : Int) (m : Rounding) : Py Dec :=
  match d with
  | .fin neg co e =>
    if co = 0 then .ok (.fin neg 0 exp)
    else if e ≥ exp then .ok (.fin neg (co * 10 ^ (e - exp).toNat) exp)
    else do
      let digits : Int := numDigits co + e - exp
      -- if digits < 0: self = _dec_from_triple(self._sign, '1', exp-1); digits = 0
      let (co', dg) := if digits < 0 then (1, 0) else (co, digits.toNat)
      let (q, changed) := roundKeep m neg co' dg
      if changed = 1 then return .fin neg (← incr q dg) exp
      else return .fin neg q exp
  | d => .ok d

/-! ## `_fix` -/

/-- `_fix_nan`, _pydecimal.py:1602-1612: keep the last `prec - clamp` digits
of the payload. -/
def fixNan (c : Ctx) (neg sig : Bool) (p : Nat) : Dec :=
  let maxLen := c.prec - (if c.clamp then 1 else 0)
  if numDigits p > maxLen ∧ p ≠ 0 then .nan neg sig (p % 10 ^ maxLen) else .nan neg sig p

/-- `Overflow.handle`, _pydecimal.py:281-294. -/
def overflowResult (c : Ctx) (neg : Bool) : Dec :=
  let maxv := Dec.fin neg (10 ^ c.prec - 1) (c.emax - c.prec + 1)
  match c.rounding with
  | .halfUp | .halfEven | .halfDown | .up => .inf neg
  | .ceiling => if neg then maxv else .inf neg
  | .floor => if neg then .inf neg else maxv
  | _ => maxv

def isZero : Dec → Bool
  | .fin _ 0 _ => true
  | _ => false

/-- `digits`, and the replacement of `self` by `10^(exp_min-1)` when it is
negative, _pydecimal.py:1661-1664. -/
def fixDigits (co : Nat) (e expMin : Int) : Nat × Nat :=
  let digits : Int := numDigits co + e - expMin
  if digits < 0 then (1, 0) else (co, digits.toNat)

/-- The increment and renormalization, _pydecimal.py:1667-1672. -/
def fixCarry (c : Ctx) (q : Nat) (changed : Int) (dg : Nat) (expMin : Int) : DM (Nat × Int) :=
  if changed > 0 then do
    let q1 ← liftPy (incr q dg)
    if numDigits q1 > c.prec then pure (q1 / 10, expMin + 1) else pure (q1, expMin)
  else pure (q, expMin)

/-- The result and its signals, _pydecimal.py:1675-1692. -/
def fixFinish (c : Ctx) (neg : Bool) (coeff : Nat) (expMin : Int) (changed : Int) (sub : Bool) : DM Dec := do
  let ans ← if expMin > c.etop then do
      raiseSig c .overflow
      pure (overflowResult c neg)
    else pure (.fin neg coeff expMin)
  if changed ≠ 0 ∧ sub then raiseSig c .underflow
  if sub then raiseSig c .subnormal
  if changed ≠ 0 then raiseSig c .inexact
  raiseSig c .rounded
  if isZero ans then raiseSig c .clamped
  return ans

/-- The rounding branch of `_fix`, _pydecimal.py:1660-1692. -/
def fixRound (c : Ctx) (neg : Bool) (co : Nat) (e expMin : Int) (sub : Bool) : DM Dec := do
  let p := fixDigits co e expMin
  let r := roundKeep c.rounding neg p.1 p.2
  let t ← fixCarry c r.1 r.2 p.2 expMin
  fixFinish c neg t.1 t.2 r.2 sub

/-- `Decimal._fix(context)`, _pydecimal.py:1614-1704. -/
def fix (c : Ctx) : Dec → DM Dec
  | .nan neg sig p => pure (fixNan c neg sig p)
  | .inf neg => pure (.inf neg)
  | .fin neg co e => do
    let etiny := c.etiny
    let etop := c.etop
    if co = 0 then
      let expMax := if c.clamp then etop else c.emax
      let newExp := min (max e etiny) expMax
      if newExp ≠ e then
        raiseSig c .clamped
        return .fin neg 0 newExp
      else return .fin neg 0 e
    let expMin0 : Int := numDigits co + e - c.prec
    if expMin0 > etop then
      raiseSig c .overflow
      raiseSig c .inexact
      raiseSig c .rounded
      return overflowResult c neg
    let sub := decide (expMin0 < etiny)
    let expMin := if sub then etiny else expMin0
    if e < expMin then fixRound c neg co e expMin sub else
    if sub then raiseSig c .subnormal
    if c.clamp ∧ e > etop then
      raiseSig c .clamped
      return .fin neg (co * 10 ^ (e - etop).toNat) etop
    return .fin neg co e

/-- `_check_nans(other, context)`, _pydecimal.py:698-728: `none` when no
operand is a NaN. A signaling NaN raises InvalidOperation, whose handler
returns the quiet NaN with the same sign and payload. -/
def checkNans (c : Ctx) (a : Dec) (b : Option Dec) : DM (Option Dec) :=
  match a, b with
  | .nan neg true p, _ => do raiseSig c .invalidOperation; return some (fixNan c neg false p)
  | _, some (.nan neg true p) => do raiseSig c .invalidOperation; return some (fixNan c neg false p)
  | .nan neg false p, _ => return some (fixNan c neg false p)
  | _, some (.nan neg false p) => return some (fixNan c neg false p)
  | _, _ => return none

/-- `context._raise_error(InvalidOperation, ...)` without an sNaN argument:
the result is a positive quiet NaN. -/
def invalid (c : Ctx) : DM Dec := do raiseSig c .invalidOperation; return .nan false false 0

/-! ## Value comparison (`_cmp`, _pydecimal.py:770-832, for non-NaNs) -/

/-- `(-1)**sign` as an ordering. -/
def signOrd (neg : Bool) : Ordering := if neg then .lt else .gt

/-- `Decimal._cmp`, _pydecimal.py:770-832, for operands that are not NaNs.
When the adjusted exponents agree, the zero-padded digit strings have equal
length, so comparing them as strings compares them as numbers. -/
def cmpVal : Dec → Dec → Ordering
  | .inf n1, .inf n2 => if n1 = n2 then .eq else if n1 then .lt else .gt
  | .inf n1, _ => if n1 then .lt else .gt
  | _, .inf n2 => if n2 then .gt else .lt
  | .fin n1 c1 e1, .fin n2 c2 e2 =>
    if c1 = 0 then (if c2 = 0 then .eq else (signOrd n2).swap)
    else if c2 = 0 then signOrd n1
    else if n2 && !n1 then .gt
    else if n1 && !n2 then .lt
    else
      let a1 := e1 + numDigits c1 - 1
      let a2 := e2 + numDigits c2 - 1
      if a1 = a2 then
        let p1 := c1 * 10 ^ (e1 - e2).toNat
        let p2 := c2 * 10 ^ (e2 - e1).toNat
        if p1 = p2 then .eq else if p1 < p2 then (signOrd n1).swap else signOrd n1
      else if a1 > a2 then signOrd n1 else (signOrd n1).swap
  | _, _ => .eq

/-! ## quantize, to_integral, round -/

def adjustedD (co : Nat) (e : Int) : Int := e + numDigits co - 1

/-- The tail of `quantize`, _pydecimal.py:2551-2559: Inexact and Rounded, then `_fix`. -/
def quantizeFlags (c : Ctx) (ans : Dec) (ae : Int) (neg : Bool) (co : Nat) (e : Int) : DM Dec := do
  if ae > e then
    if cmpVal ans (.fin neg co e) ≠ .eq then raiseSig c .inexact
    raiseSig c .rounded
  fix c ans

/-- The finite-operand part of `quantize` after the checks on rounding,
_pydecimal.py:2523-2559: the operand is `±co·10^e`, the target exponent `qe`. -/
def quantizeFin (c : Ctx) (m : Rounding) (neg : Bool) (co : Nat) (e qe : Int) : DM Dec := do
  if ¬(c.etiny ≤ qe ∧ qe ≤ c.emax) then return (← invalid c)
  if co = 0 then return (← fix c (.fin neg 0 qe))
  let adj := adjustedD co e
  if adj > c.emax then return (← invalid c)
  if adj - qe + 1 > c.prec then return (← invalid c)
  let ans ← liftPy (rescale (.fin neg co e) qe m)
  match ans with
  | .fin _ aco ae =>
    if adjustedD aco ae > c.emax then return (← invalid c)
    if numDigits aco > c.prec then return (← invalid c)
    if aco ≠ 0 ∧ adjustedD aco ae < c.emin then raiseSig c .subnormal
    quantizeFlags c ans ae neg co e
  | _ => return ans

/-- `Decimal.quantize(exp, rounding, context)`, _pydecimal.py:2500-2559. -/
def quantize (c : Ctx) (a q : Dec) (rnd : Option Rounding := none) : DM Dec := do
  let m := rnd.getD c.rounding
  match a, q with
  | .fin neg co e, .fin _ _ qe => quantizeFin c m neg co e qe
  | _, _ =>
    if let some ans ← checkNans c a (some q) then return ans
    match a, q with
    | .inf _, .inf _ => return a
    | _, _ => invalid c

/-- `to_integral_value(rounding, context)`, _pydecimal.py:2662-2676. -/
def toIntegralValue (c : Ctx) (a : Dec) (rnd : Option Rounding := none) : DM Dec := do
  let m := rnd.getD c.rounding
  match a with
  | .fin _ _ e => if e ≥ 0 then return a else liftPy (rescale a 0 m)
  | _ => return ((← checkNans c a none).getD a)

/-- `to_integral_exact(rounding, context)`, _pydecimal.py:2633-2660. -/
def toIntegralExact (c : Ctx) (a : Dec) (rnd : Option Rounding := none) : DM Dec := do
  match a with
  | .fin neg co e =>
    if e ≥ 0 then return a
    if co = 0 then return .fin neg 0 0
    let ans ← liftPy (rescale a 0 (rnd.getD c.rounding))
    if cmpVal ans a ≠ .eq then raiseSig c .inexact
    raiseSig c .rounded
    return ans
  | _ => return ((← checkNans c a none).getD a)

/-- `round(d, n)`, _pydecimal.py:1830-1835: `self.quantize(Decimal((0, (1,), -n)))`. -/
def roundN (c : Ctx) (a : Dec) (n : Int) : DM Dec := quantize c a (.fin false 1 (-n))

/-- Python truncating division toward zero of an int by `10^k`. -/
def truncDiv (neg : Bool) (v : Nat) : Int := if neg then -(v : Int) else v

/-- `Decimal.__int__`, _pydecimal.py:1573-1584. -/
def pyInt : Dec → Py Int
  | .nan _ _ _ => .error (.valueError "Cannot convert NaN to integer")
  | .inf _ => .error (.overflowError "Cannot convert infinity to integer")
  | .fin neg co e => do
    if e ≥ 0 then
      intLimit (numDigits co)
      return truncDiv neg (co * 10 ^ e.toNat)
    else
      -- int(self._int[:self._exp] or '0')
      let kept : Int := numDigits co + e
      intLimit (if kept ≤ 0 then 1 else kept.toNat)
      return truncDiv neg (co / 10 ^ e.natAbs)

/-- `__round__()`, `__floor__`, `__ceil__` (_pydecimal.py:1837-1873):
`int(self._rescale(0, mode))`. -/
def pyToInt (m : Rounding) : Dec → Py Int
  | .nan _ _ _ => .error (.valueError "cannot round a NaN")
  | .inf _ => .error (.overflowError "cannot round an infinity")
  | d => do pyInt (← rescale d 0 m)

/-! ## normalize, copy_sign, compare_total -/

/-- `Decimal.normalize(context)`, _pydecimal.py:2475-2498. -/
def normalize (c : Ctx) (a : Dec) : DM Dec := do
  if let .fin _ _ _ := a then pure () else
    if let some ans ← checkNans c a none then return ans
  let dup ← fix c a
  match dup with
  | .fin neg co e =>
    if co = 0 then return .fin neg 0 0
    let expMax := if c.clamp then c.etop else c.emax
    let rec strip (co : Nat) (e : Int) (fuel : Nat) : Nat × Int :=
      match fuel with
      | 0 => (co, e)
      | f + 1 => if co % 10 = 0 ∧ e < expMax then strip (co / 10) (e + 1) f else (co, e)
    let (co', e') := strip co e (numDigits co)
    return .fin neg co' e'
  | d => return d

def Dec.neg : Dec → Bool
  | .fin n _ _ | .inf n | .nan n _ _ => n

def Dec.withSign (d : Dec) (n : Bool) : Dec :=
  match d with
  | .fin _ c e => .fin n c e
  | .inf _ => .inf n
  | .nan _ s p => .nan n s p

/-- `copy_sign`, _pydecimal.py:2995-2999. -/
def copySign (a b : Dec) : Dec := a.withSign b.neg

/-- NaN kind as `_isnan()` reports it: 0, 1 (quiet), 2 (signaling). -/
def nanKind : Dec → Nat
  | .nan _ false _ => 1
  | .nan _ true _ => 2
  | _ => 0

def payloadOf : Dec → Nat
  | .nan _ _ p => p
  | _ => 0

def expOf : Dec → Int
  | .fin _ _ e => e
  | _ => 0

/-- `compare_total` once both operands have the sign `sign`,
_pydecimal.py:2913-2969. -/
def compareTotalSame (sign : Bool) (a b : Dec) : Int :=
  let flip (x : Int) : Int := if sign then -x else x
  let na := nanKind a
  let nb := nanKind b
  if na ≠ 0 ∨ nb ≠ 0 then
    if na = nb then
      -- payloads compared by (len(_int), _int), i.e. as integers
      if payloadOf a < payloadOf b then flip (-1)
      else if payloadOf a > payloadOf b then flip 1 else 0
    else if na = 1 then flip 1
    else if nb = 1 then flip (-1)
    else if na = 2 then flip 1
    else flip (-1)
  else
    match cmpVal a b with
    | .lt => -1
    | .gt => 1
    | .eq =>
      if expOf a < expOf b then flip (-1) else if expOf a > expOf b then flip 1 else 0

/-- `compare_total`, _pydecimal.py:2899-2969, as -1/0/1. -/
def compareTotal (a b : Dec) : Int :=
  match a.neg, b.neg with
  | true, false => -1
  | false, true => 1
  | sign, _ => compareTotalSame sign a b

/-! ## Arithmetic (`Decimal.__add__`, `__sub__`, `__mul__`) -/

/-- `_normalize(op1, op2, prec)`, _pydecimal.py:5623-5649, on `_WorkRep`s
`(sign, int, exp)`. -/
def workNormalize (prec : Nat) (o1 o2 : Bool × Nat × Int) :
    Py ((Bool × Nat × Int) × (Bool × Nat × Int)) := do
  let swap := decide (o1.2.2 < o2.2.2)
  let (tmp, other) := if swap then (o2, o1) else (o1, o2)
  strLimit tmp.2.1
  strLimit other.2.1
  let tmpLen := numDigits tmp.2.1
  let otherLen := numDigits other.2.1
  let exp := tmp.2.2 + min (-1) ((tmpLen : Int) - prec - 2)
  let other := if (otherLen : Int) + other.2.2 - 1 < exp then (other.1, 1, exp) else other
  let tmp := (tmp.1, tmp.2.1 * 10 ^ (tmp.2.2 - other.2.2).toNat, other.2.2)
  return if swap then (other, tmp) else (tmp, other)

/-- `Decimal.__add__(other, context)`, _pydecimal.py:1110-1194. -/
def add (c : Ctx) (a b : Dec) : DM Dec := do
  match a, b with
  | .fin _ _ _, .fin _ _ _ => pure ()
  | _, _ =>
    if let some ans ← checkNans c a (some b) then return ans
  match a, b with
  | .inf na, _ =>
    match b with
    | .inf nb => if na ≠ nb then invalid c else return a
    | _ => return a
  | _, .inf _ => return b
  | .fin sa ca ea, .fin sb cb eb =>
    let exp := min ea eb
    let negativezero := c.rounding = .floor ∧ sa ≠ sb
    if ca = 0 ∧ cb = 0 then
      let sign := (sa && sb) || negativezero
      return (← fix c (.fin sign 0 exp))
    if ca = 0 then
      let exp := max exp (eb - c.prec - 1)
      return (← fix c (← liftPy (rescale b exp c.rounding)))
    if cb = 0 then
      let exp := max exp (ea - c.prec - 1)
      return (← fix c (← liftPy (rescale a exp c.rounding)))
    -- _WorkRep: self.int = int(value._int)
    liftPy (intLimit (numDigits ca))
    liftPy (intLimit (numDigits cb))
    let (op1, op2) ← liftPy (workNormalize c.prec (sa, ca, ea) (sb, cb, eb))
    if op1.1 ≠ op2.1 then
      if op1.2.1 = op2.2.1 then return (← fix c (.fin negativezero 0 exp))
      let (big, small) := if op1.2.1 < op2.2.1 then (op2, op1) else (op1, op2)
      let rint := big.2.1 - small.2.1
      liftPy (strLimit rint)
      fix c (.fin big.1 rint big.2.2)
    else
      let rint := op1.2.1 + op2.2.1
      liftPy (strLimit rint)
      fix c (.fin op1.1 rint op1.2.2)
  | _, _ => return a

def negate (d : Dec) : Dec := d.withSign (!d.neg)

/-- `Decimal.__sub__`, _pydecimal.py:1198-1210. -/
def sub (c : Ctx) (a b : Dec) : DM Dec := do
  match a, b with
  | .fin _ _ _, .fin _ _ _ => pure ()
  | _, _ =>
    if let some ans ← checkNans c a (some b) then return ans
  add c a (negate b)

/-- The finite operands of `__mul__`, _pydecimal.py:1249-1272. -/
def mulFin (c : Ctx) (rs : Bool) (ca : Nat) (ea : Int) (cb : Nat) (eb : Int) : DM Dec := do
  let re := ea + eb
  if ca = 0 ∨ cb = 0 then return (← fix c (.fin rs 0 re))
  if ca = 1 then return (← fix c (.fin rs cb re))
  if cb = 1 then return (← fix c (.fin rs ca re))
  liftPy (intLimit (numDigits ca))
  liftPy (intLimit (numDigits cb))
  liftPy (strLimit (ca * cb))
  fix c (.fin rs (ca * cb) re)

/-- `Decimal.__mul__`, _pydecimal.py:1220-1274. -/
def mul (c : Ctx) (a b : Dec) : DM Dec := do
  let rs := a.neg != b.neg
  match a, b with
  | .fin _ ca ea, .fin _ cb eb => mulFin c rs ca ea cb eb
  | _, _ =>
    if let some ans ← checkNans c a (some b) then return ans
    match a, b with
    | .inf _, _ => if isZero b then invalid c else return .inf rs
    | _, .inf _ => if isZero a then invalid c else return .inf rs
    | _, _ => return a

/-! ## Hashing, ratios, construction from int -/

/-- The hash of a finite decimal once its coefficient is an int:
`coeff * 10^exp mod P` (with `pow(_PyHASH_10INV, -exp, P)` for a negative
exponent), negated for a negative non-zero value, `-1 → -2`
(_pydecimal.py:914-920). This is `PyLean.Fractions.decimalHash`, whose
`tenInv` is `_PyHASH_10INV = pow(10, P - 2, P)` (_pydecimal.py:6405). -/
abbrev hashFinite (neg : Bool) (co : Nat) (e : Int) : Int := PyLean.Fractions.decimalHash neg co e

def hashInf : Int := PyLean.Fractions.hashInf
def intHash (n : Int) : Int := PyLean.Fractions.intHash n

/-- `_pydecimal.Decimal.__hash__`, _pydecimal.py:896-920. NaNs hash by
identity (not modelled: `none`). -/
def pyHash : Dec → Py (Option Int)
  | .nan _ true _ => .error (.typeError "Cannot hash a signaling NaN value.")
  | .nan _ false _ => .ok none
  | .inf neg => .ok (some (if neg then -hashInf else hashInf))
  | .fin neg co e => do
    intLimit (numDigits co)      -- int(self._int)
    return some (hashFinite neg co e)

/-- `_decimal`'s `_dec_hash`, _decimal.c:4896-5008: the same formula computed
with libmpdec (`mpd_qpowmod` with the literal `inv10_p = 2075258708292324556`,
`mpd_qmul`, `mpd_qrem` under an extended max context), so no string
conversion is involved. (`inv10_p` is `tenInv`: `tenInv_eq` below.) -/
def cHash : Dec → Py (Option Int)
  | .nan _ true _ => .error (.typeError "Cannot hash a signaling NaN value")
  | .nan _ false _ => .ok none
  | .inf neg => .ok (some (if neg then -hashInf else hashInf))
  | .fin neg co e => .ok (some (hashFinite neg co e))

/-- `as_integer_ratio`, _pydecimal.py:929-977. The source strips factors of 5 and
of 2 from `n` and `10^-exp` in turn (:960-973), which yields the fraction in
lowest terms; the model writes that fraction with a gcd. -/
def pyRatio : Dec → Py (Int × Int)
  | .nan _ _ _ => .error (.valueError "cannot convert NaN to integer ratio")
  | .inf _ => .error (.overflowError "cannot convert Infinity to integer ratio")
  | .fin neg co e => do
    if co = 0 then return (0, 1)
    intLimit (numDigits co)
    let (n, d) : Nat × Nat :=
      if e ≥ 0 then (co * 10 ^ e.toNat, 1)
      else
        let g := Nat.gcd co (10 ^ e.natAbs)
        (co / g, 10 ^ e.natAbs / g)
    return (if neg then -(n : Int) else n, d)

/-- `_decimal`'s `as_integer_ratio` (`dec_as_integer_ratio`, _decimal.c:3770-3870): numerator and
`10^-exp` reduced by their gcd, via libmpdec. -/
def cRatio : Dec → Py (Int × Int)
  | .nan _ _ _ => .error (.valueError "cannot convert NaN to integer ratio")
  | .inf _ => .error (.overflowError "cannot convert Infinity to integer ratio")
  | .fin neg co e =>
    let (n, d) : Nat × Nat :=
      if e ≥ 0 then (co * 10 ^ e.toNat, 1)
      else
        let g := Nat.gcd co (10 ^ e.natAbs)
        (co / g, 10 ^ e.natAbs / g)
    .ok (if neg then -(n : Int) else n, d)

/-- Integer value of a finite decimal rounded with mode `m` (exact math):
`mpd_qround_to_int` then the digit export of `dec_as_long`
(_decimal.c:3684-3760). -/
def roundToIntExact (m : Rounding) (neg : Bool) (co : Nat) (e : Int) : Int :=
  if e ≥ 0 then truncDiv neg (co * 10 ^ e.toNat)
  else
    let k := e.natAbs
    let q := co / 10 ^ k
    let r := co % 10 ^ k
    let ch := roundDir m neg q r (5 * 10 ^ (k - 1))
    truncDiv neg (if ch = 1 then q + 1 else q)

/-- `_decimal`'s `int()`, `math.floor`, `math.ceil`, `round()`
(`dec_as_long` with ROUND_DOWN, FLOOR, CEILING, HALF_EVEN). -/
def cToInt (m : Rounding) : Dec → Py Int
  | .nan _ _ _ => .error (.valueError "cannot convert NaN to integer")
  | .inf _ => .error (.overflowError "cannot convert Infinity to integer")
  | .fin neg co e => .ok (roundToIntExact m neg co e)

/-- `_pydecimal.Decimal(int)`, _pydecimal.py:523-532: `str(abs(value))`. -/
def pyFromInt (n : Int) : Py Dec := do
  strLimit n.natAbs
  return .fin (n < 0) n.natAbs 0

/-- `_decimal.Decimal(int)`, `dec_from_long` (_decimal.c:2361-2402),
importing the digits with `mpd_qimport_u32`. -/
def cFromInt (n : Int) : Py Dec := .ok (.fin (n < 0) n.natAbs 0)

end PyLean.Decimal
