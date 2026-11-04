import PyLean.Decimal.Tuple
import PyLean.Decimal.Arith

/-!
The remaining `Decimal` methods of `_pydecimal` that take no division or power:
unary operators, predicates, comparisons, `max`/`min`, the logical operations,
`rotate`, `shift`, `scaleb`, `next_*`, `logb`, `fma`, the engineering string.

Each function follows its source branch by branch. As in `Arith.lean`, slices of
the digit string `_int` are arithmetic: for a coefficient below `10^p` padded to
`p` digits, `_int[:-k]` is `c / 10^k` and `_int[-k:]` is `c % 10^k`.
-/

namespace PyLean.Decimal

open PyLean

/-! ## Attributes and predicates -/

/-- `_dec_from_triple(sign, coefficient, 0..)` for a finite value, _pydecimal.py:3911-3925. -/
def decFromTriple (neg : Bool) (co : Nat) (e : Int) : Dec := .fin neg co e

/-- `Decimal.__bool__`, _pydecimal.py:855-860. -/
def decBool (d : Dec) : Bool := !isZero d

/-- `Decimal._isnan`, _pydecimal.py:762-775. -/
def isnan : Dec → Nat := nanKind

/-- `Decimal._isinfinity`, _pydecimal.py:777-788. -/
def isinfinity : Dec → Int
  | .inf neg => if neg then -1 else 1
  | _ => 0

/-- `Decimal.adjusted`, _pydecimal.py:2971-2977: `0` for specials. -/
def Dec.adjusted : Dec → Int
  | .fin _ c e => adjustedD c e
  | _ => 0

def isSpecial : Dec → Bool
  | .fin _ _ _ => false
  | _ => true

/-- `Decimal.is_nan`, `is_qnan`, `is_snan`, `is_infinite`, `is_finite`,
`is_signed`, `is_zero`, `is_canonical`, _pydecimal.py:3176-3230. -/
def isNanP (d : Dec) : Bool := decide (isnan d ≠ 0)
def isQnan (d : Dec) : Bool := decide (isnan d = 1)
def isSnan (d : Dec) : Bool := decide (isnan d = 2)
def isInfinite (d : Dec) : Bool := decide (isinfinity d ≠ 0)
def isFinite (d : Dec) : Bool := !isSpecial d
def isSigned (d : Dec) : Bool := d.neg
def isCanonical (_ : Dec) : Bool := true

/-- `Decimal.is_normal`, _pydecimal.py:3200-3206. -/
def isNormal (c : Ctx) (d : Dec) : Bool :=
  if isSpecial d || !decBool d then false else decide (c.emin ≤ d.adjusted)

/-- `Decimal.is_subnormal`, _pydecimal.py:3220-3226. -/
def isSubnormal (c : Ctx) (d : Dec) : Bool :=
  if isSpecial d || !decBool d then false else decide (d.adjusted < c.emin)

/-- `Decimal.number_class`, _pydecimal.py:3667-3707. -/
def numberClass (c : Ctx) (d : Dec) : String :=
  if isSnan d then "sNaN" else if isQnan d then "NaN"
  else if isinfinity d = 1 then "+Infinity" else if isinfinity d = -1 then "-Infinity"
  else if isZero d then (if d.neg then "-Zero" else "+Zero")
  else if isSubnormal c d then (if d.neg then "-Subnormal" else "+Subnormal")
  else if d.neg then "-Normal" else "+Normal"

/-- `Decimal.radix`, `canonical`, `conjugate`, `real`, `imag`,
_pydecimal.py:3709-3711, :2979-2985, :1695-1696, :1688-1693: `radix` is
`Decimal(10)`, the next three return `self`, `imag` is `Decimal(0)`. -/
def radixD : Dec := .fin false 10 0
def canonicalD (d : Dec) : Dec := d
def conjugateD (d : Dec) : Dec := d
def realD (d : Dec) : Dec := d
def imagD (_ : Dec) : Dec := .fin false 0 0

/-- `Decimal.same_quantum`, _pydecimal.py:2661-2674. -/
def sameQuantum : Dec → Dec → Bool
  | .fin _ _ e1, .fin _ _ e2 => e1 == e2
  | a, b => (isNanP a && isNanP b) || (isInfinite a && isInfinite b)

/-- `Decimal.copy_abs`, `copy_negate`, _pydecimal.py:3084-3093. -/
def copyAbs (d : Dec) : Dec := d.withSign false
def copyNegate (d : Dec) : Dec := negate d

/-! ## Unary operators -/

/-- `Decimal.__neg__`, _pydecimal.py:1137-1157. -/
def dunderNeg (c : Ctx) (a : Dec) : DM Dec := do
  if isSpecial a then
    if let some ans ← checkNans c a none then return ans
  let ans := if !decBool a && c.rounding != .floor then copyAbs a else copyNegate a
  fix c ans

/-- `Decimal.__pos__`, _pydecimal.py:1159-1178. -/
def dunderPos (c : Ctx) (a : Dec) : DM Dec := do
  if isSpecial a then
    if let some ans ← checkNans c a none then return ans
  let ans := if !decBool a && c.rounding != .floor then copyAbs a else a
  fix c ans

/-- `Decimal.__abs__`, _pydecimal.py:1180-1200. -/
def dunderAbs (c : Ctx) (a : Dec) (round : Bool := true) : DM Dec := do
  if !round then return copyAbs a
  if isSpecial a then
    if let some ans ← checkNans c a none then return ans
  if a.neg then dunderNeg c a else dunderPos c a

/-! ## Comparisons -/

/-- The NaN operand a comparison reports, `InvalidOperation.handle` with an
argument, _pydecimal.py:158-162: the same sign and payload, quiet. -/
def quietOf (c : Ctx) : Dec → Dec
  | .nan neg _ p => fixNan c neg false p
  | d => d

/-- `Decimal._compare_check_nans`, _pydecimal.py:822-853: an ordering with any
NaN signals InvalidOperation. -/
def compareCheckNans (c : Ctx) (a b : Dec) : DM (Option Dec) := do
  if isSpecial a || isSpecial b then
    if isSnan a then do raiseSig c .invalidOperation; return some (quietOf c a)
    else if isSnan b then do raiseSig c .invalidOperation; return some (quietOf c b)
    else if isQnan a then do raiseSig c .invalidOperation; return some (quietOf c a)
    else if isQnan b then do raiseSig c .invalidOperation; return some (quietOf c b)
    else return none
  else return none

/-- `_cmp` as the int Python returns. -/
def cmpInt (a b : Dec) : Int :=
  match cmpVal a b with
  | .lt => -1
  | .eq => 0
  | .gt => 1

/-- `Decimal.__eq__`, _pydecimal.py:926-932, for Decimal operands. -/
def dunderEq (c : Ctx) (a b : Dec) : DM Bool := do
  if (← checkNans c a (some b)).isSome then return false
  return cmpInt a b == 0

/-- `Decimal.__lt__`, `__le__`, `__gt__`, `__ge__`, _pydecimal.py:934-968, for
Decimal operands. -/
def dunderOrd (test : Int → Bool) (c : Ctx) (a b : Dec) : DM Bool := do
  if (← compareCheckNans c a b).isSome then return false
  return test (cmpInt a b)

def dunderLt := dunderOrd (fun x => decide (x < 0))
def dunderLe := dunderOrd (fun x => decide (x ≤ 0))
def dunderGt := dunderOrd (fun x => decide (x > 0))
def dunderGe := dunderOrd (fun x => decide (x ≥ 0))

/-- `Decimal(i)` for `i` in `-1, 0, 1`. -/
def decOfInt (i : Int) : Dec := .fin (i < 0) i.natAbs 0

/-- `Decimal.compare`, _pydecimal.py:970-986. -/
def compareD (c : Ctx) (a b : Dec) : DM Dec := do
  if isSpecial a || isSpecial b then
    if let some ans ← checkNans c a (some b) then return ans
  return decOfInt (cmpInt a b)

/-- `Decimal.compare_signal`, _pydecimal.py:2987-2997. -/
def compareSignal (c : Ctx) (a b : Dec) : DM Dec := do
  if let some ans ← compareCheckNans c a b then return ans
  compareD c a b

/-- `Decimal.compare_total_mag`, _pydecimal.py:3072-3082. -/
def compareTotalMag (a b : Dec) : Int := compareTotal (copyAbs a) (copyAbs b)

/-! ## `max`, `min`, `max_mag`, `min_mag` -/

/-- The NaN handling these four share, _pydecimal.py:2891-2901: `none` to go on. -/
def minmaxNans (c : Ctx) (a b : Dec) : DM (Option Dec) := do
  if isSpecial a || isSpecial b then
    let sn := isnan a
    let on := isnan b
    if sn ≠ 0 ∨ on ≠ 0 then
      if on = 1 ∧ sn = 0 then return some (← fix c a)
      if sn = 1 ∧ on = 0 then return some (← fix c b)
      return ← checkNans c a (some b)
  return none

/-- `Decimal.max`, `min`, _pydecimal.py:2880-2954, with the comparison `cmp`
(`_cmp`, or on magnitudes for `max_mag`, `min_mag`, :3515-3573): `pickA` says which
operand wins when `c == -1`. -/
def minmaxBy (cmp : Dec → Dec → Int) (lowWins : Bool) (c : Ctx) (a b : Dec) : DM Dec := do
  if let some ans ← minmaxNans c a b then return ans
  let cc := cmp a b
  let cc := if cc = 0 then compareTotal a b else cc
  let ans := if cc = -1 then (if lowWins then a else b) else (if lowWins then b else a)
  fix c ans

def maxD := minmaxBy cmpInt false
def minD := minmaxBy cmpInt true
def magCmp (a b : Dec) : Int := cmpInt (copyAbs a) (copyAbs b)
def maxMag := minmaxBy magCmp false
def minMag := minmaxBy magCmp true

/-! ## `logb` -/

/-- `Decimal.logb`, _pydecimal.py:3388-3416. `DivisionByZero.handle` returns
`_SignedInfinity[sign]`, :187-188, here `-Infinity`. -/
def logb (c : Ctx) (a : Dec) : DM Dec := do
  if let some ans ← checkNans c a none then return ans
  if isinfinity a ≠ 0 then return .inf false
  if !decBool a then
    raiseSig c .divisionByZero
    return .inf true
  -- `ans = Decimal(self.adjusted())` (:3415): `str(abs(value))` (:621) raises past 4300 digits.
  let ans ← liftPy (pyFromInt a.adjusted)
  fix c ans

/-! ## Logical operations -/

/-- `Decimal._islogical`, _pydecimal.py:3418-3430. -/
def islogical : Dec → Bool
  | .fin false co 0 => (Nat.toDigits 10 co).all (fun d => d == '0' || d == '1')
  | _ => false

/-- One operand of `Decimal._fill_logical`, _pydecimal.py:3432-3443: pad on the
left, or keep the last `prec` characters. -/
def fillDigits (prec : Nat) (s : List Char) : List Char :=
  if s.length < prec then List.replicate (prec - s.length) '0' ++ s
  else if s.length > prec then s.drop (s.length - prec)
  else s

/-- `Decimal._fill_logical`. -/
def fillLogical (prec : Nat) (a b : List Char) : List Char × List Char :=
  (fillDigits prec a, fillDigits prec b)

/-- `result.lstrip('0') or '0'` as a value. -/
def digitOp (f : Bool → Bool → Bool) (a b : List Char) : List Char :=
  (a.zip b).map (fun p => if f (p.1 == '1') (p.2 == '1') then '1' else '0')

/-- `logical_and`, `logical_or`, `logical_xor`, _pydecimal.py:3445-3513. -/
def logicalOp (f : Bool → Bool → Bool) (c : Ctx) (a b : Dec) : DM Dec := do
  if !islogical a || !islogical b then return ← invalid c
  match a, b with
  | .fin _ ca _, .fin _ cb _ =>
    let (opa, opb) := fillLogical c.prec (Nat.toDigits 10 ca) (Nat.toDigits 10 cb)
    return .fin false (digitsValue (digitOp f opa opb)) 0
  | _, _ => return a

def logicalAnd := logicalOp (· && ·)
def logicalOr := logicalOp (· || ·)
def logicalXor := logicalOp (fun x y => x != y)

/-- `Decimal.logical_invert`, _pydecimal.py:3465-3473. -/
def logicalInvert (c : Ctx) (a : Dec) : DM Dec :=
  logicalXor c a (.fin false (digitsValue (List.replicate c.prec '1')) 0)

/-! ## `rotate`, `shift`, `scaleb` -/

/-- The checks `rotate`, `shift`, `scaleb` share up to the range test:
_pydecimal.py:3719-3726. `.inl r` returns `r`; `.inr` gives `int(other)`. -/
def intArg (c : Ctx) (a b : Dec) (lo hi : Int) : DM (Dec ⊕ Int) := do
  if let some ans ← checkNans c a (some b) then return .inl ans
  match b with
  | .fin bneg bc 0 =>
    liftPy (intLimit (numDigits bc))
    let v : Int := if bneg then -(bc : Int) else bc
    if ¬(lo ≤ v ∧ v ≤ hi) then return .inl (← invalid c)
    if isinfinity a ≠ 0 then return .inl a
    return .inr v
  | _ => return .inl (← invalid c)

/-- `Decimal.rotate`, _pydecimal.py:3713-3744: `rotdig` is the coefficient
reduced to `prec` digits; rotating left by `torot` (right when negative). -/
def rotate (c : Ctx) (a b : Dec) : DM Dec := do
  match ← intArg c a b (-(c.prec : Int)) c.prec with
  | .inl r => return r
  | .inr torot =>
    match a with
    | .fin neg co e =>
      let cut := co % 10 ^ c.prec
      -- rotated = rotdig[torot:] + rotdig[:torot]; a negative `torot` keeps `-torot` tail digits
      let k : Nat := if torot ≥ 0 then torot.toNat else c.prec - torot.natAbs
      let rotated := (cut % 10 ^ (c.prec - k)) * 10 ^ k + cut / 10 ^ (c.prec - k)
      return .fin neg rotated e
    | d => return d

/-- `Decimal.shift`, _pydecimal.py:3771-3807. -/
def shift (c : Ctx) (a b : Dec) : DM Dec := do
  match ← intArg c a b (-(c.prec : Int)) c.prec with
  | .inl r => return r
  | .inr torot =>
    match a with
    | .fin neg co e =>
      let cut := co % 10 ^ c.prec
      let shifted := if torot < 0 then cut / 10 ^ torot.natAbs
                     else (cut * 10 ^ torot.toNat) % 10 ^ c.prec
      return .fin neg shifted e
    | d => return d

/-- `Decimal.scaleb`, _pydecimal.py:3746-3769. -/
def scaleb (c : Ctx) (a b : Dec) : DM Dec := do
  let lim := 2 * (c.emax + c.prec)
  match ← intArg c a b (-lim) lim with
  | .inl r => return r
  | .inr n =>
    match a with
    | .fin neg co e => fix c (.fin neg co (e + n))
    | d => return d

/-! ## `next_*` -/

/-- `context._ignore_all_flags()` on a copy, _pydecimal.py:3587-3588: nothing is
flagged and nothing raises. -/
def quietly {α : Type} (x : DM α) : DM α := fun fl => do
  let (a, _) ← x fl
  pure (a, fl)

/-- The context copy `next_*` work in, _pydecimal.py:3586-3588. -/
def quietCtx (c : Ctx) (m : Rounding) : Ctx := { c with rounding := m, traps := [] }

/-- `Decimal.next_minus`, _pydecimal.py:3575-3596. -/
def nextMinus (c : Ctx) (a : Dec) : DM Dec := do
  if let some ans ← checkNans c a none then return ans
  if isinfinity a = -1 then return .inf true
  if isinfinity a = 1 then return .fin false (10 ^ c.prec - 1) c.etop
  let q := quietCtx c .floor
  quietly do
    let newSelf ← fix q a
    if cmpVal newSelf a ≠ .eq then return newSelf
    sub q a (.fin false 1 (q.etiny - 1))

/-- `Decimal.next_plus`, _pydecimal.py:3598-3619. -/
def nextPlus (c : Ctx) (a : Dec) : DM Dec := do
  if let some ans ← checkNans c a none then return ans
  if isinfinity a = 1 then return .inf false
  if isinfinity a = -1 then return .fin true (10 ^ c.prec - 1) c.etop
  let q := quietCtx c .ceiling
  quietly do
    let newSelf ← fix q a
    if cmpVal newSelf a ≠ .eq then return newSelf
    add q a (.fin false 1 (q.etiny - 1))

/-- `Decimal.next_toward`, _pydecimal.py:3621-3665. -/
def nextToward (c : Ctx) (a b : Dec) : DM Dec := do
  if let some ans ← checkNans c a (some b) then return ans
  let cmp := cmpInt a b
  if cmp = 0 then return copySign a b
  let ans ← if cmp = -1 then nextPlus c a else nextMinus c a
  if isinfinity ans ≠ 0 then
    raiseSig c .overflow
    raiseSig c .inexact
    raiseSig c .rounded
  else if ans.adjusted < c.emin then
    raiseSig c .underflow
    raiseSig c .subnormal
    raiseSig c .inexact
    raiseSig c .rounded
    if isZero ans then raiseSig c .clamped
  return ans

/-! ## `fma` -/

/-- `Decimal.fma`, _pydecimal.py:1975-2017. -/
def fma (c : Ctx) (a b t : Dec) : DM Dec := do
  match a, b with
  | .fin sa ca ea, .fin sb cb eb =>
    liftPy (intLimit (numDigits ca))
    liftPy (intLimit (numDigits cb))
    liftPy (strLimit (ca * cb))
    add c (.fin (sa != sb) (ca * cb) (ea + eb)) t
  | _, _ =>
    if isSnan a then
      raiseSig c .invalidOperation
      return quietOf c a
    if isSnan b then
      raiseSig c .invalidOperation
      return quietOf c b
    if isQnan a then add c a t
    else if isQnan b then add c b t
    else if isinfinity a ≠ 0 then
      if !decBool b then invalid c else add c (.inf (a.neg != b.neg)) t
    else
      if !decBool a then invalid c else add c (.inf (a.neg != b.neg)) t

/-! ## `to_eng_string`, `__repr__`, `_round` -/

/-- `dotplace` of `__str__(eng=True)`, _pydecimal.py:1097-1108. -/
def engDot (isZeroInt : Bool) (e leftdigits : Int) : Int :=
  if e ≤ 0 ∧ leftdigits > -6 then leftdigits
  else if isZeroInt then (leftdigits + 1) % 3 - 1
  else (leftdigits - 1) % 3 + 1

/-- The finite branch of `__str__(eng=True)`, _pydecimal.py:1091-1126. -/
def engFinite (neg : Bool) (ds : List Char) (e : Int) (caps : Bool) : List Char :=
  let sign := if neg then ['-'] else []
  let leftdigits : Int := e + ds.length
  let dotplace := engDot (ds == ['0']) e leftdigits
  let (intpart, fracpart) :=
    if dotplace ≤ 0 then (['0'], '.' :: (List.replicate (-dotplace).toNat '0' ++ ds))
    else if dotplace ≥ ds.length then (ds ++ List.replicate (dotplace - ds.length).toNat '0', [])
    else (ds.take dotplace.toNat, '.' :: ds.drop dotplace.toNat)
  let exp := if leftdigits = dotplace then [] else
    (if caps then 'E' else 'e') :: fmtSigned (leftdigits - dotplace)
  sign ++ intpart ++ fracpart ++ exp

/-- `Decimal.to_eng_string`, _pydecimal.py:1128-1135. -/
def toEng (d : Dec) (caps : Bool := true) : List Char :=
  match d with
  | .fin neg c e => engFinite neg (Nat.toDigits 10 c) e caps
  | d => toSci d caps

/-- `Decimal.__repr__`, _pydecimal.py:1071-1074. -/
def reprD (d : Dec) : List Char := "Decimal('".toList ++ toSci d ++ "')".toList

/-- `Decimal._round`, _pydecimal.py:2710-2731, for `places ≥ 1`. -/
def roundPlaces (d : Dec) (places : Nat) (m : Rounding) : Py Dec := do
  match d with
  | .fin _ co _ =>
    if co = 0 then return d
    let ans ← rescale d (d.adjusted + 1 - places) m
    if ans.adjusted ≠ d.adjusted then rescale ans (ans.adjusted + 1 - places) m
    else return ans
  | _ => return d

/-! ## Conditions: `_raise_error` and the `handle` methods -/

/-- A condition with the arguments `_raise_error` passes to its handler. -/
inductive Cond where
  | invalidOperation (arg : Option Dec)
  | conversionSyntax
  | divisionImpossible
  | divisionUndefined
  | invalidContext
  | divisionByZero (sign : Bool)
  | overflow (sign : Bool)
  /-- Clamped, Inexact, Rounded, Subnormal, Underflow, FloatOperation: no `handle` of
  their own. -/
  | plain (s : Signal)
  deriving Repr

/-- `_condition_map.get(condition, condition)`, _pydecimal.py:336-339. -/
def Cond.signal : Cond → Signal
  | .invalidOperation _ | .conversionSyntax | .divisionImpossible
  | .divisionUndefined | .invalidContext => .invalidOperation
  | .divisionByZero _ => .divisionByZero
  | .overflow _ => .overflow
  | .plain s => s

/-- `_NaN`, _pydecimal.py:6489. -/
def nanD : Dec := .nan false false 0

/-- The `handle` methods: `DecimalException.handle` (:119-120, `none`),
`InvalidOperation.handle` (:158-162), `ConversionSyntax.handle` (:171-172),
`DivisionByZero.handle` (:187-188), `DivisionImpossible.handle` (:198-199),
`DivisionUndefined.handle` (:209-210), `InvalidContext.handle` (:236-237),
`Overflow.handle` (:284-297, `overflowResult`). -/
def handle (c : Ctx) : Cond → Option Dec
  | .invalidOperation (some a) => some (quietOf c a)
  | .invalidOperation none => some nanD
  | .conversionSyntax | .divisionImpossible | .divisionUndefined | .invalidContext => some nanD
  | .divisionByZero sign => some (.inf sign)
  | .overflow sign => some (overflowResult c sign)
  | .plain _ => none

/-- `Context._raise_error`, _pydecimal.py:4105-4125. -/
def raiseError (c : Ctx) (ignored : List Signal) (cnd : Cond) : DM (Option Dec) := do
  let error := cnd.signal
  if error ∈ ignored then return handle c cnd
  modify (fun fl => if error ∈ fl then fl else fl ++ [error])
  if error ∉ c.traps then return handle c cnd
  throw (.named error.name "~")

end PyLean.Decimal
