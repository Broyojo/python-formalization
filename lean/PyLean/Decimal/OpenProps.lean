import PyLean.Decimal.MulProps
import PyLean.Decimal.ParseAgree
import PyLean.Decimal.Ops

/-!
Statements with no proof yet. Each is registered `.open` with a note on what is
missing; none is used by any other file. They are stated in full, with the same
hypotheses a proof would be allowed: `prec ≥ 1` and `Emin ≤ 0 ≤ Emax` are the
invariants `Context._set_integer_check` enforces (_pydecimal.py:3905-3917).
-/

namespace PyLean.Decimal

open PyLean

/-- The signed exact sum of two finite decimals, as a coefficient at exponent
`min ea eb`. -/
def exactSum (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int) : Int :=
  let e := min ea eb
  (if sa then -1 else 1) * ((ca * 10 ^ (ea - e).toNat : Nat) : Int) +
    (if sb then -1 else 1) * ((cb * 10 ^ (eb - e).toNat : Nat) : Int)

/-- For every context (`prec ≥ 1`) and all finite non-zero operands whose exact
sum is non-zero, when `+` returns a value in the normal range, that value is the
exact sum correctly rounded to `prec` digits, Inexact is set exactly when non-zero
digits of the exact sum were dropped, and Rounded exactly when any were. The
statement quantifies over operands of very different size, where `_normalize`
(_pydecimal.py:5623-5649) replaces the smaller one by a sticky digit. -/
def AddCorrect : Prop :=
  ∀ (c : Ctx) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int)
    (fl fl' : List Signal) (d : Dec),
    1 ≤ c.prec → ca ≠ 0 → cb ≠ 0 →
    let x := exactSum sa ca ea sb cb eb
    let S := x.natAbs
    let e := min ea eb
    let neg := decide (x < 0)
    let r := roundPrec c.rounding neg S e c.prec
    S ≠ 0 →
    c.etiny ≤ e + (numDigits S - c.prec : Nat) →
    r.2 + numDigits r.1 - 1 ≤ c.emax →
    (add c (.fin sa ca ea) (.fin sb cb eb)).run fl = .ok (d, fl') →
    d = .fin neg (r.1 * 10 ^ (r.2 - foldExp c r.2).toNat) (foldExp c r.2) ∧
    (Signal.inexact ∈ fl' ↔ Signal.inexact ∈ fl ∨ S % 10 ^ (numDigits S - c.prec) ≠ 0) ∧
    (Signal.rounded ∈ fl' ↔ Signal.rounded ∈ fl ∨ c.prec < numDigits S)

/-- `a - b` is `a + (-b)` correctly rounded: `AddCorrect` for the operand with
the opposite sign, stated on `sub`. -/
def SubCorrect : Prop :=
  ∀ (c : Ctx) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int)
    (fl fl' : List Signal) (d : Dec),
    1 ≤ c.prec → ca ≠ 0 → cb ≠ 0 →
    let x := exactSum sa ca ea (!sb) cb eb
    let S := x.natAbs
    let e := min ea eb
    let neg := decide (x < 0)
    let r := roundPrec c.rounding neg S e c.prec
    S ≠ 0 →
    c.etiny ≤ e + (numDigits S - c.prec : Nat) →
    r.2 + numDigits r.1 - 1 ≤ c.emax →
    (sub c (.fin sa ca ea) (.fin sb cb eb)).run fl = .ok (d, fl') →
    d = .fin neg (r.1 * 10 ^ (r.2 - foldExp c r.2).toNat) (foldExp c r.2)

/-- When the correctly rounded product would have an adjusted exponent above
`Emax`, `*` returns the rounding mode's overflow value and sets Overflow,
Inexact and Rounded. -/
def MulOverflowCorrect : Prop :=
  ∀ (c : Ctx) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int)
    (fl fl' : List Signal) (d : Dec),
    1 ≤ c.prec → c.emin ≤ 0 → 0 ≤ c.emax → ca ≠ 0 → cb ≠ 0 →
    let P := ca * cb
    let e := ea + eb
    let neg := sa != sb
    let r := roundPrec c.rounding neg P e c.prec
    r.2 + numDigits r.1 - 1 > c.emax →
    (mul c (.fin sa ca ea) (.fin sb cb eb)).run fl = .ok (d, fl') →
    d = overflowResult c neg ∧ Signal.overflow ∈ fl' ∧ Signal.inexact ∈ fl' ∧ Signal.rounded ∈ fl'

/-- When the product is below the normal range, `*` rounds it at exponent
`Etiny` and sets Subnormal; Inexact and Underflow are set exactly when non-zero
digits were dropped. `numDigits P + e - prec < Etiny` is `_fix`'s test for the
subnormal case (_pydecimal.py:1651-1656). -/
def MulSubnormalCorrect : Prop :=
  ∀ (c : Ctx) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int)
    (fl fl' : List Signal) (d : Dec),
    1 ≤ c.prec → c.emin ≤ 0 → 0 ≤ c.emax → ca ≠ 0 → cb ≠ 0 →
    let P := ca * cb
    let e := ea + eb
    let neg := sa != sb
    (numDigits P : Int) + e - c.prec < c.etiny →
    e < c.etiny →
    (mul c (.fin sa ca ea) (.fin sb cb eb)).run fl = .ok (d, fl') →
    d = .fin neg (quantSpec c.rounding neg P e c.etiny) c.etiny ∧
    Signal.subnormal ∈ fl' ∧ Signal.rounded ∈ fl' ∧
    (Signal.inexact ∈ fl' ↔ Signal.inexact ∈ fl ∨ P % 10 ^ (c.etiny - e).toNat ≠ 0) ∧
    (Signal.underflow ∈ fl' ↔ Signal.underflow ∈ fl ∨ P % 10 ^ (c.etiny - e).toNat ≠ 0)

/-- The converse of `ParseCAcceptsPyCasefree`: every string `_decimal` accepts,
`_pydecimal` accepts with the same value, or refuses with the int-limit
`ValueError`. -/
def ParseConverse : Prop :=
  ∀ (s : List Char) (d : Dec),
    cParse s = .ok d → pyParse s = .ok d ∨ ∃ msg, pyParse s = .error (.valueError msg)

/-- `Decimal(d.as_tuple()) == d` in `_decimal`, for every decimal within the C
limits: sign, coefficient, exponent, NaN kind and payload. -/
def AsTupleRoundTrip : Prop :=
  ∀ d : Dec, InCLimits d →
    let t := asTuple d
    cFromTuple t.1 (some t.2.1) t.2.2 = .ok d

/-- `normalize` is `_fix` followed by stripping trailing zeros: the result has
the value `_fix` gives and no trailing zero left, unless the exponent limit
stopped it; a zero becomes the zero with exponent 0. -/
def NormalizeCorrect : Prop :=
  ∀ (c : Ctx) (a d : Dec) (fl fl' : List Signal),
    nanKind a = 0 →
    (normalize c a).run fl = .ok (d, fl') →
    ∃ v, (fix c a).run fl = .ok (v, fl') ∧ cmpVal d v = .eq ∧
      ∀ neg co e, d = .fin neg co e →
        (co = 0 ∧ e = 0) ∨ co % 10 ≠ 0 ∨ e ≥ (if c.clamp then c.etop else c.emax)

end PyLean.Decimal
