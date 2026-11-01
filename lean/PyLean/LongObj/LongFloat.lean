import PyLean.Registry
import PyLean.LongObj.IntNew
import PyLean.LongObj.ComplexDbl

/-!
The `int` functions that produce or consume a `double`: `_PyLong_Frexp`, `PyLong_AsDouble`,
`long_float`, `PyLong_FromDouble`, `long_true_divide`.

These are integer algorithms up to their last step, so they are mirrored with the digit
kernels and finish on the exact `Cplx.Dbl`. Every double they build is exactly
representable, so `roundQ` there is a conversion and not a rounding step. They are
differentially tested. Correct rounding is stated here and left open, because `Dbl` has no
rounding theory; `lean/PyLean/Binary64/` is where that proof belongs.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt PyLean.Registry Cplx

/-- `half_even_correction`, longobject.c:3480. -/
def halfEvenCorrection (i : Nat) : Int := ([0, -1, -2, 1, 0, -1, 2, 1] : List Int).getD i 0

/-- `DBL_MANT_DIG + 2`. -/
def frexpBits : Nat := 55

/-- `_PyLong_Frexp(a, &e)`, longobject.c:3468-3561, for a non-zero magnitude: the rounded
`x_digits` value, a multiple of 4 with `dx = x / 2**55`, and the exponent. The significand
`0.5 <= dx < 1` comes back as `x`, with the correction at :3553-3557 applied. -/
def frexpMag (ds : List Nat) : Nat × Nat :=
  let aBits := numBits ⟨false, ds⟩
  let xs : List Nat :=
    if aBits ≤ frexpBits then
      let sd := (frexpBits - aBits) / 30
      let sb := (frexpBits - aBits) % 30
      let (r, rem) := vLshiftGo sb ds 0
      List.replicate sd 0 ++ r ++ [rem]
    else
      let sd := (aBits - frexpBits) / 30
      let sb := (aBits - frexpBits) % 30
      let (z, rem) := vRshiftGo sb (ds.drop sd)
      let sticky := rem ≠ 0 ∨ stickyOf (ds.take sd) 0 ≠ 0
      match z with
      | d :: t => (if sticky then d ||| 1 else d) :: t
      | [] => []
  let rounded : List Nat :=
    match xs with
    | d :: t => (((d : Int) + halfEvenCorrection (d &&& 7)).toNat) :: t
    | [] => []
  let x := val rounded
  if x = 2 ^ 55 then (2 ^ 54, aBits + 1) else (x, aBits)

/-- `PyLong_AsDouble(v)`, longobject.c:3567-3596, for an exact int. -/
def asDouble (v : Long) : Py Dbl :=
  if v.isCompact = true then .ok (Dbl.roundQ (v.neg && !v.ds.isEmpty) (val v.ds) 1)
  else
    let (x, e) := frexpMag v.ds
    if e > 1024 then .error (.overflowError "int too large to convert to float")
    else .ok (Dbl.roundQ v.neg (x * 2 ^ e) (2 ^ 55))

/-- `long_float(v)`, longobject.c:5954-5961. -/
def longFloat (v : Long) : Py Dbl := asDouble v

/-- `PyLong_FromDouble(dval)`, longobject.c:469-521. Below `LONG_MAX + 1` the C cast
truncates; above it the digit loop at :511-516 copies every bit of the significand, which
for those values is the integer itself. -/
def fromDouble (d : Dbl) : Py Int :=
  let small := !d.isNaN && !d.isInf && d.mag < 2 ^ (63 + 1074)
  if small then .ok (if d.sign then -((d.mag >>> 1074 : Nat) : Int) else (d.mag >>> 1074 : Nat))
  else if d.isInf then .error (.overflowError "cannot convert float infinity to integer")
  else if d.isNaN then .error (.valueError "cannot convert float NaN to integer")
  else .ok (if d.sign then -((d.mag >>> 1074 : Nat) : Int) else (d.mag >>> 1074 : Nat))

/-- `MANT_DIG_DIGITS` and `MANT_DIG_BITS`, longobject.c:4603-4604. -/
def mantDigDigits : Nat := 53 / 30
def mantDigBits : Nat := 53 % 30

/-- `a_is_small`, longobject.c:4722-4724. -/
def isSmallForDouble (ds : List Nat) : Bool :=
  decide (ds.length ≤ mantDigDigits) ||
    (decide (ds.length = mantDigDigits + 1) && decide (ds.getD mantDigDigits 0 >>> mantDigBits = 0))

def divOverflow : PyExc := .overflowError "integer division result too large for a float"

/-- Rounding by modifying the low digit, longobject.c:4832-4836. -/
def roundLow (low extra : Nat) : Nat :=
  let mask := 1 <<< (extra - 1)
  let low := if low &&& mask ≠ 0 ∧ low &&& (3 * mask - 1) ≠ 0 then low + mask else low
  low - low % (2 * mask)

/-- `x //= b` with the inexact flag, longobject.c:4806-4822. -/
def xDivB (x bs : List Nat) (inexact : Bool) : Py (List Nat × Bool) :=
  if bs.length = 1 then
    let (q, rem) := inplaceDivrem1 (bs.getD 0 0) x
    .ok (normalize q, inexact || rem != 0)
  else
    match xDivrem x bs with
    | .ok (q, rem) => .ok (q, inexact || !rem.isEmpty)
    | .error e => .error e

/-- Steps 2 to 5 of `long_true_divide`, longobject.c:4760-4848. -/
def trueDivideSlow (as bs : List Nat) (negate : Bool) (shift : Int) : Py Dbl :=
  let start : Py (List Nat × Bool) :=
    if shift ≤ 0 then
      let n := (-shift).toNat
      let sd := n / 30
      if (as.length : Int) ≥ ssizeMax - 1 - sd then
        .error (.overflowError "intermediate overflow during division")
      else
        match longAlloc (as.length + sd + 1) with
        | .error e => .error e
        | .ok _ =>
          let (r, rem) := vLshiftGo (n % 30) as 0
          .ok (List.replicate sd 0 ++ r ++ [rem], false)
    else
      let n := shift.toNat
      let sd := n / 30
      let (z, rem) := vRshiftGo (n % 30) (as.drop sd)
      .ok (z, rem ≠ 0 ∨ stickyOf (as.take sd) 0 ≠ 0)
  match start with
  | .error e => .error e
  | .ok (x, inexact) =>
    match xDivB (normalize x) bs inexact with
    | .error e => .error e
    | .ok (x, inexact) =>
      let xBits := numBits ⟨false, x⟩
      let extra := (max (xBits : Int) (-1021 - shift) - 53).toNat
      let x' := match x with
        | d :: t => roundLow (d ||| (if inexact then 1 else 0)) extra :: t
        | [] => []
      let dx := val x'
      let top := shift + xBits
      if top ≥ 1024 ∧ (top > 1024 ∨ dx = 2 ^ xBits) then .error divOverflow
      else if shift ≥ 0 then .ok (Dbl.roundQ negate (dx * 2 ^ shift.toNat) 1)
      else .ok (Dbl.roundQ negate dx (2 ^ (-shift).toNat))

/-- `long_true_divide(v, w)`, longobject.c:4607-4861. -/
def trueDivide (a b : Long) : Py Dbl :=
  let negate := a.neg != b.neg
  if b.ds.length = 0 then .error (.zeroDivisionError "division by zero")
  else if a.ds.length = 0 then .ok (Dbl.zeroOf negate)
  else if isSmallForDouble a.ds ∧ isSmallForDouble b.ds then
    .ok (Dbl.roundQ negate (val a.ds) (val b.ds))
  else
    let diff0 : Int := (a.ds.length : Int) - b.ds.length
    if diff0 > ssizeMax / 30 - 1 then .error divOverflow
    else if diff0 < 1 - ssizeMax / 30 then .ok (Dbl.zeroOf negate)
    else
      let diff : Int := diff0 * 30 + bitLength (a.ds.getD (a.ds.length - 1) 0)
        - bitLength (b.ds.getD (b.ds.length - 1) 0)
      if diff > 1024 then .error divOverflow
      else if diff < -1021 - 53 - 1 then .ok (Dbl.zeroOf negate)
      else trueDivideSlow a.ds b.ds negate (max diff (-1021) - 53 - 2)

/-! ## Open statements

Each states the documented rounding. They need a theory of `Dbl.roundQ`: that it returns the
nearest double, and that it is exact on the values these functions build. -/

/-- "Rounds to the nearest double, using the round-half-to-even rule in the case of a tie",
longobject.c:3563-3564, with `OverflowError` exactly when that rounds to infinity. -/
def AsDoubleRounds : Prop :=
  ∀ a : Int, match asDouble (.ofInt a) with
    | .ok d => d = Dbl.roundQ (decide (a < 0)) a.natAbs 1
    | .error _ => Dbl.isInf (Dbl.roundQ (decide (a < 0)) a.natAbs 1) = true

/-- "PyLong/PyLong -> float, with correctly rounded result", longobject.c:4601. -/
def TrueDivideRounds : Prop :=
  ∀ a b : Int, b ≠ 0 → match trueDivide (.ofInt a) (.ofInt b) with
    | .ok d => d = Dbl.roundQ (decide (a < 0) != decide (b < 0)) a.natAbs b.natAbs
    | .error _ => Dbl.isInf
        (Dbl.roundQ (decide (a < 0) != decide (b < 0)) a.natAbs b.natAbs) = true

/-- `int(x)` truncates toward zero, and `float(int(x)) == x` for integral `x`. -/
def FromDoubleRoundTrip : Prop :=
  ∀ d : Dbl, d.bits < 2 ^ 64 → d.isNaN = false → d.isInf = false →
    d.mag % 2 ^ 1074 = 0 → ∃ n, fromDouble d = .ok n ∧ d.mag = n.natAbs * 2 ^ 1074

def entriesFloat : List Entry := [
  { id := "longobj-as-double-rounds", pyFile := "Objects/longobject.c"
    pyFns := ["PyLong_AsDouble", "_PyLong_Frexp", "long_float"]
    statement := "float(a) is a rounded to the nearest double, ties to even, and raises OverflowError exactly when that rounds to infinity."
    source := "comment at longobject.c:3563-3564", status := .open
    prop := ``AsDoubleRounds
    notes := "Mirrored and difftested. Open: needs a rounding theory of Dbl.roundQ, or the Binary64 model." },
  { id := "longobj-true-divide-rounds", pyFile := "Objects/longobject.c", pyFns := ["long_true_divide"]
    statement := "a / b is the correctly rounded quotient, and raises OverflowError exactly when that rounds to infinity."
    source := "comment at longobject.c:4601", status := .open
    prop := ``TrueDivideRounds
    notes := "Mirrored and difftested. Open: needs a rounding theory of Dbl.roundQ, or the Binary64 model." },
  { id := "longobj-from-double", pyFile := "Objects/longobject.c", pyFns := ["PyLong_FromDouble"]
    statement := "int(x) of an integral double x is that integer."
    source := "invariant: round trip", status := .open
    prop := ``FromDoubleRoundTrip
    notes := "The model takes the value from the significand and does not mirror the digit loop at longobject.c:511-516 line by line, so this entry stays open and its row unmodelled." }
]

end PyLean.LongObj
