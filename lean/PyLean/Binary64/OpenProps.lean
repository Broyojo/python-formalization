import PyLean.Binary64.Dtoa
import PyLean.Binary64.Round

/-!
Statements stated and difftested but not yet settled. Each has a registry entry with
status `open`, and a note there says what is missing.
-/

namespace PyLean.Binary64

open F64

/-- `hash(x)` follows the numeric rule of `Doc/library/stdtypes.rst`: for a finite `x` with
value `±m / n`, it is `±(m * n⁻¹ mod P)`, so `hash(x) == hash(int(x))` and
`hash(x) == hash(Fraction(x))`. The value `-1` becomes `-2`. -/
def FloatHashNumericTower : Prop :=
  ∀ x : F64, x.isFinite = true → ∃ h : Int, float_hash x = some h ∧ h ≠ -1 ∧
    ((h.natAbs * x.toRat.den) % hashModulus = x.toRat.num.natAbs % hashModulus ∨ (h = -2 ∧
      x.toRat.den % hashModulus = x.toRat.num.natAbs % hashModulus))

/-- `float.fromhex(x.hex()) == x` for every finite `x`, sign of zero included. -/
def HexRoundTrip : Prop :=
  ∀ x : F64, x.isFinite = true →
    float_fromhex ((float_hex x).toList.map Char.toNat) = .ok x

/-- `float(repr(x)) == x` for every finite `x`, sign of zero included. -/
def ReprRoundTrip : Prop :=
  ∀ x : F64, x.isFinite = true → ∃ r, float_repr x = some r ∧ PyFloat_FromString (.bytes r) = .ok x

/-- The number a parse denotes: `n * 10 ^ e`, with `n` the digits of the significand. -/
def parsedValue (s : List Nat) (p : Parsed) : Rat :=
  let n := (List.range p.nd).foldl (fun acc i => 10 * acc + sigDig s p.s0 p.nd0 i) 0
  if 0 ≤ p.e then ((n * 10 ^ p.e.toNat : Nat) : Rat) else mkRat n (10 ^ (-p.e).toNat)

/-- `_Py_dg_strtod` is correctly rounded, for every digit string it accepts. -/
def StrtodCorrectlyRounded : Prop :=
  ∀ (s : List Nat) (start : Nat) (p : Parsed), strtodParse s start = some p →
    (strtodAbs s p).map Prod.fst = some (ofRat (parsedValue s p))

/-- The decimal value `0.d₁d₂… * 10 ^ decpt` of a digit string. -/
def digitsValue (out : DtoaOut) : Rat :=
  let n := out.digits.foldl (fun acc d => 10 * acc + (d - 48)) 0
  let e := out.decpt - out.digits.length
  if 0 ≤ e then ((n * 10 ^ e.toNat : Nat) : Rat) else mkRat n (10 ^ (-e).toNat)

/-- Mode 3 of `_Py_dg_dtoa` is the exact value rounded half to even at `10 ^ -ndigits`,
for `ndigits` in the range `double_round` passes. -/
def DtoaFixedCorrect : Prop :=
  ∀ (x : F64) (ndigits : Int), x.isFinite = true → x.sign = false → -308 ≤ ndigits → ndigits ≤ 323 →
    ∃ out, _Py_dg_dtoa x 3 ndigits = some out ∧
      Rat.abs (digitsValue out - x.toRat) ≤
        (if 0 ≤ ndigits then mkRat 1 (2 * 10 ^ ndigits.toNat) else mkRat (10 ^ (-ndigits).toNat) 2)

/-- Mode 0 of `_Py_dg_dtoa` gives digits that read back as `x`. -/
def DtoaShortestRoundTrip : Prop :=
  ∀ x : F64, x.isFinite = true → x.sign = false → x.isZero = false →
    ∃ out, _Py_dg_dtoa x 0 0 = some out ∧ ofRat (digitsValue out) = x

/-- `round(x)` is the nearest int, with ties to even. -/
def FloatRoundHalfEven : Prop :=
  ∀ x : F64, x.isFinite = true → ∃ n : Int, float_round_int x = .ok n ∧
    Rat.abs (x.toRat - n) ≤ 1 / 2 ∧ (Rat.abs (x.toRat - n) = 1 / 2 → n % 2 = 0)

/-- `PyFloat_Pack4` inverts `PyFloat_Unpack4` on every binary32 pattern. -/
def Pack4RoundTrip : Prop :=
  ∀ b, b < 2 ^ 32 → ∀ le : Bool,
    PyFloat_Pack4 (PyFloat_Unpack4 (layout 4 b le) le) le = .ok (layout 4 b le)

/-- `quorem(b, S)` is the quotient digit, under the bound and normalization its callers keep:
`b < 10 * S`, and the top limb of `S` has bit 27 set. -/
def QuoremSpec : Prop :=
  ∀ b S : Bigint, S.val ≠ 0 → b.val < 10 * S.val → 2 ^ 27 ≤ S.top → S.top < 2 ^ 28 →
    let r := quorem b S
    b.val = r.1 * S.val + r.2.val ∧ r.2.val < S.val

/-- `d2b` writes a positive finite float as an odd integer times a power of two, with the
bit count of the integer. -/
def D2bSpec : Prop :=
  ∀ x : F64, x.isFinite = true → x.sign = false → x.isZero = false →
    let r := d2b x
    (r.1.val : Rat) * pw r.2.1 = x.toRat ∧ r.1.val % 2 = 1 ∧
      2 ^ (r.2.2 - 1) ≤ r.1.val ∧ r.1.val < 2 ^ r.2.2

/-- `b2d` gives the leading bits of a Bigint as a double in `[1, 2)`, with the exponent. -/
def B2dSpec : Prop :=
  ∀ a : Bigint, a.val ≠ 0 → (b2d a).1.bexp = 1023 ∧ (b2d a).2 = 32 - hi0bits a.top

/-- `ratio(a, b)` is within 2.5 ulps of `a / b`, as the comment at dtoa.c:1082-1083 says. -/
def RatioBound : Prop :=
  ∀ a b : Bigint, a.val ≠ 0 → b.val ≠ 0 →
    Rat.abs ((ratio a b).toRat - (a.val : Rat) / b.val) ≤
      5 / 2 * pw (ratio a b).lsbExp

end PyLean.Binary64
