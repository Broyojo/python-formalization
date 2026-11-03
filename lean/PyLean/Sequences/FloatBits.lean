import PyLean.Sequences.ArrayModel

/-!
Bit-level facts about the conversions of `Values.lean`: `(double)` of a binary32 pattern
(`floatToDouble`), `(float)` of a binary64 pattern (`doubleToFloat`), `PyFloat_Unpack2`
(`halfToDouble`) and `PyFloat_Pack2` (`packHalf`). Each conversion is the sign bit plus a
function of the exponent and fraction fields (`*Mag`), which the lemmas then treat by class.
-/

namespace PyLean.Sequences

open PyLean

set_option linter.deprecated false

theorem or22 (f : Nat) (h : f < 8388608) : f ||| 4194304 = 4194304 + f % 4194304 := by
  by_cases hb : f < 4194304
  · have := Nat.or_two_pow_eq_add_of_lt (a := f) (n := 22) hb
    simp only [Nat.reducePow] at this
    rw [this, Nat.mod_eq_of_lt hb]; omega
  · have hr : f % 4194304 < 2 ^ 22 := by simp only [Nat.reducePow]; omega
    have h2 := Nat.two_pow_add_eq_or_of_lt (i := 22) hr 1
    simp only [Nat.reducePow, Nat.mul_one] at h2
    have hf : f = 4194304 + f % 4194304 := by omega
    calc f ||| 4194304 = (4194304 + f % 4194304) ||| 4194304 := by rw [← hf]
      _ = (4194304 ||| f % 4194304) ||| 4194304 := by rw [h2]
      _ = 4194304 ||| f % 4194304 := by
        rw [Nat.or_assoc, Nat.or_comm (f % 4194304), ← Nat.or_assoc, Nat.or_self]
      _ = 4194304 + f % 4194304 := h2.symm

theorem roundShift_exact (q s : Nat) : roundShift (q * 2 ^ s) s = q := by
  unfold roundShift
  by_cases h : s = 0
  · subst h; simp
  · rw [if_neg h]
    have hp : 0 < 2 ^ s := Nat.pos_of_ne_zero (by simp)
    have h1 : (q * 2 ^ s) >>> s = q := by
      rw [Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ hp]
    have h2 : q * 2 ^ s % 2 ^ s = 0 := Nat.mul_mod_left _ _
    have h3 : 0 < 2 ^ (s - 1) := Nat.pos_of_ne_zero (by simp)
    simp only [h1, h2]
    rw [if_neg (by omega)]

/-! ### Sign and magnitude -/

/-- `floatToDouble` on the exponent field `e` and the fraction field `f`, sign bit clear. -/
def f2dMag (e f : Nat) : Nat :=
  if e = 255 then
    if f = 0 then 2047 <<< 52 else 2047 <<< 52 + ((f ||| 4194304) <<< 29)
  else if e = 0 then
    if f = 0 then 0
    else
      let L := bitLength f
      ((L + 873) <<< 52) + ((f <<< (53 - L)) - two52)
  else ((e + 896) <<< 52) + (f <<< 29)

theorem floatToDouble_eq (b : Nat) :
    floatToDouble b = (if b ≥ 2147483648 then two63 else 0) + f2dMag ((b % 2147483648) >>> 23) (b % 8388608) := by
  simp only [floatToDouble, f2dMag]
  generalize (if b ≥ 2147483648 then two63 else 0) = s
  generalize (b % 2147483648) >>> 23 = e
  generalize b % 8388608 = f
  repeat' split
  all_goals omega

/-- `doubleToFloat` on the exponent and fraction fields, sign bit clear. -/
def d2fMag (e f : Nat) : Nat :=
  if e = 2047 then
    if f = 0 then 2139095040 else 2143289344 + (f >>> 29) % 4194304
  else if e = 0 then 0
  else
    let m := two52 + f
    if e ≥ 897 then
      let q := roundShift m 29
      let (q, e') := if q = 16777216 then (8388608, e + 1) else (q, e)
      if e' ≥ 1151 then 2139095040
      else ((e' - 896) <<< 23) + (q - 8388608)
    else roundShift m (29 + (897 - e))

theorem doubleToFloat_eq (b : Nat) :
    doubleToFloat b = (if b ≥ two63 then 2147483648 else 0) + d2fMag ((b % two63) >>> 52) (b % two52) := by
  simp only [doubleToFloat, d2fMag]
  generalize (if b ≥ two63 then 2147483648 else 0) = s
  generalize (b % two63) >>> 52 = e
  generalize b % two52 = f
  split
  · split <;> omega
  · split
    · omega
    · split
      · split <;> split <;> simp only [] <;> omega
      · omega

/-- `halfToDouble` on the exponent and fraction fields, sign bit clear. -/
def h2dMag (e f : Nat) : Nat :=
  if e = 31 then (2047 <<< 52) + (f <<< 42)
  else if e = 0 then
    if f = 0 then 0
    else
      let L := bitLength f
      ((L + 998) <<< 52) + ((f <<< (53 - L)) - two52)
  else ((e + 1008) <<< 52) + (f <<< 42)

theorem halfToDouble_eq (h : Nat) :
    halfToDouble h = (if h ≥ 32768 then two63 else 0) + h2dMag ((h % 32768) >>> 10) (h % 1024) := by
  simp only [halfToDouble, h2dMag]
  generalize (if h ≥ 32768 then two63 else 0) = s
  generalize (h % 32768) >>> 10 = e
  generalize h % 1024 = f
  split <;> (try split) <;> (try split) <;> omega

/-- `packHalf` on the exponent and fraction fields, sign bit clear. -/
def phMag (be f : Nat) : Py Nat :=
  if be = 2047 then
    if f = 0 then .ok 31744
    else
      let b := f >>> 42
      .ok (31744 + (if b = 0 then 512 else b))
  else if be = 0 then .ok 0
  else
    let e : Int := (be : Int) - 1023
    if e ≥ 16 then .error packHalfErr
    else if e < -25 then .ok 0
    else if e < -14 then .ok (roundShift (two52 + f) (28 - e).toNat)
    else
      let q := roundShift f 42
      let (q, e') : Nat × Nat := if q = 1024 then (0, (e + 16).toNat) else (q, (e + 15).toNat)
      if e' = 31 then .error packHalfErr else .ok ((e' <<< 10) + q)

theorem packHalf_eq (b : Nat) :
    packHalf b = (phMag ((b % two63) >>> 52) (b % two52)).map ((if b ≥ two63 then 32768 else 0) + ·) := by
  simp only [packHalf, phMag]
  generalize (if b ≥ two63 then 32768 else 0) = s
  generalize (b % two63) >>> 52 = e
  generalize b % two52 = f
  repeat' split
  all_goals first
    | rfl
    | (simp only [Except.map]; congr 1; omega)
    | (simp only [Except.map, Except.ok.injEq]; omega)
    | (simp only [Except.map]; (repeat' split) <;> simp_all <;> omega)

end PyLean.Sequences
