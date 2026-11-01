import PyLean.LongObj.Div

/-!
The Python-level division operators on the digit model: `long_rem`, `l_divmod`,
`l_mod`, `long_div`, `long_mod`, `long_divmod`, `pylong_int_divmod`.

`lDivmod_eq` is the bridge to `MathInt`: the digit-level `l_divmod` returns the
canonical objects of `MathInt.divmod`, which assumed `long_divrem` exact.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-- The constant `_PyLong_GetOne()`, longobject.c:4431. -/
def longOne : Long := ⟨false, [1]⟩

theorem longOne_eq : longOne = Long.ofInt 1 := by decide

/-- `_PyLong_IsPositive(x)`, pycore_long.h:231-234. -/
def Long.isPositive (x : Long) : Bool := !x.neg && !x.ds.isEmpty

/-- The sign test at longobject.c:4422-4423 and :4469-4470. -/
def needsFix (md w : Long) : Bool :=
  (md.neg && w.isPositive) || (md.isPositive && w.neg)

/-- `fast_floor_div` and `fast_mod`, longobject.c:4275-4315, on one-digit objects,
returned through `PyLong_FromLong`. -/
def fastPair (v w : Long) : Long × Long :=
  let p := fastDivmod v.toInt w.toInt
  (Long.ofInt p.1, Long.ofInt p.2)

/-- `l_divmod(v, w, &div, &mod)`, longobject.c:4379-4450. The `_pylong` branch is
`pylong_int_divmod`, :4320-4354, with `MathInt.pylongIntDivmod` as its result. -/
def lDivmod (v w : Long) : Py (Long × Long) :=
  if v.ds.length = 1 ∧ w.ds.length = 1 then .ok (fastPair v w)
  else if w.ds.length > 300 ∧ (v.ds.length : Int) - w.ds.length > 150 then
    let p := pylongIntDivmod v.toInt w.toInt
    .ok (Long.ofInt p.1, Long.ofInt p.2)
  else
    match longDivrem v w with
    | .error e => .error e
    | .ok (div, md) =>
      if needsFix md w then
        match longAdd md w with
        | .error e => .error e
        | .ok m =>
          match longSub div longOne with
          | .error e => .error e
          | .ok d => .ok (d, m)
      else .ok (div, md)

/-- `l_mod(v, w, &mod)`, longobject.c:4457-4480. -/
def lMod (v w : Long) : Py Long :=
  if v.ds.length = 1 ∧ w.ds.length = 1 then .ok (fastPair v w).2
  else
    match longRem v w with
    | .error e => .error e
    | .ok md => if needsFix md w then longAdd md w else .ok md

/-- `long_div(a, b)`, longobject.c:4483-4496. -/
def longDiv (a b : Long) : Py Long :=
  if a.ds.length = 1 ∧ b.ds.length = 1 then .ok (fastPair a b).1
  else
    match lDivmod a b with
    | .error e => .error e
    | .ok p => .ok p.1

/-- `long_mod(a, b)`, longobject.c:4761-4770. -/
def longMod (a b : Long) : Py Long := lMod a b

/-- `long_divmod(a, b)`, longobject.c:4773-4793. -/
def longDivmod (a b : Long) : Py (Long × Long) := lDivmod a b

/-- Apply `Long.ofInt` to both parts of a `divmod` result. -/
def ofPair : Py (Int × Int) → Py (Long × Long)
  | .ok p => .ok (Long.ofInt p.1, Long.ofInt p.2)
  | .error e => .error e

theorem digitCount_mono {x y : Nat} (h : x ≤ y) : digitCount x ≤ digitCount y := by
  have h1 : x < 2 ^ bitLength y := Nat.lt_of_le_of_lt h (lt_two_pow_bitLength' y)
  have h2 := bitLength_le_of_lt' h1
  unfold digitCount
  omega

theorem length_ofInt_ds (v : Int) : (Long.ofInt v).ds.length = digitCount v.natAbs :=
  length_digitsOf _

theorem toInt_ofInt_eq (v : Int) : (Long.ofInt v).toInt = v := Long.toInt_ofInt v

theorem natAbs_tmod_lt (v w : Int) (hw : w ≠ 0) : (v.tmod w).natAbs < w.natAbs := by
  rw [tmod_natAbs]
  have := Nat.mod_lt v.natAbs (show 0 < w.natAbs by omega)
  generalize v.natAbs % w.natAbs = M at *
  split <;> omega

theorem natAbs_tdiv_le (v w : Int) : (v.tdiv w).natAbs ≤ v.natAbs := by
  rw [tdiv_natAbs]
  have := Nat.div_le_self v.natAbs w.natAbs
  generalize v.natAbs / w.natAbs = Q at *
  split <;> omega

theorem needsFix_ofInt (m w : Int) :
    needsFix (Long.ofInt m) (Long.ofInt w) = decide ((m < 0 ∧ w > 0) ∨ (m > 0 ∧ w < 0)) := by
  have h : ∀ x : Int, (Long.ofInt x).isPositive = decide (x > 0) := by
    intro x
    simp only [Long.isPositive, Long.ofInt]
    by_cases hx : x = 0
    · subst hx; simp
    · have hne : digitsOf x.natAbs ≠ [] := by rw [Ne, digitsOf_eq_nil]; omega
      have he : (digitsOf x.natAbs).isEmpty = false := by
        cases hh : digitsOf x.natAbs with
        | nil => exact absurd hh hne
        | cons _ _ => rfl
      rw [he]
      by_cases h2 : x < 0
      · have h3 : ¬ x > 0 := by omega
        simp [h2, h3]
      · have h3 : x > 0 := by omega
        simp [h2, h3]
  have hn : ∀ x : Int, (Long.ofInt x).neg = decide (x < 0) := fun _ => rfl
  simp only [needsFix, h, hn]
  by_cases h1 : m < 0 <;> by_cases h2 : w > 0 <;> by_cases h3 : m > 0 <;> by_cases h4 : w < 0 <;>
    simp [h1, h2, h3, h4]

/-- A size bound that holds of every operand: `long_alloc` cannot refuse a
request made while dividing these. -/
def DivSized (v w : Int) : Prop :=
  digitCount v.natAbs + 2 ≤ maxLongDigits ∧ digitCount w.natAbs + 2 ≤ maxLongDigits

/-- The digit-level `l_divmod` returns exactly the objects of `MathInt.divmod`,
which modelled `long_divrem` as exact division, so that assumption is discharged. -/
theorem lDivmod_eq (v w : Int) (hs : DivSized v w) :
    lDivmod (Long.ofInt v) (Long.ofInt w) = ofPair (divmod v w) := by
  obtain ⟨hv, hw⟩ := hs
  unfold lDivmod divmod
  simp only [length_ofInt_ds, toInt_ofInt_eq]
  by_cases h1 : digitCount v.natAbs = 1 ∧ digitCount w.natAbs = 1
  · simp only [h1, and_self, ite_true, ofPair, fastPair, toInt_ofInt_eq]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : digitCount w.natAbs > 300 ∧ (digitCount v.natAbs : Int) - digitCount w.natAbs > 150
    · simp only [h2, gt_iff_lt, and_self, ite_true, ofPair]
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : w = 0
      · subst h3
        simp [longDivrem, Long.ofInt, ofPair]
      · rw [if_neg h3, longDivrem_spec v w h3 (by omega)]
        simp only [needsFix_ofInt, decide_eq_true_eq]
        have hm := natAbs_tmod_lt v w h3
        have hq := natAbs_tdiv_le v w
        have sm : Sized (v.tmod w) := by
          have := digitCount_mono (Nat.le_of_lt hm)
          simp only [Sized]; omega
        have sw : Sized w := by simp only [Sized]; omega
        have sq : Sized (v.tdiv w) := by
          have := digitCount_mono hq
          simp only [Sized]; omega
        have s1 : Sized 1 := by unfold Sized; decide
        by_cases hfix : (v.tmod w < 0 ∧ w > 0) ∨ (v.tmod w > 0 ∧ w < 0)
        · simp only [hfix, ite_true]
          rw [longAdd_spec _ _ sm sw]
          simp only
          rw [longOne_eq, longSub_spec _ _ sq s1]
          simp only [ofPair]
        · simp only [hfix, ite_false, ofPair]

/-- Python's `//`/`%` relation holds of the digit-level `l_divmod`: quotient and
remainder are canonical objects, `q*w + r == v`, and `r` takes the sign of `w`. -/
theorem lDivmod_floor (v w : Int) (hs : DivSized v w) (hw : w ≠ 0) :
    ∃ q r, lDivmod (Long.ofInt v) (Long.ofInt w) = .ok (Long.ofInt q, Long.ofInt r) ∧
      IsFloorDivmod v w q r := by
  obtain ⟨q, r, h1, h2⟩ := (divmod_floor_proven v w).2 hw
  exact ⟨q, r, by rw [lDivmod_eq v w hs, h1]; rfl, h2⟩

end PyLean.LongObj
