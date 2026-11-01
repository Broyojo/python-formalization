import PyLean.LongObj.Div

/-!
The Python-level division operators on the digit model: `long_rem`, `l_divmod`,
`l_mod`, `long_div`, `long_mod`, `long_divmod`, `pylong_int_divmod`.

`lDivmod_eq` is the bridge to `MathInt`: the digit-level `l_divmod` returns the
canonical objects of `MathInt.divmod`, which assumed `long_divrem` exact.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-- The constant `_PyLong_GetOne()`, longobject.c:4534. -/
def longOne : Long := ⟨false, [1]⟩

theorem longOne_eq : longOne = Long.ofInt 1 := by decide

/-- `_PyLong_IsPositive(x)`, pycore_long.h:230-233. -/
def Long.isPositive (x : Long) : Bool := !x.neg && !x.ds.isEmpty

/-- The sign test at longobject.c:4525-4526 and :4572-4573. -/
def needsFix (md w : Long) : Bool :=
  (md.neg && w.isPositive) || (md.isPositive && w.neg)

/-- `fast_floor_div` and `fast_mod`, longobject.c:4378-4418, on one-digit objects,
returned through `PyLong_FromLong`. -/
def fastPair (v w : Long) : Long × Long :=
  let p := fastDivmod v.toInt w.toInt
  (Long.ofInt p.1, Long.ofInt p.2)

/-- `l_divmod(v, w, &div, &mod)`, longobject.c:4482-4553. The `_pylong` branch is
`pylong_int_divmod`, :4423-4457, with `MathInt.pylongIntDivmod` as its result. -/
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

/-- `l_mod(v, w, &mod)`, longobject.c:4560-4583. -/
def lMod (v w : Long) : Py Long :=
  if v.ds.length = 1 ∧ w.ds.length = 1 then .ok (fastPair v w).2
  else
    match longRem v w with
    | .error e => .error e
    | .ok md => if needsFix md w then longAdd md w else .ok md

/-- `long_div(a, b)`, longobject.c:4586-4599. -/
def longDiv (a b : Long) : Py Long :=
  if a.ds.length = 1 ∧ b.ds.length = 1 then .ok (fastPair a b).1
  else
    match lDivmod a b with
    | .error e => .error e
    | .ok p => .ok p.1

/-- `long_mod(a, b)`, longobject.c:4864-4873. -/
def longMod (a b : Long) : Py Long := lMod a b

/-- `long_divmod(a, b)`, longobject.c:4876-4885. -/
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

/-- The sign fix-up of a remainder, longobject.c:3266-3273 and :3310-3316. -/
theorem rem_sign (a : Int) (R : Nat) :
    (if (decide (a < 0) && !(digitsOf R).isEmpty) = true then
        (⟨false, digitsOf R⟩ : Long).flip else ⟨false, digitsOf R⟩) =
      Long.ofInt (if a < 0 then -(R : Int) else R) := by
  have s2 := signed_ofInt (decide (a < 0)) R
  have e2 : (if decide (a < 0) = true then -(R : Int) else (R : Int)) =
      (if a < 0 then -(R : Int) else R) := by simp only [decide_eq_true_eq]
  rw [e2] at s2
  rw [← s2]
  by_cases hz : digitsOf R = []
  · simp [hz, Long.flip]
  · have : (digitsOf R).isEmpty = false := by
      cases hh : digitsOf R with
      | nil => exact absurd hh hz
      | cons _ _ => rfl
    simp [this]

/-- `long_rem` returns the canonical truncated remainder, on the shortcut, on `rem1`
and on `x_divrem`. -/
theorem longRem_spec (a b : Int) (hb : b ≠ 0) (hs : digitCount a.natAbs + 1 ≤ maxLongDigits) :
    longRem (Long.ofInt a) (Long.ofInt b) = .ok (Long.ofInt (a.tmod b)) := by
  have dA := digitsOf_digits a.natAbs
  have dB := digitsOf_digits b.natAbs
  have nB := normal_digitsOf b.natAbs
  have lA := length_digitsOf a.natAbs
  have hne : digitsOf b.natAbs ≠ [] := by rw [Ne, digitsOf_eq_nil]; omega
  have hlen : ¬ (digitsOf b.natAbs).length = 0 := by
    intro h; exact hne (List.eq_nil_of_length_eq_zero h)
  have hds : (Long.ofInt a).ds = digitsOf a.natAbs := rfl
  have hdb : (Long.ofInt b).ds = digitsOf b.natAbs := rfl
  have hna : (Long.ofInt a).neg = decide (a < 0) := rfl
  unfold longRem
  simp only [hds, hdb, hna, hlen, ite_false]
  have hrem := rem_sign a (a.natAbs % b.natAbs)
  have etm : (if a < 0 then -((a.natAbs % b.natAbs : Nat) : Int)
      else ((a.natAbs % b.natAbs : Nat) : Int)) = a.tmod b := (tmod_natAbs a b).symm
  rw [etm] at hrem
  by_cases hm : magLess (digitsOf a.natAbs) (digitsOf b.natAbs) = true
  · have hlt := magLess_lt dA dB nB hm
    rw [val_digitsOf, val_digitsOf] at hlt
    simp only [hm, ite_true]
    have e2 : a.tmod b = a := by
      rw [tmod_natAbs, Nat.mod_eq_of_lt hlt]
      split <;> omega
    rw [e2]
  · simp only [hm, Bool.false_eq_true, ite_false]
    have hle : (digitsOf b.natAbs).length ≤ (digitsOf a.natAbs).length := by
      simp only [magLess, decide_eq_true_eq] at hm
      omega
    by_cases h1 : (digitsOf b.natAbs).length = 1
    · rw [if_pos h1]
      generalize hN : digitsOf b.natAbs = bd at *
      match bd, h1, dB, nB with
      | [n], _, dB, nB =>
        have hn : n < 2 ^ 30 := (isDigits_cons.1 dB).1
        have hn0 : 0 < n := by
          have := nB (by simp)
          simp at this
          omega
        have hbv : b.natAbs = n := by
          have := val_digitsOf b.natAbs
          rw [hN] at this
          simpa using this.symm
        have hr : (inplaceDivrem1 n (digitsOf a.natAbs)).2 = a.natAbs % n := by
          obtain ⟨_, _, h3, h4⟩ := inplaceDivrem1_spec hn0 hn _ dA
          rw [val_digitsOf] at h4
          generalize inplaceDivrem1 n (digitsOf a.natAbs) = p at *
          obtain ⟨q, r⟩ := p
          simp only at h3 h4 ⊢
          exact ((Nat.div_mod_unique hn0 (a := a.natAbs) (c := r) (d := val q)).2
            ⟨by omega, h3⟩).2.symm
        have hrlt : a.natAbs % n < 2 ^ 30 := by
          have := Nat.mod_lt a.natAbs hn0
          omega
        simp only [rem1, List.getD_cons_zero]
        rw [inplaceRem1_eq hn0 hn _ dA, hr]
        rw [hbv] at hrem
        generalize a.natAbs % n = m at *
        have hsingle := fromSingle_eq (x := (m : Int)) (by rw [Int.natAbs_natCast]; exact hrlt)
        rw [hsingle, Long.ofInt_natCast]
        exact congrArg Except.ok hrem
    · rw [if_neg h1]
      have h2 : 2 ≤ (digitsOf b.natAbs).length := by
        have : (digitsOf b.natAbs).length ≠ 0 := hlen
        omega
      rw [xDivrem_spec dA dB nB h2 hle (by omega), val_digitsOf, val_digitsOf]
      exact congrArg Except.ok hrem

theorem one_digit_ne_zero {v : Int} (h : digitCount v.natAbs = 1) : v ≠ 0 := by
  intro h0
  subst h0
  simp [digitCount_zero] at h

/-- `v % w` is Python's remainder on the digit-level `l_mod`, on the fast path and on
`long_rem` with its sign fix. -/
theorem lMod_floor (v w : Int) (hs : DivSized v w) (hw : w ≠ 0) :
    ∃ q r, lMod (Long.ofInt v) (Long.ofInt w) = .ok (Long.ofInt r) ∧ IsFloorDivmod v w q r := by
  obtain ⟨hv, hw2⟩ := hs
  unfold lMod
  simp only [length_ofInt_ds]
  by_cases h1 : digitCount v.natAbs = 1 ∧ digitCount w.natAbs = 1
  · rw [if_pos h1]
    refine ⟨_, _, ?_, fastDivmod_floor v w (one_digit_ne_zero h1.1) (one_digit_ne_zero h1.2)⟩
    simp only [fastPair, toInt_ofInt_eq]
  · rw [if_neg h1, longRem_spec v w hw (by omega)]
    simp only [needsFix_ofInt, decide_eq_true_eq]
    have hm := natAbs_tmod_lt v w hw
    have sm : Sized (v.tmod w) := by
      have := digitCount_mono (Nat.le_of_lt hm)
      simp only [Sized]; omega
    have sw : Sized w := by simp only [Sized]; omega
    by_cases hfix : (v.tmod w < 0 ∧ w > 0) ∨ (v.tmod w > 0 ∧ w < 0)
    · simp only [hfix, ite_true]
      rw [longAdd_spec _ _ sm sw]
      rcases tdiv_tmod_floor v w hw with h | ⟨_, h⟩
      · exfalso
        obtain ⟨_, h2, h3⟩ := h
        rcases hfix with ⟨f1, f2⟩ | ⟨f1, f2⟩
        · have := (h2 f2).1; omega
        · have := (h3 f2).2; omega
      · exact ⟨_, _, rfl, h⟩
    · simp only [hfix, ite_false]
      rcases tdiv_tmod_floor v w hw with h | ⟨h, _⟩
      · exact ⟨_, _, rfl, h⟩
      · exact absurd h hfix

/-- `v // w` is the floor quotient on the digit-level `long_div`. -/
theorem longDiv_floor (v w : Int) (hs : DivSized v w) (hw : w ≠ 0) :
    ∃ q r, longDiv (Long.ofInt v) (Long.ofInt w) = .ok (Long.ofInt q) ∧ IsFloorDivmod v w q r := by
  unfold longDiv
  simp only [length_ofInt_ds]
  by_cases h1 : digitCount v.natAbs = 1 ∧ digitCount w.natAbs = 1
  · rw [if_pos h1]
    refine ⟨_, _, ?_, fastDivmod_floor v w (one_digit_ne_zero h1.1) (one_digit_ne_zero h1.2)⟩
    simp only [fastPair, toInt_ofInt_eq]
  · rw [if_neg h1]
    obtain ⟨q, r, h2, h3⟩ := lDivmod_floor v w hs hw
    exact ⟨q, r, by rw [h2], h3⟩

end PyLean.LongObj
