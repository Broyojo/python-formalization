import PyLean.MathInt.FltHypot

/-!
# Property: `isclose`

`math_isclose_impl` (Modules/mathmodule.c:2587-2628) against Doc/library/math.rst: "If no
errors occur, the result will be: `abs(a-b) <= max(rel_tol * max(abs(a), abs(b)), abs_tol)`",
evaluated in Python floats, for finite `a`, `b` and the documented tolerances; IEEE special
values ("NaN is not considered close to any other value, including NaN. inf and -inf are only
considered close to themselves"); negative tolerances rejected; and symmetry.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-- Python's built-in `max(a, b)` on two floats: `b` if `b > a`, else `a`. -/
def pyMax (a b : F64) : F64 := if F64.lt a b then b else a

/-- `isclose(a, b, rel_tol=rt, abs_tol=atol)` on floats.

* A negative tolerance raises `ValueError("tolerances must be non-negative")`, whatever `a` and
  `b` are.
* With `0 <= rel_tol < 1` and `abs_tol >= 0` ("rel_tol must be nonnegative and less than 1.0",
  "it must be nonnegative"): a NaN is close to nothing; an infinity only to itself; finite `a`
  and `b` are close exactly when `abs(a-b) <= max(rel_tol * max(abs(a), abs(b)), abs_tol)` in
  Python float arithmetic; and `isclose(a, b) == isclose(b, a)`.
* `math.isclose(a, b)` with no tolerances uses `rel_tol=1e-09`, `abs_tol=0.0`. -/
def IsCloseDoc : Prop :=
  (∀ a b : F64, math_isclose (.float a) (.float b) none none = isclose_impl a b relTolDefault c0) ∧
  ∀ a b rt atol : F64,
    ((F64.lt rt c0 || F64.lt atol c0) = true →
      isclose_impl a b rt atol = .error (.valueError "tolerances must be non-negative")) ∧
    (F64.le c0 rt = true → F64.lt rt c1 = true → F64.le c0 atol = true →
      ((a.isNaN || b.isNaN) = true → isclose_impl a b rt atol = .ok false) ∧
      ((a.isNaN || b.isNaN) = false → (a.isInf || b.isInf) = true →
        isclose_impl a b rt atol = .ok (F64.eq a b)) ∧
      (a.isFinite = true → b.isFinite = true → isclose_impl a b rt atol =
        .ok (F64.le (F64.abs (F64.sub a b)) (pyMax (F64.mul rt (pyMax (F64.abs a) (F64.abs b))) atol))) ∧
      isclose_impl a b rt atol = isclose_impl b a rt atol)

/-! ## Values of rounded operations -/

/-- The value `ofRat` rounds `q` to (`0` for an infinity). -/
abbrev rnd (q : Rat) : Rat := (ofRat q).toRat

theorem rnd_zero : rnd 0 = 0 := by unfold rnd; rw [ofRat_zero, zero_toRat]

theorem rnd_neg (q : Rat) : rnd (-q) = - rnd q := by
  by_cases hq : q = 0
  · subst hq; simp [rnd_zero]
  · unfold rnd; rw [ofRat_neg hq, toRat_neg]

theorem ofRat_zero_finite : (ofRat 0).isFinite = true := by rw [ofRat_zero]; exact zero_isFinite _

theorem rnd_nonneg {q : Rat} (h : 0 ≤ q) : 0 ≤ rnd q := by
  unfold rnd
  cases hf : (ofRat q).isFinite
  · rw [toRat_of_not_finite hf]; exact Rat.le_refl
  · have := ofRat_mono h ofRat_zero_finite hf
    rwa [ofRat_zero, zero_toRat] at this

theorem abs_toRat (y : F64) : (F64.abs y).toRat = Rat.abs y.toRat := by
  unfold F64.abs
  cases hs : y.sign
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hf : y.isFinite
    · rw [toRat_of_not_finite hf]; rfl
    · rw [abs_of_nonneg]
      rw [toRat_of_finite hf, hs]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (pw_pos _))
  · simp only [↓reduceIte]
    rw [toRat_neg]
    cases hf : y.isFinite
    · rw [toRat_of_not_finite hf]; rfl
    · rw [abs_of_nonpos]
      rw [toRat_of_finite hf, hs]; simp only [↓reduceIte]
      have := Rat.mul_nonneg (Rat.natCast_nonneg (a := y.mant)) (Rat.le_of_lt (pw_pos y.lsbExp))
      grind

theorem sub_facts {a b : F64} (fa : a.isFinite = true) (fb : b.isFinite = true) :
    (F64.sub a b).toRat = rnd (a.toRat - b.toRat) ∧
    (F64.sub a b).isFinite = (ofRat (a.toRat - b.toRat)).isFinite ∧ (F64.sub a b).isNaN = false := by
  have hnb : b.neg.isFinite = true := by rw [neg_isFinite]; exact fb
  unfold F64.sub
  rw [add_of_finite fa hnb, toRat_neg]
  have e : a.toRat + -b.toRat = a.toRat - b.toRat := by grind
  rw [e]
  split
  · rename_i h
    rw [h, rnd_zero, zero_toRat, ofRat_zero_finite, zero_isFinite]
    exact ⟨rfl, rfl, isNaN_false_of_finite (zero_isFinite _)⟩
  · exact ⟨rfl, rfl, ofRat_isNaN _⟩

theorem mul_facts {a b : F64} (fa : a.isFinite = true) (fb : b.isFinite = true) :
    (F64.mul a b).toRat = rnd (a.toRat * b.toRat) ∧
    (F64.mul a b).isFinite = (ofRat (a.toRat * b.toRat)).isFinite ∧ (F64.mul a b).isNaN = false := by
  rw [mul_of_finite fa fb]
  split
  · rename_i h
    rw [h, rnd_zero, zero_toRat, ofRat_zero_finite, zero_isFinite]
    exact ⟨rfl, rfl, isNaN_false_of_finite (zero_isFinite _)⟩
  · exact ⟨rfl, rfl, ofRat_isNaN _⟩

theorem ofRat_finite_of_le {p q : Rat} (h : Rat.abs p ≤ Rat.abs q) (hq : (ofRat q).isFinite = true) :
    (ofRat p).isFinite = true := by
  rw [ofRat_isFinite] at hq ⊢
  exact (by grind : ∀ {x y z : Rat}, x ≤ y → y < z → x < z) h hq

theorem abs_finite (y : F64) : (F64.abs y).isFinite = y.isFinite := abs_isFinite y

theorem le_val {u v : F64} (hu : u.isFinite = true) (hv : v.isFinite = true) :
    F64.le u v = decide (u.toRat ≤ v.toRat) := le_of_finite hu hv

/-- A rounded product with a factor in `[0, 1)` stays finite. -/
theorem small_mul_finite {rt b : F64} (fr : rt.isFinite = true) (fb : b.isFinite = true)
    (h0 : 0 ≤ rt.toRat) (h1 : rt.toRat < 1) : (ofRat (rt.toRat * b.toRat)).isFinite = true := by
  apply ofRat_finite_of_le (q := b.toRat) _ ((ofRat_isFinite _).2 (abs_toRat_lt fb))
  rw [abs_eq_ite (rt.toRat * b.toRat), abs_eq_ite b.toRat]
  by_cases hb : b.toRat < 0
  · have p1 : rt.toRat * b.toRat ≤ 0 := by
      have := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hb) h0; grind
    have p2 : rt.toRat * -b.toRat ≤ 1 * -b.toRat :=
      Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt h1) (by grind)
    have p3 : rt.toRat * -b.toRat = -(rt.toRat * b.toRat) := by grind
    simp only [hb, ↓reduceIte]
    split <;> grind
  · have p1 : 0 ≤ rt.toRat * b.toRat := Rat.mul_nonneg h0 (by grind)
    have p2 : rt.toRat * b.toRat ≤ 1 * b.toRat :=
      Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt h1) (by grind)
    simp only [hb, ↓reduceIte]
    split <;> grind

theorem rnd_abs_mul {rt b : F64} (h0 : 0 ≤ rt.toRat) :
    Rat.abs (rnd (rt.toRat * b.toRat)) = rnd (rt.toRat * Rat.abs b.toRat) := by
  rw [abs_eq_ite b.toRat]
  split
  · rename_i hb
    rw [show rt.toRat * -b.toRat = -(rt.toRat * b.toRat) by grind, rnd_neg]
    have : rt.toRat * b.toRat ≤ 0 := by
      have := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hb) h0; grind
    have hn := rnd_nonneg (q := -(rt.toRat * b.toRat)) (by grind)
    rw [rnd_neg] at hn
    rw [abs_eq_ite]; split <;> grind
  · rename_i hb
    have : 0 ≤ rt.toRat * b.toRat := Rat.mul_nonneg h0 (by grind)
    rw [abs_of_nonneg (rnd_nonneg this)]

theorem inf_false_facts : (F64.inf false).isNaN = false ∧ (F64.inf false).isInf = true ∧
    (F64.inf false).sign = false ∧ (F64.inf false).isFinite = false := by decide +kernel

theorem le_inf_true {v : F64} (hn : v.isNaN = false) : F64.le v (F64.inf false) = true := by
  unfold F64.le F64.lt F64.eq
  cases hi : v.isInf
  · simp [hn, hi, inf_false_facts]
  · cases hs : v.sign <;> simp [hn, hi, hs, inf_false_facts]

theorem inf_le_fin {v : F64} (hv : v.isFinite = true) : F64.le (F64.inf false) v = false := by
  unfold F64.le F64.lt F64.eq
  simp [isNaN_false_of_finite hv, isInf_false_of_finite hv, inf_false_facts]

theorem lt_fin_inf {v : F64} (hv : v.isFinite = true) : F64.lt v (F64.inf false) = true := by
  unfold F64.lt
  simp [isNaN_false_of_finite hv, isInf_false_of_finite hv, inf_false_facts]

theorem rt_facts {rt : F64} (h0 : F64.le c0 rt = true) (h1 : F64.lt rt c1 = true) :
    rt.isFinite = true ∧ 0 ≤ rt.toRat ∧ rt.toRat < 1 := by
  have hc1 : c1.isFinite = true ∧ c1.toRat = 1 := by decide +kernel
  rcases classify rt with h | h | h
  · refine ⟨h, ?_, ?_⟩
    · rw [le_val c0_facts.1 h, c0_facts.2.2.1] at h0; simpa using h0
    · rw [lt_of_finite h hc1.1, hc1.2] at h1; simpa using h1
  · exfalso
    have e := eq_inf_of_isInf h
    cases hs : rt.sign
    · rw [e, hs] at h1; revert h1; decide +kernel
    · rw [e, hs] at h0; revert h0; decide +kernel
  · exfalso; revert h0; unfold F64.le F64.lt F64.eq; simp [h]

theorem atol_cases {atol : F64} (h2 : F64.le c0 atol = true) :
    (atol.isFinite = true ∧ 0 ≤ atol.toRat) ∨ atol = F64.inf false := by
  rcases classify atol with h | h | h
  · left; refine ⟨h, ?_⟩
    rw [le_val c0_facts.1 h, c0_facts.2.2.1] at h2; simpa using h2
  · right
    have e := eq_inf_of_isInf h
    cases hs : atol.sign
    · rw [e, hs]
    · exfalso; rw [e, hs] at h2; revert h2; decide +kernel
  · exfalso; revert h2; unfold F64.le F64.lt F64.eq; simp [h]

theorem neg_tol_false {rt atol : F64} (h0 : F64.le c0 rt = true) (h2 : F64.le c0 atol = true) :
    (F64.lt rt c0 || F64.lt atol c0) = false := by
  have key : ∀ v : F64, F64.le c0 v = true → F64.lt v c0 = false := by
    intro v hv
    rcases classify v with h | h | h
    · rw [le_val c0_facts.1 h, c0_facts.2.2.1] at hv
      rw [lt_of_finite h c0_facts.1, c0_facts.2.2.1]; simp at hv ⊢; grind
    · have e := eq_inf_of_isInf h
      cases hs : v.sign
      · rw [e, hs]; decide +kernel
      · exfalso; rw [e, hs] at hv; revert hv; decide +kernel
    · exfalso; revert hv; unfold F64.le F64.lt F64.eq; simp [h]
  rw [key rt h0, key atol h2]; rfl

theorem combine_true (D X Y A : Rat) (h : (if X < Y then Y else X) < A) :
    (decide (D ≤ Y) || decide (D ≤ X) || decide (D ≤ A)) = decide (D ≤ A) := by
  by_cases h1 : D ≤ A <;> by_cases h2 : D ≤ X <;> by_cases h3 : D ≤ Y <;>
    simp only [h1, h2, h3, decide_true, decide_false, Bool.or_true, Bool.or_false, Bool.true_or,
      Bool.false_or] <;> split at h <;> grind

theorem combine_false (D X Y A : Rat) (h : ¬ (if X < Y then Y else X) < A) :
    (decide (D ≤ Y) || decide (D ≤ X) || decide (D ≤ A)) = decide (D ≤ (if X < Y then Y else X)) := by
  by_cases hc : X < Y
  · rw [if_pos hc] at h ⊢
    by_cases h1 : D ≤ A <;> by_cases h2 : D ≤ X <;> by_cases h3 : D ≤ Y <;>
      simp only [h1, h2, h3, decide_true, decide_false, Bool.or_true, Bool.or_false, Bool.true_or,
        Bool.false_or] <;> grind
  · rw [if_neg hc] at h ⊢
    by_cases h1 : D ≤ A <;> by_cases h2 : D ≤ X <;> by_cases h3 : D ≤ Y <;>
      simp only [h1, h2, h3, decide_true, decide_false, Bool.or_true, Bool.or_false, Bool.true_or,
        Bool.false_or] <;> grind

theorem isclose_finite (a b rt atol : F64) (fa : a.isFinite = true) (fb : b.isFinite = true)
    (h0 : F64.le c0 rt = true) (h1 : F64.lt rt c1 = true) (h2 : F64.le c0 atol = true) :
    isclose_impl a b rt atol =
      .ok (F64.le (F64.abs (F64.sub a b)) (pyMax (F64.mul rt (pyMax (F64.abs a) (F64.abs b))) atol)) := by
  obtain ⟨frt, hrt0, hrt1⟩ := rt_facts h0 h1
  unfold isclose_impl
  rw [neg_tol_false h0 h2]
  simp only [Bool.false_eq_true, ↓reduceIte, isInf_false_of_finite fa, isInf_false_of_finite fb,
    Bool.or_false]
  -- the finite quantities
  obtain ⟨dbv, dbf, dbn⟩ := sub_facts fb fa
  obtain ⟨dav, daf, dan⟩ := sub_facts fa fb
  have hdiff : (F64.abs (F64.sub b a)).toRat = (F64.abs (F64.sub a b)).toRat := by
    rw [abs_toRat, abs_toRat, dbv, dav, show b.toRat - a.toRat = -(a.toRat - b.toRat) by grind,
      rnd_neg, abs_neg]
  have hdfin : (F64.abs (F64.sub b a)).isFinite = (F64.abs (F64.sub a b)).isFinite := by
    rw [abs_finite, abs_finite, dbf, daf, show b.toRat - a.toRat = -(a.toRat - b.toRat) by grind]
    by_cases hq : a.toRat - b.toRat = 0
    · rw [hq, show -(0 : Rat) = 0 by decide]
    · rw [ofRat_neg hq, neg_isFinite]
  obtain ⟨xbv, xbf, _⟩ := mul_facts frt fb
  obtain ⟨xav, xaf, _⟩ := mul_facts frt fa
  have fXb : (F64.abs (F64.mul rt b)).isFinite = true := by
    rw [abs_finite, xbf]; exact small_mul_finite frt fb hrt0 hrt1
  have fXa : (F64.abs (F64.mul rt a)).isFinite = true := by
    rw [abs_finite, xaf]; exact small_mul_finite frt fa hrt0 hrt1
  have vXb : (F64.abs (F64.mul rt b)).toRat = rnd (rt.toRat * Rat.abs b.toRat) := by
    rw [abs_toRat, xbv, rnd_abs_mul hrt0]
  have vXa : (F64.abs (F64.mul rt a)).toRat = rnd (rt.toRat * Rat.abs a.toRat) := by
    rw [abs_toRat, xav, rnd_abs_mul hrt0]
  -- the documented formula
  have fAa : (F64.abs a).isFinite = true := by rw [abs_finite]; exact fa
  have fAb : (F64.abs b).isFinite = true := by rw [abs_finite]; exact fb
  have hM : (pyMax (F64.abs a) (F64.abs b)).isFinite = true ∧
      (pyMax (F64.abs a) (F64.abs b)).toRat = (if Rat.abs a.toRat < Rat.abs b.toRat then Rat.abs b.toRat
        else Rat.abs a.toRat) := by
    unfold pyMax
    rw [lt_of_finite fAa fAb, abs_toRat, abs_toRat]
    by_cases hc : Rat.abs a.toRat < Rat.abs b.toRat
    · simp only [hc, decide_true, ↓reduceIte]; exact ⟨fAb, abs_toRat b⟩
    · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]; exact ⟨fAa, abs_toRat a⟩
  obtain ⟨tv, tf, _⟩ := mul_facts frt hM.1
  have fT : (F64.mul rt (pyMax (F64.abs a) (F64.abs b))).isFinite = true := by
    rw [tf]; exact small_mul_finite frt hM.1 hrt0 hrt1
  generalize hX : rnd (rt.toRat * Rat.abs a.toRat) = X at vXa
  generalize hY : rnd (rt.toRat * Rat.abs b.toRat) = Y at vXb
  have vT : (F64.mul rt (pyMax (F64.abs a) (F64.abs b))).toRat = (if X < Y then Y else X) := by
    rw [tv, hM.2]
    have fa' := small_mul_finite (b := F64.abs a) frt fAa hrt0 hrt1
    have fb' := small_mul_finite (b := F64.abs b) frt fAb hrt0 hrt1
    rw [abs_toRat] at fa' fb'
    by_cases hlt : Rat.abs a.toRat < Rat.abs b.toRat
    · have hm := ofRat_mono (Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hlt) hrt0) fa' fb'
      simp only [hlt, ↓reduceIte]
      have hY' : rnd (rt.toRat * Rat.abs b.toRat) = Y := hY
      rw [hY']
      by_cases hc : X < Y
      · simp [hc]
      · simp only [hc, ↓reduceIte]; grind
    · have hm := ofRat_mono (Rat.mul_le_mul_of_nonneg_left (Rat.not_lt.1 hlt) hrt0) fb' fa'
      simp only [hlt, ↓reduceIte]
      have hX' : rnd (rt.toRat * Rat.abs a.toRat) = X := hX
      rw [hX']
      by_cases hc : X < Y
      · simp only [hc, ↓reduceIte]; grind
      · simp [hc]
  have hX0 : 0 ≤ X := by rw [← hX]; exact rnd_nonneg (Rat.mul_nonneg hrt0 (abs_nonneg _))
  have hY0 : 0 ≤ Y := by rw [← hY]; exact rnd_nonneg (Rat.mul_nonneg hrt0 (abs_nonneg _))
  generalize F64.mul rt (pyMax (F64.abs a) (F64.abs b)) = T at fT vT
  generalize F64.abs (F64.mul rt a) = XA at fXa vXa
  generalize F64.abs (F64.mul rt b) = XB at fXb vXb
  by_cases heq : F64.eq a b = true
  · simp only [heq, ↓reduceIte]
    rw [eq_of_finite fa fb] at heq
    have hab : a.toRat - b.toRat = 0 := by simp at heq; grind
    have hD : (F64.abs (F64.sub a b)).isFinite = true ∧ (F64.abs (F64.sub a b)).toRat = 0 := by
      rw [abs_finite, daf, hab, abs_toRat, dav, hab, rnd_zero]
      exact ⟨ofRat_zero_finite, by decide⟩
    unfold pyMax
    rcases atol_cases h2 with ⟨fat, hat0⟩ | hat
    · rw [lt_of_finite fT fat]
      split
      · rw [le_val hD.1 fat, hD.2]; simp [hat0]
      · rw [le_val hD.1 fT, hD.2, vT]; simp; split <;> assumption
    · subst hat
      rw [lt_fin_inf fT]
      simp only [↓reduceIte]
      rw [le_inf_true (isNaN_false_of_finite hD.1)]
  · simp only [heq, Bool.false_eq_true, ↓reduceIte]
    congr 1
    by_cases hdf : (F64.abs (F64.sub a b)).isFinite = true
    · have hdf' : (F64.abs (F64.sub b a)).isFinite = true := by rw [hdfin]; exact hdf
      rw [le_val hdf' fXb, le_val hdf' fXa, hdiff, vXb, vXa]
      unfold pyMax
      rcases atol_cases h2 with ⟨fat, hat0⟩ | hat
      · rw [le_val hdf' fat, hdiff]
        by_cases hta : F64.lt T atol = true
        · simp only [hta, ↓reduceIte, le_val hdf fat]
          rw [lt_of_finite fT fat, vT] at hta
          generalize (F64.abs (F64.sub a b)).toRat = D
          exact combine_true D X Y _ (of_decide_eq_true hta)
        · simp only [hta, Bool.false_eq_true, ↓reduceIte, le_val hdf fT, vT]
          rw [lt_of_finite fT fat, vT] at hta
          generalize (F64.abs (F64.sub a b)).toRat = D
          exact combine_false D X Y _ (fun h => hta (decide_eq_true h))
      · subst hat
        rw [lt_fin_inf fT, le_inf_true (isNaN_false_of_finite hdf')]
        simp only [↓reduceIte, Bool.or_true]
        rw [le_inf_true (isNaN_false_of_finite hdf)]
    · -- the difference overflows: close only for `abs_tol == inf`
      have hdf' : (F64.abs (F64.sub b a)).isFinite = false := by rw [hdfin]; simpa using hdf
      have inf_of : ∀ y : F64, (F64.abs y).isFinite = false → y.isNaN = false →
          F64.abs y = F64.inf false := by
        intro y hf hn
        rcases classify (F64.abs y) with h | h | h
        · rw [h] at hf; cases hf
        · rw [eq_inf_of_isInf h, (abs_fields y).1]
        · rw [abs_isNaN, hn] at h; cases h
      rw [inf_of _ hdf' dbn, inf_of _ (by simpa using hdf) dan, inf_le_fin fXb, inf_le_fin fXa]
      unfold pyMax
      rcases atol_cases h2 with ⟨fat, _⟩ | hat
      · rw [inf_le_fin fat]
        split
        · rw [inf_le_fin fat]; rfl
        · rw [inf_le_fin fT]; rfl
      · subst hat
        rw [lt_fin_inf fT]
        simp only [↓reduceIte]
        rw [le_inf_true inf_false_facts.1]
        rfl

theorem abs_sub_comm {a b : F64} (fa : a.isFinite = true) (fb : b.isFinite = true) :
    F64.abs (F64.sub b a) = F64.abs (F64.sub a b) := by
  obtain ⟨dbv, dbf, dbn⟩ := sub_facts fb fa
  obtain ⟨dav, daf, dan⟩ := sub_facts fa fb
  have hv : (F64.abs (F64.sub b a)).toRat = (F64.abs (F64.sub a b)).toRat := by
    rw [abs_toRat, abs_toRat, dbv, dav, show b.toRat - a.toRat = -(a.toRat - b.toRat) by grind,
      rnd_neg, abs_neg]
  have hf : (F64.abs (F64.sub b a)).isFinite = (F64.abs (F64.sub a b)).isFinite := by
    rw [abs_finite, abs_finite, dbf, daf, show b.toRat - a.toRat = -(a.toRat - b.toRat) by grind]
    by_cases hq : a.toRat - b.toRat = 0
    · rw [hq, show -(0 : Rat) = 0 by decide]
    · rw [ofRat_neg hq, neg_isFinite]
  have s1 := (abs_fields (F64.sub b a)).1
  have s2 := (abs_fields (F64.sub a b)).1
  cases h2 : (F64.abs (F64.sub a b)).isFinite
  · rw [h2] at hf
    have i1 : (F64.abs (F64.sub b a)).isInf = true := by
      rcases classify (F64.abs (F64.sub b a)) with h | h | h
      · rw [h] at hf; cases hf
      · exact h
      · rw [abs_isNaN, dbn] at h; cases h
    have i2 : (F64.abs (F64.sub a b)).isInf = true := by
      rcases classify (F64.abs (F64.sub a b)) with h | h | h
      · rw [h] at h2; cases h2
      · exact h
      · rw [abs_isNaN, dan] at h; cases h
    rw [eq_inf_of_isInf i1, eq_inf_of_isInf i2, s1, s2]
  · rw [h2] at hf
    cases hz : (F64.abs (F64.sub b a)).isZero
    · exact toRat_inj hf h2 hz hv
    · have hz2 : (F64.abs (F64.sub a b)).isZero = true := by
        rw [isZero_iff_toRat h2, ← hv]; exact toRat_of_isZero hz
      rw [eq_zero_of_isZero hz, eq_zero_of_isZero hz2, s1, s2]

theorem le_nan {u : F64} (h : u.isNaN = true) (v : F64) : F64.le u v = false := by
  unfold F64.le F64.lt F64.eq; simp [h]

theorem eq_comm' (a b : F64) : F64.eq a b = F64.eq b a := by
  unfold F64.eq
  cases ha : a.isNaN <;> cases hb : b.isNaN <;> simp only [Bool.or_false, Bool.false_or,
    Bool.or_true, Bool.true_or, Bool.false_eq_true, ↓reduceIte]
  cases hai : a.isInf <;> cases hbi : b.isInf <;> simp only [Bool.or_false, Bool.false_or,
    Bool.or_true, Bool.true_or, Bool.false_eq_true, ↓reduceIte, Bool.true_and, Bool.false_and,
    Bool.and_false, Bool.and_true]
  · simp only [decide_eq_decide]; exact ⟨fun h => h.symm, fun h => h.symm⟩
  · cases a.sign <;> cases b.sign <;> rfl

theorem sub_nan {a b : F64} (h : (a.isNaN || b.isNaN) = true) : (F64.sub a b).isNaN = true := by
  unfold F64.sub F64.add
  rw [neg_isNaN]
  simp [h, qnan_facts.2]

theorem isCloseDoc_proven : IsCloseDoc := by
  refine ⟨fun a b => by simp only [math_isclose, convDouble, bind, Except.bind, pure, Except.pure],
    fun a b rt atol => ⟨fun hneg => ?_, fun h0 h1 h2 => ?_⟩⟩
  · unfold isclose_impl; rw [hneg]; rfl
  · have hn0 := neg_tol_false h0 h2
    refine ⟨fun hn => ?_, fun hn hi => ?_, fun fa fb => isclose_finite a b rt atol fa fb h0 h1 h2, ?_⟩
    · unfold isclose_impl
      rw [hn0]
      have heq : F64.eq a b = false := by unfold F64.eq; simp [hn]
      simp only [Bool.false_eq_true, ↓reduceIte, heq]
      split
      · rfl
      · have hd : (F64.abs (F64.sub b a)).isNaN = true := by
          rw [abs_isNaN]; apply sub_nan; rw [Bool.or_comm]; exact hn
        rw [le_nan hd, le_nan hd, le_nan hd]; rfl
    · unfold isclose_impl
      rw [hn0]
      simp only [Bool.false_eq_true, ↓reduceIte, hi]
      split
      · rename_i h; rw [h]
      · rename_i h; simp at h; rw [h]
    · unfold isclose_impl
      rw [hn0]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [eq_comm' b a, Bool.or_comm b.isInf]
      split
      · rfl
      · split
        · rfl
        · rename_i hinf
          have hinf' : (a.isInf || b.isInf) = false := by simpa using hinf
          by_cases hfab : (a.isFinite && b.isFinite) = true
          · simp at hfab
            rw [abs_sub_comm hfab.1 hfab.2]
            cases F64.le (F64.abs (F64.sub a b)) (F64.abs (F64.mul rt b)) <;>
              cases F64.le (F64.abs (F64.sub a b)) (F64.abs (F64.mul rt a)) <;> rfl
          · have hnan : (a.isNaN || b.isNaN) = true := by
              simp at hinf'
              rcases classify a with h | h | h <;> rcases classify b with h' | h' | h' <;>
                simp_all
            have d1 : (F64.abs (F64.sub b a)).isNaN = true := by
              rw [abs_isNaN]; apply sub_nan; rw [Bool.or_comm]; exact hnan
            have d2 : (F64.abs (F64.sub a b)).isNaN = true := by
              rw [abs_isNaN]; apply sub_nan; exact hnan
            rw [le_nan d1, le_nan d1, le_nan d1, le_nan d2, le_nan d2, le_nan d2]

end PyLean.MathInt
