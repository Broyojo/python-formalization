import PyLean.MathInt.FltLemmas

/-!
Order facts about binary64 `+`, `-` and `*` that the distribution properties use:
rounding is monotone, so a bound that holds of the exact result holds of the rounded one.
-/

namespace PyLean.CoreLibs.Rand.F64Order

open PyLean PyLean.Binary64 PyLean.Binary64.F64 PyLean.MathInt

/-- A finite value survives `ofRat ∘ toRat`. -/
theorem ofRat_toRat' {y : F64} (hy : y.isFinite = true) :
    (ofRat y.toRat).isFinite = true ∧ (ofRat y.toRat).toRat = y.toRat := by
  cases hz : y.isZero
  · rw [ofRat_toRat hy hz]; exact ⟨hy, rfl⟩
  · rw [toRat_of_isZero hz, ofRat_zero]
    exact ⟨zero_isFinite false, zero_toRat false⟩

/-- The shape of a rounded nonzero-or-signed-zero result in `add` and `mul`. -/
def rnd (q : Rat) (z : Bool) : F64 := if q = 0 then zero z else ofRat q

theorem rnd_ge {q : Rat} {z : Bool} {y : F64} (hy : y.isFinite = true) (hq : y.toRat ≤ q)
    (hf : (rnd q z).isFinite = true) : y.toRat ≤ (rnd q z).toRat := by
  unfold rnd at hf ⊢
  by_cases h0 : q = 0
  · simp only [h0, if_true] at hf ⊢
    rw [zero_toRat]; rw [h0] at hq; exact hq
  · simp only [h0, if_false] at hf ⊢
    obtain ⟨h1, h2⟩ := ofRat_toRat' hy
    have := ofRat_mono hq h1 hf
    rwa [h2] at this

theorem rnd_le {q : Rat} {z : Bool} {y : F64} (hy : y.isFinite = true) (hq : q ≤ y.toRat)
    (hf : (rnd q z).isFinite = true) : (rnd q z).toRat ≤ y.toRat := by
  unfold rnd at hf ⊢
  by_cases h0 : q = 0
  · simp only [h0, if_true] at hf ⊢
    rw [zero_toRat]; rw [h0] at hq; exact hq
  · simp only [h0, if_false] at hf ⊢
    obtain ⟨h1, h2⟩ := ofRat_toRat' hy
    have := ofRat_mono hq hf h1
    rwa [h2] at this

theorem rnd_isFinite {q : Rat} {z : Bool} (h : Rat.abs q < overflowLimit) : (rnd q z).isFinite = true := by
  unfold rnd
  split
  · exact zero_isFinite z
  · exact (ofRat_isFinite q).2 h

theorem rnd_isNaN (q : Rat) (z : Bool) : (rnd q z).isNaN = false := by
  unfold rnd
  split
  · exact isNaN_false_of_finite (zero_isFinite z)
  · exact ofRat_isNaN q

theorem add_eq {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    F64.add x y = rnd (x.toRat + y.toRat) (x.sign && y.sign) := by
  simp [F64.add, rnd, isNaN_false_of_finite hx, isNaN_false_of_finite hy,
    isInf_false_of_finite hx, isInf_false_of_finite hy]

theorem mul_eq {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    F64.mul x y = rnd (x.toRat * y.toRat) (x.sign != y.sign) := by
  simp [F64.mul, rnd, isNaN_false_of_finite hx, isNaN_false_of_finite hy,
    isInf_false_of_finite hx, isInf_false_of_finite hy]

/-- `b - a >= 0` when `a <= b`, if it does not overflow. -/
theorem sub_nonneg {a b : F64} (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hab : a.toRat ≤ b.toRat) (hf : (F64.sub b a).isFinite = true) : 0 ≤ (F64.sub b a).toRat := by
  have hna : a.neg.isFinite = true := by rw [neg_isFinite]; exact ha
  unfold F64.sub at hf ⊢
  rw [add_eq hb hna, toRat_neg] at hf ⊢
  have := rnd_ge (zero_isFinite false) (q := b.toRat + -a.toRat) (z := b.sign && a.neg.sign)
    (by rw [zero_toRat]; grind) hf
  rwa [zero_toRat] at this

/-- `d * u` lies in `[0, d]` for `d >= 0` and `0 <= u <= 1`. -/
theorem mul_unit {d u : F64} (hd : d.isFinite = true) (hu : u.isFinite = true)
    (hd0 : 0 ≤ d.toRat) (hu0 : 0 ≤ u.toRat) (hu1 : u.toRat ≤ 1) :
    (F64.mul d u).isFinite = true ∧ 0 ≤ (F64.mul d u).toRat ∧ (F64.mul d u).toRat ≤ d.toRat := by
  rw [mul_eq hd hu]
  have hq0 : 0 ≤ d.toRat * u.toRat := Rat.mul_nonneg hd0 hu0
  have hq1 : d.toRat * u.toRat ≤ d.toRat := by
    have := Rat.mul_le_mul_of_nonneg_left hu1 hd0
    rwa [Rat.mul_one] at this
  have hlim := abs_toRat_lt hd
  have hf : (rnd (d.toRat * u.toRat) (d.sign != u.sign)).isFinite = true := by
    apply rnd_isFinite
    rw [abs_of_nonneg hq0]
    rw [abs_of_nonneg hd0] at hlim
    grind
  refine ⟨hf, ?_, rnd_le hd hq1 hf⟩
  have := rnd_ge (zero_isFinite false) (by rw [zero_toRat]; exact hq0) hf
  rwa [zero_toRat] at this

/-- `a <= a + t` for `t >= 0`, overflow included (to `+inf`). -/
theorem le_add {a t : F64} (ha : a.isFinite = true) (ht : t.isFinite = true) (ht0 : 0 ≤ t.toRat) :
    F64.le a (F64.add a t) = true := by
  rw [add_eq ha ht]
  have hq : a.toRat ≤ a.toRat + t.toRat := by grind
  cases hf : (rnd (a.toRat + t.toRat) (a.sign && t.sign)).isFinite
  · -- overflow: the result is `+inf`
    have hne : a.toRat + t.toRat ≠ 0 := by
      intro h0
      have : (rnd (a.toRat + t.toRat) (a.sign && t.sign)).isFinite = true := by
        unfold rnd; rw [if_pos h0]; exact zero_isFinite _
      rw [hf] at this; cases this
    have hr : rnd (a.toRat + t.toRat) (a.sign && t.sign) = ofRat (a.toRat + t.toRat) := by
      unfold rnd; rw [if_neg hne]
    rw [hr] at hf ⊢
    have hinf : (ofRat (a.toRat + t.toRat)).isInf = true := by
      rcases classify (ofRat (a.toRat + t.toRat)) with h | h | h
      · rw [hf] at h; cases h
      · exact h
      · rw [ofRat_isNaN] at h; cases h
    have hbig := (ofRat_class _).2.1 hinf
    have hla := abs_toRat_lt ha
    have hpos : ¬ (a.toRat + t.toRat < 0) := by
      intro hneg
      have e1 : Rat.abs (a.toRat + t.toRat) = -(a.toRat + t.toRat) := by
        rw [abs_eq_ite]; simp [hneg]
      have e2 : -a.toRat ≤ Rat.abs a.toRat := by rw [abs_eq_ite]; split <;> grind
      grind
    have hs : (ofRat (a.toRat + t.toRat)).sign = false := by
      rw [ofRat_sign hne]; simp [hpos]
    simp [F64.le, F64.lt, isNaN_false_of_finite ha, ofRat_isNaN, isInf_false_of_finite ha, hinf, hs]
  · rw [le_of_finite ha hf]
    exact decide_eq_true (rnd_ge ha hq hf)

end PyLean.CoreLibs.Rand.F64Order
