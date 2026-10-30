import PyLean.Fractions.Lemmas

/-!
Construction from two ints: normalization and the zero-denominator error.
-/

namespace PyLean.Fractions

open PyLean

/-- The value of `x` is `n / d` (for `d ≠ 0`), by cross-multiplication. -/
def Frac.Rep (x : Frac) (n d : Int) : Prop := x.num * d = n * x.den

theorem normalize_ok {n d : Int} (hd : d ≠ 0) :
    ∃ x, normalize n d = .ok x ∧ x.Normal ∧ x.Rep n d := by
  obtain ⟨a, b, ha, hb, hab, hg⟩ := gcd_cofactors (n := n) (d := d) hd
  generalize hG : (Int.gcd n d : Int) = G at ha hb hg
  have hdvdn : G ∣ n := ⟨a, ha⟩
  have hdvdd : G ∣ d := ⟨b, hb⟩
  have hGne : G ≠ 0 := by omega
  have hna : n / G = a := by rw [ha]; exact Int.mul_ediv_cancel_left _ hGne
  have hdb : d / G = b := by rw [hb]; exact Int.mul_ediv_cancel_left _ hGne
  by_cases hneg : d < 0
  · have hb0 : b < 0 := by
      rcases Int.lt_trichotomy b 0 with h | h | h
      · exact h
      · subst h; omega
      · have := Int.mul_pos hg h; omega
    refine ⟨⟨-a, -b⟩, ?_, ?_, ?_⟩
    · simp only [normalize, hd, hneg, ↓reduceIte, hG]
      rw [pyDiv_of_dvd (Int.neg_dvd.mpr hdvdn), pyDiv_of_dvd (Int.neg_dvd.mpr hdvdd),
        Int.ediv_neg, Int.ediv_neg, hna, hdb]
      rfl
    · refine ⟨by simp only; omega, ?_⟩
      simp only [Int.neg_gcd, Int.gcd_neg]; exact hab
    · simp only [Frac.Rep]; rw [ha, hb]; grind
  · refine ⟨⟨a, b⟩, ?_, ?_, ?_⟩
    · simp only [normalize, hd, hneg, ↓reduceIte, hG]
      rw [pyDiv_of_dvd hdvdn, pyDiv_of_dvd hdvdd, hna, hdb]
      rfl
    · refine ⟨?_, hab⟩
      show 0 < b
      rcases Int.lt_trichotomy b 0 with h | h | h
      · have := Int.mul_neg_of_pos_of_neg hg h; omega
      · subst h; omega
      · exact h
    · simp only [Frac.Rep]; rw [ha, hb]; grind

/-- `Fraction(numerator, denominator)` docs: "returns a new Fraction instance
with a value equal to numerator/denominator", and the class invariant
(numerator and denominator "in lowest terms", denominator "Guaranteed to be
positive"). For all ints `n`, `d ≠ 0`. -/
def CtorNormalizes : Prop :=
  ∀ n d : Int, d ≠ 0 → ∃ x, ofInts n d = .ok x ∧ x.Normal ∧ x.Rep n d

theorem ctorNormalizes_proven : CtorNormalizes := fun _ _ hd => normalize_ok hd

/-- Docs, `Fraction(numerator=0, denominator=1)`: "If denominator is zero, it
raises a ZeroDivisionError." For every int numerator. -/
def CtorZeroDenominatorRaises : Prop :=
  ∀ n : Int, (ofInts n 0).raises "ZeroDivisionError"

theorem numDigits_pow_ten_4300 : numDigits (10 ^ 4300) > maxStrDigits := by
  unfold numDigits maxStrDigits
  apply Nat.lt_of_not_le
  intro h
  have := (Nat.length_toDigits_le_iff (b := 10) (n := 10 ^ 4300) (k := 4300) (by decide) (by decide)).mp h
  omega

/-- `Fraction(10**4300, 0)` raises `ValueError` (from formatting the message
`'Fraction(%s, 0)' % numerator`), not `ZeroDivisionError`. -/
theorem ctorZeroDenominatorRaises_refuted : ¬CtorZeroDenominatorRaises := by
  intro h
  obtain ⟨e, he, hcls⟩ := h (10 ^ 4300)
  have hv : ofInts (10 ^ 4300) 0 = .error (.valueError limitToStrMsg) := by
    have hn : numDigits (Int.natAbs (10 ^ 4300 : Int)) > maxStrDigits := by
      have : Int.natAbs (10 ^ 4300 : Int) = 10 ^ 4300 := by simp [Int.natAbs_pow]
      rw [this]; exact numDigits_pow_ten_4300
    simp only [ofInts, normalize, zeroDivMsg, strInt, hn, ↓reduceIte]
    rfl
  rw [hv] at he
  cases he
  simp [PyExc.className] at hcls

end PyLean.Fractions
