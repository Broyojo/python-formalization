import PyLean.Fractions.ArithProps

/-!
`__floor__`, `__ceil__`, `__trunc__`, `__int__`, `is_integer`,
`as_integer_ratio` and `__round__`.
-/

namespace PyLean.Fractions

open PyLean

/-- `R` is the integer nearest to `n / d` (`d > 0`), ties to even:
`|n/d - R| ≤ 1/2`, and `R` is even when the distance is exactly `1/2`. -/
def HalfEven (R n d : Int) : Prop :=
  -d ≤ 2 * (n - R * d) ∧ 2 * (n - R * d) ≤ d ∧
  ((2 * (n - R * d) = d ∨ 2 * (n - R * d) = -d) → R % 2 = 0)

/-- `HalfEven` depends only on the value `n / d`. -/
theorem halfEven_congr {R n d n' d' : Int} (hd : 0 < d) (hd' : 0 < d') (h : n * d' = n' * d) :
    HalfEven R n d → HalfEven R n' d' := by
  rintro ⟨h1, h2, h3⟩
  have key : 2 * (n' - R * d') * d = 2 * (n - R * d) * d' := by grind
  refine ⟨?_, ?_, ?_⟩
  · apply le_of_mul_le_mul_r (z := d) _ hd
    rw [key]; have := mul_le_mul_r h1 (Int.le_of_lt hd'); grind
  · apply le_of_mul_le_mul_r (z := d) _ hd
    rw [key]; have := mul_le_mul_r h2 (Int.le_of_lt hd'); grind
  · intro ht
    apply h3
    rcases ht with ht | ht
    · left
      apply Int.eq_of_mul_eq_mul_right (a := d') (by omega)
      rw [← key, ht]; grind
    · right
      apply Int.eq_of_mul_eq_mul_right (a := d') (by omega)
      rw [← key, ht]; grind

theorem round_halfEven (a : Frac) (hd : 0 < a.den) : HalfEven (round a) a.num a.den := by
  have hdiv : pyDiv a.num a.den = a.num / a.den := pyDiv_of_nonneg _ (by omega)
  have hmod : pyMod a.num a.den = a.num % a.den := pyMod_of_nonneg _ (by omega)
  have hfl2 : ∀ x : Int, pyMod x 2 = x % 2 := fun x => pyMod_of_nonneg _ (by decide)
  have e := Int.mul_ediv_add_emod a.num a.den
  have r0 := Int.emod_nonneg a.num (show a.den ≠ 0 by omega)
  have r1 := Int.emod_lt_of_pos a.num hd
  generalize a.num / a.den = fl at e hdiv
  generalize a.num % a.den = r at e hmod r0 r1
  have hfl : a.num - fl * a.den = r := by grind
  have hfl1 : a.num - (fl + 1) * a.den = r - a.den := by grind
  simp only [round, hdiv, hmod, hfl2]
  split
  · unfold HalfEven; rw [hfl]; refine ⟨by omega, by omega, by omega⟩
  · split
    · unfold HalfEven; rw [hfl1]; refine ⟨by omega, by omega, by omega⟩
    · split
      · unfold HalfEven; rw [hfl]; refine ⟨by omega, by omega, fun _ => by omega⟩
      · unfold HalfEven; rw [hfl1]; refine ⟨by omega, by omega, fun _ => by omega⟩

/-- `__floor__`/`__ceil__` docs ("the greatest int <= self", "the least int >=
self"), `math.trunc` and `int()` (rounding toward zero), `is_integer` docs
("True if the Fraction is an integer") and `as_integer_ratio` docs ("lowest
terms and ... positive denominator"). For every Fraction. -/
def IntConversions : Prop :=
  ∀ a : Frac, a.Normal →
    floor a * a.den ≤ a.num ∧ a.num < (floor a + 1) * a.den ∧
    (ceil a - 1) * a.den < a.num ∧ a.num ≤ ceil a * a.den ∧
    trunc a = (if a.num < 0 then ceil a else floor a) ∧ toInt a = trunc a ∧
    (isInteger a = true ↔ a.den ∣ a.num) ∧
    (asIntegerRatio a).2 > 0 ∧ Int.gcd (asIntegerRatio a).1 (asIntegerRatio a).2 = 1 ∧
    (asIntegerRatio a).1 * a.den = a.num * (asIntegerRatio a).2

theorem intConversions_proven : IntConversions := by
  intro a ⟨hd, hg⟩
  have hdiv : pyDiv a.num a.den = a.num / a.den := pyDiv_of_nonneg _ (by omega)
  have hdiv' : pyDiv (-a.num) a.den = (-a.num) / a.den := pyDiv_of_nonneg _ (by omega)
  have e := Int.mul_ediv_add_emod a.num a.den
  have r0 := Int.emod_nonneg a.num (show a.den ≠ 0 by omega)
  have r1 := Int.emod_lt_of_pos a.num hd
  have e' := Int.mul_ediv_add_emod (-a.num) a.den
  have r0' := Int.emod_nonneg (-a.num) (show a.den ≠ 0 by omega)
  have r1' := Int.emod_lt_of_pos (-a.num) hd
  generalize a.num / a.den = fl at e hdiv
  generalize a.num % a.den = r at e r0 r1
  generalize (-a.num) / a.den = fl' at e' hdiv'
  generalize (-a.num) % a.den = r' at e' r0' r1'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hd, hg, rfl⟩
  · simp only [floor, hdiv]; grind
  · simp only [floor, hdiv]; grind
  · simp only [ceil, hdiv']; grind
  · simp only [ceil, hdiv']; grind
  · simp only [trunc, ceil, floor]
  · simp only [toInt, trunc]
  · simp only [isInteger, beq_iff_eq]
    constructor
    · intro h; rw [h]; exact Int.one_dvd _
    · intro h
      have := Int.gcd_eq_natAbs_right h
      rw [hg] at this
      omega

/-- `__round__` docs: "The first version returns the nearest int to self,
rounding half to even." For every Fraction. -/
def RoundHalfEven : Prop := ∀ a : Frac, a.Normal → HalfEven (round a) a.num a.den

theorem roundHalfEven_proven : RoundHalfEven := fun a ha => round_halfEven a ha.1

/-- `__round__` docs: "The second version rounds self to the nearest multiple
of Fraction(1, 10**ndigits) (logically, if ndigits is negative), again
rounding half toward even." For every Fraction and int `ndigits`; the result
is a normalized Fraction. -/
def RoundNdigits : Prop :=
  ∀ a : Frac, a.Normal → ∀ nd : Int,
    (0 < nd → ∃ r R, roundTo a nd = .ok r ∧ r.Normal ∧ r.Rep R (10 ^ nd.toNat) ∧
      HalfEven R (a.num * 10 ^ nd.toNat) a.den) ∧
    (nd ≤ 0 → ∃ R, roundTo a nd = .ok ⟨R * 10 ^ nd.natAbs, 1⟩ ∧
      HalfEven R a.num (a.den * 10 ^ nd.natAbs))

theorem roundNdigits_proven : RoundNdigits := by
  intro a ha nd
  have hshift : (0 : Int) < 10 ^ nd.natAbs := Int.pow_pos (by decide)
  refine ⟨fun hnd => ?_, fun hnd => ?_⟩
  · have he : nd.natAbs = nd.toNat := by omega
    obtain ⟨hmn, hmv⟩ := mul_spec a (ofInt (10 ^ nd.natAbs)) ha ⟨by simp [ofInt], by simp [ofInt]⟩
    have hR := round_halfEven (mul a (ofInt (10 ^ nd.natAbs))) hmn.1
    obtain ⟨r, hr, hrn, hrv⟩ := normalize_ok (n := round (mul a (ofInt (10 ^ nd.natAbs))))
      (d := 10 ^ nd.natAbs) (by omega)
    refine ⟨r, round (mul a (ofInt (10 ^ nd.natAbs))), ?_, hrn, ?_, ?_⟩
    · simp only [roundTo, hnd, ↓reduceIte, ofInts]; exact hr
    · rw [← he]; exact hrv
    · rw [← he]
      apply halfEven_congr hmn.1 ha.1 _ hR
      simp only [ofInt, Int.mul_one] at hmv ⊢
      exact hmv
  · have hb : (ofInt (10 ^ nd.natAbs)).Normal := ⟨by simp [ofInt], by simp [ofInt]⟩
    obtain ⟨m, hm, hmn, hmv⟩ := div_spec a (ofInt (10 ^ nd.natAbs)) ha hb (by simp [ofInt]; omega)
    have hR := round_halfEven m hmn.1
    refine ⟨round m, ?_, ?_⟩
    · simp only [roundTo, show ¬ (0 < nd) by omega, ↓reduceIte, hm]; rfl
    · apply halfEven_congr hmn.1 (Int.mul_pos ha.1 hshift) _ hR
      simp only [ofInt, Int.mul_one] at hmv ⊢
      rw [hmv]

end PyLean.Fractions
