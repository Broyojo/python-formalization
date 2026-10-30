import PyLean.Fractions.Round

/-!
`limit_denominator` (fractions.py:384-439) returns a closest fraction with
denominator at most `max_denominator`.

Proof outline. Write `x = N/D` in lowest terms, `D > M`. The loop keeps
`N = p1*n + p0*d`, `D = q1*n + q0*d` with `p1*q0 - p0*q1 = ±1`. At exit the
two candidates `U = p1/q1` and `L = (p0+k*p1)/(q0+k*q1)` are Farey neighbours
(determinant ±1) whose denominators sum past `M`, and `x = A*L + B*U` with
`A, B > 0` (as integer vectors). Writing any `r/s` as `u*L + v*U`, `s <= M`
forces `u` and `v` to have opposite signs, which makes `r/s` no closer than
`L` (when `u >= 1`) or than `U` (when `v >= 1`). The final comparison
`2*d*(q0+k*q1) <= D` picks the closer of the two.
-/

namespace PyLean.Fractions

open PyLean

/-- Loop invariant of `limit_denominator` after the first iteration. -/
def LInv (N D M p0 q0 p1 q1 n d : Int) : Prop :=
  N = p1 * n + p0 * d ∧ D = q1 * n + q0 * d ∧
  (p1 * q0 - p0 * q1 = 1 ∨ p1 * q0 - p0 * q1 = -1) ∧
  1 ≤ q1 ∧ q1 ≤ M ∧ 0 ≤ q0 ∧ q0 ≤ M ∧ 0 ≤ d ∧ d < n

theorem linv_d_pos {N D M p0 q0 p1 q1 n d : Int} (h : LInv N D M p0 q0 p1 q1 n d)
    (hg : Int.gcd N D = 1) (hDM : M < D) : 0 < d := by
  obtain ⟨h1, h2, _, _, hq1M, _, _, hd0, hdn⟩ := h
  rcases Int.lt_or_eq_of_le hd0 with h | h
  · exact h
  · subst h
    simp only [Int.mul_zero, Int.add_zero] at h1 h2
    have hn1 : n ∣ N := ⟨p1, by rw [h1, Int.mul_comm]⟩
    have hn2 : n ∣ D := ⟨q1, by rw [h2, Int.mul_comm]⟩
    have hdvd : n.natAbs ∣ Int.gcd N D :=
      Nat.dvd_gcd (Int.natAbs_dvd_natAbs.mpr hn1) (Int.natAbs_dvd_natAbs.mpr hn2)
    rw [hg] at hdvd
    have : n.natAbs = 1 := Nat.dvd_one.mp hdvd
    have hn : n = 1 := by omega
    subst hn
    omega

theorem ldLoop_spec (N D M : Int) (hg : Int.gcd N D = 1) (hDM : M < D) :
    ∀ (fuel : Nat) (p0 q0 p1 q1 n d : Int), LInv N D M p0 q0 p1 q1 n d → d < fuel →
    ∃ p0' q0' p1' q1' n' d', ldLoop M fuel (p0, q0, p1, q1, n, d) = .ok (p0', q0', p1', q1', n', d') ∧
      LInv N D M p0' q0' p1' q1' n' d' ∧ 0 < d' ∧ M < q0' + (n' / d') * q1' := by
  intro fuel
  induction fuel with
  | zero => intro p0 q0 p1 q1 n d h hf; have := h.2.2.2.2.2.2.2.1; omega
  | succ fuel ih =>
    intro p0 q0 p1 q1 n d h hf
    have hd := linv_d_pos h hg hDM
    have hdne : d ≠ 0 := by omega
    have hdiv : pyDiv n d = n / d := pyDiv_of_nonneg _ (by omega)
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    by_cases hq : q0 + n / d * q1 > M
    · refine ⟨p0, q0, p1, q1, n, d, ?_, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, hd, hq⟩
      simp only [ldLoop, hdne, ↓reduceIte, hdiv, hq]
    · have e := Int.mul_ediv_add_emod n d
      have r0 := Int.emod_nonneg n hdne
      have r1 := Int.emod_lt_of_pos n hd
      generalize n / d = a at e hdiv hq
      generalize n % d = r at e r0 r1
      have ha : 1 ≤ a := by
        apply Int.le_of_not_gt
        intro ha
        have := mul_le_mul_r (show a ≤ 0 by omega) (Int.le_of_lt hd)
        grind
      have hrd : n - a * d = r := by grind
      have hq1a : q1 ≤ a * q1 := by
        have := mul_le_mul_r ha (show 0 ≤ q1 by omega); grind
      obtain ⟨p0', q0', p1', q1', n', d', hl, hinv, hd', hex⟩ :=
        ih p1 q1 (p0 + a * p1) (q0 + a * q1) d r
          ⟨by rw [← hrd, h1]; grind, by rw [← hrd, h2]; grind,
           by rcases h3 with h3 | h3
              · right; grind
              · left; grind,
           by omega, by omega, by omega, by omega, r0, r1⟩ (by omega)
      refine ⟨p0', q0', p1', q1', n', d', ?_, hinv, hd', hex⟩
      simp only [ldLoop, hdne, ↓reduceIte, hdiv, hq, hrd]
      exact hl

/-- `|x|` as an int. -/
def iabs (x : Int) : Int := (x.natAbs : Int)

theorem iabs_mul_unit {e x : Int} (he : e = 1 ∨ e = -1) : iabs (e * x) = iabs x := by
  rcases he with he | he <;> subst he <;> simp [iabs]

theorem iabs_of_nonneg {x : Int} (h : 0 ≤ x) : iabs x = x := by simp [iabs]; omega

theorem iabs_of_nonpos {x : Int} (h : x ≤ 0) : iabs x = -x := by simp [iabs]; omega

/-- The final step: Farey neighbours `L`, `U` around `x = A*L + B*U`. -/
theorem farey_closest (N D M pL qL pU qU A B e : Int)
    (he : e = 1 ∨ e = -1) (hdet : pL * qU - qL * pU = e)
    (hqL : 1 ≤ qL) (hqU : 1 ≤ qU) (hsum : M < qL + qU)
    (hA : 0 < A) (hB : 0 < B) (hN : N = A * pL + B * pU) (hD : D = A * qL + B * qU)
    (r s : Int) (hs1 : 1 ≤ s) (hsM : s ≤ M) :
    B * s ≤ iabs (r * D - s * N) * qL ∨ A * s ≤ iabs (r * D - s * N) * qU := by
  -- coordinates of (r, s) in the basis (L, U)
  have he2 : e * e = 1 := by rcases he with he | he <;> subst he <;> decide
  generalize hu : e * (r * qU - s * pU) = u
  generalize hv : e * (s * pL - r * qL) = v
  have hr : r = u * pL + v * pU := by rw [← hu, ← hv]; grind
  have hs : s = u * qL + v * qU := by rw [← hu, ← hv]; grind
  have hcr : r * D - s * N = e * (u * B - v * A) := by rw [hr, hs, hN, hD]; grind
  rw [hcr, iabs_mul_unit he]
  -- `u` and `v` have opposite signs
  by_cases hu1 : 1 ≤ u
  · by_cases hv1 : 1 ≤ v
    · exfalso
      have := mul_le_mul_r hu1 (show 0 ≤ qL by omega)
      have := mul_le_mul_r hv1 (show 0 ≤ qU by omega)
      grind
    · left
      have hv0 : v ≤ 0 := by omega
      have t1 := mul_le_mul_r hv0 (show 0 ≤ qU by omega)
      have t2 := mul_le_mul_r hv0 (show 0 ≤ A by omega)
      have t3 := mul_le_mul_r hu1 (show 0 ≤ B by omega)
      have hpos : 0 ≤ u * B - v * A := by grind
      rw [iabs_of_nonneg hpos]
      have t4 := mul_le_mul_r (show v * qU ≤ 0 by grind) (show 0 ≤ B by omega)
      have t5 := mul_le_mul_r (show v * A ≤ 0 by grind) (show 0 ≤ qL by omega)
      rw [hs]; grind
  · have hu0 : u ≤ 0 := by omega
    by_cases hv1 : 1 ≤ v
    · right
      have t1 := mul_le_mul_r hu0 (show 0 ≤ qL by omega)
      have t2 := mul_le_mul_r hu0 (show 0 ≤ B by omega)
      have t3 := mul_le_mul_r hv1 (show 0 ≤ A by omega)
      have hpos : u * B - v * A ≤ 0 := by grind
      rw [iabs_of_nonpos hpos]
      have t4 := mul_le_mul_r (show u * qL ≤ 0 by grind) (show 0 ≤ A by omega)
      have t5 := mul_le_mul_r (show u * B ≤ 0 by grind) (show 0 ≤ qU by omega)
      rw [hs]; grind
    · exfalso
      have := mul_le_mul_r hu0 (show 0 ≤ qL by omega)
      have := mul_le_mul_r (show v ≤ 0 by omega) (show 0 ≤ qU by omega)
      grind

/-- Coprime from a unit determinant. -/
theorem gcd_one_of_det {p q p' q' : Int} (h : p * q' - q * p' = 1 ∨ p * q' - q * p' = -1) :
    Int.gcd p q = 1 := by
  have h1 : (Int.gcd p q : Int) ∣ p * q' - q * p' :=
    Int.dvd_sub (Int.dvd_trans (Int.gcd_dvd_left p q) (Int.dvd_mul_right _ _))
      (Int.dvd_trans (Int.gcd_dvd_right p q) (Int.dvd_mul_right _ _))
  have h2 : (Int.gcd p q : Int) ∣ 1 := by
    rcases h with h | h
    · rw [h] at h1; exact h1
    · rw [h] at h1; exact Int.dvd_neg.mp h1
  have := Int.natAbs_dvd_natAbs.mpr h2
  simp at this
  exact this

/-- `limit_denominator` docstring, fractions.py:387: "Closest Fraction to
self with denominator at most max_denominator", and its `ValueError` for
`max_denominator < 1` (fractions.py:416-417). For every Fraction `x` and int
`M`: the result is a normalized Fraction with denominator in `1..M`, and no
fraction `r/s` with `1 <= s <= M` is strictly closer to `x` (distances
compared by cross-multiplication: `|c - x| = |c.num*D - c.den*N| / (c.den*D)`). -/
def LimitDenominatorClosest : Prop :=
  ∀ x : Frac, x.Normal → ∀ M : Int,
    (M < 1 → (limitDenominator x M).raises "ValueError") ∧
    (1 ≤ M → ∃ c, limitDenominator x M = .ok c ∧ c.Normal ∧ c.den ≤ M ∧
      ∀ r s : Int, 1 ≤ s → s ≤ M →
        iabs (c.num * x.den - c.den * x.num) * s ≤ iabs (r * x.den - s * x.num) * c.den)

theorem limitDenominatorClosest_proven : LimitDenominatorClosest := by
  intro x hx M
  refine ⟨fun hM => ⟨.valueError "max_denominator should be at least 1", ?_, rfl⟩, fun hM => ?_⟩
  · simp only [limitDenominator, hM, ↓reduceIte]; rfl
  obtain ⟨hD, hg⟩ := hx
  by_cases hsmall : x.den ≤ M
  · refine ⟨x, ?_, ⟨hD, hg⟩, hsmall, fun r s _ _ => ?_⟩
    · simp only [limitDenominator, show ¬ M < 1 by omega, hsmall, ↓reduceIte]; rfl
    · have : x.num * x.den - x.den * x.num = 0 := by grind
      rw [this]; simp only [iabs, Int.natAbs_zero, Int.natCast_zero, Int.zero_mul]
      exact Int.mul_nonneg (by omega) (by omega)
  have hDM : M < x.den := by omega
  -- first iteration, by hand
  have hD0 : x.den ≠ 0 := by omega
  have hdiv0 : pyDiv x.num x.den = x.num / x.den := pyDiv_of_nonneg _ (by omega)
  have e0 := Int.mul_ediv_add_emod x.num x.den
  have r0 := Int.emod_nonneg x.num hD0
  have r1 := Int.emod_lt_of_pos x.num hD
  generalize x.num / x.den = a0 at e0 hdiv0
  generalize x.num % x.den = m0 at e0 r0 r1
  have hfuel : x.den.toNat = (x.den.toNat - 1) + 1 := by omega
  have hstep : ldLoop M (x.den.toNat + 1) (0, 1, 1, 0, x.num, x.den) =
      ldLoop M x.den.toNat (1, 0, 0 + a0 * 1, 0 + a0 * 0 + 1, x.den, m0) := by
    simp only [ldLoop, hD0, ↓reduceIte, hdiv0]
    have hq : ¬ (1 + a0 * 0 > M) := by omega
    simp only [hq, ↓reduceIte]
    have : x.num - a0 * x.den = m0 := by grind
    rw [this]; congr 2 <;> grind
  have hinv1 : LInv x.num x.den M 1 0 (0 + a0 * 1) (0 + a0 * 0 + 1) x.den m0 :=
    ⟨by grind, by grind, by right; grind, by omega, by omega, by omega, by omega, r0, r1⟩
  obtain ⟨p0, q0, p1, q1, n, d, hl, hinv, hd, hex⟩ :=
    ldLoop_spec x.num x.den M hg hDM x.den.toNat _ _ _ _ _ _ hinv1 (by omega)
  obtain ⟨hN, hDe, hdet, hq1, hq1M, hq0, hq0M, _, hdn⟩ := hinv
  have hdiv : pyDiv (M - q0) q1 = (M - q0) / q1 := pyDiv_of_nonneg _ (by omega)
  have ek := Int.mul_ediv_add_emod (M - q0) q1
  have k0 := Int.emod_nonneg (M - q0) (show q1 ≠ 0 by omega)
  have k1 := Int.emod_lt_of_pos (M - q0) (show 0 < q1 by omega)
  have hkpos : 0 ≤ (M - q0) / q1 := Int.ediv_nonneg (by omega) (by omega)
  generalize (M - q0) / q1 = k at ek hdiv hkpos
  generalize (M - q0) % q1 = mk at ek k0 k1
  -- `k < n / d`
  have en := Int.mul_ediv_add_emod n d
  have n0 := Int.emod_nonneg n (show d ≠ 0 by omega)
  have n1 := Int.emod_lt_of_pos n hd
  generalize n / d = a at en hex
  generalize n % d = rn at en n0 n1
  have hka : k < a := by
    apply Int.lt_of_not_ge
    intro hak
    have := mul_le_mul_r hak (show 0 ≤ q1 by omega)
    grind
  have hka' : k + 1 ≤ a := by omega
  have hB : 0 < n - k * d := by
    have := mul_le_mul_r hka' (Int.le_of_lt hd)
    grind
  have hqL : 1 ≤ q0 + k * q1 := by
    by_cases h0 : q0 = 0
    · subst h0
      have : 1 ≤ k := by
        apply Int.le_of_not_gt; intro hk
        have : k = 0 := by omega
        subst this; grind
      have := mul_le_mul_r this (show 0 ≤ q1 by omega)
      grind
    · have := Int.mul_nonneg hkpos (show 0 ≤ q1 by omega); omega
  have hqLM : q0 + k * q1 ≤ M := by grind
  have hsum : M < (q0 + k * q1) + q1 := by grind
  have he : (p0 + k * p1) * q1 - (q0 + k * q1) * p1 = -(p1 * q0 - p0 * q1) := by grind
  have hunit : -(p1 * q0 - p0 * q1) = 1 ∨ -(p1 * q0 - p0 * q1) = -1 := by omega
  have hNx : x.num = d * (p0 + k * p1) + (n - k * d) * p1 := by rw [hN]; grind
  have hDx : x.den = d * (q0 + k * q1) + (n - k * d) * q1 := by rw [hDe]; grind
  have hclose := farey_closest x.num x.den M (p0 + k * p1) (q0 + k * q1) p1 q1 d (n - k * d) _
    hunit he hqL hq1 hsum hd hB hNx hDx
  -- distances of the two candidates
  have hcrU : iabs (p1 * x.den - q1 * x.num) = d := by
    have : p1 * x.den - q1 * x.num = -(-(p1 * q0 - p0 * q1)) * d := by rw [hDx, hNx]; grind
    rw [this, Int.neg_mul, ← Int.mul_neg, iabs_mul_unit hunit]
    simp only [iabs]; omega
  have hcrL : iabs ((p0 + k * p1) * x.den - (q0 + k * q1) * x.num) = n - k * d := by
    have : (p0 + k * p1) * x.den - (q0 + k * q1) * x.num = -(p1 * q0 - p0 * q1) * (n - k * d) := by
      rw [hDx, hNx]; grind
    rw [this, iabs_mul_unit hunit]
    simp only [iabs]; omega
  have hres : limitDenominator x M =
      if 2 * d * (q0 + k * q1) ≤ x.den then .ok ⟨p1, q1⟩ else .ok ⟨p0 + k * p1, q0 + k * q1⟩ := by
    simp only [limitDenominator, show ¬ M < 1 by omega, hsmall, ↓reduceIte]
    rw [hstep]
    simp only [bind, Except.bind, hl, show ¬ q1 = 0 by omega, ↓reduceIte, hdiv]
    rfl
  rw [hres]
  split
  · rename_i hc
    refine ⟨⟨p1, q1⟩, rfl, ⟨by simp only; omega, ?_⟩, hq1M, fun r s hs1 hsM => ?_⟩
    · simp only
      apply gcd_one_of_det (p' := p0) (q' := q0)
      rcases hdet with h | h
      · left; grind
      · right; grind
    · simp only
      rw [hcrU]
      have hAB : d * (q0 + k * q1) ≤ (n - k * d) * q1 := by grind
      rcases hclose r s hs1 hsM with h | h
      · -- r/s is no closer than L, and U is at least as close as L
        apply le_of_mul_le_mul_r (z := q0 + k * q1) _ (by omega)
        have t1 := mul_le_mul_r hAB (show 0 ≤ s by omega)
        have t2 := mul_le_mul_r h (show 0 ≤ q1 by omega)
        grind
      · exact h
  · rename_i hc
    refine ⟨⟨p0 + k * p1, q0 + k * q1⟩, rfl, ⟨by simp only; omega, ?_⟩, hqLM, fun r s hs1 hsM => ?_⟩
    · simp only
      apply gcd_one_of_det (p' := p1) (q' := q1)
      omega
    · simp only
      rw [hcrL]
      have hAB : (n - k * d) * q1 < d * (q0 + k * q1) := by grind
      rcases hclose r s hs1 hsM with h | h
      · exact h
      · apply le_of_mul_le_mul_r (z := q1) _ (by omega)
        have t1 := mul_le_mul_r (Int.le_of_lt hAB) (show 0 ≤ s by omega)
        have t2 := mul_le_mul_r h (show 0 ≤ q0 + k * q1 by omega)
        grind

end PyLean.Fractions
