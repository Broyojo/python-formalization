import PyLean.Decimal.Props

/-!
`as_integer_ratio` of `_pydecimal` (_pydecimal.py:1021-1069): its factor-stripping loops give the
fraction in lowest terms, the same pair as `_decimal`'s gcd reduction.
-/

namespace PyLean.Decimal

open PyLean

/-- The loop `while d5 > 0 and n % 5 == 0` stops with `d5 ≤ k`, `n = n' · 5^(k - d5)`, and `n'`
not divisible by 5 when it stopped early. -/
theorem strip5_spec : ∀ (k n : Nat),
    (strip5 n k).2 ≤ k ∧ n = (strip5 n k).1 * 5 ^ (k - (strip5 n k).2) ∧
      (0 < (strip5 n k).2 → (strip5 n k).1 % 5 ≠ 0)
  | 0, n => by simp [strip5]
  | k + 1, n => by
    simp only [strip5]
    split
    · rename_i h
      obtain ⟨h1, h2, h3⟩ := strip5_spec k (n / 5)
      refine ⟨by omega, ?_, h3⟩
      have e1 : k + 1 - (strip5 (n / 5) k).2 = (k - (strip5 (n / 5) k).2) + 1 := by omega
      rw [e1, Nat.pow_succ, ← Nat.mul_assoc, ← h2]
      omega
    · rename_i h
      exact ⟨Nat.le_refl _, by simp, fun _ => h⟩

theorem tz2_spec : ∀ (f n : Nat), n ≤ f → n ≠ 0 → 2 ^ tz2 f n ∣ n ∧ (n / 2 ^ tz2 f n) % 2 = 1
  | 0, n, h, h0 => by omega
  | f + 1, n, h, h0 => by
    simp only [tz2]
    split
    · rename_i hc
      obtain ⟨h1, h2⟩ := tz2_spec f (n / 2) (by omega) (by omega)
      have hn : n = n / 2 * 2 := by omega
      refine ⟨?_, ?_⟩
      · have h3 := Nat.mul_dvd_mul_right h1 2
        rw [← hn] at h3
        rw [Nat.pow_succ]
        exact h3
      · rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
        exact h2
    · rename_i hc
      refine ⟨by simp, ?_⟩
      simp only [Nat.pow_zero, Nat.div_one]
      omega

theorem coprime_of_mod (N q : Nat) (hq : q = 2 ∨ q = 5) (h : N % q ≠ 0) : Nat.Coprime N q := by
  have h1 := Nat.gcd_dvd_right N q
  have h2 := Nat.gcd_dvd_left N q
  unfold Nat.Coprime
  generalize Nat.gcd N q = g at h1 h2
  rcases hq with rfl | rfl
  · have hg : g ≤ 2 := Nat.le_of_dvd (by decide) h1
    rcases (by omega : g = 0 ∨ g = 1 ∨ g = 2) with rfl | rfl | rfl
    · exact absurd h1 (by decide)
    · rfl
    · exact absurd (Nat.mod_eq_zero_of_dvd h2) h
  · have hg : g ≤ 5 := Nat.le_of_dvd (by decide) h1
    rcases (by omega : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd h1 (by decide)
    · rfl
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)
    · exact absurd (Nat.mod_eq_zero_of_dvd h2) h

/-- The pair the loops make for `co ≠ 0` and `k = -exp > 0` is `co / 10^k` in lowest terms with a
positive denominator. -/
theorem strip_ratio (co k : Nat) (hc : co ≠ 0) :
    ((strip5 co k).1 / 2 ^ min (trailingZeros (strip5 co k).1) k) * 10 ^ k =
        co * (5 ^ (strip5 co k).2 * 2 ^ (k - min (trailingZeros (strip5 co k).1) k)) ∧
      Nat.Coprime ((strip5 co k).1 / 2 ^ min (trailingZeros (strip5 co k).1) k)
        (5 ^ (strip5 co k).2 * 2 ^ (k - min (trailingZeros (strip5 co k).1) k)) ∧
      0 < 5 ^ (strip5 co k).2 * 2 ^ (k - min (trailingZeros (strip5 co k).1) k) := by
  obtain ⟨s1, s2, s3⟩ := strip5_spec k co
  generalize hP1 : (strip5 co k).1 = P1 at s1 s2 s3 ⊢
  generalize hP2 : (strip5 co k).2 = P2 at s1 s2 s3 ⊢
  have hp1 : P1 ≠ 0 := by
    intro h0; apply hc; rw [s2, h0, Nat.zero_mul]
  obtain ⟨t1, t2⟩ := tz2_spec P1 P1 (Nat.le_refl _) hp1
  have ht : trailingZeros P1 = tz2 P1 P1 := rfl
  rw [ht]
  generalize hT : tz2 P1 P1 = T at t1 t2 ⊢
  generalize hA : min T k = a
  have hat : a ≤ T := by omega
  have hak : a ≤ k := by omega
  have hda : 2 ^ a ∣ P1 := Nat.dvd_trans (Nat.pow_dvd_pow 2 hat) t1
  have hN : P1 = P1 / 2 ^ a * 2 ^ a := (Nat.div_mul_cancel hda).symm
  generalize hNd : P1 / 2 ^ a = N at hN
  refine ⟨?_, ?_, Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))⟩
  · have e2 : 2 ^ k = 2 ^ a * 2 ^ (k - a) := by rw [← Nat.pow_add]; congr 1; omega
    have e5 : 5 ^ k = 5 ^ (k - P2) * 5 ^ P2 := by rw [← Nat.pow_add]; congr 1; omega
    have e10 : 10 ^ k = 2 ^ k * 5 ^ k := by rw [← Nat.mul_pow]
    rw [e10, e2, e5, s2, hN]
    ac_rfl
  · apply Nat.Coprime.mul_right
    · by_cases h5 : P2 = 0
      · rw [h5, Nat.pow_zero]; exact Nat.coprime_one_right _
      · apply Nat.Coprime.pow_right
        apply coprime_of_mod N 5 (Or.inr rfl)
        intro hm
        apply s3 (by omega)
        rw [hN, Nat.mul_mod, hm, Nat.zero_mul, Nat.zero_mod]
    · by_cases h2 : k - a = 0
      · rw [h2, Nat.pow_zero]; exact Nat.coprime_one_right _
      · apply Nat.Coprime.pow_right
        apply coprime_of_mod N 2 (Or.inl rfl)
        have hat' : a = T := by omega
        rw [← hNd, hat']
        omega

/-- Two lowest-terms forms of the same fraction are the same. -/
theorem lowest_unique {N D N' D' X co : Nat} (hX : 0 < X) (h1 : N * X = co * D) (h2 : N' * X = co * D')
    (c1 : Nat.Coprime N D) (c2 : Nat.Coprime N' D') (hD : 0 < D) (hD' : 0 < D') : N = N' ∧ D = D' := by
  have hx : N * D' * X = N' * D * X := by
    rw [Nat.mul_right_comm, h1, Nat.mul_right_comm N', h2, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm D]
  have hx' : N * D' = N' * D := Nat.eq_of_mul_eq_mul_right hX hx
  have d1 : D ∣ D' := by
    have : D ∣ N * D' := ⟨N', by rw [hx', Nat.mul_comm]⟩
    exact (Nat.Coprime.symm c1).dvd_of_dvd_mul_left this
  have d2 : D' ∣ D := by
    have : D' ∣ N' * D := ⟨N, by rw [← hx', Nat.mul_comm]⟩
    exact (Nat.Coprime.symm c2).dvd_of_dvd_mul_left this
  have hDD := Nat.dvd_antisymm d1 d2
  subst hDD
  exact ⟨Nat.eq_of_mul_eq_mul_right hD hx', rfl⟩

/-- `as_integer_ratio` of `_pydecimal` (_pydecimal.py:1021-1069; docstring "Express a finite Decimal
instance in the form n / d. Returns a pair (n, d) of integers. When called on an infinity or NaN,
raises OverflowError or ValueError respectively."), for every value:

* a zero gives `(0, 1)`; a coefficient of more than 4300 digits raises `int(self._int)`'s
  int/str-limit `ValueError` (:1046);
* every pair it returns has `d > 0`, is in lowest terms, and is the value exactly:
  `n · 10^(-e) = ±c · 10^e · d`;
* within the limit it is the pair `_decimal` returns (the loops at :1052-1065 strip exactly the
  common factors of 2 and 5);
* a NaN raises `ValueError`, an infinity `OverflowError`, with the source's messages. -/
def RatioExactPy : Prop :=
  (∀ (neg : Bool) (e : Int), pyRatio (.fin neg 0 e) = .ok (0, 1)) ∧
  (∀ (neg : Bool) (c : Nat) (e : Int), c ≠ 0 → maxStrDigits < numDigits c →
    pyRatio (.fin neg c e) = .error (.valueError (limitToIntMsg (numDigits c)))) ∧
  (∀ (neg : Bool) (c : Nat) (e : Int) (n d : Int), pyRatio (.fin neg c e) = .ok (n, d) →
    0 < d ∧ Int.gcd n d = 1 ∧ n * 10 ^ (-e).toNat = (if neg then -(c : Int) else c) * 10 ^ e.toNat * d) ∧
  (∀ (neg : Bool) (c : Nat) (e : Int), numDigits c ≤ maxStrDigits →
    pyRatio (.fin neg c e) = cRatio (.fin neg c e)) ∧
  (∀ (neg s : Bool) (p : Nat), pyRatio (.nan neg s p) = .error (.valueError "cannot convert NaN to integer ratio")) ∧
  (∀ neg : Bool, pyRatio (.inf neg) = .error (.overflowError "cannot convert Infinity to integer ratio"))

theorem cRatio_zero (neg : Bool) (e : Int) : cRatio (.fin neg 0 e) = .ok (0, 1) := by
  have h : 10 ^ e.natAbs / 10 ^ e.natAbs = 1 := Nat.div_self (Nat.pow_pos (by decide))
  by_cases he : e ≥ 0 <;> cases neg <;> simp [cRatio, he, h]

theorem pyRatio_eq_c (neg : Bool) (c : Nat) (e : Int) (hl : numDigits c ≤ maxStrDigits) :
    pyRatio (.fin neg c e) = cRatio (.fin neg c e) := by
  by_cases hc : c = 0
  · subst hc; rw [cRatio_zero]; rfl
  have hi : intLimit (numDigits c) = .ok () := by
    unfold intLimit; rw [if_neg (Nat.not_lt.mpr hl)]
  simp only [pyRatio, hc, ↓reduceIte, hi, bind, Except.bind, pure, Except.pure, cRatio]
  by_cases he : e ≥ 0
  · simp only [he, ↓reduceIte]
  · simp only [he, ↓reduceIte]
    obtain ⟨r1, r2, r3⟩ := strip_ratio c e.natAbs hc
    have hp : 0 < 10 ^ e.natAbs := Nat.pow_pos (by decide)
    have hg : 0 < Nat.gcd c (10 ^ e.natAbs) := Nat.gcd_pos_of_pos_right _ hp
    obtain ⟨u, hu⟩ := Nat.gcd_dvd_left c (10 ^ e.natAbs)
    obtain ⟨v, hv⟩ := Nat.gcd_dvd_right c (10 ^ e.natAbs)
    have hcop := Nat.coprime_div_gcd_div_gcd (m := c) (n := 10 ^ e.natAbs) hg
    have hd : 0 < 10 ^ e.natAbs / Nat.gcd c (10 ^ e.natAbs) := Nat.div_pos (Nat.le_of_dvd hp ⟨v, hv⟩) hg
    have hval : c / Nat.gcd c (10 ^ e.natAbs) * 10 ^ e.natAbs = c * (10 ^ e.natAbs / Nat.gcd c (10 ^ e.natAbs)) := by
      generalize hG : Nat.gcd c (10 ^ e.natAbs) = g at *
      generalize hP : 10 ^ e.natAbs = P at *
      subst hu hv
      rw [Nat.mul_div_cancel_left _ hg, Nat.mul_div_cancel_left _ hg, ← Nat.mul_assoc, Nat.mul_comm u g]
    obtain ⟨q1, q2⟩ := lowest_unique hp r1 hval r2 hcop r3 hd
    rw [q1, q2]

theorem ratioExactPy_proven : RatioExactPy := by
  refine ⟨fun neg e => rfl, fun neg c e hc hl => ?_, fun neg c e n d h => ?_, pyRatio_eq_c,
    fun neg s p => rfl, fun neg => rfl⟩
  · simp only [pyRatio, hc, ↓reduceIte, intLimit, gt_iff_lt, hl, bind, Except.bind]
  · by_cases hl : numDigits c ≤ maxStrDigits
    · rw [pyRatio_eq_c neg c e hl] at h
      exact ratioCorrectC_proven neg c e n d h
    · by_cases hc : c = 0
      · subst hc; exact absurd hl (by decide)
      · simp only [pyRatio, hc, ↓reduceIte, intLimit, gt_iff_lt, Nat.lt_of_not_le hl, bind,
          Except.bind] at h
        exact absurd h (by simp)

end PyLean.Decimal
