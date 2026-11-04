import PyLean.Decimal.CmpProps
import PyLean.Fractions.Hash

/-!
Rounding, integer conversions and hashing.
-/

namespace PyLean.Decimal

open PyLean

/-! ## Rounding modes (`_rescale`) -/

theorem numDigits_mono {a b : Nat} (h : a ≤ b) : numDigits a ≤ numDigits b :=
  (numDigits_le_iff (numDigits_pos b)).mpr (Nat.lt_of_le_of_lt h (lt_pow_numDigits b))

theorem incr_ok {q d : Nat} (h1 : ¬ max d 1 > maxStrDigits) (h2 : ¬ numDigits (q + 1) > maxStrDigits) :
    incr q d = .ok (q + 1) := by
  simp [incr, intLimit, strLimit, h1, h2, bind, Except.bind, pure, Except.pure]

/-- `_rescale` to a larger exponent cannot hit the int/str limit when the coefficient is
within it: the kept prefix plus one has no more digits than the coefficient. -/
theorem rescale_noerr (m : Rounding) (neg : Bool) (c : Nat) (e x : Int) (hc : c ≠ 0) (hx : e < x)
    (hd : numDigits c ≤ maxStrDigits) (err : PyExc) : rescale (.fin neg c e) x m ≠ .error err := by
  unfold rescale
  simp only [hc, ↓reduceIte, show ¬(e ≥ x) by omega]
  by_cases hneg : (numDigits c : Int) + e - x < 0
  · simp only [hneg, ↓reduceIte, roundKeep]
    have hi : incr (1 / 10 ^ (numDigits 1 - 0)) 0 = .ok (1 / 10 ^ (numDigits 1 - 0) + 1) :=
      incr_ok (by decide) (by decide)
    split <;> simp_all [bind, Except.bind, pure, Except.pure]
  · simp only [hneg, ↓reduceIte, roundKeep]
    have hk : 1 ≤ numDigits c - ((numDigits c : Int) + e - x).toNat := by omega
    have hq : c / 10 ^ (numDigits c - ((numDigits c : Int) + e - x).toNat) + 1 ≤ c := by
      have h10 : 10 ≤ 10 ^ (numDigits c - ((numDigits c : Int) + e - x).toNat) :=
        Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) hk)
      have := Nat.div_le_div_left (a := c) h10 (by decide)
      omega
    have hi := incr_ok (q := c / 10 ^ (numDigits c - ((numDigits c : Int) + e - x).toNat))
      (d := ((numDigits c : Int) + e - x).toNat) (by simp only [maxStrDigits] at hd ⊢; omega)
      (by have := numDigits_mono hq; simp only [maxStrDigits] at hd ⊢; omega)
    split <;> simp_all [bind, Except.bind, pure, Except.pure]

/-- For every rounding mode, every finite non-zero value `c·10^e` and every target exponent
`x > e`, `_pydecimal`'s `_rescale` returns the coefficient the mode prescribes for the dropped
digits (`roundSpec`), at exponent `x`; the only other outcome is the int/str-limit
`ValueError`, and only for a coefficient of more than 4300 digits. -/
def RoundingModesCorrect : Prop :=
  ∀ (m : Rounding) (neg : Bool) (c : Nat) (e x : Int),
    (c ≠ 0 → e < x →
      rescale (.fin neg c e) x m = .ok (.fin neg
          (roundSpec m neg (c / 10 ^ (x - e).toNat) (c % 10 ^ (x - e).toNat) (10 ^ (x - e).toNat)) x) ∨
      (maxStrDigits < numDigits c ∧ ∃ msg, rescale (.fin neg c e) x m = .error (.valueError msg))) ∧
    (c ≠ 0 → x ≤ e → rescale (.fin neg c e) x m = .ok (.fin neg (c * 10 ^ (e - x).toNat) x)) ∧
    rescale (.fin neg 0 e) x m = .ok (.fin neg 0 x)

theorem roundingModesCorrect_proven : RoundingModesCorrect := by
  intro m neg c e x
  refine ⟨fun hc hx => ?_, fun hc hx => by simp [rescale, hc, hx], by simp [rescale]⟩
  rcases rescale_round m neg c e x hc hx with h | ⟨msg, h⟩
  · exact Or.inl h
  · by_cases hd : numDigits c ≤ maxStrDigits
    · exact absurd h (rescale_noerr m neg c e x hc hx hd _)
    · exact Or.inr ⟨by omega, msg, h⟩

/-! ## `to_integral_value` -/

/-- For every context, rounding argument and finite value `c·10^e` with `e < 0`,
`to_integral_value` (_pydecimal.py:2762-2776) returns the integer `roundSpec` prescribes (at
exponent 0) and leaves the flags untouched (docs: "without signaling Inexact or Rounded",
Doc/library/decimal.rst:929), except for the int/str-limit `ValueError` on a coefficient of
more than 4300 digits; a zero coefficient gives the signed zero at exponent 0; values with
`e ≥ 0` and infinities are returned unchanged; a NaN goes through `_check_nans`. -/
def ToIntegralValueCorrect : Prop :=
  ∀ (ctx : Ctx) (r : Option Rounding) (neg : Bool) (c : Nat) (e : Int) (fl : List Signal),
    let m := r.getD ctx.rounding
    let k := e.natAbs
    (e ≥ 0 → (toIntegralValue ctx (.fin neg c e) r).run fl = .ok (.fin neg c e, fl)) ∧
    (e < 0 → c ≠ 0 →
      (toIntegralValue ctx (.fin neg c e) r).run fl =
        .ok (.fin neg (roundSpec m neg (c / 10 ^ k) (c % 10 ^ k) (10 ^ k)) 0, fl) ∨
      (maxStrDigits < numDigits c ∧ ∃ msg, (toIntegralValue ctx (.fin neg c e) r).run fl = .error (.valueError msg))) ∧
    (e < 0 → (toIntegralValue ctx (.fin neg 0 e) r).run fl = .ok (.fin neg 0 0, fl)) ∧
    (toIntegralValue ctx (.inf neg) r).run fl = .ok (.inf neg, fl) ∧
    (toIntegralValue ctx (.nan neg false c) r).run fl = .ok (.nan neg false (c % 10 ^ nanDigits ctx), fl) ∧
    (toIntegralValue ctx (.nan neg true c) r).run fl =
      afterSig ctx .invalidOperation fl (.nan neg false (c % 10 ^ nanDigits ctx))

theorem toIntegralValueCorrect_proven : ToIntegralValueCorrect := by
  intro ctx r neg c e fl m k
  refine ⟨fun he => ?_, fun he hc => ?_, fun he => ?_, by cases neg <;> rfl, ?_, ?_⟩
  · simp [toIntegralValue, he, StateT.run, pure, StateT.pure, Except.pure]
  · have hk : (0 - e).toNat = k := by simp only [k]; omega
    rcases (roundingModesCorrect_proven m neg c e 0).1 hc he with h | ⟨hd, msg, h⟩
    · left
      rw [hk] at h
      simp [toIntegralValue, show ¬ e ≥ 0 by omega, liftPy, h, StateT.run, Functor.map,
        Except.map, m]
    · right
      exact ⟨hd, msg, by simp [toIntegralValue, show ¬ e ≥ 0 by omega, liftPy, h, StateT.run, Functor.map,
        Except.map, m]⟩
  · simp [toIntegralValue, show ¬ e ≥ 0 by omega, liftPy, rescale, StateT.run, Functor.map, Except.map]
  · have h := fixNan_spec ctx neg false c
    simp [toIntegralValue, checkNans, StateT.run, pure, StateT.pure, Except.pure, bind, StateT.bind,
      Except.bind, h]
  · rw [← raiseSig_then]
    have h := fixNan_spec ctx neg false c
    have e : toIntegralValue ctx (.nan neg true c) r =
        (do raiseSig ctx .invalidOperation; pure (.nan neg false (c % 10 ^ nanDigits ctx))) := by
      simp [toIntegralValue, checkNans, h]
    rw [e]

/-! ## Integer conversions -/

/-- `_decimal`'s `int()`, `math.floor`, `math.ceil` and `round()` (and every
other rounding mode `dec_as_long` is called with): for every finite value
`±c·10^e`, the result is `±c·10^e` when `e ≥ 0`, and otherwise the signed
integer whose magnitude `roundSpec` prescribes. -/
def IntConversionsC : Prop :=
  ∀ (m : Rounding) (neg : Bool) (c : Nat) (e : Int),
    let k := e.natAbs
    let mag := if e ≥ 0 then c * 10 ^ e.toNat else roundSpec m neg (c / 10 ^ k) (c % 10 ^ k) (10 ^ k)
    cToInt m (.fin neg c e) = .ok (if neg then -(mag : Int) else mag)

theorem intConversionsC_proven : IntConversionsC := by
  intro m neg c e k mag
  simp only [cToInt, roundToIntExact, truncDiv, mag]
  by_cases he : e ≥ 0
  · simp [he]
  · have hk1 : 1 ≤ k := by simp only [k]; omega
    have hr : c % 10 ^ k < 10 ^ k := Nat.mod_lt _ (Nat.pow_pos (by decide))
    have hs := (roundDir_spec m neg (c / 10 ^ k) (c % 10 ^ k) (5 * 10 ^ (k - 1)) (by
      rw [← pow_ten_eq_two_half hk1]; exact hr)).1
    rw [← pow_ten_eq_two_half hk1] at hs
    simp only [he, ↓reduceIte]
    rw [← hs]

/-- The same for `_pydecimal`, except that the int/str-limit `ValueError`
is the only other outcome. -/
def IntConversionsPyOrLimit : Prop :=
  ∀ (m : Rounding) (neg : Bool) (c : Nat) (e : Int),
    let k := e.natAbs
    let mag := if e ≥ 0 then c * 10 ^ e.toNat else roundSpec m neg (c / 10 ^ k) (c % 10 ^ k) (10 ^ k)
    pyToInt m (.fin neg c e) = cToInt m (.fin neg c e) ∨
    ((maxStrDigits < numDigits c ∨ maxStrDigits < numDigits mag) ∧
      ∃ msg, pyToInt m (.fin neg c e) = .error (.valueError msg))

theorem intConversionsPyOrLimit_proven : IntConversionsPyOrLimit := by
  intro m neg c e k mag
  have hC := intConversionsC_proven m neg c e
  simp only at hC
  rw [hC]
  simp only [pyToInt]
  by_cases hc : c = 0
  · subst hc
    left
    have h0 : roundSpec m neg (0 / 10 ^ e.natAbs) (0 % 10 ^ e.natAbs) (10 ^ e.natAbs) = 0 := by
      cases m <;> simp [roundSpec]
    have hl : ¬ maxStrDigits < numDigits 0 := by decide
    simp only [rescale, ↓reduceIte, bind, Except.bind, pyInt, ge_iff_le, Int.le_refl, intLimit, hl,
      pure, Except.pure, truncDiv, h0, Nat.zero_mul]
    cases neg <;> simp
  by_cases he : e ≥ 0
  · have hres : rescale (.fin neg c e) 0 m = .ok (.fin neg (c * 10 ^ e.toNat) 0) := by
      simp [rescale, hc, he]
    simp only [hres, bind, Except.bind, pyInt, ge_iff_le, Int.le_refl, ↓reduceIte, he]
    by_cases hl : maxStrDigits < numDigits (c * 10 ^ e.toNat)
    · right; exact ⟨Or.inr (by simp only [mag, if_pos he]; exact hl),
        limitToIntMsg (numDigits (c * 10 ^ e.toNat)), by simp [intLimit, hl]⟩
    · left
      simp [intLimit, hl, pure, Except.pure, truncDiv]
  · have hk : (0 - e).toNat = e.natAbs := by omega
    rcases (roundingModesCorrect_proven m neg c e 0).1 hc (by omega) with h | ⟨hd, msg, h⟩
    · rw [hk] at h
      simp only [h, bind, Except.bind, pyInt, ge_iff_le, Int.le_refl, ↓reduceIte, he]
      have hm : mag = roundSpec m neg (c / 10 ^ e.natAbs) (c % 10 ^ e.natAbs) (10 ^ e.natAbs) := by
        simp only [mag, k, if_neg he]
      rw [← hm]
      by_cases hl : maxStrDigits < numDigits mag
      · right; exact ⟨Or.inr hl, limitToIntMsg (numDigits mag), by simp [intLimit, hl]⟩
      · left
        simp [intLimit, hl, pure, Except.pure, truncDiv]
    · right; exact ⟨Or.inl hd, msg, by simp [h, bind, Except.bind]⟩

/-! ## Hashing -/

/-- `_decimal`'s literal `inv10_p` (_decimal.c:5827) is `_pydecimal`'s
`_PyHASH_10INV = pow(10, P - 2, P)`, so the two hash formulas coincide. -/
theorem tenInv_eq : PyLean.Fractions.tenInv = 2075258708292324556 := by
  set_option maxRecDepth 100000 in decide +kernel

/-- `_decimal`'s `hash()` agrees with numeric equality: for every finite
`Decimal` it equals `hash(Fraction(d))` (`Fraction(d)` built from
`as_integer_ratio`), and for every int `n`, `hash(Decimal(n)) == hash(n)`. -/
def HashConsistentC : Prop :=
  (∀ (neg : Bool) (c : Nat) (e : Int),
    cHash (.fin neg c e) = .ok (some (PyLean.Fractions.hash (PyLean.Fractions.ofDecimal neg c e)))) ∧
  (∀ n : Int, (cFromInt n >>= cHash) = .ok (some (intHash n)))

theorem hashConsistentC_proven : HashConsistentC := by
  refine ⟨fun neg c e => ?_, fun n => ?_⟩
  · simp [cHash, hashFinite, PyLean.Fractions.hashMatchesDecimal_proven neg c e]
  · have h1 := PyLean.Fractions.hashMatchesDecimal_proven (decide (n < 0)) n.natAbs 0
    have h2 : PyLean.Fractions.ofDecimal (decide (n < 0)) n.natAbs 0 = PyLean.Fractions.ofInt n := by
      simp only [PyLean.Fractions.ofDecimal, PyLean.Fractions.ofInt]
      have hn : (if n < 0 then -(n.natAbs : Int) else n.natAbs) = n := by
        split <;> omega
      simp [hn]
    rw [h2, PyLean.Fractions.hashMatchesInt_proven n] at h1
    simp [cFromInt, cHash, bind, Except.bind, hashFinite, ← h1, intHash]

/-! ## `as_integer_ratio` -/

/-- `_decimal`'s `as_integer_ratio`: for every finite value `±c·10^e`, the result
`(n, d)` has `d > 0`, is in lowest terms, and equals the value exactly. -/
def RatioCorrectC : Prop :=
  ∀ (neg : Bool) (c : Nat) (e : Int) (n d : Int), cRatio (.fin neg c e) = .ok (n, d) →
    0 < d ∧ Int.gcd n d = 1 ∧
    n * 10 ^ (-e).toNat = (if neg then -(c : Int) else c) * 10 ^ e.toNat * d

theorem ratioCorrectC_proven : RatioCorrectC := by
  intro neg c e n d h
  simp only [cRatio] at h
  by_cases he : e ≥ 0
  · simp only [he, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hz : (-e).toNat = 0 := by omega
    refine ⟨by decide, by simp [Int.gcd], ?_⟩
    rw [hz]
    cases neg <;> simp [Int.pow_zero, Int.neg_mul]
  · simp only [he, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hk : (-e).toNat = e.natAbs := by omega
    have hz : e.toNat = 0 := by omega
    have hp : 0 < 10 ^ e.natAbs := Nat.pow_pos (by decide)
    have hg : 0 < Nat.gcd c (10 ^ e.natAbs) := Nat.gcd_pos_of_pos_right _ hp
    have h1 : Nat.gcd c (10 ^ e.natAbs) ∣ c := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd c (10 ^ e.natAbs) ∣ 10 ^ e.natAbs := Nat.gcd_dvd_right _ _
    obtain ⟨u, hu⟩ := h1
    obtain ⟨v, hv⟩ := h2
    have hcop := Nat.coprime_div_gcd_div_gcd (m := c) (n := 10 ^ e.natAbs) hg
    have hd : 0 < 10 ^ e.natAbs / Nat.gcd c (10 ^ e.natAbs) := Nat.div_pos (Nat.le_of_dvd hp ⟨v, hv⟩) hg
    have hval : c / Nat.gcd c (10 ^ e.natAbs) * 10 ^ e.natAbs = c * (10 ^ e.natAbs / Nat.gcd c (10 ^ e.natAbs)) := by
      generalize hG : Nat.gcd c (10 ^ e.natAbs) = g at *
      generalize hP : 10 ^ e.natAbs = P at *
      subst hu hv
      rw [Nat.mul_div_cancel_left _ hg, Nat.mul_div_cancel_left _ hg, ← Nat.mul_assoc, Nat.mul_comm u g]
    rw [hk, hz]
    generalize hN : c / Nat.gcd c (10 ^ e.natAbs) = N at *
    generalize hD : 10 ^ e.natAbs / Nat.gcd c (10 ^ e.natAbs) = D at *
    refine ⟨by omega, ?_, ?_⟩
    · cases neg
      · simpa [Int.gcd] using hcop
      · simpa [Int.gcd] using hcop
    · have hval' : (N : Int) * (10 : Int) ^ e.natAbs = c * D := by
        exact_mod_cast hval
      cases neg
      · simpa using hval'
      · simp only [↓reduceIte, Int.pow_zero, Int.mul_one, Int.neg_mul]
        omega

end PyLean.Decimal
