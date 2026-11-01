import PyLean.Decimal.Compare
import PyLean.Fractions.Hash

/-!
Rounding, integer conversions and hashing.
-/

namespace PyLean.Decimal

open PyLean

/-! ## Rounding modes (`_rescale`) -/

/-- For every rounding mode, every finite non-zero value `c·10^e` and every
target exponent `x > e`, `_pydecimal`'s `_rescale` returns the coefficient
the mode prescribes for the dropped digits (`roundSpec`), at exponent `x`;
the only other outcome is the int/str-limit `ValueError`. -/
def RoundingModesCorrect : Prop :=
  ∀ (m : Rounding) (neg : Bool) (c : Nat) (e x : Int), c ≠ 0 → e < x →
    rescale (.fin neg c e) x m = .ok (.fin neg
        (roundSpec m neg (c / 10 ^ (x - e).toNat) (c % 10 ^ (x - e).toNat) (10 ^ (x - e).toNat)) x) ∨
    ∃ msg, rescale (.fin neg c e) x m = .error (.valueError msg)

theorem roundingModesCorrect_proven : RoundingModesCorrect :=
  fun m neg c e x hc hx => rescale_round m neg c e x hc hx

/-! ## `to_integral_value` -/

/-- For every context, rounding argument and finite value `c·10^e` with
`e < 0`, `to_integral_value` returns the integer `roundSpec` prescribes (at
exponent 0) and leaves the flags untouched (docs: "without signaling
Inexact or Rounded", Doc/library/decimal.rst:937), or raises the int/str-limit `ValueError`; values with
`e ≥ 0` are returned unchanged. -/
def ToIntegralValueCorrect : Prop :=
  ∀ (ctx : Ctx) (r : Option Rounding) (neg : Bool) (c : Nat) (e : Int) (fl : List Signal),
    let m := r.getD ctx.rounding
    let k := e.natAbs
    (e ≥ 0 → (toIntegralValue ctx (.fin neg c e) r).run fl = .ok (.fin neg c e, fl)) ∧
    (e < 0 → c ≠ 0 →
      (toIntegralValue ctx (.fin neg c e) r).run fl =
        .ok (.fin neg (roundSpec m neg (c / 10 ^ k) (c % 10 ^ k) (10 ^ k)) 0, fl) ∨
      ∃ msg, (toIntegralValue ctx (.fin neg c e) r).run fl = .error (.valueError msg))

theorem toIntegralValueCorrect_proven : ToIntegralValueCorrect := by
  intro ctx r neg c e fl m k
  refine ⟨fun he => ?_, fun he hc => ?_⟩
  · simp [toIntegralValue, he, StateT.run, pure, StateT.pure, Except.pure]
  · have hk : (0 - e).toNat = k := by simp only [k]; omega
    rcases rescale_round m neg c e 0 hc he with h | ⟨msg, h⟩
    · left
      rw [hk] at h
      simp [toIntegralValue, show ¬ e ≥ 0 by omega, liftPy, h, StateT.run, Functor.map,
        Except.map, m]
    · right
      exact ⟨msg, by simp [toIntegralValue, show ¬ e ≥ 0 by omega, liftPy, h, StateT.run, Functor.map,
        Except.map, m]⟩

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
    pyToInt m (.fin neg c e) = cToInt m (.fin neg c e) ∨
    ∃ msg, pyToInt m (.fin neg c e) = .error (.valueError msg)

theorem intConversionsPyOrLimit_proven : IntConversionsPyOrLimit := by
  intro m neg c e
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
    · right; exact ⟨limitToIntMsg (numDigits (c * 10 ^ e.toNat)), by simp [intLimit, hl]⟩
    · left
      simp [intLimit, hl, pure, Except.pure, truncDiv]
  · have hk : (0 - e).toNat = e.natAbs := by omega
    rcases rescale_round m neg c e 0 hc (by omega) with h | ⟨msg, h⟩
    · rw [hk] at h
      simp only [h, bind, Except.bind, pyInt, ge_iff_le, Int.le_refl, ↓reduceIte, he]
      generalize roundSpec m neg (c / 10 ^ e.natAbs) (c % 10 ^ e.natAbs) (10 ^ e.natAbs) = q
      by_cases hl : maxStrDigits < numDigits q
      · right; exact ⟨limitToIntMsg (numDigits q), by simp [intLimit, hl]⟩
      · left
        simp [intLimit, hl, pure, Except.pure, truncDiv]
    · right; exact ⟨msg, by simp [h, bind, Except.bind]⟩

/-! ## Hashing -/

/-- `_decimal`'s literal `inv10_p` (_decimal.c:4903) is `_pydecimal`'s
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

end PyLean.Decimal
