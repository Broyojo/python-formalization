import PyLean.CoreLibs.CalStat.StatExact

/-!
Refuted statements about `_sqrtprod`, `correlation`, `_decimal_sqrt_of_frac` and `quantiles`
(Lib/statistics.py, CPython 3.15.2). Each counterexample is evaluated on the mirror by the kernel
and was run on python3 3.15.2; the bug records under `bugs/` hold the reproducers.
-/

namespace PyLean.CoreLibs.CalStat

open PyLean

/-- `q` is a binary64 value: rounding it to a float gives it back. -/
def Repr64 (q : Rat) : Prop := Flt.ofRat q = .fin q

/-- `q` is a normal float: representable and at least `2**-1022` in magnitude. -/
def Normal64 (q : Rat) : Prop := Repr64 q ∧ (Flt.pow2 (-1022) ≤ q ∨ q ≤ -Flt.pow2 (-1022))

/-- `_sqrtprod`, statistics.py:1772-1795: "Return sqrt(x * y) computed with improved accuracy and
without overflow/underflow." For positive finite floats the result is a positive finite float `v`
within about one unit in the last place of the root: `|v*v - x*y| <= 2**-50 * x*y`. The source
rescales when `sqrt(x * y)` is `0.0` (statistics.py:1784-1789) but not when the product only
underflows into the subnormal range, where it keeps a handful of bits. -/
def SqrtprodAccurate : Prop :=
  ∀ a b : Rat, 0 < a → 0 < b → Repr64 a → Repr64 b →
    ∃ v : Rat, sqrtprod (.fin a) (.fin b) = .ok (.fin v) ∧
      v * v - a * b ≤ Flt.pow2 (-50) * (a * b) ∧ a * b - v * v ≤ Flt.pow2 (-50) * (a * b)

/-- `_sqrtprod(10 * 2**-540, 10 * 2**-538)`: the product `100 * 2**-1078` is subnormal and rounds to
`96 * 2**-1078`, so the result is `9.79... * 2**-539` instead of `10 * 2**-539`, 2% low. -/
theorem sqrtprodAccurate_refuted : ¬SqrtprodAccurate := by
  intro h
  have ha : Repr64 (10 * Flt.pow2 (-540)) := by unfold Repr64; decide +kernel
  have hb : Repr64 (10 * Flt.pow2 (-538)) := by unfold Repr64; decide +kernel
  obtain ⟨v, hv, h1, h2⟩ := h _ _ (by decide +kernel) (by decide +kernel) ha hb
  have e : sqrtprod (.fin (10 * Flt.pow2 (-540))) (.fin (10 * Flt.pow2 (-538))) =
      .ok (.fin (2757880273211543 * Flt.pow2 (-587))) := by decide +kernel
  rw [e] at hv
  have hv' := (Flt.fin.inj (Except.ok.inj hv)).symm
  subst hv'
  revert h2
  decide +kernel

/-- `correlation`, statistics.py:687-739: "Pearson's correlation coefficient r takes values between
-1 and +1. It measures the strength and direction of a linear relationship." For exactly
proportional data, `y[i] == c * x[i]` with `c > 0`, normal floats throughout and `x` not constant,
`r` is `1.0` up to rounding: within `2**-50`. -/
def CorrelationProportional : Prop :=
  ∀ (xs : List Rat) (c : Rat), 0 < c → (∀ q ∈ xs, Normal64 q ∧ Normal64 (c * q)) →
    (∃ a ∈ xs, ∃ b ∈ xs, a ≠ b) →
    ∃ r : Rat, correlation (floats (xs.map .fin)) (floats (xs.map (fun q => Flt.fin (c * q)))) "linear" =
        .ok (.flt (.fin r)) ∧ r - 1 ≤ Flt.pow2 (-50) ∧ 1 - r ≤ Flt.pow2 (-50)

/-- The data `[1, 2, 3, 4, 5]` times `2**-270`, and `y = 2 * x`: every value and both sums of
squares (`10 * 2**-540`, `10 * 2**-538`) are normal floats, yet `r == 1.0206207261596576`. The
product of the sums of squares underflows inside `_sqrtprod`. -/
theorem correlationProportional_refuted : ¬CorrelationProportional := by
  intro h
  have hx : ∀ q ∈ [1, 2, 3, 4, 5].map (fun i : Nat => (i : Rat) * Flt.pow2 (-270)),
      Normal64 q ∧ Normal64 (2 * q) := by
    simp only [List.map, List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl | rfl) <;>
      exact ⟨⟨by unfold Repr64; decide +kernel, by decide +kernel⟩,
             ⟨by unfold Repr64; decide +kernel, by decide +kernel⟩⟩
  obtain ⟨r, hr, h1, -⟩ := h _ 2 (by decide) hx
    ⟨1 * Flt.pow2 (-270), by simp, 2 * Flt.pow2 (-270), by simp, by decide +kernel⟩
  have e : correlation (floats (([1, 2, 3, 4, 5].map (fun i : Nat => (i : Rat) * Flt.pow2 (-270))).map .fin))
      (floats (([1, 2, 3, 4, 5].map (fun i : Nat => (i : Rat) * Flt.pow2 (-270))).map (fun q => Flt.fin (2 * q))))
      "linear" = .ok (.flt (.fin (mkRat 4596467122019239 4503599627370496))) := by decide +kernel
  rw [e] at hr
  have hr' := (Flt.fin.inj (Val.flt.inj (Except.ok.inj hr))).symm
  subst hr'
  revert h1
  decide +kernel

/-- `_decimal_sqrt_of_frac`, statistics.py:1731-1756: "Square root of n/m as a Decimal, correctly
rounded." In the default context (28 digits, `ROUND_HALF_EVEN`) that is the half-even rounding of the
root. Stated where the root `s` is rational, so that the rounding is `decRound s`. -/
def DecimalSqrtHalfEven : Prop :=
  ∀ (n m : Int) (s : Rat), 0 < n → 0 < m → 0 < s → s * s = (n : Rat) / (m : Rat) →
    decimalSqrtOfFrac n m = .ok (decRound s)

/-- The root `1.0000000000000000000000000015` lies exactly halfway between two 28-digit values; half-even
gives `1.000000000000000000000000002`, the function `1.000000000000000000000000001`: neither
neighbour test at statistics.py:1747 and :1753 fires on equality. -/
theorem decimalSqrtHalfEven_refuted : ¬DecimalSqrtHalfEven := by
  intro h
  have e := h (2000000000000000000000000003 ^ 2) (2000000000000000000000000000 ^ 2)
    (mkRat 2000000000000000000000000003 2000000000000000000000000000)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have e1 : decimalSqrtOfFrac (2000000000000000000000000003 ^ 2) (2000000000000000000000000000 ^ 2) =
      .ok (mkRat 1000000000000000000000000001 1000000000000000000000000000) := by decide +kernel
  have e2 : decRound (mkRat 2000000000000000000000000003 2000000000000000000000000000) =
      mkRat 1000000000000000000000000002 1000000000000000000000000000 := by decide +kernel
  rw [e1, e2] at e
  revert e
  decide +kernel

/-- The narrowing of `DecimalSqrtHalfEven` that may hold: the result is one of the 28-digit values
nearest to the root (ties either way). Stated without the root: a 28-digit value `y` other than
the result `r` is never closer, i.e. the midpoint of `r` and `y` lies on `y`'s far side of the root. -/
def DecimalSqrtNearest : Prop :=
  ∀ (n m : Int) (r y : Rat), 0 < n → 0 < m → 0 < y → decRound y = y →
    decimalSqrtOfFrac n m = .ok r →
    (r < y → (n : Rat) ≤ ((r + y) / 2) * ((r + y) / 2) * (m : Rat)) ∧
    (y < r → ((r + y) / 2) * ((r + y) / 2) * (m : Rat) ≤ (n : Rat))

/-- `quantiles(..., method='inclusive')`, statistics.py:1176-1211: "If method is set to inclusive,
data is treated as population data. The minimum value is treated as the 0th percentile and the
maximum value is treated as the 100th percentile." Every cut point of finite float data lies between
the minimum and the maximum. -/
def QuantilesInclusiveInRange : Prop :=
  ∀ (xs : List Rat) (n : Int) (qs : List PyN), (∀ q ∈ xs, Repr64 q) →
    quantiles (floats (xs.map .fin)) n "inclusive" = .ok qs →
    ∀ c ∈ qs, ∃ r : Rat, c.v = .flt (.fin r) ∧ (∃ a ∈ xs, a ≤ r) ∧ (∃ b ∈ xs, r ≤ b)

/-- `quantiles([0.1, 0.1], n=3, method='inclusive')` is `[0.10000000000000002] * 2`: the data is
constant and every cut point is above it. `(0.1 * 2 + 0.1 * 1) / 3` rounds twice. -/
theorem quantilesInclusiveInRange_refuted : ¬QuantilesInclusiveInRange := by
  intro h
  have h01 : Repr64 (mkRat 3602879701896397 36028797018963968) := by unfold Repr64; decide +kernel
  have e : quantiles (floats ([mkRat 3602879701896397 36028797018963968,
      mkRat 3602879701896397 36028797018963968].map .fin)) 3 "inclusive" =
      .ok [(Val.flt (.fin (mkRat 7205759403792795 72057594037927936))).toN,
           (Val.flt (.fin (mkRat 7205759403792795 72057594037927936))).toN] := by decide +kernel
  have := h _ 3 _ (by simp [h01]) e (Val.flt (.fin (mkRat 7205759403792795 72057594037927936))).toN
    (by simp)
  obtain ⟨r, hr, -, b, hb, hle⟩ := this
  simp only [Val.toN, Val.flt.injEq, Flt.fin.injEq] at hr
  subst hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hb
  subst hb
  revert hle
  decide +kernel

end PyLean.CoreLibs.CalStat
