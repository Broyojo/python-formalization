import PyLean.CoreLibs.CalStat.DistProps

/-! `_float_sqrt_of_frac`: what is proven (zero and perfect squares come out exact) and the full
statement, correct rounding, which stays open. -/

namespace PyLean.CoreLibs.CalStat

open PyLean

theorem bitLen_nonneg (m : Int) : 0 ≤ bitLen m := by
  unfold bitLen; omega

theorem isqrtInt_square (s : Nat) : isqrtInt (((s * s : Nat) : Int)) = .ok (s : Int) := by
  obtain ⟨r, h1, h2, h3⟩ := MathInt.isqrtFloorSqrt_proven (s * s)
  have hle : r ≤ s := Nat.mul_self_le_mul_self_iff.mp h2
  have hlt : s < r + 1 := Nat.mul_self_lt_mul_self_iff.mp h3
  have : r = s := by omega
  subst this
  simp only [isqrtInt, h1]
  rfl

/-- `_float_sqrt_of_frac` is exact where the root is: `0` gives `0.0`, and `k*k` gives what `k`
converts to, for `k` below `2**53`. -/
def FloatSqrtBasic : Prop :=
  (∀ m : Int, 0 < m → floatSqrtOfFrac 0 m = .ok (.zero false)) ∧
  (∀ k : Nat, 0 < k → k < 2 ^ 53 →
    floatSqrtOfFrac ((k * k : Nat) : Int) 1 = intTrueDiv (k : Int) 1)

theorem floatSqrtBasic_proven : FloatSqrtBasic := by
  constructor
  · intro m hm
    have hb := bitLen_nonneg m
    have h0 : bitLen 0 = 0 := rfl
    have hq : ¬ ((bitLen 0 - bitLen m - sqrtBitWidth) / 2 ≥ 0) := by
      rw [h0]
      unfold sqrtBitWidth
      omega
    generalize hQ : (bitLen 0 - bitLen m - sqrtBitWidth) / 2 = q at hq
    have hr : integerSqrtOfFracRto (0 * 2 ^ (-2 * q).toNat) m = .ok 0 := by
      have e : isqrtInt 0 = .ok 0 := by simpa using isqrtInt_square 0
      simp [integerSqrtOfFracRto, e, bind, Except.bind, pure, Except.pure]
    have hp : (2 : Int) ^ (-q).toNat ≠ 0 := Int.pow_ne_zero (by decide)
    have hn : ¬ ((2 : Int) ^ (-q).toNat < 0) := by
      have : (0 : Int) < 2 ^ (-q).toNat := Int.pow_pos (by decide)
      omega
    simp only [floatSqrtOfFrac, hQ, hq, if_false, bind, Except.bind, hr, intTrueDiv, hp, if_true]
    simp [hn]
  · intro k h0 h1
    have hk2 : k * k < 2 ^ 106 := by
      calc k * k < 2 ^ 53 * 2 ^ 53 := Nat.mul_self_lt_mul_self h1
        _ = 2 ^ 106 := by decide
    have hk1 : 1 ≤ k * k := Nat.mul_pos h0 h0
    have hbl : bitLength (k * k) ≤ 106 := by
      refine Classical.byContradiction fun hc => ?_
      have := (MathInt.two_pow_le_iff_lt_bitLength (k * k) 106 hk1).mpr (by omega)
      omega
    have e1 : bitLen ((k * k : Nat) : Int) = (bitLength (k * k) : Int) := by
      unfold bitLen
      rw [Int.natAbs_natCast]
    have e2 : bitLen 1 = 1 := by decide
    have hq : ¬ ((bitLen ((k * k : Nat) : Int) - bitLen 1 - sqrtBitWidth) / 2 ≥ 0) := by
      rw [e1, e2]
      unfold sqrtBitWidth
      omega
    generalize hQ : (bitLen ((k * k : Nat) : Int) - bitLen 1 - sqrtBitWidth) / 2 = q at hq
    obtain ⟨p, hp⟩ : ∃ p : Nat, -q = p := ⟨(-q).toNat, by omega⟩
    have hp0 : (-q).toNat = p := by omega
    have hp2 : (-2 * q).toNat = 2 * p := by omega
    let s : Nat := k * 2 ^ p
    have hss : ((k * k : Nat) : Int) * 2 ^ (2 * p) = ((s * s : Nat) : Int) := by
      simp only [s]
      push_cast
      rw [Nat.mul_comm 2 p] <;> skip
      rw [Int.pow_mul]
      simp only [Int.pow_succ, Int.pow_zero, Int.one_mul]
      grind
    have hdiv : ((s * s : Nat) : Int) / 1 = ((s * s : Nat) : Int) := Int.ediv_one _
    have hr : integerSqrtOfFracRto (((k * k : Nat) : Int) * 2 ^ (2 * p)) 1 = .ok (s : Int) := by
      rw [hss]
      simp only [integerSqrtOfFracRto, hdiv, isqrtInt_square s, bind, Except.bind, pure, Except.pure]
      have : ((s : Int) * s * 1 ≠ ((s * s : Nat) : Int)) = False := by
        simp
      simp [this]
    have hP : ((2 : Int) ^ p) ≠ 0 := Int.pow_ne_zero (by decide)
    have hPn : ¬ ((2 : Int) ^ p < 0) := by
      have : (0 : Int) < 2 ^ p := Int.pow_pos (by decide)
      omega
    have hspos : 0 < s := Nat.mul_pos h0 (Nat.two_pow_pos p)
    have hs0 : ¬ ((s : Int) = 0) := by omega
    have hsn : ¬ ((s : Int) < 0) := by omega
    have hk0 : ¬ ((k : Int) = 0) := by omega
    have hkn : ¬ ((k : Int) < 0) := by omega
    have heq : (((s : Int)) : Rat) / (((2 : Int) ^ p : Int) : Rat) = ((k : Int) : Rat) / ((1 : Int) : Rat) := by
      have hP' : (((2 : Int) ^ p : Int) : Rat) ≠ 0 := fun h => hP (Rat.intCast_eq_zero_iff.mp h)
      have es : ((s : Int) : Rat) = ((k : Int) : Rat) * (((2 : Int) ^ p : Int) : Rat) := by
        simp only [s]
        push_cast
        rfl
      rw [es]
      generalize (((2 : Int) ^ p : Int) : Rat) = P at hP'
      generalize ((k : Int) : Rat) = K
      have : ((1 : Int) : Rat) = 1 := rfl
      rw [this]
      grind
    simp only [floatSqrtOfFrac, hQ, hq, if_false, bind, Except.bind, hp0, hp2, hr]
    simp only [intTrueDiv, hP, hs0, hk0, if_false, hsn, hPn, hkn]
    have h1ne : ¬ ((1 : Int) = 0) := by decide
    have h1n : ¬ ((1 : Int) < 0) := by decide
    simp only [h1ne, h1n, if_false, heq]

/-- The docstring of `_float_sqrt_of_frac`: "Square root of n/m as a float, correctly rounded". A
binary64 value `y` different from the result `v` is never closer to the root: the midpoint of `v` and
`y` lies on `y`'s far side of the exact root. Comparing squares keeps this in the rationals. -/
def FloatSqrtCorrectlyRounded : Prop :=
  ∀ (n m : Int) (v y : Rat), 0 < n → 0 < m → 0 < v → 0 < y →
    floatSqrtOfFrac n m = .ok (.fin v) → Flt.ofRat y = .fin y →
    (v < y → (n : Rat) ≤ ((v + y) / 2) * ((v + y) / 2) * (m : Rat)) ∧
    (y < v → ((v + y) / 2) * ((v + y) / 2) * (m : Rat) ≤ (n : Rat))

/-- `X + Y` and `Y + X` have the same `sigma`. `vector_norm` adds the squares of its coordinates
in order into a compensated sum, so this does not follow from the shape of the code. -/
def HypotCommutes : Prop :=
  ∀ a b : Flt, a.isFinite = true → b.isFinite = true → hypot a b = hypot b a

end PyLean.CoreLibs.CalStat
