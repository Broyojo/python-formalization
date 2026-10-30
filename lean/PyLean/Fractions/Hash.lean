import PyLean.Fractions.Round

/-!
`Fraction.__hash__` against `int.__hash__` and `Decimal.__hash__`.

The docs (Built-in Types, "Hashing of numeric types") promise
`hash(x) == hash(y)` whenever `x == y` for numbers of different types. For a
Fraction equal to an int or a finite Decimal this is exact modular arithmetic
modulo `P = 2**61 - 1`; it needs only that `10` is invertible modulo `P`,
not that `P` is prime.
-/

namespace PyLean.Fractions

open PyLean

theorem egcd_spec : ∀ (fuel : Nat) (a b : Int), 0 ≤ a → 0 ≤ b → b < fuel →
    (egcd fuel a b).1 = (Int.gcd a b : Int) ∧
      a * (egcd fuel a b).2.1 + b * (egcd fuel a b).2.2 = (egcd fuel a b).1 := by
  intro fuel
  induction fuel with
  | zero => intro a b _ hb hf; omega
  | succ fuel ih =>
    intro a b ha hb hf
    by_cases hb0 : b = 0
    · subst hb0
      simp only [egcd, ↓reduceIte, Int.gcd_zero]
      refine ⟨by omega, by grind⟩
    · have hbpos : 0 < b := by omega
      have r0 := Int.emod_nonneg a hb0
      have r1 := Int.emod_lt_of_pos a hbpos
      obtain ⟨h1, h2⟩ := ih b (a % b) hb r0 (by omega)
      simp only [egcd, hb0, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · rw [h1]
        have e := Int.emod_def a b
        rw [e, Int.gcd_sub_mul_left_right, Int.gcd_comm]
      · have e := Int.emod_def a b
        rw [e] at h2
        grind

/-- `P = 2**61 - 1` is odd and greater than 1; `10` is invertible modulo `P`. -/
theorem hashModulus_gt_one : 1 < hashModulus := by decide

theorem modInv_spec (d : Nat) (hd : Nat.gcd d hashModulus = 1) :
    ∃ x : Nat, modInv (d : Int) hashModulus = some (x : Int) ∧ x < hashModulus ∧
      (d * x) % hashModulus = 1 := by
  have hP : (0 : Int) < hashModulus := by decide
  have hm0 := Int.emod_nonneg (d : Int) (show (hashModulus : Int) ≠ 0 by decide)
  have hm1 := Int.emod_lt_of_pos (d : Int) hP
  obtain ⟨h1, h2⟩ := egcd_spec (hashModulus + 1) ((d : Int) % hashModulus) hashModulus hm0
    (by omega) (by omega)
  have hg : Int.gcd ((d : Int) % hashModulus) hashModulus = 1 := by
    rw [Int.emod_def, Int.gcd_sub_mul_left_left, Int.gcd_natCast_natCast]
    exact hd
  rw [hg] at h1
  simp only [Int.natCast_one] at h1
  obtain ⟨⟨g, x, y⟩, hr⟩ : ∃ r, egcd (hashModulus + 1) ((d : Int) % hashModulus) hashModulus = r :=
    ⟨_, rfl⟩
  rw [hr] at h1 h2
  simp only at h1 h2
  subst h1
  have hx0 := Int.emod_nonneg x (show (hashModulus : Int) ≠ 0 by decide)
  have hx1 := Int.emod_lt_of_pos x hP
  refine ⟨(x % hashModulus).toNat, ?_, by omega, ?_⟩
  · simp only [modInv, hr]
    rw [Int.toNat_of_nonneg hx0]
    rfl
  · have key : ((d : Int) * (x % hashModulus)) % hashModulus = 1 := by
      have ex := Int.emod_def x hashModulus
      have ed := Int.emod_def (d : Int) hashModulus
      have : (d : Int) * (x % hashModulus) =
          1 + hashModulus * (-y + ((d : Int) / hashModulus) * x - d * (x / hashModulus)) := by
        grind
      rw [this, Int.add_mul_emod_self_left]
      decide
    apply Int.ofNat_inj.mp
    rw [Int.natCast_emod, Int.natCast_mul, Int.toNat_of_nonneg hx0]
    exact key

/-- `hash(i)` for an int `i >= 0` is `i % P`. -/
theorem intHash_nat (z : Nat) : intHash z = ((z % hashModulus : Nat) : Int) := by
  simp only [intHash, Int.natAbs_natCast]
  have : ¬ ((z : Int) < 0) := by omega
  simp only [this, ↓reduceIte]
  split
  · omega
  · rfl

theorem modInv_one : modInv 1 hashModulus = some 1 := by
  obtain ⟨x, hx, hxP, h⟩ := modInv_spec 1 (by decide)
  simp only [Int.natCast_one] at hx
  rw [hx]
  simp only [Nat.one_mul] at h
  rw [Nat.mod_eq_of_lt hxP] at h
  rw [h]; rfl

/-- Built-in Types, "Hashing of numeric types": `hash(x) == hash(y)` whenever
`x == y`; here for a Fraction equal to an int. For every int `n`,
`hash(Fraction(n)) == hash(n)`. -/
def HashMatchesInt : Prop := ∀ n : Int, hash (ofInt n) = intHash n

theorem hashMatchesInt_proven : HashMatchesInt := by
  intro n
  simp only [hash, ofInt, hashAlgorithm, modInv_one]
  rw [intHash_nat, show ((n.natAbs % hashModulus : Nat) : Int) * 1 =
    ((n.natAbs % hashModulus : Nat) : Int) by omega, intHash_nat, Nat.mod_mod]
  simp only [intHash]
  by_cases hn : n < 0
  · have : ¬ n ≥ 0 := by omega
    simp only [hn, this, ↓reduceIte]
  · have : n ≥ 0 := by omega
    simp only [hn, this, ↓reduceIte]

set_option maxRecDepth 100000 in
/-- `10 * _PyHASH_10INV ≡ 1 (mod P)`. -/
theorem ten_tenInv : (10 * tenInv) % hashModulus = 1 := by decide

theorem pow_ten_tenInv (k : Nat) : (10 ^ k * tenInv ^ k) % hashModulus = 1 := by
  rw [← Nat.mul_pow, Nat.pow_mod, ten_tenInv, Nat.one_pow]
  decide

/-- Inverses modulo `P` are unique. -/
theorem inv_unique {D x y : Nat} (hx : (D * x) % hashModulus = 1) (hy : (D * y) % hashModulus = 1) :
    x % hashModulus = y % hashModulus := by
  have e1 : x % hashModulus = (x * (D * y)) % hashModulus := by
    rw [Nat.mul_mod, hy, Nat.mul_one, Nat.mod_mod]
  have e2 : y % hashModulus = (y * (D * x)) % hashModulus := by
    rw [Nat.mul_mod, hx, Nat.mul_one, Nat.mod_mod]
  rw [e1, e2]; congr 1; grind

/-- The common sign tail of both hash functions. -/
theorem sign_finish (z h : Int) (neg : Bool) (c : Nat) (hz : z ≥ 0 ↔ ¬(neg = true ∧ c ≠ 0)) :
    (if (if z ≥ 0 then h else -h) = -1 then -2 else (if z ≥ 0 then h else -h)) =
    (if (if neg = true ∧ c ≠ 0 then -h else h) = -1 then -2
      else (if neg = true ∧ c ≠ 0 then -h else h)) := by
  by_cases hs : neg = true ∧ c ≠ 0
  · have : ¬ z ≥ 0 := fun h' => hz.mp h' hs
    rw [ite_eq_right this, ite_eq_left hs]
  · have := hz.mpr hs
    rw [ite_eq_left this, ite_eq_right hs]

/-- Built-in Types, "Hashing of numeric types": `hash(x) == hash(y)` whenever
`x == y`; here for a Fraction equal to a Decimal. For every finite Decimal
`(-1)**sign * coeff * 10**exp`, `hash(Fraction(d)) == hash(d)`. -/
def HashMatchesDecimal : Prop :=
  ∀ (neg : Bool) (coeff : Nat) (exp : Int), hash (ofDecimal neg coeff exp) = decimalHash neg coeff exp

theorem hashMatchesDecimal_proven : HashMatchesDecimal := by
  intro neg c e
  by_cases he : 0 ≤ e
  · -- integer-valued Decimal
    have hof : ofDecimal neg c e = ⟨(if neg then -(c : Int) else c) * 10 ^ e.toNat, 1⟩ := by
      simp only [ofDecimal, he, ↓reduceIte, Int.gcd_one, Int.natCast_one, Int.ediv_one]
    rw [hof]
    simp only [hash, hashAlgorithm, modInv_one, decimalHash, he, ↓reduceIte]
    have habs : ((if neg then -(c : Int) else c) * 10 ^ e.toNat).natAbs = c * 10 ^ e.toNat := by
      cases neg <;> simp [Int.natAbs_mul, Int.natAbs_pow]
    rw [habs, intHash_nat, show ((c * 10 ^ e.toNat % hashModulus : Nat) : Int) * 1 =
      ((c * 10 ^ e.toNat % hashModulus : Nat) : Int) by omega, intHash_nat, Nat.mod_mod,
      Nat.powMod_def, Nat.mul_mod_mod]
    have hsign : ((if neg then -(c : Int) else c) * 10 ^ e.toNat ≥ 0) ↔ ¬ (neg = true ∧ c ≠ 0) := by
      have hp : (0 : Int) < 10 ^ e.toNat := Int.pow_pos (by decide)
      cases neg
      · simp only [Bool.false_eq_true, ↓reduceIte, false_and, not_false_eq_true, iff_true]
        exact Int.mul_nonneg (by omega) (by omega)
      · simp only [↓reduceIte, true_and]
        constructor
        · intro h hc
          have : (0 : Int) < c := by omega
          have := Int.mul_neg_of_neg_of_pos (show -(c : Int) < 0 by omega) hp
          omega
        · intro h
          have : c = 0 := by omega
          subst this; simp
    exact sign_finish _ _ neg c hsign
  · -- `Decimal` with a negative exponent: `c / 10**k` reduced by `G`
    generalize hk : (-e).toNat = k
    have hd10 : ((10 : Int) ^ k) = ((10 ^ k : Nat) : Int) := by simp
    generalize hG : Nat.gcd c (10 ^ k) = G
    have hGpos : 0 < G := by rw [← hG]; exact Nat.gcd_pos_of_pos_right _ (Nat.pow_pos (by decide))
    obtain ⟨c', hc'⟩ : G ∣ c := hG ▸ Nat.gcd_dvd_left c (10 ^ k)
    obtain ⟨D', hD'⟩ : G ∣ 10 ^ k := hG ▸ Nat.gcd_dvd_right c (10 ^ k)
    have hD'pos : 0 < D' := by
      rcases Nat.eq_zero_or_pos D' with h | h
      · subst h; simp at hD'
      · exact h
    have hof : ofDecimal neg c e = ⟨if neg then -(c' : Int) else c', D'⟩ := by
      simp only [ofDecimal, he, ↓reduceIte, hk]
      have hg : Int.gcd (if neg then -(c : Int) else c) (10 ^ k) = G := by
        rw [← hG, hd10]; cases neg <;> simp [Int.gcd_eq_natAbs_gcd_natAbs]
      rw [hg, hd10, hc', hD']
      have hG0 : (G : Int) ≠ 0 := by omega
      cases neg
      · simp only [Bool.false_eq_true, ↓reduceIte, Int.natCast_mul]
        rw [Int.mul_ediv_cancel_left _ hG0, Int.mul_ediv_cancel_left _ hG0]
      · simp only [↓reduceIte, Int.natCast_mul]
        rw [Int.neg_ediv_of_dvd ⟨c', rfl⟩, Int.mul_ediv_cancel_left _ hG0,
          Int.mul_ediv_cancel_left _ hG0]
    rw [hof]
    -- the inverse of `D'`
    have hcop : Nat.gcd D' hashModulus = 1 := by
      have h10 : Nat.gcd (10 ^ k) hashModulus = 1 := Nat.Coprime.pow_left k (by decide)
      exact Nat.Coprime.coprime_dvd_left ⟨G, by rw [hD', Nat.mul_comm]⟩ h10
    obtain ⟨x, hx, hxP, hxinv⟩ := modInv_spec D' hcop
    have hmod : x % hashModulus = (G * tenInv ^ k) % hashModulus := by
      apply inv_unique hxinv
      rw [← Nat.mul_assoc, Nat.mul_comm D' G, ← hD']
      exact pow_ten_tenInv k
    have habs : (if neg then -(c' : Int) else c').natAbs = c' := by cases neg <;> simp
    simp only [hash, hashAlgorithm, hx, decimalHash, he, ↓reduceIte, hk, habs]
    rw [intHash_nat, show ((c' % hashModulus : Nat) : Int) * (x : Int) =
      (((c' % hashModulus) * x : Nat) : Int) by simp, intHash_nat, Nat.powMod_def,
      Nat.mod_mul_mod, Nat.mul_mod_mod]
    have hval : (c' * x) % hashModulus = (c * tenInv ^ k) % hashModulus := by
      rw [Nat.mul_mod, hmod, ← Nat.mul_mod, hc', Nat.mul_left_comm c' G, ← Nat.mul_assoc]
    rw [hval]
    have hsign : ((if neg then -(c' : Int) else c') ≥ 0) ↔ ¬ (neg = true ∧ c ≠ 0) := by
      cases neg
      · simp
      · simp only [↓reduceIte, true_and]
        constructor
        · intro h hc
          have : c' ≠ 0 := by intro h0; subst h0; simp at hc'; exact hc hc'
          omega
        · intro h
          have : c = 0 := by omega
          subst this
          have : c' = 0 := by
            rcases Nat.mul_eq_zero.mp hc'.symm with h | h
            · omega
            · exact h
          subst this; simp
    exact sign_finish _ _ neg c hsign

end PyLean.Fractions
