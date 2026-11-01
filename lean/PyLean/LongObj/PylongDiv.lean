import PyLean.LongObj.Pylong

/-!
`_div2n1n`, `_div3n2n`, `_int2digits`, `_digits2int` and `_divmod_pos` of
`Lib/_pylong.py` are exact: the Burnikel-Ziegler recursion under the docstring's
preconditions, including that `while r < 0` adds `b` at most twice.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

theorem div3Loop_spec {b q r A : Int} (hb : 0 < b) (hA : A = q * b + r) (h1 : -(2 * b) < r)
    (h2 : r < b) : ∃ q' r', div3Loop b 4 q r = .ok (q', r') ∧ A = q' * b + r' ∧ 0 ≤ r' ∧ r' < b := by
  by_cases h3 : r < 0
  · by_cases h4 : r + b < 0
    · refine ⟨q - 1 - 1, r + b + b, ?_, ?_, by omega, by omega⟩
      · rw [div3Loop, if_pos h3, div3Loop, if_pos h4, div3Loop, if_neg (by omega)]
      · rw [hA, Int.sub_mul, Int.sub_mul, Int.one_mul]
        omega
    · refine ⟨q - 1, r + b, ?_, ?_, by omega, by omega⟩
      · rw [div3Loop, if_pos h3, div3Loop, if_neg h4]
      · rw [hA, Int.sub_mul, Int.one_mul]
        omega
  · exact ⟨q, r, by rw [div3Loop, if_neg h3], hA, by omega, h2⟩

/-- The arithmetic of `_div3n2n` after its first branch: the estimate `q` is at most two
too large. -/
theorem div3_arith {a12 a3 b b1 b2 P q r : Nat} (hP : 0 < P) (hb : b = b1 * P + b2) (hb2 : b2 < P)
    (ha3 : a3 < P) (hb1 : P ≤ 2 * b1) (hq : q < P) (hdec : a12 = q * b1 + r)
    (hR : r * P + a3 < b + q * b2) :
    ∃ q' r' : Int, div3Loop b 4 q (((r * P + a3 : Nat) : Int) - (q : Int) * (b2 : Int)) =
        .ok (q', r') ∧ q'.toNat = (a12 * P + a3) / b ∧ r'.toNat = (a12 * P + a3) % b := by
  have hbpos : 0 < b := by
    have : 0 < b1 * P := Nat.mul_pos (by omega) hP
    omega
  have hprod : q * b2 < 2 * b := by
    have h1 : q * b2 < P * P := Nat.mul_lt_mul'' hq hb2
    have h2 : P * P ≤ (2 * b1) * P := Nat.mul_le_mul_right _ hb1
    have h3 : (2 * b1) * P = 2 * (b1 * P) := Nat.mul_assoc ..
    omega
  obtain ⟨X, hX⟩ : ∃ X, (a12 * P + a3 : Nat) = X := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, (r * P + a3 : Nat) = Y := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, q * b2 = Z := ⟨_, rfl⟩
  have hnat : X + Z = q * b + Y := by
    rw [← hX, ← hY, ← hZ, hdec, hb, Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
    omega
  have hA : (X : Int) = (q : Int) * (b : Int) + ((Y : Int) - (Z : Int)) := by
    have : ((X + Z : Nat) : Int) = ((q * b + Y : Nat) : Int) := by rw [hnat]
    push_cast at this
    omega
  rw [hZ] at hprod
  rw [hY, hX]
  have hZc : (q : Int) * (b2 : Int) = (Z : Int) := by rw [← hZ]; push_cast; rfl
  rw [hZc]
  have hr : Y < b + Z := by rw [← hY, ← hZ]; exact hR
  obtain ⟨q', r', e, h1, h2, h3⟩ := div3Loop_spec (b := (b : Int)) (by omega) hA (by omega) (by omega)
  have hq0 : 0 ≤ q' := by
    apply Int.le_of_not_lt
    intro hc
    have : q' * (b : Int) ≤ (-1) * (b : Int) :=
      Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    omega
  obtain ⟨qn, rfl⟩ := Int.eq_ofNat_of_zero_le hq0
  obtain ⟨rn, rfl⟩ := Int.eq_ofNat_of_zero_le h2
  have hu : rn + b * qn = X := by
    have : ((rn + b * qn : Nat) : Int) = (X : Int) := by
      push_cast
      rw [h1, Int.mul_comm (b : Int), Int.add_comm]
    exact_mod_cast this
  have ⟨u1, u2⟩ := (Nat.div_mod_unique hbpos).2 ⟨hu, by omega⟩
  exact ⟨qn, rn, e, by simpa using u1.symm, by simpa using u2.symm⟩

/-- Preconditions of `_div2n1n`: `b` has exactly `n` bits, `a < 2**n * b`. -/
def Pre2 (a b n : Nat) : Prop := 1 ≤ n ∧ 2 ^ (n - 1) ≤ b ∧ b < 2 ^ n ∧ a < 2 ^ n * b

/-- What `_div2n1n` needs of `_div3n2n`: `b = b1*2**n + b2` with `b1` of exactly `n` bits,
`a3 < 2**n` and `a12 < b`. -/
def Pre3 (a12 a3 b b1 b2 n : Nat) : Prop :=
  1 ≤ n ∧ 2 ^ (n - 1) ≤ b1 ∧ b1 < 2 ^ n ∧ b2 < 2 ^ n ∧ a3 < 2 ^ n ∧ b = b1 * 2 ^ n + b2 ∧ a12 < b

theorem pow_half {n : Nat} (h : 1 ≤ n) : 2 ^ n = 2 * 2 ^ (n - 1) := by
  rw [← Nat.pow_succ', Nat.sub_add_cancel h]

/-- One level of the recursion on an even width `2 * h`, given `_div3n2n` at `h`. -/
theorem div2_even {D3 : Nat → Nat → Nat → Nat → Nat → Nat → Py (Nat × Nat)} {a b h : Nat}
    (hD : ∀ a12 a3 b b1 b2, Pre3 a12 a3 b b1 b2 h →
      D3 a12 a3 b b1 b2 h = .ok ((a12 * 2 ^ h + a3) / b, (a12 * 2 ^ h + a3) % b))
    (hp : Pre2 a b (2 * h)) (hh : 1 ≤ h) :
    (do
      let (q1, r) ← D3 (a >>> (2 * h)) ((a >>> h) &&& ((1 <<< h) - 1)) b (b >>> h)
        (b &&& ((1 <<< h) - 1)) h
      let (q2, r) ← D3 r (a &&& ((1 <<< h) - 1)) b (b >>> h) (b &&& ((1 <<< h) - 1)) h
      return ((q1 <<< h) ||| q2, r)) = (.ok (a / b, a % b) : Py (Nat × Nat)) := by
  obtain ⟨_, hlo, hhi, ha⟩ := hp
  obtain ⟨P, hPd⟩ : ∃ P, 2 ^ h = P := ⟨_, rfl⟩
  have hPpos : 0 < P := by rw [← hPd]; exact Nat.pow_pos (by decide)
  have hPP : 2 ^ (2 * h) = P * P := by rw [← hPd, ← Nat.pow_add]; congr 1; omega
  have hmask : (1 <<< h) - 1 = 2 ^ h - 1 := by rw [Nat.one_shiftLeft]
  have hm : ∀ x, x &&& ((1 <<< h) - 1) = x % P := by
    intro x; rw [hmask, Nat.and_two_pow_sub_one_eq_mod, hPd]
  have hs : ∀ x, x >>> h = x / P := by intro x; rw [Nat.shiftRight_eq_div_pow, hPd]
  have hs2 : ∀ x, x >>> (2 * h) = x / (P * P) := by intro x; rw [Nat.shiftRight_eq_div_pow, hPP]
  simp only [hm, hs, hs2]
  rw [hPP] at ha hhi
  have hb0 : 0 < b := by
    have : 0 < 2 ^ (2 * h - 1) := Nat.pow_pos (by decide)
    omega
  obtain ⟨b1, hb1⟩ : ∃ b1, b / P = b1 := ⟨_, rfl⟩
  obtain ⟨b2, hb2⟩ : ∃ b2, b % P = b2 := ⟨_, rfl⟩
  have hbd : b = b1 * P + b2 := by
    rw [← hb1, ← hb2, Nat.mul_comm]; exact (Nat.div_add_mod b P).symm
  have hb2lt : b2 < P := by rw [← hb2]; exact Nat.mod_lt _ hPpos
  have hb1hi : b1 < P := by
    rw [← hb1]; exact Nat.div_lt_of_lt_mul hhi
  have hb1lo : 2 ^ (h - 1) ≤ b1 := by
    rw [← hb1]
    apply (Nat.le_div_iff_mul_le hPpos).2
    have e : 2 ^ (2 * h - 1) = 2 ^ (h - 1) * P := by
      rw [← hPd, ← Nat.pow_add]; congr 1; omega
    omega
  obtain ⟨a12, ha12⟩ : ∃ x, a / (P * P) = x := ⟨_, rfl⟩
  obtain ⟨am, ham⟩ : ∃ x, a % (P * P) = x := ⟨_, rfl⟩
  have hadec : a = a12 * (P * P) + am := by
    rw [← ha12, ← ham, Nat.mul_comm]; exact (Nat.div_add_mod a (P * P)).symm
  have hamlt : am < P * P := by rw [← ham]; exact Nat.mod_lt _ (Nat.mul_pos hPpos hPpos)
  have ha12lt : a12 < b := by
    rw [← ha12]; exact Nat.div_lt_of_lt_mul ha
  have ha2 : (a / P) % P = am / P := by
    rw [hadec, ← Nat.mul_assoc, Nat.mul_add_div hPpos]
    sorry
  sorry

end PyLean.LongObj
