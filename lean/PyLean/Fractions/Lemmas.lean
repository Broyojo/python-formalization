import PyLean.Fractions.Model

/-!
Arithmetic helper lemmas shared by the `fractions` proofs.
-/

namespace PyLean.Fractions

open PyLean

theorem pyDiv_of_dvd {a b : Int} (h : b ∣ a) : pyDiv a b = a / b := Int.fdiv_eq_ediv_of_dvd h

theorem pyDiv_of_nonneg (a : Int) {b : Int} (hb : 0 ≤ b) : pyDiv a b = a / b :=
  Int.fdiv_eq_ediv_of_nonneg a hb

theorem pyMod_of_nonneg (a : Int) {b : Int} (hb : 0 ≤ b) : pyMod a b = a % b :=
  Int.fmod_eq_emod_of_nonneg a hb

/-- `x ≤ y`, `0 ≤ z` gives `x * z ≤ y * z`. -/
theorem mul_le_mul_r {x y z : Int} (h : x ≤ y) (hz : 0 ≤ z) : x * z ≤ y * z := by
  have := Int.mul_nonneg (Int.sub_nonneg.mpr h) hz
  have e : (y - x) * z = y * z - x * z := by grind
  omega

theorem mul_lt_mul_r {x y z : Int} (h : x < y) (hz : 0 < z) : x * z < y * z := by
  have := Int.mul_pos (Int.sub_pos.mpr h) hz
  have e : (y - x) * z = y * z - x * z := by grind
  omega

theorem le_of_mul_le_mul_r {x y z : Int} (h : x * z ≤ y * z) (hz : 0 < z) : x ≤ y :=
  Int.le_of_mul_le_mul_right h hz

theorem lt_of_mul_lt_mul_r {x y z : Int} (h : x * z < y * z) (hz : 0 < z) : x < y := by
  apply Int.lt_of_not_ge
  intro hc
  have := mul_le_mul_r hc (Int.le_of_lt hz)
  omega

theorem pos_mul_pos {x y : Int} (hx : 0 < x) (hy : 0 < y) : 0 < x * y := Int.mul_pos hx hy

/-- The gcd of the two cofactors after dividing out the gcd is one. -/
theorem gcd_cofactors {n d : Int} (hd : d ≠ 0) :
    ∃ a b : Int, n = (Int.gcd n d : Int) * a ∧ d = (Int.gcd n d : Int) * b ∧ Int.gcd a b = 1 ∧
      0 < (Int.gcd n d : Int) := by
  have hg : 0 < Int.gcd n d := Int.gcd_pos_of_ne_zero_right n hd
  obtain ⟨a, ha⟩ := Int.gcd_dvd_left n d
  obtain ⟨b, hb⟩ := Int.gcd_dvd_right n d
  refine ⟨a, b, ha, hb, ?_, by omega⟩
  have h1 : Int.gcd ((Int.gcd n d : Int) * a) ((Int.gcd n d : Int) * b) = Int.gcd n d := by
    rw [← ha, ← hb]
  rw [Int.gcd_mul_left] at h1
  simp only [Int.natAbs_natCast] at h1
  have : Int.gcd n d * Int.gcd a b = Int.gcd n d * 1 := by omega
  exact Nat.eq_of_mul_eq_mul_left hg this

theorem gcd_one_of_dvd {x y X Y : Int} (hx : x ∣ X) (hy : y ∣ Y) (h : Int.gcd X Y = 1) :
    Int.gcd x y = 1 := by
  have h1 := Int.gcd_dvd_gcd_of_dvd_left Y hx
  have h2 := Int.gcd_dvd_gcd_of_dvd_right x hy
  rw [h] at h1
  exact Nat.dvd_one.mp (Nat.dvd_trans h2 h1)

theorem gcd_mul_one {x a b : Int} (ha : Int.gcd x a = 1) (hb : Int.gcd x b = 1) :
    Int.gcd x (a * b) = 1 := by
  rw [Int.gcd_mul_right_right_of_gcd_eq_one ha]; exact hb

theorem gcd_one_comm {x y : Int} (h : Int.gcd x y = 1) : Int.gcd y x = 1 := by
  rw [Int.gcd_comm]; exact h

theorem dvd_of_dvd_mul_coprime {k m n : Int} (h : Int.gcd k m = 1) (hd : k ∣ m * n) : k ∣ n := by
  rw [← Int.natAbs_dvd_natAbs] at hd ⊢
  rw [Int.natAbs_mul] at hd
  exact Nat.Coprime.dvd_of_dvd_mul_left h hd

theorem dvd_of_eq_mul_left {X G y : Int} (h : X = G * y) : y ∣ X := ⟨G, by rw [h, Int.mul_comm]⟩

theorem dvd_of_eq_mul_right {X G y : Int} (h : X = G * y) : G ∣ X := ⟨y, h⟩

theorem pos_of_mul_pos_left {G b : Int} (hG : 0 < G) (h : 0 < G * b) : 0 < b := by
  rcases Int.lt_trichotomy b 0 with hb | hb | hb
  · have := Int.mul_neg_of_pos_of_neg hG hb; omega
  · subst hb; simp at h
  · exact hb

end PyLean.Fractions
