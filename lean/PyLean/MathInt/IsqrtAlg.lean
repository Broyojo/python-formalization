/-!
Integer inequalities behind the correctness of `math.isqrt`
(mathmodule.c:1494-1636, "Sketch of proof of correctness"), stated without
square roots.
-/

namespace PyLean.MathInt

/-- `a` approximates `√m` to within 1: `(a-1)^2 < m < (a+1)^2`. -/
def Approx (a m : Nat) : Prop := (a - 1) * (a - 1) < m ∧ m < (a + 1) * (a + 1)

theorem sq_nonneg' (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (show 0 ≤ -a by omega) (show 0 ≤ -a by omega)
    have e : -a * -a = a * a := by grind
    omega

/-- One Newton step on integers. With `x = 2H = a*P` (`P = 2^k`, `k >= 1`), the
hypotheses are the loop invariant `(a-1)^2 < m >> 2k < (a+1)^2` (as
`h1`, `h2`) and `2^(k-1) <= a` (`h3`); the result is `b = H + m // 2x`. -/
theorem newton_int (H P M Q R : Int) (hP : 1 ≤ P) (hX : P ≤ (2 * H))
    (h1 : ((2 * H) - P) * ((2 * H) - P) + P * P ≤ M) (h2 : M < ((2 * H) + P) * ((2 * H) + P))
    (h3 : P * P ≤ 2 * (2 * H))
    (hM : M = 2 * (2 * H) * Q + R) (hR0 : 0 ≤ R) (hR1 : R < 2 * (2 * H)) (hQ : 0 ≤ Q) :
    (H + Q - 1) * (H + Q - 1) < M ∧ M < (H + Q + 1) * (H + Q + 1) := by
  have hX0 : 0 < (2 * H) := by omega
  constructor
  · -- lower bound
    generalize hS : H + Q - 1 = S
    have F1 : 2 * (2 * H) * (S + 1) ≤ (2 * H) * (2 * H) + M := by rw [← hS]; grind
    refine Classical.byContradiction fun hc => ?_
    have hc : M ≤ S * S := by omega
    have hT : P * P ≤ (S - (2 * H)) * (S - (2 * H)) := by grind
    by_cases hSX : (2 * H) ≤ S
    · have hTP : P ≤ S - (2 * H) := by
        refine Classical.byContradiction fun h => ?_
        have := Int.mul_self_lt_mul_self (show 0 ≤ S - (2 * H) by omega)
          (show S - (2 * H) < P by omega)
        omega
      have e : 2 * (2 * H) * (S + 1) < 2 * (2 * H) * ((2 * H) + P + 1) := by grind
      have := Int.lt_of_mul_lt_mul_left e (by omega)
      omega
    · have hTP : P ≤ (2 * H) - S := by
        refine Classical.byContradiction fun h => ?_
        have := Int.mul_self_lt_mul_self (show 0 ≤ (2 * H) - S by omega)
          (show (2 * H) - S < P by omega)
        have e : ((2 * H) - S) * ((2 * H) - S) = (S - (2 * H)) * (S - (2 * H)) := by grind
        omega
      by_cases hS0 : 0 ≤ S
      · have := Int.mul_self_le_mul_self hS0 (show S ≤ (2 * H) - P by omega)
        have : 0 < P * P := Int.mul_pos (by omega) (by omega)
        omega
      · have hS1 : S = -1 := by
          have : 1 ≤ H := by
            refine Classical.byContradiction fun h => ?_
            omega
          omega
        subst hS1
        have : 0 < P * P := Int.mul_pos (by omega) (by omega)
        have h0 : 0 ≤ ((2 * H) - P) * ((2 * H) - P) := sq_nonneg' _
        omega
  · -- upper bound
    generalize hB : H + Q + 1 = B
    have F : (2 * H) * (2 * H) + M < 2 * (2 * H) * B := by rw [← hB]; grind
    have hsq : 4 * ((2 * H) * (2 * H)) * M ≤ ((2 * H) * (2 * H) + M) * ((2 * H) * (2 * H) + M) := by
      have := sq_nonneg' ((2 * H) * (2 * H) - M); grind
    have hlt : ((2 * H) * (2 * H) + M) * ((2 * H) * (2 * H) + M) <
        (2 * (2 * H) * B) * (2 * (2 * H) * B) :=
      Int.mul_self_lt_mul_self (by
        have := sq_nonneg' (2 * H); have := sq_nonneg' (2 * H - P); have := sq_nonneg' P
        omega) F
    refine Classical.byContradiction fun hc => ?_
    have hc : B * B ≤ M := by omega
    have : 4 * ((2 * H) * (2 * H)) * (B * B) ≤ 4 * ((2 * H) * (2 * H)) * M :=
      Int.mul_le_mul_of_nonneg_left hc (by have := sq_nonneg' (2 * H); omega)
    grind

theorem two_pow_two_mul (k : Nat) : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by
  rw [Nat.two_mul, Nat.pow_add]

theorem approx_pos {a m : Nat} (h : Approx a m) : 1 ≤ a := by
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · subst h0; have := h.1; have := h.2; simp at *; omega
  · exact h0

/-- One iteration of the Newton loop: `b = (a << k-1) + (m >> k+1) // a`
(mathmodule.c:1531-1547, :1772-1789). -/
theorem newton_step (m a k : Nat) (hk : 1 ≤ k) (hA : Approx a (m >>> (2 * k)))
    (h3 : 2 ^ (k - 1) ≤ a) : Approx ((a <<< (k - 1)) + (m >>> (k + 1)) / a) m := by
  have ha := approx_pos hA
  obtain ⟨hA1, hA2⟩ := hA
  rw [Nat.shiftRight_eq_div_pow, two_pow_two_mul] at hA1 hA2
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
  generalize hp : 2 ^ (k - 1) = p at *
  have hP : 2 ^ k = 2 * p := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [← hp, Nat.add_sub_cancel, Nat.pow_succ]; omega
  rw [hP] at hA1 hA2
  rw [show 2 ^ (k + 1) = 2 * (2 * p) by rw [Nat.pow_succ, hP]; omega]
  have hp1 : 1 ≤ p := by rw [← hp]; exact Nat.one_le_two_pow
  have n1 : (2 * p) * (2 * p) * ((a - 1) * (a - 1) + 1) ≤ m := by
    have := (Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) (by omega))).mp (Nat.succ_le_of_lt hA1)
    rw [Nat.mul_comm]; exact this
  have n2 : m < (a + 1) * (a + 1) * ((2 * p) * (2 * p)) :=
    (Nat.div_lt_iff_lt_mul (Nat.mul_pos (by omega) (by omega))).mp hA2
  have eQ := Nat.div_add_mod m (2 * (2 * p) * a)
  have eR := Nat.mod_lt m (show 0 < 2 * (2 * p) * a from Nat.mul_pos (by omega) (by omega))
  generalize m / (2 * (2 * p) * a) = Q at *
  generalize m % (2 * (2 * p) * a) = R at *
  have key := newton_int ((a * p : Nat) : Int) ((2 * p : Nat) : Int) (m : Int) (Q : Int) (R : Int)
    (by push_cast; omega) (by push_cast; have := Nat.mul_le_mul_right p ha; push_cast at this; grind)
    (by
      have : ((2 * p * (2 * p) * ((a - 1) * (a - 1) + 1) : Nat) : Int) ≤ m := by exact_mod_cast n1
      push_cast [Int.ofNat_sub ha] at this; grind)
    (by
      have : (m : Int) < (((a + 1) * (a + 1) * ((2 * p) * (2 * p)) : Nat) : Int) := by
        exact_mod_cast n2
      push_cast at this; grind)
    (by have := Nat.mul_le_mul_left (2 * p) (show 2 * p ≤ 2 * a by omega); push_cast; grind)
    (by have : ((m : Nat) : Int) = ((2 * (2 * p) * a * Q + R : Nat) : Int) := by rw [eQ]
        push_cast at this; grind)
    (by omega) (by push_cast; grind) (by omega)
  have hHQ : 1 ≤ a * p + Q := by have := Nat.mul_le_mul ha hp1; omega
  obtain ⟨k1, k2⟩ := key
  constructor
  · have : (((a * p + Q - 1) * (a * p + Q - 1) : Nat) : Int) < (m : Int) := by
      push_cast [Int.ofNat_sub hHQ]; push_cast at k1; exact k1
    exact_mod_cast (by rw [Nat.mul_comm a p] at this ⊢; exact_mod_cast this)
  · have : (m : Int) < (((a * p + Q + 1) * (a * p + Q + 1) : Nat) : Int) := by
      push_cast; push_cast at k2; exact k2
    exact_mod_cast (by rw [Nat.mul_comm a p] at this ⊢; exact_mod_cast this)

/-- Scaling an approximation down: if `a ≈ √M` then `a >> s ≈ √(M >> 2s)`, provided
`a >> s >= 2` (or `M` is an exact multiple of `4^s` and `a >> s >= 1`).
Used where `_approximate_isqrt`'s result is shifted (mathmodule.c:1733, :1758). -/
theorem approx_shift (A M s : Nat) (hA : Approx A M)
    (hc : 2 ≤ A / 2 ^ s ∨ (M % (2 ^ s * 2 ^ s) = 0 ∧ 1 ≤ A / 2 ^ s)) :
    Approx (A >>> s) (M >>> (2 * s)) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, two_pow_two_mul]
  generalize hP : 2 ^ s = P at *
  have hP1 : 1 ≤ P := by rw [← hP]; exact Nat.one_le_two_pow
  obtain ⟨hA1, hA2⟩ := hA
  have e := Nat.div_add_mod A P
  have em := Nat.mod_lt A (show 0 < P by omega)
  generalize A / P = u at *
  generalize A % P = v at *
  have hu1 : 1 ≤ u := by omega
  constructor
  · -- lower bound
    apply Nat.lt_of_succ_le
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) (by omega))).mpr
    refine Classical.byContradiction fun hcon => ?_
    have hcon : M < (u - 1) * (u - 1) * (P * P) + P * P := by
      rw [Nat.succ_mul] at hcon; omega
    have hPu : (P * u - 1) * (P * u - 1) ≤ (A - 1) * (A - 1) :=
      Nat.mul_self_le_mul_self (by omega)
    have hlt : (P * u - 1) * (P * u - 1) < (u - 1) * (u - 1) * (P * P) + P * P := by omega
    rcases hc with hc | ⟨hc, _⟩
    · -- floor case, u ≥ 2
      have hP2 : 2 ≤ P ∨ P = 1 := by omega
      rcases hP2 with hP2 | hP2
      · have hI : (((P * u - 1) * (P * u - 1) : Nat) : Int) <
            (((u - 1) * (u - 1) * (P * P) + P * P : Nat) : Int) := by exact_mod_cast hlt
        push_cast [Int.ofNat_sub (show 1 ≤ P * u by have := Nat.mul_le_mul hP1 hu1; omega),
          Int.ofNat_sub hu1] at hI
        have f1 : (0 : Int) ≤ ((u : Int) - 2) * ((P : Int) * ((P : Int) - 1)) :=
          Int.mul_nonneg (by omega) (Int.mul_nonneg (by omega) (by omega))
        have f2 : (0 : Int) ≤ ((P : Int) - 2) * (P : Int) := Int.mul_nonneg (by omega) (by omega)
        grind
      · subst hP2
        have hu : u = A := by omega
        subst hu
        simp only [Nat.mul_one, Nat.one_mul] at hcon
        omega
    · -- exact case: M = P*P*m
      have hm := Nat.div_add_mod M (P * P)
      rw [hc, Nat.add_zero] at hm
      generalize M / (P * P) = m at *
      have hb : (A - 1) * (A - 1) < P * P * m := by rw [hm]; exact hA1
      have hmu : m ≤ (u - 1) * (u - 1) := by
        refine Classical.byContradiction fun h => ?_
        have := Nat.mul_le_mul_left (P * P) (show (u - 1) * (u - 1) + 1 ≤ m by omega)
        rw [Nat.mul_add, Nat.mul_one] at this
        rw [Nat.mul_comm ((u - 1) * (u - 1))] at hcon
        omega
      have h3 := Nat.mul_le_mul_left (P * P) hmu
      have e2 : P * P * ((u - 1) * (u - 1)) = (P * (u - 1)) * (P * (u - 1)) := by
        simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have h1 : (P * u - 1) * (P * u - 1) < (P * (u - 1)) * (P * (u - 1)) := by omega
      have := Nat.mul_self_lt_mul_self_iff.mp h1
      have : P * (u - 1) = P * u - P := by rw [Nat.mul_sub, Nat.mul_one]
      have : P ≤ P * u := Nat.le_mul_of_pos_right _ (by omega)
      omega
  · -- upper bound
    apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos (by omega) (by omega))).mpr
    have h1 : A + 1 ≤ P * (u + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    have h2 := Nat.mul_self_le_mul_self h1
    have e2 : P * (u + 1) * (P * (u + 1)) = (u + 1) * (u + 1) * (P * P) := by
      simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    omega

/-- The final check-and-correct step, mathmodule.c:1793-1813 and :1734. -/
theorem approx_correct (a n : Nat) (h : Approx a n) :
    let r := if n < a * a then a - 1 else a
    r * r ≤ n ∧ n < (r + 1) * (r + 1) := by
  obtain ⟨h1, h2⟩ := h
  have ha := approx_pos ⟨h1, h2⟩
  by_cases hc : n < a * a
  · simp only [hc, ite_true]
    rw [Nat.sub_add_cancel ha]; exact ⟨by omega, hc⟩
  · simp only [hc, ite_false]; exact ⟨by omega, h2⟩

end PyLean.MathInt
