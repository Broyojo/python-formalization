import PyLean.CoreLibs.CalStat.StatQuant
import PyLean.Binary64.Lemmas

/-!
Facts about the exact float model `Flt` of this area, obtained by identifying its rounding step
`Flt.roundMag` with `roundPos` of `PyLean.Binary64`, whose correctness (`rounded_nearest`) is proven
there: `Flt.ofRat` rounds to nearest, so it returns every binary64 value unchanged.
-/

namespace PyLean.CoreLibs.CalStat

open PyLean
open PyLean.Binary64 (pw pw_pos pw_ne pw_natCast pw_neg pw_add Rep binary64 roundExp divPow2 roundInt
  floorLog2Q rounded_nearest natAbs_div_den abs_of_nonneg abs_of_nonpos)

theorem pow2_eq (e : Int) : Flt.pow2 e = pw e := by
  unfold Flt.pow2
  split
  · rename_i h
    have : e = ((e.toNat : Nat) : Int) := by omega
    conv => rhs; rw [this]
    rw [pw_natCast]
  · rename_i h
    have : e = -(((-e).toNat : Nat) : Int) := by omega
    conv => rhs; rw [this]
    rw [pw_neg, pw_natCast, Rat.mkRat_eq_div]
    simp [Rat.div_def]

theorem floorLog2_eq (n d : Nat) : Flt.floorLog2 n d = floorLog2Q n d := by
  unfold Flt.floorLog2 floorLog2Q
  simp only
  generalize (Nat.log2 n : Int) - (Nat.log2 d : Int) = l
  by_cases h : 0 ≤ l
  · have h1 : (-l).toNat = 0 := by omega
    simp only [h, ite_true, h1, Nat.pow_zero, Nat.mul_one]
    by_cases c : d * 2 ^ l.toNat ≤ n <;> simp [c]
  · have h1 : l.toNat = 0 := by omega
    simp only [h, ite_false, h1, Nat.pow_zero, Nat.mul_one]
    by_cases c : d ≤ n * 2 ^ (-l).toNat <;> simp [c]

theorem roundDiv_eq (a b : Nat) : Flt.roundDiv a b = roundInt (a / b) (a % b) b := by
  unfold Flt.roundDiv roundInt
  simp only
  by_cases h1 : b < 2 * (a % b)
  · have : 2 * (a % b) > b := h1
    simp [h1, this]
  · by_cases h2 : 2 * (a % b) = b
    · by_cases h3 : (a / b) % 2 = 1
      · simp [h1, h2, h3]
      · simp [h1, h2, h3]
    · have : ¬ (2 * (a % b) > b) := h1
      simp [h1, h2, this]

/-- `Flt.roundMag` is the rounding step of `Binary64.roundPos` (before its renormalisation of a
carry into the next binade, which does not change the value). -/
theorem roundMag_eq (n d : Nat) :
    Flt.roundMag n d = (roundInt (divPow2 n d (roundExp binary64 n d)).1 (divPow2 n d (roundExp binary64 n d)).2.1
      (divPow2 n d (roundExp binary64 n d)).2.2, roundExp binary64 n d) := by
  unfold Flt.roundMag roundExp
  rw [floorLog2_eq]
  have hp : ((binary64.p - 1 : Nat) : Int) = 52 := by decide
  have he : binary64.etiny = -1074 := by decide
  rw [hp, he]
  simp only [divPow2]
  split
  · rename_i h
    have h1 : (-(max (floorLog2Q n d - 52) (-1074))).toNat = 0 := by omega
    simp only [h1, Nat.pow_zero, Nat.mul_one, roundDiv_eq]
  · rename_i h
    have h1 : (max (floorLog2Q n d - 52) (-1074)).toNat = 0 := by omega
    simp only [h1, Nat.pow_zero, Nat.mul_one, roundDiv_eq]

/-- `Flt.ofRat` rounds to nearest: the magnitude it produces is at least as close to `|q|` as any
binary64 number. -/
theorem roundMag_nearest {q : Rat} (hq : q ≠ 0) {y : Rat} (hy : Rep binary64 y) :
    Rat.abs ((if q < 0 then -q else q) - ((Flt.roundMag q.num.natAbs q.den).1 : Rat) *
      Flt.pow2 (Flt.roundMag q.num.natAbs q.den).2) ≤ Rat.abs ((if q < 0 then -q else q) - y) := by
  obtain ⟨hn, hd, hv⟩ := natAbs_div_den hq
  rw [roundMag_eq, pow2_eq, ← hv]
  exact rounded_nearest binary64 (by decide) hn hd hy

theorem abs_eq_zero {a : Rat} (h : Rat.abs a ≤ 0) : a = 0 := by
  unfold Rat.abs at h
  split at h <;> grind

/-- A binary64 value below the overflow threshold is returned unchanged by `Flt.ofRat`. -/
theorem ofRat_exact {q : Rat} (hq : q ≠ 0) (hrep : Rep binary64 q) (hlt : Rat.abs q < Flt.pow2 1024) :
    Flt.ofRat q = .fin q := by
  have hrepa : Rep binary64 (if q < 0 then -q else q) := by
    obtain ⟨M, E, hM, hE, h⟩ := hrep
    refine ⟨M, E, hM, hE, ?_⟩
    split
    · rcases h with h | h
      · right; rw [h]
      · left; rw [h, Rat.neg_neg]
    · exact h
  have hnear := roundMag_nearest hq hrepa
  rw [Rat.sub_self, abs_of_nonneg (a := 0) (by decide)] at hnear
  have hv := abs_eq_zero hnear
  unfold Flt.ofRat
  rw [if_neg hq]
  simp only
  generalize hRM : Flt.roundMag q.num.natAbs q.den = RM at hv
  obtain ⟨m, e⟩ := RM
  simp only at hv ⊢
  have hval : (m : Rat) * Flt.pow2 e = (if q < 0 then -q else q) := by grind
  have hnz : (if q < 0 then -q else q) ≠ 0 := by split <;> grind
  have hm : m ≠ 0 := by
    intro h0
    rw [h0] at hval
    apply hnz
    rw [← hval]
    simp
  rw [if_neg hm, hval]
  have habs : (if q < 0 then -q else q) = Rat.abs q := by
    unfold Rat.abs; split <;> split <;> grind
  rw [habs, if_neg (Rat.not_le.mpr hlt)]
  congr 1
  unfold Rat.abs
  by_cases hneg : q < 0
  · simp only [hneg, decide_true, ite_true]
    split <;> grind
  · simp only [hneg, decide_false]
    split <;> grind

/-- `Flt.ofRat` commutes with negation (an exact zero gives `+0.0` either way). -/
theorem ofRat_neg (q : Rat) (hq : q ≠ 0) : Flt.ofRat (-q) = Flt.neg (Flt.ofRat q) := by
  · have hq' : -q ≠ 0 := by intro h; apply hq; grind
    have hnum : (-q).num.natAbs = q.num.natAbs := by simp
    have hden : (-q).den = q.den := by simp
    unfold Flt.ofRat
    rw [if_neg hq', if_neg hq, hnum, hden]
    have hd : decide (-q < 0) = !decide (q < 0) := by
      by_cases h : q < 0
      · have : ¬ (-q < 0) := by grind
        simp [h, this]
      · have : -q < 0 := by grind
        simp [h, this]
    rw [hd]
    generalize Flt.roundMag q.num.natAbs q.den = RM
    obtain ⟨m, e⟩ := RM
    simp only
    split
    · simp [Flt.neg]
    · split
      · simp [Flt.neg]
      · cases decide (q < 0) <;> simp [Flt.neg]

/-- A non-zero integer below `2**53` in magnitude is a binary64 value. -/
theorem rep_int (i : Int) (h : i.natAbs < 2 ^ 53) : Rep binary64 (i : Rat) := by
  refine ⟨i.natAbs, 0, h, by decide, ?_⟩
  have hp : pw 0 = 1 := by simp [pw]
  rw [hp, Rat.mul_one]
  rcases Int.natAbs_eq i with h1 | h1
  · left; conv => lhs; rw [h1]
    exact Rat.intCast_natCast _
  · right; conv => lhs; rw [h1]
    rw [Rat.intCast_neg, Rat.intCast_natCast]

theorem ofRat_int (i : Int) (h0 : i ≠ 0) (h : i.natAbs < 2 ^ 53) : Flt.ofRat (i : Rat) = .fin (i : Rat) := by
  apply ofRat_exact (by simpa using h0) (rep_int i h)
  have : Rat.abs (i : Rat) = ((i.natAbs : Nat) : Rat) := by
    have hx : (0 : Rat) ≤ ((i.natAbs : Nat) : Rat) := Rat.natCast_nonneg
    rcases Int.natAbs_eq i with h1 | h1
    · conv => lhs; rw [h1]
      rw [Rat.intCast_natCast, abs_of_nonneg hx]
    · conv => lhs; rw [h1]
      rw [Rat.intCast_neg, Rat.intCast_natCast, abs_of_nonpos (by grind), Rat.neg_neg]
  have e2 : pw (53 : Int) = ((2 ^ 53 : Nat) : Rat) := pw_natCast 53
  have h53 : ((i.natAbs : Nat) : Rat) < pw 53 := by
    rw [e2]; exact Rat.natCast_lt_natCast.mpr h
  rw [this, pow2_eq]
  have h2 := PyLean.Binary64.pw_le (show (53 : Int) ≤ 1024 by decide)
  grind

end PyLean.CoreLibs.CalStat
