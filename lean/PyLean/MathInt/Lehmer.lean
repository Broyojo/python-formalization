import PyLean.MathInt.LehmerStep
import PyLean.MathInt.Gcd
import PyLean.MathInt.ToBytes

/-!
Correctness of `_PyLong_GCD` (longobject.c:5647-5851), including Lehmer's
step: the inner loop never overflows `int64_t`, the cofactors it accepts are
the true Euclidean cofactors of `(a, b)`, so the digit loop's results are two
consecutive nonnegative remainders below `2^(30*size_a)`, and `b` strictly
decreases.
-/

namespace PyLean.MathInt

open PyLean

/-- Invariant of Lehmer's inner loop (see `LehmerStep.lean`). -/
def LInv (M a b : Int) (st : LehmerState) (xp yp ap bp : Int) : Prop :=
  st.x = st.A * xp - st.B * yp ∧ st.y = st.D * yp - st.C * xp ∧ st.A * st.D - st.B * st.C = 1 ∧
  1 ≤ st.A ∧ 1 ≤ st.D ∧ 0 ≤ st.B ∧ 0 ≤ st.C ∧ st.C ≤ st.y ∧ st.y ≤ st.x ∧
  M * xp ≤ ap ∧ ap < M * (xp + 1) ∧ M * yp ≤ bp ∧ bp < M * (yp + 1) ∧
  0 ≤ xp ∧ xp < 2 ^ 60 ∧ 0 ≤ yp ∧ yp < 2 ^ 60 ∧
  0 ≤ st.D * bp - st.C * ap ∧ st.D * bp - st.C * ap ≤ st.A * ap - st.B * bp ∧
  st.A * ap - st.B * bp ≤ a ∧ st.D * bp - st.C * ap ≤ b ∧
  (1 ≤ st.k → st.D * bp - st.C * ap < b) ∧
  Int.gcd (st.A * ap - st.B * bp) (st.D * bp - st.C * ap) = Int.gcd a b ∧
  ((st.k % 2 = 0 ∧ ap = a ∧ bp = b) ∨ (st.k % 2 = 1 ∧ ap = b ∧ bp = a))

theorem inI64_of {v : Int} (h1 : -(2 ^ 63) ≤ v) (h2 : v < 2 ^ 63) : inI64 v = true := by
  simp [inI64]; omega

/-- The inner loop terminates with the invariant intact and no overflow. -/
theorem lehmerInner_spec (M a b : Int) (hM : 1 ≤ M) (hba : b ≤ a) :
    ∀ (fuel : Nat) (st : LehmerState) xp yp ap bp, LInv M a b st xp yp ap bp → st.y < (fuel : Int) →
      ∃ st' xp' yp' ap' bp', lehmerInner fuel st = .ok st' ∧ LInv M a b st' xp' yp' ap' bp' := by
  intro fuel
  induction fuel with
  | zero =>
    intro st _ _ _ _ h1 h2
    obtain ⟨-, -, -, -, -, -, hC, hCy, -⟩ := h1
    omega
  | succ f ih =>
    intro st xp yp ap bp hinv hf
    obtain ⟨hx, hy, hdet, hA, hD, hB, hC, hCy, hyx, ha1, ha2, hb1, hb2, hxp0, hxp, hyp0, hyp,
      hY0, hYX, hXa, hYb, hYk, hg, hpar⟩ := hinv
    have exp : st.D * st.x + st.B * st.y = xp := by
      have : (st.A * st.D - st.B * st.C) * xp = xp := by rw [hdet, Int.one_mul]
      rw [hx, hy]; grind
    have hxle : st.x ≤ xp := by
      have := Int.mul_nonneg (show 0 ≤ st.D - 1 by omega) (show 0 ≤ st.x by omega)
      have := Int.mul_nonneg hB (show 0 ≤ st.y by omega)
      grind
    unfold lehmerInner
    have hyc64 : inI64 (st.y - st.C) = true := inI64_of (by omega) (by omega)
    simp only [hyc64, Bool.not_true, Bool.false_eq_true, ite_false]
    by_cases hyc0 : st.y - st.C = 0
    · simp only [hyc0, ite_true]
      exact ⟨st, xp, yp, ap, bp, rfl, hx, hy, hdet, hA, hD, hB, hC, hCy, hyx, ha1, ha2, hb1, hb2,
        hxp0, hxp, hyp0, hyp, hY0, hYX, hXa, hYb, hYk, hg, hpar⟩
    simp only [hyc0, ite_false]
    have hyc : 1 ≤ st.y - st.C := by omega
    have hnum : 0 ≤ st.x + (st.A - 1) := by omega
    have htd : (st.x + (st.A - 1)).tdiv (st.y - st.C) = (st.x + (st.A - 1)) / (st.y - st.C) :=
      Int.tdiv_eq_ediv_of_nonneg hnum
    rw [htd]
    generalize hq : (st.x + (st.A - 1)) / (st.y - st.C) = q
    have hq0 : 0 ≤ q := by rw [← hq]; exact Int.ediv_nonneg hnum (by omega)
    have hq1 : q * (st.y - st.C) ≤ st.x + st.A - 1 := by
      rw [← hq]; have := Int.ediv_mul_le (st.x + (st.A - 1)) (show st.y - st.C ≠ 0 by omega); omega
    have hq2 : st.x + st.A - 1 < (q + 1) * (st.y - st.C) := by
      rw [← hq]
      have := Int.lt_mul_ediv_self_add (x := st.x + (st.A - 1)) (show 0 < st.y - st.C by omega)
      grind
    obtain ⟨n0, n1, d0, d1, c0, c1, y0, y1, hB60, hA60⟩ :=
      lehmer_no_overflow xp yp st.x st.y st.A st.B st.C st.D q hx hy hdet hA hD hB hC hCy hyx
        hxp hyp hyc hq0 hq1
    have i1 : inI64 (st.x + (st.A - 1)) = true := inI64_of (by omega) (by omega)
    have i2 : inI64 (q * st.D) = true := inI64_of (by omega) (by omega)
    have i3 : inI64 (st.B + q * st.D) = true := inI64_of (by omega) (by omega)
    have i4 : inI64 (q * st.y) = true := inI64_of (by omega) (by omega)
    have i5 : inI64 (st.x - q * st.y) = true := inI64_of (by omega) (by omega)
    simp only [i1, i2, i3, i4, i5, Bool.and_self, Bool.not_true, Bool.false_eq_true, ite_false]
    by_cases hrej : st.B + q * st.D > st.x - q * st.y
    · simp only [hrej, ite_true]
      exact ⟨st, xp, yp, ap, bp, rfl, hx, hy, hdet, hA, hD, hB, hC, hCy, hyx, ha1, ha2, hb1, hb2,
        hxp0, hxp, hyp0, hyp, hY0, hYX, hXa, hYb, hYk, hg, hpar⟩
    simp only [hrej, ite_false]
    have hacc : st.B + q * st.D ≤ st.x - q * st.y := by omega
    have i6 : inI64 (q * st.C) = true := inI64_of (by omega) (by omega)
    have i7 : inI64 (st.A + q * st.C) = true := inI64_of (by omega) (by omega)
    simp only [i6, i7, Bool.and_self, Bool.not_true, Bool.false_eq_true, ite_false]
    -- the true pair and the quotient
    obtain ⟨bX1, bX2, bY1, bY2⟩ := lehmer_true_bounds M xp yp ap bp st.x st.y st.A st.B st.C st.D
      hM hx hy hA hD hB hC ha1 ha2 hb1 hb2
    obtain ⟨tq1, tq2⟩ := lehmer_true_quotient M st.x st.y st.A st.B st.C st.D
      (st.A * ap - st.B * bp) (st.D * bp - st.C * ap) q hM hA hq0 hyc hq2 hacc bX1 bX2 bY1 bY2
    have ht_lt : st.x - q * st.y < st.y := by
      have := Int.mul_nonneg (show 0 ≤ q + 1 by omega) hC
      grind
    apply ih ⟨st.y, st.x - q * st.y, st.D, st.C, st.B + q * st.D, st.A + q * st.C, st.k + 1⟩
      yp xp bp ap _ (by simp only; omega)
    have eY' : (st.A + q * st.C) * ap - (st.B + q * st.D) * bp =
        (st.A * ap - st.B * bp) - q * (st.D * bp - st.C * ap) := by grind
    dsimp only [LInv]
    refine ⟨hy, by rw [hx, hy]; grind, by grind, hD, by have := Int.mul_nonneg hq0 hC; omega, hC,
      by have := Int.mul_nonneg hq0 (show 0 ≤ st.D by omega); omega, hacc, by omega,
      hb1, hb2, ha1, ha2, hyp0, hyp, hxp0, hxp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eY']; exact tq1
    · rw [eY']; omega
    · omega
    · rw [eY']; omega
    · intro _; rw [eY']; omega
    · rw [eY', Int.gcd_sub_mul_right_right, Int.gcd_comm, hg]
    · rcases hpar with ⟨hk, h1, h2⟩ | ⟨hk, h1, h2⟩
      · right; exact ⟨by omega, h2, h1⟩
      · left; exact ⟨by omega, h2, h1⟩

end PyLean.MathInt
