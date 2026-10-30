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

theorem digitCount_zero_iff (n : Nat) : digitCount n = 0 ↔ n = 0 := by
  constructor
  · intro h; have := (digitCount_spec n).1; rw [h] at this; simpa using this
  · intro h; subst h; rfl

/-- What one pass of the outer loop may do. -/
def StepOk (a b : Nat) (r : Py (Nat ⊕ (Nat × Nat))) : Prop :=
  r = .ok (.inl (Nat.gcd a b)) ∨
    ∃ c d, r = .ok (.inr (c, d)) ∧ d ≤ c ∧ d < b ∧ Nat.gcd c d = Nat.gcd a b

/-- One pass of the outer loop of `_PyLong_GCD` on `0 <= b <= a`: it returns
`gcd(a, b)`, or a pair with the same gcd and a strictly smaller `b`. -/
theorem lehmerOuterStep_spec (a b : Nat) (hba : b ≤ a) : StepOk a b (lehmerOuterStep a b) := by
  unfold lehmerOuterStep StepOk
  by_cases hsa : digitCount a ≤ 2
  · rw [if_pos hsa, gcdSimple_eq]; left; rfl
  rw [if_neg hsa]
  by_cases hsb : digitCount b = 0
  · rw [if_pos hsb]
    have : b = 0 := (digitCount_zero_iff b).mp hsb
    subst this; left; simp
  rw [if_neg hsb]
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · exact absurd ((digitCount_zero_iff b).mpr h) hsb
    · exact h
  have hm : (a : Int) < 2 ^ (30 * digitCount a) := by
    have := (digitCount_spec a).1; exact_mod_cast this
  have hsa3 : 3 ≤ digitCount a := by omega
  -- a < 2^(sh + 60), so the top part x0 = a >> sh is below 2^60
  have hx60 : a >>> lehmerShift a < 2 ^ 60 := by
    unfold lehmerShift
    generalize hnb : bitLength (a >>> (30 * (digitCount a - 1))) = nb
    have h1 : a >>> (30 * (digitCount a - 1)) < 2 ^ nb := by rw [← hnb]; exact lt_two_pow_bitLength' _
    rw [Nat.shiftRight_eq_div_pow] at h1 ⊢
    have h2 : a < 2 ^ nb * 2 ^ (30 * (digitCount a - 1)) :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mp h1
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    have e : 2 ^ 60 * 2 ^ (30 * (digitCount a - 3) + nb) = 2 ^ nb * 2 ^ (30 * (digitCount a - 1)) := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    omega
  generalize hsh : lehmerShift a = sh at *
  have hyx0 : b >>> sh ≤ a >>> sh := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]; exact Nat.div_le_div_right hba
  have hax : 2 ^ sh * (a >>> sh) ≤ a ∧ a < 2 ^ sh * (a >>> sh + 1) := by
    rw [Nat.shiftRight_eq_div_pow]
    exact ⟨Nat.mul_div_le a _, Nat.lt_mul_div_succ a (Nat.two_pow_pos _)⟩
  have hby : 2 ^ sh * (b >>> sh) ≤ b ∧ b < 2 ^ sh * (b >>> sh + 1) := by
    rw [Nat.shiftRight_eq_div_pow]
    exact ⟨Nat.mul_div_le b _, Nat.lt_mul_div_succ b (Nat.two_pow_pos _)⟩
  generalize hx0 : a >>> sh = x0 at *
  generalize hy0 : b >>> sh = y0 at *
  have hM : (1 : Int) ≤ ((2 ^ sh : Nat) : Int) := by have := Nat.one_le_two_pow (n := sh); omega
  have hinit : LInv ((2 ^ sh : Nat) : Int) a b ⟨(x0 : Int), (y0 : Int), 1, 0, 0, 1, 0⟩
      x0 y0 a b := by
    dsimp only [LInv]
    have c1 : ((2 ^ sh : Nat) : Int) * x0 ≤ a := by exact_mod_cast hax.1
    have c2 : (a : Int) < ((2 ^ sh : Nat) : Int) * (x0 + 1) := by exact_mod_cast hax.2
    have c3 : ((2 ^ sh : Nat) : Int) * y0 ≤ b := by exact_mod_cast hby.1
    have c4 : (b : Int) < ((2 ^ sh : Nat) : Int) * (y0 + 1) := by exact_mod_cast hby.2
    refine ⟨by simp, by simp, by simp, by decide, by decide, by decide, by decide, by omega,
      by omega, c1, c2, c3, c4, by omega, by omega, by omega, by omega, by simp, by simp; omega,
      by simp, by simp, by simp, by simp, Or.inl ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨st, xp, yp, ap, bp, hrun, hinv⟩ :=
    lehmerInner_spec _ a b hM (by omega) lehmerInnerFuel _ _ _ _ _ hinit (by
      have e : lehmerInnerFuel = 2 ^ 64 := by unfold lehmerInnerFuel; rfl
      rw [e]; have : y0 < 2 ^ 64 := by omega
      exact Int.ofNat_lt.mpr this)
  rw [hrun]
  split
  · rename_i e he; cases he
  rename_i st' he
  cases he
  by_cases hk0 : st.k = 0
  · rw [if_pos hk0]
    right
    refine ⟨b, a % b, rfl, Nat.le_of_lt (Nat.mod_lt _ hb0), Nat.mod_lt _ hb0, ?_⟩
    rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec, Nat.gcd_comm]
  rw [if_neg hk0]
  right
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hY0, hYX, hXa, -, hYk, hg, hpar⟩ := hinv
  have hYb := hYk (by omega)
  obtain ⟨X, hX⟩ : ∃ X, st.A * ap - st.B * bp = X := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, st.D * bp - st.C * ap = Y := ⟨_, rfl⟩
  rw [hX, hY] at hYX hg
  rw [hX] at hXa
  rw [hY] at hY0 hYb
  have hnew : lehmerNew st a b = (X.toNat, Y.toNat) := by
    unfold lehmerNew
    have key : ∀ (c d : Int), c = X → d = Y →
        ((c % 2 ^ (30 * digitCount a)).toNat, (d % 2 ^ (30 * digitCount a)).toNat) =
          (X.toNat, Y.toNat) := by
      intro c d hc hd
      rw [hc, hd, Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)]
    by_cases hp : st.k % 2 = 1
    · rw [if_pos hp]
      rcases hpar with ⟨h1, -⟩ | ⟨-, h2, h3⟩
      · omega
      apply key
      · rw [← hX, h2, h3]; grind
      · rw [← hY, h2, h3]; grind
    · rw [if_neg hp]
      rcases hpar with ⟨-, h2, h3⟩ | ⟨h1, -⟩
      · apply key
        · rw [← hX, h2, h3]
        · rw [← hY, h2, h3]
      · omega
  refine ⟨X.toNat, Y.toNat, by rw [hnew], by omega, by omega, ?_⟩
  have : Int.gcd X Y = Nat.gcd X.toNat Y.toNat := by
    unfold Int.gcd; congr 1 <;> omega
  rw [← this, hg]; rfl

/-- The outer loop of `_PyLong_GCD` on `0 <= b <= a` returns `gcd(a, b)`. -/
theorem lehmerOuter_spec : ∀ (fuel a b : Nat), b ≤ a → b < fuel →
    lehmerOuter fuel a b = .ok (Nat.gcd a b) := by
  intro fuel
  induction fuel with
  | zero => intro a b _ h; omega
  | succ f ih =>
    intro a b hba hf
    rw [lehmerOuter]
    rcases lehmerOuterStep_spec a b hba with h | ⟨c, d, h, hdc, hdb, hg⟩
    · rw [h]
    · rw [h]; dsimp only; rw [ih c d hdc (by omega), hg]

/-- `_PyLong_GCD(a, b)` is `gcd(a, b)` for all ints. -/
theorem pyLongGCD_eq (a b : Int) : pyLongGCD a b = .ok (Int.gcd a b) := by
  unfold pyLongGCD
  split
  · rw [gcdSimple_eq]
  · dsimp only
    by_cases h : a.natAbs < b.natAbs
    · simp only [h, ite_true]
      rw [lehmerOuter_spec _ _ _ (by omega) (by omega), Nat.gcd_comm]; rfl
    · simp only [h, ite_false]
      rw [lehmerOuter_spec _ _ _ (by omega) (by omega)]; rfl

/-! ### `math.gcd` and `math.lcm` for all arguments -/

theorem gcdLoop_general : ∀ (xs : List Int) (res : Nat),
    gcdLoop (res : Int) xs = .ok (xs.foldl (fun g a => Nat.gcd g a.natAbs) res : Nat)
  | [], _ => rfl
  | x :: xs, res => by
    unfold gcdLoop
    by_cases h1 : (res : Int) = 1
    · have : res = 1 := by omega
      subst this
      rw [if_pos h1, gcdLoop_general xs 1]
      simp only [List.foldl_cons, Nat.gcd_one_left, foldl_gcd_one]
    · rw [if_neg h1, pyLongGCD_eq]
      simp only [bind, Except.bind]
      exact gcdLoop_general xs _

theorem gcdGeneral_proven : GcdGeneral := by
  intro args
  unfold gcd listGcd
  match args with
  | [a, b] =>
    simp only
    rw [pyLongGCD_eq]
    simp [List.foldl, Int.gcd]; rfl
  | [] => rfl
  | [a] => simp [List.foldl]
  | a :: b :: c :: rest =>
    simp only
    unfold gcdLoop
    by_cases h1 : a = 1
    · subst h1
      rw [if_pos rfl]
      have := gcdLoop_general (c :: rest) 1
      rw [show ((1 : Nat) : Int) = 1 from rfl] at this
      rw [this]
      simp only [List.foldl, Nat.gcd_one_left, Nat.gcd_zero_left, Int.natAbs_one, foldl_gcd_one]
    · rw [if_neg h1, pyLongGCD_eq]
      simp only [bind, Except.bind]
      refine (gcdLoop_general (c :: rest) (Int.gcd a b)).trans ?_
      simp [List.foldl, Int.gcd]

/-- `long_lcm(a, b)`, mathmodule.c:765-789, is `lcm(abs(a), abs(b))`. -/
theorem longLcm_eq (a b : Int) : longLcm a b = .ok (Nat.lcm a.natAbs b.natAbs : Int) := by
  unfold longLcm
  by_cases h0 : a = 0
  · subst h0; simp [Nat.lcm]
  by_cases hb0 : b = 0
  · subst hb0; simp [Nat.lcm]
  simp only [h0, hb0, or_self, ite_false]
  rw [pyLongGCD_eq]
  simp only [bind, Except.bind, pure, Except.pure]
  congr 1
  have hdvd : (Int.gcd a b : Int) ∣ a := Int.gcd_dvd_left a b
  have hgpos : 0 < Int.gcd a b := Int.gcd_pos_of_ne_zero_left b h0
  have hgn : Nat.gcd a.natAbs b.natAbs = Int.gcd a b := rfl
  generalize Int.gcd a b = g at *
  obtain ⟨t, ht⟩ := hdvd
  have hq : floorDiv a g = t := by
    unfold floorDiv
    rw [Int.fdiv_eq_ediv_of_dvd ⟨t, ht⟩, ht, Int.mul_ediv_cancel_left _ (by omega)]
  rw [hq]
  unfold Nat.lcm
  have e1 : a.natAbs = g * t.natAbs := by
    have := congrArg Int.natAbs ht; rw [Int.natAbs_mul] at this; simpa using this
  rw [hgn, e1, Nat.mul_assoc, Nat.mul_div_cancel_left _ hgpos, Int.natAbs_mul]

theorem foldl_lcm_zero : ∀ xs : List Int, xs.foldl (fun (l : Nat) (a : Int) => Nat.lcm l a.natAbs) 0 = 0
  | [] => rfl
  | x :: xs => by simp only [List.foldl, Nat.lcm_zero_left]; exact foldl_lcm_zero xs

theorem lcmLoop_general : ∀ (xs : List Int) (res : Nat),
    lcmLoop (res : Int) xs = .ok ((xs.foldl (fun (l : Nat) (a : Int) => Nat.lcm l a.natAbs) res : Nat) : Int)
  | [], _ => rfl
  | x :: xs, res => by
    unfold lcmLoop
    by_cases h0 : (res : Int) = 0
    · have : res = 0 := by omega
      subst this
      rw [if_pos h0, lcmLoop_general xs 0]
      simp only [List.foldl_cons, Nat.lcm_zero_left, foldl_lcm_zero]
    · rw [if_neg h0, longLcm_eq]
      simp only [bind, Except.bind]
      exact lcmLoop_general xs _

theorem lcmGeneral_proven : LcmGeneral := by
  intro args
  unfold lcm
  match args with
  | [] => rfl
  | [a] => simp [List.foldl, Nat.lcm]
  | a :: x :: rest =>
    simp only
    unfold lcmLoop
    by_cases h0 : a = 0
    · subst h0
      rw [if_pos rfl]
      have := lcmLoop_general rest 0
      rw [show ((0 : Nat) : Int) = 0 from rfl] at this
      rw [this]
      simp only [List.foldl_cons, Int.natAbs_zero, Nat.lcm_zero_right, Nat.lcm_zero_left,
        foldl_lcm_zero]
    · rw [if_neg h0, longLcm_eq]
      simp only [bind, Except.bind]
      refine (lcmLoop_general rest _).trans ?_
      simp [List.foldl, Nat.lcm_one_left]

end PyLean.MathInt
