import PyLean.CoreLibs.CalStat.StatFlt

/-!
`math.sumprod` on ints is exact, through its `long` fast path (Modules/mathmodule.c:2205-2231)
and the generic `PyNumber_Multiply`/`PyNumber_Add` path it falls back to on overflow; with that,
`linear_regression(x, y, proportional=True)` (Lib/statistics.py:745-805) of int data is the least
squares slope through the origin, `sum(x*y) / sum(x*x)`, with the two sums exact.
-/

namespace PyLean.CoreLibs.CalStat

open PyLean
open PyLean.Binary64 (pw Rep binary64)

/-- `sum(a[i] * b[i])` over the common prefix. -/
def dotI : List Int → List Int → Int
  | a :: as, b :: bs => a * b + dotI as bs
  | _, _ => 0

/-- What `sumprod` keeps while every item is an int: the Python-level total and the C `long`
accumulator add up to the exact sum so far, nothing went through the float path. -/
def SpInv (st : SP) (S : Int) : Prop :=
  ∃ T : Int, st.total = .int T ∧ T + st.intTotal = S ∧ st.fltInUse = false ∧
    (st.intInUse = false → st.intTotal = 0) ∧ (st.intEnabled = false → st.intTotal = 0)

theorem bind_ok {α β : Type} {x : Py α} {v : α} (h : x = .ok v) (f : α → Py β) :
    (x >>= f) = f v := by rw [h]; rfl

@[simp] theorem ok_bind' {α β : Type} (v : α) (f : α → Py β) : ((Except.ok v : Py α) >>= f) = f v := rfl

theorem le_div_of_mul_le {a b c : Rat} (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c :=
  Rat.not_lt.mp (fun h' => by rw [Rat.div_lt_iff hc] at h'; exact Rat.not_le.mpr h' h)

theorem pow2_pos (e : Int) : 0 < Flt.pow2 e := by rw [pow2_eq]; exact PyLean.Binary64.pw_pos e

theorem ite_bind_eq {α β : Type} (c : Prop) [Decidable c] (x y : Py α) (k : α → Py β) :
    (if c then x >>= k else y >>= k) = ((if c then x else y) >>= k) := by
  split <;> rfl

theorem spFinalizeInt_inv (st : SP) (S : Int) (h : SpInv st S) :
    ∃ st', spFinalizeInt st = .ok st' ∧ SpInv st' S ∧ st'.intEnabled = false := by
  obtain ⟨T, h1, h2, h3, h4, h5⟩ := h
  unfold spFinalizeInt
  by_cases hu : st.intInUse = true
  · rw [if_pos hu, h1]
    refine ⟨_, rfl, ⟨T + st.intTotal, rfl, by simp; omega, by simpa using h3, fun _ => rfl, fun _ => rfl⟩, rfl⟩
  · have hu' : st.intInUse = false := by simpa using hu
    rw [if_neg hu]
    refine ⟨_, rfl, ⟨T, h1, h2, by simpa using h3, by simpa using h4, fun _ => by simpa using h4 hu'⟩, rfl⟩

theorem spFinalizeFlt_inv (st : SP) (S : Int) (h : SpInv st S) :
    spFinalizeFlt st = .ok { st with fltEnabled := false } := by
  obtain ⟨T, h1, h2, h3, h4, h5⟩ := h
  unfold spFinalizeFlt
  rw [if_neg (by simp [h3])]
  rfl

theorem spInv_fltOff (st : SP) (S : Int) (h : SpInv st S) : SpInv { st with fltEnabled := false } S := by
  obtain ⟨T, h1, h2, h3, h4, h5⟩ := h
  exact ⟨T, h1, h2, h3, h4, h5⟩

/-- `if st.int_path_enabled: finalize` leaves the int path disabled with nothing in the `long`. -/
theorem finInt_inv (st : SP) (S : Int) (h : SpInv st S) :
    ∃ st1, (if st.intEnabled then spFinalizeInt st else pure st) = .ok st1 ∧ SpInv st1 S ∧
      st1.intEnabled = false := by
  split
  · exact spFinalizeInt_inv st S h
  · rename_i hc
    exact ⟨st, rfl, h, by simpa using hc⟩

theorem finFlt_inv (st : SP) (S : Int) (h : SpInv st S) :
    ∃ st1, (if st.fltEnabled then spFinalizeFlt st else pure st) = .ok st1 ∧ SpInv st1 S ∧
      st1.intEnabled = st.intEnabled := by
  split
  · exact ⟨_, spFinalizeFlt_inv st S h, spInv_fltOff st S h, rfl⟩
  · exact ⟨st, rfl, h, rfl⟩

theorem viaInt_some (st : SP) (a b prod : Int)
    (hv : (if (st.intEnabled && clsInt.same clsInt && clsInt.same clsInt) = true then
      if (fitsLong a && fitsLong b && fitsLong (a * b) && fitsLong (st.intTotal + a * b)) = true then some (a * b)
      else none
    else none) = some prod) : prod = a * b ∧ st.intEnabled = true := by
  by_cases c1 : st.intEnabled = true
  · by_cases c2 : (fitsLong a && fitsLong b && fitsLong (a * b) && fitsLong (st.intTotal + a * b)) = true
    · have e : (st.intEnabled && clsInt.same clsInt && clsInt.same clsInt) = true := by
        simp [c1, Cls.same]
      rw [if_pos e, if_pos c2] at hv
      exact ⟨(Option.some.inj hv).symm, c1⟩
    · have e : (st.intEnabled && clsInt.same clsInt && clsInt.same clsInt) = true := by
        simp [c1, Cls.same]
      rw [if_pos e, if_neg c2] at hv
      cases hv
  · have e : ¬ (st.intEnabled && clsInt.same clsInt && clsInt.same clsInt) = true := by
      simp [c1]
    rw [if_neg e] at hv
    cases hv

theorem spStep_int (st : SP) (S a b : Int) (h : SpInv st S) :
    ∃ st', spStep st (Val.int a).toN (Val.int b).toN = .ok st' ∧ SpInv st' (S + a * b) := by
  unfold spStep
  simp only [Val.toN, Val.cls]
  split
  · rename_i prod hv
    obtain ⟨hp, hen⟩ := viaInt_some st a b prod hv
    subst hp
    obtain ⟨T, h1, h2, h3, h4, h5⟩ := h
    refine ⟨_, rfl, T, h1, ?_, h3, fun h => by simp at h, fun h => by simp [hen] at h⟩
    simp only; omega
  · obtain ⟨st1, e1, i1, -⟩ := finInt_inv st S h
    rw [ite_bind_eq, bind_ok e1]
    simp only [spFloats]
    have hvf : (if st1.fltEnabled = true then (none : Option TL) else none) = none := by
      split <;> rfl
    simp only [Option.map, hvf]
    obtain ⟨st2, e2, i2, -⟩ := finFlt_inv st1 S i1
    rw [ite_bind_eq, bind_ok e2]
    obtain ⟨T, h1, h2, h3, h4, h5⟩ := i2
    have em : vmul (Val.int a) (Val.int b) = .ok (.int (a * b)) := rfl
    rw [bind_ok em, h1]
    refine ⟨_, rfl, T + a * b, rfl, ?_, h3, h4, h5⟩
    simp only; omega

theorem sumprodLoop_int (as bs : List Int) (st : SP) (S : Int) (h : SpInv st S) (hl : as.length = bs.length) :
    sumprodLoop st (ints as) (ints bs) = .ok (.int (S + dotI as bs)) := by
  induction as generalizing bs st S with
  | nil =>
    cases bs with
    | cons _ _ => simp at hl
    | nil =>
      simp only [ints, List.map_nil, sumprodLoop, dotI, Int.add_zero]
      obtain ⟨st1, e1, i1, d1⟩ := finInt_inv st S h
      rw [ite_bind_eq, bind_ok e1]
      obtain ⟨st2, e2, i2, d2⟩ := finFlt_inv st1 S i1
      rw [ite_bind_eq, bind_ok e2]
      obtain ⟨T, h1, h2, h3, h4, h5⟩ := i2
      have h0 := h5 (by rw [d2, d1])
      rw [h1]
      show Except.ok (Val.int T) = Except.ok (Val.int S)
      congr 2
      omega
  | cons a as ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      simp only [ints, List.map_cons, sumprodLoop]
      obtain ⟨st', e, i'⟩ := spStep_int st S a b h
      rw [bind_ok e]
      have := ih bs st' (S + a * b) i' (by simpa using hl)
      simp only [ints] at this
      rw [this]
      simp only [dotI]
      congr 2
      omega

theorem sumprod_ints (as bs : List Int) (hl : as.length = bs.length) :
    sumprod (ints as) (ints bs) = .ok (.int (dotI as bs)) := by
  have := sumprodLoop_int as bs {} 0 ⟨0, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩ hl
  simpa [sumprod] using this

/-- `ofRat` of a non-zero rational at least `2**-1074` in magnitude is not a zero: a zero result
would be farther from it than the smallest subnormal. -/
theorem ofRat_pos_ne_zero {q : Rat} (hq : Flt.pow2 (-1074) ≤ q) (b : Bool) : Flt.ofRat q ≠ .zero b := by
  have hP := pow2_pos (-1074)
  have hq0 : q ≠ 0 := by
    generalize Flt.pow2 (-1074) = P at *
    intro h; rw [h] at hq; grind
  have hpos : ¬ q < 0 := by
    generalize Flt.pow2 (-1074) = P at *
    grind
  intro h
  unfold Flt.ofRat at h
  rw [if_neg hq0] at h
  simp only at h
  have hy : Rep binary64 (Flt.pow2 (-1074)) := ⟨1, -1074, by decide, by decide, Or.inl (by rw [pow2_eq]; simp)⟩
  have hnear := roundMag_nearest hq0 hy
  generalize hRM : Flt.roundMag q.num.natAbs q.den = RM at h hnear
  obtain ⟨m, e⟩ := RM
  simp only at h hnear
  by_cases hm : m = 0
  · subst hm
    rw [if_neg hpos] at hnear
    have e0 : q - ((0 : Nat) : Rat) * Flt.pow2 e = q := by simp [Rat.sub_eq_add_neg, Rat.add_zero]
    rw [e0] at hnear
    generalize Flt.pow2 (-1074) = P at *
    have h1 : 0 ≤ q - P := by grind
    have h2 : Rat.abs q = q := PyLean.Binary64.abs_of_nonneg (by grind)
    rw [h2, PyLean.Binary64.abs_of_nonneg h1] at hnear
    grind
  · rw [if_neg hm] at h
    split at h <;> cases h

theorem intToFlt_small (i : Int) (h : i.natAbs < 2 ^ 53) :
    intToFlt i = .ok (if i = 0 then Flt.pz else .fin (i : Rat)) := by
  unfold intToFlt Flt.ofInt
  by_cases h0 : i = 0
  · subst h0; rfl
  · rw [ofRat_int i h0 h, if_neg h0]

/-- `linear_regression(x, y, proportional=True)` of int data, statistics.py:745-805. The two sums
`sumprod(x, y)` and `sumprod(x, x)` are exact (`sumprod_ints`), whichever path of `math.sumprod` they
take; what remains is `float(sum(x*y)) / float(sum(x*x))`, `OverflowError` when a sum is beyond
the float range, `StatisticsError('x is constant')` when every `x` is zero, intercept `0.0`
("The data is fit to a line passing through the origin", "the intercept will always be 0.0"). When
both sums are below `2**53` the slope is the least-squares slope through the origin,
`sum(x*y) / sum(x*x)`, correctly rounded. The length checks come first. -/
def LinRegProportional : Prop :=
  ∀ xs ys : List Int,
    (xs.length ≠ ys.length → linearRegression (ints xs) (ints ys) true = .error
      (.named "StatisticsError" "linear regression requires that both inputs have same number of data points")) ∧
    (xs.length = ys.length → xs.length < 2 → linearRegression (ints xs) (ints ys) true = .error
      (.named "StatisticsError" "linear regression requires at least two data points")) ∧
    (xs.length = ys.length → 2 ≤ xs.length →
      linearRegression (ints xs) (ints ys) true =
        (do let a ← intToFlt (dotI xs ys)
            let b ← intToFlt (dotI xs xs)
            if b.truthy then .ok (Val.flt (Flt.div (Flt.add a Flt.pz) b), Val.flt Flt.pz)
            else .error (.named "StatisticsError" "x is constant")) ∧
      (dotI xs xs = 0 → linearRegression (ints xs) (ints ys) true =
        .error (.named "StatisticsError" "x is constant")) ∧
      ((dotI xs ys).natAbs < 2 ^ 53 → 0 < dotI xs xs → dotI xs xs < 2 ^ 53 →
        linearRegression (ints xs) (ints ys) true =
          .ok (Val.flt (Flt.ofRat ((dotI xs ys : Rat) / (dotI xs xs : Rat))), Val.flt Flt.pz)))

theorem lr_general (xs ys : List Int) (hl : xs.length = ys.length) (h2 : 2 ≤ xs.length) :
    linearRegression (ints xs) (ints ys) true =
      (do let a ← intToFlt (dotI xs ys)
          let b ← intToFlt (dotI xs xs)
          if b.truthy then .ok (Val.flt (Flt.div (Flt.add a Flt.pz) b), Val.flt Flt.pz)
          else .error (.named "StatisticsError" "x is constant")) := by
  have hlen : (ints ys).length = (ints xs).length := by simp [ints, hl]
  have hlen2 : ¬ (ints xs).length < 2 := by simp [ints]; omega
  have e1 := sumprod_ints xs ys hl
  have e2 := sumprod_ints xs xs rfl
  unfold linearRegression
  simp only [hlen, bne_self_eq_false, Bool.false_eq_true, ite_false, hlen2, Bool.not_true]
  show lrCore (ints xs) (ints ys) true Flt.pz Flt.pz = _
  unfold lrCore
  simp only [e1, e2, ok_bind']
  cases ha : intToFlt (dotI xs ys) with
  | error e =>
    simp [vadd, arith, addOp, ha, bind, Except.bind, pure, Except.pure]
  | ok a =>
    cases hb : intToFlt (dotI xs xs) with
    | error e =>
      have he : e = .overflowError "int too large to convert to float" := by
        unfold intToFlt at hb; split at hb <;> cases hb; rfl
      subst he
      simp [vadd, arith, addOp, ha, vdiv, divOp, hb, bind, Except.bind, pure, Except.pure]
    | ok b =>
      cases b <;> simp [vadd, arith, addOp, ha, vdiv, divOp, hb, fltDiv, Flt.truthy, bind, Except.bind,
        pure, Except.pure, statErr]

theorem sq_nonneg' (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have : a * a = (-a) * (-a) := by rw [Int.neg_mul_neg]
    rw [this]; exact Int.mul_nonneg (by omega) (by omega)

theorem dotI_sq_nonneg (xs : List Int) : 0 ≤ dotI xs xs := by
  induction xs with
  | nil => simp [dotI]
  | cons a as ih => simp only [dotI]; have := sq_nonneg' a; omega

theorem dotI_zero (xs ys : List Int) (h : dotI xs xs = 0) : dotI xs ys = 0 := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons a as ih =>
    simp only [dotI] at h
    have h1 := sq_nonneg' a
    have h2 := dotI_sq_nonneg as
    have ha : a * a = 0 := by omega
    have ha' : a = 0 := by
      rcases Int.mul_eq_zero.mp ha with h | h <;> exact h
    cases ys with
    | nil => rfl
    | cons b bs =>
      simp only [dotI, ha', Int.zero_mul, Int.zero_add]
      exact ih bs (by omega)

theorem ofRat_ne_zero_of_abs {q : Rat} (hq : Flt.pow2 (-1074) ≤ q ∨ q ≤ -Flt.pow2 (-1074)) (b : Bool) :
    Flt.ofRat q ≠ .zero b := by
  rcases hq with h | h
  · exact ofRat_pos_ne_zero h b
  · have hP := pow2_pos (-1074)
    have hq0 : -q ≠ 0 := by
      generalize Flt.pow2 (-1074) = P at *
      grind
    have hq1 : Flt.pow2 (-1074) ≤ -q := by
      generalize Flt.pow2 (-1074) = P at *
      grind
    have e : q = -(-q) := by grind
    rw [e, ofRat_neg (-q) hq0]
    intro hc
    have := ofRat_pos_ne_zero (q := -q) hq1 (!b)
    apply this
    cases h' : Flt.ofRat (-q) <;> rw [h'] at hc <;> simp [Flt.neg] at hc
    · subst hc; simp

theorem linRegProportional_proven : LinRegProportional := by
  intro xs ys
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have : ((ints ys).length != (ints xs).length) = true := by simp [ints]; omega
    simp only [linearRegression, this, ite_true]
    rfl
  · intro hl h
    have hlen : (ints ys).length = (ints xs).length := by simp [ints, hl]
    have h' : (ints xs).length < 2 := by simp [ints]; omega
    simp only [linearRegression, hlen, bne_self_eq_false, Bool.false_eq_true, ite_false, h', ite_true]
    rfl
  · intro hl h2
    have hg := lr_general xs ys hl h2
    refine ⟨hg, ?_, ?_⟩
    · intro h0
      rw [hg, h0, dotI_zero xs ys h0]
      rfl
    · intro h1 h3 h4
      rw [hg, intToFlt_small _ h1, intToFlt_small _ (by omega)]
      have hx0 : ¬ dotI xs xs = 0 := by omega
      simp only [bind, Except.bind, hx0, ite_false, Flt.truthy, ite_true]
      have hD : (0 : Rat) < (dotI xs xs : Rat) := Rat.intCast_pos.mpr h3
      by_cases hy0 : dotI xs ys = 0
      · have e0 : ((0 : Int) : Rat) / (dotI xs xs : Rat) = 0 := by simp [Rat.div_def]
        simp only [hy0, ite_true, Flt.pz, Flt.add, Flt.div, e0]
        have : ¬ ((dotI xs xs : Rat) < 0) := by grind
        simp [this, Flt.ofRat]
      · simp only [hy0, ite_false, Flt.add, Flt.div, Flt.pz]
        have hne : ∀ b, Flt.ofRat ((dotI xs ys : Rat) / (dotI xs xs : Rat)) ≠ .zero b := by
          intro b
          apply ofRat_ne_zero_of_abs
          have hD2 : (dotI xs xs : Rat) < Flt.pow2 53 := by
            rw [pow2_eq]
            have e2 : PyLean.Binary64.pw (53 : Int) = ((2 ^ 53 : Nat) : Rat) := PyLean.Binary64.pw_natCast 53
            rw [e2]
            have : ((dotI xs xs : Int) : Rat) = (((dotI xs xs).toNat : Nat) : Rat) := by
              rw [← Rat.intCast_natCast]; congr 1; omega
            rw [this]
            exact Rat.natCast_lt_natCast.mpr (by omega)
          have hsmall : Flt.pow2 (-1074) * (dotI xs xs : Rat) ≤ 1 := by
            have h53 : Flt.pow2 (-1074) * Flt.pow2 53 ≤ 1 := by
              rw [pow2_eq, pow2_eq, ← PyLean.Binary64.pw_add]
              have := PyLean.Binary64.pw_le (show (-1074 + 53 : Int) ≤ 0 by decide)
              simpa [PyLean.Binary64.pw] using this
            have hp := pow2_pos (-1074)
            have := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hD2) (Rat.le_of_lt hp)
            generalize Flt.pow2 (-1074) = P at *
            generalize Flt.pow2 53 = Q at *
            grind
          rcases Int.lt_or_gt_of_ne hy0 with hn | hp
          · right
            have : (1 : Rat) ≤ -(dotI xs ys : Rat) := by
              have := Rat.intCast_le_intCast.mpr (show 1 ≤ -dotI xs ys by omega)
              simpa using this
            have h5 : Flt.pow2 (-1074) ≤ -(dotI xs ys : Rat) / (dotI xs xs : Rat) :=
              le_div_of_mul_le hD (by generalize Flt.pow2 (-1074) = P at *; grind)
            have e5 : -(dotI xs ys : Rat) / (dotI xs xs : Rat) = -((dotI xs ys : Rat) / (dotI xs xs : Rat)) := by
              simp only [Rat.div_def]; grind
            rw [e5] at h5
            generalize Flt.pow2 (-1074) = P at *
            grind
          · left
            have : (1 : Rat) ≤ (dotI xs ys : Rat) := by
              have := Rat.intCast_le_intCast.mpr (show 1 ≤ dotI xs ys by omega)
              simpa using this
            exact le_div_of_mul_le hD (by generalize Flt.pow2 (-1074) = P at *; grind)
        cases hr : Flt.ofRat ((dotI xs ys : Rat) / (dotI xs xs : Rat)) with
        | zero b => exact absurd hr (hne b)
        | _ => rfl

end PyLean.CoreLibs.CalStat
