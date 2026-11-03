import PyLean.ListSort.CountRunMax

/-! # The run `count_run` finds is a run of its input -/

namespace PyLean.ListSort

variable {α : Type}

/-- Consecutive keys never decrease. -/
def NonDec (kf : α → Int) : List α → Prop
  | a :: b :: l => kf a ≤ kf b ∧ NonDec kf (b :: l)
  | _ => True

/-- Consecutive keys never increase. -/
def NonInc (kf : α → Int) : List α → Prop
  | a :: b :: l => kf b ≤ kf a ∧ NonInc kf (b :: l)
  | _ => True

theorem nonDec_tail (kf : α → Int) (a : α) (l : List α) (h : NonDec kf (a :: l)) : NonDec kf l := by
  match l, h with
  | [], _ => trivial
  | _ :: _, h => exact h.2

theorem ascTake_nonDec (kf : α → Int) :
    ∀ (prev : α) (rest : List α) (ms : MS), NonDec kf (prev :: (ascTake (ltOf kf) prev rest ms).1)
  | _, [], _ => trivial
  | prev, z :: rest, ms => by
    simp only [ascTake, islt, ltOf]
    by_cases h : kf z < kf prev
    · simp only [h, decide_true, ↓reduceIte]; trivial
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by omega, ascTake_nonDec kf z rest _⟩

theorem nonDec_head_le_last (kf : α → Int) :
    ∀ (a : α) (l : List α), NonDec kf (a :: l) → kf a ≤ kf ((a :: l).getLast (by simp))
  | a, [], _ => by simp
  | a, b :: l, h => by
    rw [List.getLast_cons (by simp)]
    have := nonDec_head_le_last kf b l h.2
    exact Int.le_trans h.1 this

/-- A non-decreasing list whose last key is at most its first is constant, so non-increasing too. -/
theorem nonDec_flat (kf : α → Int) :
    ∀ (a : α) (l : List α), NonDec kf (a :: l) → kf ((a :: l).getLast (by simp)) ≤ kf a → NonInc kf (a :: l)
  | a, [], _, _ => trivial
  | a, b :: l, h, hl => by
    rw [List.getLast_cons (by simp)] at hl
    have hb := nonDec_head_le_last kf b l h.2
    exact ⟨Int.le_trans hb hl, nonDec_flat kf b l h.2 (Int.le_trans hl h.1)⟩

theorem nonInc_snoc (kf : α → Int) :
    ∀ (a : α) (l : List α) (y : α), NonInc kf (a :: l) → kf y ≤ kf ((a :: l).getLast (by simp)) →
      NonInc kf ((a :: l) ++ [y])
  | a, [], y, _, h => ⟨h, trivial⟩
  | a, b :: l, y, hn, h => by
    rw [List.getLast_cons (by simp)] at h
    exact ⟨hn.1, nonInc_snoc kf b l y hn.2 h⟩

theorem nonInc_append (kf : α → Int) :
    ∀ (l1 l2 : List α) (a : α), NonInc kf (l1 ++ [a]) → NonInc kf (a :: l2) → NonInc kf (l1 ++ a :: l2)
  | [], l2, a, _, h2 => h2
  | [x], l2, a, h1, h2 => ⟨h1.1, h2⟩
  | x :: y :: l1, l2, a, h1, h2 => ⟨h1.1, nonInc_append kf (y :: l1) l2 a h1.2 h2⟩

/-- What the descending loop consumes is non-increasing from `prev` on, and it leaves the rest. -/
theorem descLoop_consumed (kf : α → Int) :
    ∀ (done grp : List α) (prev : α) (rest : List α) (ms : MS),
      ∃ c, rest = c ++ (descLoop (ltOf kf) done grp prev rest ms).2.1 ∧ NonInc kf (prev :: c)
  | done, grp, prev, [], ms => ⟨[], by simp [descLoop], trivial⟩
  | done, grp, prev, z :: rest, ms => by
    simp only [descLoop, islt, ltOf]
    by_cases h : kf z < kf prev
    · simp only [h, decide_true, ↓reduceIte]
      obtain ⟨c, h1, h2⟩ := descLoop_consumed kf (done ++ grp.reverse) [z] z rest
        { ms with ncmp := ms.ncmp + 1 }
      exact ⟨z :: c, by rw [List.cons_append, ← h1], ⟨by omega, h2⟩⟩
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      by_cases h' : kf prev < kf z
      · simp only [h', decide_true, ↓reduceIte]
        exact ⟨[], by simp, trivial⟩
      · simp only [h', decide_false, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨c, h1, h2⟩ := descLoop_consumed kf done (grp ++ [z]) z rest
          { ms with ncmp := ms.ncmp + 1 + 1 }
        exact ⟨z :: c, by rw [List.cons_append, ← h1], ⟨by omega, h2⟩⟩

/-- `count_run` (listobject.c:1972-2064) with keys compared by `<` (any strict weak order on a finite
list, as `Stable.lean` explains): the first `n` items of its input, in the input's order, are a
non-increasing part followed by a non-decreasing part — a descending run whose equal groups it reversed
in place, then the ascending extension (:2048-2056); for an ascending run the first part is empty. With
`CountRunSpec` (the run ends up sorted) and `CountRunMaximal` (it stops only at a smaller item) this pins
the length: a `count_run` that sorted the whole slice of `[1, 3, 2]` and returned 3 fails it. -/
def CountRunInputRun : Prop :=
  ∀ (α : Type) (kf : α → Int) (xs : List α) (ms : MS),
    ∃ P Q, xs.take (countRun (ltOf kf) xs ms).1 = P ++ Q ∧ NonInc kf P ∧ NonDec kf Q

theorem countRunInputRun_proven : CountRunInputRun := by
  intro α kf xs ms
  match xs with
  | [] => exact ⟨[], [], by simp [countRun], trivial, trivial⟩
  | x0 :: rest =>
    simp only [countRun]
    have hsp := ascTake_spec (ltOf kf) x0 rest ms
    have hnd := ascTake_nonDec kf x0 rest ms
    have hbr := ascTake_break (ltOf kf) x0 rest ms
    generalize ascTake (ltOf kf) x0 rest ms = A at hsp hnd hbr
    obtain ⟨t, r, ms1⟩ := A
    simp only at hsp hnd hbr ⊢
    subst hsp
    match r with
    | [] => exact ⟨[], x0 :: t, by simp, trivial, by simpa using hnd⟩
    | y :: r' =>
      simp only
      have hy := hbr y r' rfl
      simp only [ltOf, decide_eq_true_eq] at hy
      generalize hE : (if (x0 :: t).length > 1 then
          islt (ltOf kf) ms1 x0 ((x0 :: t).getLast (by simp)) else (false, ms1)) = E
      obtain ⟨early, ms2⟩ := E
      cases early
      · simp only [Bool.false_eq_true, ↓reduceIte]
        -- not ascending: x0 :: t is all equal
        have hflat : NonInc kf (x0 :: t) := by
          apply nonDec_flat kf x0 t hnd
          by_cases hl : (x0 :: t).length > 1
          · rw [if_pos hl] at hE
            simp only [islt, ltOf, Prod.mk.injEq] at hE
            have := hE.1
            simp only [decide_eq_false_iff_not] at this
            omega
          · have ht : t = [] := by
              cases t with
              | nil => rfl
              | cons _ _ => simp at hl
            subst ht; simp
        have hpre : NonInc kf ((x0 :: t) ++ [y]) := nonInc_snoc kf x0 t y hflat (Int.le_of_lt hy)
        obtain ⟨c, hc1, hc2⟩ := descLoop_consumed kf (x0 :: t).reverse [y] y r' ms2
        have hdp := (descLoop_perm (ltOf kf) (x0 :: t).reverse [y] y r' ms2).length_eq
        generalize descLoop (ltOf kf) (x0 :: t).reverse [y] y r' ms2 = D at hc1 hdp ⊢
        obtain ⟨pre, r2, ms3⟩ := D
        simp only at hc1 hdp ⊢
        have hP : NonInc kf ((x0 :: t) ++ y :: c) := nonInc_append kf (x0 :: t) c y hpre hc2
        match hrun : pre.reverse with
        | [] => exact ⟨[], [], by simp, trivial, trivial⟩
        | w :: ws =>
          simp only
          have hs := ascTake_spec (ltOf kf) ((w :: ws).getLast (by simp)) r2 ms3
          have hn2 := ascTake_nonDec kf ((w :: ws).getLast (by simp)) r2 ms3
          generalize ascTake (ltOf kf) ((w :: ws).getLast (by simp)) r2 ms3 = E2 at hs hn2 ⊢
          obtain ⟨e, r3, ms4⟩ := E2
          simp only at hs hn2 ⊢
          have hlen : (w :: ws).length = (x0 :: t).length + 1 + c.length := by
            have h1 : (w :: ws).length = pre.length := by rw [← hrun]; simp
            rw [h1]
            rw [hc1, ← hs] at hdp
            simp at hdp ⊢; omega
          refine ⟨(x0 :: t) ++ y :: c, e, ?_, hP, nonDec_tail kf _ e hn2⟩
          rw [hc1, ← hs]
          have : x0 :: (t ++ y :: (c ++ (e ++ r3))) = ((x0 :: t) ++ y :: c ++ e) ++ r3 := by simp
          rw [this, List.take_left' (by simp [hlen]; omega)]
      · simp only [↓reduceIte]
        exact ⟨[], x0 :: t, by simp, trivial, hnd⟩

end PyLean.ListSort
