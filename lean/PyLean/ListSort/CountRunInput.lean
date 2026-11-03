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

/-- The descending loop stops at a strictly larger item, after a non-increasing stretch from `prev`. -/
theorem descLoop_stop (kf : α → Int) :
    ∀ (done grp : List α) (prev : α) (rest : List α) (ms : MS) (z : α) (r : List α),
      (descLoop (ltOf kf) done grp prev rest ms).2.1 = z :: r →
      ∃ c, rest = c ++ z :: r ∧ kf ((prev :: c).getLast (by simp)) < kf z
  | done, grp, prev, [], ms, z, r, h => by simp [descLoop] at h
  | done, grp, prev, w :: rest, ms, z, r, h => by
    simp only [descLoop, islt, ltOf] at h
    by_cases hw : kf w < kf prev
    · simp only [hw, decide_true, ↓reduceIte] at h
      obtain ⟨c, h1, h2⟩ := descLoop_stop kf _ _ w rest _ z r h
      exact ⟨w :: c, by rw [h1]; rfl, by rw [List.getLast_cons (by simp)]; exact h2⟩
    · simp only [hw, decide_false, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hw' : kf prev < kf w
      · simp only [hw', decide_true, ↓reduceIte, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], rfl, by simpa using hw'⟩
      · simp only [hw', decide_false, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨c, h1, h2⟩ := descLoop_stop kf _ _ w rest _ z r h
        exact ⟨w :: c, by rw [h1]; rfl, by rw [List.getLast_cons (by simp)]; exact h2⟩

/-- `count_run` (listobject.c:1972-2064) with keys compared by `<` (any strict weak order on a finite
list, as `Stable.lean` explains), on its input in the input's order: the first `n` items are a
non-increasing part `P` then a non-decreasing part `Q`, and the stopping conditions of C hold:

* an ascending run (`P` empty) is the whole slice or has at least 2 items with `lo[0] < lo[n-1]`
  (:2001-2023: otherwise the all-equal prefix is treated as descending);
* a descending run has at least 2 items (it is entered on a strict drop, :2000-2003) and ends at the end
  of the slice or at a strictly larger item (`IF_NEXT_LARGER break`, :2038-2041); equal items are
  absorbed (`++neq`), so `P` is non-increasing, not strictly decreasing;
* the ascending extension `Q` ends at the end or at a strictly smaller item (`CountRunMaximal`).

So on `[2, 1, 3, 0]` the length is 3; a `count_run` that returned 1 on a drop, or sorted the whole slice,
fails it. -/
def CountRunInputRun : Prop :=
  ∀ (α : Type) (kf : α → Int) (xs : List α) (ms : MS),
    ∃ P Q, xs.take (countRun (ltOf kf) xs ms).1 = P ++ Q ∧ NonInc kf P ∧ NonDec kf Q ∧
      (P = [] → (countRun (ltOf kf) xs ms).1 = xs.length ∨
        (2 ≤ (countRun (ltOf kf) xs ms).1 ∧ ∃ a b, xs[0]? = some a ∧
          xs[(countRun (ltOf kf) xs ms).1 - 1]? = some b ∧ kf a < kf b)) ∧
      (P ≠ [] → 2 ≤ P.length ∧ (P.length = xs.length ∨
        ∃ a b, xs[P.length - 1]? = some a ∧ xs[P.length]? = some b ∧ kf a < kf b))

theorem countRunInputRun_proven : CountRunInputRun := by
  intro α kf xs ms
  match xs with
  | [] => exact ⟨[], [], by simp [countRun], trivial, trivial, fun _ => Or.inl (by simp [countRun]),
      fun h => absurd rfl h⟩
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
    | [] => exact ⟨[], x0 :: t, by simp, trivial, by simpa using hnd, fun _ => Or.inl (by simp),
        fun h => absurd rfl h⟩
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
        have hst := descLoop_stop kf (x0 :: t).reverse [y] y r' ms2
        generalize descLoop (ltOf kf) (x0 :: t).reverse [y] y r' ms2 = D at hc1 hdp hst ⊢
        obtain ⟨pre, r2, ms3⟩ := D
        simp only at hc1 hdp hst ⊢
        have hP : NonInc kf ((x0 :: t) ++ y :: c) := nonInc_append kf (x0 :: t) c y hpre hc2
        have hstop : ((x0 :: t) ++ y :: c).length = (x0 :: (t ++ y :: r')).length ∨
            ∃ a b, (x0 :: (t ++ y :: r'))[((x0 :: t) ++ y :: c).length - 1]? = some a ∧
              (x0 :: (t ++ y :: r'))[((x0 :: t) ++ y :: c).length]? = some b ∧ kf a < kf b := by
          cases hr2 : r2 with
          | nil => left; rw [hc1, hr2]; simp
          | cons z r =>
            right
            obtain ⟨c', h1, h2⟩ := hst z r hr2
            have hcc : c' = c := by
              rw [hc1, hr2] at h1; exact (List.append_cancel_right h1).symm
            subst hcc
            have hx : x0 :: (t ++ y :: r') = ((x0 :: t) ++ y :: c') ++ z :: r := by rw [h1]; simp
            refine ⟨(y :: c').getLast (by simp), z, ?_, ?_, h2⟩
            · rw [hx, getElem?_last_split _ _ (by simp)]
              congr 1
              exact getLast_cons_append x0 t (y :: c') (by simp)
            · rw [hx, List.getElem?_append_right (by simp)]
              simp
        match hrun : pre.reverse with
        | [] =>
          exfalso
          have : pre = [] := by simpa using hrun
          subst this
          rw [hc1] at hdp
          simp at hdp; omega
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
          refine ⟨(x0 :: t) ++ y :: c, e, ?_, hP, nonDec_tail kf _ e hn2, fun h => by simp at h,
            fun _ => ⟨by simp; omega, hstop⟩⟩
          rw [hc1, ← hs]
          have : x0 :: (t ++ y :: (c ++ (e ++ r3))) = ((x0 :: t) ++ y :: c ++ e) ++ r3 := by simp
          rw [this, List.take_left' (by simp [hlen]; omega)]
      · simp only [↓reduceIte]
        by_cases hl : (x0 :: t).length > 1
        · rw [if_pos hl] at hE
          simp only [islt, ltOf, Prod.mk.injEq, decide_eq_true_eq] at hE
          refine ⟨[], x0 :: t, by simp, trivial, hnd, (fun _ => Or.inr ⟨by omega, x0,
            (x0 :: t).getLast (by simp), rfl, getElem?_last_split (x0 :: t) (y :: r') (by simp), hE.1⟩),
            fun h => absurd rfl h⟩
        · rw [if_neg hl] at hE
          simp at hE

end PyLean.ListSort
