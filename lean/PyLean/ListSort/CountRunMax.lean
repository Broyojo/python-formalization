import PyLean.ListSort.Props

/-! # `count_run` finds the whole run -/

namespace PyLean.ListSort

variable {α : Type}

/-- The ascending scan stops only at the end or at an item smaller than the last one taken. -/
theorem ascTake_break (lt : α → α → Bool) :
    ∀ (prev : α) (rest : List α) (ms : MS) (z : α) (r : List α),
      (ascTake lt prev rest ms).2.1 = z :: r →
      lt z ((prev :: (ascTake lt prev rest ms).1).getLast (by simp)) = true
  | _, [], _, _, _, h => by simp [ascTake] at h
  | prev, w :: rest, ms, z, r, h => by
    simp only [ascTake, islt] at h ⊢
    by_cases hw : lt w prev = true
    · simp only [hw, ↓reduceIte] at h ⊢
      simp only [List.cons.injEq] at h
      rw [← h.1]; simpa using hw
    · have hw' : lt w prev = false := by simpa using hw
      simp only [hw', Bool.false_eq_true, ↓reduceIte] at h ⊢
      have := ascTake_break lt w rest _ z r h
      rw [List.getLast_cons (by simp)]
      exact this

theorem getElem?_last_split (l1 l2 : List α) (h : l1 ≠ []) :
    (l1 ++ l2)[l1.length - 1]? = some (l1.getLast h) := by
  have hpos : 0 < l1.length := by
    cases l1 with
    | nil => exact absurd rfl h
    | cons a as => simp
  rw [List.getElem?_append_left (by omega), List.getLast_eq_getElem]
  exact List.getElem?_eq_getElem _

theorem getLast_cons_append (w : α) (ws e : List α) (h : e ≠ []) :
    (w :: (ws ++ e)).getLast (by simp) = e.getLast h := by
  induction ws generalizing w with
  | nil =>
    cases e with
    | nil => exact absurd rfl h
    | cons a as => simp only [List.nil_append]; rw [List.getLast_cons (by simp)]
  | cons v vs ih => simp only [List.cons_append]; rw [List.getLast_cons (by simp)]; exact ih v

/-- `count_run(ms, slo, nremaining)` (listobject.c:1972-2064) returns the whole run, for every
comparison: either the run is the rest of the slice, or the item after it is smaller than the run's
last item, which is the only condition on which each of its loops stops (`IF_NEXT_SMALLER break`,
:2004-2006, :2052-2055; the descending loop's `IF_NEXT_LARGER` is followed by the ascending one).
With `CountRunSpec` (the run is sorted) this pins the length; a `count_run` that returned 1 fails it
on `[1, 2]`. -/
def CountRunMaximal : Prop :=
  ∀ (α : Type) (lt : α → α → Bool) (xs : List α) (ms : MS), xs ≠ [] →
    (countRun lt xs ms).1 = xs.length ∨
    ∃ a b, (countRun lt xs ms).2.1[(countRun lt xs ms).1]? = some a ∧
      (countRun lt xs ms).2.1[(countRun lt xs ms).1 - 1]? = some b ∧ lt a b = true

theorem countRunMaximal_proven : CountRunMaximal := by
  intro α lt xs ms hne
  match xs with
  | x0 :: rest =>
    have hp := (countRun_perm lt (x0 :: rest) ms).1
    simp only [countRun] at hp ⊢
    have hsp := ascTake_spec lt x0 rest ms
    have hbr := ascTake_break lt x0 rest ms
    generalize ascTake lt x0 rest ms = A at hsp hbr hp
    obtain ⟨t, r, ms1⟩ := A
    simp only at hsp hbr hp ⊢
    subst hsp
    match r with
    | [] => left; simp
    | y :: r' =>
      simp only at hp ⊢
      have hb := hbr y r' rfl
      generalize hE : (if (x0 :: t).length > 1 then
          islt lt ms1 x0 ((x0 :: t).getLast (by simp)) else (false, ms1)) = E at hp ⊢
      obtain ⟨early, ms2⟩ := E
      cases early
      · simp only [Bool.false_eq_true, ↓reduceIte] at hp ⊢
        have hsp2 := fun w ws => ascTake_spec lt ((w :: ws).getLast (by simp))
        have hbr2 := fun w ws => ascTake_break lt ((w :: ws).getLast (by simp))
        have hdl := descLoop_len lt (x0 :: t).reverse [y] y r' ms2
        generalize descLoop lt (x0 :: t).reverse [y] y r' ms2 = D at hp hdl ⊢
        obtain ⟨pre, r2, ms3⟩ := D
        simp only at hp hdl ⊢
        match hrun : pre.reverse with
        | [] =>
          exfalso
          have : pre = [] := by simpa using hrun
          subst this; simp at hdl
        | w :: ws =>
          simp only [hrun] at hp ⊢
          have hs := hsp2 w ws r2 ms3
          have hbk := hbr2 w ws r2 ms3
          generalize ascTake lt ((w :: ws).getLast (by simp)) r2 ms3 = E2 at hs hbk hp ⊢
          obtain ⟨e, r3, ms4⟩ := E2
          simp only at hs hbk hp ⊢
          have hl := hp.length_eq
          match r3 with
          | [] => left; simp at hl ⊢; omega
          | z :: r3' =>
            right
            have hz := hbk z r3' rfl
            refine ⟨z, ((w :: ws).getLast (by simp) :: e).getLast (by simp), ?_, ?_, hz⟩
            · rw [List.append_assoc, show (w :: ws).length + e.length = ((w :: ws) ++ e).length by
                  rw [List.length_append], ← List.append_assoc, List.getElem?_append_right (by simp)]
              simp
            · have hne2 : (w :: ws) ++ e ≠ [] := by simp
              rw [show (w :: ws).length + e.length - 1 = ((w :: ws) ++ e).length - 1 by
                  rw [List.length_append], getElem?_last_split _ _ hne2]
              congr 1
              cases e with
              | nil => simp
              | cons e0 es =>
                have h1 : ((w :: ws) ++ e0 :: es).getLast hne2 = (e0 :: es).getLast (by simp) :=
                  getLast_cons_append w ws (e0 :: es) (by simp)
                rw [h1]
                exact (List.getLast_cons (by simp)).symm
      · simp only [↓reduceIte]
        right
        refine ⟨y, (x0 :: t).getLast (by simp), ?_, ?_, hb⟩
        · rw [show (x0 :: t).length = (x0 :: t).length + 0 by rfl]
          simp
        · have := getElem?_last_split (x0 :: t) (y :: r') (by simp)
          simpa using this

end PyLean.ListSort
