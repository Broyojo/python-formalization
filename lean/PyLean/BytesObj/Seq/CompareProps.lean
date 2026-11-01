import PyLean.BytesObj.Seq.SearchProps

/-!
`list_richcompare_impl` against `tuple_richcompare`. The note at tupleobject.c:753-758
says lists have an early out for `==` and `!=` on different lengths that tuples
lack. `CompareAgree` says that this is the only difference, for every comparison,
including one that raises (where the early out shows: `[x] == [x, y]` never calls
`x.__eq__`, while `(x,) == (x, y)` does).
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α ρ : Type}

theorem tupleFirstDiff_nil_left (E : ElemOps α ρ) (w : List α) : tupleFirstDiff E [] w = .ok none := by
  cases w <;> simp [tupleFirstDiff]

theorem tupleFirstDiff_nil_right (E : ElemOps α ρ) (v : List α) : tupleFirstDiff E v [] = .ok none := by
  cases v <;> simp [tupleFirstDiff]

/-- The pure search loop of a list comparison, in terms of the tuple's. -/
theorem cmpLoop_pure (E : ElemOps α ρ) (v w : List α) (f i : Nat)
    (hi : i ≤ min v.length w.length) (hf : min v.length w.length < i + f) :
    match tupleFirstDiff E (v.drop i) (w.drop i) with
    | .error e => cmpLoop E.same (pureCmp2 E) f (i : Int) (v, w) = (.error e, (v, w))
    | .ok none => cmpLoop E.same (pureCmp2 E) f (i : Int) (v, w) = (.ok (min v.length w.length : Nat), (v, w))
    | .ok (some (x, y)) =>
      ∃ j : Nat, cmpLoop E.same (pureCmp2 E) f (i : Int) (v, w) = (.ok (j : Int), (v, w)) ∧
        j < v.length ∧ j < w.length ∧ v[j]? = some x ∧ w[j]? = some y := by
  induction f generalizing i with
  | zero => omega
  | succ f ih =>
    have hnext : ((i + 1 : Nat) : Int) = (i : Int) + 1 := by omega
    by_cases hlt : i < v.length ∧ i < w.length
    · obtain ⟨hv, hw⟩ := hlt
      have hvg : v[i]? = some v[i] := List.getElem?_eq_getElem hv
      have hwg : w[i]? = some w[i] := List.getElem?_eq_getElem hw
      rw [drop_cons_of_lt v i hv, drop_cons_of_lt w i hw]
      simp only [tupleFirstDiff]
      have hc1 : ((i : Int) < (v.length : Int) ∧ (i : Int) < (w.length : Int)) := by omega
      have hIH := ih (i + 1) (by omega) (by omega)
      rw [hnext] at hIH
      by_cases hs : E.same v[i] w[i] = true
      · have hr : richBool E .eq v[i] w[i] = .ok true := by simp [richBool, hs]
        rw [hr]
        simp only
        rw [cmpLoop, if_pos hc1]
        simp only [slot_nat, hvg, hwg, hs, if_true]
        exact hIH
      · cases hc : richBool E .eq v[i] w[i] with
        | error e =>
          simp only
          rw [cmpLoop, if_pos hc1]
          simp only [slot_nat, hvg, hwg, hs, if_false, pureCmp2, hc]
          rfl
        | ok b =>
          cases b with
          | true =>
            simp only
            rw [cmpLoop, if_pos hc1]
            simp only [slot_nat, hvg, hwg, hs, if_false, pureCmp2, hc]
            exact hIH
          | false =>
            simp only
            refine ⟨i, ?_, hv, hw, hvg, hwg⟩
            rw [cmpLoop, if_pos hc1]
            simp only [slot_nat, hvg, hwg, hs, if_false, pureCmp2, hc]
            rfl
    · have hmin : i = min v.length w.length := by omega
      have hnone : tupleFirstDiff E (v.drop i) (w.drop i) = .ok none := by
        by_cases hv : v.length ≤ i
        · rw [List.drop_eq_nil_of_le hv, tupleFirstDiff_nil_left]
        · have hw' : w.length ≤ i := by omega
          rw [List.drop_eq_nil_of_le hw', tupleFirstDiff_nil_right]
      rw [hnone]
      simp only
      have hc : ¬ ((i : Int) < (v.length : Int) ∧ (i : Int) < (w.length : Int)) := by omega
      rw [cmpLoop, if_neg hc, ← hmin]

/-- For every element type, every comparison (which may raise or return a non-bool),
every operator and all lists, when the comparison leaves the lists alone: a list
comparison is the tuple comparison, except for the early out on `==` and `!=` when
the lengths differ. That is the difference the note at tupleobject.c:753-758 states,
and it is the only one. The explicit identity skip of listobject.c:3482 changes
nothing, since `PyObject_RichCompareBool` has the same shortcut. -/
def CompareAgree : Prop :=
  ∀ (α ρ : Type) (E : ElemOps α ρ) (op : CmpOp) (v w : List α) (fuel : Nat),
    min v.length w.length < fuel →
    (listRichcompare E (pureCmp2 E) (pureFinal E) fuel op v w).1 =
      if v.length ≠ w.length ∧ (op = .eq ∨ op = .ne) then .ok (E.ofBool (decide (op = .ne)))
      else tupleRichcompare E op v w

theorem compareAgree_proven : CompareAgree := by
  intro α ρ E op v w fuel hf
  unfold listRichcompare
  by_cases hshort : (v.length ≠ w.length ∧ (op = .eq ∨ op = .ne))
  · rw [if_pos hshort, if_pos hshort]
  · rw [if_neg hshort, if_neg hshort]
    have h := cmpLoop_pure E v w fuel 0 (by omega) (by omega)
    simp only [List.drop_zero] at h
    have hzero : ((0 : Nat) : Int) = 0 := rfl
    rw [hzero] at h
    unfold tupleRichcompare
    cases hd : tupleFirstDiff E v w with
    | error e =>
      rw [hd] at h
      simp only at h
      rw [h]
    | ok r =>
      cases r with
      | none =>
        rw [hd] at h
        simp only at h
        rw [h]
        have hc : ((min v.length w.length : Nat) : Int) ≥ v.length ∨
            ((min v.length w.length : Nat) : Int) ≥ w.length := by omega
        simp only [if_pos hc]
      | some p =>
        obtain ⟨x, y⟩ := p
        rw [hd] at h
        simp only at h
        obtain ⟨j, hj, hjv, hjw, hx, hy⟩ := h
        rw [hj]
        have hc : ¬ ((j : Int) ≥ v.length ∨ (j : Int) ≥ w.length) := by omega
        simp only [if_neg hc]
        by_cases he : op = .eq
        · simp [he]
        · by_cases hn : op = .ne
          · simp [hn]
          · simp only [he, hn, if_false, slot_nat, hx, hy, pureFinal]

/-- Every comparison of two tuples that share a prefix of identical objects behaves
as the comparison of what follows. In particular a tuple or list holding a NaN-like
object equals itself, because identity implies equality here (documented at
Doc/reference/expressions.rst, "value comparisons", for built-in collections). -/
def CompareReflexive : Prop :=
  ∀ (α ρ : Type) (E : ElemOps α ρ) (v : List α), (∀ x ∈ v, E.same x x = true) →
    tupleRichcompare E .eq v v = .ok (E.ofBool true)

theorem compareReflexive_proven : CompareReflexive := by
  intro α ρ E v h
  have key : ∀ (l : List α), (∀ x ∈ l, E.same x x = true) → tupleFirstDiff E l l = .ok none := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons x xs ih =>
      intro hl
      have hx := hl x (by simp)
      have hr : richBool E .eq x x = .ok true := by simp [richBool, hx]
      simp only [tupleFirstDiff, hr]
      exact ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
  unfold tupleRichcompare
  rw [key v h]
  simp [cmpSizes]

end PyLean.BytesObj.Seq
