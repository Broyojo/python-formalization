import PyLean.ListSort.Fallible
import PyLean.ListSort.Bound

/-!
# Nothing is lost when `<` raises

Every function of `Fallible.lean` leaves a permutation of its input in the array, on its success path
and on its failure path, for every comparison: the sort's promise that "the list is left in some
permutation of its input state" when a comparison raises (`binarysort`'s comment, listobject.c:1829-1831;
Doc/library/stdtypes.rst `list.sort`).
-/

namespace PyLean.ListSort

open PyLean

variable {α : Type}

/-! ## count_run -/

theorem ascTakeF_spec (lt : PLt α) :
    ∀ (prev : α) (rest : List α) (ms : MS),
      (ascTakeF lt prev rest ms).1 ++ (ascTakeF lt prev rest ms).2.1 = rest
  | _, [], _ => rfl
  | prev, z :: rest, ms => by
    simp only [ascTakeF]
    split
    · rfl
    · rfl
    · simp [ascTakeF_spec lt z rest]

theorem descLoopF_perm (lt : PLt α) :
    ∀ (done grp : List α) (prev : α) (rest : List α) (ms : MS),
      ((descLoopF lt done grp prev rest ms).1 ++ (descLoopF lt done grp prev rest ms).2.1).Perm
        (done ++ grp ++ rest)
  | done, grp, _, [], ms => by simp only [descLoopF]; perm_count
  | done, grp, prev, z :: rest, ms => by
    simp only [descLoopF]
    split
    · perm_count
    · exact (descLoopF_perm lt _ _ _ rest _).trans (by perm_count)
    · split
      · perm_count
      · perm_count
      · exact (descLoopF_perm lt _ _ _ rest _).trans (by perm_count)

theorem descLoopF_len (lt : PLt α) :
    ∀ (done grp : List α) (prev : α) (rest : List α) (ms : MS),
      done.length + grp.length ≤ (descLoopF lt done grp prev rest ms).1.length
  | done, grp, _, [], ms => by simp [descLoopF]
  | done, grp, prev, z :: rest, ms => by
    simp only [descLoopF]
    split
    · simp
    · have := descLoopF_len lt (done ++ grp.reverse) [z] z rest
        (isltF lt ms z prev).2
      rename_i heq
      simp only [heq] at this
      simp at this ⊢; omega
    · split
      · simp
      · simp
      · rename_i heq1 _ _ heq2
        have := descLoopF_len lt done (grp ++ [z]) z rest
          (isltF lt (isltF lt ms z prev).2 prev z).2
        simp only [heq1, heq2] at this
        simp at this ⊢; omega

theorem countRunF_perm (lt : PLt α) (xs : List α) (ms : MS) :
    (countRunF lt xs ms).2.1.Perm xs ∧
    ((countRunF lt xs ms).2.2.2 = none → xs ≠ [] →
      1 ≤ (countRunF lt xs ms).1 ∧ (countRunF lt xs ms).1 ≤ xs.length) := by
  match xs with
  | [] => simp [countRunF]
  | x0 :: rest =>
    simp only [countRunF]
    have hsp := ascTakeF_spec lt x0 rest ms
    generalize ascTakeF lt x0 rest ms = A at hsp
    obtain ⟨t, r, ms1, er⟩ := A
    simp only at hsp
    subst hsp
    cases er with
    | some e => simp
    | none =>
      simp only
      match r with
      | [] => simp
      | y :: r' =>
        simp only
        generalize (if (x0 :: t).length > 1 then
            isltF lt ms1 x0 ((x0 :: t).getLast (by simp)) else (Except.ok false, ms1)) = E
        obtain ⟨early, ms2⟩ := E
        rcases early with e | early
        · simp
        cases early
        · simp only
          have hd := descLoopF_perm lt (x0 :: t).reverse [y] y r' ms2
          have hdl := descLoopF_len lt (x0 :: t).reverse [y] y r' ms2
          generalize descLoopF lt (x0 :: t).reverse [y] y r' ms2 = D at hd hdl
          obtain ⟨pre, r2, ms3, er2⟩ := D
          simp only at hd hdl
          cases er2 with
          | some e =>
            simp only
            refine ⟨hd.trans (by perm_count), fun h => by simp at h⟩
          | none =>
            simp only
            have hpre : pre ≠ [] := by
              intro h; subst h; simp at hdl
            match hrun : pre.reverse with
            | [] => simp at hrun; exact absurd hrun hpre
            | w :: ws =>
              simp only
              have hsp2 := ascTakeF_spec lt ((w :: ws).getLast (by simp)) r2 ms3
              generalize ascTakeF lt ((w :: ws).getLast (by simp)) r2 ms3 = E2 at hsp2
              obtain ⟨e, r3, ms4, er3⟩ := E2
              simp only at hsp2
              subst hsp2
              have hl := hd.length_eq
              have hrl : (w :: ws).length = pre.length := by rw [← hrun]; simp
              have hp : (pre.reverse ++ e ++ r3).Perm (pre ++ (e ++ r3)) := by perm_count
              rw [hrun] at hp
              have hpp : ((w :: ws) ++ e ++ r3).Perm (x0 :: (t ++ y :: r')) :=
                hp.trans (hd.trans (by perm_count))
              cases er3 with
              | some er => exact ⟨hpp, fun h => by simp at h⟩
              | none =>
                refine ⟨hpp, fun _ _ => ⟨by simp; omega, ?_⟩⟩
                simp at hl hrl ⊢; omega
        · simp

/-! ## binarysort -/

theorem bsInsertF_perm (lt : PLt α) (sorted : List α) (p : α) (ms : MS) (s : List α) (ms' : MS)
    (h : bsInsertF lt sorted p ms = (.ok s, ms')) : s.Perm (sorted ++ [p]) := by
  simp only [bsInsertF] at h
  generalize binLoopF _ _ _ _ _ = R at h
  obtain ⟨l, ms2⟩ := R
  rcases l with e | l
  · simp at h
  · simp only [Prod.mk.injEq, Except.ok.injEq] at h
    rw [← h.1]
    apply perm_of_count; intro x
    have := count_take_drop l sorted x
    simp only [List.count_append, List.count_cons, List.count_nil] at *
    omega

theorem bsLoopF_perm (lt : PLt α) :
    ∀ (sorted ps : List α) (ms : MS), (bsLoopF lt sorted ps ms).1.Perm (sorted ++ ps)
  | sorted, [], ms => by simp [bsLoopF]
  | sorted, p :: ps, ms => by
    simp only [bsLoopF]
    generalize hB : bsInsertF lt sorted p ms = B
    obtain ⟨r, ms2⟩ := B
    rcases r with e | s
    · exact List.Perm.refl _
    · simp only
      refine (bsLoopF_perm lt _ ps _).trans ?_
      have := bsInsertF_perm lt sorted p ms s ms2 hB
      refine (this.append_right ps).trans ?_
      simp

theorem binarysortF_perm (lt : PLt α) (a : List α) (n ok : Nat) (ms : MS)
    (h : (if ok = 0 then 1 else ok) ≤ n) : (binarysortF lt a n ok ms).1.Perm a := by
  simp only [binarysortF]
  generalize hk : (if ok = 0 then 1 else ok) = k at h
  have := bsLoopF_perm lt (a.take k) ((a.take n).drop k) ms
  generalize bsLoopF lt (a.take k) ((a.take n).drop k) ms = R at this
  obtain ⟨s, ms', e⟩ := R
  simp only at this ⊢
  refine (this.append_right _).trans ?_
  have e : a.take k ++ (a.take n).drop k = a.take n := by
    conv => rhs; rw [← List.take_append_drop k (a.take n)]
    rw [List.take_take, Nat.min_eq_left h]
  rw [e, List.take_append_drop]

end PyLean.ListSort
