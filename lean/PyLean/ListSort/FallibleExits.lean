import PyLean.ListSort.FallibleSort

/-! # Each `goto fail` passes the exception on, with the array the C code leaves -/

namespace PyLean.ListSort

open PyLean

variable {α : Type}

/-- The failure exits of the sort's pieces, for a comparison that raises `e`:

* `gallop_left`/`gallop_right` return the error after their first comparison (:2158, :2247);
* `merge_at` returns it from its first gallop with the runs untouched (:2650-2651);
* `merge_lo` has already moved B's first item to the front (:2366) and copies the rest of A back on
  `Fail` (:2461-2463): `b₀ :: A ++ rest of B`;
* `merge_hi` has already moved A's last item to the end (:2498) and copies the rest of B back
  (:2601-2603): `A without its last ++ B ++ [A's last]`;
* `binarysort` fails on the first pivot's search with nothing moved (:1914, :1951);
* `count_run` fails on its first comparison with nothing moved (:2004-2006, :2058-2059).

A version that swallowed any of these errors (treating it as `false`) would fail the statement. -/
def SortFailExits : Prop :=
  ∀ (α : Type) (e : PyExc) (key a b x y : α) (A B rest : List α) (get : Nat → α) (n hint ok : Nat) (ms : MS),
    let lt : PLt α := fun _ _ => .error e
    gallopLeftF lt key get n hint ms = (.error e, { ms with ncmp := ms.ncmp + 1 }) ∧
    gallopRightF lt key get n hint ms = (.error e, { ms with ncmp := ms.ncmp + 1 }) ∧
    (∃ ms', mergeAtF lt A (b :: B) ms = (A ++ b :: B, ms', some e)) ∧
    (B ≠ [] → 2 ≤ A.length → ∃ ms', mergeLoF lt A (b :: B) ms = (b :: (A ++ B), ms', some e)) ∧
    (2 ≤ B.length → ∃ ms', mergeHiF lt (A ++ [a]) B ms = (A ++ B ++ [a], ms', some e) ∨ A = []) ∧
    ((if ok = 0 then 1 else ok) < n → n ≤ A.length → ∃ ms', binarysortF lt A n ok ms = (A, ms', some e)) ∧
    (∃ ms', countRunF lt (x :: y :: rest) ms = (0, x :: y :: rest, ms', some e))

theorem sortFailExits_proven : SortFailExits := by
  intro α e key a b x y A B rest get n hint ok ms lt
  refine ⟨rfl, rfl, ⟨_, rfl⟩, fun hB hA => ?_, fun hB => ?_, fun hn hA => ?_, ⟨_, rfl⟩⟩
  · simp only [mergeLoF]
    rw [if_neg hB, if_neg (by omega)]
    match A, hA with
    | a0 :: a1 :: As, _ =>
      match B, hB with
      | b1 :: Bs, _ => exact ⟨_, rfl⟩
  · by_cases hA : A = []
    · exact ⟨ms, Or.inr hA⟩
    · simp only [mergeHiF, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append]
      have hAr : A.reverse ≠ [] := by simpa using hA
      rw [if_neg hAr, if_neg (by omega)]
      have hBr : B.reverse ≠ [] := by
        intro h; rw [List.reverse_eq_nil_iff] at h; subst h; simp at hB
      obtain ⟨c0, Bc, hbr⟩ : ∃ c0 Bc, B.reverse = c0 :: Bc := by
        cases hq : B.reverse with
        | nil => exact absurd hq hBr
        | cons c0 Bc => exact ⟨c0, Bc, rfl⟩
      obtain ⟨a0, Ar, har⟩ : ∃ a0 Ar, A.reverse = a0 :: Ar := by
        cases hq : A.reverse with
        | nil => exact absurd hq hAr
        | cons a0 Ar => exact ⟨a0, Ar, rfl⟩
      refine ⟨{ ms with ncmp := ms.ncmp + 1 }, Or.inl ?_⟩
      rw [hbr, har]
      have hA' : A = (a0 :: Ar).reverse := by rw [← har, List.reverse_reverse]
      have hB' : B = (c0 :: Bc).reverse := by rw [← hbr, List.reverse_reverse]
      conv => rhs; rw [hA', hB']
      rfl
  · simp only [binarysortF]
    generalize hk : (if ok = 0 then 1 else ok) = k at hn ⊢
    have hk1 : 1 ≤ k := by rw [← hk]; split <;> omega
    have hd : (A.take n).drop k = A[k]'(by omega) :: (A.take n).drop (k + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; omega)]
      simp
    rw [hd]
    simp only [bsLoopF, bsInsertF]
    have hnz : (A.take k).length ≠ 0 := by rw [List.length_take]; omega
    have hlo : 0 < (A.take k).length := by omega
    match hm : (A.take k).length, hnz with
    | m + 1, _ =>
      simp only [binLoopF, show 0 < m + 1 by omega, ↓reduceIte, notF, isltF]
      refine ⟨{ ms with ncmp := ms.ncmp + 1 }, ?_⟩
      rw [← hd, show List.take k A = List.take k (List.take n A) by
        rw [List.take_take, Nat.min_eq_left (by omega)], List.take_append_drop, List.take_append_drop]

end PyLean.ListSort
