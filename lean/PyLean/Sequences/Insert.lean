import PyLean.Sequences.DequeOps

/-!
`insert(i, x)` across `list` and `collections.deque`, and against the
documented equivalent `s[i:i] = [x]`.
-/

namespace PyLean.Sequences

open PyLean
open PyLean.RangeSlice (Slice)

set_option linter.unusedSectionVars false

variable {α : Type} [Inhabited α]

theorem ins1Pos_bounds (n w : Int) (hn : 0 ≤ n) : 0 ≤ ins1Pos n w ∧ ins1Pos n w ≤ n := by
  unfold ins1Pos; dsimp only; split <;> (try split) <;> (try split) <;> omega

/-- `list.insert`: `OverflowError` outside `Py_ssize_t`, else insert at the
clipped position. -/
theorem listInsert_eq (l : List α) (i : Int) (x : α) :
    listInsert l i x = if ssizeMin ≤ i ∧ i ≤ ssizeMax then .ok (insAt l (ins1Pos l.length i).toNat x)
      else .error (.overflowError "Python int too large to convert to C ssize_t") := by
  unfold listInsert asSsize
  split <;> rfl

theorem rotLi_insert_pos (l : List α) (k : Nat) (x : α) (hk : k < l.length) :
    rotLi (-(k : Int)) (x :: rotLi k l) = insAt l k x := by
  rw [rotLi_nat _ _ hk]
  unfold rotLi rotL insAt
  have hlen : ((x :: (l.drop k ++ l.take k)).length : Int) = l.length + 1 := by
    simp only [List.length_cons, List.length_append, List.length_drop, List.length_take]; omega
  rw [hlen]
  by_cases hk0 : k = 0
  · subst hk0; simp
  rw [emod_char (-(k : Int)) ((l.length : Int) + 1 - k) _ (-1) (by omega) (by omega) (by omega)]
  have : ((l.length : Int) + 1 - k).toNat = (x :: l.drop k).length := by
    simp only [List.length_cons, List.length_drop]; omega
  rw [this, ← List.cons_append]
  exact Deque.rotL_append _ _

theorem rotLi_insert_neg (l : List α) (k : Nat) (x : α) (hk0 : 0 < k) (hk : k < l.length) :
    rotLi (k : Int) (rotLi (-(k : Int)) l ++ [x]) = insAt l (l.length - k) x := by
  have e : rotLi (-(k : Int)) l = rotL (l.length - k) l := by
    rw [show (-(k : Int)) = ((l.length - k : Nat) : Int) + (l.length : Int) * (-1) by omega,
      rotLi_add_mul, rotLi_nat _ _ (by omega)]
  rw [e]
  unfold rotL insAt
  have hlen : ((l.drop (l.length - k) ++ l.take (l.length - k) ++ [x]).length) = l.length + 1 := by
    simp only [List.length_append, List.length_drop, List.length_take, List.length_singleton]; omega
  rw [rotLi_nat _ _ (by rw [hlen]; omega)]
  have hA : (l.drop (l.length - k)).length = k := by simp only [List.length_drop]; omega
  generalize l.drop (l.length - k) = A at hA ⊢
  generalize l.take (l.length - k) = B
  rw [List.append_assoc, ← hA, Deque.rotL_append, List.append_assoc, List.singleton_append]

/-- `insert(i, x)` agrees across `list` and `deque`: for every element type,
list `l`, int `i` and `x`, `deque.insert` on any deque with items `l` (type
invariant `WF`) gives `list.insert`'s result unless the deque is full
(`maxlen == len(d)`), where it raises `IndexError("deque already at its
maximum size")` as documented (Doc/library/collections.rst:543-548); the
resulting deque keeps the invariant and `maxlen`. -/
def InsertAgree : Prop :=
  ∀ (α : Type) [Inhabited α] (l : List α) (i : Int) (x : α),
    (∀ d : Deque α, d.WF → d.items = l →
      (d.maxlen ≠ l.length → (d.insert i x).map (·.items) = listInsert l i x ∧
        ∀ d', d.insert i x = .ok d' → d'.WF ∧ d'.maxlen = d.maxlen) ∧
      (d.maxlen = l.length → ssizeMin ≤ i → i ≤ ssizeMax →
        d.insert i x = .error (.indexError "deque already at its maximum size")))

theorem dequeInsert_spec (d : Deque α) (h : d.WF) (i : Int) (x : α) (hi : ssizeMin ≤ i ∧ i ≤ ssizeMax)
    (hm : d.maxlen ≠ d.items.length) :
    ∃ d', d.insert i x = .ok d' ∧ d'.items = insAt d.items (ins1Pos d.items.length i).toNat x ∧
      d'.WF ∧ d'.maxlen = d.maxlen := by
  have hroom : d.maxlen < 0 ∨ (d.items.length : Int) + 1 ≤ d.maxlen := by
    rcases h.2 with h2 | h2
    · left; omega
    · right; rw [Deque.size_eq] at h2; omega
  unfold Deque.insert Deque.insertC
  simp only [asSsize, bind, Except.bind]
  rw [iteT hi]
  simp only [pure, Except.pure]
  rw [iteF (by rw [Deque.size_eq]; exact hm)]
  have hlen0 : (0 : Int) ≤ d.items.length := by omega
  by_cases h1 : i ≥ d.size
  · rw [iteT h1]
    obtain ⟨w, it, m⟩ := Deque.append_spec d x h
    refine ⟨_, rfl, ?_, w, m⟩
    rw [Deque.size_eq] at h1
    have hp : ins1Pos d.items.length i = d.items.length := by
      unfold ins1Pos; dsimp only; split <;> (try split) <;> (try split) <;> omega
    rw [it, keepLast_of_le _ _ (by simp only [List.length_append, List.length_singleton]; omega), hp]
    unfold insAt
    rw [show (d.items.length : Int).toNat = d.items.length by omega, List.take_length, List.drop_length]
  rw [iteF h1]
  by_cases h2 : i ≤ -d.size ∨ i = 0
  · rw [iteT h2]
    obtain ⟨w, it, m⟩ := Deque.appendleft_spec d x h
    refine ⟨_, rfl, ?_, w, m⟩
    rw [Deque.size_eq] at h2
    have hp : ins1Pos d.items.length i = 0 := by
      unfold ins1Pos; dsimp only; split <;> (try split) <;> (try split) <;> omega
    rw [it, keepFirst_of_le _ _ (by simp only [List.length_cons]; omega), hp]
    simp [insAt]
  rw [iteF h2]
  rw [Deque.size_eq] at h1 h2
  obtain ⟨d1, r1, w1, i1, m1⟩ := Deque.rotateC_wf d (-i) h
  rw [r1]
  simp only
  by_cases hneg : i < 0
  · rw [iteT hneg]
    obtain ⟨w2, it2, m2⟩ := Deque.append_spec d1 x w1
    obtain ⟨d3, r3, w3, i3, m3⟩ := Deque.rotateC_wf (d1.append x) i w2
    refine ⟨d3, r3, ?_, w3, by rw [m3, m2, m1]⟩
    have hl1 : ((d1.items ++ [x]).length : Int) ≤ d1.maxlen ∨ d1.maxlen < 0 := by
      rw [i1, m1]; simp only [List.length_append, List.length_singleton, length_rotLi]; omega
    rw [i3, it2, keepLast_of_le _ _ (hl1.symm), i1]
    have := rotLi_insert_neg d.items (-i).toNat x (by omega) (by omega)
    rw [show (((-i).toNat : Nat) : Int) = -i by omega, Int.neg_neg] at this
    rw [Int.neg_neg, this]
    have hp : ins1Pos d.items.length i = i + d.items.length := by
      unfold ins1Pos; dsimp only; split <;> (try split) <;> (try split) <;> omega
    rw [hp]
    congr 1; omega
  · rw [iteF hneg]
    obtain ⟨w2, it2, m2⟩ := Deque.appendleft_spec d1 x w1
    obtain ⟨d3, r3, w3, i3, m3⟩ := Deque.rotateC_wf (d1.appendleft x) i w2
    refine ⟨d3, r3, ?_, w3, by rw [m3, m2, m1]⟩
    have hl1 : ((x :: d1.items).length : Int) ≤ d1.maxlen ∨ d1.maxlen < 0 := by
      rw [i1, m1]; simp only [List.length_cons, length_rotLi]; omega
    rw [i3, it2, keepFirst_of_le _ _ (hl1.symm), i1]
    have := rotLi_insert_pos d.items i.toNat x (by omega)
    rw [show ((i.toNat : Nat) : Int) = i by omega] at this
    rw [Int.neg_neg, this]
    have hp : ins1Pos d.items.length i = i := by
      unfold ins1Pos; dsimp only; split <;> (try split) <;> (try split) <;> omega
    rw [hp]

theorem insertAgree_proven : InsertAgree := by
  intro α _ l i x d hd hl
  refine ⟨fun hm => ?_, fun hm hi0 hi1 => ?_⟩
  · rw [listInsert_eq]
    subst hl
    by_cases hi : ssizeMin ≤ i ∧ i ≤ ssizeMax
    · obtain ⟨d', hr, hi', w, m⟩ := dequeInsert_spec d hd i x hi hm
      rw [hr, iteT hi, ← hi']
      exact ⟨rfl, fun d'' he => by simp only [Except.ok.injEq] at he; subst he; exact ⟨w, m⟩⟩
    · rw [iteF hi]
      have : d.insert i x = .error (.overflowError "Python int too large to convert to C ssize_t") := by
        simp only [Deque.insert, asSsize, bind, Except.bind]; rw [iteF hi]
      rw [this]
      exact ⟨rfl, fun d'' he => nomatch he⟩
  · subst hl
    simp only [Deque.insert, Deque.insertC, asSsize, bind, Except.bind]
    rw [iteT ⟨hi0, hi1⟩]
    simp only [Deque.size_eq, hm]
    rfl

/-! ### `insert` against `s[i:i] = [x]` -/

/-- `list.insert(i, x)` "is equivalent to writing `sequence[index:index] =
[value]`" (Doc/library/stdtypes.rst@3.14.7:1336-1343), for every int `i`. -/
def InsertIsSliceAssign : Prop :=
  ∀ (α : Type) [Inhabited α] (l : List α) (i : Int) (x : α), (l.length : Int) ≤ ssizeMax →
    listInsert l i x = listAssSubscript l ⟨some i, some i, none⟩ (some [x])

/-- The same, for `i` inside `Py_ssize_t`. -/
def InsertIsSliceAssignSsize : Prop :=
  ∀ (α : Type) [Inhabited α] (l : List α) (i : Int) (x : α), (l.length : Int) ≤ ssizeMax →
    ssizeMin ≤ i → i ≤ ssizeMax →
    listInsert l i x = listAssSubscript l ⟨some i, some i, none⟩ (some [x])

theorem insertIsSliceAssign_refuted : ¬ InsertIsSliceAssign := by
  intro h
  have := h Int [] (2 ^ 63) 0 (by decide)
  revert this
  decide

theorem insertIsSliceAssignSsize_proven : InsertIsSliceAssignSsize := by
  intro α _ l i x hlen hi0 hi1
  rw [listInsert_eq, iteT ⟨hi0, hi1⟩]
  have hc : RangeSlice.clampSsize i = i := by
    unfold RangeSlice.clampSsize; rw [iteF (by omega), iteF (by omega)]
  simp only [listAssSubscript, adjustSlice, RangeSlice.sliceUnpack, hc, bind, Except.bind, pure,
    Except.pure, RangeSlice.adjustIndices, RangeSlice.adjustOne]
  simp only [show ¬ ((1 : Int) < 0) by decide, ite_false, show (1 : Int) > 0 by decide, ite_true]
  unfold listAssSlice insAt ins1Pos
  dsimp only
  have hn : (0 : Int) ≤ l.length := by omega
  generalize hp : (if i < 0 then (if i + (l.length : Int) < 0 then 0 else i + l.length)
    else if i ≥ (l.length : Int) then (l.length : Int) else i) = p
  have hp' : 0 ≤ p ∧ p ≤ l.length := by rw [← hp]; split <;> (try split) <;> omega
  have e1 : (if (if i < 0 then (if i + (l.length : Int) < 0 then 0 else i + l.length) else i) > (l.length : Int)
      then (l.length : Int) else (if i < 0 then (if i + (l.length : Int) < 0 then 0 else i + l.length) else i)) = p := by
    rw [← hp]; split <;> (try split) <;> (try split) <;> (try split) <;> omega
  have e2 : (if p < 0 then 0 else if p > (l.length : Int) then (l.length : Int) else p) = p := by
    split <;> (try split) <;> omega
  rw [e1, e2]
  simp only [show ¬ (p < p) by omega, show ¬ (p > p) by omega, and_false, or_false, ite_false,
    show ¬ (p > (l.length : Int)) by omega, List.append_assoc, List.singleton_append]

end PyLean.Sequences
