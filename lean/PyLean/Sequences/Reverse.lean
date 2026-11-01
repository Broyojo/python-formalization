import PyLean.Sequences.DequeOps

/-!
`deque.reverse()`: the two-cursor swap loop over the blocks reverses the items.
-/

namespace PyLean.Sequences

open PyLean

set_option linter.unusedSectionVars false

variable {α : Type} [Inhabited α]

/-- The items after `k` swaps of the outermost pairs. -/
def swapped (k : Nat) (l : List α) : List α :=
  (List.range l.length).map (fun j => if j < k ∨ l.length - k ≤ j then ix l (l.length - 1 - j : Nat) else ix l j)

theorem length_swapped (k : Nat) (l : List α) : (swapped k l).length = l.length := by
  simp [swapped]

theorem swapped_zero (l : List α) : swapped 0 l = l := by
  apply List.ext_getElem?
  intro j
  unfold swapped
  rw [List.getElem?_map]
  by_cases hj : j < l.length
  · rw [List.getElem?_range hj]
    simp only [Nat.not_lt_zero, false_or, Option.map_some, Nat.sub_zero]
    rw [iteF (by omega)]
    unfold ix; rw [List.getD_eq_getElem?_getD, show ((j : Int)).toNat = j by omega, List.getElem?_eq_getElem hj]
    simp [List.getElem?_eq_getElem hj]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]; rfl

theorem swapped_half (l : List α) : swapped (l.length / 2) l = l.reverse := by
  apply List.ext_getElem?
  intro j
  unfold swapped
  rw [List.getElem?_map]
  by_cases hj : j < l.length
  · rw [List.getElem?_range hj, List.getElem?_reverse hj]
    simp only [Option.map_some]
    rw [List.getElem?_eq_getElem (by omega)]
    congr 1
    split
    · rw [ix_getElem _ _ (by omega)]
    · rw [ix_getElem _ _ hj]; congr 1; omega
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]; rfl

theorem swapped_step (l : List α) (k : Nat) (hk : k < l.length / 2) :
    ((swapped k l).set k (ix (swapped k l) (l.length - 1 - k : Nat))).set (l.length - 1 - k)
      (ix (swapped k l) k) = swapped (k + 1) l := by
  have hn := length_swapped k l
  have g : ∀ (k' j : Nat), j < l.length → (swapped k' l)[j]? =
      some (if j < k' ∨ l.length - k' ≤ j then ix l (l.length - 1 - j : Nat) else ix l j) := by
    intro k' j hj
    unfold swapped
    rw [List.getElem?_map, List.getElem?_range hj]; rfl
  have gi : ∀ (k' j : Nat), j < l.length → ix (swapped k' l) j =
      (if j < k' ∨ l.length - k' ≤ j then ix l (l.length - 1 - j : Nat) else ix l j) := by
    intro k' j hj
    unfold ix
    rw [List.getD_eq_getElem?_getD, show ((j : Int)).toNat = j by omega, g k' j hj]
    rfl
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set, List.getElem?_set, List.length_set, hn]
  by_cases hj : j < l.length
  · rw [g (k + 1) j hj]
    by_cases h1 : l.length - 1 - k = j
    · subst h1
      rw [iteT (show l.length - 1 - k = l.length - 1 - k from rfl),
        iteT (show l.length - 1 - k < l.length by omega),
        gi k k (by omega), iteF (show ¬ (k < k ∨ l.length - k ≤ k) by omega),
        iteT (show (l.length - 1 - k < k + 1 ∨ l.length - (k + 1) ≤ l.length - 1 - k) by omega)]
      congr 2; omega
    · rw [iteF h1]
      by_cases h2 : k = j
      · subst h2
        rw [iteT (show k = k from rfl), iteT (show k < l.length by omega),
          gi k (l.length - 1 - k) (by omega),
          iteF (show ¬ (l.length - 1 - k < k ∨ l.length - k ≤ l.length - 1 - k) by omega),
          iteT (show (k < k + 1 ∨ l.length - (k + 1) ≤ k) by omega)]
      · rw [iteF h2, g k j hj]
        congr 1
        by_cases h3 : j < k ∨ l.length - k ≤ j
        · rw [iteT h3, iteT (show j < k + 1 ∨ l.length - (k + 1) ≤ j by omega)]
        · rw [iteF h3, iteF (show ¬ (j < k + 1 ∨ l.length - (k + 1) ≤ j) by omega)]
  · rw [iteF (show ¬ (l.length - 1 - k = j) by omega), iteF (show ¬ (k = j) by omega),
      List.getElem?_eq_none (by rw [length_swapped]; omega),
      List.getElem?_eq_none (by rw [length_swapped]; omega)]

namespace Deque

theorem write_items (d : Deque α) (b j : Int) (v : α) (d' : Deque α) (h : d.write b j v = .ok d') :
    d'.left = d.left ∧ d'.right = d.right ∧ d'.maxlen = d.maxlen ∧
      d'.items = d.items.set (b * 64 + j - d.left).toNat v := by
  unfold write at h
  split at h
  · exact nomatch h
  · simp only at h
    split at h
    · simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl⟩
    · exact nomatch h

theorem reverseLoop_spec (l : List α) : ∀ (m : Nat) (d : Deque α) (k : Nat) (lb li rb ri : Int),
    d.Layout → d.items = swapped k l → l.length = d.items.length →
    lb * 64 + li - d.left = k → 0 ≤ li → li < 64 →
    rb * 64 + ri - d.left = (l.length - 1 - k : Nat) → 0 ≤ ri → ri < 64 →
    k + m = l.length / 2 →
    ∃ d', d.reverseLoop m lb li rb ri = .ok d' ∧ d'.items = l.reverse ∧ d'.left = d.left ∧
      d'.right = d.right ∧ d'.maxlen = d.maxlen := by
  intro m
  induction m with
  | zero =>
    intro d k lb li rb ri _ hi _ _ _ _ _ _ _ hk
    refine ⟨d, rfl, ?_, rfl, rfl, rfl⟩
    rw [hi, show k = l.length / 2 by omega, swapped_half]
  | succ m ih =>
    intro d k lb li rb ri hL hi hlen hlp hl0 hl1 hrp hr0 hr1 hk
    have h' := hL
    rw [layout_iff] at h'
    simp only [reverseLoop, bind, Except.bind]
    rw [read_ok d hL lb li (by dq_omega) (by dq_omega) hl0 hl1 (by omega) (by dq_omega)]
    rw [read_ok d hL rb ri (by dq_omega) (by dq_omega) hr0 hr1 (by omega) (by dq_omega)]
    simp only
    rw [write_ok d lb li _ (by dq_omega) (by dq_omega) hl0 hl1 (by omega) (by dq_omega)]
    try simp only
    rw [write_ok _ rb ri _ (by (try simp only [rbNum, size_eq, List.length_set] at *) <;> omega)
      (by (try simp only [rbNum, size_eq, List.length_set] at *) <;> omega) hr0 hr1
      (by (try simp only at *) <;> omega)
      (by (try simp only [size_eq, List.length_set] at *) <;> omega)]
    try simp only
    rw [hlp, hrp, show ((k : Int)).toNat = k by omega,
      show (((l.length - 1 - k : Nat) : Int)).toNat = l.length - 1 - k by omega]
    have hk2 : k < l.length / 2 := by omega
    have hst := swapped_step l k hk2
    rw [← hi] at hst
    obtain ⟨c1, c2, c3⟩ := step1_pos d lb li k hlp hl0 hl1
    have hL2 : ({ d with items := ((d.items.set k (ix d.items ((l.length - 1 - k : Nat) : Int))).set (l.length - 1 - k) (ix d.items (k : Int))) } : Deque α).Layout := by
      rw [layout_iff]; simp only [List.length_set]; exact h'
    obtain ⟨d', h3, h4, h5, h6, h7⟩ := ih _ (k + 1) (step1 lb li).1 (step1 lb li).2
      (if ri - 1 < 0 then (rb - 1, 64 - 1) else (rb, ri - 1)).1
      (if ri - 1 < 0 then (rb - 1, 64 - 1) else (rb, ri - 1)).2
      hL2 hst (by simp only [List.length_set]; exact hlen) (by simp only; rw [c1]; omega) c2 c3
      (by split <;> simp only <;> omega) (by split <;> simp only <;> omega)
      (by split <;> simp only <;> omega) (by omega)
    exact ⟨d', h3, h4, h5, h6, h7⟩

end Deque

/-- `d.reverse()` reverses the items in place (Doc/library/collections.rst:571-575):
for every deque with the layout invariant, the two-cursor swap loop over the
blocks (`deque_reverse_impl`) only touches used slots and leaves exactly the
reversed items, with the layout and `maxlen` unchanged. -/
def DequeReverse : Prop :=
  ∀ (α : Type) [Inhabited α] (d : Deque α), d.WF → ∃ d', d.reverse = .ok d' ∧ d'.items = d.items.reverse ∧ d'.WF ∧
    d'.maxlen = d.maxlen

theorem dequeReverse_proven : DequeReverse := by
  intro α _ d h
  have h' := h.1
  rw [Deque.layout_iff] at h'
  unfold Deque.reverse
  by_cases hne : d.items = []
  · refine ⟨d, ?_, by rw [hne]; rfl, h, rfl⟩
    simp [hne, Deque.reverseLoop]
  have hlen := List.length_pos_iff.mpr hne
  obtain ⟨d', h1, h2, h3, h4, h5⟩ := Deque.reverseLoop_spec d.items (d.items.length / 2) d 0 0 d.left d.rbNum
    d.right h.1 (swapped_zero _).symm rfl (by omega) h'.1 h'.2.1 (by dq_omega) h'.2.2.1 h'.2.2.2.1 (by omega)
  refine ⟨d', h1, h2, ⟨?_, ?_⟩, h5⟩
  · rw [Deque.layout_iff, h3, h4, h2, List.length_reverse]; exact h'
  · rw [Deque.maxOk_iff, h5, h2, List.length_reverse]; exact h.2

end PyLean.Sequences
