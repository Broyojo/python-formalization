import PyLean.Sequences.DequeModel

/-!
Basic facts about the deque model: the end operations preserve the layout
invariant and act on the items as the documented list operations, with
`maxlen` eviction from the opposite end.
-/

namespace PyLean.Sequences

open PyLean

set_option linter.unusedSectionVars false

variable {α : Type} [Inhabited α]

/-- Keep the last `maxlen` items (all of them when `maxlen < 0`): what a
bounded deque retains after items are added on the right. -/
def keepLast (maxlen : Int) (l : List α) : List α :=
  if maxlen < 0 then l else l.drop (l.length - maxlen.toNat)

/-- Keep the first `maxlen` items: after items are added on the left. -/
def keepFirst (maxlen : Int) (l : List α) : List α :=
  if maxlen < 0 then l else l.take maxlen.toNat

namespace Deque

theorem size_eq (d : Deque α) : d.size = (d.items.length : Int) := rfl

theorem layout_iff (d : Deque α) : d.Layout ↔
    (0 ≤ d.left ∧ d.left < 64 ∧ 0 ≤ d.right ∧ d.right < 64 ∧
      (d.left + (d.items.length : Int) - 1) % 64 = d.right ∧
      ((d.items.length : Int) = 0 → d.left = d.right + 1)) := Iff.rfl

theorem popleft_spec (d : Deque α) (h : d.Layout) (hne : d.items ≠ []) :
    ∃ d', d.popleft = .ok (ix d.items 0, d') ∧ d'.Layout ∧ d'.items = d.items.drop 1 ∧
      d'.maxlen = d.maxlen := by
  have hlen : 0 < d.items.length := List.length_pos_iff.mpr hne
  rw [layout_iff] at h
  have hs : ¬ d.size = 0 := by rw [size_eq]; omega
  unfold popleft
  rw [iteF hs]
  simp only
  split
  · split
    · refine ⟨_, rfl, ?_, rfl, rfl⟩
      rw [layout_iff]; simp only [List.length_drop, size_eq] at *
      omega
    · refine ⟨_, rfl, ?_, rfl, rfl⟩
      rw [layout_iff]; simp only [List.length_drop, CENTER, size_eq, implies_true, and_true] at *
      omega
  · refine ⟨_, rfl, ?_, rfl, rfl⟩
    rw [layout_iff]; simp only [List.length_drop, size_eq] at *
    omega

theorem pop_spec (d : Deque α) (h : d.Layout) (hne : d.items ≠ []) :
    ∃ d', d.pop = .ok (ix d.items (d.items.length - 1), d') ∧ d'.Layout ∧
      d'.items = d.items.dropLast ∧ d'.maxlen = d.maxlen := by
  have hlen : 0 < d.items.length := List.length_pos_iff.mpr hne
  rw [layout_iff] at h
  have hs : ¬ d.size = 0 := by rw [size_eq]; omega
  unfold pop
  rw [iteF hs]
  simp only [size_eq]
  split
  · split
    · refine ⟨_, rfl, ?_, rfl, rfl⟩
      rw [layout_iff]; simp only [List.length_dropLast, size_eq] at *
      omega
    · refine ⟨_, rfl, ?_, rfl, rfl⟩
      rw [layout_iff]; simp only [List.length_dropLast, CENTER, size_eq, implies_true, and_true] at *
      omega
  · refine ⟨_, rfl, ?_, rfl, rfl⟩
    rw [layout_iff]; simp only [List.length_dropLast, size_eq] at *
    omega

/-- `deque_append_lock_held`: layout kept, items are `keepLast maxlen (items ++ [x])`
when the deque respected `maxlen` before. -/
theorem appendM_spec (d : Deque α) (x : α) (maxlen : Int) (h : d.Layout)
    (hm : maxlen < 0 ∨ (d.items.length : Int) ≤ maxlen) :
    (d.appendM x maxlen).Layout ∧ (d.appendM x maxlen).items = keepLast maxlen (d.items ++ [x]) ∧
      (d.appendM x maxlen).maxlen = d.maxlen := by
  rw [layout_iff] at h
  unfold appendM
  simp only
  generalize hd1 : ({ d with items := d.items ++ [x], right := (if d.right = 64 - 1 then -1 else d.right) + 1 } : Deque α) = d1
  have hl1 : d1.Layout := by
    rw [← hd1, layout_iff]; simp only [List.length_append, List.length_singleton]
    split <;> omega
  have hi1 : d1.items = d.items ++ [x] := by rw [← hd1]
  have hm1 : d1.maxlen = d.maxlen := by rw [← hd1]
  unfold keepLast
  by_cases ht : d1.needsTrim maxlen = true
  · rw [iteT ht]
    unfold needsTrim at ht
    simp only [decide_eq_true_eq, size_eq, hi1, List.length_append, List.length_singleton] at ht
    have hne : d1.items ≠ [] := by rw [hi1]; simp
    obtain ⟨d', hp, hl, hi, hmx⟩ := popleft_spec d1 hl1 hne
    rw [hp]; simp only [snd']
    refine ⟨hl, ?_, by rw [hmx, hm1]⟩
    rw [hi, hi1, iteF (by omega)]
    congr 1; simp only [List.length_append, List.length_singleton]; omega
  · rw [iteF ht]
    unfold needsTrim at ht
    simp only [decide_eq_true_eq, size_eq, hi1, List.length_append, List.length_singleton] at ht
    subst hd1
    refine ⟨hl1, ?_, rfl⟩
    show d.items ++ [x] = _
    split
    · rfl
    · rw [show (d.items ++ [x]).length - maxlen.toNat = 0 by simp; omega]; rfl

theorem appendleftM_spec (d : Deque α) (x : α) (maxlen : Int) (h : d.Layout)
    (hm : maxlen < 0 ∨ (d.items.length : Int) ≤ maxlen) :
    (d.appendleftM x maxlen).Layout ∧ (d.appendleftM x maxlen).items = keepFirst maxlen (x :: d.items) ∧
      (d.appendleftM x maxlen).maxlen = d.maxlen := by
  rw [layout_iff] at h
  unfold appendleftM
  simp only
  generalize hd1 : ({ d with items := x :: d.items, left := (if d.left = 0 then 64 else d.left) - 1 } : Deque α) = d1
  have hl1 : d1.Layout := by
    rw [← hd1, layout_iff]; simp only [List.length_cons]
    split <;> omega
  have hi1 : d1.items = x :: d.items := by rw [← hd1]
  have hm1 : d1.maxlen = d.maxlen := by rw [← hd1]
  unfold keepFirst
  by_cases ht : d1.needsTrim maxlen = true
  · rw [iteT ht]
    unfold needsTrim at ht
    simp only [decide_eq_true_eq, size_eq, hi1, List.length_cons] at ht
    have hne : d1.items ≠ [] := by rw [hi1]; simp
    obtain ⟨d', hp, hl, hi, hmx⟩ := pop_spec d1 hl1 hne
    rw [hp]; simp only [snd']
    refine ⟨hl, ?_, by rw [hmx, hm1]⟩
    rw [hi, hi1, iteF (by omega), List.dropLast_eq_take]
    congr 1; simp only [List.length_cons]; omega
  · rw [iteF ht]
    unfold needsTrim at ht
    simp only [decide_eq_true_eq, size_eq, hi1, List.length_cons] at ht
    subst hd1
    refine ⟨hl1, ?_, rfl⟩
    show x :: d.items = _
    split
    · rfl
    · rw [List.take_of_length_le (by simp; omega)]

end Deque

end PyLean.Sequences
