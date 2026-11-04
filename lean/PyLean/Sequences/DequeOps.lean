import PyLean.Sequences.Rot

/-!
Deque operations in terms of the items: extend/extendleft with eviction,
item access through the block arithmetic, deletion through rotation.
-/

namespace PyLean.Sequences

open PyLean

set_option linter.unusedSectionVars false

variable {α : Type} [Inhabited α]

/-- `omega` after unfolding the deque size and right-block number. -/
macro "dq_omega" : tactic => `(tactic| ((try simp only [Deque.rbNum, Deque.size_eq] at *) <;> omega))

theorem keepLast_keepLast (k : Nat) (l ys : List α) :
    (l.drop (l.length - k) ++ ys).drop ((l.drop (l.length - k) ++ ys).length - k) =
      (l ++ ys).drop ((l ++ ys).length - k) := by
  have h1 : (l ++ ys).drop (l.length - k) = l.drop (l.length - k) ++ ys :=
    List.drop_append_of_le_length (by omega)
  rw [← h1, List.drop_drop]
  congr 1
  simp only [List.length_drop, List.length_append]
  omega

theorem keepFirst_cons (k : Nat) (x : α) (l : List α) :
    (x :: l.take k).take k = (x :: l).take k := by
  cases k with
  | zero => rfl
  | succ k => simp only [List.take_succ_cons, List.take_take]; congr 2; omega

theorem take_append_take (k : Nat) (ys l : List α) :
    (ys ++ l.take k).take k = (ys ++ l).take k := by
  rw [List.take_append, List.take_append, List.take_take]
  congr 2; omega

theorem length_keepLast_le (m : Int) (l : List α) (hm : 0 ≤ m) :
    ((keepLast m l).length : Int) ≤ m := by
  unfold keepLast; rw [iteF (by omega)]; simp only [List.length_drop]; omega

theorem length_keepFirst_le (m : Int) (l : List α) (hm : 0 ≤ m) :
    ((keepFirst m l).length : Int) ≤ m := by
  unfold keepFirst; rw [iteF (by omega)]; simp only [List.length_take]; omega

theorem keepLast_of_le (m : Int) (l : List α) (h : m < 0 ∨ (l.length : Int) ≤ m) : keepLast m l = l := by
  unfold keepLast; split
  · rfl
  · rw [show l.length - m.toNat = 0 by omega]; rfl

theorem keepFirst_of_le (m : Int) (l : List α) (h : m < 0 ∨ (l.length : Int) ≤ m) : keepFirst m l = l := by
  unfold keepFirst; split
  · rfl
  · rw [List.take_of_length_le (by omega)]

theorem snd_popleft_tname (d : Deque α) : (Deque.snd' d.popleft d).tname = d.tname := by
  unfold Deque.popleft
  split
  · rfl
  · dsimp only
    split
    · split <;> rfl
    · rfl

theorem snd_pop_tname (d : Deque α) : (Deque.snd' d.pop d).tname = d.tname := by
  unfold Deque.pop
  split
  · rfl
  · dsimp only
    split
    · split <;> rfl
    · rfl

theorem appendM_tname (d : Deque α) (x : α) (m : Int) : (d.appendM x m).tname = d.tname := by
  unfold Deque.appendM
  dsimp only
  split <;> split <;> first | rfl | exact snd_popleft_tname _

theorem appendleftM_tname (d : Deque α) (x : α) (m : Int) : (d.appendleftM x m).tname = d.tname := by
  unfold Deque.appendleftM
  dsimp only
  split <;> split <;> first | rfl | exact snd_pop_tname _

theorem foldl_appendM_tname (xs : List α) : ∀ d : Deque α,
    (xs.foldl (fun d x => d.appendM x d.maxlen) d).tname = d.tname := by
  induction xs with
  | nil => intro d; rfl
  | cons x xs ih => intro d; simp only [List.foldl_cons]; rw [ih, appendM_tname]

theorem extend_tname (d : Deque α) (xs : List α) : (d.extend xs).tname = d.tname := by
  unfold Deque.extend
  split
  · rfl
  · dsimp only
    rw [foldl_appendM_tname]
    split <;> rfl

namespace Deque

theorem maxOk_iff (d : Deque α) : d.MaxOk ↔ d.maxlen = -1 ∨ (0 ≤ d.maxlen ∧ (d.items.length : Int) ≤ d.maxlen) :=
  Iff.rfl

/-- The fold of `deque_extend_impl`. -/
theorem foldl_appendM (xs : List α) : ∀ (d : Deque α), d.Layout →
    (d.maxlen = -1 ∨ 0 < d.maxlen) → (d.maxlen < 0 ∨ (d.items.length : Int) ≤ d.maxlen) →
    let d' := xs.foldl (fun d x => d.appendM x d.maxlen) d
    d'.Layout ∧ d'.items = keepLast d.maxlen (d.items ++ xs) ∧ d'.maxlen = d.maxlen := by
  induction xs with
  | nil => intro d h _ hm; exact ⟨h, by rw [List.append_nil, keepLast_of_le _ _ hm]; rfl, rfl⟩
  | cons x xs ih =>
    intro d h hpos hm
    simp only [List.foldl_cons]
    obtain ⟨hl, hi, hmx⟩ := appendM_spec d x d.maxlen h hm
    have hm' : (d.appendM x d.maxlen).maxlen < 0 ∨
        ((d.appendM x d.maxlen).items.length : Int) ≤ (d.appendM x d.maxlen).maxlen := by
      rw [hmx, hi]
      rcases hpos with hp | hp
      · left; omega
      · right; exact length_keepLast_le _ _ (by omega)
    obtain ⟨h1, h2, h3⟩ := ih _ hl (by rw [hmx]; exact hpos) hm'
    refine ⟨h1, ?_, by rw [h3, hmx]⟩
    rw [h2, hi, hmx]
    unfold keepLast
    split
    · simp
    · rw [keepLast_keepLast]; simp

theorem foldl_appendleftM (xs : List α) : ∀ (d : Deque α), d.Layout →
    (d.maxlen = -1 ∨ 0 < d.maxlen) → (d.maxlen < 0 ∨ (d.items.length : Int) ≤ d.maxlen) →
    let d' := xs.foldl (fun d x => d.appendleftM x d.maxlen) d
    d'.Layout ∧ d'.items = keepFirst d.maxlen (xs.reverse ++ d.items) ∧ d'.maxlen = d.maxlen := by
  induction xs with
  | nil => intro d h _ hm; exact ⟨h, by rw [List.reverse_nil, List.nil_append, keepFirst_of_le _ _ hm]; rfl, rfl⟩
  | cons x xs ih =>
    intro d h hpos hm
    simp only [List.foldl_cons]
    obtain ⟨hl, hi, hmx⟩ := appendleftM_spec d x d.maxlen h hm
    have hm' : (d.appendleftM x d.maxlen).maxlen < 0 ∨
        ((d.appendleftM x d.maxlen).items.length : Int) ≤ (d.appendleftM x d.maxlen).maxlen := by
      rw [hmx, hi]
      rcases hpos with hp | hp
      · left; omega
      · right; exact length_keepFirst_le _ _ (by omega)
    obtain ⟨h1, h2, h3⟩ := ih _ hl (by rw [hmx]; exact hpos) hm'
    refine ⟨h1, ?_, by rw [h3, hmx]⟩
    rw [h2, hi, hmx]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    unfold keepFirst
    split
    · rfl
    · exact take_append_take _ _ _

theorem maxlen_cases (d : Deque α) (h : d.WF) :
    d.maxlen = -1 ∨ d.maxlen = 0 ∨ 0 < d.maxlen := by
  rcases h.2 with h | h
  · left; exact h
  · right; omega

theorem items_nil_of_maxlen_zero (d : Deque α) (h : d.WF) (h0 : d.maxlen = 0) : d.items = [] := by
  rcases h.2 with h | h
  · omega
  · have : d.items.length = 0 := by have := h.2; rw [size_eq] at this; omega
    exact List.eq_nil_of_length_eq_zero this

/-- `d.extend(xs)`: layout and `maxlen` kept, items `keepLast maxlen (items ++ xs)`. -/
theorem extend_spec (d : Deque α) (xs : List α) (h : d.WF) :
    (d.extend xs).WF ∧ (d.extend xs).items = keepLast d.maxlen (d.items ++ xs) ∧
      (d.extend xs).maxlen = d.maxlen := by
  unfold extend
  rcases maxlen_cases d h with hm | hm | hm
  · rw [iteF (by omega)]
    simp only
    generalize hd1 : (if d.size = 0 then { d with left := 1, right := 0 } else d) = d1
    have hl1 : d1.Layout ∧ d1.items = d.items ∧ d1.maxlen = d.maxlen := by
      rw [← hd1]; split
      · rename_i hs; rw [size_eq] at hs
        refine ⟨?_, rfl, rfl⟩
        rw [layout_iff]; simp only; omega
      · exact ⟨h.1, rfl, rfl⟩
    obtain ⟨hl1, hi1, hmx1⟩ := hl1
    obtain ⟨a, b, c⟩ := foldl_appendM xs d1 hl1 (by omega) (by omega)
    refine ⟨⟨a, ?_⟩, by rw [b, hi1, hmx1], by rw [c, hmx1]⟩
    rw [maxOk_iff, c, hmx1]; left; exact hm
  · rw [iteT hm]
    refine ⟨h, ?_, rfl⟩
    rw [items_nil_of_maxlen_zero d h hm, hm]
    unfold keepLast; simp
  · rw [iteF (by omega)]
    simp only
    generalize hd1 : (if d.size = 0 then { d with left := 1, right := 0 } else d) = d1
    have hl1 : d1.Layout ∧ d1.items = d.items ∧ d1.maxlen = d.maxlen := by
      rw [← hd1]; split
      · rename_i hs; rw [size_eq] at hs
        refine ⟨?_, rfl, rfl⟩
        rw [layout_iff]; simp only; omega
      · exact ⟨h.1, rfl, rfl⟩
    obtain ⟨hl1, hi1, hmx1⟩ := hl1
    have hle : (d1.items.length : Int) ≤ d1.maxlen := by
      rw [hi1, hmx1]; rcases h.2 with h2 | h2
      · omega
      · rw [← size_eq]; exact h2.2
    obtain ⟨a, b, c⟩ := foldl_appendM xs d1 hl1 (by omega) (Or.inr hle)
    refine ⟨⟨a, ?_⟩, by rw [b, hi1, hmx1], by rw [c, hmx1]⟩
    rw [maxOk_iff, c, hmx1, b, hmx1]; right
    exact ⟨by omega, length_keepLast_le _ _ (by omega)⟩

/-- `d.extendleft(xs)`: items `keepFirst maxlen (reversed xs ++ items)`. -/
theorem extendleft_spec (d : Deque α) (xs : List α) (h : d.WF) :
    (d.extendleft xs).WF ∧ (d.extendleft xs).items = keepFirst d.maxlen (xs.reverse ++ d.items) ∧
      (d.extendleft xs).maxlen = d.maxlen := by
  unfold extendleft
  rcases maxlen_cases d h with hm | hm | hm
  · rw [iteF (by omega)]
    simp only
    generalize hd1 : (if d.size = 0 then { d with left := 64 - 1, right := 64 - 2 } else d) = d1
    have hl1 : d1.Layout ∧ d1.items = d.items ∧ d1.maxlen = d.maxlen := by
      rw [← hd1]; split
      · rename_i hs; rw [size_eq] at hs
        refine ⟨?_, rfl, rfl⟩
        rw [layout_iff]; simp only; omega
      · exact ⟨h.1, rfl, rfl⟩
    obtain ⟨hl1, hi1, hmx1⟩ := hl1
    obtain ⟨a, b, c⟩ := foldl_appendleftM xs d1 hl1 (by omega) (by omega)
    refine ⟨⟨a, ?_⟩, by rw [b, hi1, hmx1], by rw [c, hmx1]⟩
    rw [maxOk_iff, c, hmx1]; left; exact hm
  · rw [iteT hm]
    refine ⟨h, ?_, rfl⟩
    rw [items_nil_of_maxlen_zero d h hm, hm]
    unfold keepFirst; simp
  · rw [iteF (by omega)]
    simp only
    generalize hd1 : (if d.size = 0 then { d with left := 64 - 1, right := 64 - 2 } else d) = d1
    have hl1 : d1.Layout ∧ d1.items = d.items ∧ d1.maxlen = d.maxlen := by
      rw [← hd1]; split
      · rename_i hs; rw [size_eq] at hs
        refine ⟨?_, rfl, rfl⟩
        rw [layout_iff]; simp only; omega
      · exact ⟨h.1, rfl, rfl⟩
    obtain ⟨hl1, hi1, hmx1⟩ := hl1
    have hle : (d1.items.length : Int) ≤ d1.maxlen := by
      rw [hi1, hmx1]; rcases h.2 with h2 | h2
      · omega
      · rw [← size_eq]; exact h2.2
    obtain ⟨a, b, c⟩ := foldl_appendleftM xs d1 hl1 (by omega) (Or.inr hle)
    refine ⟨⟨a, ?_⟩, by rw [b, hi1, hmx1], by rw [c, hmx1]⟩
    rw [maxOk_iff, c, hmx1, b, hmx1]; right
    exact ⟨by omega, length_keepFirst_le _ _ (by omega)⟩

theorem append_spec (d : Deque α) (x : α) (h : d.WF) :
    (d.append x).WF ∧ (d.append x).items = keepLast d.maxlen (d.items ++ [x]) ∧
      (d.append x).maxlen = d.maxlen := by
  unfold append
  have hm : d.maxlen < 0 ∨ (d.items.length : Int) ≤ d.maxlen := by
    rcases h.2 with h2 | h2
    · omega
    · rw [← size_eq]; exact Or.inr h2.2
  obtain ⟨a, b, c⟩ := appendM_spec d x d.maxlen h.1 hm
  refine ⟨⟨a, ?_⟩, b, c⟩
  rw [maxOk_iff, c, b]
  rcases h.2 with h2 | h2
  · left; exact h2
  · right; exact ⟨h2.1, length_keepLast_le _ _ h2.1⟩

theorem appendleft_spec (d : Deque α) (x : α) (h : d.WF) :
    (d.appendleft x).WF ∧ (d.appendleft x).items = keepFirst d.maxlen (x :: d.items) ∧
      (d.appendleft x).maxlen = d.maxlen := by
  unfold appendleft
  have hm : d.maxlen < 0 ∨ (d.items.length : Int) ≤ d.maxlen := by
    rcases h.2 with h2 | h2
    · omega
    · rw [← size_eq]; exact Or.inr h2.2
  obtain ⟨a, b, c⟩ := appendleftM_spec d x d.maxlen h.1 hm
  refine ⟨⟨a, ?_⟩, b, c⟩
  rw [maxOk_iff, c, b]
  rcases h.2 with h2 | h2
  · left; exact h2
  · right; exact ⟨h2.1, length_keepFirst_le _ _ h2.1⟩

/-! ### Item access -/

theorem read_ok (d : Deque α) (_h : d.Layout) (b j : Int) (hb0 : 0 ≤ b) (hb : b ≤ d.rbNum)
    (hj0 : 0 ≤ j) (hj : j < 64) (hk0 : 0 ≤ b * 64 + j - d.left) (hk : b * 64 + j - d.left < d.size) :
    d.read b j = .ok (ix d.items (b * 64 + j - d.left)) := by
  unfold read
  rw [iteF (by omega)]
  simp only
  rw [iteT ⟨hj0, hj, hk0, hk⟩]

theorem write_ok (d : Deque α) (b j : Int) (v : α) (hb0 : 0 ≤ b) (hb : b ≤ d.rbNum)
    (hj0 : 0 ≤ j) (hj : j < 64) (hk0 : 0 ≤ b * 64 + j - d.left) (hk : b * 64 + j - d.left < d.size) :
    d.write b j v = .ok { d with items := d.items.set (b * 64 + j - d.left).toNat v } := by
  unfold write
  rw [iteF (by omega)]
  simp only
  rw [iteT ⟨hj0, hj, hk0, hk⟩]

/-- `deque_item_lock_held`: every in-range index reads its item through the
block arithmetic (from the left or from the right). -/
theorem itemC_spec (d : Deque α) (h : d.Layout) (i : Int) :
    d.itemC i = if 0 ≤ i ∧ i < d.size then .ok (ix d.items i)
      else .error (.indexError "deque index out of range") := by
  have hL := h
  rw [layout_iff] at h
  unfold itemC
  by_cases hv : 0 ≤ i ∧ i < d.size
  · have hv' : validIndex i d.size = true := by unfold validIndex; simp only [decide_eq_true_eq]; exact hv
    rw [hv', iteT hv]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    by_cases h0 : i = 0
    · rw [iteT h0, read_ok d hL 0 d.left (by omega) (by dq_omega) (by omega) (by omega) (by omega) (by dq_omega)]
      congr 2; omega
    rw [iteF h0]
    by_cases h1 : i = d.size - 1
    · rw [iteT h1, read_ok d hL _ _ (by dq_omega) (by dq_omega) (by omega) (by omega) (by dq_omega) (by dq_omega)]
      congr 2; dq_omega
    rw [iteF h1]
    by_cases h2 : i < d.size / 2
    · rw [iteT h2, read_ok d hL _ _ (by omega) (by dq_omega) (by omega) (by omega) (by omega) (by dq_omega)]
      congr 2; omega
    · rw [iteF h2, read_ok d hL _ _ (by dq_omega) (by dq_omega) (by omega) (by omega) (by dq_omega) (by dq_omega)]
      congr 2; dq_omega
  · have hv' : validIndex i d.size = false := by unfold validIndex; simp only [decide_eq_false_iff_not]; exact hv
    rw [hv', iteF hv]
    rfl

theorem pop_wf (d : Deque α) (h : d.WF) (hne : d.items ≠ []) :
    ∃ d', d.pop = .ok (ix d.items (d.items.length - 1), d') ∧ d'.WF ∧
      d'.items = d.items.dropLast ∧ d'.maxlen = d.maxlen := by
  obtain ⟨d', hp, hl, hi, hm⟩ := pop_spec d h.1 hne
  refine ⟨d', hp, ⟨hl, ?_⟩, hi, hm⟩
  rw [maxOk_iff, hm, hi, List.length_dropLast]
  rcases h.2 with h2 | h2
  · left; exact h2
  · right; rw [size_eq] at h2; omega

theorem popleft_wf (d : Deque α) (h : d.WF) (hne : d.items ≠ []) :
    ∃ d', d.popleft = .ok (ix d.items 0, d') ∧ d'.WF ∧ d'.items = d.items.drop 1 ∧ d'.maxlen = d.maxlen := by
  obtain ⟨d', hp, hl, hi, hm⟩ := popleft_spec d h.1 hne
  refine ⟨d', hp, ⟨hl, ?_⟩, hi, hm⟩
  rw [maxOk_iff, hm, hi, List.length_drop]
  rcases h.2 with h2 | h2
  · left; exact h2
  · right; rw [size_eq] at h2; omega

theorem rotateC_wf (d : Deque α) (n : Int) (h : d.WF) :
    ∃ d', d.rotateC n = .ok d' ∧ d'.WF ∧ d'.items = rotLi (-n) d.items ∧ d'.maxlen = d.maxlen := by
  obtain ⟨d', hr, hl, hi, hm⟩ := rotateC_spec d n h.1
  refine ⟨d', hr, ⟨hl, ?_⟩, hi, hm⟩
  rw [maxOk_iff, hm, hi, length_rotLi]
  exact h.2

theorem rotL_append (A B : List α) : rotL A.length (A ++ B) = B ++ A := by
  unfold rotL
  rw [List.drop_append_of_le_length (Nat.le_refl _), List.take_append_of_le_length (Nat.le_refl _),
    List.drop_length, List.take_length, List.nil_append]

theorem rotLi_erase (l : List α) (i : Nat) (hi : i < l.length) :
    rotLi (-(i : Int)) ((rotLi i l).drop 1) = l.eraseIdx i := by
  rw [rotLi_nat _ _ hi, List.eraseIdx_eq_take_drop_succ]
  unfold rotL
  have hd : 1 ≤ (l.drop i).length := by simp only [List.length_drop]; omega
  rw [List.drop_append_of_le_length hd, List.drop_drop]
  by_cases h0 : i = 0
  · subst h0; simp [rotLi_zero]
  by_cases hlast : i + 1 = l.length
  · rw [List.drop_of_length_le (show l.length ≤ i + 1 by omega), List.nil_append]
    unfold rotLi
    rw [List.length_take, show (-(i : Int)) % ((min i l.length : Nat) : Int) = 0 by
      rw [show min i l.length = i by omega]
      exact emod_char _ _ _ (-1) (by omega) (by omega) (by omega)]
    simp [rotL_zero]
  · unfold rotLi
    have hlen : ((l.drop (i + 1) ++ l.take i).length : Int) = l.length - 1 := by
      simp only [List.length_append, List.length_drop, List.length_take]; omega
    rw [hlen, emod_char (-(i : Int)) ((l.length : Int) - 1 - i) _ (-1) (by omega) (by omega) (by omega)]
    have : ((l.length : Int) - 1 - i).toNat = (l.drop (i + 1)).length := by
      simp only [List.length_drop]; omega
    rw [this, rotL_append]

/-- `deque_del_item`: rotate, popleft, rotate back deletes item `i`. -/
theorem delItem_spec (d : Deque α) (i : Int) (h : d.WF) (h0 : 0 ≤ i) (hi : i < d.size) :
    ∃ d', d.delItem i = .ok d' ∧ d'.WF ∧ d'.items = d.items.eraseIdx i.toNat ∧ d'.maxlen = d.maxlen := by
  unfold delItem
  obtain ⟨d1, h1, w1, i1, m1⟩ := rotateC_wf d (-i) h
  have hne : d1.items ≠ [] := by
    intro he; rw [i1] at he; have := congrArg List.length he
    rw [length_rotLi, List.length_nil] at this; rw [size_eq] at hi; omega
  obtain ⟨d2, h2, w2, i2, m2⟩ := popleft_wf d1 w1 hne
  obtain ⟨d3, h3, w3, i3, m3⟩ := rotateC_wf d2 i w2
  refine ⟨d3, ?_, w3, ?_, by rw [m3, m2, m1]⟩
  · simp only [h1, h2, bind, Except.bind, h3]
  · rw [i3, i2, i1, Int.neg_neg]
    rw [size_eq] at hi
    have := rotLi_erase d.items i.toNat (by omega)
    rw [show ((i.toNat : Nat) : Int) = i by omega] at this
    exact this

/-- `d[i] = v` / `del d[i]` after `PySequence_SetItem` normalisation. -/
theorem assItemC_spec (d : Deque α) (h : d.WF) (i : Int) (v : Option α) :
    d.assItemC i v = if 0 ≤ i ∧ i < d.size then
        (match v with
         | some v => .ok { d with items := d.items.set i.toNat v }
         | none => d.delItem i)
      else .error (.indexError "deque index out of range") := by
  have hL := h.1
  have h' := h.1
  rw [layout_iff] at h'
  unfold assItemC
  dsimp only
  by_cases hv : 0 ≤ i ∧ i < d.size
  · have hv' : validIndex i d.size = true := by unfold validIndex; simp only [decide_eq_true_eq]; exact hv
    rw [hv', iteT hv]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    cases v with
    | none => rfl
    | some v =>
      simp only
      split
      · rw [write_ok d _ _ v (by omega) (by dq_omega) (by omega) (by omega) (by omega) (by dq_omega)]
        congr 4; omega
      · rw [write_ok d _ _ v (by dq_omega) (by dq_omega) (by omega) (by omega) (by dq_omega) (by dq_omega)]
        congr 4; dq_omega
  · have hv' : validIndex i d.size = false := by unfold validIndex; simp only [decide_eq_false_iff_not]; exact hv
    rw [hv', iteF hv]
    rfl

theorem step1_pos (d : Deque α) (b j p : Int) (hp : b * 64 + j - d.left = p) (hj0 : 0 ≤ j) (hj : j < 64) :
    (step1 b j).1 * 64 + (step1 b j).2 - d.left = p + 1 ∧ 0 ≤ (step1 b j).2 ∧ (step1 b j).2 < 64 := by
  unfold step1
  split
  · simp only; omega
  · simp only; omega

theorem foldl_step1 (d : Deque α) (k : Nat) : ∀ (b j p : Int), b * 64 + j - d.left = p → 0 ≤ j → j < 64 →
    let bj := (List.range k).foldl (fun (bj : Int × Int) _ => step1 bj.1 bj.2) (b, j)
    bj.1 * 64 + bj.2 - d.left = p + k ∧ 0 ≤ bj.2 ∧ bj.2 < 64 := by
  induction k with
  | zero => intro b j p hp h0 h1; simp only [List.range_zero, List.foldl_nil]; exact ⟨by omega, h0, h1⟩
  | succ k ih =>
    intro b j p hp h0 h1
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨a1, a2, a3⟩ := ih b j p hp h0 h1
    obtain ⟨c1, c2, c3⟩ := step1_pos d _ _ _ a1 a2 a3
    exact ⟨by rw [c1]; omega, c2, c3⟩


/-! ### Iterators that do not touch the deque -/

theorem finalize_some (e : PyExc) (h : e ≠ .stopIteration) : finalizeIterator (some e) = .error e := by
  cases e <;> first | exact absurd rfl h | rfl

theorem snd_popleft_maxlen (d : Deque α) : (snd' d.popleft d).maxlen = d.maxlen := by
  unfold popleft
  split
  · rfl
  · dsimp only
    split
    · split <;> rfl
    · rfl

theorem snd_pop_maxlen (d : Deque α) : (snd' d.pop d).maxlen = d.maxlen := by
  unfold pop
  split
  · rfl
  · dsimp only
    split
    · split <;> rfl
    · rfl

theorem appendM_maxlen (d : Deque α) (x : α) (m : Int) : (d.appendM x m).maxlen = d.maxlen := by
  unfold appendM
  dsimp only
  split <;> split <;> first | rfl | exact snd_popleft_maxlen _

theorem appendleftM_maxlen (d : Deque α) (x : α) (m : Int) : (d.appendleftM x m).maxlen = d.maxlen := by
  unfold appendleftM
  dsimp only
  split <;> split <;> first | rfl | exact snd_pop_maxlen _

/-- The calls that end a `ReIter.ofList` iterator. -/
theorem ofList_nexts (xs : List α) (e : Option PyExc) : (ReIter.ofList xs e).nexts =
    xs.map (fun x (d : Deque α) => ((.ok x : Py α), d)) ++
      (match e with | none => [] | some e => [fun d => (.error e, d)]) := rfl

theorem pushLoop_end (push : Deque α → α → Int → Deque α) (m : Int) (e : Option PyExc) (d : Deque α) :
    pushLoop push m (match e with | none => [] | some e => [fun d => (.error e, d)]) d =
      (finalizeIterator e, d) := by
  cases e <;> rfl

theorem consumeLoop_end (e : Option PyExc) (d : Deque α) :
    consumeLoop (match e with | none => [] | some e => [fun d => (.error e, d)]) d =
      (finalizeIterator e, d) := by
  cases e <;> rfl

theorem pushLoop_pure_right (m : Int) (e : Option PyExc) (xs : List α) : ∀ d : Deque α, d.maxlen = m →
    pushLoop appendM m (xs.map (fun x (d : Deque α) => ((.ok x : Py α), d)) ++
      (match e with | none => [] | some e => [fun d => (.error e, d)])) d =
      (finalizeIterator e, xs.foldl (fun d x => d.appendM x d.maxlen) d) := by
  induction xs with
  | nil => intro d _; exact pushLoop_end _ _ _ _
  | cons x xs ih =>
    intro d hm
    simp only [List.map_cons, List.cons_append, pushLoop, List.foldl_cons]
    rw [hm, ih _ (by rw [appendM_maxlen, hm])]

theorem pushLoop_pure_left (m : Int) (e : Option PyExc) (xs : List α) : ∀ d : Deque α, d.maxlen = m →
    pushLoop appendleftM m (xs.map (fun x (d : Deque α) => ((.ok x : Py α), d)) ++
      (match e with | none => [] | some e => [fun d => (.error e, d)])) d =
      (finalizeIterator e, xs.foldl (fun d x => d.appendleftM x d.maxlen) d) := by
  induction xs with
  | nil => intro d _; exact pushLoop_end _ _ _ _
  | cons x xs ih =>
    intro d hm
    simp only [List.map_cons, List.cons_append, pushLoop, List.foldl_cons]
    rw [hm, ih _ (by rw [appendleftM_maxlen, hm])]

theorem consumeLoop_pure (e : Option PyExc) (xs : List α) : ∀ d : Deque α,
    consumeLoop (xs.map (fun x (d : Deque α) => ((.ok x : Py α), d)) ++
      (match e with | none => [] | some e => [fun d => (.error e, d)])) d = (finalizeIterator e, d) := by
  induction xs with
  | nil => intro d; exact consumeLoop_end _ _
  | cons x xs ih => intro d; simp only [List.map_cons, List.cons_append, consumeLoop]; exact ih d

/-- `extendRe` on an iterator that does not touch the deque is `extend`. -/
theorem extendRe_ofList (d : Deque α) (xs : List α) (e : Option PyExc) :
    d.extendRe (.ofList xs e) = (finalizeIterator e, d.extend xs) := by
  unfold extendRe extend
  simp only [ReIter.ofList]
  by_cases h0 : d.maxlen = 0
  · rw [iteT h0, iteT h0]; exact consumeLoop_pure e xs d
  · rw [iteF h0, iteF h0]
    exact pushLoop_pure_right _ e xs _ (by split <;> rfl)

theorem extendleftRe_ofList (d : Deque α) (xs : List α) (e : Option PyExc) :
    d.extendleftRe (.ofList xs e) = (finalizeIterator e, d.extendleft xs) := by
  unfold extendleftRe extendleft
  simp only [ReIter.ofList]
  by_cases h0 : d.maxlen = 0
  · rw [iteT h0, iteT h0]; exact consumeLoop_pure e xs d
  · rw [iteF h0, iteF h0]
    exact pushLoop_pure_left _ e xs _ (by split <;> rfl)

theorem extendIter_iter (d : Deque α) (xs : List α) (e : Option PyExc) :
    d.extendIter (.iter xs e) = (finalizeIterator e, d.extend xs) := extendRe_ofList d xs e

theorem extendleftIter_iter (d : Deque α) (xs : List α) (e : Option PyExc) :
    d.extendleftIter (.iter xs e) = (finalizeIterator e, d.extendleft xs) := extendleftRe_ofList d xs e

end Deque

end PyLean.Sequences
