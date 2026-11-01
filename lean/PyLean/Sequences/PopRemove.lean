import PyLean.Sequences.Index

/-!
`pop`, `remove` and `count` agree across `list` and `collections.deque`.
-/

namespace PyLean.Sequences

open PyLean

set_option linter.unusedSectionVars false

variable {α : Type} [Inhabited α]

/-- `pop([i])` on a list of items, as `list_pop_impl` does it but with the
empty-sequence message as a parameter: `Py_ssize_t` conversion of `i`
(default `-1`), `IndexError(emptyMsg)` on an empty sequence, add `len` to a
negative index, then `IndexError("pop index out of range")` or remove and
return item `j`. -/
def popSpecK (emptyMsg : String) (l : List α) (index : Int) : Py (α × List α) := do
  if l.length = 0 then throw (.indexError emptyMsg)
  let index := if index < 0 then index + l.length else index
  if !validIndex index l.length then throw (.indexError "pop index out of range")
  return (ix l index, l.eraseIdx index.toNat)

def popSpec (emptyMsg : String) (l : List α) (i : Option Int) : Py (α × List α) :=
  popArg i >>= popSpecK emptyMsg l

/-- `remove(x)`: delete the first item that `p` accepts, else `ValueError(msg)`. -/
def removeSpec (msg : String) (l : List α) (p : α → Bool) : Py (List α) :=
  match (List.range l.length).find? (fun (k : Nat) => p (ix l k)) with
  | some k => .ok (l.eraseIdx k)
  | none => .error (.valueError msg)

theorem firstFrom_spec (p : α → Bool) (l : List α) : ∀ (fuel i : Nat), l.length ≤ i + fuel →
    IsFirst p l i l.length ((firstFrom p l i fuel).map (fun k : Nat => (k : Int)))
  | 0, i, h => by
    simp only [firstFrom, Option.map_none]
    exact isFirst_empty p l i l.length (by omega)
  | fuel + 1, i, h => by
    unfold firstFrom
    by_cases h1 : i < l.length
    · rw [iteT h1]
      by_cases h2 : p (ix l i) = true
      · simp only [h2, ite_true]; exact isFirst_here p l i l.length (by omega) (by omega) (by omega) h2
      · have h2' : p (ix l i) = false := by simpa using h2
        simp only [h2', Bool.false_eq_true, ite_false]
        have := firstFrom_spec p l fuel (i + 1) (by omega)
        rw [show ((i + 1 : Nat) : Int) = (i : Int) + 1 by omega] at this
        exact isFirst_step p l i l.length _ h2' this
    · rw [iteF h1]; exact isFirst_empty p l i l.length (by omega)

theorem find_isFirst (p : α → Bool) (l : List α) :
    IsFirst p l 0 l.length (((List.range l.length).find? (fun (k : Nat) => p (ix l k))).map (fun k : Nat => (k : Int))) := by
  cases hf : (List.range l.length).find? (fun (k : Nat) => p (ix l k)) with
  | none =>
    intro j _ h2 h3 _
    have := List.find?_eq_none.mp hf j.toNat (List.mem_range.mpr (by omega))
    simp only [Bool.not_eq_true] at this
    rw [show ((j.toNat : Nat) : Int) = j by omega] at this
    exact this
  | some k =>
    obtain ⟨hk, n, hn, hkn, hbefore⟩ := List.find?_eq_some_iff_getElem.mp hf
    rw [List.getElem_range] at hkn
    subst hkn
    simp only [Option.map_some]
    refine ⟨by omega, by simp only [List.length_range] at hn; omega, by omega,
      by simp only [List.length_range] at hn; omega, hk, fun j hj1 hj2 hj3 => ?_⟩
    have := hbefore j.toNat (by simp only [List.length_range] at hn; omega)
    simp only [List.getElem_range, Bool.not_eq_eq_eq_not, Bool.not_true] at this
    rw [show ((j.toNat : Nat) : Int) = j by omega] at this
    exact this

theorem countLoop_spec (d : Deque α) (hL : d.Layout) (f : α → α → Bool) (v : α) : ∀ (n : Nat) (p b j c : Int),
    b * 64 + j - d.left = p → 0 ≤ j → j < 64 → 0 ≤ p → p + n ≤ d.size →
    Deque.countLoop (pureCmp f) v d.state n b j c d =
      (.ok (c + (((d.items.drop p.toNat).take n).filter (f · v)).length), d) := by
  have h' := hL
  rw [Deque.layout_iff] at h'
  intro n
  induction n with
  | zero => intro p b j c _ _ _ _ _; simp [Deque.countLoop]
  | succ n ih =>
    intro p b j c hp h0 h1 hp0 hk
    simp only [Deque.countLoop]
    rw [Deque.read_ok d hL b j (by dq_omega) (by dq_omega) h0 h1 (by omega) (by dq_omega)]
    simp only [hp, pureCmp, ne_eq, not_true_eq_false, ite_false]
    obtain ⟨c1, c2, c3⟩ := Deque.step1_pos d b j p hp h0 h1
    rw [ih (p + 1) _ _ _ c1 c2 c3 (by omega) (by omega)]
    rw [Deque.size_eq] at hk
    rw [List.drop_eq_getElem_cons (show p.toNat < d.items.length by omega), List.take_succ_cons,
      List.filter_cons, show (p + 1).toNat = p.toNat + 1 by omega]
    have hix : ix d.items p = d.items[p.toNat] := by
      unfold ix; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    rw [← hix]
    by_cases hx : f (ix d.items p) v = true
    · simp only [hx, ite_true, List.length_cons]; congr 2; omega
    · simp only [hx, ite_false, Bool.false_eq_true]; congr 2; omega

/-- For every element type, every pure truth-valued `__eq__` `f` (the assumption
on the element type), list `l`, `x` and optional index `i`: `list.pop(i)` is
`popSpec`; `deque.pop()` / `deque.popleft()` (any deque with items `l`, type
invariant `WF`) are `list.pop()` / `list.pop(0)` with the deque's message; `remove(x)`
deletes the first equal item in both (`ValueError` with each type's message
otherwise), `count(x)` is the same number for both and `x in d` is `any`. -/
def PopRemoveCountAgree : Prop :=
  ∀ (α : Type) [Inhabited α] (f : α → α → Bool) (l : List α) (x : α) (i : Option Int),
    listPop l i = popSpec "pop from empty list" l i ∧
    listRemove f l x = removeSpec "list.remove(x): x not in list" l (f · x) ∧
    (∀ d : Deque α, d.WF → d.items = l →
      d.pop.map (fun p => (p.1, p.2.items)) = popSpec "pop from an empty deque" l none ∧
      d.popleft.map (fun p => (p.1, p.2.items)) = popSpec "pop from an empty deque" l (some 0) ∧
      (d.remove (pureCmp f) x).1 = ((removeSpec "" l (f · x)).map (fun _ => ())).mapError
        (fun _ => .valueError "deque.remove(x): x not in deque") ∧
      (∀ l', removeSpec "" l (f · x) = .ok l' → (d.remove (pureCmp f) x).2.items = l') ∧
      d.count (pureCmp f) x = (.ok (listCount f l x), d) ∧
      d.contains (pureCmp f) x = (.ok (l.any (f · x)), d))

theorem firstFrom_eq_find (p : α → Bool) (l : List α) :
    firstFrom p l 0 l.length = (List.range l.length).find? (fun (k : Nat) => p (ix l k)) := by
  have h1 := firstFrom_spec p l l.length 0 (by omega)
  have h2 := find_isFirst p l
  have := isFirst_unique _ _ _ _ _ _ h1 h2
  cases ha : firstFrom p l 0 l.length <;> cases hb : (List.range l.length).find? (fun (k : Nat) => p (ix l k)) <;>
    rw [ha, hb] at this <;> simp_all <;> omega

theorem dequePop_eq (d : Deque α) (h : d.WF) :
    d.pop.map (fun p => (p.1, p.2.items)) = popSpec "pop from an empty deque" d.items none := by
  by_cases he : d.items = []
  · have hs : d.size = 0 := by rw [Deque.size_eq, he]; rfl
    unfold Deque.pop popSpec popArg popSpecK
    rw [iteT hs]
    simp [he, bind, Except.bind, pure, Except.pure]; rfl
  · obtain ⟨d', hp, _, hi, _⟩ := Deque.pop_wf d h he
    rw [hp]
    have hlen := List.length_pos_iff.mpr he
    unfold popSpec popArg popSpecK
    simp only [pure, Except.pure, bind, Except.bind, Except.map, validIndex]
    rw [iteF (show ¬ d.items.length = 0 by omega)]
    simp only [show (-1 : Int) < 0 by decide, ite_true]
    rw [iteF (by simp; omega)]
    rw [hi, show (-1 + (d.items.length : Int)).toNat = d.items.length - 1 by omega,
      List.eraseIdx_length_sub_one, show (-1 + (d.items.length : Int)) = (d.items.length : Int) - 1 by omega]

theorem dequePopleft_eq (d : Deque α) (h : d.WF) :
    d.popleft.map (fun p => (p.1, p.2.items)) = popSpec "pop from an empty deque" d.items (some 0) := by
  by_cases he : d.items = []
  · have hs : d.size = 0 := by rw [Deque.size_eq, he]; rfl
    unfold Deque.popleft popSpec popArg popSpecK
    rw [iteT hs]
    simp [he, bind, Except.bind, pure, Except.pure, asSsize, ssizeMin, ssizeMax]; rfl
  · obtain ⟨d', hp, _, hi, _⟩ := Deque.popleft_wf d h he
    rw [hp]
    have hlen := List.length_pos_iff.mpr he
    unfold popSpec popArg popSpecK
    simp only [asSsize, pure, Except.pure, bind, Except.bind, Except.map, validIndex]
    rw [iteT (by unfold ssizeMin ssizeMax; omega)]
    simp only
    rw [iteF (show ¬ d.items.length = 0 by omega)]
    simp only [show ¬ ((0 : Int) < 0) by decide, ite_false]
    rw [iteF (by simp; omega)]
    simp only [hi, Int.toNat_zero, List.eraseIdx_zero, List.drop_one]

theorem isFirst_any (p : α → Bool) (l : List α) (r : Option Int)
    (h : IsFirst p l 0 l.length r) : r.isSome = l.any p := by
  cases r with
  | none =>
    symm
    rw [Option.isSome_none, Bool.eq_false_iff, ne_eq, List.any_eq_true]
    rintro ⟨y, hy, hpy⟩
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hy
    have := h i (by omega) (by omega) (by omega) (by omega)
    rw [ix_getElem l i hi, e, hpy] at this
    exact nomatch this
  | some k =>
    obtain ⟨_, _, h3, h4, h5, _⟩ := h
    symm
    rw [Option.isSome_some, List.any_eq_true]
    exact ⟨ix l k, ix_mem l k h3 h4, h5⟩

theorem dequeRemove_eq (d : Deque α) (h : d.WF) (f : α → α → Bool) (x : α) :
    (d.remove (pureCmp f) x).1 = ((removeSpec "" d.items (f · x)).map (fun _ => ())).mapError
        (fun _ => .valueError "deque.remove(x): x not in deque") ∧
      (∀ l', removeSpec "" d.items (f · x) = .ok l' → (d.remove (pureCmp f) x).2.items = l') := by
  have hL := h.1
  have h' := h.1
  rw [Deque.layout_iff] at h'
  obtain ⟨r, hr, hf⟩ := Deque.scanLoop_spec d hL f x true (.indexError "deque mutated during iteration")
    d.items.length 0 0 d.left (by omega) h'.1 h'.2.1 (by omega) (by rw [Deque.size_eq]; omega)
  have hu := isFirst_unique _ _ _ _ _ _ hf (by simpa using find_isFirst (f · x) d.items)
  unfold Deque.remove removeSpec
  rw [hr]
  cases hfind : (List.range d.items.length).find? (fun (k : Nat) => f (ix d.items k) x) with
  | none =>
    rw [hfind] at hu; simp at hu; subst hu
    exact ⟨rfl, fun l' he => nomatch he⟩
  | some k =>
    rw [hfind] at hu; simp at hu; subst hu
    obtain ⟨_, n, hn, hkn, _⟩ := List.find?_eq_some_iff_getElem.mp hfind
    rw [List.getElem_range] at hkn
    subst hkn
    simp only [List.length_range] at hn
    obtain ⟨d', hdel, _, hi, _⟩ := Deque.delItem_spec d n h (by omega) (by rw [Deque.size_eq]; omega)
    simp only [hdel]
    refine ⟨rfl, fun l' he => ?_⟩
    simp only [Except.ok.injEq] at he
    rw [hi, ← he]; simp

theorem dequeCount_eq (d : Deque α) (h : d.WF) (f : α → α → Bool) (x : α) :
    d.count (pureCmp f) x = (.ok (listCount f d.items x), d) := by
  have h' := h.1
  rw [Deque.layout_iff] at h'
  unfold Deque.count
  rw [countLoop_spec d h.1 f x d.items.length 0 0 d.left 0 (by omega) h'.1 h'.2.1 (by omega)
    (by rw [Deque.size_eq]; omega)]
  simp [listCount]

theorem dequeContains_eq (d : Deque α) (h : d.WF) (f : α → α → Bool) (x : α) :
    d.contains (pureCmp f) x = (.ok (d.items.any (f · x)), d) := by
  have hL := h.1
  have h' := h.1
  rw [Deque.layout_iff] at h'
  obtain ⟨r, hr, hf⟩ := Deque.scanLoop_spec d hL f x false Deque.mutatedErr
    d.items.length 0 0 d.left (by omega) h'.1 h'.2.1 (by omega) (by rw [Deque.size_eq]; omega)
  unfold Deque.contains
  rw [hr]
  simp only
  rw [isFirst_any (f · x) d.items r (by simpa using hf)]

theorem popRemoveCountAgree_proven : PopRemoveCountAgree := by
  intro α _ f l x i
  refine ⟨rfl, ?_, fun d hd hl => ?_⟩
  · unfold listRemove removeSpec; rw [firstFrom_eq_find]; rfl
  · subst hl
    obtain ⟨r1, r2⟩ := dequeRemove_eq d hd f x
    exact ⟨dequePop_eq d hd, dequePopleft_eq d hd, r1, r2, dequeCount_eq d hd f x, dequeContains_eq d hd f x⟩

end PyLean.Sequences
