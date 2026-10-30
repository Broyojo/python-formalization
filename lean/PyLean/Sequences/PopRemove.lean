import PyLean.Sequences.Index

/-!
`pop`, `remove` and `count` agree across `list`, `array.array` and
`collections.deque`.
-/

namespace PyLean.Sequences

open PyLean

/-- `pop([i])` on a list of items, as `list_pop_impl` does it but with the
empty-sequence message as a parameter: `Py_ssize_t` conversion of `i`
(default `-1`), `IndexError(emptyMsg)` on an empty sequence, add `len` to a
negative index, then `IndexError("pop index out of range")` or remove and
return item `j`. -/
def popSpecK (emptyMsg : String) (l : List Int) (index : Int) : Py (Int × List Int) := do
  if l.length = 0 then throw (.indexError emptyMsg)
  let index := if index < 0 then index + l.length else index
  if !validIndex index l.length then throw (.indexError "pop index out of range")
  return (ix l index, l.eraseIdx index.toNat)

def popSpec (emptyMsg : String) (l : List Int) (i : Option Int) : Py (Int × List Int) :=
  popArg i >>= popSpecK emptyMsg l

/-- `remove(x)`: delete the first item equal to `x`, else `ValueError(msg)`. -/
def removeSpec (msg : String) (l : List Int) (x : Int) : Py (List Int) :=
  match (List.range l.length).find? (fun (k : Nat) => ix l k = x) with
  | some k => .ok (l.eraseIdx k)
  | none => .error (.valueError msg)

theorem firstFrom_spec (l : List Int) (x : Int) : ∀ (fuel i : Nat), l.length ≤ i + fuel →
    IsFirst l x i l.length ((firstFrom l x i fuel).map (fun k : Nat => (k : Int)))
  | 0, i, h => by
    simp only [firstFrom, Option.map_none]
    exact isFirst_empty l x i l.length (by omega)
  | fuel + 1, i, h => by
    unfold firstFrom
    by_cases h1 : i < l.length
    · rw [iteT h1]
      by_cases h2 : ix l i = x
      · rw [iteT h2]; exact isFirst_here l x i l.length (by omega) (by omega) (by omega) h2
      · rw [iteF h2]
        have := firstFrom_spec l x fuel (i + 1) (by omega)
        rw [show ((i + 1 : Nat) : Int) = (i : Int) + 1 by omega] at this
        exact isFirst_step l x i l.length _ h2 this
    · rw [iteF h1]; exact isFirst_empty l x i l.length (by omega)

theorem find_isFirst (l : List Int) (x : Int) :
    IsFirst l x 0 l.length (((List.range l.length).find? (fun (k : Nat) => ix l k = x)).map (fun k : Nat => (k : Int))) := by
  cases hf : (List.range l.length).find? (fun (k : Nat) => ix l k = x) with
  | none =>
    intro j _ h2 h3 _ hx
    have := List.find?_eq_none.mp hf j.toNat (List.mem_range.mpr (by omega))
    simp only [decide_eq_true_eq] at this
    exact this (by rw [show ((j.toNat : Nat) : Int) = j by omega]; exact hx)
  | some k => 
    obtain ⟨hk, n, hn, hkn, hbefore⟩ := List.find?_eq_some_iff_getElem.mp hf
    simp only [decide_eq_true_eq] at hk
    rw [List.getElem_range] at hkn
    subst hkn
    simp only [Option.map_some]
    refine ⟨by omega, by simp only [List.length_range] at hn; omega, by omega,
      by simp only [List.length_range] at hn; omega, hk, fun j hj1 hj2 hj3 hx => ?_⟩
    have := hbefore j.toNat (by simp only [List.length_range] at hn; omega)
    simp [List.getElem_range] at this
    exact this (by rw [show max j 0 = j by omega]; exact hx)

theorem countLoop_spec (d : Deque) (hL : d.Layout) (v : Int) : ∀ (n : Nat) (p b j : Int),
    b * 64 + j - d.left = p → 0 ≤ j → j < 64 → 0 ≤ p → p + n ≤ d.size →
    d.countLoop v n b j = .ok ((((d.items.drop p.toNat).take n).filter (· == v)).length : Int) := by
  have h' := hL
  rw [Deque.layout_iff] at h'
  intro n
  induction n with
  | zero => intro p b j _ _ _ _ _; simp [Deque.countLoop]
  | succ n ih =>
    intro p b j hp h0 h1 hp0 hk
    simp only [Deque.countLoop, bind, Except.bind]
    rw [Deque.read_ok d hL b j (by dq_omega) (by dq_omega) h0 h1 (by omega) (by dq_omega)]
    simp only [hp]
    obtain ⟨c1, c2, c3⟩ := Deque.step1_pos d b j p hp h0 h1
    rw [ih (p + 1) _ _ c1 c2 c3 (by omega) (by omega)]
    simp only [pure, Except.pure, Except.ok.injEq]
    rw [Deque.size_eq] at hk
    rw [List.drop_eq_getElem_cons (show p.toNat < d.items.length by omega), List.take_succ_cons,
      List.filter_cons, show (p + 1).toNat = p.toNat + 1 by omega]
    have hix : ix d.items p = d.items[p.toNat] := by
      unfold ix; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    rw [hix]
    split <;> simp_all <;> omega

/-- For every list of ints `l`, `x` and optional index `i`:
`list.pop(i)` and `array.pop(i)` (any typecode) are `popSpec` with their own
empty-sequence message; `deque.pop()` / `deque.popleft()` (any deque with
items `l`, type invariant `WF`) are `list.pop()` / `list.pop(0)` with the
deque's message; `remove(x)` deletes the first equal item in all three
(`ValueError` with each type's message otherwise), and `count(x)` is the
same number for all three. -/
def PopRemoveCountAgree : Prop :=
  ∀ (l : List Int) (x : Int) (i : Option Int),
    listPop l i = popSpec "pop from empty list" l i ∧
    (∀ tc, (arrPop ⟨tc, l⟩ i).map (fun p => (p.1, p.2.items)) = popSpec "pop from empty array" l i) ∧
    listRemove l x = removeSpec "list.remove(x): x not in list" l x ∧
    (∀ tc, (arrRemove ⟨tc, l⟩ x).map (·.items) = removeSpec "array.remove(x): x not in array" l x) ∧
    (∀ tc, arrCount ⟨tc, l⟩ x = listCount l x) ∧
    (∀ d : Deque, d.WF → d.items = l →
      d.pop.map (fun p => (p.1, p.2.items)) = popSpec "pop from an empty deque" l none ∧
      d.popleft.map (fun p => (p.1, p.2.items)) = popSpec "pop from an empty deque" l (some 0) ∧
      (d.remove x).map (·.items) = removeSpec "deque.remove(x): x not in deque" l x ∧
      d.count x = .ok (listCount l x))

theorem firstFrom_eq_find (l : List Int) (x : Int) :
    firstFrom l x 0 l.length = (List.range l.length).find? (fun (k : Nat) => ix l k = x) := by
  have h1 := firstFrom_spec l x l.length 0 (by omega)
  have h2 := find_isFirst l x
  have := isFirst_unique _ _ _ _ _ _ h1 h2
  cases ha : firstFrom l x 0 l.length <;> cases hb : (List.range l.length).find? (fun (k : Nat) => ix l k = x) <;>
    rw [ha, hb] at this <;> simp_all <;> omega

theorem arrPop_eq (tc : TC) (l : List Int) (i : Option Int) :
    (arrPop ⟨tc, l⟩ i).map (fun p => (p.1, p.2.items)) = popSpec "pop from empty array" l i := by
  unfold arrPop popSpec
  cases popArg i with
  | error e => rfl
  | ok k =>
    simp only [bind, Except.bind, arrPopK, popSpecK]
    by_cases he : l.length = 0
    · rw [iteT (show ((l.length : Nat) : Int) = 0 by omega), iteT he]; rfl
    · rw [iteF (show ¬ ((l.length : Nat) : Int) = 0 by omega), iteF he]
      simp only [pure, Except.pure, validIndex, Except.map]
      generalize (if k < 0 then k + (l.length : Int) else k) = j
      by_cases hv : 0 ≤ j ∧ j < l.length
      · rw [iteF (by omega)]; simp [hv]
      · rw [iteT (by omega)]; simp [hv]; rfl

theorem dequePop_eq (d : Deque) (h : d.WF) :
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

theorem dequePopleft_eq (d : Deque) (h : d.WF) :
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

theorem dequeRemove_eq (d : Deque) (h : d.WF) (x : Int) :
    (d.remove x).map (·.items) = removeSpec "deque.remove(x): x not in deque" d.items x := by
  have hL := h.1
  have h' := h.1
  rw [Deque.layout_iff] at h'
  obtain ⟨r, hr, hf⟩ := Deque.findLoop_spec d hL x d.items.length 0 0 d.left (by omega) h'.1 h'.2.1
    (by omega) (by rw [Deque.size_eq]; omega)
  have hu := isFirst_unique _ _ _ _ _ _ hf (by simpa using find_isFirst d.items x)
  unfold Deque.remove removeSpec
  simp only [bind, Except.bind, hr]
  cases hfind : (List.range d.items.length).find? (fun (k : Nat) => ix d.items k = x) with
  | none => rw [hfind] at hu; simp at hu; subst hu; rfl
  | some k =>
    rw [hfind] at hu; simp at hu; subst hu
    obtain ⟨_, n, hn, hkn, _⟩ := List.find?_eq_some_iff_getElem.mp hfind
    rw [List.getElem_range] at hkn
    subst hkn
    simp only [List.length_range] at hn
    obtain ⟨d', hdel, _, hi, _⟩ := Deque.delItem_spec d n h (by omega) (by rw [Deque.size_eq]; omega)
    simp only [hdel, Except.map, hi]
    rfl

theorem dequeCount_eq (d : Deque) (h : d.WF) (x : Int) : d.count x = .ok (listCount d.items x) := by
  have h' := h.1
  rw [Deque.layout_iff] at h'
  unfold Deque.count
  rw [countLoop_spec d h.1 x d.items.length 0 0 d.left (by omega) h'.1 h'.2.1 (by omega)
    (by rw [Deque.size_eq]; omega)]
  simp [listCount]

theorem popRemoveCountAgree_proven : PopRemoveCountAgree := by
  intro l x i
  refine ⟨rfl, fun tc => arrPop_eq tc l i, ?_, fun tc => ?_, fun tc => rfl, fun d hd hl => ?_⟩
  · unfold listRemove removeSpec; rw [firstFrom_eq_find]; rfl
  · unfold arrRemove removeSpec; simp only; rw [firstFrom_eq_find]
    cases (List.find? (fun (k : Nat) => ix l k = x) (List.range l.length)) <;> rfl
  · subst hl
    exact ⟨dequePop_eq d hd, dequePopleft_eq d hd, dequeRemove_eq d hd x, dequeCount_eq d hd x⟩

end PyLean.Sequences
