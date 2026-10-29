import PyLean.Accel.Heap

/-!
The C heap primitives compute exactly what the Python ones compute, for every
element type and every comparison `lt` (so for the min-heap functions, the
`*_max` functions via `maxLt`, and the tuple comparisons that `merge`,
`nsmallest` and `nlargest` feed them). The C sift loops swap where the Python
ones move items into a hole; the invariant is that the C list is the Python
list with the hole filled by `newitem`.
-/

namespace PyLean.Accel

open PyLean

variable {α : Type} [Inhabited α]

theorem at!_set (l : List α) (i j : Nat) (v : α) :
    at! (l.set i v) j = if i = j ∧ i < l.length then v else at! l j := by
  simp only [at!, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · subst h
    by_cases h2 : i < l.length <;> simp [h2]
  · simp [h]

theorem at!_set_ne (l : List α) (i j : Nat) (v : α) (h : i ≠ j) :
    at! (l.set i v) j = at! l j := by
  rw [at!_set]; simp [h]

theorem at!_set_self (l : List α) (i : Nat) (v : α) (h : i < l.length) :
    at! (l.set i v) i = v := by
  rw [at!_set]; simp [h]

theorem set_at!_self (l : List α) (i : Nat) : l.set i (at! l i) = l := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  rw [List.getElem_set]
  split
  · subst_vars; simp [at!, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  · rfl

/-! ### siftdown -/

theorem siftdownLoop_twins (lt : α → α → Bool) (newitem : α) (s : Nat) :
    ∀ (fuel : Nat) (heap : List α) (pos : Nat), pos < heap.length →
      cSiftdownLoop lt newitem s fuel (heap.set pos newitem) pos =
        let r := pySiftdownLoop lt newitem s fuel heap pos
        r.1.set r.2 newitem := by
  intro fuel
  induction fuel with
  | zero => intro heap pos _; simp [cSiftdownLoop, pySiftdownLoop]
  | succ fuel ih =>
    intro heap pos hpos
    simp only [cSiftdownLoop, pySiftdownLoop]
    split
    · rename_i hgt
      have hpp : (pos - 1) >>> 1 < pos := by rw [Nat.shiftRight_eq_div_pow]; omega
      rw [at!_set_ne heap pos ((pos - 1) >>> 1) newitem (by omega)]
      split
      · rw [at!_set_self _ _ _ hpos]
        have := ih (heap.set pos (at! heap ((pos - 1) >>> 1))) ((pos - 1) >>> 1) (by simp; omega)
        rw [← this]
        congr 1
        rw [List.set_comm _ _ (show pos ≠ (pos - 1) >>> 1 by omega), List.set_set,
          List.set_comm _ _ (show (pos - 1) >>> 1 ≠ pos by omega)]
      · rfl
    · rfl

theorem cSiftdown_eq (lt : α → α → Bool) (heap : List α) (s pos : Nat) (h : pos < heap.length) :
    cSiftdown lt heap s pos = .ok (pySiftdown lt heap s pos) := by
  simp only [cSiftdown, pySiftdown, if_neg (Nat.not_le.2 h)]
  have := siftdownLoop_twins lt (at! heap pos) s pos heap pos h
  rw [set_at!_self] at this
  rw [this]

theorem pySiftdownLoop_length (lt : α → α → Bool) (newitem : α) (s : Nat) :
    ∀ (fuel : Nat) (heap : List α) (pos : Nat),
      (pySiftdownLoop lt newitem s fuel heap pos).1.length = heap.length := by
  intro fuel
  induction fuel with
  | zero => intro heap pos; rfl
  | succ fuel ih =>
    intro heap pos
    simp only [pySiftdownLoop]
    split
    · split
      · rw [ih]; simp
      · rfl
    · rfl

theorem pySiftdown_length (lt : α → α → Bool) (heap : List α) (s pos : Nat) :
    (pySiftdown lt heap s pos).length = heap.length := by
  simp [pySiftdown, pySiftdownLoop_length]

/-! ### siftup -/

theorem siftupLoop_twins (lt : α → α → Bool) (newitem : α) (endpos : Nat) :
    ∀ (fuel : Nat) (heap : List α) (pos : Nat), pos < heap.length → heap.length = endpos →
      cSiftupLoop lt endpos (endpos >>> 1) fuel (heap.set pos newitem) pos =
        ((pySiftupLoop lt endpos fuel heap pos).1.set (pySiftupLoop lt endpos fuel heap pos).2 newitem,
          (pySiftupLoop lt endpos fuel heap pos).2) ∧
      (pySiftupLoop lt endpos fuel heap pos).2 < heap.length ∧
      (pySiftupLoop lt endpos fuel heap pos).1.length = heap.length := by
  intro fuel
  induction fuel with
  | zero => intro heap pos h _; simp [cSiftupLoop, pySiftupLoop, h]
  | succ fuel ih =>
    intro heap pos hpos hlen
    have hlim : (pos < endpos >>> 1) ↔ (2 * pos + 1 < endpos) := by
      rw [Nat.shiftRight_eq_div_pow]; omega
    simp only [cSiftupLoop, pySiftupLoop]
    by_cases hc : 2 * pos + 1 < endpos
    · rw [if_pos (hlim.2 hc), if_pos hc]
      rw [at!_set_ne heap pos (2 * pos + 1) newitem (by omega),
        at!_set_ne heap pos (2 * pos + 1 + 1) newitem (by omega)]
      -- the chosen child is the same in both twins
      have hch : (if 2 * pos + 1 + 1 < endpos then
            (if lt (at! heap (2 * pos + 1)) (at! heap (2 * pos + 1 + 1)) = true then 2 * pos + 1
             else 2 * pos + 1 + 1) else 2 * pos + 1) =
          (if 2 * pos + 1 + 1 < endpos ∧ (!lt (at! heap (2 * pos + 1)) (at! heap (2 * pos + 1 + 1))) = true
           then 2 * pos + 1 + 1 else 2 * pos + 1) := by
        by_cases h1 : 2 * pos + 1 + 1 < endpos <;>
          cases h2 : lt (at! heap (2 * pos + 1)) (at! heap (2 * pos + 1 + 1)) <;> simp [h1]
      rw [hch]
      generalize hcp : (if 2 * pos + 1 + 1 < endpos ∧ (!lt (at! heap (2 * pos + 1)) (at! heap (2 * pos + 1 + 1))) = true
           then 2 * pos + 1 + 1 else 2 * pos + 1) = cp
      have hcp1 : pos < cp ∧ cp < endpos := by
        rw [← hcp]; split <;> omega
      rw [at!_set_ne heap pos cp newitem (by omega), at!_set_self _ _ _ hpos]
      have := ih (heap.set pos (at! heap cp)) cp (by simp; omega) (by simp; omega)
      obtain ⟨h1, h2, h3⟩ := this
      refine ⟨?_, by simpa using h2, by simpa using h3⟩
      rw [← h1]
      congr 1
      rw [List.set_comm _ _ (show pos ≠ cp by omega), List.set_set,
        List.set_comm _ _ (show cp ≠ pos by omega)]
    · rw [if_neg (fun h => hc (hlim.1 h)), if_neg hc]
      exact ⟨rfl, hpos, rfl⟩

theorem cSiftup_eq (lt : α → α → Bool) (heap : List α) (pos : Nat) (h : pos < heap.length) :
    cSiftup lt heap pos = .ok (pySiftup lt heap pos) := by
  simp only [cSiftup, pySiftup, if_neg (Nat.not_le.2 h)]
  obtain ⟨h1, h2, h3⟩ := siftupLoop_twins lt (at! heap pos) heap.length heap.length heap pos h rfl
  rw [set_at!_self] at h1
  rw [h1]
  exact cSiftdown_eq lt _ pos _ (by simp [h3, h2])

theorem pySiftupLoop_length (lt : α → α → Bool) (endpos : Nat) :
    ∀ (fuel : Nat) (heap : List α) (pos : Nat),
      (pySiftupLoop lt endpos fuel heap pos).1.length = heap.length := by
  intro fuel
  induction fuel with
  | zero => intro heap pos; rfl
  | succ fuel ih =>
    intro heap pos
    simp only [pySiftupLoop]
    split
    · rw [ih]; simp
    · rfl

theorem pySiftup_length (lt : α → α → Bool) (heap : List α) (pos : Nat) :
    (pySiftup lt heap pos).length = heap.length := by
  simp [pySiftup, pySiftdown_length, pySiftupLoop_length]

/-! ### The public functions -/

/-- Same outcome, comparing exceptions by class only. -/
def SameUpToMsg {β : Type} : Py β → Py β → Prop
  | .ok a, .ok b => a = b
  | .error e1, .error e2 => e1.className = e2.className
  | _, _ => False

/-- C/Python agreement of `heappush`, `heappop`, `heapreplace`, `heappushpop`
(and, through `lt := maxLt lt`, their `_max` variants), for every element type
and comparison: same returned item, same final list, and an exception of the
same class. -/
def HeapTwinsAgree : Prop :=
  ∀ (α : Type) [Inhabited α] (lt : α → α → Bool) (heap : List α) (item : α),
    cHeappush lt heap item = .ok (pyHeappush lt heap item) ∧
    SameUpToMsg (cHeappop lt heap) (pyHeappop lt heap) ∧
    SameUpToMsg (cHeapreplace lt heap item) (pyHeapreplace lt heap item) ∧
    cHeappushpop lt heap item = .ok (pyHeappushpop lt heap item)

theorem heapTwinsAgree_proven : HeapTwinsAgree := by
  intro α _ lt heap item
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [cHeappush, pyHeappush]
    exact cSiftdown_eq lt _ 0 _ (by simp)
  · cases heap with
    | nil => exact rfl
    | cons y ys =>
      have hl : (y :: ys).getLast? = some (at! (y :: ys) ys.length) := by
        rw [List.getLast?_eq_getElem?]
        simp [at!, List.getD_eq_getElem?_getD]
      have hd : (y :: ys).dropLast = (y :: ys).take ys.length := by
        rw [List.dropLast_eq_take]; simp
      simp only [cHeappop, pyHeappop, hl, hd, List.length_cons, Nat.add_sub_cancel]
      by_cases h0 : ys.length = 0
      · have : ys = [] := List.eq_nil_of_length_eq_zero h0
        subst this
        simp [SameUpToMsg, pure, Except.pure, bind, Except.bind]
      · have hne : (y :: ys).take ys.length ≠ [] := by
          apply List.ne_nil_of_length_pos
          simp only [List.length_take, List.length_cons]; omega
        simp only [h0, hne, if_false, ne_eq, not_false_eq_true, if_true]
        rw [cSiftup_eq lt _ 0 (by simp only [List.length_set, List.length_take, List.length_cons]; omega)]
        simp [SameUpToMsg, pure, Except.pure, bind, Except.bind]
  · cases heap with
    | nil => exact rfl
    | cons y ys =>
      simp only [cHeapreplace, pyHeapreplace, List.length_cons, Nat.add_one_ne_zero, if_false,
        reduceCtorEq]
      rw [cSiftup_eq lt _ 0 (by simp)]
      simp [SameUpToMsg, pure, Except.pure, bind, Except.bind]
  · cases heap with
    | nil => simp [cHeappushpop, pyHeappushpop, pure, Except.pure]
    | cons y ys =>
      simp only [cHeappushpop, pyHeappushpop, List.length_cons, Nat.add_one_ne_zero, if_false,
        ne_eq, reduceCtorEq, not_false_eq_true, true_and]
      cases hlt : lt (at! (y :: ys) 0) item
      · simp [pure, Except.pure]
      · simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true]
        rw [cSiftup_eq lt _ 0 (by simp)]
        simp [pure, Except.pure, bind, Except.bind]

/-- C/Python agreement including the exception message. -/
def HeapTwinsAgreeExact : Prop :=
  ∀ (heap : List Int) (item : Int),
    (cHeappop (fun a b => decide (a < b)) heap).map Prod.fst =
      (pyHeappop (fun a b => decide (a < b)) heap).map Prod.fst ∧
    (cHeapreplace (fun a b => decide (a < b)) heap item).map Prod.fst =
      (pyHeapreplace (fun a b => decide (a < b)) heap item).map Prod.fst

/-- `heappop([])` raises `IndexError('index out of range')` in C and
`IndexError('pop from empty list')` in Python. -/
theorem heapTwinsAgreeExact_refuted : ¬HeapTwinsAgreeExact := by
  intro h
  have := (h [] 0).1
  revert this
  decide

end PyLean.Accel
