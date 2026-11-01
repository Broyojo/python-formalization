import PyLean.BytesObj.Seq.Repr
import PyLean.BytesObj.Seq.SearchProps

/-!
`repr` of tuples and lists: the shape of the text, and termination on containers
that hold themselves.
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α : Type}

/-- The items separated by `", "`. -/
def commaJoin : List String → String
  | [] => ""
  | [x] => x
  | x :: y :: rest => x ++ ", " ++ commaJoin (y :: rest)

/-- With every item's repr known, the tuple loop writes the separated items. -/
theorem tupleReprLoop_tail (elem : α → Py String) (strs : α → String) (xs : List α) (i : Nat)
    (acc : String) (h : ∀ x ∈ xs, elem x = .ok (strs x)) (hi : 0 < i) :
    tupleReprLoop elem i xs acc =
      .ok (match xs with
        | [] => acc
        | _ :: _ => acc ++ ", " ++ commaJoin (xs.map strs)) := by
  induction xs generalizing i acc with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    simp only [tupleReprLoop, hx, show i > 0 from hi, if_true]
    rw [ih (i + 1) _ (fun y hy => h y (List.mem_cons_of_mem _ hy)) (by omega)]
    cases xs with
    | nil => simp [commaJoin]
    | cons y ys => simp [commaJoin, String.append_assoc]

theorem tupleReprLoop_head (elem : α → Py String) (strs : α → String) (xs : List α) (acc : String)
    (h : ∀ x ∈ xs, elem x = .ok (strs x)) :
    tupleReprLoop elem 0 xs acc = .ok (acc ++ commaJoin (xs.map strs)) := by
  cases xs with
  | nil => simp [tupleReprLoop, commaJoin]
  | cons x xs =>
    have hx := h x (by simp)
    simp only [tupleReprLoop, hx, show ¬ (0 : Nat) > 0 by omega, if_false]
    rw [tupleReprLoop_tail elem strs xs 1 _ (fun y hy => h y (List.mem_cons_of_mem _ hy)) (by omega)]
    cases xs with
    | nil => simp [commaJoin]
    | cons y ys => simp [commaJoin, String.append_assoc]

/-- The list loop on an unchanging list is the tuple loop, closed with `]`. -/
theorem listReprLoop_pure (elem : α → Py String) (o : LObj α) (f i : Nat) (acc : String)
    (hi : i ≤ o.items.length) (hf : o.items.length < i + f) :
    (listReprLoop (fun o x => (elem x, o)) f i acc o).1 =
      (tupleReprLoop elem i (o.items.drop i) acc).map (· ++ "]") := by
  induction f generalizing i acc with
  | zero => omega
  | succ f ih =>
    by_cases h : i < o.items.length
    · rw [listReprLoop, dif_pos h, drop_cons_of_lt _ _ h]
      simp only [tupleReprLoop]
      cases hc : elem o.items[i] with
      | error e => rfl
      | ok s => exact ih (i + 1) _ (by omega) (by omega)
    · rw [listReprLoop, dif_neg h, List.drop_eq_nil_of_le (by omega)]
      rfl

/-- The shape of `repr`, for every element type and every list of items whose reprs
succeed and leave the container alone: `(a, b)`, the trailing comma of `(a,)`, and
`[a, b]`. The empty forms are `()` and `[]`. -/
def ReprShape : Prop :=
  ∀ (α : Type) (elem : α → Py String) (strs : α → String) (o : LObj α) (fuel : Nat),
    (∀ x ∈ o.items, elem x = .ok (strs x)) → o.items.length < fuel →
    tupleRepr elem false o.items =
      .ok (if o.items.length = 0 then "()" else
        "(" ++ commaJoin (o.items.map strs) ++ (if o.items.length = 1 then ",)" else ")")) ∧
    (listRepr (fun o x => (elem x, o)) fuel false o).1 =
      .ok (if o.items.length = 0 then "[]" else "[" ++ commaJoin (o.items.map strs) ++ "]")

theorem reprShape_proven : ReprShape := by
  intro α elem strs o fuel h hf
  by_cases h0 : o.items.length = 0
  · simp [tupleRepr, listRepr, h0]
  · constructor
    · simp only [tupleRepr, h0, if_false, tupleReprBody, Bool.false_eq_true]
      rw [tupleReprLoop_head elem strs _ _ h]
    · simp only [listRepr, h0, if_false, Bool.false_eq_true]
      rw [listReprLoop_pure elem o fuel 0 "[" (by omega) (by omega)]
      simp only [List.drop_zero]
      rw [tupleReprLoop_head elem strs _ _ h]
      rfl

/-- The loops succeed when each element does. -/
theorem tupleReprLoop_ok (elem : α → Py String) (xs : List α) (i : Nat) (acc : String)
    (h : ∀ x ∈ xs, ∃ s, elem x = .ok s) : ∃ s, tupleReprLoop elem i xs acc = .ok s := by
  induction xs generalizing i acc with
  | nil => exact ⟨acc, rfl⟩
  | cons x xs ih =>
    obtain ⟨s, hs⟩ := h x (by simp)
    simp only [tupleReprLoop, hs]
    exact ih _ _ (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- Every reference in the heap points into the heap. -/
def RObj.Valid (h : RHeap) : RObj → Prop
  | .atom _ => True
  | .ref id => id < h.length

def RHeap.Valid (h : RHeap) : Prop := ∀ c ∈ h, ∀ x ∈ c.items, RObj.Valid h x

theorem reprObj_ok (h : RHeap) (hv : h.Valid) (fuel : Nat) (stack : List Nat) (obj : RObj)
    (hobj : RObj.Valid h obj) (hnd : stack.Nodup) (hsub : ∀ i ∈ stack, i < h.length)
    (hf : h.length - stack.length + 1 ≤ fuel) :
    ∃ s, reprObj h fuel stack obj = .ok s := by
  induction fuel generalizing stack obj with
  | zero => omega
  | succ fuel ih =>
    cases obj with
    | atom s => exact ⟨s, rfl⟩
    | ref id =>
      have hid : id < h.length := hobj
      have hcell : h[id]? = some h[id] := List.getElem?_eq_getElem hid
      simp only [reprObj, hcell]
      have hmem : h[id] ∈ h := List.getElem_mem hid
      by_cases hin : id ∈ stack
      · have hc : stack.contains id = true := by simpa using hin
        rw [hc]
        by_cases hl : h[id].isList = true
        · by_cases h0 : h[id].items.length = 0
          · exact ⟨"[]", by simp [listRepr, hl, h0]⟩
          · exact ⟨"[...]", by simp [listRepr, hl, h0]⟩
        · by_cases h0 : h[id].items.length = 0
          · exact ⟨"()", by simp [tupleRepr, hl, h0]⟩
          · exact ⟨"(...)", by simp [tupleRepr, hl, h0]⟩
      · have hc : stack.contains id = false := by simpa using hin
        rw [hc]
        have hnd' : (id :: stack).Nodup := List.nodup_cons.mpr ⟨hin, hnd⟩
        have hsub' : ∀ i ∈ id :: stack, i < h.length := by
          intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact hid
          · exact hsub i hi
        have hcard : (id :: stack).length ≤ (List.range h.length).length :=
          List.Nodup.length_le_of_subset hnd' (fun i hi => List.mem_range.mpr (hsub' i hi))
        have hlen : stack.length + 1 ≤ h.length := by simpa using hcard
        have helem : ∀ x ∈ h[id].items, ∃ s, reprObj h fuel (id :: stack) x = .ok s := by
          intro x hx
          refine ih (id :: stack) x (hv _ hmem x hx) hnd' hsub' ?_
          simp only [List.length_cons]
          omega
        by_cases hl : h[id].isList = true
        · by_cases h0 : h[id].items.length = 0
          · exact ⟨"[]", by simp [listRepr, hl, h0]⟩
          · obtain ⟨s, hs⟩ := tupleReprLoop_ok (reprObj h fuel (id :: stack))
              h[id].items 0 "[" helem
            have hp := listReprLoop_pure (reprObj h fuel (id :: stack))
              ({ items := h[id].items } : LObj RObj) (h[id].items.length + 1) 0 "[" (by simp) (by simp)
            simp only [List.drop_zero] at hp
            rw [hs] at hp
            refine ⟨s ++ "]", ?_⟩
            simp only [hl, if_true, listRepr, h0, if_false, Bool.false_eq_true]
            exact hp
        · by_cases h0 : h[id].items.length = 0
          · exact ⟨"()", by simp [tupleRepr, hl, h0]⟩
          · obtain ⟨s, hs⟩ := tupleReprLoop_ok (reprObj h fuel (id :: stack)) h[id].items 0 "(" helem
            refine ⟨s ++ (if h[id].items.length = 1 then ",)" else ")"), ?_⟩
            simp only [hl, if_false, tupleRepr, h0, Bool.false_eq_true, tupleReprBody, hs]

/-- `repr` terminates on every heap of lists and tuples, however they refer to each
other, cycles included: `Py_ReprEnter` cuts each cycle (`[...]`, `(...)`), and the
depth never exceeds the number of containers plus one. Every reference pointing into
the heap is the type invariant. This model has no `Py_EnterRecursiveCall`, so it
says nothing about `RecursionError` on deep but finite nesting. -/
def ReprTerminates : Prop :=
  ∀ (h : RHeap) (obj : RObj), h.Valid → RObj.Valid h obj →
    ∃ s, reprObj h (h.length + 1) [] obj = .ok s

theorem reprTerminates_proven : ReprTerminates := by
  intro h obj hv hobj
  exact reprObj_ok h hv _ [] obj hobj List.nodup_nil (by simp) (by simp)

end PyLean.BytesObj.Seq
