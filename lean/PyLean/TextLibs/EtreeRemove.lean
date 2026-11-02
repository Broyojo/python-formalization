import PyLean.TextLibs.EtreeWriters

/-!
`Element.remove(subelement)`: the C accelerator (Modules/_elementtree.c:1663-1720) against the
pure-Python twin (Lib/xml/etree/ElementTree.py:247-270), which calls `list.remove`
(`list_remove_impl`, Objects/listobject.c:3425-3444).

Children are compared by identity (`DecidableEq`) and then with `==`. A child's `__eq__` is
`cmp`: it may raise, and it may change the element's children in place (append, insert, delete,
slice assignment), threading its own state `σ`. `clear()` is out of scope: the twin rebinds
`self._children`, so an `__eq__` calling it acts on different lists in the two twins. A
comparison that keeps growing the children never ends in either twin; `fuel` bounds both loops
alike.
-/

namespace PyLean.TextLibs.Etree

open PyLean PyLean.Sequences

variable {α σ : Type} [DecidableEq α]

/-- `PyObject_RichCompareBool(child, x, Py_EQ)` for a child that is not `x`: the result, the
children afterwards, the comparator's state afterwards. -/
abbrev Cmp (α σ : Type) := σ → List α → α → α → Py Bool × List α × σ

/-- The search loop of `Element.remove`, :1680-1696: `i` walks while `extra` exists and
`i < length` (re-read each pass); identity, then `==`. Returns the index found, if any. -/
def removeLoopC (cmp : Cmp α σ) (x : α) : Nat → σ → List α → Nat → List α × σ × Py (Option Nat)
  | 0, s, kids, _ => (kids, s, .error .modelFuel)
  | f + 1, s, kids, i =>
    match kids[i]? with
    | none => (kids, s, .ok none)
    | some c =>
      if c = x then (kids, s, .ok (some i))
      else
        match cmp s kids c x with
        | (.error e, kids, s) => (kids, s, .error e)
        | (.ok true, kids, s) => (kids, s, .ok (some i))
        | (.ok false, kids, s) => removeLoopC cmp x f s kids (i + 1)

/-- `Element.remove` for an Element `x` (Clinic has checked the type), :1673-1720: not found is
`ValueError("%R not in %R")`; found at `i` removes it unless the comparison left fewer than
`i + 1` children. -/
def removeC (cmp : Cmp α σ) (fuel : Nat) (s : σ) (kids : List α) (x : α) : List α × Py Unit :=
  match removeLoopC cmp x fuel s kids 0 with
  | (kids, _, .error e) => (kids, .error e)
  | (kids, _, .ok none) => (kids, .error (.valueError "~%R not in %R"))
  | (kids, _, .ok (some i)) => if i < kids.length then (kids.eraseIdx i, .ok ()) else (kids, .ok ())

/-- `list_remove_impl`'s loop, listobject.c:3430-3440: `i < Py_SIZE(self)` each pass;
`PyObject_RichCompareBool` returns 1 for identity without calling `__eq__`. -/
def listRemoveLoop (cmp : Cmp α σ) (x : α) : Nat → σ → List α → Nat → List α × σ × Py (Option Nat)
  | 0, s, l, _ => (l, s, .error .modelFuel)
  | f + 1, s, l, i =>
    if h : i < l.length then
      let obj := l[i]
      let (r, l, s) := if obj = x then (.ok true, l, s) else cmp s l obj x
      match r with
      | .error e => (l, s, .error e)
      | .ok true => (l, s, .ok (some i))
      | .ok false => listRemoveLoop cmp x f s l (i + 1)
    else (l, s, .ok none)

/-- `list.remove(x)`: `list_ass_slice(self, i, i+1, NULL)` clips `i` to the current size, so a
match whose slot the comparison removed deletes nothing. -/
def listRemoveM (cmp : Cmp α σ) (fuel : Nat) (s : σ) (l : List α) (x : α) : List α × Py Unit :=
  match listRemoveLoop cmp x fuel s l 0 with
  | (l, _, .error e) => (l, .error e)
  | (l, _, .ok none) => (l, .error (.valueError "list.remove(x): x not in list"))
  | (l, _, .ok (some i)) => (listAssSlice l (i : Int) ((i : Int) + 1) [], .ok ())

/-- `Element.remove` in the twin, for an Element `x`: any `ValueError`, including one raised by an
`__eq__`, becomes `ValueError(f"{subelement!r} not in {self!r}")`. -/
def removePy (cmp : Cmp α σ) (fuel : Nat) (s : σ) (kids : List α) (x : α) : List α × Py Unit :=
  match listRemoveM cmp fuel s kids x with
  | (l, .error (.valueError _)) => (l, .error (.valueError "~%r not in %r"))
  | r => r

/-- For every comparator, however it raises or mutates the children in place, `remove` of an
Element leaves the same children and raises the same exception class in both twins. -/
def RemoveTwins : Prop :=
  ∀ (α σ : Type) [DecidableEq α] (cmp : Cmp α σ) (fuel : Nat) (s : σ) (kids : List α) (x : α),
    (removeC cmp fuel s kids x).1 = (removePy cmp fuel s kids x).1 ∧
    Agree (removeC cmp fuel s kids x).2 (removePy cmp fuel s kids x).2

theorem removeLoop_same (cmp : Cmp α σ) (x : α) (f : Nat) (s : σ) (kids : List α) (i : Nat) :
    removeLoopC cmp x f s kids i = listRemoveLoop cmp x f s kids i := by
  induction f generalizing s kids i with
  | zero => rfl
  | succ f ih =>
    unfold removeLoopC listRemoveLoop
    by_cases h : i < kids.length
    · rw [List.getElem?_eq_getElem h, dif_pos h]
      simp only
      by_cases hx : kids[i] = x
      · simp [hx]
      · simp only [hx, if_false]
        rcases hc : cmp s kids kids[i] x with ⟨r, l, s'⟩
        rcases r with e | b
        · rfl
        · cases b
          · exact ih s' l (i + 1)
          · rfl
    · rw [List.getElem?_eq_none (by omega), dif_neg h]

theorem eraseIdx_slice (l : List α) (i : Nat) (h : i < l.length) :
    l.eraseIdx i = listAssSlice l (i : Int) ((i : Int) + 1) [] := by
  unfold listAssSlice
  simp only [List.append_nil]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show ((i : Int)).toNat = i by omega, show ((i : Int) + 1).toNat = i + 1 by omega, List.eraseIdx_eq_take_drop_succ]

theorem slice_noop (l : List α) (i : Nat) (h : ¬ i < l.length) :
    listAssSlice l (i : Int) ((i : Int) + 1) [] = l := by
  unfold listAssSlice
  dsimp only
  rw [List.take_of_length_le (by (repeat' split) <;> omega),
    List.drop_eq_nil_of_le (by (repeat' split) <;> omega)]
  simp

theorem removeTwins_proven : RemoveTwins := by
  intro α σ _ cmp fuel s kids x
  unfold removeC removePy listRemoveM
  rw [removeLoop_same]
  rcases listRemoveLoop cmp x fuel s kids 0 with ⟨l, s', r⟩
  rcases r with e | o
  · cases e <;> simp [Agree, PyExc.className]
  · rcases o with _ | i
    · simp [Agree, PyExc.className]
    · by_cases h : i < l.length
      · simp [h, eraseIdx_slice l i h, Agree]
      · simp [h, slice_noop l i h, Agree]

end PyLean.TextLibs.Etree
