import PyLean.BytesObj.Seq.ListRows6
import PyLean.ListSort.FallibleSort

/-!
The compares `list.sort` selects, tied to the sort; `sortslice_reverse` slot by slot; `PyList_Reverse`'s
refusal (Objects/listobject.c, CPython 3.15.2).
-/

namespace PyLean.BytesObj.Seq

open PyLean PyLean.ListSort

variable {α ρ : Type}

theorem tupleGo_first (E : ElemOps α ρ) (first first' : α → α → Py Bool) :
    ∀ (i : Nat) (xs ys : List α), 0 < i →
      unsafeTupleCompare.go E first i xs ys = unsafeTupleCompare.go E first' i xs ys := by
  intro i xs
  induction xs generalizing i with
  | nil => intro ys _; cases ys <;> rfl
  | cons x xs ih =>
    intro ys hi
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [unsafeTupleCompare.go]
      cases richBool E .eq x y with
      | error e => rfl
      | ok b =>
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.ne_of_gt hi, if_false]
        · exact ih (i + 1) ys (by omega)

/-- The compares `list.sort` selects (listobject.c:2788-2938), tied to the sort:

* `safe_object_compare` (:2788-2792) is the comparison the fallible sort runs when the pre-sort check
  finds nothing to specialise: `PyObject_RichCompareBool(v, w, Py_LT)`. So `list.sort` with it leaves a
  permutation whatever `__lt__` does, and when `__lt__` never raises on the items it is the model's sort
  with that order;
* `unsafe_tuple_compare` (:2904-2938) calls `ms->tuple_elem_compare` exactly when the first elements
  differ (`i == 0`, :2934-2935), with its answer as the result, and never after an equal first element;
  so it is `tuple.__lt__` for every `tuple_elem_compare` that agrees with `<` on the first elements. -/
def SortCompareTied : Prop :=
  ∀ (α ρ : Type) (E : ElemOps α ρ) (first : α → α → Py Bool) (x y : α) (xs ys l : List α) (reverse : Bool),
    (listSortImplF (safeObjectCompare E) l reverse).1.Perm l ∧
    (∀ (f : α → α → Bool), (∀ a b, richBool E .lt a b = .ok (f a b)) →
      listSortImplF (safeObjectCompare E) l reverse = (listSort f l reverse, none)) ∧
    (richBool E .eq x y = .ok false → unsafeTupleCompare E first (x :: xs) (y :: ys) = first x y) ∧
    (richBool E .eq x y = .ok true →
      unsafeTupleCompare E first (x :: xs) (y :: ys) = unsafeTupleCompare.go E first 1 xs ys ∧
      ∀ first', unsafeTupleCompare E first (x :: xs) (y :: ys) = unsafeTupleCompare E first' (x :: xs) (y :: ys)) ∧
    (∀ e, richBool E .eq x y = .error e → unsafeTupleCompare E first (x :: xs) (y :: ys) = .error e) ∧
    ((∀ b, E.truth (E.ofBool b) = .ok b) → first x y = richBool E .lt x y →
      unsafeTupleCompare E first (x :: xs) (y :: ys) =
        (match tupleRichcompare E .lt (x :: xs) (y :: ys) with
         | .ok r => E.truth r
         | .error e => .error e))

theorem sortCompareTied_proven : SortCompareTied := by
  intro α ρ E first x y xs ys l reverse
  refine ⟨?_, fun f hf => ?_, fun h => ?_, fun h => ?_, fun e h => ?_, fun ht hfirst => ?_⟩
  · exact sortPermOnError_proven α (safeObjectCompare E) l reverse
  · have hp : safeObjectCompare E = pureLt f := by
      funext a b; exact hf a b
    rw [hp]
    exact (sortFallibleAgree_proven α α f l [] [] x (fun _ => x) 0 0 0 {} reverse id f).2.2.2.2.2.2.2.2.1
  · simp only [unsafeTupleCompare, unsafeTupleCompare.go, h, ↓reduceIte]
  · refine ⟨by simp only [unsafeTupleCompare, unsafeTupleCompare.go, h], fun first' => ?_⟩
    simp only [unsafeTupleCompare, unsafeTupleCompare.go, h]
    exact tupleGo_first E first first' 1 xs ys (by omega)
  · simp only [unsafeTupleCompare, unsafeTupleCompare.go, h]
  · have hsame : unsafeTupleCompare E first (x :: xs) (y :: ys) =
        unsafeTupleCompare E (fun a b => richBool E .lt a b) (x :: xs) (y :: ys) := by
      simp only [unsafeTupleCompare, unsafeTupleCompare.go]
      cases hq : richBool E .eq x y with
      | error e => rfl
      | ok b =>
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte, hfirst]
        · exact tupleGo_first E first _ 1 xs ys (by omega)
    rw [hsame]
    exact unsafeTuple_go E ht (x :: xs) (y :: ys) 0

/-- `sortslice_reverse(s, n)` (listobject.c:1956-1961) reverses the first `n` slots of the keys and,
when there are values, of the values, and leaves the rest: slot `t < n` gets what slot `n - 1 - t` held.
`PyList_Reverse` (:3263-3278) refuses a non-list with `SystemError`. -/
def SortsliceReverseSlots : Prop :=
  ∀ (κ α : Type) (s : SortSlice κ α) (vs : List α) (n t : Nat), n ≤ s.keys.length →
    ((sortsliceReverse s n).keys[t]? = if t < n then s.keys[n - 1 - t]? else s.keys[t]?) ∧
    (s.values = some vs → n ≤ vs.length → ∃ w, (sortsliceReverse s n).values = some w ∧
      w[t]? = if t < n then vs[n - 1 - t]? else vs[t]?) ∧
    (s.values = none → (sortsliceReverse s n).values = none) ∧
    pyListReverse (none : Option (LObj α)) = .error systemError

theorem rev_get {β : Type} (l : List β) (n t : Nat) (h : n ≤ l.length) :
    ((l.take n).reverse ++ l.drop n)[t]? = if t < n then l[n - 1 - t]? else l[t]? := by
  have hl : ((l.take n).reverse).length = n := by simp; omega
  by_cases ht : t < n
  · rw [List.getElem?_append_left (by omega), List.getElem?_reverse (by simp; omega), if_pos ht,
      List.getElem?_take]
    simp only [List.length_take, Nat.min_eq_left h]
    rw [if_pos (by omega)]
  · rw [List.getElem?_append_right (by omega), hl, List.getElem?_drop, if_neg ht]
    congr 1; omega

theorem sortsliceReverseSlots_proven : SortsliceReverseSlots := by
  intro κ α s vs n t hn
  refine ⟨?_, fun h1 h2 => ?_, fun h1 => ?_, rfl⟩
  · exact rev_get s.keys n t hn
  · refine ⟨(vs.take n).reverse ++ vs.drop n, by simp [sortsliceReverse, h1], rev_get vs n t h2⟩
  · simp [sortsliceReverse, h1]

end PyLean.BytesObj.Seq
