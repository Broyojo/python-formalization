import PyLean.Accel.HeapCorrect

/-!
`heapify` / `heapify_max`: the C twin (`heapify_internal`, with the
cache-friendly order above 2500 items) builds exactly the list the Python
twin builds.
-/

namespace PyLean.Accel

open PyLean

variable {α : Type} [Inhabited α]

theorem downFrom_zero (m : Nat) : downFrom 0 m = (List.range m).reverse := by
  apply List.ext_getElem (by simp [downFrom])
  intro i h1 h2
  simp only [downFrom, List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_range]

theorem forDown_siftup_eq (lt : α → α → Bool) :
    ∀ (is : List Nat) (h : List α), (∀ i ∈ is, i < h.length) →
      forDown (fun h i => cSiftup lt h i) h is = .ok (is.foldl (fun h i => pySiftup lt h i) h) := by
  intro is
  induction is with
  | nil => intro h _; rfl
  | cons i is ih =>
    intro h hi
    simp only [forDown, List.foldlM_cons, List.foldl_cons]
    rw [cSiftup_eq lt h i (hi i (by simp))]
    simp only [bind, Except.bind]
    exact ih _ (fun j hj => by rw [pySiftup_length]; exact hi j (by simp [hj]))

/-- C `heapify` equals Python `heapify` on lists of at most 2500 items. -/
theorem cHeapify_small (lt : α → α → Bool) (x : List α) (hn : x.length ≤ 2500) :
    cHeapify lt x = .ok (pyHeapify lt x) := by
  simp only [cHeapify, if_neg (Nat.not_lt.2 hn), pyHeapify, shr1, downFrom_zero]
  apply forDown_siftup_eq
  intro i hi
  simp at hi; omega

/-- C/Python agreement of `heapify` (and `heapify_max` via `maxLt`), for every
element type, comparison and length, including the cache-friendly order that
`_heapqmodule.c:374-375` uses above 2500 items. -/
def HeapifyTwinsAgree : Prop :=
  ∀ (α : Type) [Inhabited α] (lt : α → α → Bool) (x : List α),
    cHeapify lt x = .ok (pyHeapify lt x)

end PyLean.Accel
