import PyLean.Accel.Select
import PyLean.Accel.BisectProps
import PyLean.Accel.HeapProps

/-!
`nsmallest`, `nlargest` and `merge` against the "equivalent" `sorted(...)`
expressions their docs give.
-/

namespace PyLean.Accel

open PyLean

/-- Sorted by key in descending order. -/
def SortedRevBy (key : Option (Int → Int)) (a : List Int) : Prop :=
  a.Pairwise (fun u v => applyKey key v ≤ applyKey key u)

/-- `nsmallest` docstring, Lib/heapq.py:477-481 and Doc/library/heapq.rst:188-193:
"Equivalent to: `sorted(iterable, key=key)[:n]`", for every count `n >= 0`
(negative `n` has no meaning, python/cpython#57483), sized or not, with or
without key, including the order of items with equal keys. -/
def NsmallestIsSortedPrefix : Prop :=
  ∀ (n : Int) (it : List Int) (sized : Bool) (key : Option (Int → Int)), 0 ≤ n →
    nsmallest n it sized key = .ok (sliceTo (pySorted key it) n)

/-- `nlargest` docstring, Lib/heapq.py:537-541 and Doc/library/heapq.rst:179-185:
"Equivalent to: `sorted(iterable, key=key, reverse=True)[:n]`", for `n >= 0`. -/
def NlargestIsSortedPrefix : Prop :=
  ∀ (n : Int) (it : List Int) (sized : Bool) (key : Option (Int → Int)), 0 ≤ n →
    nlargest n it sized key = .ok (sliceTo (pySortedRev key it) n)

/-- `merge` docstring, Lib/heapq.py:330-346 and Doc/library/heapq.rst:154-176:
for inputs each sorted by key (descending when `reverse=True`), the output is
`sorted(itertools.chain(*iterables), key=key, reverse=reverse)`, ties included. -/
def MergeIsSorted : Prop :=
  ∀ (its : List (List Int)) (key : Option (Int → Int)) (reverse : Bool),
    (∀ it ∈ its, if reverse then SortedRevBy key it else SortedBy key it) →
    merge its key reverse =
      .ok (if reverse then pySortedRev key its.flatten else pySorted key its.flatten)

end PyLean.Accel
