import PyLean.Accel.HeapProps
import PyLean.Accel.HeapTwins

/-!
`heapq` with a comparison that can raise, for `sched.scheduler` and `queue.PriorityQueue`.

`PyLean.Accel.Heap` models `Modules/_heapqmodule.c` over a total `lt : α → α → Bool`. `sched` and
`queue` hand user objects to `heapq`, and there `<` can raise. The heap is a Python list mutated in
place, so an exception leaves the list as far as the sift got: every function here returns the
list next to an optional exception. `heappushP` and `heappopP` are proved equal to the `Accel`
functions when the comparison cannot raise (`heappushP_pure`, `heappopP_pure`), which is how the
correctness theorems of `Accel` reach `sched` and `queue`.
-/

namespace PyLean.CoreLibs.Misc

open PyLean PyLean.Accel

variable {α : Type} [Inhabited α]

/-- A comparison `a < b` as Python evaluates it. -/
abbrev LtP (α : Type) := α → α → Py Bool

/-- The `while (pos > startpos)` loop of `siftdown`, Modules/_heapqmodule.c:43-66. -/
def siftdownLoopP (lt : LtP α) (newitem : α) (startpos : Nat) :
    Nat → List α → Nat → List α × Option PyExc
  | 0, arr, _ => (arr, none)
  | fuel + 1, arr, pos =>
    if pos > startpos then
      let parentpos := (pos - 1) >>> 1
      let parent := at! arr parentpos
      match lt newitem parent with
      | .error e => (arr, some e)
      | .ok true =>
        let parent := at! arr parentpos
        let newitem' := at! arr pos
        siftdownLoopP lt newitem startpos fuel ((arr.set parentpos newitem').set pos parent) parentpos
      | .ok false => (arr, none)
    else (arr, none)

/-- `siftdown` for an in-range `pos`, Modules/_heapqmodule.c:25-68. -/
def siftdownP (lt : LtP α) (heap : List α) (startpos pos : Nat) : List α × Option PyExc :=
  siftdownLoopP lt (at! heap pos) startpos pos heap pos

/-- The `while (pos < limit)` loop of `siftup`, Modules/_heapqmodule.c:88-115. -/
def siftupLoopP (lt : LtP α) (endpos limit : Nat) :
    Nat → List α → Nat → List α × Nat × Option PyExc
  | 0, arr, pos => (arr, pos, none)
  | fuel + 1, arr, pos =>
    if pos < limit then
      let childpos := 2 * pos + 1
      let moveUp (childpos : Nat) :=
        let tmp1 := at! arr childpos
        let tmp2 := at! arr pos
        siftupLoopP lt endpos limit fuel ((arr.set childpos tmp2).set pos tmp1) childpos
      if childpos + 1 < endpos then
        match lt (at! arr childpos) (at! arr (childpos + 1)) with
        | .error e => (arr, pos, some e)
        | .ok true => moveUp childpos
        | .ok false => moveUp (childpos + 1)
      else moveUp childpos
    else (arr, pos, none)

/-- `siftup` for an in-range `pos`, Modules/_heapqmodule.c:70-118. -/
def siftupP (lt : LtP α) (heap : List α) (pos : Nat) : List α × Option PyExc :=
  let endpos := heap.length
  let startpos := pos
  let limit := endpos >>> 1
  match siftupLoopP lt endpos limit endpos heap pos with
  | (arr, _, some e) => (arr, some e)
  | (arr, pos, none) => siftdownP lt arr startpos pos

/-- `_heapq.heappush`, Modules/_heapqmodule.c:131-150. The item is appended before the sift, so
it stays in the list when a comparison raises. -/
def heappushP (lt : LtP α) (heap : List α) (item : α) : List α × Option PyExc :=
  let heap := heap ++ [item]
  siftdownP lt heap 0 (heap.length - 1)

/-- `heappop_internal`, Modules/_heapqmodule.c:152-183. When the sift raises, `returnitem` is
dropped and the last element has already moved to the root. -/
def heappopP (lt : LtP α) (heap : List α) : List α × Py α :=
  let n := heap.length
  if n = 0 then (heap, .error (.indexError "index out of range"))
  else
    let lastelt := at! heap (n - 1)
    let heap := heap.take (n - 1)
    let n := n - 1
    if n = 0 then (heap, .ok lastelt)
    else
      let returnitem := at! heap 0
      match siftupP lt (heap.set 0 lastelt) 0 with
      | (h, some e) => (h, .error e)
      | (h, none) => (h, .ok returnitem)

/-- The `for (i = (n >> 1) - 1 ; i >= 0 ; i--)` loop of `heapify_internal`,
Modules/_heapqmodule.c:376-378. -/
def heapifyLoopP (lt : LtP α) : List Nat → List α → List α × Option PyExc
  | [], h => (h, none)
  | i :: rest, h =>
    match siftupP lt h i with
    | (h, some e) => (h, some e)
    | (h, none) => heapifyLoopP lt rest h

/-- `heapify_internal`, Modules/_heapqmodule.c:364-380. Above 2500 elements C takes
`cache_friendly_heapify`, which does the same comparisons in another order: with a comparison that
raises, the partial state differs, and that path is not modelled here (the `sched` and `queue`
difftests stay below it). -/
def heapifyP (lt : LtP α) (x : List α) : List α × Option PyExc :=
  heapifyLoopP lt ((List.range (x.length / 2)).reverse) x

/-! ### A comparison that cannot raise -/

theorem siftdownLoopP_pure (lt : α → α → Bool) (newitem : α) (s : Nat) :
    ∀ fuel (arr : List α) pos,
      siftdownLoopP (fun a b => .ok (lt a b)) newitem s fuel arr pos =
        (cSiftdownLoop lt newitem s fuel arr pos, none) := by
  intro fuel
  induction fuel with
  | zero => intro arr pos; rfl
  | succ f ih =>
    intro arr pos
    simp only [siftdownLoopP, cSiftdownLoop]
    split
    · cases h : lt newitem (at! arr ((pos - 1) >>> 1)) with
      | true => simp only [h]; rw [ih]; rfl
      | false => simp [h]
    · rfl

theorem siftdownP_pure (lt : α → α → Bool) (heap : List α) (s pos : Nat) (h : pos < heap.length) :
    siftdownP (fun a b => .ok (lt a b)) heap s pos = (pySiftdown lt heap s pos, none) := by
  have := cSiftdown_eq lt heap s pos h
  simp only [cSiftdown, if_neg (Nat.not_le.2 h)] at this
  simp only [siftdownP, siftdownLoopP_pure]
  rw [Except.ok.injEq] at this
  rw [this]

theorem siftupLoopP_pure (lt : α → α → Bool) (endpos limit : Nat) :
    ∀ fuel (arr : List α) pos,
      siftupLoopP (fun a b => .ok (lt a b)) endpos limit fuel arr pos =
        ((cSiftupLoop lt endpos limit fuel arr pos).1,
          (cSiftupLoop lt endpos limit fuel arr pos).2, none) := by
  intro fuel
  induction fuel with
  | zero => intro arr pos; rfl
  | succ f ih =>
    intro arr pos
    simp only [siftupLoopP, cSiftupLoop]
    split
    · by_cases hc : 2 * pos + 1 + 1 < endpos
      · simp only [hc, if_true]
        cases h : lt (at! arr (2 * pos + 1)) (at! arr (2 * pos + 1 + 1)) with
        | true => simp only [h, if_true]; rw [ih]
        | false => simp only [h, if_false]; simp only [Bool.false_eq_true, if_false]; rw [ih]
      · simp only [hc, if_false]; rw [ih]
    · rfl

end PyLean.CoreLibs.Misc
