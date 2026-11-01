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

/-- `heappop` called `n` times on one list, `list(map(heapq.heappop, [h]*n))`. -/
def popsP (lt : LtP α) : Nat → List α → Py (List α)
  | 0, _ => .ok []
  | n + 1, h =>
    match heappopP lt h with
    | (_, .error x) => .error x
    | (h, .ok v) =>
      match popsP lt n h with
      | .error x => .error x
      | .ok rest => .ok (v :: rest)

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

theorem siftdownP_c (lt : α → α → Bool) (heap : List α) (s pos : Nat) :
    siftdownP (fun a b => .ok (lt a b)) heap s pos =
      (cSiftdownLoop lt (at! heap pos) s pos heap pos, none) := by
  simp only [siftdownP, siftdownLoopP_pure]

theorem siftupP_pure (lt : α → α → Bool) (heap : List α) (pos : Nat) (h : pos < heap.length) :
    siftupP (fun a b => .ok (lt a b)) heap pos = (pySiftup lt heap pos, none) := by
  have hc := cSiftup_eq lt heap pos h
  simp only [cSiftup, if_neg (Nat.not_le.2 h)] at hc
  simp only [siftupP, siftupLoopP_pure]
  rw [siftdownP_c]
  revert hc
  generalize cSiftupLoop lt heap.length (heap.length >>> 1) heap.length heap pos = r
  obtain ⟨arr, p⟩ := r
  simp only [cSiftdown]
  split
  · intro hc; cases hc
  · intro hc
    rw [Except.ok.injEq] at hc
    rw [hc]

theorem heappushP_pure (lt : α → α → Bool) (heap : List α) (item : α) :
    heappushP (fun a b => .ok (lt a b)) heap item = (pyHeappush lt heap item, none) := by
  simp only [heappushP, pyHeappush]
  exact siftdownP_pure lt _ 0 _ (by simp)

theorem heappopP_pure (lt : α → α → Bool) (heap : List α) (hne : heap ≠ []) :
    ∃ v h', heappopP (fun a b => .ok (lt a b)) heap = (h', .ok v) ∧
      pyHeappop lt heap = .ok (v, h') := by
  obtain ⟨d, last, hd⟩ : ∃ d last, heap = d ++ [last] :=
    ⟨heap.dropLast, heap.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
  subst hd
  have hat : at! (d ++ [last]) d.length = last := by simp [at!]
  have hgl : ∀ d : List α, (d ++ [last]).getLast? = some last := by intro d; simp
  have hdl : ∀ d : List α, (d ++ [last]).dropLast = d := by intro d; simp
  cases d with
  | nil =>
    refine ⟨last, [], ?_, rfl⟩
    simp [heappopP, at!]
  | cons d0 dt =>
    have hlen : (d0 :: dt ++ [last]).length ≠ 0 := by simp
    have hn : (d0 :: dt ++ [last]).length - 1 = dt.length + 1 := by simp
    have hat' : at! (d0 :: dt ++ [last]) (dt.length + 1) = last := by
      simpa using hat
    have htake : (d0 :: dt ++ [last]).take (dt.length + 1) = d0 :: dt := by
      simp
    refine ⟨d0, pySiftup lt (last :: dt) 0, ?_, ?_⟩
    · simp only [heappopP, hlen, if_false, hn, hat', htake]
      have : (dt.length + 1 = 0) = False := by simp
      simp only [this, if_false]
      have e : at! (d0 :: dt) 0 = d0 := rfl
      have e2 : (d0 :: dt).set 0 last = last :: dt := rfl
      rw [e, e2, siftupP_pure lt (last :: dt) 0 (by simp)]
    · simp only [pyHeappop, hgl (d0 :: dt), hdl (d0 :: dt)]
      simp [at!]

theorem isHeap_nil (lt : α → α → Bool) : IsHeap lt ([] : List α) := by
  intro c hc
  simp at hc

/-- Popping a heap until it is empty gives its elements in order: the output of `popsP` is a
permutation of the heap and no element is `<` an earlier one. -/
theorem popsP_sorted {lt : α → α → Bool} (hlt : StrictWeak lt) :
    ∀ (n : Nat) (heap : List α), heap.length = n → IsHeap lt heap →
      ∃ l, popsP (fun a b => .ok (lt a b)) n heap = .ok l ∧ l.Perm heap ∧
        l.Pairwise (fun a b => lt b a = false) := by
  intro n
  induction n with
  | zero =>
    intro heap hl _
    have : heap = [] := List.length_eq_zero_iff.1 hl
    subst this
    exact ⟨[], rfl, List.Perm.refl _, List.Pairwise.nil⟩
  | succ n ih =>
    intro heap hl hh
    have hne : heap ≠ [] := by
      intro e
      subst e
      simp at hl
    obtain ⟨v, h', hp, hq⟩ := heappopP_pure lt heap hne
    obtain ⟨v2, h2, hq2, hh2, hperm, hmin⟩ := pyHeappop_correct hlt heap hh hne
    rw [hq] at hq2
    cases hq2
    have hlen : h'.length = n := by
      have := hperm.length_eq
      simp at this
      omega
    obtain ⟨l, hl1, hl2, hl3⟩ := ih h' hlen hh2
    refine ⟨v :: l, ?_, ?_, ?_⟩
    · simp only [popsP, hp, hl1]
    · exact (hl2.cons v).trans hperm
    · refine List.Pairwise.cons ?_ hl3
      intro b hb
      exact hmin b (hperm.subset (List.mem_cons_of_mem _ (hl2.subset hb)))

end PyLean.CoreLibs.Misc
