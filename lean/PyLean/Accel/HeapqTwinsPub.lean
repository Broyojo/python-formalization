import PyLean.Accel.HeapqTwins

/-!
C/Python agreement of the public heap functions with fallible comparisons: proven for
comparisons that neither read nor write the heap list (up to the empty-heap `IndexError`
message, and for `heapify` up to 2500 items), refuted for re-entrant comparisons, for the
list left behind by a raising comparison, and for `heapify` above 2500 items.
-/

namespace PyLean.Accel.Heapq

open PyLean

variable {σ α : Type} [Inhabited α]

/-- Twin agreement with the one tolerated difference: on an empty heap both raise
`IndexError`, with different messages (`accel-heapq-empty-error-message`). -/
def Agree (h0 : List α) {β : Type} : Except CErr β × HW σ α → Except PyExc β × HW σ α → Prop
  | (.ok a, w1), (.ok b, w2) => a = b ∧ w1 = w2
  | (.error (.py e1), w1), (.error e2, w2) =>
    (e1 = e2 ∨ (h0 = [] ∧ e1.className = "IndexError" ∧ e2.className = "IndexError")) ∧
      w1.st = w2.st
  | _, _ => False

theorem Rel.agree {β : Type} {h0 : List α} {r : Except CErr β × HW σ α}
    {p : Except PyExc β × HW σ α} (h : Rel r p) : Agree h0 r p := by
  rcases r with ⟨r, w1⟩
  rcases p with ⟨p, w2⟩
  cases r with
  | ok a => cases p with
    | ok b => exact h
    | error _ => exact h.elim
  | error e => cases e with
    | crash _ => cases p <;> exact h.elim
    | py e1 => cases p with
      | ok _ => exact h.elim
      | error e2 => exact ⟨Or.inl h.1, h.2⟩

theorem listPop_run_cons (y : α) (ys : List α) (st : σ) :
    ((listSeq : Seq (HW σ α) α).pop).run ⟨st, y :: ys⟩ =
      (.ok (at! (y :: ys) ys.length), ⟨st, (y :: ys).take ys.length⟩) := by
  have hl : (y :: ys).getLast? = some (at! (y :: ys) ys.length) := by
    rw [List.getLast?_eq_getElem?]
    simp [at!, List.getD_eq_getElem?_getD]
  have hd : (y :: ys).dropLast = (y :: ys).take ys.length := by
    rw [List.dropLast_eq_take]; simp
  show (match (y :: ys).getLast? with
    | some x => (Except.ok x, ({ st := st, heap := (y :: ys).dropLast } : HW σ α))
    | none => (Except.error (PyExc.indexError "pop from empty list"), ({ st := st, heap := y :: ys } : HW σ α)))
    = _
  rw [hl, hd]

/-! ### The public functions -/

theorem push_sim (mx : Bool) (f : α → α → σ → Except PyExc Bool × σ) (tp : String) (item : α)
    (w : HW σ α) :
    Rel ((cHeappush mx (ofSt f) ⟨true, tp⟩ item).run w)
      ((pyHeappush listSeq (ofSt f) mx item).run w) := by
  simp only [cHeappush, cChecked, ↓reduceIte, pyHeappush]
  rw [Eff.run_bind_ok (cAppend_run _ _), Eff.run_bind_ok (listAppend_run _ _),
    Eff.run_bind_ok (cSize_run _), Eff.run_bind_ok (listLen_run _)]
  have e : (((({ w with heap := w.heap ++ [item] } : HW σ α).heap.length : Nat) : Int) - 1) =
      ((((({ w with heap := w.heap ++ [item] } : HW σ α)).heap.length - 1 : Nat) : Int)) := by
    simp
  rw [e]
  exact siftdown_sim mx f 0 _ _ (by simp)

theorem pop_agree (mx : Bool) (f : α → α → σ → Except PyExc Bool × σ) (tp : String) (w : HW σ α) :
    Agree w.heap ((cHeappop mx (ofSt f) ⟨true, tp⟩).run w)
      ((pyHeappop listSeq (ofSt f) mx).run w) := by
  rcases w with ⟨st, h⟩
  cases h with
  | nil =>
    refine ⟨Or.inr ⟨rfl, rfl, rfl⟩, rfl⟩
  | cons y ys =>
    apply Rel.agree
    simp only [cHeappop, cChecked, ↓reduceIte, cHeappopInternal, pyHeappop]
    rw [Eff.run_bind_ok (cSize_run _), if_neg (by simp),
      Eff.run_bind_ok (cItem_run (show (y :: ys).length - 1 < (y :: ys).length by simp)),
      Eff.run_bind_ok (cDelTail_run _ _), Eff.run_bind_ok (listPop_run_cons y ys st),
      Eff.run_bind_ok (listTruth_run _)]
    simp only [List.length_cons, Nat.add_sub_cancel]
    by_cases h0 : ys.length = 0
    · have : ys = [] := List.eq_nil_of_length_eq_zero h0
      subst this
      exact ⟨rfl, rfl⟩
    · have hne : ((y :: ys).take ys.length).isEmpty = false := by
        cases ys with
        | nil => simp at h0
        | cons z zs => simp
      rw [if_neg h0, hne]
      simp only [Bool.not_false, ↓reduceIte]
      rw [Eff.run_bind_ok (cItem_run (show 0 < ((y :: ys).take ys.length).length by simp; omega)),
        Eff.run_bind_ok (listGet_run 0 0 (by simp) (show 0 < ((y :: ys).take ys.length).length by
          simp; omega)),
        Eff.run_bind_ok (cStore_run (show 0 < ((y :: ys).take ys.length).length by simp; omega)),
        Eff.run_bind_ok (listSet_run 0 0 (by simp) _ (show 0 < ((y :: ys).take ys.length).length by
          simp; omega))]
      exact Rel.bind (siftup_sim mx f 0 _ (by simp; omega)) (fun _ w => Rel.pure _ w)

theorem replace_agree (mx : Bool) (f : α → α → σ → Except PyExc Bool × σ) (tp : String) (item : α)
    (w : HW σ α) :
    Agree w.heap ((cHeapreplace mx (ofSt f) ⟨true, tp⟩ item).run w)
      ((pyHeapreplace listSeq (ofSt f) mx item).run w) := by
  rcases w with ⟨st, h⟩
  cases h with
  | nil => exact ⟨Or.inr ⟨rfl, rfl, rfl⟩, rfl⟩
  | cons y ys =>
    apply Rel.agree
    simp only [cHeapreplace, cChecked, ↓reduceIte, cHeapreplaceInternal, pyHeapreplace]
    rw [Eff.run_bind_ok (cSize_run _), if_neg (by simp),
      Eff.run_bind_ok (cItem_run (show 0 < (y :: ys).length by simp)),
      Eff.run_bind_ok (listGet_run 0 0 (by simp) (show 0 < (y :: ys).length by simp)),
      Eff.run_bind_ok (cStore_run (show 0 < (y :: ys).length by simp)),
      Eff.run_bind_ok (listSet_run 0 0 (by simp) _ (show 0 < (y :: ys).length by simp))]
    exact Rel.bind (siftup_sim mx f 0 _ (by simp)) (fun _ w => Rel.pure _ w)

theorem pushpop_sim (mx : Bool) (f : α → α → σ → Except PyExc Bool × σ) (tp : String) (item : α)
    (w : HW σ α) :
    Rel ((cHeappushpop mx (ofSt f) ⟨true, tp⟩ item).run w)
      ((pyHeappushpop listSeq (ofSt f) mx item).run w) := by
  rcases w with ⟨st, h⟩
  simp only [cHeappushpop, cChecked, ↓reduceIte, cHeappushpopImpl, pyHeappushpop, pyTopLt,
    Eff.bind_assoc, Eff.ite_bind]
  rw [Eff.run_bind_ok (cSize_run _), Eff.run_bind_ok (listTruth_run _)]
  cases h with
  | nil =>
    simp only [List.length_nil, ↓reduceIte, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true,
      Eff.run_pure, Eff.pure_bind]
    exact ⟨rfl, rfl⟩
  | cons y ys =>
    simp only [List.length_cons, Nat.add_one_ne_zero, ↓reduceIte, List.isEmpty_cons, Bool.not_false]
    rw [Eff.run_bind_ok (cItem_run (show 0 < (y :: ys).length by simp)),
      Eff.run_bind_ok (listGet_run 0 0 (by simp) (show 0 < (y :: ys).length by simp)),
      cLtOrd_ofSt, pyLtOrd_ofSt]
    rcases cmp_ofSt f (if mx then item else at! (y :: ys) 0) (if mx then at! (y :: ys) 0 else item)
        st (y :: ys) (y :: ys) with ⟨c, s', -, h1, h2⟩ | ⟨e, s', h1, h2⟩
    · rw [Eff.run_bind_ok h1, Eff.run_bind_ok h2]
      cases c
      · simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true, Eff.run_pure]
        exact ⟨rfl, rfl⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [Eff.run_bind_ok (cSize_run _), if_neg (by simp),
          Eff.run_bind_ok (cItem_run (show 0 < (y :: ys).length by simp)),
          Eff.run_bind_ok (listGet_run 0 0 (by simp) (show 0 < (y :: ys).length by simp)),
          Eff.run_bind_ok (cStore_run (show 0 < (y :: ys).length by simp)),
          Eff.run_bind_ok (listSet_run 0 0 (by simp) _ (show 0 < (y :: ys).length by simp))]
        exact Rel.bind (siftup_sim mx f 0 _ (by simp)) (fun _ w => Rel.pure _ w)
    · rw [Eff.run_bind_err h1, Eff.run_bind_err h2]
      exact ⟨rfl, rfl⟩

theorem effFor_sim (mx : Bool) (f : α → α → σ → Except PyExc Bool × σ) (n : Nat) :
    ∀ (is : List Nat), (∀ i ∈ is, i < n) → ∀ w : HW σ α, w.heap.length = n →
      Rel ((effFor (fun i => cSiftup mx (ofSt f) i) is).run w)
        ((effFor (fun i => pySiftup listSeq (ofSt f) mx (i : Int)) is).run w) := by
  intro is
  induction is with
  | nil => intro _ w _; exact ⟨rfl, rfl⟩
  | cons i is ih =>
    intro hi w hw
    simp only [effFor]
    have hin : i < w.heap.length := by rw [hw]; exact hi i (by simp)
    have hs := siftup_sim mx f i w hin
    have ho := cSiftup_out mx (ofSt f) i w hin
    rcases hc : (cSiftup mx (ofSt f) i).run w with ⟨rc, wc⟩
    rcases hp : (pySiftup listSeq (ofSt f) mx (i : Int)).run w with ⟨rp, wp⟩
    rw [hc, hp] at hs
    rw [hc] at ho
    cases rc with
    | ok _ =>
      cases rp with
      | ok _ =>
        obtain ⟨-, rfl⟩ := hs
        rw [Eff.run_bind_ok hc, Eff.run_bind_ok hp]
        exact ih (fun j hj => hi j (by simp [hj])) wc (by rw [ho, hw])
      | error _ => exact hs.elim
    | error e1 =>
      cases e1 with
      | crash _ => cases rp <;> exact hs.elim
      | py e1 =>
        cases rp with
        | ok _ => exact hs.elim
        | error e2 => rw [Eff.run_bind_err hc, Eff.run_bind_err hp]; exact hs

theorem heapify_sim (mx : Bool) (f : α → α → σ → Except PyExc Bool × σ) (tp : String) (w : HW σ α)
    (hn : w.heap.length ≤ 2500) :
    Rel ((cHeapify mx (ofSt f) ⟨true, tp⟩).run w) ((pyHeapify listSeq (ofSt f) mx).run w) := by
  simp only [cHeapify, cChecked, ↓reduceIte, cHeapifyInternal, pyHeapify]
  rw [Eff.run_bind_ok (cSize_run w), Eff.run_bind_ok (listLen_run w), if_neg (by omega),
    Accel.downFrom_zero, shr1']
  exact effFor_sim mx f _ _ (fun i hi => by simp at hi; omega) w rfl

/-! ### Registry properties -/

/-- **C and Python agree for comparisons that do not touch the list.** For every element type,
every comparison that neither reads nor writes the heap list (it may raise in `__lt__` or in
the truth test of its result, keep any state of its own, and answer depending on that state),
both the min-heap and the `*_max` variants, and every list (an exact `list` on the Python
side), the C and Python `heappush`, `heappop`, `heapreplace`, `heappushpop` and (up to 2500
items) `heapify`:

* make the same comparisons on the same operands in the same order (so leave the comparison's
  state the same);
* return the same item and leave the same list when they succeed;
* raise the same exception, message included, except that on an empty heap `heappop` and
  `heapreplace` raise `IndexError` with different messages in C and Python.

Source: invariant (C accelerator vs pure-Python twin, `Modules/_heapqmodule.c:1` "Drop in
replacement for heapq.py"). The lists left behind by a raising comparison differ
(`HeapTwinsSameListOnRaise`), re-entrant comparisons make the twins diverge
(`HeapTwinsAgreeReentrant`), and so does `heapify` above 2500 items (`HeapifyTwinsAgreeFallible`). -/
def HeapTwinsAgree : Prop :=
  ∀ (σ α : Type) [Inhabited α] (f : α → α → σ → Except PyExc Bool × σ) (mx : Bool) (w : HW σ α)
    (item : α) (tp : String),
    Rel ((cHeappush mx (ofSt f) ⟨true, tp⟩ item).run w)
      ((pyHeappush listSeq (ofSt f) mx item).run w) ∧
    Agree w.heap ((cHeappop mx (ofSt f) ⟨true, tp⟩).run w)
      ((pyHeappop listSeq (ofSt f) mx).run w) ∧
    Agree w.heap ((cHeapreplace mx (ofSt f) ⟨true, tp⟩ item).run w)
      ((pyHeapreplace listSeq (ofSt f) mx item).run w) ∧
    Rel ((cHeappushpop mx (ofSt f) ⟨true, tp⟩ item).run w)
      ((pyHeappushpop listSeq (ofSt f) mx item).run w) ∧
    (w.heap.length ≤ 2500 →
      Rel ((cHeapify mx (ofSt f) ⟨true, tp⟩).run w) ((pyHeapify listSeq (ofSt f) mx).run w))

theorem heapTwinsAgree_proven : HeapTwinsAgree := by
  intro σ α _ f mx w item tp
  exact ⟨push_sim mx f tp item w, pop_agree mx f tp w, replace_agree mx f tp item w,
    pushpop_sim mx f tp item w, heapify_sim mx f tp w⟩

/-- Including the message: refuted by the empty heap. -/
def HeapTwinsAgreeExact : Prop :=
  ∀ (σ α : Type) [Inhabited α] (f : α → α → σ → Except PyExc Bool × σ) (mx : Bool) (w : HW σ α)
    (item : α) (tp : String),
    Rel ((cHeappop mx (ofSt f) ⟨true, tp⟩).run w) ((pyHeappop listSeq (ofSt f) mx).run w) ∧
    Rel ((cHeapreplace mx (ofSt f) ⟨true, tp⟩ item).run w)
      ((pyHeapreplace listSeq (ofSt f) mx item).run w)

/-- `heappop([])`: C `IndexError('index out of range')`, Python `IndexError('pop from empty
list')`. -/
theorem heapTwinsAgreeExact_refuted : ¬ HeapTwinsAgreeExact := by
  intro h
  have := (h Unit Int (fun a b s => (.ok (decide (a < b)), s)) false ⟨(), []⟩ 0 "list").1
  exact absurd this.1 (by decide)

/-- The broad statement: the twins agree (as in `HeapTwinsAgree`, `heapify` at every length)
for every comparison, including ones that read or mutate the heap list. -/
def HeapTwinsAgreeReentrant : Prop :=
  ∀ (σ α : Type) [Inhabited α] (lt : Cmp σ α) (mx : Bool) (w : HW σ α) (item : α) (tp : String),
    Agree w.heap ((cHeappush mx lt ⟨true, tp⟩ item).run w) ((pyHeappush listSeq lt mx item).run w) ∧
    Agree w.heap ((cHeappop mx lt ⟨true, tp⟩).run w) ((pyHeappop listSeq lt mx).run w) ∧
    Agree w.heap ((cHeapreplace mx lt ⟨true, tp⟩ item).run w)
      ((pyHeapreplace listSeq lt mx item).run w) ∧
    Agree w.heap ((cHeappushpop mx lt ⟨true, tp⟩ item).run w)
      ((pyHeappushpop listSeq lt mx item).run w) ∧
    Agree w.heap ((cHeapify mx lt ⟨true, tp⟩).run w) ((pyHeapify listSeq lt mx).run w)

/-- `x < y` on ints, which appends `99` to the heap the first time it runs (`st` counts the
calls). -/
def appendOnce : Cmp Nat Int := fun a b =>
  ⟨fun w => (.ok (decide (a < b)),
    if w.st = 0 then { st := 1, heap := w.heap ++ [99] } else { w with st := w.st + 1 })⟩

/-- `heappush([1, 2, 3], 0)` with a comparison that appends to the heap on its first call:
C raises `RuntimeError('list changed size during iteration')`
(`_heapqmodule.c:53-57`); Python carries on and returns `None`, leaving
`[0, 1, 3, 2, 99]`. -/
theorem heapTwinsAgreeReentrant_refuted : ¬ HeapTwinsAgreeReentrant := by
  intro h
  have := (h Nat Int appendOnce false ⟨0, [1, 2, 3]⟩ 0 "list").1
  have hc : (cHeappush false appendOnce ⟨true, "list"⟩ (0 : Int)).run ⟨0, [1, 2, 3]⟩ =
      (.error (.py sizeChanged), ⟨1, [1, 2, 3, 0, 99]⟩) := by rfl
  have hp : (pyHeappush listSeq appendOnce false (0 : Int)).run ⟨0, [1, 2, 3]⟩ =
      (.ok (), ⟨2, [0, 1, 3, 2, 99]⟩) := by rfl
  rw [hc, hp] at this
  exact this

/-- The lists the twins leave behind also agree when a comparison raises (comparisons that do
not touch the list, as in `HeapTwinsAgree`). -/
def HeapTwinsSameListOnRaise : Prop :=
  ∀ (σ α : Type) [Inhabited α] (f : α → α → σ → Except PyExc Bool × σ) (mx : Bool) (w : HW σ α)
    (item : α) (tp : String),
    ((cHeappush mx (ofSt f) ⟨true, tp⟩ item).run w).2 = ((pyHeappush listSeq (ofSt f) mx item).run w).2 ∧
    ((cHeappop mx (ofSt f) ⟨true, tp⟩).run w).2 = ((pyHeappop listSeq (ofSt f) mx).run w).2 ∧
    ((cHeapreplace mx (ofSt f) ⟨true, tp⟩ item).run w).2 =
      ((pyHeapreplace listSeq (ofSt f) mx item).run w).2 ∧
    ((cHeappushpop mx (ofSt f) ⟨true, tp⟩ item).run w).2 =
      ((pyHeappushpop listSeq (ofSt f) mx item).run w).2 ∧
    ((cHeapify mx (ofSt f) ⟨true, tp⟩).run w).2 = ((pyHeapify listSeq (ofSt f) mx).run w).2

/-- `x < y` on ints that raises `ValueError('boom')` on its second call. -/
def raiseSecond : Int → Int → Nat → Except PyExc Bool × Nat := fun a b s =>
  if s = 1 then (.error (.named "ValueError" "boom"), s + 1) else (.ok (decide (a < b)), s + 1)

/-- `heappop([0, 1, 2, 3, 4, 5, 6])` with a comparison that raises on its second call: C leaves
`[1, 6, 2, 3, 4, 5]` (the old root is gone, as it was being returned, and every other item is
still there), Python `[1, 1, 2, 3, 4, 5]` (the hole technique has copied `1` up and `6`, held in
a local, is lost). -/
theorem heapTwinsSameListOnRaise_refuted : ¬ HeapTwinsSameListOnRaise := by
  intro h
  have := (h Nat Int raiseSecond false ⟨0, [0, 1, 2, 3, 4, 5, 6]⟩ 0 "list").2.1
  have hc : ((cHeappop false (ofSt raiseSecond) ⟨true, "list"⟩).run ⟨0, [0, 1, 2, 3, 4, 5, 6]⟩).2.heap =
      [1, 6, 2, 3, 4, 5] := by decide
  have hp : ((pyHeappop listSeq (ofSt raiseSecond) false).run ⟨0, [0, 1, 2, 3, 4, 5, 6]⟩).2.heap =
      [1, 1, 2, 3, 4, 5] := by decide
  rw [this] at hc
  rw [hc] at hp
  exact absurd hp (by decide)

/-! ### Beyond exact lists -/

/-- The broad statement behind `HeapTwinsAgree` without its exact-list scope: for every first
argument, the C functions (which see `PyList_Check` and the raw list storage) and the Python
functions (which see the object's own `append`, `__getitem__`, `__setitem__`, `__len__`, `pop`
and truth, `S`) agree. A list subclass is `⟨true, _⟩` on the C side with any `S` on the Python
side; a non-list is `⟨false, _⟩`. -/
def HeapTwinsAgreeAnySeq : Prop :=
  ∀ (σ α : Type) [Inhabited α] (f : α → α → σ → Except PyExc Bool × σ) (mx : Bool) (w : HW σ α)
    (item : α) (arg : CArg) (S : Seq (HW σ α) α),
    Agree w.heap ((cHeappush mx (ofSt f) arg item).run w) ((pyHeappush S (ofSt f) mx item).run w) ∧
    Agree w.heap ((cHeapify mx (ofSt f) arg).run w) ((pyHeapify S (ofSt f) mx).run w)

/-- A list subclass whose `append` override records each call in `st`, then appends. -/
def loggedListSeq : Seq (HW Nat Int) Int :=
  { (listSeq : Seq (HW Nat Int) Int) with
    append := fun v => ⟨fun w => (.ok (), { st := w.st + 1, heap := w.heap ++ [v] })⟩ }

/-- `heappush(LoggedList([1, 2, 3]), 0)` for a list subclass overriding `append`: both twins
leave `[0, 1, 3, 2]`, but only Python calls the override (C appends to the raw storage,
`_heapqmodule.c:142`). (The non-list case: `heapify(())` raises `TypeError` in C and returns
`None` in Python; see `bugs/accel-heapq-list-subclass-overrides.yaml`.) -/
theorem heapTwinsAgreeAnySeq_refuted : ¬ HeapTwinsAgreeAnySeq := by
  intro h
  have := (h Nat Int (fun a b s => (.ok (decide (a < b)), s)) false ⟨0, [1, 2, 3]⟩ 0
    ⟨true, "LoggedList"⟩ loggedListSeq).1
  have hc : (cHeappush false (ofSt (fun a b s => (.ok (decide (a < b)), s))) ⟨true, "LoggedList"⟩
      (0 : Int)).run ⟨(0 : Nat), [1, 2, 3]⟩ = (.ok (), ⟨0, [0, 1, 3, 2]⟩) := by rfl
  have hp : (pyHeappush loggedListSeq (ofSt (fun a b s => (.ok (decide (a < b)), s))) false
      (0 : Int)).run ⟨(0 : Nat), [1, 2, 3]⟩ = (.ok (), ⟨1, [0, 1, 3, 2]⟩) := by rfl
  rw [hc, hp] at this
  have := congrArg HW.st this.2
  exact absurd this (by decide)

end PyLean.Accel.Heapq
