import PyLean.BytesObj.Seq.ListModel

/-!
What Python can see of tearing a container down: items are released and visited last
to first (finalizers and `gc.get_referents` show the order), and which iterators
let go of their container once exhausted.
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α : Type}

/-- `i = Py_SIZE(op); while (--i >= 0) f(op->ob_item[i])`: `tuple_dealloc`,
tupleobject.c:229-232, `list_dealloc`, listobject.c:559-562, `list_clear_impl`,
:852-858. `tuple_traverse`, tupleobject.c:653-655, and `list_traverse`, listobject.c:3390-3391,
are the same walk with `Py_VISIT`. `i` slots are left to visit. -/
def backLoop (items : List α) : Nat → List (Option α)
  | 0 => []
  | i + 1 => items[i]? :: backLoop items i

/-- `tuple_dealloc(self)`, tupleobject.c:208-237: the empty singleton returns at once. -/
def tupleDeallocOrder (items : List α) : List (Option α) :=
  if items.length = 0 then [] else backLoop items items.length

/-- `list_dealloc(self)`, listobject.c:548-572. -/
def listDeallocOrder (o : LObj α) : List (Option α) :=
  if o.hasItems then backLoop o.items o.items.length else []

/-- `tuple_traverse(self, visit, arg)`, tupleobject.c:649-657. -/
def tupleTraverse (items : List α) : List (Option α) := backLoop items items.length

/-- `list_traverse(self, visit, arg)`, listobject.c:3384-3393. -/
def listTraverse (items : List α) : List (Option α) := backLoop items items.length

/-- `tupleiter_traverse`, tupleobject.c:1036-1042: `Py_VISIT(it->it_seq)`. -/
def tupleIterTraverse (it : TupleIter α) : List (List α) := it.seq.toList

/-- `listiter_traverse`, listobject.c:4011-4016, and `listreviter_traverse`, :4165-4170:
`Py_VISIT(it->it_seq)`, so `gc.get_referents` shows whether the iterator holds its list. -/
def listIterTraverse (it : ListIter) (l : List α) : List (List α) := if it.alive then [l] else []

/-- `n` calls of `next` on a list that does not change. -/
def iterRun (nxt : ListIter → List α → Py (Option α × ListIter)) (l : List α) :
    Nat → ListIter → Py ListIter
  | 0, it => .ok it
  | n + 1, it =>
    match nxt it l with
    | .ok (_, it') => iterRun nxt l n it'
    | .error e => .error e

theorem backLoop_take (items : List α) (n : Nat) (h : n ≤ items.length) :
    backLoop items n = (items.take n).reverse.map some := by
  induction n with
  | zero => simp [backLoop]
  | succ n ih =>
    have hlt : n < items.length := by omega
    have hrev : (items.take (n + 1)).reverse = items[n] :: (items.take n).reverse := by
      rw [List.take_succ_eq_append_getElem hlt, List.reverse_append]
      rfl
    rw [backLoop, ih (by omega), List.getElem?_eq_getElem hlt, hrev]
    rfl

/-- Containers release and visit their items last to first, for every element type:
finalizers run in that order when a tuple or list dies or a list is cleared, and
`gc.get_referents` lists the items in that order. The empty tuple singleton does
nothing. A live iterator refers to exactly its sequence. -/
def ReleaseOrder : Prop :=
  ∀ (α : Type) (l : List α) (o : LObj α) (it : TupleIter α),
    tupleTraverse l = l.reverse.map some ∧
    listTraverse l = l.reverse.map some ∧
    tupleDeallocOrder l = l.reverse.map some ∧
    (o.hasItems = true → listDeallocOrder o = o.items.reverse.map some) ∧
    (o.hasItems = false → listDeallocOrder o = []) ∧
    (it.seq = none → tupleIterTraverse it = []) ∧
    (∀ s, it.seq = some s → tupleIterTraverse it = [s]) ∧
    (∀ (r : ListIter), r.alive = true → listIterTraverse r l = [l]) ∧
    (∀ (r : ListIter), r.alive = false → listIterTraverse r l = [])

theorem releaseOrder_proven : ReleaseOrder := by
  intro α l o it
  have hall : ∀ (x : List α), backLoop x x.length = x.reverse.map some := by
    intro x
    have := backLoop_take x x.length (by omega)
    simpa using this
  refine ⟨hall l, hall l, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold tupleDeallocOrder
    by_cases h : l.length = 0
    · have : l = [] := List.length_eq_zero_iff.mp h
      simp [this]
    · rw [if_neg h]
      exact hall l
  · intro h
    simp only [listDeallocOrder, h, if_true]
    exact hall o.items
  · intro h
    simp [listDeallocOrder, h]
  · intro h
    simp [tupleIterTraverse, h]
  · intro s h
    simp [tupleIterTraverse, h]
  · intro r h
    simp [listIterTraverse, h]
  · intro r h
    simp [listIterTraverse, h]

/-- What holds of a forward iterator after any number of `next` calls. -/
def ForwardReach (it : ListIter) : Prop := (it.alive = true ∧ 0 ≤ it.index) ∨ it.alive = false

theorem forward_step (it it' : ListIter) (l : List α) (v : Option α) (hr : ForwardReach it)
    (h : listIterNext it l = .ok (v, it')) : ForwardReach it' := by
  unfold listIterNext at h
  by_cases h1 : it.index < 0
  · rw [if_pos h1] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact hr
  · rw [if_neg h1] at h
    by_cases h2 : it.alive = true
    · simp only [h2, Bool.not_true, Bool.false_eq_true, if_false] at h
      cases hg : listGetItemRef l it.index with
      | none =>
        rw [hg] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        exact Or.inr rfl
      | some x =>
        rw [hg] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        exact Or.inl ⟨rfl, by simp only; omega⟩
    · simp [h2] at h

theorem forward_run (l : List α) (n : Nat) (it it' : ListIter) (hr : ForwardReach it)
    (h : iterRun listIterNext l n it = .ok it') : ForwardReach it' := by
  induction n generalizing it with
  | zero =>
    simp only [iterRun, Except.ok.injEq] at h
    rw [← h]
    exact hr
  | succ n ih =>
    simp only [iterRun] at h
    cases hs : listIterNext it l with
    | error e => rw [hs] at h; simp at h
    | ok p =>
      obtain ⟨v, it2⟩ := p
      rw [hs] at h
      exact ih it2 (forward_step it it2 l v hr hs) h

/-- `iter(l)` lets go of the list once it is exhausted, for every list: after any
number of `next` calls, the call that stops has cleared `it_seq`. -/
def ListIterReleases : Prop :=
  ∀ (α : Type) (l : List α) (n : Nat) (it it' : ListIter),
    iterRun listIterNext l n listIter = .ok it → listIterNext it l = .ok (none, it') →
      it'.alive = false

theorem listIterReleases_proven : ListIterReleases := by
  intro α l n it it' h1 h2
  have hr : ForwardReach it := forward_run l n listIter it (Or.inl ⟨rfl, by simp [listIter]⟩) h1
  unfold listIterNext at h2
  by_cases h3 : it.index < 0
  · rw [if_pos h3] at h2
    simp only [Except.ok.injEq, Prod.mk.injEq] at h2
    rw [← h2.2]
    rcases hr with ⟨_, h⟩ | h
    · omega
    · exact h
  · rw [if_neg h3] at h2
    by_cases h4 : it.alive = true
    · simp only [h4, Bool.not_true, Bool.false_eq_true, if_false] at h2
      cases hg : listGetItemRef l it.index with
      | none =>
        rw [hg] at h2
        simp only [Except.ok.injEq, Prod.mk.injEq] at h2
        rw [← h2.2]
      | some x =>
        rw [hg] at h2
        simp at h2
    · simp [h4] at h2

/-- `reversed(l)` lets go of the list once it is exhausted, as `iter(l)` does and as
the comment on `it_seq` says ("Set to NULL when iterator is exhausted",
listobject.c:4084). It does not: the last item leaves `it_index` at `-1`, and
`listreviter_next` then returns at its early `index < 0` test (:4178), so the code that
clears `it_seq` (:4189-4193) only runs when the list has shrunk under the iterator. -/
def ListRevIterReleases : Prop :=
  ∀ (α : Type) (l : List α) (n : Nat) (it it' : ListIter),
    iterRun listRevIterNext l n (listReversed l) = .ok it → listRevIterNext it l = .ok (none, it') →
      it'.alive = false

theorem listRevIterReleases_refuted : ¬ ListRevIterReleases := by
  intro h
  have := h Unit [()] 1 ⟨-1, true⟩ ⟨-1, true⟩ (by decide) (by decide)
  simp at this

/-- What `reversed(l)` does do: the iterator stops for good, and it clears `it_seq`
exactly when it runs into the end of a list that has shrunk. -/
def ListRevIterStops : Prop :=
  ∀ (α : Type) (l : List α) (it : ListIter), it.alive = true → 0 ≤ it.index →
    (l.length : Int) ≤ ssizeMax → it.index ≤ ssizeMax → (l.length : Int) ≤ it.index →
      listRevIterNext it l = .ok (none, ⟨-1, false⟩)

theorem listRevIterStops_proven : ListRevIterStops := by
  intro α l it h1 h2 h3 h4 h5
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h2
  have hnot : listGetItemRef l it.index = none := by
    unfold listGetItemRef
    have hv : validIndex it.index l.length = false := by
      unfold validIndex ssizeMax at *
      have e1 : (2 : Int) ^ 64 = 18446744073709551616 := by decide
      have e2 : (2 : Int) ^ 63 = 9223372036854775808 := by decide
      rw [e1]
      rw [e2] at h3 h4
      have a : it.index % 18446744073709551616 = it.index := Int.emod_eq_of_lt h2 (by omega)
      have b : (l.length : Int) % 18446744073709551616 = l.length := Int.emod_eq_of_lt (by omega) (by omega)
      rw [a, b]
      simp only [decide_eq_false_iff_not]
      omega
    simp [hv]
  unfold listRevIterNext
  rw [if_neg (by omega)]
  simp only [h1, Bool.not_true, Bool.false_eq_true, if_false, hnot]

end PyLean.BytesObj.Seq
