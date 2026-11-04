import PyLean.BytesObj.Seq.SearchProps

/-!
Iterators of `tuple` and `list`: what they yield, that an exhausted iterator stays
exhausted whatever happens to the list, that `it_seq` is never dereferenced after
it was cleared, and that `__reduce__` followed by `__setstate__` rebuilds the same
remaining sequence.
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α : Type}

/-! ## Tuple iterators -/

/-- What is left to yield. -/
def TupleIter.rest (it : TupleIter α) : List α :=
  match it.seq with
  | some s => s.drop it.index.toNat
  | none => []

/-- `n` calls of `next`, dropping the iterator. -/
def tupleIterTake : Nat → TupleIter α → List (Option α)
  | 0, _ => []
  | n + 1, it => (tupleIterNext it).1 :: tupleIterTake n (tupleIterNext it).2

theorem tupleIterTake_drop (s : List α) (i n : Nat) (hi : i ≤ s.length) (hn : s.length ≤ i + n) :
    tupleIterTake n { index := (i : Int), seq := some s } =
      (s.drop i).map some ++ List.replicate (n - (s.length - i)) none := by
  induction n generalizing i with
  | zero =>
    have : s.drop i = [] := List.drop_eq_nil_of_le hn
    simp [tupleIterTake, this]
  | succ n ih =>
    by_cases h : i < s.length
    · have hstep : tupleIterNext ({ index := (i : Int), seq := some s } : TupleIter α) =
          (s[i]?, { index := ((i + 1 : Nat) : Int), seq := some s }) := by
        have h' : (i : Int) < (s.length : Int) := by omega
        have e : (i : Int) + 1 = ((i + 1 : Nat) : Int) := by omega
        simp only [tupleIterNext, if_pos h', slot_nat, e]
      simp only [tupleIterTake, hstep]
      rw [ih (i + 1) (by omega) (by omega), drop_cons_of_lt s i h, List.getElem?_eq_getElem h]
      simp only [List.map_cons, List.cons_append, List.cons.injEq, true_and]
      congr 2
      omega
    · have hi' : i = s.length := by omega
      subst hi'
      have hstop : tupleIterNext ({ index := (s.length : Int), seq := some s } : TupleIter α) =
          (none, { index := (s.length : Int), seq := none }) := by
        simp [tupleIterNext]
      have hnone : ∀ (k : Nat) (x : Int), tupleIterTake k ({ index := x, seq := none } : TupleIter α) =
          List.replicate k none := by
        intro k x
        induction k with
        | zero => rfl
        | succ k ihk => simp [tupleIterTake, tupleIterNext, ihk, List.replicate_succ]
      simp only [tupleIterTake, hstop, hnone]
      simp [List.replicate_succ]

/-- `iter(t)` yields each item once in order and then stops for good, for every
tuple: `next` called any number `n >= len(t)` of times gives the items and then
`n - len(t)` stops. -/
def TupleIterYields : Prop :=
  ∀ (α : Type) (t : List α) (n : Nat), t.length ≤ n →
    tupleIterTake n (tupleIter t) = t.map some ++ List.replicate (n - t.length) none

theorem tupleIterYields_proven : TupleIterYields := by
  intro α t n h
  have := tupleIterTake_drop t 0 n (by omega) (by omega)
  simpa [tupleIter] using this

/-- The value of `__reduce__` when the builtins lookup runs no code. -/
def tupleIterReducePure (it : TupleIter α) : Py (TIterReduce Unit α) :=
  (tupleIterReduce (fun it => (.ok (), it)) it).1

/-- `tupleiter_len`, `__reduce__` and `__setstate__`, for every iterator state with
`0 <= index <= len(t)` (the invariant `tuple_iter`, `tupleiter_next` and
`tupleiter_setstate` keep; `len(t) <= sys.maxsize` is the tuple's): the length hint
counts what is left, and rebuilding from `__reduce__` gives an iterator with the same
items left. The exact form of `__reduce__` and `__setstate__` on every branch is
`TupleIterReduceForm`. -/
def TupleIterReduce : Prop :=
  ∀ (α : Type) (it : TupleIter α),
    (match it.seq with
      | some s => 0 ≤ it.index ∧ it.index ≤ s.length ∧ (s.length : Int) ≤ ssizeMax
      | none => True) →
    tupleIterLen it = it.rest.length ∧
    ∃ it', (match tupleIterReducePure it with
      | .ok r => tupleIterRebuild r
      | .error e => .error e) = .ok it' ∧ it'.rest = it.rest

theorem tupleIterReduce_proven : TupleIterReduce := by
  intro α it h
  cases hs : it.seq with
  | none =>
    refine ⟨by simp [tupleIterLen, TupleIter.rest, hs], tupleIter [], ?_, ?_⟩
    · simp [tupleIterReducePure, tupleIterRebuild, tupleIterReduce, hs]
    · simp [tupleIter, TupleIter.rest, hs]
  | some s =>
    rw [hs] at h
    simp only at h
    obtain ⟨h0, h1, h2⟩ := h
    have hlen : tupleIterLen it = it.rest.length := by
      simp only [tupleIterLen, TupleIter.rest, hs, List.length_drop]
      omega
    refine ⟨hlen, { index := it.index, seq := some s }, ?_, ?_⟩
    · have ha : PyLean.Sequences.asSsize it.index = .ok it.index := by
        unfold PyLean.Sequences.asSsize
        rw [if_pos]
        unfold ssizeMin ssizeMax at *
        constructor <;> omega
      simp only [tupleIterReducePure, tupleIterRebuild, tupleIterReduce, hs, tupleIterSetstate, tupleIter, ha,
        bind, Except.bind]
      have h3 : ¬ it.index < 0 := by omega
      have h4 : ¬ it.index > (s.length : Int) := by omega
      simp [h3, h4]
    · simp [TupleIter.rest, hs]

/-! ## List iterators -/

/-- Type invariant of both list iterators: `it_seq` is only cleared together with
setting the index to `-1`. -/
def ListIter.WF (it : ListIter) : Prop := it.alive = false → it.index < 0

/-- `list_iter`, `list.__reversed__`, `next`, `__setstate__` keep `ListIter.WF`, and
in such a state `next` never reaches the `NULL` `it_seq`, whatever the list has
become. Once `next` has stopped, it stops forever: no change to the list and no
`next` restarts it. (Only an explicit `__setstate__` can, and only if the iterator
stopped by holding a negative index without being exhausted, as `reversed([])` does;
an exhausted iterator ignores `__setstate__`.) -/
def ListIterSafe : Prop :=
  ∀ (α : Type) (it it' : ListIter) (l l' : List α) (x : Option α) (s : Int),
    ListIter.WF listIter ∧ ListIter.WF (listReversed l) ∧
    (it.WF →
      (∃ r, listIterNext it l = .ok r) ∧ (∃ r, listRevIterNext it l = .ok r) ∧
      (listIterNext it l = .ok (x, it') → it'.WF) ∧
      (listRevIterNext it l = .ok (x, it') → it'.WF) ∧
      (listIterSetstate it l s = .ok it' → it'.WF) ∧
      (listRevIterSetstate it l s = .ok it' → it'.WF) ∧
      (listIterNext it l = .ok (none, it') → listIterNext it' l' = .ok (none, it')) ∧
      (listRevIterNext it l = .ok (none, it') → listRevIterNext it' l' = .ok (none, it')))

theorem listIterSafe_proven : ListIterSafe := by
  intro α it it' l l' x s
  refine ⟨by simp [listIter, ListIter.WF], by simp [listReversed, ListIter.WF], ?_⟩
  intro hw
  have hdead : it.alive = false → ¬ 0 ≤ it.index := fun h => by have := hw h; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold listIterNext
    by_cases h : it.index < 0
    · simp [h]
    · have halive : it.alive = true := by
        cases ha : it.alive with
        | true => rfl
        | false => exact absurd (hw ha) h
      simp only [h, if_false, halive]
      cases listGetItemRef l it.index <;> simp
  · unfold listRevIterNext
    by_cases h : it.index < 0
    · simp [h]
    · have halive : it.alive = true := by
        cases ha : it.alive with
        | true => rfl
        | false => exact absurd (hw ha) h
      simp only [h, if_false, halive]
      cases listGetItemRef l it.index <;> simp
  · intro hr
    unfold listIterNext at hr
    split at hr
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      rw [← hr.2]; exact hw
    · split at hr
      · simp at hr
      · rename_i h1 h2
        cases hg : listGetItemRef l it.index with
        | none =>
          rw [hg] at hr
          simp only [Except.ok.injEq, Prod.mk.injEq] at hr
          rw [← hr.2]
          simp [ListIter.WF]
        | some v =>
          rw [hg] at hr
          simp only [Except.ok.injEq, Prod.mk.injEq] at hr
          rw [← hr.2]
          simp [ListIter.WF] at h2 ⊢
          simp [h2]
  · intro hr
    unfold listRevIterNext at hr
    split at hr
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      rw [← hr.2]; exact hw
    · split at hr
      · simp at hr
      · rename_i h1 h2
        cases hg : listGetItemRef l it.index with
        | none =>
          rw [hg] at hr
          simp only [Except.ok.injEq, Prod.mk.injEq] at hr
          rw [← hr.2]
          simp [ListIter.WF]
        | some v =>
          rw [hg] at hr
          simp only [Except.ok.injEq, Prod.mk.injEq] at hr
          rw [← hr.2]
          simp [ListIter.WF] at h2 ⊢
          simp [h2]
  · intro hr
    unfold listIterSetstate at hr
    cases ha : PyLean.Sequences.asSsize s with
    | error e => simp [ha, bind, Except.bind] at hr
    | ok i =>
      simp only [ha, bind, Except.bind] at hr
      split at hr
      · rename_i halive
        simp only [Except.ok.injEq] at hr
        rw [← hr]
        simp [ListIter.WF, halive]
      · simp only [Except.ok.injEq] at hr
        rw [← hr]; exact hw
  · intro hr
    unfold listRevIterSetstate at hr
    cases ha : PyLean.Sequences.asSsize s with
    | error e => simp [ha, bind, Except.bind] at hr
    | ok i =>
      simp only [ha, bind, Except.bind] at hr
      split at hr
      · rename_i halive
        simp only [Except.ok.injEq] at hr
        rw [← hr]
        simp [ListIter.WF, halive]
      · simp only [Except.ok.injEq] at hr
        rw [← hr]; exact hw
  · intro hr
    unfold listIterNext at hr
    split at hr
    · rename_i h
      simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      rw [← hr.2]
      simp [listIterNext, h]
    · split at hr
      · simp at hr
      · cases hg : listGetItemRef l it.index with
        | none =>
          rw [hg] at hr
          simp only [Except.ok.injEq, Prod.mk.injEq] at hr
          rw [← hr.2]
          simp [listIterNext]
        | some v =>
          rw [hg] at hr
          simp at hr
  · intro hr
    unfold listRevIterNext at hr
    split at hr
    · rename_i h
      simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      rw [← hr.2]
      simp [listRevIterNext, h]
    · split at hr
      · simp at hr
      · cases hg : listGetItemRef l it.index with
        | none =>
          rw [hg] at hr
          simp only [Except.ok.injEq, Prod.mk.injEq] at hr
          rw [← hr.2]
          simp [listRevIterNext]
        | some v =>
          rw [hg] at hr
          simp at hr

/-- `n` calls of a list iterator's `next` on a list that does not change. -/
def listIterTake (nxt : ListIter → List α → Py (Option α × ListIter)) (l : List α) :
    Nat → ListIter → List (Py (Option α))
  | 0, _ => []
  | n + 1, it =>
    match nxt it l with
    | .ok (v, it') => .ok v :: listIterTake nxt l n it'
    | .error e => [.error e]

theorem listIterTake_forward (l : List α) (hl : (l.length : Int) ≤ ssizeMax) (n i : Nat)
    (hi : i ≤ l.length) (hn : n = l.length - i + 1) :
    listIterTake listIterNext l n ⟨(i : Int), true⟩ =
      (l.drop i).map (fun x => .ok (some x)) ++ [.ok none] := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    have hg := listGetItemRef_nat l i hl (by omega)
    have hnn : ¬ (i : Int) < 0 := by omega
    by_cases h : i < l.length
    · have hget : l[i]? = some l[i] := List.getElem?_eq_getElem h
      have hstep : listIterNext (⟨(i : Int), true⟩ : ListIter) l =
          .ok (some l[i], ⟨((i + 1 : Nat) : Int), true⟩) := by
        simp only [listIterNext, hnn, if_false, Bool.not_true, hg, hget]
        rfl
      simp only [listIterTake, hstep]
      rw [ih (i + 1) (by omega) (by omega), drop_cons_of_lt l i h]
      rfl
    · have hnone : l[i]? = none := List.getElem?_eq_none (by omega)
      have hstep : listIterNext (⟨(i : Int), true⟩ : ListIter) l = .ok (none, ⟨-1, false⟩) := by
        simp only [listIterNext, hnn, if_false, Bool.not_true, hg, hnone]
        rfl
      have hn0 : n = 0 := by omega
      subst hn0
      simp only [listIterTake, hstep]
      simp [List.drop_eq_nil_of_le (show l.length ≤ i by omega)]

theorem listIterTake_reverse (l : List α) (hl : (l.length : Int) ≤ ssizeMax) (n i : Nat)
    (hi : i ≤ l.length) (hn : n = i + 1) :
    listIterTake listRevIterNext l n ⟨(i : Int) - 1, true⟩ =
      ((l.take i).reverse).map (fun x => .ok (some x)) ++ [.ok none] := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      have hn0 : n = 0 := by omega
      subst hn0
      have hstep : listRevIterNext (⟨((0 : Nat) : Int) - 1, true⟩ : ListIter) l =
          .ok (none, ⟨((0 : Nat) : Int) - 1, true⟩) := by
        simp [listRevIterNext]
      simp only [listIterTake, hstep]
      simp
    | succ k =>
      have hg := listGetItemRef_nat l k hl (by omega)
      have hk : k < l.length := by omega
      have hget : l[k]? = some l[k] := List.getElem?_eq_getElem hk
      have hcast : (((k + 1 : Nat) : Int) - 1) = (k : Int) := by omega
      have hnn : ¬ (k : Int) < 0 := by omega
      have hcast2 : (k : Int) - 1 = (k : Int) - 1 := rfl
      have hstep : listRevIterNext (⟨((k + 1 : Nat) : Int) - 1, true⟩ : ListIter) l =
          .ok (some l[k], ⟨(k : Int) - 1, true⟩) := by
        rw [hcast]
        simp only [listRevIterNext, hnn, if_false, Bool.not_true, hg, hget]
        rfl
      simp only [listIterTake, hstep]
      rw [ih k (by omega) (by omega)]
      have htake : l.take (k + 1) = l.take k ++ [l[k]] := by
        rw [List.take_succ_eq_append_getElem hk]
      have hrev : (l.take k ++ [l[k]]).reverse = l[k] :: (l.take k).reverse := by simp
      rw [htake, hrev]
      rfl

/-- On a list that does not change, `iter(l)` yields the items in order and `reversed(l)`
yields them in reverse, each then stopping, for every list (`len(l) <= sys.maxsize`). -/
def ListIterYields : Prop :=
  ∀ (α : Type) (l : List α), (l.length : Int) ≤ ssizeMax →
    listIterTake listIterNext l (l.length + 1) listIter =
      l.map (fun x => .ok (some x)) ++ [.ok none] ∧
    listIterTake listRevIterNext l (l.length + 1) (listReversed l) =
      l.reverse.map (fun x => .ok (some x)) ++ [.ok none]

theorem listIterYields_proven : ListIterYields := by
  intro α l hl
  constructor
  · have := listIterTake_forward l hl (l.length + 1) 0 (by omega) (by omega)
    simpa [listIter] using this
  · have := listIterTake_reverse l hl (l.length + 1) l.length (by omega) (by omega)
    simpa [listReversed] using this

/-- `__length_hint__` of the list iterators against what `next` will still produce,
on a list that does not change and any state in range; a hint never goes negative,
even after the list shrinks past the iterator. `__reduce__` gives the list and the
index for a live iterator, and rebuilding through `iter`/`reversed` and `__setstate__`
restores that index. -/
def ListIterHint : Prop :=
  ∀ (α : Type) (l : List α) (i : Int), (l.length : Int) ≤ ssizeMax →
    (0 ≤ listIterLen ⟨i, true⟩ l) ∧ (0 ≤ i → i ≤ l.length → listIterLen ⟨i, true⟩ l = l.length - i) ∧
    (0 ≤ listRevIterLen ⟨i, true⟩ l ∨ i < -1) ∧
    (-1 ≤ i → i < l.length → listRevIterLen ⟨i, true⟩ l = i + 1) ∧
    (0 ≤ i → i ≤ l.length →
      listIterReduce ⟨i, true⟩ l = (l, some i) ∧ listIterSetstate listIter l i = .ok ⟨i, true⟩) ∧
    (0 ≤ i → i < l.length →
      listIterReduce ⟨i, true⟩ l = (l, some i) ∧ listRevIterSetstate (listReversed l) l i = .ok ⟨i, true⟩) ∧
    (i < 0 → listIterReduce ⟨i, true⟩ l = ([], none))

theorem listIterHint_proven : ListIterHint := by
  intro α l i hl
  have hssize : 0 ≤ i → i ≤ l.length → PyLean.Sequences.asSsize i = .ok i := by
    intro h0 h1
    unfold PyLean.Sequences.asSsize
    rw [if_pos]
    unfold ssizeMin ssizeMax at *
    constructor <;> omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold listIterLen
    simp only
    split
    · split <;> omega
    · omega
  · intro h0 h1
    unfold listIterLen
    simp only [show i ≥ 0 by omega, if_true, show (l.length : Int) - i ≥ 0 by omega]
  · unfold listRevIterLen
    simp only [Bool.not_true, Bool.false_eq_true, false_or]
    split <;> omega
  · intro h0 h1
    unfold listRevIterLen
    simp only [Bool.not_true, Bool.false_eq_true, false_or]
    rw [if_neg (by omega)]
  · intro h0 h1
    refine ⟨by simp [listIterReduce, h0], ?_⟩
    simp only [listIterSetstate, hssize h0 h1, bind, Except.bind, listIter]
    have h3 : ¬ i < -1 := by omega
    have h4 : ¬ i > (l.length : Int) := by omega
    simp [h3, h4]
  · intro h0 h1
    refine ⟨by simp [listIterReduce, h0], ?_⟩
    simp only [listRevIterSetstate, hssize h0 (by omega), bind, Except.bind, listReversed]
    have h3 : ¬ i < -1 := by omega
    have h4 : ¬ i > (l.length : Int) - 1 := by omega
    simp [h3, h4]
  · intro h0
    have : ¬ i ≥ 0 := by omega
    simp [listIterReduce, this]

end PyLean.BytesObj.Seq
