import PyLean.BytesObj.Seq.ListRows8
import PyLean.Sequences.Index
import PyLean.Sequences.SliceAssign

/-!
`l.index`, `l.count` and `l.remove` under a comparison that changes the list, `l.index`'s argument
conversion and clipping, the type dispatch of `l[item]`, `l[item] = v` and `del l[item]`, and the
callable of the list iterators' `__reduce__` (Objects/listobject.c, CPython 3.15.2).
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α ρ : Type}

/-! ## `l.index` -/

/-- `l.index(value, start, stop)`, `list_index_impl` (listobject.c:3345-3375), for every comparison,
including one that changes the list. The bounds are clipped once, against the size on entry
(:3350-3359); then each pass reads through `list_get_item_ref` on the list as it is now (:3361), so

* at or past `stop` the search ends without a call;
* past the current end it ends without a call ("out-of-bounds", :3362-3365);
* otherwise it compares the current item and goes on with the list the comparison left: a true
  comparison returns `i` (:3368-3369), a raising one its exception (:3370-3371), a false one the
  search from `i + 1` on that list;
* falling out of the loop is `ValueError("list.index(x): x not in list")` (:3373);
* so if every comparison is false and removes the last item, as an `__eq__` that pops does, only
  the first `ceil(n/2)` items are compared, the result is that `ValueError`, and the first `n // 2`
  items remain. A loop over a copy of the items would compare all `n` and leave nothing.

Hypothesis: lists have at most `PY_SSIZE_T_MAX` items (type invariant). -/
def IndexStep : Prop :=
  ∀ (α : Type) (cmp : Cmp α) (v : α) (stop : Int),
    (∀ (f : Nat) (i : Int) (p : LObj α), ¬ i < stop → indexLoop cmp v stop (f + 1) i p = (.ok none, p)) ∧
    (∀ (f i : Nat) (p : LObj α), (p.items.length : Int) ≤ ssizeMax → (i : Int) ≤ ssizeMax →
      p.items.length ≤ i → indexLoop cmp v stop (f + 1) i p = (.ok none, p)) ∧
    (∀ (f i : Nat) (p p' : LObj α) (h : i < p.items.length), (p.items.length : Int) ≤ ssizeMax →
      (i : Int) < stop →
      (cmp p p.items[i] v = (.ok false, p') →
        indexLoop cmp v stop (f + 1) i p = indexLoop cmp v stop f ((i : Int) + 1) p') ∧
      (cmp p p.items[i] v = (.ok true, p') → indexLoop cmp v stop (f + 1) i p = (.ok (some (i : Int)), p')) ∧
      (∀ e, cmp p p.items[i] v = (.error e, p') → indexLoop cmp v stop (f + 1) i p = (.error e, p'))) ∧
    (∀ (fuel : Nat) (o o' : LObj α) (start stop' : Option Int),
      indexLoop cmp v (listIndexBounds o.items.length start stop').2 fuel
          (listIndexBounds o.items.length start stop').1 o = (.ok none, o') →
      listIndex cmp fuel o v start stop' = (.error (.valueError "list.index(x): x not in list"), o')) ∧
    ((∀ (p : LObj α) (x : α), (cmp p x v).1 = .ok false ∧ ((cmp p x v).2).items = p.items.dropLast) →
      ∀ (o : LObj α) (fuel : Nat), (o.items.length : Int) ≤ ssizeMax → o.items.length < fuel →
        (listIndex cmp fuel o v none none).1 = .error (.valueError "list.index(x): x not in list") ∧
        ((listIndex cmp fuel o v none none).2).items = o.items.take (o.items.length / 2))

theorem indexLoop_end (cmp : Cmp α) (v : α) (stop : Int) (f i : Nat) (p : LObj α)
    (hl : (p.items.length : Int) ≤ ssizeMax) (hi : (i : Int) ≤ ssizeMax) (h : p.items.length ≤ i) :
    indexLoop cmp v stop (f + 1) i p = (.ok none, p) := by
  have hg := getItemRefC_nat p.items i hl hi
  have hn : p.items[i]? = none := List.getElem?_eq_none h
  rw [hn] at hg
  simp only [indexLoop]
  split
  · rw [hg]
  · rfl

theorem indexLoop_item (cmp : Cmp α) (v : α) (stop : Int) (f i : Nat) (p : LObj α)
    (h : i < p.items.length) (hl : (p.items.length : Int) ≤ ssizeMax) (hs : (i : Int) < stop) :
    indexLoop cmp v stop (f + 1) i p =
      match cmp p p.items[i] v with
      | (.ok true, o') => (.ok (some (i : Int)), o')
      | (.ok false, o') => indexLoop cmp v stop f ((i : Int) + 1) o'
      | (.error e, o') => (.error e, o') := by
  have hg := getItemRefC_nat p.items i hl (by omega)
  rw [List.getElem?_eq_getElem h] at hg
  simp only [indexLoop, if_pos hs, hg]
  generalize cmp p p.items[i] v = r
  obtain ⟨r, q⟩ := r
  cases r with
  | error e => rfl
  | ok b => cases b <;> rfl

theorem indexLoop_pop (cmp : Cmp α) (v : α)
    (hc : ∀ (p : LObj α) (x : α), (cmp p x v).1 = .ok false ∧ ((cmp p x v).2).items = p.items.dropLast) :
    ∀ (f i : Nat) (p : LObj α), (p.items.length : Int) ≤ ssizeMax → (i : Int) ≤ ssizeMax →
      p.items.length - i < f →
      (indexLoop cmp v ssizeMax f (i : Int) p).1 = .ok none ∧
      ((indexLoop cmp v ssizeMax f (i : Int) p).2).items =
        p.items.take (p.items.length - (p.items.length - i + 1) / 2) := by
  intro f
  induction f with
  | zero => intro i p _ _ h; omega
  | succ f ih =>
    intro i p hl hi h
    by_cases hlt : i < p.items.length
    · obtain ⟨hr, hp⟩ := hc p p.items[i]
      have hcmp : cmp p p.items[i] v = (.ok false, (cmp p p.items[i] v).2) := by rw [← hr]
      have hstep : indexLoop cmp v ssizeMax (f + 1) (i : Int) p =
          indexLoop cmp v ssizeMax f ((i : Int) + 1) (cmp p p.items[i] v).2 := by
        rw [indexLoop_item cmp v ssizeMax f i p hlt hl (by omega), hcmp]
      generalize hq : (cmp p p.items[i] v).2 = q at hstep hp
      have hql : q.items.length = p.items.length - 1 := by rw [hp, List.length_dropLast]
      obtain ⟨r1, r2⟩ := ih (i + 1) q (by rw [hql]; omega) (by omega) (by rw [hql]; omega)
      rw [show ((i + 1 : Nat) : Int) = (i : Int) + 1 by omega] at r1 r2
      rw [hstep]
      refine ⟨r1, ?_⟩
      rw [r2, hp, List.dropLast_eq_take, List.take_take]
      refine congrArg (fun n => List.take n p.items) ?_
      simp only [List.length_take]
      omega
    · rw [indexLoop_end cmp v ssizeMax f i p hl hi (by omega)]
      refine ⟨rfl, ?_⟩
      show p.items = _
      have : p.items.length - (p.items.length - i + 1) / 2 = p.items.length := by omega
      rw [this, List.take_length]

theorem listIndexBounds_none (n : Int) : listIndexBounds n none none = (0, ssizeMax) := by
  have hM : ssizeMax = 9223372036854775807 := by decide
  have hm : ssizeMin = -9223372036854775808 := by decide
  simp only [listIndexBounds, Option.getD_none, PyLean.Sequences.sliceIndex, RangeSlice.clampSsize, hM, hm]
  simp

theorem indexStep_proven : IndexStep := by
  intro α cmp v stop
  refine ⟨fun f i p h => ?_, fun f i p hl hi h => indexLoop_end cmp v stop f i p hl hi h,
    fun f i p p' h hl hs => ?_, fun fuel o o' start stop' h => ?_, fun hc o fuel hl hf => ?_⟩
  · simp only [indexLoop, if_neg h]
  · rw [indexLoop_item cmp v stop f i p h hl hs]
    refine ⟨fun hr => by rw [hr], fun hr => by rw [hr], fun e hr => by rw [hr]⟩
  · unfold listIndex
    simp only
    rw [h]
  · obtain ⟨r1, r2⟩ := indexLoop_pop cmp v hc fuel 0 o hl (by decide) (by omega)
    unfold listIndex
    rw [listIndexBounds_none]
    simp only
    have e0 : ((0 : Nat) : Int) = 0 := rfl
    rw [e0] at r1 r2
    generalize indexLoop cmp v ssizeMax fuel 0 o = r at r1 r2 ⊢
    obtain ⟨r, q⟩ := r
    simp only at r1 r2
    subst r1
    refine ⟨rfl, ?_⟩
    show q.items = _
    rw [r2]
    congr 1
    omega

/-- `l.index(value[, start[, stop]])` as a call: the clinic wrapper `list_index`
(Objects/clinic/listobject.c.h:320-348) converts `start`, then `stop`, with `_PyEval_SliceIndexNotNone`
(Python/ceval.c:2957-2979), and only then runs `list_index_impl` (`IndexStep`) on the list as those
conversions left it:

* an `int` saturates to `Py_ssize_t` and runs no code; an object with `__index__` runs it, which may
  change the list or raise, and its result saturates; anything else is
  `TypeError("slice indices must be integers or have an __index__ method")`;
* a failure of `start`'s conversion ends the call before `stop` is looked at, and a failure of
  `stop`'s ends it before the search; either keeps the list as the `__index__` calls left it;
* the bounds `list_index_impl` computes from the list's size after the conversions are those of
  `slice(start, stop).indices(len(l))`: the positions searched in the list are the positions of
  `range(*slice(start, stop).indices(len(l)))`, and the start is in `[0, PY_SSIZE_T_MAX]`
  ("interpreted as in the slice notation", Doc/library/stdtypes.rst, common sequence operations).

Hypothesis: lists have at most `PY_SSIZE_T_MAX` items (type invariant). -/
def IndexCall : Prop :=
  ∀ (α : Type) (cmp : Cmp α) (fuel : Nat) (o : LObj α) (v : α) (a b : IdxArg α),
    (∀ n tp, sliceIndexArg (.int n tp) o = (.ok (RangeSlice.clampSsize n), o)) ∧
    (∀ tp (f : LObj α → Py Int × LObj α),
      (∀ n o', f o = (.ok n, o') → sliceIndexArg (.index tp f) o = (.ok (RangeSlice.clampSsize n), o')) ∧
      (∀ e o', f o = (.error e, o') → sliceIndexArg (.index tp f) o = (.error e, o'))) ∧
    (∀ tp, sliceIndexArg (.notIndex tp) o =
      (.error (.typeError "slice indices must be integers or have an __index__ method"), o)) ∧
    (∀ e o1, sliceIndexArg a o = (.error e, o1) → ∀ sb,
      listIndexCall cmp fuel o v (some a) sb = (.error e, o1)) ∧
    (∀ s o1 e o2, sliceIndexArg a o = (.ok s, o1) → sliceIndexArg b o1 = (.error e, o2) →
      listIndexCall cmp fuel o v (some a) (some b) = (.error e, o2)) ∧
    (∀ s o1 t o2, sliceIndexArg a o = (.ok s, o1) → sliceIndexArg b o1 = (.ok t, o2) →
      listIndexCall cmp fuel o v (some a) (some b) = listIndex cmp fuel o2 v (some s) (some t)) ∧
    (∀ s o1, sliceIndexArg a o = (.ok s, o1) →
      listIndexCall cmp fuel o v (some a) none = listIndex cmp fuel o1 v (some s) none) ∧
    listIndexCall cmp fuel o v none none = listIndex cmp fuel o v none none ∧
    (∀ (n : Int) (start stop : Option Int), 0 ≤ n → n ≤ ssizeMax →
      ∃ a' b', RangeSlice.sliceIndices ⟨start, stop, none⟩ n = .ok (a', b', 1) ∧
        0 ≤ (listIndexBounds n start stop).1 ∧ (listIndexBounds n start stop).1 ≤ ssizeMax ∧
        ∀ j, 0 ≤ j → j < n →
          ((listIndexBounds n start stop).1 ≤ j ∧ j < (listIndexBounds n start stop).2 ↔ a' ≤ j ∧ j < b'))

theorem indexCall_proven : IndexCall := by
  intro α cmp fuel o v a b
  refine ⟨fun n tp => rfl, fun tp f => ⟨fun n o' h => ?_, fun e o' h => ?_⟩, fun tp => rfl,
    fun e o1 h sb => ?_, fun s o1 e o2 h1 h2 => ?_, fun s o1 t o2 h1 h2 => ?_, fun s o1 h1 => ?_, rfl,
    fun n start stop hn hn' => ?_⟩
  · simp only [sliceIndexArg, IdxArg.index?, h]
  · simp only [sliceIndexArg, IdxArg.index?, h]
  · simp only [listIndexCall, h]
  · simp only [listIndexCall, h1, h2]
  · simp only [listIndexCall, h1, h2]
  · simp only [listIndexCall, h1]
  · refine ⟨_, _, PyLean.Sequences.sliceIndices_step1 start stop n hn, ?_, ?_, fun j hj hjn => ?_⟩
    · exact PyLean.Sequences.normIdx_nonneg _ n hn
    · obtain ⟨h1, -, h3, -⟩ := index_bounds n start stop hn hn'
      rw [h1]; exact h3
    · have e1 := PyLean.Sequences.clip_start start n hn hn' j hj hjn
      have e2 := PyLean.Sequences.clip_stop stop n hn hn' j hj hjn
      unfold PyLean.Sequences.normIdx at e1 e2
      simp only [listIndexBounds]
      rw [e1, e2]

/-! ## `l.count` -/

/-- `l.count(value)`, `list_count_impl` (listobject.c:3386-3410), for every comparison, including
one that changes the list. Each pass reads through `list_get_item_ref` on the list as it is now
(:3392), so

* past the current end the count is returned (:3393-3395, :3409);
* an item that is `value` itself is counted without a call (:3397-3401);
* otherwise the comparison runs, and the count goes on, with one more for a true comparison, on the
  list the comparison left (:3402-3405); a raising comparison returns its exception (:3406-3407);
* so if every comparison is true and removes the last item, and no item is `value` itself, the
  count is `ceil(n/2)` and the first `n // 2` items remain; a loop over a copy would count `n`.

Hypothesis: lists have at most `PY_SSIZE_T_MAX` items (type invariant). -/
def CountStep : Prop :=
  ∀ (α : Type) (same : α → α → Bool) (cmp : Cmp α) (v : α),
    (∀ (f i : Nat) (c : Int) (p : LObj α), (p.items.length : Int) ≤ ssizeMax → (i : Int) ≤ ssizeMax →
      p.items.length ≤ i → countLoop same cmp v (f + 1) i c p = (.ok c, p)) ∧
    (∀ (f i : Nat) (c : Int) (p : LObj α) (h : i < p.items.length), (p.items.length : Int) ≤ ssizeMax →
      same p.items[i] v = true →
      countLoop same cmp v (f + 1) i c p = countLoop same cmp v f ((i : Int) + 1) (c + 1) p) ∧
    (∀ (f i : Nat) (c : Int) (p p' : LObj α) (h : i < p.items.length), (p.items.length : Int) ≤ ssizeMax →
      same p.items[i] v = false →
      (cmp p p.items[i] v = (.ok true, p') →
        countLoop same cmp v (f + 1) i c p = countLoop same cmp v f ((i : Int) + 1) (c + 1) p') ∧
      (cmp p p.items[i] v = (.ok false, p') →
        countLoop same cmp v (f + 1) i c p = countLoop same cmp v f ((i : Int) + 1) c p') ∧
      (∀ e, cmp p p.items[i] v = (.error e, p') → countLoop same cmp v (f + 1) i c p = (.error e, p'))) ∧
    ((∀ (p : LObj α) (x : α), (cmp p x v).1 = .ok true ∧ ((cmp p x v).2).items = p.items.dropLast) →
      ∀ (o : LObj α) (fuel : Nat), (∀ x ∈ o.items, same x v = false) →
        (o.items.length : Int) ≤ ssizeMax → o.items.length < fuel →
        (listCount same cmp fuel o v).1 = .ok (((o.items.length + 1) / 2 : Nat) : Int) ∧
        ((listCount same cmp fuel o v).2).items = o.items.take (o.items.length / 2))

theorem countLoop_item (same : α → α → Bool) (cmp : Cmp α) (v : α) (f i : Nat) (c : Int) (p : LObj α)
    (h : i < p.items.length) (hl : (p.items.length : Int) ≤ ssizeMax) :
    countLoop same cmp v (f + 1) i c p =
      if same p.items[i] v then countLoop same cmp v f ((i : Int) + 1) (c + 1) p
      else match cmp p p.items[i] v with
        | (.ok true, o') => countLoop same cmp v f ((i : Int) + 1) (c + 1) o'
        | (.ok false, o') => countLoop same cmp v f ((i : Int) + 1) c o'
        | (.error e, o') => (.error e, o') := by
  have hg := getItemRefC_nat p.items i hl (by omega)
  rw [List.getElem?_eq_getElem h] at hg
  simp only [countLoop, hg]
  by_cases hs : same p.items[i] v = true
  · simp only [hs, if_true]
  · simp only [hs, Bool.false_eq_true, if_false]
    generalize cmp p p.items[i] v = r
    obtain ⟨r, q⟩ := r
    cases r with
    | error e => rfl
    | ok b => cases b <;> rfl

theorem countLoop_end (same : α → α → Bool) (cmp : Cmp α) (v : α) (f i : Nat) (c : Int) (p : LObj α)
    (hl : (p.items.length : Int) ≤ ssizeMax) (hi : (i : Int) ≤ ssizeMax) (h : p.items.length ≤ i) :
    countLoop same cmp v (f + 1) i c p = (.ok c, p) := by
  have hg := getItemRefC_nat p.items i hl hi
  rw [List.getElem?_eq_none h] at hg
  simp only [countLoop, hg]

theorem countLoop_pop (same : α → α → Bool) (cmp : Cmp α) (v : α)
    (hc : ∀ (p : LObj α) (x : α), (cmp p x v).1 = .ok true ∧ ((cmp p x v).2).items = p.items.dropLast) :
    ∀ (f i : Nat) (c : Int) (p : LObj α), (∀ x ∈ p.items, same x v = false) →
      (p.items.length : Int) ≤ ssizeMax → (i : Int) ≤ ssizeMax → p.items.length - i < f →
      (countLoop same cmp v f (i : Int) c p).1 = .ok (c + (((p.items.length - i + 1) / 2 : Nat) : Int)) ∧
      ((countLoop same cmp v f (i : Int) c p).2).items =
        p.items.take (p.items.length - (p.items.length - i + 1) / 2) := by
  intro f
  induction f with
  | zero => intro i c p _ _ _ h; omega
  | succ f ih =>
    intro i c p hs hl hi h
    by_cases hlt : i < p.items.length
    · obtain ⟨hr, hp⟩ := hc p p.items[i]
      have hcmp : cmp p p.items[i] v = (.ok true, (cmp p p.items[i] v).2) := by rw [← hr]
      have hsame : same p.items[i] v = false := hs _ (List.getElem_mem hlt)
      have hstep : countLoop same cmp v (f + 1) (i : Int) c p =
          countLoop same cmp v f ((i : Int) + 1) (c + 1) (cmp p p.items[i] v).2 := by
        rw [countLoop_item same cmp v f i c p hlt hl, hsame, hcmp]
        rfl
      generalize hq : (cmp p p.items[i] v).2 = q at hstep hp
      have hql : q.items.length = p.items.length - 1 := by rw [hp, List.length_dropLast]
      have hqs : ∀ x ∈ q.items, same x v = false := by
        intro x hx
        rw [hp] at hx
        exact hs x (List.dropLast_subset _ hx)
      obtain ⟨r1, r2⟩ := ih (i + 1) (c + 1) q hqs (by rw [hql]; omega) (by omega) (by rw [hql]; omega)
      rw [show ((i + 1 : Nat) : Int) = (i : Int) + 1 by omega] at r1 r2
      rw [hstep]
      refine ⟨?_, ?_⟩
      · rw [r1, hql]
        congr 1
        omega
      · rw [r2, hp, List.dropLast_eq_take, List.take_take]
        congr 1
        simp only [List.length_take]
        omega
    · rw [countLoop_end same cmp v f i c p hl hi (by omega)]
      refine ⟨?_, ?_⟩
      · show Except.ok c = _
        congr 1
        omega
      · show p.items = _
        have : p.items.length - (p.items.length - i + 1) / 2 = p.items.length := by omega
        rw [this, List.take_length]

theorem countStep_proven : CountStep := by
  intro α same cmp v
  refine ⟨fun f i c p hl hi h => countLoop_end same cmp v f i c p hl hi h,
    fun f i c p h hl hs => ?_, fun f i c p p' h hl hs => ?_, fun hc o fuel hs hl hf => ?_⟩
  · rw [countLoop_item same cmp v f i c p h hl, if_pos hs]
  · rw [countLoop_item same cmp v f i c p h hl, hs]
    refine ⟨fun hr => by rw [hr]; rfl, fun hr => by rw [hr]; rfl, fun e hr => by rw [hr]; rfl⟩
  · obtain ⟨r1, r2⟩ := countLoop_pop same cmp v hc fuel 0 0 o hs hl (by decide) (by omega)
    have e0 : ((0 : Nat) : Int) = 0 := rfl
    rw [e0] at r1 r2
    unfold listCount
    refine ⟨?_, ?_⟩
    · rw [r1]
      congr 1
      omega
    · rw [r2]
      congr 1
      omega

/-! ## `l.remove` -/

/-- `l.remove(value)`, `list_remove_impl` (listobject.c:3424-3445), for every comparison, including
one that changes the list. The loop tests `i < Py_SIZE(self)` on the list as it is now (:3430), so

* past the current end it raises `ValueError("list.remove(x): x not in list")` (:3443);
* otherwise it compares `self->ob_item[i]` of the current list (:3431-3433): a false comparison goes
  on from `i + 1` on the list the comparison left; a raising one returns its exception (:3440-3441),
  with that list;
* a true one deletes `self[i:i+1]` with the old `i` on the list the comparison left
  (`list_ass_slice_lock_held`, :3436), which clips: the item now at `i` goes, or nothing if the list
  became shorter than `i + 1`; this never fails on a well-formed list.

Hypothesis for the deletion: the comparison leaves a well-formed list (`LObj.WF`, type invariant). -/
def RemoveStep : Prop :=
  ∀ (α : Type) (cmp : Cmp α) (v : α),
    (∀ (f i : Nat) (p : LObj α), p.items.length ≤ i →
      removeLoop cmp v (f + 1) i p = (.error (.valueError "list.remove(x): x not in list"), p)) ∧
    (∀ (f i : Nat) (p p' : LObj α) (h : i < p.items.length),
      (cmp p p.items[i] v = (.ok false, p') → removeLoop cmp v (f + 1) i p = removeLoop cmp v f ((i : Int) + 1) p') ∧
      (∀ e, cmp p p.items[i] v = (.error e, p') → removeLoop cmp v (f + 1) i p = (.error e, p')) ∧
      (cmp p p.items[i] v = (.ok true, p') → p'.WF →
        ∃ q, removeLoop cmp v (f + 1) i p = (.ok (), q) ∧ q.items = p'.items.eraseIdx i ∧ q.WF))

theorem removeLoop_item (cmp : Cmp α) (v : α) (f i : Nat) (p : LObj α) (h : i < p.items.length) :
    removeLoop cmp v (f + 1) i p =
      match cmp p p.items[i] v with
      | (.ok true, o') =>
        match listAssSlice o' i (i + 1) none with
        | .ok o'' => (.ok (), o'')
        | .error e => (.error e, o')
      | (.ok false, o') => removeLoop cmp v f ((i : Int) + 1) o'
      | (.error e, o') => (.error e, o') := by
  have hs : slot p.items (i : Int) = some p.items[i] := by
    rw [slot_nat]; exact List.getElem?_eq_getElem h
  simp only [removeLoop, show ((i : Int) < p.items.length) by omega, if_true, hs]
  generalize cmp p p.items[i] v = r
  obtain ⟨r, q⟩ := r
  cases r with
  | error e => rfl
  | ok b => cases b <;> rfl

theorem listAssSlice_del_one (o : LObj α) (i : Nat) (hw : o.WF) :
    ∃ q, listAssSlice o i (i + 1) none = .ok q ∧ q.items = o.items.eraseIdx i ∧ q.WF := by
  obtain ⟨q, h1, h2, h3⟩ := listAssSlice_del o i (i + 1) hw
  refine ⟨q, h1, ?_, h3⟩
  rw [h2, List.eraseIdx_eq_take_drop_succ]
  congr 2 <;> omega

theorem removeStep_proven : RemoveStep := by
  intro α cmp v
  refine ⟨fun f i p h => ?_, fun f i p p' h => ?_⟩
  · simp only [removeLoop, show ¬ ((i : Int) < p.items.length) by omega, if_false]
  · rw [removeLoop_item cmp v f i p h]
    refine ⟨fun hr => by rw [hr], fun e hr => by rw [hr], fun hr hw => ?_⟩
    rw [hr]
    obtain ⟨q, h1, h2, h3⟩ := listAssSlice_del_one p' i hw
    exact ⟨q, by simp only [h1], h2, h3⟩

/-- What `l.remove(x)` does when the comparisons leave the list alone (the documented case,
Doc/library/stdtypes.rst, mutable sequence `s.remove(x)`), for every element type and every
comparison, which may raise: with the comparisons run in order from the first item,

* if the first that does not return false returns true, at position `k`, item `k` is deleted and
  the others keep their order;
* if it raises, `l.remove` raises that exception and the list is unchanged;
* if every one returns false, `ValueError("list.remove(x): x not in list")`, list unchanged.

A `remove` that took a raising `__eq__` for false, or deleted the last match, fails this.
Hypotheses: the list is well formed (`LObj.WF`, type invariant); `fuel` exceeds its length. -/
def RemoveResult : Prop :=
  ∀ (α ρ : Type) (E : ElemOps α ρ) (o : LObj α) (v : α) (fuel : Nat), o.WF → o.items.length < fuel →
    (∀ (k : Nat) (hk : k < o.items.length),
      (∀ (j : Nat) (hj : j < k), richBool E .eq (o.items[j]'(by omega)) v = .ok false) →
      richBool E .eq o.items[k] v = .ok true →
      ∃ q, listRemove (pureCmp E) fuel o v = (.ok (), q) ∧ q.items = o.items.eraseIdx k) ∧
    (∀ (k : Nat) (hk : k < o.items.length) (e : PyExc),
      (∀ (j : Nat) (hj : j < k), richBool E .eq (o.items[j]'(by omega)) v = .ok false) →
      richBool E .eq o.items[k] v = .error e → listRemove (pureCmp E) fuel o v = (.error e, o)) ∧
    ((∀ (j : Nat) (hj : j < o.items.length), richBool E .eq o.items[j] v = .ok false) →
      listRemove (pureCmp E) fuel o v = (.error (.valueError "list.remove(x): x not in list"), o))

theorem removeLoop_pure_false (E : ElemOps α ρ) (o : LObj α) (v : α) (f i : Nat) (h : i < o.items.length)
    (hx : richBool E .eq o.items[i] v = .ok false) :
    removeLoop (pureCmp E) v (f + 1) i o = removeLoop (pureCmp E) v f ((i : Int) + 1) o := by
  rw [removeLoop_item (pureCmp E) v f i o h]
  simp only [pureCmp, hx]

theorem removeLoop_pure_skip (E : ElemOps α ρ) (o : LObj α) (v : α) (k : Nat) (hk : k ≤ o.items.length) :
    ∀ (m f j : Nat), j + m = k →
      (∀ (t : Nat) (ht : t < o.items.length), j ≤ t → t < k → richBool E .eq o.items[t] v = .ok false) →
      removeLoop (pureCmp E) v (f + m) (j : Int) o = removeLoop (pureCmp E) v f (k : Int) o := by
  intro m
  induction m with
  | zero => intro f j h _; subst h; rfl
  | succ m ih =>
    intro f j h hpre
    have hj : j < o.items.length := by omega
    rw [show f + (m + 1) = f + m + 1 by omega,
      removeLoop_pure_false E o v (f + m) j hj (hpre j hj (by omega) (by omega))]
    rw [show (j : Int) + 1 = ((j + 1 : Nat) : Int) by omega]
    exact ih f (j + 1) (by omega) (fun t ht h1 h2 => hpre t ht (by omega) h2)

theorem removeResult_proven : RemoveResult := by
  intro α ρ E o v fuel hw hf
  refine ⟨fun k hk hpre hx => ?_, fun k hk e hpre hx => ?_, fun hall => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 + k := ⟨fuel - k - 1, by omega⟩
    have hs := removeLoop_pure_skip E o v k (by omega) k (m + 1) 0 (by omega)
      (fun t ht _ h2 => hpre t h2)
    push_cast at hs
    unfold listRemove
    rw [hs, removeLoop_item (pureCmp E) v m k o hk]
    simp only [pureCmp, hx]
    obtain ⟨q, h1, h2, -⟩ := listAssSlice_del_one o k hw
    exact ⟨q, by simp only [h1], h2⟩
  · obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 + k := ⟨fuel - k - 1, by omega⟩
    have hs := removeLoop_pure_skip E o v k (by omega) k (m + 1) 0 (by omega)
      (fun t ht _ h2 => hpre t h2)
    push_cast at hs
    unfold listRemove
    rw [hs, removeLoop_item (pureCmp E) v m k o hk]
    simp only [pureCmp, hx]
  · obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 + o.items.length := ⟨fuel - o.items.length - 1, by omega⟩
    have hs := removeLoop_pure_skip E o v o.items.length (by omega) o.items.length (m + 1) 0 (by omega)
      (fun t ht _ _ => hall t ht)
    push_cast at hs
    unfold listRemove
    rw [hs]
    simp only [removeLoop, show ¬ ((o.items.length : Int) < o.items.length) by omega, if_false]

/-! ## `l[item]` -/

/-- `l[item]`, `list_subscript` (listobject.c:3711-3733), for every kind of `item`:

* an object with `__index__` (`_PyIndex_Check`, :3715) runs it first (`PyNumber_AsSsize_t(item,
  PyExc_IndexError)`, :3717): if it raises, that exception, with the list as `__index__` left it;
  if its value does not fit `Py_ssize_t`, `IndexError("cannot fit '<type>' into an
  index-sized integer")`; otherwise the size is read after it ran (:3720-3721), and the result is
  the item at `n` (or `n + len` for a negative `n`) of the list as it is then, or
  `IndexError("list index out of range")` (`list_item`, :695-714);
* an `int` (a subclass too) is the same with no code run;
* a slice is `list_slice_subscript` (:3724-3725);
* anything else is `TypeError("list indices must be integers or slices, not <type>")`
  (:3727-3731).

Hypothesis: lists have at most `PY_SSIZE_T_MAX` items (type invariant). `<type>` is the type's name
cut by `%.200s` to 200 bytes of UTF-8 without a partial character (`trunc200`). -/
def SubscriptDispatch : Prop :=
  ∀ (α : Type) (o : LObj α) (tp : String) (f : LObj α → Py Int × LObj α),
    (∀ e o', f o = (.error e, o') → listSubscriptAny o (.index tp f) = (.error e, o')) ∧
    (∀ n o', f o = (.ok n, o') → (o'.items.length : Int) ≤ ssizeMax →
      (¬ (ssizeMin ≤ n ∧ n ≤ ssizeMax) → listSubscriptAny o (.index tp f) =
        (.error (.indexError s!"cannot fit '{trunc200 tp}' into an index-sized integer"), o')) ∧
      (ssizeMin ≤ n → n ≤ ssizeMax → -(o'.items.length : Int) ≤ n → n < o'.items.length →
        ∃ x, o'.items[(if n < 0 then n + (o'.items.length : Int) else n).toNat]? = some x ∧
          listSubscriptAny o (.index tp f) = (.ok (.inl x), o')) ∧
      (ssizeMin ≤ n → n ≤ ssizeMax → ¬ (-(o'.items.length : Int) ≤ n ∧ n < o'.items.length) →
        listSubscriptAny o (.index tp f) = (.error (.indexError "list index out of range"), o'))) ∧
    (∀ n, listSubscriptAny o (.int n tp) = listSubscriptAny o (.index tp (fun p => (.ok n, p)))) ∧
    (∀ s r, listGetSlice o.items s = .ok r → listSubscriptAny o (.slice s) = (.ok (.inr r), o)) ∧
    (∀ s e, listGetSlice o.items s = .error e → listSubscriptAny o (.slice s) = (.error e, o)) ∧
    listSubscriptAny o (.other tp) =
      (.error (.typeError s!"list indices must be integers or slices, not {trunc200 tp}"), o)

theorem validIndex_ssize (k n : Int) (h0 : ssizeMin ≤ k) (h1 : k ≤ ssizeMax) (hn : 0 ≤ n)
    (hn' : n ≤ ssizeMax) : validIndex k n = decide (0 ≤ k ∧ k < n) :=
  validIndex_eq k n (by unfold ssizeMin at h0; omega) (by unfold ssizeMax at h1; omega) hn hn'

theorem idx_bounds (n len : Int) (h1 : ssizeMin ≤ n) (h2 : n ≤ ssizeMax) (hl : 0 ≤ len) (hl' : len ≤ ssizeMax) :
    ssizeMin ≤ (if n < 0 then n + len else n) ∧ (if n < 0 then n + len else n) ≤ ssizeMax ∧
    (0 ≤ (if n < 0 then n + len else n) ∧ (if n < 0 then n + len else n) < len ↔ -len ≤ n ∧ n < len) := by
  unfold ssizeMin ssizeMax at *
  split <;> omega

theorem subscriptDispatch_proven : SubscriptDispatch := by
  intro α o tp f
  refine ⟨fun e o' h => ?_, fun n o' h hl => ⟨fun hn => ?_, fun h1 h2 h3 h4 => ?_, fun h1 h2 h3 => ?_⟩,
    fun n => rfl, fun s r h => ?_, fun s e h => ?_, rfl⟩
  · simp only [listSubscriptAny, listSubscriptAny.idxArm, h]
  · simp only [listSubscriptAny, listSubscriptAny.idxArm, h, asSsizeIndexError, if_neg hn]
  · obtain ⟨b1, b2, b3⟩ := idx_bounds n o'.items.length h1 h2 (by omega) hl
    have hin := b3.mpr ⟨h3, h4⟩
    simp only [listSubscriptAny, listSubscriptAny.idxArm, h, asSsizeIndexError, if_pos (And.intro h1 h2)]
    generalize (if n < 0 then n + (o'.items.length : Int) else n) = k at b1 b2 hin ⊢
    have hv : validIndex k o'.items.length = true := by
      rw [validIndex_ssize k _ b1 b2 (by omega) hl]; simp [hin.1, hin.2]
    have hx : o'.items[k.toNat]? = some (o'.items[k.toNat]'(by omega)) := List.getElem?_eq_getElem _
    have hs : slot o'.items k = some (o'.items[k.toNat]'(by omega)) := by
      simp only [slot, if_pos hin.1, hx]
    refine ⟨_, hx, ?_⟩
    simp only [listItem, hv, Bool.not_true, Bool.false_eq_true, if_false, hs]
  · obtain ⟨b1, b2, b3⟩ := idx_bounds n o'.items.length h1 h2 (by omega) hl
    have hout : ¬ (0 ≤ (if n < 0 then n + (o'.items.length : Int) else n) ∧
        (if n < 0 then n + (o'.items.length : Int) else n) < o'.items.length) := fun hh => h3 (b3.mp hh)
    simp only [listSubscriptAny, listSubscriptAny.idxArm, h, asSsizeIndexError, if_pos (And.intro h1 h2)]
    generalize (if n < 0 then n + (o'.items.length : Int) else n) = k at b1 b2 hout ⊢
    have hv : validIndex k o'.items.length = false := by
      rw [validIndex_ssize k _ b1 b2 (by omega) hl]; simpa using hout
    simp only [listItem, hv, Bool.not_false, if_true]
  · simp only [listSubscriptAny, h]
  · simp only [listSubscriptAny, h]

/-! ## `l[item] = v`, `del l[item]` -/

/-- `l[item] = v` and `del l[item]`, `list_ass_subscript_lock_held` (listobject.c:3752-3916), outside
the slice arm:

* an object with `__index__` runs it first (:3759-3761): if it raises, that exception, with the list
  as `__index__` left it; if its value does not fit `Py_ssize_t`, `IndexError("cannot fit '<type>'
  into an index-sized integer")`; otherwise the size is read after it ran (:3762-3763) and
  `list_ass_item_lock_held` (:3764, :1159-1179) acts on the list as it is then: with `k = n` (or
  `n + len` for a negative `n`) in range, `l[item] = v` replaces item `k` and keeps the array, and
  `del l[item]` removes item `k` and never fails; out of range,
  `IndexError("list assignment index out of range")`;
* an `int` (a subclass too) is the same with no code run;
* anything that is neither an index nor a slice is `TypeError("list indices must be integers or
  slices, not <type>")` (:3910-3914), the list unchanged.

Hypothesis: the list `__index__` leaves is well formed (`LObj.WF`, type invariant). `<type>` is cut
as in `SubscriptDispatch`. -/
def AssSubscriptArms : Prop :=
  ∀ (α : Type) (o : LObj α) (tp : String) (f : LObj α → Py Int × LObj α) (value : Option (α × SeqView α)),
    (∀ e o', f o = (.error e, o') → listAssSubscriptAny o (.index tp f) value = (o', some e)) ∧
    (∀ n o', f o = (.ok n, o') → o'.WF →
      (¬ (ssizeMin ≤ n ∧ n ≤ ssizeMax) → listAssSubscriptAny o (.index tp f) value =
        (o', some (.indexError s!"cannot fit '{trunc200 tp}' into an index-sized integer"))) ∧
      (ssizeMin ≤ n → n ≤ ssizeMax → -(o'.items.length : Int) ≤ n → n < o'.items.length →
        (∀ x sv, listAssSubscriptAny o (.index tp f) (some (x, sv)) =
          ({ o' with items := o'.items.set (if n < 0 then n + (o'.items.length : Int) else n).toNat x },
            none)) ∧
        (∃ q, listAssSubscriptAny o (.index tp f) none = (q, none) ∧
          q.items = o'.items.eraseIdx (if n < 0 then n + (o'.items.length : Int) else n).toNat ∧ q.WF)) ∧
      (ssizeMin ≤ n → n ≤ ssizeMax → ¬ (-(o'.items.length : Int) ≤ n ∧ n < o'.items.length) →
        listAssSubscriptAny o (.index tp f) value =
          (o', some (.indexError "list assignment index out of range")))) ∧
    (∀ n, listAssSubscriptAny o (.int n tp) value =
      listAssSubscriptAny o (.index tp (fun p => (.ok n, p))) value) ∧
    listAssSubscriptAny o (.other tp) value =
      (o, some (.typeError s!"list indices must be integers or slices, not {trunc200 tp}"))

theorem wf_len (o : LObj α) (hw : o.WF) : (o.items.length : Int) ≤ ssizeMax := by
  have := hw.covers; have := hw.bytes; have : ssizeMax / 8 ≤ ssizeMax := by decide
  omega

theorem assSubscriptArms_proven : AssSubscriptArms := by
  intro α o tp f value
  refine ⟨fun e o' h => ?_, fun n o' h hw => ⟨fun hn => ?_, fun h1 h2 h3 h4 => ?_, fun h1 h2 h3 => ?_⟩,
    fun n => rfl, rfl⟩
  · simp only [listAssSubscriptAny, listAssSubscriptAny.idxArm, h]
  · simp only [listAssSubscriptAny, listAssSubscriptAny.idxArm, h, asSsizeIndexError, if_neg hn]
  · have hl := wf_len o' hw
    obtain ⟨b1, b2, b3⟩ := idx_bounds n o'.items.length h1 h2 (by omega) hl
    have hin := b3.mpr ⟨h3, h4⟩
    refine ⟨fun x sv => ?_, ?_⟩
    · simp only [listAssSubscriptAny, listAssSubscriptAny.idxArm, h, asSsizeIndexError,
        if_pos (And.intro h1 h2), Option.map]
      generalize (if n < 0 then n + (o'.items.length : Int) else n) = k at b1 b2 hin ⊢
      rw [((listAssItem_spec o' k x hw).1 hin.1 hin.2).1]
      rfl
    · simp only [listAssSubscriptAny, listAssSubscriptAny.idxArm, h, asSsizeIndexError,
        if_pos (And.intro h1 h2), Option.map]
      generalize (if n < 0 then n + (o'.items.length : Int) else n) = k at b1 b2 hin ⊢
      obtain ⟨q, q1, q2, q3⟩ :=
        ((listAssItem_spec o' k (o'.items[k.toNat]'(by omega)) hw).1 hin.1 hin.2).2
      exact ⟨q, by rw [q1]; rfl, q2, q3⟩
  · have hl := wf_len o' hw
    obtain ⟨b1, b2, b3⟩ := idx_bounds n o'.items.length h1 h2 (by omega) hl
    have hout : ¬ (0 ≤ (if n < 0 then n + (o'.items.length : Int) else n) ∧
        (if n < 0 then n + (o'.items.length : Int) else n) < o'.items.length) := fun hh => h3 (b3.mp hh)
    simp only [listAssSubscriptAny, listAssSubscriptAny.idxArm, h, asSsizeIndexError,
      if_pos (And.intro h1 h2)]
    generalize (if n < 0 then n + (o'.items.length : Int) else n) = k at b1 b2 hout ⊢
    have hv : validIndex k o'.items.length = false := by
      rw [validIndex_ssize k _ b1 b2 (by omega) hl]; simpa using hout
    simp only [listAssItem, hv, Bool.not_false, if_true, liftRes]

/-- The slice arm's refusals (listobject.c:3766-3909), before anything is changed: a zero step is
`ValueError("slice step cannot be zero")` (`PySlice_Unpack`, :3769) whatever the value; a value
`PySequence_Fast` refuses is `TypeError("must assign iterable to extended slice")` (:3846-3856),
for every slice, step 1 included; and an extended slice (step other than 1) given a sequence of the
wrong length is `ValueError("attempt to assign sequence of size <len(t)> to extended slice of size
<L>")` (:3867-3876) with `L = len(range(*s.indices(len(l))))`. Hypothesis: the list has at most
`PY_SSIZE_T_MAX` items (type invariant). -/
def AssSliceErrors : Prop :=
  ∀ (α : Type) (o : LObj α) (s : RangeSlice.Slice) (x : α) (t : List α), (o.items.length : Int) ≤ ssizeMax →
    (s.step = some 0 → ∀ value, listAssSubscriptAny o (.slice s) value =
      (o, some (.valueError "slice step cannot be zero"))) ∧
    (s.step ≠ some 0 → listAssSubscriptAny o (.slice s) (some (x, .notIterable)) =
      (o, some (.typeError "must assign iterable to extended slice"))) ∧
    (∀ a b c, RangeSlice.sliceIndices s o.items.length = .ok (a, b, c) → c ≠ 1 →
      (t.length : Int) ≠ RangeSlice.computeRangeLengthSlow a b c →
      listAssSubscriptAny o (.slice s) (some (x, .seq t)) =
        (o, some (.valueError s!"attempt to assign sequence of size {t.length} to extended slice of size {RangeSlice.computeRangeLengthSlow a b c}")))

theorem assSliceErrors_proven : AssSliceErrors := by
  intro α o s x t hl
  refine ⟨fun h0 value => ?_, fun h0 => ?_, fun a b c hsi hc ht => ?_⟩
  · obtain ⟨st, sp, ss⟩ := s
    simp only at h0; subst h0
    rcases value with _ | ⟨x, _ | _ | _ | _⟩ <;> rfl
  · obtain ⟨st, sp, ss⟩ := s
    have hu : ∃ r, RangeSlice.sliceUnpack ⟨st, sp, ss⟩ = .ok r := by
      cases ss with
      | none => exact ⟨_, rfl⟩
      | some c =>
        simp only [ne_eq, Option.some.injEq] at h0
        unfold RangeSlice.sliceUnpack
        simp only [bind, Except.bind, pure, Except.pure]
        have : RangeSlice.clampSsize c ≠ 0 := by
          unfold RangeSlice.clampSsize ssizeMin ssizeMax; split <;> (try split) <;> omega
        rw [if_neg this]
        exact ⟨_, rfl⟩
    obtain ⟨r, hr⟩ := hu
    simp only [listAssSubscriptAny, listAssSubscript, hr, bind, Except.bind, liftRes]
  · have h0 : s.step ≠ some 0 := by
      intro h0
      obtain ⟨st, sp, ss⟩ := s
      simp only at h0; subst h0
      unfold RangeSlice.sliceIndices at hsi
      rw [if_neg (by omega)] at hsi
      simp [RangeSlice.getLongIndices, bind, Except.bind] at hsi
    obtain ⟨a', b', c', L, st, sp, c'', hsi', -, -, hLdef, hsu, hadj, h1, -, -, -, -⟩ :=
      PyLean.Sequences.adjust_spec s o.items.length (by omega) hl h0
    rw [hsi] at hsi'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hsi'
    obtain ⟨rfl, rfl, rfl⟩ := hsi'
    have hc'' : ¬ c'' = 1 := fun h => hc (h1.mp h)
    rw [← hLdef] at ht ⊢
    simp only [listAssSubscriptAny, listAssSubscript, hsu, bind, Except.bind,
      listAssSubscript.assSeq, adjustSliceIndexes, hadj, if_neg hc'', if_pos ht, liftRes]

/-- `l[s] = it` for an iterable `it` that is neither the list nor an exact list or tuple, which
`PySequence_Fast` (listobject.c:3851) turns into a list by iterating it (`PySequence_List`): that is
user code, which may raise or change the list. The slice is unpacked first, so a zero step raises
before `it` is iterated (`AssSliceErrors`); an exception from the iteration is the result, with the
list as the iteration left it; otherwise the store runs on that list, its size read after the
iteration (`adjust_slice_indexes`, :3858), exactly as a store of those items from a list. -/
def AssSliceIter : Prop :=
  ∀ (α : Type) (o : LObj α) (s : RangeSlice.Slice) (x : α) (f : LObj α → Py (List α) × LObj α),
    s.step ≠ some 0 →
    (∀ e o', f o = (.error e, o') → listAssSubscriptAny o (.slice s) (some (x, .iter f)) = (o', some e)) ∧
    (∀ items o', f o = (.ok items, o') →
      listAssSubscriptAny o (.slice s) (some (x, .iter f)) =
        listAssSubscriptAny o' (.slice s) (some (x, .seq items)))

theorem assSliceIter_proven : AssSliceIter := by
  intro α o s x f h0
  have hu : ∃ r, RangeSlice.sliceUnpack s = .ok r := by
    obtain ⟨st, sp, ss⟩ := s
    cases ss with
    | none => exact ⟨_, rfl⟩
    | some c =>
      simp only [ne_eq, Option.some.injEq] at h0
      unfold RangeSlice.sliceUnpack
      simp only [bind, Except.bind, pure, Except.pure]
      have : RangeSlice.clampSsize c ≠ 0 := by
        unfold RangeSlice.clampSsize ssizeMin ssizeMax; split <;> (try split) <;> omega
      rw [if_neg this]
      exact ⟨_, rfl⟩
  obtain ⟨r, hr⟩ := hu
  refine ⟨fun e o' h => ?_, fun items o' h => ?_⟩
  · simp only [listAssSubscriptAny, hr, h]
  · simp only [listAssSubscriptAny, hr, h]

/-! ## Iterator `__reduce__` -/

/-- `it.__reduce__()` of a list iterator (`listiter_reduce`, listobject.c:4126-4130) and of a reverse
list iterator (`listreviter_reduce`, :4278-4282), through `listiter_reduce_general` (:4303-4335), for
every builtins lookup, including one that runs code (a key whose `__eq__` changes the iterator or the
list, as in gh-101765) or fails:

* the forward iterator looks up `iter` and the reverse one `reversed` (:4314, :4321), and a
  successful result names what the lookup returned;
* the index and the list are read after the lookup (:4316, :4323): a live index gives
  `(callable, (seq,), index)`, a negative one `(callable, ([],))` (:4328-4334); so a lookup that
  exhausts the iterator gives the empty form, and one that appends to the list shows the longer list;
* a failed lookup is the result, with the state it left (`AttributeError(name)` for a missing name,
  Python/ceval.c:2651-2658). -/
def ReduceOrder : Prop :=
  ∀ (α β : Type) (g : String → ListIter × List α → Py β × (ListIter × List α)) (st : ListIter × List α),
    (∀ c st', g "iter" st = (.ok c, st') →
      listIterReduceFwd g st =
        (.ok (if st'.1.index ≥ 0 then .live c st'.2 st'.1.index else .empty c), st')) ∧
    (∀ c st', g "reversed" st = (.ok c, st') →
      listRevIterReduce g st =
        (.ok (if st'.1.index ≥ 0 then .live c st'.2 st'.1.index else .empty c), st')) ∧
    (∀ e st', g "iter" st = (.error e, st') → listIterReduceFwd g st = (.error e, st')) ∧
    (∀ e st', g "reversed" st = (.error e, st') → listRevIterReduce g st = (.error e, st')) ∧
    (∀ c l', g "iter" st = (.ok c, (⟨-1, false⟩, l')) →
      listIterReduceFwd g st = (.ok (.empty c), (⟨-1, false⟩, l'))) ∧
    (∀ c l', g "reversed" st = (.ok c, (⟨-1, false⟩, l')) →
      listRevIterReduce g st = (.ok (.empty c), (⟨-1, false⟩, l')))

theorem reduceOrder_proven : ReduceOrder := by
  intro α β g st
  refine ⟨fun c st' h => ?_, fun c st' h => ?_, fun e st' h => ?_, fun e st' h => ?_,
    fun c l' h => ?_, fun c l' h => ?_⟩
  · simp only [listIterReduceFwd, listIterReduceGen, if_true, h]
    split <;> rfl
  · simp only [listRevIterReduce, listIterReduceGen, Bool.false_eq_true, if_false, h]
    split <;> rfl
  · simp only [listIterReduceFwd, listIterReduceGen, if_true, h]
  · simp only [listRevIterReduce, listIterReduceGen, Bool.false_eq_true, if_false, h]
  · simp only [listIterReduceFwd, listIterReduceGen, if_true, h]
    rfl
  · simp only [listRevIterReduce, listIterReduceGen, Bool.false_eq_true, if_false, h]
    rfl

end PyLean.BytesObj.Seq
