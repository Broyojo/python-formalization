import PyLean.BytesObj.Seq.ListRows2
import PyLean.BytesObj.Seq.ReprProps

/-!
User code inside `x in l` and `repr(l)` (Objects/listobject.c, CPython 3.15.2): the comparison or
the item's `__repr__` may change the list, and both loops reread the list after each call.
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α : Type}

theorem getItemRef_nat (l : List α) (i : Nat) (hl : (l.length : Int) ≤ ssizeMax) (hi : (i : Int) ≤ ssizeMax) :
    listGetItemRef l (i : Int) = l[i]? := by
  have h63 : (2 : Int) ^ 63 = 9223372036854775808 := by decide
  have hM : ssizeMax = 9223372036854775807 := by decide
  unfold listGetItemRef
  rw [validIndex_eq (i : Int) l.length (by omega) (by omega) (by omega) hl]
  by_cases h : i < l.length
  · rw [if_pos (by simp only [decide_eq_true_eq]; omega), slot_nat]
  · rw [if_neg (by simp only [decide_eq_true_eq]; omega)]
    exact (List.getElem?_eq_none (by omega)).symm

/-! ## `x in l` -/

/-- `x in l`, `list_contains` (listobject.c:676-693), for every comparison, including one that changes
the list. Each pass reads the item through `list_get_item_ref` on the list as it is now (:680), so

* the search stops when the index is past the current end (:681-684);
* after a false comparison it goes on at the next index of the list the comparison left (:685-690);
* a true or raising comparison ends it, with the list as the comparison left it;
* so if every comparison is false and removes the last item, as an `__eq__` that pops does, only the
  first `ceil(n/2)` items are compared, `x in l` is `False`, and the first `n // 2` items remain. A
  loop over a copy of the items would compare all `n` and leave nothing.

Hypothesis: the list's length fits `Py_ssize_t` (type invariant). -/
def ContainsReentrant : Prop :=
  ∀ (α : Type) (cmp : Cmp α) (el : α),
    (∀ (f : Nat) (i : Int) (p : LObj α), listGetItemRef p.items i = none →
      containsLoop cmp el (f + 1) i p = (.ok false, p)) ∧
    (∀ (f : Nat) (i : Int) (p p' : LObj α) (x : α), listGetItemRef p.items i = some x →
      cmp p x el = (.ok false, p') → containsLoop cmp el (f + 1) i p = containsLoop cmp el f (i + 1) p') ∧
    (∀ (f : Nat) (i : Int) (p p' : LObj α) (x : α) (r : Py Bool), listGetItemRef p.items i = some x →
      cmp p x el = (r, p') → r ≠ .ok false → containsLoop cmp el (f + 1) i p = (r, p')) ∧
    ((∀ (p : LObj α) (x : α), (cmp p x el).1 = .ok false ∧ ((cmp p x el).2).items = p.items.dropLast) →
      ∀ (o : LObj α) (fuel : Nat), (o.items.length : Int) ≤ ssizeMax → o.items.length < fuel →
        (listContains cmp fuel o el).1 = .ok false ∧
        ((listContains cmp fuel o el).2).items = o.items.take (o.items.length / 2))

theorem containsLoop_pop (cmp : Cmp α) (el : α)
    (hc : ∀ (p : LObj α) (x : α), (cmp p x el).1 = .ok false ∧ ((cmp p x el).2).items = p.items.dropLast) :
    ∀ (f : Nat) (i : Nat) (p : LObj α), (p.items.length : Int) ≤ ssizeMax → (i : Int) ≤ ssizeMax →
      p.items.length - i < f →
      (containsLoop cmp el f (i : Int) p).1 = .ok false ∧
      ((containsLoop cmp el f (i : Int) p).2).items =
        p.items.take (p.items.length - (p.items.length - i + 1) / 2) := by
  intro f
  induction f with
  | zero => intro i p _ _ h; omega
  | succ f ih =>
    intro i p hl hi h
    by_cases hlt : i < p.items.length
    · have hget : listGetItemRef p.items (i : Int) = some p.items[i] := by
        rw [getItemRef_nat p.items i hl hi]; exact List.getElem?_eq_getElem hlt
      obtain ⟨hr, hp⟩ := hc p p.items[i]
      have hcmp : cmp p p.items[i] el = (.ok false, (cmp p p.items[i] el).2) := by
        rw [← hr]
      have hstep : containsLoop cmp el (f + 1) (i : Int) p =
          containsLoop cmp el f ((i : Int) + 1) (cmp p p.items[i] el).2 := by
        simp only [containsLoop, hget]
        rw [hcmp]
      generalize hq : (cmp p p.items[i] el).2 = q at hstep hp
      have hql : q.items.length = p.items.length - 1 := by rw [hp, List.length_dropLast]
      obtain ⟨r1, r2⟩ := ih (i + 1) q (by rw [hql]; omega) (by omega) (by rw [hql]; omega)
      rw [show ((i + 1 : Nat) : Int) = (i : Int) + 1 by omega] at r1 r2
      rw [hstep]
      refine ⟨r1, ?_⟩
      rw [r2, hp, List.dropLast_eq_take, List.take_take]
      congr 1
      simp only [List.length_take]
      omega
    · have hget : listGetItemRef p.items (i : Int) = none := by
        rw [getItemRef_nat p.items i hl hi]; exact List.getElem?_eq_none (by omega)
      simp only [containsLoop, hget]
      refine ⟨by first | trivial | rfl, ?_⟩
      show p.items = _
      have : p.items.length - (p.items.length - i + 1) / 2 = p.items.length := by omega
      rw [this, List.take_length]

theorem containsReentrant_proven : ContainsReentrant := by
  intro α cmp el
  refine ⟨fun f i p h => by simp only [containsLoop, h], fun f i p p' x h1 h2 => by simp only [containsLoop, h1, h2],
    fun f i p p' x r h1 h2 h3 => ?_, fun hc o fuel hl hf => ?_⟩
  · simp only [containsLoop, h1, h2]
    split
    · rename_i o' heq
      simp only [Prod.mk.injEq] at heq
      exact absurd heq.1 h3
    · rfl
  · obtain ⟨r1, r2⟩ := containsLoop_pop cmp el hc fuel 0 o hl (by decide) (by omega)
    refine ⟨r1, ?_⟩
    unfold listContains
    rw [show ((0 : Nat) : Int) = 0 from rfl] at r2
    rw [r2]
    congr 1
    omega

/-! ## `repr(l)` -/

/-- `repr(l)`, `list_repr_impl` (listobject.c:601-654), when each item's `__repr__` changes the list.
The comment at :621-622 says the loop must "refetch the list size on each iteration" because
`repr(item)` "may mutate the list"; so if every item's repr succeeds and removes the last item, the
result is the repr of the first `ceil(n/2)` items, and the first `n // 2` items remain. A loop over a
snapshot would print all `n`. Separately, a list already being printed, found again through
`Py_ReprEnter` (:604-607), prints as `[...]`, and a tuple as `(...)`. Hypothesis: the item reprs succeed
(`g` is what they print); the length fits `Py_ssize_t`. -/
def ReprReentrant : Prop :=
  (∀ (α : Type) (elem : LObj α → α → Py String × LObj α) (g : α → String) (o : LObj α) (fuel : Nat),
    (∀ (p : LObj α) (x : α), (elem p x).1 = .ok (g x) ∧ ((elem p x).2).items = p.items.dropLast) →
    o.items.length < fuel →
    (listRepr elem fuel false o).1 =
      .ok (if o.items.length = 0 then "[]" else
        "[" ++ commaJoin ((o.items.take ((o.items.length + 1) / 2)).map g) ++ "]") ∧
    ((listRepr elem fuel false o).2).items = o.items.take (o.items.length / 2)) ∧
  (∀ (h : RHeap) (fuel : Nat) (stack : List Nat) (id : Nat) (cell : RCell),
    h[id]? = some cell → cell.items ≠ [] → id ∈ stack →
    reprObj h (fuel + 1) stack (.ref id) = .ok (if cell.isList then "[...]" else "(...)"))

/-- The loop over a list whose reprs each drop the last item prints what the loop over a fixed list
with the same items at the indices it reaches prints. -/
theorem listReprLoop_pop (elem : LObj α → α → Py String × LObj α) (g : α → String)
    (he : ∀ (p : LObj α) (x : α), (elem p x).1 = .ok (g x) ∧ ((elem p x).2).items = p.items.dropLast) :
    ∀ (f : Nat) (i : Nat) (acc : String) (p q : LObj α),
      p.items.length - i < f →
      q.items.length = i + (p.items.length - i + 1) / 2 →
      (∀ k, i ≤ k → k < q.items.length → q.items[k]? = p.items[k]?) →
      (listReprLoop elem f i acc p).1 = (listReprLoop (fun r x => (.ok (g x), r)) f i acc q).1 ∧
      ((listReprLoop elem f i acc p).2).items = p.items.take (p.items.length - (p.items.length - i + 1) / 2) := by
  intro f
  induction f with
  | zero => intro i acc p q h; omega
  | succ f ih =>
    intro i acc p q h hq hagree
    by_cases hlt : i < p.items.length
    · have hqi : i < q.items.length := by omega
      have hx : q.items[i] = p.items[i] := by
        have := hagree i (by omega) hqi
        rw [List.getElem?_eq_getElem hqi, List.getElem?_eq_getElem hlt] at this
        exact Option.some.inj this
      obtain ⟨hr, hp⟩ := he p p.items[i]
      have hel : elem p p.items[i] = (.ok (g p.items[i]), (elem p p.items[i]).2) := by rw [← hr]
      have hstepL : listReprLoop elem (f + 1) i acc p =
          listReprLoop elem f (i + 1) ((if i > 0 then acc ++ ", " else acc) ++ g p.items[i])
            (elem p p.items[i]).2 := by
        rw [listReprLoop, dif_pos hlt]
        simp only
        rw [hel]
      have hstepR : listReprLoop (fun r x => (.ok (g x), r)) (f + 1) i acc q =
          listReprLoop (fun r x => (.ok (g x), r)) f (i + 1)
            ((if i > 0 then acc ++ ", " else acc) ++ g p.items[i]) q := by
        rw [listReprLoop, dif_pos hqi]
        simp only
        rw [hx]
      generalize hp' : (elem p p.items[i]).2 = p' at hstepL hp
      have hpl : p'.items.length = p.items.length - 1 := by rw [hp, List.length_dropLast]
      rw [hstepL, hstepR]
      obtain ⟨r1, r2⟩ := ih (i + 1) _ p' q (by omega) (by omega) (fun k hk1 hk2 => by
        rw [hagree k (by omega) hk2, hp, List.dropLast_eq_take, List.getElem?_take]
        rw [if_pos (by omega)])
      refine ⟨r1, ?_⟩
      rw [r2, hp, List.dropLast_eq_take, List.take_take]
      congr 1
      simp only [List.length_take]
      omega
    · have hqi : ¬ i < q.items.length := by omega
      rw [listReprLoop, dif_neg hlt, listReprLoop, dif_neg hqi]
      refine ⟨rfl, ?_⟩
      show p.items = _
      have : p.items.length - (p.items.length - i + 1) / 2 = p.items.length := by omega
      rw [this, List.take_length]

theorem reprReentrant_proven : ReprReentrant := by
  refine ⟨fun α elem g o fuel he hf => ?_, fun h fuel stack id cell hc hne hin => ?_⟩
  · by_cases h0 : o.items.length = 0
    · simp [listRepr, h0, List.length_eq_zero_iff.mp h0]
    · let q : LObj α := { items := o.items.take ((o.items.length + 1) / 2) }
      have hql : q.items.length = (o.items.length + 1) / 2 := by
        simp only [q, List.length_take]; omega
      obtain ⟨r1, r2⟩ := listReprLoop_pop elem g he fuel 0 "[" o q (by omega) (by rw [hql]; omega)
        (fun k _ hk => by
          simp only [q, List.getElem?_take]
          rw [if_pos (by rw [hql] at hk; omega)])
      have hshape := (reprShape_proven α (fun x => .ok (g x)) g q fuel (fun _ _ => rfl) (by omega)).2
      have hq0 : ¬ q.items.length = 0 := by omega
      rw [if_neg hq0] at hshape
      simp only [listRepr, h0, if_false, Bool.false_eq_true]
      refine ⟨?_, ?_⟩
      · rw [r1]
        simp only [listRepr, hq0, if_false, Bool.false_eq_true] at hshape
        exact hshape
      · rw [r2]
        congr 1
        omega
  · unfold reprObj
    simp only [hc]
    have hs : stack.contains id = true := by simpa using hin
    have hl : cell.items.length ≠ 0 := fun h => hne (List.length_eq_zero_iff.mp h)
    cases hk : cell.isList
    · simp [tupleRepr, hs, hin, hl]
    · simp [listRepr, hs, hin, hl]

/-! ## Slice assignment that empties the list; `extend` into an array that has room -/

/-- `list_ass_slice_lock_held` frees the array whenever the result is empty (`list_clear`, :1006-1010),
and `list_extend_fast` into a list that has an array keeps it when there is room and the array is at
most half empty (`list_resize`'s fast path), rather than reallocating exactly. -/
def ListAssSliceClear : Prop :=
  ∀ (α : Type) (o o' : LObj α) (lo hi : Int) (v : Option (List α)) (s : List α), o.WF →
    (listAssSlice o lo hi v = .ok o' → o'.items = [] → o' = LObj.empty) ∧
    (o.hasItems = true → s ≠ [] → ((o.items.length + s.length : Nat) : Int) ≤ o.allocated →
      (o.allocated / 2 ≤ ((o.items.length + s.length : Nat) : Int) ∨ o.allocated ≤ 32) →
      listExtendFast o s = .ok { items := o.items ++ s, allocated := o.allocated, hasItems := true })

theorem listAssSliceClear_proven : ListAssSliceClear := by
  intro α o o' lo hi v s hw
  constructor
  · intro h he
    obtain ⟨L, H, h0, h1, h2, -, -, heq⟩ := listAssSlice_shape o lo hi v
    rw [heq] at h
    have hcov := hw.covers
    split at h
    · simp only [Except.ok.injEq] at h
      rw [← h, listClear_empty o hw]
    · split at h
      · rename_i hz hd
        simp only [Except.ok.injEq] at h
        have hl := congrArg List.length he
        rw [← h] at hl
        simp only [List.length_append, List.length_take, List.length_drop, List.length_nil] at hl
        omega
      · rename_i hz hd
        have hi := (resizeTo_wf hw h).2
        have hl := congrArg List.length he
        rw [hi] at hl
        simp only [List.length_append, List.length_take, List.length_drop, List.length_nil] at hl
        omega
  · intro hh hne hroom hhalf
    have hs0 : s.length ≠ 0 := fun h => hne (List.length_eq_zero_iff.mp h)
    have hfast := (listResizeExact_proven o.allocated o.hasItems o.items.length
      ((o.items ++ s).length) hw.nonneg (by omega)).1 (by simpa using hroom) (by simpa using hhalf)
    rw [hh] at hfast
    unfold listExtendFast resizeTo
    rw [if_neg hs0]
    simp only [hh, Bool.not_true, Bool.false_eq_true, if_false]
    rw [hfast]

end PyLean.BytesObj.Seq
