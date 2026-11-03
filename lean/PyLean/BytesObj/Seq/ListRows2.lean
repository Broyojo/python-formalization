import PyLean.BytesObj.Seq.ListRows
import PyLean.Sequences.DequeRepeat

/-!
`l * n` and `l *= n`, the C API entry points, `PyList_GetSlice`, `PyList_New`,
`list_new_prealloc`, `_PyList_Concat` and `clear` of Objects/listobject.c (CPython 3.15.2), by
outcome, success forced.
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α : Type}

/-! ## `l * n` and `l *= n` -/

/-- `l *= n` (`list_inplace_repeat_lock_held`, listobject.c:1101-1140, and its wrapper
`list_inplace_repeat`, :1142-1156) for every list with its invariant and every `n`:

* `l *= 1` and `[] *= n` leave the list, its array included, alone (:1105-1107);
* `l *= n` for `n < 1` clears it, freeing the array (:1109-1112);
* otherwise the result is `n` copies of the items when that is at most `PY_SSIZE_T_MAX / 8 - 3`
  items, and `MemoryError` past `PY_SSIZE_T_MAX / 8`: either the explicit test (:1114-1117) or
  `list_resize`'s overflow test fires;
* the contents model `Sequences.listIRepeat`, which takes an exactly allocated list, is this
  model whenever the output is larger than the allocation, as it is for every list whose
  array does not already hold `len * n` slots;
* the contents model `Sequences.listRepeat` of `l * n` is `list_repeat_lock_held` (:840-880),
  for every list and count. -/
def ListInplaceRepeatSpec : Prop :=
  ∀ (α : Type) (o : LObj α) (n : Int), o.WF →
    ((o.items.length = 0 ∨ n = 1) → listInplaceRepeat o n = .ok o) ∧
    (o.items.length ≠ 0 → n < 1 → listInplaceRepeat o n = .ok LObj.empty) ∧
    (1 < n → 0 < o.items.length → (o.items.length : Int) * n ≤ ssizeMax / 8 - 3 →
      ∃ o', listInplaceRepeat o n = .ok o' ∧ o'.items = (List.replicate n.toNat o.items).flatten ∧ o'.WF) ∧
    (1 < n → 0 < o.items.length → ssizeMax / 8 < (o.items.length : Int) * n →
      listInplaceRepeat o n = .error memoryError) ∧
    ((o.items.length = 0 ∨ n ≤ 1 ∨ o.allocated < (o.items.length : Int) * n) →
      (listIMul o n).map LObj.items = PyLean.Sequences.listIRepeat o.items n) ∧
    (listMul o.items n).map LObj.items = PyLean.Sequences.listRepeat o.items n

theorem newAllocated_eq (size n : Int) : newAllocated size n = PyLean.Sequences.listNewAllocated size n := rfl

theorem listClear_empty (o : LObj α) (hw : o.WF) : listClear o = LObj.empty := by
  unfold listClear
  cases hh : o.hasItems with
  | true => rfl
  | false =>
    obtain ⟨hi, ha⟩ := wf_noitems hw hh
    simp only [Bool.not_false, if_true]
    cases o
    simp_all [LObj.empty]

theorem listInplaceRepeatSpec_proven : ListInplaceRepeatSpec := by
  intro α o n hw
  have h8 : ssizeMax / 8 = 1152921504606846975 := by decide
  have hM : ssizeMax = 9223372036854775807 := by decide
  have hcov := hw.covers
  have hby := hw.bytes
  have hdiv : ∀ (h : 0 < n), ((o.items.length : Int) > ssizeMax / n ↔ ssizeMax < (o.items.length : Int) * n) := by
    intro h
    constructor
    · intro hg; apply Int.not_le.mp; intro hle
      have := (Int.le_ediv_iff_mul_le h).mpr hle; omega
    · intro hg; apply Int.not_le.mp; intro hle
      have := (Int.le_ediv_iff_mul_le h).mp hle; omega
  have hgrow : 1 < n → 0 < o.items.length → (o.items.length : Int) < (o.items.length : Int) * n ∧
      2 * (o.items.length : Int) ≤ (o.items.length : Int) * n := by
    intro h1 h0
    have := Int.mul_le_mul_of_nonneg_left (show (2 : Int) ≤ n by omega) (show (0 : Int) ≤ o.items.length by omega)
    omega
  -- the slow path of `list_resize` for a growing list
  have hres : 1 < n → 0 < o.items.length → o.allocated < (o.items.length : Int) * n →
      ¬ ((o.items.length : Int) > ssizeMax / n) →
      listInplaceRepeat o n =
        (if newAllocated o.items.length ((o.items.length : Int) * n) ≤ ssizeMax / 8 then
          .ok { items := (List.replicate n.toNat o.items).flatten,
                allocated := newAllocated o.items.length ((o.items.length : Int) * n), hasItems := true }
         else .error memoryError) := by
    intro h1 h0 ha hA
    have hR := listResizeExact_proven o.allocated o.hasItems o.items.length ((o.items.length : Int) * n)
      hw.nonneg (by omega)
    unfold listInplaceRepeat
    simp only
    rw [if_neg (by omega), if_neg (by omega), if_neg hA]
    by_cases hle : newAllocated o.items.length ((o.items.length : Int) * n) ≤ ssizeMax / 8
    · rw [if_pos hle, hR.2.2.1 ha hle]
    · rw [if_neg hle, hR.2.2.2.1 ha (by omega)]
  have hg := fun (h1 : 1 < n) (h0 : 0 < o.items.length) =>
    PyLean.Sequences.listNewAllocated_grow (o.items.length : Int) ((o.items.length : Int) * n) (by omega)
      (hgrow h1 h0).2
  refine ⟨fun h => ?_, fun h0 h1 => ?_, fun h1 h0 hb => ?_, fun h1 h0 hb => ?_, fun hc => ?_, ?_⟩
  · unfold listInplaceRepeat; rw [if_pos (by omega)]
  · unfold listInplaceRepeat
    rw [if_neg (by omega), if_pos h1, listClear_empty o hw]
  · have hA : ¬ ((o.items.length : Int) > ssizeMax / n) := fun hA => by
      have := (hdiv (by omega)).mp hA; omega
    have hna : newAllocated o.items.length ((o.items.length : Int) * n) ≤ ssizeMax / 8 := by
      rw [newAllocated_eq]; exact (hg h1 h0).mpr hb
    have hR := listResizeExact_proven o.allocated o.hasItems o.items.length ((o.items.length : Int) * n)
      hw.nonneg (by omega)
    have hok : ∃ r, listResize o.allocated o.hasItems o.items.length ((o.items.length : Int) * n) = .ok r := by
      by_cases ha : o.allocated < (o.items.length : Int) * n
      · exact ⟨_, hR.2.2.1 ha hna⟩
      · exact hR.2.2.2.2.2.1 (by omega)
    obtain ⟨⟨a, b⟩, hr⟩ := hok
    obtain ⟨g1, g2, g3, g4⟩ := listResize_spec _ _ _ _ a b (by omega) hw.nonneg hw.bytes hw.array hr
    unfold listInplaceRepeat
    simp only
    rw [if_neg (by omega), if_neg (by omega), if_neg hA, hr]
    refine ⟨_, rfl, rfl, ⟨g2, ?_, g4, g3⟩⟩
    show (((List.replicate n.toNat o.items).flatten.length : Nat) : Int) ≤ a
    rw [length_repeat]
    have hcast : ((n.toNat * o.items.length : Nat) : Int) = (o.items.length : Int) * n := by
      rw [Int.natCast_mul, Int.toNat_of_nonneg (by omega), Int.mul_comm]
    omega
  · by_cases hA : (o.items.length : Int) > ssizeMax / n
    · unfold listInplaceRepeat
      rw [if_neg (by omega), if_neg (by omega), if_pos hA]
    · have ha : o.allocated < (o.items.length : Int) * n := by omega
      have hge := newAllocated_ge o.items.length ((o.items.length : Int) * n) (by omega)
      rw [hres h1 h0 ha hA, if_neg (by omega)]
  · unfold listIMul PyLean.Sequences.listIRepeat
    cases hrc : PyLean.Sequences.repeatCount n with
    | error e => rfl
    | ok m =>
      have hm : m = n := by
        unfold PyLean.Sequences.repeatCount PyLean.Sequences.asSsizeExc at hrc
        split at hrc
        · simp only [Except.ok.injEq] at hrc; exact hrc.symm
        · simp at hrc
      subst hm
      simp only [bind, Except.bind, pure, Except.pure]
      by_cases hc1 : (o.items.length : Int) = 0 ∨ m = 1
      · rw [if_pos hc1]
        unfold listInplaceRepeat
        rw [if_pos (by omega)]
        rfl
      rw [if_neg hc1]
      by_cases hc2 : m < 1
      · rw [if_pos hc2]
        unfold listInplaceRepeat
        rw [if_neg (by omega), if_pos hc2]
        show Except.ok (listClear o).items = _
        rw [listClear_items o hw]
      rw [if_neg hc2]
      have h1 : 1 < m := by omega
      have h0 : 0 < o.items.length := by omega
      have ha : o.allocated < (o.items.length : Int) * m := by omega
      by_cases hA : (o.items.length : Int) > ssizeMax / m
      · rw [if_pos hA]
        unfold listInplaceRepeat
        rw [if_neg (by omega), if_neg (by omega), if_pos hA]
        rfl
      rw [if_neg hA, hres h1 h0 ha hA, ← newAllocated_eq]
      by_cases hle : newAllocated o.items.length ((o.items.length : Int) * m) ≤ ssizeMax / 8
      · rw [if_pos hle, if_neg (by omega)]
        rfl
      · rw [if_neg hle, if_pos (by omega)]
        rfl
  · unfold listMul PyLean.Sequences.listRepeat
    cases hrc : PyLean.Sequences.repeatCount n with
    | error e => rfl
    | ok m =>
      simp only [bind, Except.bind, pure, Except.pure]
      unfold listRepeat
      simp only
      by_cases hc1 : (o.items.length : Int) = 0 ∨ m ≤ 0
      · rw [if_pos hc1, if_pos hc1]; rfl
      rw [if_neg hc1, if_neg hc1]
      by_cases hA : (o.items.length : Int) > ssizeMax / m
      · rw [if_pos hA, if_pos hA]; rfl
      rw [if_neg hA, if_neg hA]
      by_cases hB : (o.items.length : Int) * m > ssizeMax / 8
      · rw [if_pos hB, if_pos hB]; rfl
      rw [if_neg hB, if_neg hB]
      show Except.ok (LObj.prealloc _).items = _
      rw [prealloc_items]

/-! ## The C API -/

/-- The list entry points of the C API (Doc/c-api/list.rst), for every argument and every list with
its invariant: each refuses an object that is not a list with `SystemError`
(`PyErr_BadInternalCall`), `PyList_Insert` and `PyList_Append` refuse a `NULL` item the same way,
and on a list each does what the method does:

* `PyList_SetItem` (listobject.c:474-500) refuses a non-list before looking at the index;
* `PyList_Insert` (:530-543) inserts at the clipped position, or raises `MemoryError` when the list
  cannot grow by one;
* `PyList_Append` (:559-571) appends, with the same failure;
* `PyList_SetSlice` (:1091-1099) deletes for `NULL`, which always succeeds, replaces the clipped
  range for a sequence, and raises `TypeError` for an object `PySequence_Fast` refuses;
* `PyList_Clear` (:1570-1581) leaves an empty list with no array;
* `PyList_Extend` (:1559-1567) extends from a sequence, and raises the `TypeError` of
  `PyObject_GetIter` for an object that is not iterable, leaving the list alone. -/
def CApiListOps : Prop :=
  ∀ (α : Type) (o : LObj α) (i j : Int) (v : α) (x : Option α) (av : AssVal α) (arg : ExtArg α)
    (w : List α) (name : String), o.WF →
    pyListSetItem (none : Option (LObj α)) i v = .error systemError ∧
    pyListInsert (none : Option (LObj α)) i x = .error systemError ∧
    pyListInsert (some o) i none = .error systemError ∧
    (listCanGrow o (o.items.length + 1) → ∃ o', pyListInsert (some o) i (some v) = .ok o' ∧
      o'.items = PyLean.Sequences.listIns1 o.items i v) ∧
    (¬ listCanGrow o (o.items.length + 1) → pyListInsert (some o) i (some v) = .error memoryError) ∧
    pyListAppend (none : Option (LObj α)) x = .error systemError ∧
    pyListAppend (some o) none = .error systemError ∧
    (listCanGrow o (o.items.length + 1) → ∃ o', pyListAppend (some o) (some v) = .ok o' ∧
      o'.items = o.items ++ [v]) ∧
    (¬ listCanGrow o (o.items.length + 1) → pyListAppend (some o) (some v) = .error memoryError) ∧
    pyListSetSlice (none : Option (LObj α)) i j av = .error systemError ∧
    pyListSetSlice (some o) i j .notIterable = .error (.typeError "can only assign an iterable") ∧
    (∃ o', pyListSetSlice (some o) i j .del = .ok o' ∧
      o'.items = o.items.take i.toNat ++ o.items.drop (max i.toNat j.toNat)) ∧
    (((o.items.take i.toNat ++ w ++ o.items.drop (max i.toNat j.toNat)).length : Int) ≤ ssizeMax / 16 →
      ∃ o', pyListSetSlice (some o) i j (.seq w) = .ok o' ∧
        o'.items = o.items.take i.toNat ++ w ++ o.items.drop (max i.toNat j.toNat)) ∧
    pyListClear (none : Option (LObj α)) = .error systemError ∧
    pyListClear (some o) = .ok LObj.empty ∧
    (pyListExtend (none : Option (LObj α)) arg).1.2 = some systemError ∧
    (pyListExtend (none : Option (LObj α)) arg).2 = none ∧
    ((o.items.length + w.length : Int) ≤ ssizeMax / 16 → ∃ o',
      pyListExtend (some o) (.fast w) = ((o', none), some ()) ∧ o'.items = o.items ++ w) ∧
    pyListExtend (some o) (.notIterable name) =
      ((o, some (.typeError s!"'{name}' object is not iterable")), some ())

theorem cApiListOps_proven : CApiListOps := by
  intro α o i j v x av arg w name hw
  obtain ⟨a1, a2⟩ := listAppend_spec o v hw
  obtain ⟨i1, i2⟩ := ins1_spec o i v hw
  obtain ⟨e1, -, -⟩ := listExtendFast_spec o w hw
  obtain ⟨d1, d2, d3⟩ := listAssSlice_del o i j hw
  obtain ⟨q1, -⟩ := listAssSlice_spec o i j w hw
  refine ⟨rfl, rfl, rfl, fun h => ?_, i2, rfl, rfl, fun h => ?_, a2, rfl, rfl, ⟨d1, d2, d3.1⟩, fun h => ?_,
    rfl, ?_, rfl, rfl, fun h => ?_, rfl⟩
  · obtain ⟨o', h1, h2, -⟩ := i1 h; exact ⟨o', h1, h2⟩
  · obtain ⟨o', h1, h2, -⟩ := a1 h; exact ⟨o', h1, h2⟩
  · obtain ⟨o', h1, h2, -⟩ := q1 h; exact ⟨o', h1, h2⟩
  · show Except.ok (listClear o) = _
    rw [listClear_empty o hw]
  · obtain ⟨o', h1, h2, -⟩ := e1 h
    refine ⟨o', ?_, h2⟩
    simp only [pyListExtend, listExtend, liftRes, h1]

/-! ## Slices, `PyList_New`, concatenation -/

/-- `PyList_GetSlice`, `PyList_New`, `list_new_prealloc` and `_PyList_Concat`, for every argument:

* `PyList_GetSlice(a, i, j)` (listobject.c:764-788) clips both indices to the list without counting
  a negative one from the end, so it is `a[max(i,0):max(j,0)]`, as `(a.take j).drop i` gives it; the
  copy is exactly allocated (`list_new_prealloc`), and has no array when it is empty;
* `PyList_New(0)` (:261-300) makes a list with no array; a size past `PY_SSIZE_T_MAX / 8` fails in
  `PyMem_Calloc`'s overflow test (Objects/obmalloc.c:1264) with `MemoryError`;
* `list_new_prealloc` (:302-327) allocates exactly the slots asked for, and fails past
  `PY_SSIZE_T_MAX / 8` (Include/pymem.h:63-65);
* `a + b` (`_PyList_Concat`, :822-838) refuses a non-list with the source's `TypeError`, and for a list
  is the items of `a` then `b`, exactly allocated, or `MemoryError` when the total is past
  `PY_SSIZE_T_MAX / 8`. -/
def CApiSliceConcat : Prop :=
  ∀ (α : Type) (l a b items : List α) (i j n : Int) (name : String),
    (pyListGetSlice (some l) i j).map LObj.items = .ok ((l.take j.toNat).drop i.toNat) ∧
    (∀ r, pyListGetSlice (some l) i j = .ok r →
      r.allocated = r.items.length ∧ (r.hasItems = true ↔ r.items ≠ [])) ∧
    pyListNew (0 : Int) = (.ok LObj.empty : Py (LObj (Option α))) ∧
    (ssizeMax / 8 < n → pyListNew n = (.error memoryError : Py (LObj (Option α)))) ∧
    ((items.length : Int) ≤ ssizeMax / 8 →
      listNewPrealloc items = .ok { items := items, allocated := items.length, hasItems := true }) ∧
    (ssizeMax / 8 < (items.length : Int) → listNewPrealloc items = .error memoryError) ∧
    listConcatAny a (.inr name) =
      .error (.typeError s!"can only concatenate list (not \"{name}\") to list") ∧
    ((a.length + b.length : Int) ≤ ssizeMax / 8 → listConcatAny a (.inl b) = .ok (LObj.prealloc (a ++ b))) ∧
    (ssizeMax / 8 < (a.length + b.length : Int) → listConcatAny a (.inl b) = .error memoryError)

theorem prealloc_shape (items : List α) :
    (LObj.prealloc items).allocated = (LObj.prealloc items).items.length ∧
    ((LObj.prealloc items).hasItems = true ↔ (LObj.prealloc items).items ≠ []) := by
  unfold LObj.prealloc
  split
  · rename_i h
    have : items = [] := List.length_eq_zero_iff.mp h
    simp [LObj.empty]
  · rename_i h
    have : items ≠ [] := fun he => h (by simp [he])
    simp [this]

theorem cApiSliceConcat_proven : CApiSliceConcat := by
  intro α l a b items i j n name
  have h8 : ssizeMax / 8 = 1152921504606846975 := by decide
  generalize hL : (if i < 0 then (0 : Int) else if i > (l.length : Int) then (l.length : Int) else i) = L
  generalize hH : (if j < L then L else if j > (l.length : Int) then (l.length : Int) else j) = H
  have hb1 : 0 ≤ L ∧ L ≤ l.length ∧ min L.toNat l.length = min i.toNat l.length := by
    rw [← hL]; split <;> (try split) <;> omega
  have hb2 : L ≤ H ∧ H ≤ l.length ∧
      min (H - L).toNat (l.length - L.toNat) = min (j.toNat - i.toNat) (l.length - L.toNat) := by
    rw [← hH]; split <;> (try split) <;> omega
  have hs : pyListGetSlice (some l) i j = .ok (listSliceLH l L H) := by
    simp only [pyListGetSlice]; rw [hL, hH]
  have hd : l.drop L.toNat = l.drop i.toNat := drop_min_eq _ _ _ hb1.2.2
  have hitems : (listSliceLH l L H).items = (l.take j.toNat).drop i.toNat := by
    rw [List.drop_take, ← hd]
    unfold listSliceLH
    simp only
    split
    · rename_i hle
      have hz : min (j.toNat - i.toNat) (l.length - L.toNat) = 0 := by omega
      have : (l.drop L.toNat).take (j.toNat - i.toNat) = (l.drop L.toNat).take 0 :=
        take_min_eq _ _ _ (by rw [List.length_drop]; omega)
      rw [this]; simp [LObj.empty]
    · rw [prealloc_items]
      apply take_min_eq
      rw [List.length_drop]
      omega
  refine ⟨?_, ?_, rfl, fun h => ?_, fun h => ?_, fun h => ?_, rfl, fun h => ?_, fun h => ?_⟩
  · rw [hs]; show Except.ok (listSliceLH l L H).items = _; rw [hitems]
  · intro r hr
    rw [hs] at hr
    simp only [Except.ok.injEq] at hr
    subst hr
    unfold listSliceLH
    simp only
    split
    · simp [LObj.empty]
    · exact prealloc_shape _
  · unfold pyListNew; rw [if_neg (by omega), if_neg (by omega), if_pos h]
  · unfold listNewPrealloc; rw [if_neg (by omega)]
  · unfold listNewPrealloc; rw [if_pos h]
  · show listConcatLH a b = _
    unfold listConcatLH listNewPrealloc
    by_cases h0 : a.length + b.length = 0
    · have ha : a = [] := List.length_eq_zero_iff.mp (by omega)
      have hb : b = [] := List.length_eq_zero_iff.mp (by omega)
      subst ha hb; rfl
    · have hne : (a ++ b).length ≠ 0 := by simp only [List.length_append]; omega
      rw [if_neg h0, if_neg (by simp only [List.length_append]; omega)]
      unfold LObj.prealloc
      rw [if_neg hne]
  · show listConcatLH a b = _
    unfold listConcatLH listNewPrealloc
    rw [if_neg (by omega), if_pos (by simp only [List.length_append]; omega)]

/-! ## `clear` -/

/-- `l.clear()` (`py_list_clear_impl`, listobject.c:1220-1226), `list_clear` (:923-927),
`list_clear_impl` (:893-921) and `PyList_Clear` (:1570-1581), for every list with its invariant: the
list ends with no items and no array (`sys.getsizeof` shows 40 bytes), and the old items are released
last to first, as their finalizers show. -/
def ListClearSpec : Prop :=
  ∀ (α : Type) (o : LObj α), o.WF →
    listClear o = LObj.empty ∧ listSizeof (listClear o) = 40 ∧
    listClearOrder o = o.items.reverse.map some ∧
    pyListClear (some o) = .ok LObj.empty

theorem listClearSpec_proven : ListClearSpec := by
  intro α o hw
  have hc : listClear o = LObj.empty := listClear_empty o hw
  refine ⟨hc, by rw [hc]; rfl, ?_, by show Except.ok (listClear o) = _; rw [hc]⟩
  have hall : backLoop o.items o.items.length = o.items.reverse.map some := by
    have := backLoop_take o.items o.items.length (by omega)
    simpa using this
  unfold listClearOrder
  cases hh : o.hasItems with
  | true => simp only [Bool.not_true, Bool.false_eq_true, if_false]; exact hall
  | false =>
    obtain ⟨hi, -⟩ := wf_noitems hw hh
    simp [hi]

end PyLean.BytesObj.Seq
