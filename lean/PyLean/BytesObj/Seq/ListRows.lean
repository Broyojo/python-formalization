import PyLean.BytesObj.Seq.CApiContent
import PyLean.BytesObj.Seq.Release
import PyLean.Sequences.ListModel

/-!
The allocation-dependent outcome of the mutating `list` operations of Objects/listobject.c
(CPython 3.15.2): which calls succeed, with what contents and allocation, and which raise.

`ListOpsWF` and `ListContents` state what a successful call leaves; they hold for a function
that always fails. The statements here force success under the conditions the C code
gives, and pin the `MemoryError` past `PY_SSIZE_T_MAX / sizeof(PyObject *)` slots, the
`SystemError` refusals of the C API, and the allocation that `sys.getsizeof` shows.
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α : Type}

/-! ## `list_resize` and `py_list_resize` -/

/-- `list_resize(o, newsize)` succeeds: either the array is already large enough, or the new
allocation fits `PY_SSIZE_T_MAX / sizeof(PyObject *)`. -/
def listCanGrow (o : LObj α) (newsize : Int) : Prop :=
  newsize ≤ o.allocated ∨ newAllocated o.items.length newsize ≤ ssizeMax / 8

/-- `list_resize`, listobject.c:110-129, and `py_list_resize`, :133-216, for every allocation,
size and target size:

* the fast path (:121-128) keeps the array when it is large enough and the new size is at least
  half of it, or the array is small (`LIST_SMALL_ALLOCATED`, gh-158592);
* so an array of more than 32 slots shrinking below half of its size is reallocated to
  `new_allocated`, which always fits for a list whose array fits;
* growing past the array allocates `new_allocated` if that fits `PY_SSIZE_T_MAX / 8` slots
  (:194-200) and raises `MemoryError` otherwise;
* a shrinking resize whose `new_allocated` does not fit keeps the old array and succeeds
  (:203-207, "Never fail when shrinking allocations"), so a resize to at most the allocation
  never fails (the comment at :103, "Failure is impossible if newsize <= self.allocated");
* `new_allocated` (:148-156) is `newsize + newsize/8 + 6` rounded down to a multiple of 4, unless
  the jump from the current size is larger than that over-allocation, when it is `newsize`
  rounded up to a multiple of 4; `0` for an empty list. -/
def ListResizeExact : Prop :=
  ∀ (allocated : Int) (h : Bool) (size newsize : Int), 0 ≤ allocated → 0 ≤ newsize →
    (newsize ≤ allocated → (allocated / 2 ≤ newsize ∨ allocated ≤ 32) →
      listResize allocated h size newsize = .ok (allocated, h)) ∧
    (allocated ≤ ssizeMax / 8 → 32 < allocated → newsize < allocated / 2 →
      listResize allocated h size newsize = .ok (newAllocated size newsize, true)) ∧
    (allocated < newsize → newAllocated size newsize ≤ ssizeMax / 8 →
      listResize allocated h size newsize = .ok (newAllocated size newsize, true)) ∧
    (allocated < newsize → ssizeMax / 8 < newAllocated size newsize →
      listResize allocated h size newsize = .error memoryError) ∧
    (newsize < allocated → ssizeMax / 8 < newAllocated size newsize →
      ¬ (allocated / 2 ≤ newsize ∨ allocated ≤ 32) →
      listResize allocated h size newsize = .ok (allocated, h)) ∧
    (newsize ≤ allocated → ∃ r, listResize allocated h size newsize = .ok r) ∧
    newAllocated size 0 = 0 ∧
    (0 < newsize → newsize - size ≤ (newsize + newsize / 8 + 6) / 4 * 4 - newsize →
      newAllocated size newsize = (newsize + newsize / 8 + 6) / 4 * 4) ∧
    (0 < newsize → (newsize + newsize / 8 + 6) / 4 * 4 - newsize < newsize - size →
      newAllocated size newsize = (newsize + 3) / 4 * 4)

theorem newAllocated_le (size n : Int) (h0 : 0 ≤ n) : newAllocated size n ≤ n + n / 8 + 6 := by
  unfold newAllocated overalloc
  simp only
  split <;> (try split) <;> omega

theorem listResizeExact_proven : ListResizeExact := by
  intro allocated h size newsize ha hn
  have h8 : ssizeMax / 8 = 1152921504606846975 := by decide
  have hs : listSmallAllocated = 32 := rfl
  have hna := newAllocated_le size newsize hn
  refine ⟨fun h1 h2 => ?_, fun hb h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_,
    fun h1 h2 h3 => ?_, fun h1 => ?_, ?_, fun h0 h1 => ?_, fun h0 h1 => ?_⟩
  · unfold listResize
    rw [if_pos ⟨h1, by rw [hs]; omega⟩]
  · unfold listResize
    rw [if_neg (by rw [hs]; omega)]
    simp only
    rw [if_pos (by omega)]
  · unfold listResize
    rw [if_neg (by omega)]
    simp only
    rw [if_pos h2]
  · unfold listResize
    rw [if_neg (by omega)]
    simp only
    rw [if_neg (by omega), if_neg (by omega)]
  · unfold listResize
    rw [if_neg (by rw [hs]; omega)]
    simp only
    rw [if_neg (by omega), if_pos h1]
  · unfold listResize
    split
    · exact ⟨_, rfl⟩
    · simp only
      split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · rename_i hf _ hlt
          exact absurd ⟨h1, Or.inl (by omega)⟩ hf
  · unfold newAllocated
    simp
  · unfold newAllocated overalloc
    simp only
    rw [if_neg (by omega), if_neg (by omega)]
  · unfold newAllocated overalloc
    simp only
    rw [if_neg (by omega), if_pos h1]

/-- `list_resize` succeeds exactly when `listCanGrow`, and fails with `MemoryError` otherwise. -/
theorem listResize_ok_iff (allocated : Int) (h : Bool) (size newsize : Int) (hn : 0 ≤ newsize)
    (ha : 0 ≤ allocated) :
    ((newsize ≤ allocated ∨ newAllocated size newsize ≤ ssizeMax / 8) →
      ∃ r, listResize allocated h size newsize = .ok r) ∧
    (¬ (newsize ≤ allocated ∨ newAllocated size newsize ≤ ssizeMax / 8) →
      listResize allocated h size newsize = .error memoryError) := by
  obtain ⟨-, -, h3, h4, -, h6, -⟩ := listResizeExact_proven allocated h size newsize ha hn
  constructor
  · intro hc
    by_cases hle : newsize ≤ allocated
    · exact h6 hle
    · exact ⟨_, h3 (by omega) (by omega)⟩
  · intro hc
    exact h4 (by omega) (by omega)

/-- `list_resize` followed by setting the items: success exactly when `listCanGrow`, and then
the invariant holds. -/
theorem resizeTo_spec (o : LObj α) (items : List α) (hw : o.WF) :
    (listCanGrow o items.length → ∃ o', resizeTo o items = .ok o' ∧ o'.items = items ∧ o'.WF) ∧
    (¬ listCanGrow o items.length → resizeTo o items = .error memoryError) := by
  obtain ⟨h1, h2⟩ := listResize_ok_iff o.allocated o.hasItems o.items.length items.length
    (by omega) hw.nonneg
  constructor
  · intro hc
    obtain ⟨⟨a, b⟩, hr⟩ := h1 hc
    have hres : resizeTo o items = .ok { items := items, allocated := a, hasItems := b } := by
      unfold resizeTo; rw [hr]
    obtain ⟨hw', hi⟩ := resizeTo_wf hw hres
    exact ⟨_, hres, hi, hw'⟩
  · intro hc
    unfold resizeTo
    rw [h2 hc]

theorem canGrow_small (o : LObj α) (n : Int) (h0 : 0 ≤ n) (h : n ≤ ssizeMax / 16) :
    listCanGrow o n := by
  right
  have h16 : ssizeMax / 16 = 576460752303423487 := by decide
  have h8 : ssizeMax / 8 = 1152921504606846975 := by decide
  have := newAllocated_le o.items.length n h0
  omega

theorem canGrow_big (o : LObj α) (n : Int) (hw : o.WF) (h : ssizeMax / 8 < n) :
    ¬ listCanGrow o n := by
  intro hc
  have h8 : (0 : Int) ≤ ssizeMax / 8 := by decide
  have := newAllocated_ge o.items.length n (by omega)
  have := hw.bytes
  rcases hc with hc | hc <;> omega

theorem wf_noitems {o : LObj α} (hw : o.WF) (h : o.hasItems = false) :
    o.items = [] ∧ o.allocated = 0 := by
  have hal : ¬ 0 < o.allocated := fun hp => by have := hw.array hp; simp [this] at h
  have hc := hw.covers
  have hn := hw.nonneg
  exact ⟨List.length_eq_zero_iff.mp (by omega), by omega⟩

/-! ## Taking and dropping at clipped positions -/

theorem take_min_eq : ∀ (l : List α) (a b : Nat), min a l.length = min b l.length → l.take a = l.take b
  | [], _, _, _ => by simp
  | _ :: _, 0, 0, _ => rfl
  | _ :: _, 0, _ + 1, h => by simp only [List.length_cons] at h; omega
  | _ :: _, _ + 1, 0, h => by simp only [List.length_cons] at h; omega
  | x :: xs, a + 1, b + 1, h => by
    simp only [List.take_succ_cons]
    rw [take_min_eq xs a b (by simp only [List.length_cons] at h; omega)]

theorem drop_min_eq : ∀ (l : List α) (a b : Nat), min a l.length = min b l.length → l.drop a = l.drop b
  | [], _, _, _ => by simp
  | _ :: _, 0, 0, _ => rfl
  | _ :: _, 0, _ + 1, h => by simp only [List.length_cons] at h; omega
  | _ :: _, _ + 1, 0, h => by simp only [List.length_cons] at h; omega
  | _ :: xs, a + 1, b + 1, h => by
    simp only [List.drop_succ_cons]
    exact drop_min_eq xs a b (by simp only [List.length_cons] at h; omega)

/-- The clipping of `list_ass_slice_lock_held` (listobject.c:995-1003), as positions. -/
theorem listAssSlice_shape (o : LObj α) (lo hi : Int) (v : Option (List α)) :
    ∃ L H : Int, 0 ≤ L ∧ L ≤ H ∧ H ≤ o.items.length ∧
      o.items.take L.toNat = o.items.take lo.toNat ∧
      o.items.drop H.toNat = o.items.drop (max lo.toNat hi.toNat) ∧
      listAssSlice o lo hi v =
        (if (o.items.length : Int) + (((v.getD []).length : Int) - (H - L)) = 0 then .ok (listClear o)
         else if ((v.getD []).length : Int) - (H - L) = 0 then
           .ok { o with items := o.items.take L.toNat ++ v.getD [] ++ o.items.drop H.toNat }
         else resizeTo o (o.items.take L.toNat ++ v.getD [] ++ o.items.drop H.toNat)) := by
  generalize hL : (if lo < 0 then (0 : Int) else
    if lo > (o.items.length : Int) then (o.items.length : Int) else lo) = L
  generalize hH : (if hi < L then L else
    if hi > (o.items.length : Int) then (o.items.length : Int) else hi) = H
  have hb1 : 0 ≤ L ∧ L ≤ o.items.length ∧ min L.toNat o.items.length = min lo.toNat o.items.length := by
    rw [← hL]; split <;> (try split) <;> omega
  have hb2 : L ≤ H ∧ H ≤ o.items.length ∧
      min H.toNat o.items.length = min (max lo.toNat hi.toNat) o.items.length := by
    rw [← hH]; split <;> (try split) <;> omega
  refine ⟨L, H, hb1.1, hb2.1, hb2.2.1, take_min_eq _ _ _ hb1.2.2, drop_min_eq _ _ _ hb2.2.2, ?_⟩
  unfold listAssSlice
  simp only
  rw [hL, hH]

/-! ## What succeeds -/

/-- The mutating operations of a list with its invariant (`LObj.WF`), for every argument, by
outcome:

* `append` (`list_append_impl`, `_PyList_AppendTakeRef`, `_PyList_AppendTakeRefListResize`,
  listobject.c:546-557) stores in place while there is room and otherwise resizes; it succeeds
  exactly when `list_resize` can grow the list by one, and raises `MemoryError` otherwise;
* `ins1` (:502-528) refuses `NULL` with `SystemError` before anything else, then always calls
  `list_resize(n + 1)` and inserts at the clipped position of `Sequences.listIns1` (the one
  `InsertAgree` pins against `deque.insert`);
* `l[i] = x` and `del l[i]` (`list_ass_item`, :1159-1190) succeed for every valid index (the
  store keeps the array; the delete is a shrinking resize, which cannot fail) and raise
  `IndexError` otherwise;
* `clear` (`list_clear_impl`, :893-921) leaves no array: `allocated == 0`, `ob_item == NULL`;
* `extend` from a list or tuple (`list_extend_fast`, :1262-1298) and from a set or dict
  (`list_extend_set`, `list_extend_dict`, `list_extend_dictitems`, :1388-1475) succeed with the
  items appended up to `PY_SSIZE_T_MAX / 16` items in total and raise `MemoryError` past
  `PY_SSIZE_T_MAX / 8`; a list without an array takes `list_preallocate_exact` (the size rounded
  up to even, :230) from a sequence, but `list_resize` (over-allocated) from a set or dict;
* `list_ass_slice` (:970-1089) replaces `a[max(lo,0):max(lo,hi,0)]`, clipped to the list,
  succeeds up to `PY_SSIZE_T_MAX / 16` items and raises `MemoryError` past `PY_SSIZE_T_MAX / 8`;
  a deletion always succeeds; `a[lo:hi] = a` uses a copy; an object `PySequence_Fast` refuses
  raises `TypeError("can only assign an iterable")`.

`sys.getsizeof` shows the allocation, which the difftest compares after every operation. -/
def ListOpsSucceed : Prop :=
  ∀ (α : Type) (o : LObj α) (v : α) (w lo hi : Int) (s : List α), o.WF →
    (listCanGrow o (o.items.length + 1) →
      ∃ o', listAppend o v = .ok o' ∧ o'.items = o.items ++ [v] ∧ o'.WF) ∧
    (¬ listCanGrow o (o.items.length + 1) → listAppend o v = .error memoryError) ∧
    ((o.items.length : Int) < o.allocated → listAppend o v = .ok { o with items := o.items ++ [v] }) ∧
    ins1 o w none = .error systemError ∧
    (listCanGrow o (o.items.length + 1) →
      ∃ o', ins1 o w (some v) = .ok o' ∧ o'.items = PyLean.Sequences.listIns1 o.items w v ∧ o'.WF) ∧
    (¬ listCanGrow o (o.items.length + 1) → ins1 o w (some v) = .error memoryError) ∧
    (0 ≤ w → w < o.items.length →
      listAssItem o w (some v) = .ok { o with items := o.items.set w.toNat v } ∧
      ∃ o', listAssItem o w none = .ok o' ∧ o'.items = o.items.eraseIdx w.toNat ∧ o'.WF) ∧
    ((w < 0 ∨ (o.items.length : Int) ≤ w) → ssizeMin ≤ w → w ≤ ssizeMax → ∀ x,
      listAssItem o w x = .error (.indexError "list assignment index out of range")) ∧
    listClear o = LObj.empty ∧
    ((o.items.length + s.length : Int) ≤ ssizeMax / 16 →
      ∃ o', listExtendFast o s = .ok o' ∧ o'.items = o.items ++ s ∧ o'.WF) ∧
    (ssizeMax / 8 < (o.items.length + s.length : Int) → listExtendFast o s = .error memoryError) ∧
    (o.hasItems = false → s ≠ [] → (s.length : Int) ≤ ssizeMax / 16 →
      ∃ o', listExtendFast o s = .ok o' ∧ o'.allocated = ((s.length : Int) + 1) / 2 * 2) ∧
    ((o.items.length + s.length : Int) ≤ ssizeMax / 16 →
      ∃ o', listExtendSized o s = .ok o' ∧ o'.items = o.items ++ s ∧ o'.WF) ∧
    (ssizeMax / 8 < (o.items.length + s.length : Int) → listExtendSized o s = .error memoryError) ∧
    (o.hasItems = false → s ≠ [] → (s.length : Int) ≤ ssizeMax / 16 →
      ∃ o', listExtendSized o s = .ok o' ∧ o'.allocated = newAllocated 0 s.length) ∧
    (((o.items.take lo.toNat ++ s ++ o.items.drop (max lo.toNat hi.toNat)).length : Int) ≤ ssizeMax / 16 →
      ∃ o', listAssSliceV o lo hi (.seq s) = .ok o' ∧
        o'.items = o.items.take lo.toNat ++ s ++ o.items.drop (max lo.toNat hi.toNat) ∧ o'.WF) ∧
    (ssizeMax / 8 < ((o.items.take lo.toNat ++ s ++ o.items.drop (max lo.toNat hi.toNat)).length : Int) →
      listAssSliceV o lo hi (.seq s) = .error memoryError) ∧
    (((o.items.length + o.items.length : Nat) : Int) ≤ ssizeMax / 16 →
      ∃ o', listAssSliceV o lo hi .selfCopy = .ok o' ∧
        o'.items = o.items.take lo.toNat ++ o.items ++ o.items.drop (max lo.toNat hi.toNat)) ∧
    (∃ o', listAssSliceV o lo hi .del = .ok o' ∧
      o'.items = o.items.take lo.toNat ++ o.items.drop (max lo.toNat hi.toNat) ∧ o'.WF) ∧
    listAssSliceV o lo hi .notIterable = .error (.typeError "can only assign an iterable")

theorem listAppend_spec (o : LObj α) (v : α) (hw : o.WF) :
    (listCanGrow o (o.items.length + 1) →
      ∃ o', listAppend o v = .ok o' ∧ o'.items = o.items ++ [v] ∧ o'.WF) ∧
    (¬ listCanGrow o (o.items.length + 1) → listAppend o v = .error memoryError) := by
  obtain ⟨r1, r2⟩ := resizeTo_spec o (o.items ++ [v]) hw
  have hl : (((o.items ++ [v]).length : Nat) : Int) = (o.items.length : Int) + 1 := by simp
  rw [hl] at r1 r2
  unfold listAppend
  constructor
  · intro hc
    split
    · rename_i hroom
      refine ⟨_, rfl, rfl, ⟨hw.nonneg, ?_, hw.array, hw.bytes⟩⟩
      show (((o.items ++ [v]).length : Nat) : Int) ≤ o.allocated
      rw [hl]; omega
    · exact r1 hc
  · intro hc
    rw [if_neg (fun h => hc (Or.inl (by omega)))]
    exact r2 hc

theorem ins1_spec (o : LObj α) (w : Int) (v : α) (hw : o.WF) :
    (listCanGrow o (o.items.length + 1) →
      ∃ o', ins1 o w (some v) = .ok o' ∧ o'.items = PyLean.Sequences.listIns1 o.items w v ∧ o'.WF) ∧
    (¬ listCanGrow o (o.items.length + 1) → ins1 o w (some v) = .error memoryError) := by
  have hk := (listContents_proven α o o [] [] [] v w "" hw).2.2.1
  have hk' : (ins1Where o.items.length w).toNat ≤ o.items.length := by omega
  have hl : (((o.items.take (ins1Where o.items.length w).toNat ++
      v :: o.items.drop (ins1Where o.items.length w).toNat).length : Nat) : Int) = (o.items.length : Int) + 1 := by
    simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]
    omega
  have hseq : PyLean.Sequences.listIns1 o.items w v = o.items.take (ins1Where o.items.length w).toNat ++
      v :: o.items.drop (ins1Where o.items.length w).toNat := rfl
  obtain ⟨r1, r2⟩ := resizeTo_spec o (o.items.take (ins1Where o.items.length w).toNat ++
      v :: o.items.drop (ins1Where o.items.length w).toNat) hw
  rw [hl] at r1 r2
  have hins : ins1 o w (some v) = resizeTo o (o.items.take (ins1Where o.items.length w).toNat ++
      v :: o.items.drop (ins1Where o.items.length w).toNat) := rfl
  rw [hins, hseq]
  exact ⟨r1, r2⟩

theorem listAssItem_spec (o : LObj α) (w : Int) (v : α) (hw : o.WF) :
    (0 ≤ w → w < o.items.length →
      listAssItem o w (some v) = .ok { o with items := o.items.set w.toNat v } ∧
      ∃ o', listAssItem o w none = .ok o' ∧ o'.items = o.items.eraseIdx w.toNat ∧ o'.WF) ∧
    ((w < 0 ∨ (o.items.length : Int) ≤ w) → ssizeMin ≤ w → w ≤ ssizeMax → ∀ x,
      listAssItem o w x = .error (.indexError "list assignment index out of range")) := by
  have hm : ssizeMin = -9223372036854775808 := by decide
  have h63 : (2 : Int) ^ 63 = 9223372036854775808 := by decide
  have hM : ssizeMax = 9223372036854775807 := by decide
  have hlen : (o.items.length : Int) ≤ ssizeMax := by
    have := hw.covers; have := hw.bytes; have : ssizeMax / 8 ≤ ssizeMax := by decide
    omega
  constructor
  · intro h0 h1
    have hv : validIndex w o.items.length = true := by
      rw [validIndex_eq w o.items.length (by omega) (by omega) (by omega) hlen]
      simp only [decide_eq_true_eq]; omega
    have hlt : (((o.items.eraseIdx w.toNat).length : Nat) : Int) ≤ o.allocated := by
      have := hw.covers
      rw [List.length_eraseIdx]
      split <;> omega
    obtain ⟨r1, -⟩ := resizeTo_spec o (o.items.eraseIdx w.toNat) hw
    obtain ⟨o', h1', h2', h3'⟩ := r1 (Or.inl hlt)
    refine ⟨?_, o', ?_, h2', h3'⟩
    · unfold listAssItem; rw [hv]; rfl
    · unfold listAssItem; rw [hv]; exact h1'
  · intro hout hm0 hm1 x
    have hv : validIndex w o.items.length = false := by
      rw [validIndex_eq w o.items.length (by omega) (by omega) (by omega) hlen]
      simp only [decide_eq_false_iff_not]; omega
    unfold listAssItem
    rw [hv]
    rfl

theorem listExtendFast_spec (o : LObj α) (s : List α) (hw : o.WF) :
    ((o.items.length + s.length : Int) ≤ ssizeMax / 16 →
      ∃ o', listExtendFast o s = .ok o' ∧ o'.items = o.items ++ s ∧ o'.WF) ∧
    (ssizeMax / 8 < (o.items.length + s.length : Int) → listExtendFast o s = .error memoryError) ∧
    (o.hasItems = false → s ≠ [] → (s.length : Int) ≤ ssizeMax / 16 →
      ∃ o', listExtendFast o s = .ok o' ∧ o'.allocated = ((s.length : Int) + 1) / 2 * 2) := by
  have h16 : ssizeMax / 16 = 576460752303423487 := by decide
  have h8 : ssizeMax / 8 = 1152921504606846975 := by decide
  have hl : (((o.items ++ s).length : Nat) : Int) = (o.items.length : Int) + s.length := by simp
  obtain ⟨r1, r2⟩ := resizeTo_spec o (o.items ++ s) hw
  rw [hl] at r1 r2
  have hpre : ∀ (m : Int), 0 ≤ m → m ≤ ssizeMax / 16 → listPreallocateExact m = .ok ((m + 1) / 2 * 2) := by
    intro m h0 h1
    unfold listPreallocateExact; simp only; rw [if_pos (by omega)]
  have hpreBig : ∀ (m : Int), ssizeMax / 8 < m → listPreallocateExact m = .error memoryError := by
    intro m h1
    unfold listPreallocateExact; simp only; rw [if_neg (by omega)]
  refine ⟨fun hb => ?_, fun hb => ?_, fun hh hne hb => ?_⟩
  · unfold listExtendFast
    by_cases hs0 : s.length = 0
    · rw [if_pos hs0]
      exact ⟨o, rfl, by rw [List.length_eq_zero_iff.mp hs0]; simp, hw⟩
    rw [if_neg hs0]
    cases hh : o.hasItems with
    | false =>
      obtain ⟨hi, ha⟩ := wf_noitems hw hh
      simp only [Bool.not_false, if_true]
      have hs1 : (0 : Int) ≤ s.length := by omega
      have hs2 : (s.length : Int) ≤ ssizeMax / 16 := by omega
      rw [hpre s.length hs1 hs2]
      refine ⟨_, rfl, rfl, ⟨?_, ?_, fun _ => rfl, ?_⟩⟩
      · show (0 : Int) ≤ ((s.length : Int) + 1) / 2 * 2
        omega
      · show (((o.items ++ s).length : Nat) : Int) ≤ ((s.length : Int) + 1) / 2 * 2
        rw [hl, hi]; simp only [List.length_nil]; omega
      · show ((s.length : Int) + 1) / 2 * 2 ≤ ssizeMax / 8
        omega
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      exact r1 (canGrow_small o _ (by omega) hb)
  · unfold listExtendFast
    have hcov := hw.covers
    have hby := hw.bytes
    rw [if_neg (by omega)]
    cases hh : o.hasItems with
    | false =>
      obtain ⟨hi, ha⟩ := wf_noitems hw hh
      simp only [Bool.not_false, if_true]
      have h0 : o.items.length = 0 := by simp [hi]
      have hs3 : ssizeMax / 8 < (s.length : Int) := by omega
      rw [hpreBig s.length hs3]
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      exact r2 (canGrow_big o _ hw hb)
  · unfold listExtendFast
    have hs0 : s.length ≠ 0 := fun h => hne (List.length_eq_zero_iff.mp h)
    rw [if_neg hs0]
    simp only [hh, Bool.not_false, if_true]
    rw [hpre s.length (by omega) hb]
    exact ⟨_, rfl, rfl⟩

theorem listExtendSized_spec (o : LObj α) (s : List α) (hw : o.WF) :
    ((o.items.length + s.length : Int) ≤ ssizeMax / 16 →
      ∃ o', listExtendSized o s = .ok o' ∧ o'.items = o.items ++ s ∧ o'.WF) ∧
    (ssizeMax / 8 < (o.items.length + s.length : Int) → listExtendSized o s = .error memoryError) ∧
    (o.hasItems = false → s ≠ [] → (s.length : Int) ≤ ssizeMax / 16 →
      ∃ o', listExtendSized o s = .ok o' ∧ o'.allocated = newAllocated 0 s.length) := by
  have h16 : ssizeMax / 16 = 576460752303423487 := by decide
  have h8 : ssizeMax / 8 = 1152921504606846975 := by decide
  have hl : (((o.items ++ s).length : Nat) : Int) = (o.items.length : Int) + s.length := by simp
  obtain ⟨r1, r2⟩ := resizeTo_spec o (o.items ++ s) hw
  rw [hl] at r1 r2
  refine ⟨fun hb => ?_, fun hb => ?_, fun hh hne hb => ?_⟩
  · unfold listExtendSized
    by_cases h0 : o.items.length + s.length = 0
    · rw [if_pos h0]
      have : s = [] := List.length_eq_zero_iff.mp (by omega)
      exact ⟨o, rfl, by simp [this], hw⟩
    · rw [if_neg h0]
      exact r1 (canGrow_small o _ (by omega) hb)
  · unfold listExtendSized
    rw [if_neg (by omega)]
    exact r2 (canGrow_big o _ hw hb)
  · obtain ⟨hi, ha⟩ := wf_noitems hw hh
    have hs0 : s.length ≠ 0 := fun h => hne (List.length_eq_zero_iff.mp h)
    have hna : newAllocated 0 s.length ≤ ssizeMax / 8 := by
      have := newAllocated_le 0 s.length (by omega); omega
    unfold listExtendSized resizeTo
    rw [if_neg (by omega)]
    have hres := (listResizeExact_proven o.allocated o.hasItems o.items.length (o.items ++ s).length
      hw.nonneg (by omega)).2.2.1 (by rw [ha]; simp only [List.length_append]; omega)
      (by rw [hi]; simpa using hna)
    rw [hres]
    refine ⟨_, rfl, ?_⟩
    simp [hi]

theorem listAssSlice_spec (o : LObj α) (lo hi : Int) (vs : List α) (hw : o.WF) :
    let r := o.items.take lo.toNat ++ vs ++ o.items.drop (max lo.toNat hi.toNat)
    ((r.length : Int) ≤ ssizeMax / 16 → ∃ o', listAssSlice o lo hi (some vs) = .ok o' ∧ o'.items = r ∧ o'.WF) ∧
    (ssizeMax / 8 < (r.length : Int) → listAssSlice o lo hi (some vs) = .error memoryError) := by
  intro r
  have h16 : ssizeMax / 16 = 576460752303423487 := by decide
  have h8 : ssizeMax / 8 = 1152921504606846975 := by decide
  obtain ⟨L, H, h0, h1, h2, ht, hd, heq⟩ := listAssSlice_shape o lo hi (some vs)
  simp only [Option.getD_some] at heq
  have hr : o.items.take L.toNat ++ vs ++ o.items.drop H.toNat = r := by rw [ht, hd]
  have hrl : (r.length : Int) = L + vs.length + (o.items.length - H) := by
    rw [← hr]; simp only [List.length_append, List.length_take, List.length_drop]; omega
  rw [hr] at heq
  obtain ⟨r1, r2⟩ := resizeTo_spec o r hw
  have hcov := hw.covers
  have hby := hw.bytes
  constructor
  · intro hb
    rw [heq]
    split
    · rename_i hz
      have hv : vs = [] := List.length_eq_zero_iff.mp (by omega)
      have hrn : r = [] := List.length_eq_zero_iff.mp (by omega)
      refine ⟨_, rfl, ?_, clear_wf o hw⟩
      rw [hrn, listClear_items o hw]
    · split
      · refine ⟨_, rfl, rfl, ⟨hw.nonneg, ?_, hw.array, hw.bytes⟩⟩
        show (r.length : Int) ≤ o.allocated
        omega
      · exact r1 (canGrow_small o _ (by omega) hb)
  · intro hb
    rw [heq, if_neg (by omega), if_neg (by omega)]
    exact r2 (canGrow_big o _ hw hb)

theorem listAssSlice_del (o : LObj α) (lo hi : Int) (hw : o.WF) :
    ∃ o', listAssSlice o lo hi none = .ok o' ∧
      o'.items = o.items.take lo.toNat ++ o.items.drop (max lo.toNat hi.toNat) ∧ o'.WF := by
  obtain ⟨L, H, h0, h1, h2, ht, hd, heq⟩ := listAssSlice_shape o lo hi none
  simp only [Option.getD_none, List.length_nil, List.append_nil] at heq
  have hr : o.items.take L.toNat ++ o.items.drop H.toNat =
      o.items.take lo.toNat ++ o.items.drop (max lo.toNat hi.toNat) := by rw [ht, hd]
  have hrl : ((o.items.take L.toNat ++ o.items.drop H.toNat).length : Int) = L + (o.items.length - H) := by
    simp only [List.length_append, List.length_take, List.length_drop]; omega
  obtain ⟨r1, -⟩ := resizeTo_spec o (o.items.take L.toNat ++ o.items.drop H.toNat) hw
  have hcov := hw.covers
  rw [heq]
  split
  · rename_i hz
    refine ⟨_, rfl, ?_, clear_wf o hw⟩
    rw [← hr, listClear_items o hw]
    have : (o.items.take L.toNat ++ o.items.drop H.toNat).length = 0 := by omega
    exact (List.length_eq_zero_iff.mp this).symm
  · split
    · refine ⟨_, rfl, hr, ⟨hw.nonneg, ?_, hw.array, hw.bytes⟩⟩
      show (((o.items.take L.toNat ++ o.items.drop H.toNat).length : Nat) : Int) ≤ o.allocated
      omega
    · obtain ⟨o', a1, a2, a3⟩ := r1 (Or.inl (by omega))
      exact ⟨o', a1, by rw [a2, hr], a3⟩

theorem listOpsSucceed_proven : ListOpsSucceed := by
  intro α o v w lo hi s hw
  obtain ⟨a1, a2⟩ := listAppend_spec o v hw
  obtain ⟨i1, i2⟩ := ins1_spec o w v hw
  obtain ⟨s1, s2⟩ := listAssItem_spec o w v hw
  obtain ⟨e1, e2, e3⟩ := listExtendFast_spec o s hw
  obtain ⟨z1, z2, z3⟩ := listExtendSized_spec o s hw
  obtain ⟨q1, q2⟩ := listAssSlice_spec o lo hi s hw
  obtain ⟨p1, -⟩ := listAssSlice_spec o lo hi o.items hw
  refine ⟨a1, a2, fun h => ?_, rfl, i1, i2, s1, s2, ?_, e1, e2, e3, z1, z2, z3, q1, q2,
    fun hb => ?_, listAssSlice_del o lo hi hw, rfl⟩
  · unfold listAppend; rw [if_pos h]
  · unfold listClear
    cases hh : o.hasItems with
    | true => rfl
    | false =>
      obtain ⟨hi, ha⟩ := wf_noitems hw hh
      simp only [Bool.not_false, if_true]
      cases o; simp_all [LObj.empty]
  · have hlen : ((o.items.take lo.toNat ++ o.items ++ o.items.drop (max lo.toNat hi.toNat)).length : Int)
        ≤ ssizeMax / 16 := by
      simp only [List.length_append, List.length_take, List.length_drop]
      omega
    obtain ⟨o', h1, h2, -⟩ := p1 hlen
    exact ⟨o', h1, h2⟩

end PyLean.BytesObj.Seq
