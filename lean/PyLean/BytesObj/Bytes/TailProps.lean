import PyLean.BytesObj.Bytes.FormatProps8
import PyLean.BytesObj.Bytes.CtorProps

/-!
Properties for the second half of Objects/bytesobject.c: `_PyBytes_FromList` with an `__index__`
that changes the list, `bytes_alloc`, `_PyBytes_Resize`'s failure arm, the bytes iterator's
`__reduce__` and `__setstate__`, and `byteswriter_resize`'s bytes and overallocation guard.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

set_option linter.unusedSimpArgs false

/-! ## `_PyBytes_FromList` -/

theorem clamp_byte' (v : Int) (h1 : 0 ≤ v) (h2 : v < 256) : clampSsize v = v :=
  clamp_id v (by simp only [ssizeMin]; omega) (by rw [ssizeMax_val]; omega)

/-- `bytes(lst)` reads the list again after every `__index__` (bytesobject.c:2995-2996): with no item
touching it, the result is the conversion of each item in turn, for every list that can exist; an
item whose `__index__` appends a value gets that value converted too, range check included; one that
clears the list ends the loop after its own byte, and one that pops the last item keeps it from being
read; an `__index__` that raises stops the loop with its exception. The writer grows past its
allocation by `ResizeAndUpdatePointer(size + 1)` and `ResizeToAllocated` (:3011-3019): a list of 257
items whose last `__index__` appends a 258th gives all 258 bytes. Scope: the GIL build. -/
def FromListMut : Prop :=
  (∀ items : List Obj, (items.length : Int) + 33 < 2 ^ 46 →
    bytesFromList (items.map .plain) = bytesFromItems items) ∧
  (∀ v u : Int, 0 ≤ v → v < 256 → 0 ≤ u → u < 256 →
    bytesFromList [.mut (.ok v) (.append u)] = .ok [v.toNat, u.toNat]) ∧
  (∀ v u : Int, 0 ≤ v → v < 256 → (u < 0 ∨ u ≥ 256) →
    bytesFromList [.mut (.ok v) (.append u)] = .error (.valueError "bytes must be in range(0, 256)")) ∧
  (∀ (v : Int) (rest : List LItem), 0 ≤ v → v < 256 → (rest.length : Int) + 34 < 2 ^ 46 →
    bytesFromList (.mut (.ok v) .clear :: rest) = .ok [v.toNat]) ∧
  (∀ (v : Int) (x : Obj), 0 ≤ v → v < 256 →
    bytesFromList [.mut (.ok v) .popLast, .plain x] = .ok [v.toNat]) ∧
  (∀ (e : PyExc) (act : ListAct) (rest : List LItem), (rest.length : Int) + 34 < 2 ^ 46 →
    bytesFromList (.mut (.error e) act :: rest) = .error e) ∧
  (bytesFromList (List.replicate 256 (.plain (.int 7)) ++ [.mut (.ok 8) (.append 9)]) =
    .ok (List.replicate 256 7 ++ [8, 9]))

theorem writerCreate_small (n : Nat) (h : n ≤ 256) :
    ∃ w, writerCreate n false = .ok w ∧ writerResizeToAllocated w = { size := 256, overallocate := true } := by
  by_cases h0 : n = 0
  · subst h0; exact ⟨_, rfl, rfl⟩
  · have h1 : (n : Int) ≥ 1 := by omega
    have h2 : (n : Int) ≤ 256 := by omega
    refine ⟨{ size := n, overallocate := true }, ?_, rfl⟩
    simp [writerCreate, h1, writerResizeRaw, writerAllocated, smallBufferSize, h2]

theorem writerCreate_big (n : Nat) (h0 : 0 < n) (h : (n : Int) + 33 < 2 ^ 46) :
    ∃ w, writerCreate n false = .ok w ∧ (writerResizeToAllocated w).size ≥ n ∧
      (writerResizeToAllocated w).size < 2 ^ 46 ∧ (writerResizeToAllocated w).useBytearray = false := by
  obtain ⟨w, hw, _⟩ := writerCreate_ok n (by omega)
  obtain ⟨hs, ha1, ha2, hb⟩ := writerCreate_facts n w hw
  exact ⟨w, hw, by simp [writerResizeToAllocated]; omega, by simp [writerResizeToAllocated]; omega,
    by simp [writerResizeToAllocated, hb]⟩

theorem fromListMut_proven : FromListMut := by
  refine ⟨bytesFromList_plain, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v u h1 h2 h3 h4
    have hw : writerCreate 1 false = .ok { size := 1, overallocate := true } := by decide
    have hv := clamp_byte' v h1 h2
    have hu := clamp_byte' u h3 h4
    have hv' : ¬ (v < 0 ∨ v ≥ 256) := by omega
    have hu' : ¬ (u < 0 ∨ u ≥ 256) := by omega
    simp [bytesFromList, hw, writerResizeToAllocated, writerAllocated, smallBufferSize, fromListLoop, lItemIndex, ListAct.apply, asSsizeClamp, Obj.index?, hv, hu,
      hv', hu', Except.map, bind, Except.bind, pure, Except.pure]
    simp [writerFinish, writerFinishSize, bytesSizeCheck, mallocFails, bytesObjectSize, ssizeMax_val]
  · intro v u h1 h2 hu
    have hw : writerCreate 1 false = .ok { size := 1, overallocate := true } := by decide
    have hv := clamp_byte' v h1 h2
    have hv' : ¬ (v < 0 ∨ v ≥ 256) := by omega
    have hcu : clampSsize u < 0 ∨ clampSsize u ≥ 256 := by
      simp only [clampSsize, ssizeMin, ssizeMax_val, Int.max_def, Int.min_def]; split <;> split <;> omega
    simp [bytesFromList, hw, writerResizeToAllocated, writerAllocated, smallBufferSize, fromListLoop, lItemIndex, ListAct.apply, asSsizeClamp, Obj.index?, hv,
      hv', hcu, Except.map, bind, Except.bind, pure, Except.pure]
  · intro v rest h1 h2 hl
    have hv := clamp_byte' v h1 h2
    have hv' : ¬ (v < 0 ∨ v ≥ 256) := by omega
    obtain ⟨w, hw, hs1, hs2, hb⟩ := writerCreate_big (rest.length + 1) (by omega) (by omega)
    unfold bytesFromList
    rw [List.length_cons, hw]
    simp only [bind, Except.bind]
    generalize writerResizeToAllocated w = W at hs1 hs2 hb
    have hge : ¬ W.size ≤ 0 := by omega
    simp [fromListLoop, lItemIndex, ListAct.apply, hv, hv', hge, Except.map]
    rw [show 2 * (rest.length + 1) = (2 * rest.length + 1) + 1 by omega, fromListLoop]
    simp only [List.length_nil, Nat.lt_irrefl, ite_false, Nat.not_lt_zero]
    exact wfinish_ok _ _ hb (by simp; omega) hs2
  · intro v x h1 h2
    have hw : writerCreate 2 false = .ok { size := 2, overallocate := true } := by decide
    have hv := clamp_byte' v h1 h2
    have hv' : ¬ (v < 0 ∨ v ≥ 256) := by omega
    simp [bytesFromList, hw, writerResizeToAllocated, writerAllocated, smallBufferSize, fromListLoop, lItemIndex, ListAct.apply, hv, hv', Except.map, bind,
      Except.bind, pure, Except.pure]
    simp [writerFinish, writerFinishSize, bytesSizeCheck, mallocFails, bytesObjectSize, ssizeMax_val]
  · intro e act rest hl
    obtain ⟨w, hw, hs1, hs2, hb⟩ := writerCreate_big (rest.length + 1) (by omega) (by omega)
    unfold bytesFromList
    rw [List.length_cons, hw]
    simp [fromListLoop, lItemIndex, Except.map, bind, Except.bind]
  · set_option maxRecDepth 100000 in decide

/-! ## `bytes_alloc` -/

/-- `bytes_alloc` (bytesobject.c:3171-3180) leaves no cached hash: a fresh object has `ob_shash = -1`,
not the 0 of `PyType_GenericAlloc`'s zeroed memory, so whatever contents the caller then writes, the
first `hash()` computes the hash of those contents (gh-91020). `bytes_subtype_new` then copies the
cache of its source over it. -/
def BytesAllocSpec : Prop :=
  (∀ n : Nat, (bytesAlloc n).shash = -1 ∧ (bytesAlloc n).data.length = n) ∧
  (∀ (hb : Seq → Int) (n : Nat) (d : Seq),
    (bytesHash hb { bytesAlloc n with data := d }).1 = hb d) ∧
  (∀ tmp : BytesSt, bytesSubtypeNew tmp = { data := tmp.data, shash := tmp.shash })

theorem bytesAllocSpec_proven : BytesAllocSpec := by
  refine ⟨fun n => ⟨rfl, by simp [bytesAlloc]⟩, ?_, ?_⟩
  · intro hb n d; simp [bytesHash, bytesAlloc]
  · intro tmp; rfl

/-! ## `_PyBytes_Resize` -/

/-- `_PyBytes_Resize(pv, newsize)` (bytesobject.c:3474-3484) sets `*pv` to NULL and drops the object
when the resize fails, and gives the resized object otherwise; a negative size is the bad internal
call of :3423-3426, and a size past `PY_SSIZE_T_MAX - PyBytesObject_SIZE` is the OverflowError. In
`PyBytes_Concat`'s in-place branch (:3285-3310) a sum past that limit leaves `*pv` NULL with that
error. -/
def PyBytesResizeSpec : Prop :=
  (∀ (o : BytesSt) (n : Int) (e : PyExc), bytesResize o n = .error e → pyBytesResize o n = (none, some e)) ∧
  (∀ (o o' : BytesSt) (n : Int), bytesResize o n = .ok o' → pyBytesResize o n = (some o', none)) ∧
  (∀ (o : BytesSt) (n : Int), n < 0 →
    pyBytesResize o n = (none, some (badInternalCall "Objects/bytesobject.c" 3424))) ∧
  (∀ (o : BytesSt) (n : Int), (o.data.length : Int) ≠ n → o.data ≠ [] → ssizeMax - 33 < n →
    pyBytesResize o n = (none, some (.overflowError "byte string is too large"))) ∧
  (∀ (v wb : Seq) (w : Obj), w.buffer? = some wb → v ≠ [] → wb ≠ [] →
    (v.length : Int) ≤ ssizeMax - wb.length → ssizeMax - 33 < (v.length : Int) + wb.length →
    pyBytesConcat (some v) (some w) true = (none, some (.overflowError "byte string is too large")))

theorem pyBytesResizeSpec_proven : PyBytesResizeSpec := by
  have hmax := ssizeMax_val
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro o n e h; simp [pyBytesResize, h]
  · intro o o' n h; simp [pyBytesResize, h]
  · intro o n h; simp [pyBytesResize, bytesResize, bytesResizeCheck, h, bind, Except.bind]
  · intro o n h1 h2 h3
    have hz : ¬ ((o.data.length : Int) = 0) := by intro e; exact h2 (List.eq_nil_of_length_eq_zero (by omega))
    have h4 : ¬ n < 0 := by rw [hmax] at h3; omega
    have h5 : ¬ n = 0 := by rw [hmax] at h3; omega
    have h6 : n > ssizeMax - bytesObjectSize := by rw [objsize_val]; omega
    simp [pyBytesResize, bytesResize, bytesResizeCheck, bytesSizeCheck, h1, hz, h4, h5, h6, bind, Except.bind]
  · intro v wb w hb hv hwb h1 h2
    have hz : ¬ ((v.length : Int) = 0) := by intro e; exact hv (List.eq_nil_of_length_eq_zero (by omega))
    have hwl : 0 < wb.length := by cases wb with | nil => exact absurd rfl hwb | cons _ _ => simp
    have h0 : ¬ ((v.length : Int) > ssizeMax - wb.length) := by omega
    have hr := (pyBytesResizeSpec_aux v wb hz hwl h2)
    simp only [pyBytesConcat, hb, h0, if_false, hr, ite_true, ite_false]
where
  pyBytesResizeSpec_aux (v wb : Seq) (hz : ¬ ((v.length : Int) = 0)) (hwl : 0 < wb.length)
      (h2 : ssizeMax - 33 < (v.length : Int) + wb.length) :
      pyBytesResize { data := v } ((v.length : Int) + wb.length) =
        (none, some (.overflowError "byte string is too large")) := by
    have hmax := ssizeMax_val
    have h1 : ((v.length : Int)) ≠ (v.length : Int) + wb.length := by omega
    have h4 : ¬ ((v.length : Int) + wb.length < 0) := by omega
    have h5 : ¬ ((v.length : Int) + wb.length = 0) := by omega
    have h6 : (v.length : Int) + wb.length > ssizeMax - bytesObjectSize := by rw [objsize_val]; omega
    simp [pyBytesResize, bytesResize, bytesResizeCheck, bytesSizeCheck, h1, hz, h4, h5, h6, bind, Except.bind]

/-! ## The bytes iterator -/

/-- `iter(b).__reduce__()` (bytesobject.c:3549-3563): the builtins lookup of `iter` comes first, and
`it_seq` and `it_index` are read as that lookup left them (gh-101765), so a lookup whose code exhausts
the iterator gives `(iter, ((),))`; a failed lookup is the result. With a lookup that runs no code, a
live iterator reduces to `(iter, (b,), index)`, and `iter(b).__setstate__(index)` rebuilds it, for
every index in `[0, len(b)]` (a bytes object has at most `PY_SSIZE_T_MAX` bytes). -/
def StrIterReduceSpec : Prop :=
  (∀ (β : Type) (g : String → StrIter → Py β × StrIter) (it : StrIter) (c : β) (it' : StrIter),
    g "iter" it = (.ok c, it') →
    striterReduceG g it =
      (.ok (match it'.seq with | some s => .live c s it'.index | none => .empty c), it')) ∧
  (∀ (β : Type) (g : String → StrIter → Py β × StrIter) (it : StrIter) (e : PyExc) (it' : StrIter),
    g "iter" it = (.error e, it') → striterReduceG g it = (.error e, it')) ∧
  (∀ (β : Type) (c : β) (s : Seq) (i : Int),
    striterReduceG (fun _ it => (.ok c, { it with seq := none })) { seq := some s, index := i } =
      (.ok (.empty c), { seq := none, index := i })) ∧
  (∀ (β : Type) (c : β) (s : Seq) (i : Int), 0 ≤ i → i ≤ s.length → (s.length : Int) ≤ ssizeMax →
    striterReduceG (fun _ it => (.ok c, it)) { seq := some s, index := i } =
      (.ok (.live c s i), { seq := some s, index := i }) ∧
    striterSetstate (bytesIter s) i = .ok { seq := some s, index := i }) ∧
  (∀ it : StrIter, striterReduce it =
    match (striterReduceG (fun _ it => (.ok (), it)) it).1 with
    | .ok (.live _ s i) => some (s, i)
    | _ => none)

theorem strIterReduceSpec_proven : StrIterReduceSpec := by
  have hmax := ssizeMax_val
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro β g it c it' h
    simp only [striterReduceG, h]
    cases it'.seq <;> rfl
  · intro β g it e it' h
    simp [striterReduceG, h]
  · intro β c s i; rfl
  · intro β c s i h1 h2 h2'
    refine ⟨rfl, ?_⟩
    have hr : ssizeMin ≤ i ∧ i ≤ ssizeMax := by simp only [ssizeMin, hmax]; omega
    have h3 : ¬ i < 0 := by omega
    have h4 : ¬ i > s.length := by omega
    simp [striterSetstate, bytesIter, Sequences.asSsize, hr, h3, h4, bind, Except.bind, pure, Except.pure]
  · intro it
    cases h : it.seq <;> simp [striterReduce, striterReduceG, h]

/-- `__setstate__(index)` (bytesobject.c:3567-3582) clamps an index above `len(b)` to `len(b)` (the
iterator is then exhausted, and its length hint 0) and a negative one to 0, does nothing to an
exhausted iterator, and refuses an index outside `Py_ssize_t` with `PyLong_AsSsize_t`'s
OverflowError, before anything else. After it, the length hint of a live iterator is never negative. -/
def StrIterSetstateSpec : Prop :=
  (∀ (s : Seq) (i idx : Int), (s.length : Int) < idx → idx ≤ ssizeMax →
    striterSetstate { seq := some s, index := i } idx = .ok { seq := some s, index := s.length }) ∧
  (∀ (it : StrIter) (idx : Int), it.seq = none → ssizeMin ≤ idx → idx ≤ ssizeMax →
    striterSetstate it idx = .ok it) ∧
  (∀ (it : StrIter) (idx : Int), (idx < ssizeMin ∨ idx > ssizeMax) →
    striterSetstate it idx = .error (.overflowError "Python int too large to convert to C ssize_t")) ∧
  (∀ (s : Seq) (i idx : Int) (it' : StrIter), striterSetstate { seq := some s, index := i } idx = .ok it' →
    0 ≤ striterLen it' ∧ striterLen it' ≤ s.length)

theorem strIterSetstateSpec_proven : StrIterSetstateSpec := by
  have hmax := ssizeMax_val
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s i idx h1 h2
    have hr : ssizeMin ≤ idx ∧ idx ≤ ssizeMax := by simp only [ssizeMin, hmax] at *; omega
    have h3 : ¬ idx < 0 := by omega
    simp [striterSetstate, Sequences.asSsize, hr, h3, h1, bind, Except.bind, pure, Except.pure]
  · intro it idx h h1 h2
    simp [striterSetstate, Sequences.asSsize, h1, h2, h, bind, Except.bind, pure, Except.pure]
  · intro it idx h
    have hr : ¬ (ssizeMin ≤ idx ∧ idx ≤ ssizeMax) := by omega
    simp [striterSetstate, Sequences.asSsize, hr, bind, Except.bind]
  · intro s i idx it' h
    unfold striterSetstate at h
    simp only [Sequences.asSsize, bind, Except.bind] at h
    split at h
    · cases h
    · cases h
      simp only [striterLen]
      split <;> (try split) <;> omega

/-! ## `byteswriter_resize` -/

/-- `byteswriter_resize` with its bytes (bytesobject.c:3730-3798): its control flow is the one the
writer model has (the writer half of the result is `writerResizeRaw`'s, for every storage), and a
growing resize keeps every byte of the old storage at the front of the new one, the small buffer
included when the first object is made (:3771-3773, :3783-3785), so what was written survives.
The overallocation guard of :3742: below it a bytes writer asks for `size + size / 4`, so past
`PY_SSIZE_T_MAX - 33` that is the `byte string is too large` OverflowError of `_PyBytes_FromSize`;
above it (`size / 4` would overflow `size`) it asks for `size` itself, and up to
`PY_SSIZE_T_MAX - 33` that is `malloc`'s MemoryError. Through `%`: a width of
7378697629483820638 is the OverflowError and one of 7378697629483820645 the MemoryError. -/
def WriterBytesSpec : Prop :=
  (∀ (w : Writer) (buf : Seq) (size : Int) (r : Bool),
    (writerResizeRawD w buf size r).map (·.1) = writerResizeRaw w size r) ∧
  (∀ (w w' : Writer) (buf buf' : Seq) (size : Int), (buf.length : Int) = writerAllocated w →
    writerResizeRawD w buf size true = .ok (w', buf') →
    (buf'.length : Int) = writerAllocated w' ∧ buf'.take buf.length = buf) ∧
  (∀ (w : Writer) (size : Int), w.obj = none → w.useBytearray = false → w.overallocate = true →
    256 < size → ssizeMax - size / 4 < size → size ≤ ssizeMax - 33 →
    writerResizeRaw w size true = .error memoryError) ∧
  (∀ (w : Writer) (size : Int), w.obj = none → w.useBytearray = false → w.overallocate = true →
    256 < size → size ≤ ssizeMax - size / 4 → ssizeMax - 33 < size + size / 4 →
    writerResizeRaw w size true = .error (.overflowError "byte string is too large")) ∧
  bytesMod (asc "%*bx") (.tuple [.int 7378697629483820638, .bytes []]) =
    .error (.overflowError "byte string is too large") ∧
  bytesMod (asc "%*bx") (.tuple [.int 7378697629483820645, .bytes []]) = .error memoryError

theorem asc_starbx : asc "%*bx" = [37, 42, 98, 120] := by decide

theorem writerBytesSpec_proven : WriterBytesSpec := by
  have hmax := ssizeMax_val
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w buf size r
    unfold writerResizeRawD writerResizeRaw
    split
    · rfl
    · simp only
      cases writerObjResize w _ <;> rfl
  · intro w w' buf buf' size hl h
    unfold writerResizeRawD at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hl, List.take_length⟩
    · rename_i hgt
      simp only at h
      split at h
      · rename_i obj hobj
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h1 := writerObjResize_size _ _ _ hobj
        have hq : 0 ≤ size / overallocateFactor := Int.ediv_nonneg (by omega) (by decide)
        have hsz : (buf.length : Int) < obj.1 := by
          rw [h1]; split <;> omega
        have hfin : ∀ keep : Seq, keep = buf →
            (((keep ++ List.replicate obj.1.toNat 0).take obj.1.toNat).length : Int) =
              writerAllocated { w with obj := some obj } ∧
            ((keep ++ List.replicate obj.1.toNat 0).take obj.1.toNat).take buf.length = buf := by
          intro keep hk
          rw [hk]
          refine ⟨?_, ?_⟩
          · simp [writerAllocated]; omega
          · rw [List.take_take, show min buf.length obj.1.toNat = buf.length by omega]
            exact List.take_left' rfl
        cases ho : w.obj with
        | some p => simp only [ho] at hfin ⊢; exact hfin buf rfl
        | none =>
          have : (buf.length : Int) = smallBufferSize := by simp [writerAllocated, ho] at hl; exact hl
          simp only [ho, ite_true] at hfin ⊢
          exact hfin _ (List.take_of_length_le (by simp [smallBufferSize] at this ⊢; omega))
      · cases h
  · intro w size ho hb hov h1 h2 h3
    have hna : ¬ (size ≤ writerAllocated w) := by simp [writerAllocated, ho, smallBufferSize]; omega
    have hgs : ¬ (size ≤ ssizeMax - size / overallocateFactor) := by simp only [overallocateFactor]; omega
    have h0 : ¬ size = 0 := by omega
    have h4 : ¬ size > ssizeMax - bytesObjectSize := by rw [objsize_val]; omega
    have h5 : mallocFails (bytesObjectSize + size) = true := by simp [mallocFails, objsize_val]; omega
    simp [writerResizeRaw, hna, hov, hgs, writerObjResize, ho, bytesSizeCheck, h0, h4, h5]
  · intro w size ho hb hov h1 h2 h3
    have hna : ¬ (size ≤ writerAllocated w) := by simp [writerAllocated, ho, smallBufferSize]; omega
    have hgs : size ≤ ssizeMax - size / overallocateFactor := by simp only [overallocateFactor]; omega
    have h0 : ¬ size + size / overallocateFactor = 0 := by simp only [overallocateFactor]; omega
    have h4 : size + size / overallocateFactor > ssizeMax - bytesObjectSize := by
      rw [objsize_val]; simp only [overallocateFactor]; omega
    simp [writerResizeRaw, hna, hov, hgs, writerObjResize, ho, bytesSizeCheck, h0, h4]
  · rw [asc_starbx]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw, writerAllocated, smallBufferSize,
      asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg, starWidth,
      Obj.longValue?, hmax, ssizeMin, formatObj, writeField, signStep, fieldAlloc, writerGrow,
      writerResizeRaw, writerAllocated, smallBufferSize, overallocateFactor, writerObjResize,
      bytesSizeCheck, objsize_val, mallocFails, bind, Except.bind, pure, Except.pure]
  · rw [asc_starbx]
    simp [bytesMod, bytesFormatEx, writerCreate, writerResizeRaw, writerAllocated, smallBufferSize,
      asMapping, bind, Except.bind, pure, Except.pure]
    rw [formatLoop]
    simp [formatSpec, flagsLoop, readSigned, sgnChar, parseWidth, parsePrec, nextC, getNextArg, starWidth,
      Obj.longValue?, hmax, ssizeMin, formatObj, writeField, signStep, fieldAlloc, writerGrow,
      writerResizeRaw, writerAllocated, smallBufferSize, overallocateFactor, writerObjResize,
      bytesSizeCheck, objsize_val, mallocFails, bind, Except.bind, pure, Except.pure]

end PyLean.BytesObj.Bytes
