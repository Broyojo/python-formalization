import PyLean.BytesObj.Bytes.HeapProps2

/-!
More properties of Objects/bytearrayobject.c (CPython 3.15.2): the extended-slice branch and the other
right-hand sides of slice assignment, the remaining paths of `__init__`, the failure path of
`bytearray_resize_storage`, `tp_new` and `tp_dealloc`.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## Extended-slice assignment and deletion -/

/-- The extended-slice part of `bytearray_ass_subscript_lock_held`, :880-939 (`baAssExtended`): a value
of the slice's length (not 0) is stored by the loop of :928-934 and succeeds whether or not there are
exports, since the size does not change; a value of another non-zero length is the `ValueError`
naming both sizes; an empty value deletes, which with exports is `_canresize`'s `BufferError` even for
an empty slice (:887-889, before the `slicelen == 0` exit), and without exports an empty slice leaves
the object alone. For every object, bounds and value. -/
def BaAssExtendedSpec : Prop :=
  ∀ (b : BA) (start stop step slicelen : Int) (bytes : List Int),
    ((bytes.length : Int) = slicelen → bytes ≠ [] →
      baAssExtended b start stop step slicelen bytes = .ok { b with data := Sequences.storeLoop b.data start step bytes }) ∧
    ((bytes.length : Int) ≠ slicelen → bytes ≠ [] →
      baAssExtended b start stop step slicelen bytes =
        .error (.valueError s!"attempt to assign bytes of size {(bytes.length : Int)} to extended slice of size {slicelen}")) ∧
    (bytes = [] → 0 < b.exports → baAssExtended b start stop step slicelen bytes = .error exportsMsg) ∧
    (bytes = [] → b.exports = 0 → slicelen = 0 → baAssExtended b start stop step slicelen bytes = .ok b)

theorem baAssExtendedSpec_proven : BaAssExtendedSpec := by
  intro b start stop step slicelen bytes
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hl hne
    have h0 : ¬ ((bytes.length : Int) = 0) := by intro e; apply hne; exact List.eq_nil_of_length_eq_zero (by omega)
    unfold baAssExtended
    rw [if_neg h0]
    simp [hl, pure, Except.pure, bind, Except.bind]
  · intro hl hne
    have h0 : ¬ ((bytes.length : Int) = 0) := by intro e; apply hne; exact List.eq_nil_of_length_eq_zero (by omega)
    unfold baAssExtended
    rw [if_neg h0]
    simp [hl, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · intro he hx
    subst he
    simp [baAssExtended, canResize, hx, bind, Except.bind, exportsMsg]
  · intro he hx hz
    subst he; subst hz
    simp [baAssExtended, canResize, hx, bind, Except.bind, pure, Except.pure]

/-- With the slice's own length, `b[s] = v` for an extended slice succeeds on every object and slice,
so with `SliceAssignAgreesNonempty` it does what `list[s] = v` does; `b[s] = v` of a bytearray value
with any other non-zero length raises the `ValueError`. For every object, slice with a step other than
1, and non-empty value. -/
def BaAssSliceExtOk : Prop :=
  ∀ (b : BA) (sl : RangeSlice.Slice) (v : Seq) (st sp se : Int), RangeSlice.sliceUnpack sl = .ok (st, sp, se) →
    se ≠ 1 → v ≠ [] →
    ((v.length : Int) = (RangeSlice.adjustIndices b.size st sp se).2.2 →
      ∃ r, baAssSlice b sl (some (.bytearray v)) = .ok r ∧ r.exports = b.exports ∧
        Sequences.listAssSubscript b.data sl (some (seqData v)) = .ok r.data) ∧
    ((v.length : Int) ≠ (RangeSlice.adjustIndices b.size st sp se).2.2 →
      baAssSlice b sl (some (.bytearray v)) = .error (.valueError
        s!"attempt to assign bytes of size {(v.length : Int)} to extended slice of size {(RangeSlice.adjustIndices b.size st sp se).2.2}"))

theorem assSlice_bytearray_bytes (b : BA) (sl : RangeSlice.Slice) (v : Seq) :
    baAssSlice b sl (some (.bytearray v)) = baAssSlice b sl (some (.bytes v)) := by
  simp only [baAssSlice, assValue_bytes]
  rfl

theorem baAssSliceExtOk_proven : BaAssSliceExtOk := by
  intro b sl v st sp se hu hse hne
  have hlen : (seqData v).length = v.length := by simp [seqData]
  have hne' : seqData v ≠ [] := by intro e; apply hne; simpa [seqData] using e
  have hval : assValue b (some (.bytearray v)) = .ok (some v) := rfl
  refine ⟨?_, ?_⟩
  · intro hl
    have hok : baAssSlice b sl (some (.bytearray v)) =
        .ok { b with data := Sequences.storeLoop b.data (RangeSlice.adjustIndices b.size st sp se).1 se (seqData v) } := by
      unfold baAssSlice
      simp only [bind, Except.bind, hu, hval, pure, Except.pure, hse, ↓reduceIte, Option.getD_some]
      exact (baAssExtendedSpec_proven b _ _ se _ (seqData v)).1 (by rw [hlen]; exact hl) hne'
    refine ⟨_, hok, rfl, ?_⟩
    have := sliceAssignAgreesNonempty_proven b _ sl v hne (by rw [← assSlice_bytearray_bytes]; exact hok)
    exact this
  · intro hl
    unfold baAssSlice
    simp only [bind, Except.bind, hu, hval, pure, Except.pure, hse, ↓reduceIte, Option.getD_some]
    rw [(baAssExtendedSpec_proven b _ _ se _ (seqData v)).2.1 (by rw [hlen]; exact hl) hne', hlen]

/-! ## The other right-hand sides of slice assignment -/

theorem baNew_list (vs : List Nat) (hc : ∀ c ∈ vs, c < 256) (hs : (vs.length : Int) < 2 ^ 46) :
    ∃ r, baNew (some (.list (vs.map (fun c : Nat => Obj.int (c : Int))))) none none = .ok r ∧ r.seq = vs := by
  have hz : ({} : BA).size = 0 := rfl
  obtain ⟨r0, hr0, hd0⟩ : ∃ r0, baResize {} (vs.length : Int) = .ok r0 ∧
      r0.data = List.replicate vs.length uninit := by
    by_cases h0 : vs.length = 0
    · refine ⟨{}, ?_, by simp [h0]⟩
      have := exportRule_proven.1 ({} : BA)
      rw [hz] at this; simpa [h0] using this
    · obtain ⟨r, hr, hd, _⟩ := exportRule_proven.2.2.2 {} vs.length (by omega) rfl hs
      have hne : ¬ ((vs.length : Int) = ({} : BA).size) := by rw [hz]; omega
      simp only [hne, ↓reduceIte, resizedData] at hd
      exact ⟨r, hr, by simp [hd]⟩
  have hf := initFast_ok vs 0 r0 [] hc (by simpa using hd0) rfl
  refine ⟨{ r0 with data := [] ++ seqData vs }, ?_, by simp [BA.seq, seqData_seq]⟩
  have hl : (vs.map (fun c : Nat => Obj.int (c : Int))).length = vs.length := by simp
  rw [baNew, baNewObject_eq, baInit_list, hl, hr0]
  simp only [baInitFast, hf]

/-- `b[s] = v` (:828-940) for the right-hand sides that need `PyByteArray_FromObject` (:856-862): the
slice is unpacked once before the value is looked at; then a list of `int`s in `range(256)` is copied
through `bytearray(list)`, a class with `__buffer__` runs it and then its `__release_buffer__` (as
`_PyByteArray_FromBufferObject` does), and `self` is copied as the first unpacking left it; then the
function runs again on the copy, unpacking the slice a second time. For every heap, `__index__`
slice parts with a non-zero step, and values below 2^46 bytes. -/
def BaAssSubValues : Prop :=
  ∀ (h : H) (st sp se : Option (List Act × Int)), stepOk se →
    let sl : RangeSlice.Slice := ⟨ipVal st, ipVal sp, ipVal se⟩
    let once := fun (h0 : H) => runActs (runActs (runActs h0 (ipActs se)) (ipActs st)) (ipActs sp)
    (∀ vs : List Nat, (∀ c ∈ vs, c < 256) → (vs.length : Int) < 2 ^ 46 →
      baAssSubE (.slice (ipArg st) (ipArg sp) (ipArg se)) (some (.obj (.list (vs.map (fun c : Nat => Obj.int (c : Int))))))
        h = liftBA (fun b => baAssSlice b sl (some (.bytearray vs))) (once (once h))) ∧
    (∀ (acts rel : List Act) (t : Seq), (t.length : Int) < 2 ^ 46 →
      baAssSubE (.slice (ipArg st) (ipArg sp) (ipArg se)) (some (.buf acts (.ok t) rel)) h =
        liftBA (fun b => baAssSlice b sl (some (.bytearray t))) (once (runActs (runActs (once h) acts) rel))) ∧
    baAssSubE (.slice (ipArg st) (ipArg sp) (ipArg se)) (some .me) h =
      liftBA (fun b => baAssSlice b sl (some (.bytearray (once h).ba.seq))) (once (once h))

theorem baAssSubValues_proven : BaAssSubValues := by
  intro h st sp se hok
  dsimp only
  have hu := sliceUnpack_ip st sp se
  obtain ⟨t, ht⟩ : ∃ t, RangeSlice.sliceUnpack ⟨ipVal st, ipVal sp, ipVal se⟩ = .ok t := by
    cases hsu : RangeSlice.sliceUnpack ⟨ipVal st, ipVal sp, ipVal se⟩ with
    | error e => exact absurd hsu (sliceUnpack_ne st sp se hok e)
    | ok t => exact ⟨t, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro vs hc hs
    obtain ⟨r, hr, hseq⟩ := baNew_list vs hc hs
    simp only [baAssSubE, E.bind_app, hu _ hok, ht, Arg.numberCheck, Obj.isNumber, Bool.false_or, Bool.false_eq_true,
      ↓reduceIte, fromObjectE, E.lift_app, hr, Functor.map, Except.map, hseq]
    exact assSliceCore_ip st sp se (some vs) _ hok
  · intro acts rel t hs
    obtain ⟨r, hr⟩ := baFromStringAndSize_ok t.length (by omega) hs
    simp only [baAssSubE, E.bind_app, hu _ hok, ht, Arg.numberCheck, Bool.false_or, Bool.false_eq_true,
      ↓reduceIte, fromObjectE, runCb_app, E.lift_app, hr, E.pure_app]
    exact assSliceCore_ip st sp se (some t) _ hok
  · simp only [baAssSubE, E.bind_app, hu _ hok, ht, Arg.numberCheck, Bool.false_or, Bool.false_eq_true,
      ↓reduceIte, fromObjectE, curSeq]
    exact assSliceCore_ip st sp se (some _) _ hok

/-! ## The remaining paths of `__init__` -/

theorem drop_succ_of (ss : List α) (i : Nat) (x : α) (t : List α) (hd : ss.drop i = x :: t) :
    ss.drop (i + 1) = t := by
  have : ss.drop (i + 1) = (ss.drop i).drop 1 := by simp [List.drop_drop, Nat.add_comm]
  rw [this, hd]
  rfl

theorem initLoop_append (b : BA) (c : Nat) (hc : c < 256) (hx : b.exports = 0) (hs : (b.data.length : Int) + 1 < 2 ^ 46) :
    ∃ r, baInitLoop b [.int c] = .ok r ∧ r.data = b.data ++ [(c : Int)] ∧ r.exports = 0 := by
  obtain ⟨r, hr⟩ := resize_small b (b.size + 1) (by simp [BA.size]; omega) hx (by simp only [BA.size]; omega)
  have hrx := baResize_exports _ _ _ hr
  by_cases hg : b.size + 1 < b.alloc
  · exact ⟨{ b with data := b.data ++ [(c : Int)] }, by simp [baInitLoop, getByte_ok c hc, hg], rfl, hx⟩
  · exact ⟨{ r with data := b.data ++ [(c : Int)] }, by simp [baInitLoop, getByte_ok c hc, hg, hr], rfl,
      by simp [hrx, hx]⟩

/-- The iterator loop of `__init__` (:1142-1172) over items that run no Python code and convert to
bytes (`f c` has `__index__` value `c`): each item is appended, in order, none dropped, and the end of
the iteration returns. -/
theorem initLoop_objs (f : Nat → Obj) (hf : ∀ c, c < 256 → (f c).index? = some (.ok (c : Int))) :
    ∀ (ws : List Nat) (ss : List (List Act × Item)) (i fuel : Nat) (h : H),
      (∀ c ∈ ws, c < 256) → ss.drop i = ws.map (fun c => (([] : List Act), Item.obj (f c))) → ws.length < fuel →
      h.ba.exports = 0 → (h.ba.data.length : Int) + ws.length < 2 ^ 45 →
      ∃ h', initLoopE ss [] none fuel i h = (.ok (), h') ∧ h'.ba.data = h.ba.data ++ seqData ws ∧
        h'.ba.exports = 0 := by
  intro ws
  induction ws with
  | nil =>
    intro ss i fuel h _ hd hfu hx _
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hfu; omega⟩
    refine ⟨h, ?_, by simp [seqData], hx⟩
    simp only [List.map_nil] at hd
    simp [initLoopE, iterStepE, hd, E.bind_app, runCb_app, runActs]
  | cons c rest ih =>
    intro ss i fuel h hc hd hfu hx hs
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hfu; omega⟩
    have hc1 : c < 256 := hc c (by simp)
    simp only [List.map_cons] at hd
    obtain ⟨r, hr, hrd, hrx⟩ := initLoop_append h.ba c hc1 hx (by simp at hs; omega)
    have hg : getByteValueE (Item.toArg (.obj (f c))) h = (.ok c, h) := by
      have hv : ¬ ((c : Int) < 0 ∨ (c : Int) ≥ 256) := by omega
      simp [getByteValueE, Item.toArg, indexE, hf c hc1, E.bind_app, E.lift_app, hv]
    obtain ⟨h', h1, h2, h3⟩ := ih ss (i + 1) k (h.put r) (fun x hx' => hc x (by simp [hx']))
      (drop_succ_of ss i _ _ hd) (by simp at hfu; omega) (by simp [H.put, hrx])
      (by simp [H.put, hrd]; simp at hs; omega)
    refine ⟨h', ?_, by rw [h2]; simp [H.put, hrd, seqData], h3⟩
    simp only [initLoopE, iterStepE, hd, E.bind_app, runCb_app, runActs, List.foldl_nil, E.pure_app]
    simp only [hg, put_ok, hr]
    exact h1

theorem init_reset_empty (h : H) (hx : h.ba.exports = 0) (hz : h.ba.size = 0) :
    ∀ k : E Unit, (do canResizeE; resizeE 0; k : E Unit) h = k h := by
  have hc : canResize h.ba = .ok () := by simp [canResize, hx]
  have hr : baResize h.ba 0 = .ok h.ba := by
    have := exportRule_proven.1 h.ba; rw [hz] at this; exact this
  intro k
  simp [E.bind_app, canResizeE, hc, resizeE, hr, put_self]

/-- More of `bytearray___init___impl`, :982-1182, for an object without exports:
* `encoding` or `errors` without a string argument (also with no argument at all) is the `TypeError`
  of :1006-1012 or :1048-1054, after the object was emptied;
* a list of `int`s whose fast path meets a value outside `range(256)` empties the object again
  (:1121-1122) and raises that value's `ValueError`, also when later items are not `int`s;
* a list of objects that are not exact `int`s (here: classes with `__index__`) leaves the fast path
  (:1115-1117), resizes the object back to 0 and runs the iterator loop, which appends every item;
* a tuple goes through the same fast path as a list;
* a generator (`bytearray(iter(...))`) runs the iterator loop (:1130-1181), which appends every item
  in order and drops none;
* on an empty object, a class with `__buffer__` runs it, and when the object has no exports then the
  bytes it gave become the contents, after which `__release_buffer__` runs; if the callback took a
  view of the object, the resize to the buffer's length raises `BufferError` and the release still
  runs.
For every heap and every value, below 2^45 bytes. -/
def BaInitPaths : Prop :=
  ∀ h : H, h.ba.exports = 0 →
    (∀ (enc : String × Codec) (err : Option String), ∃ h', baInitE none (some enc) err h =
      (.error (.typeError "encoding without a string argument"), h') ∧ h'.ba.data = []) ∧
    (∀ e : String, ∃ h', baInitE none none (some e) h =
      (.error (.typeError "errors without a string argument"), h') ∧ h'.ba.data = []) ∧
    (∀ (v : Int) (enc : String × Codec), ∃ h', baInitE (some (.obj (.int v))) (some enc) none h =
      (.error (.typeError "encoding without a string argument"), h') ∧ h'.ba.data = []) ∧
    (∀ (xs : List Nat) (v : Int) (ys : List Obj), (∀ c ∈ xs, c < 256) → (v < 0 ∨ v ≥ 256) →
      ((xs.length + 1 + ys.length : Nat) : Int) < 2 ^ 45 →
      ∃ h', baInitE (some (.obj (.list (xs.map (fun c : Nat => Obj.int (c : Int)) ++ .int v :: ys)))) none none h =
        (.error (.valueError "byte must be in range(0, 256)"), h') ∧ h'.ba.data = []) ∧
    (∀ vs : List Nat, (∀ c ∈ vs, c < 256) → vs ≠ [] → (vs.length : Int) < 2 ^ 45 →
      ∃ h', baInitE (some (.obj (.list (vs.map (fun c : Nat => Obj.index (c : Int)))))) none none h = (.ok (), h') ∧
        h'.ba.data = seqData vs) ∧
    (∀ vs : List Nat, (∀ c ∈ vs, c < 256) → 0 < vs.length → (vs.length : Int) < 2 ^ 46 →
      ∃ h', baInitE (some (.obj (.tuple (vs.map (fun c : Nat => Obj.int (c : Int)))))) none none h = (.ok (), h') ∧
        h'.ba.data = seqData vs) ∧
    (∀ vs : List Nat, (∀ c ∈ vs, c < 256) → (vs.length : Int) < 2 ^ 45 →
      ∃ h', baInitE (some (.obj (.iter (vs.map (fun c : Nat => Obj.int (c : Int)))))) none none h = (.ok (), h') ∧
        h'.ba.data = seqData vs) ∧
    (h.ba.size = 0 → ∀ (acts rel : List Act) (t : Seq), (t.length : Int) < 2 ^ 46 →
      (runActs h acts).ba.exports = 0 →
      ∃ h2, baInitE (some (.buf acts (.ok t) rel)) none none h = (.ok (), runActs h2 rel) ∧ h2.ba.data = seqData t) ∧
    (h.ba.size = 0 → ∀ (acts rel : List Act) (t : Seq), 0 < (runActs h acts).ba.exports →
      (t.length : Int) ≠ (runActs h acts).ba.size →
      baInitE (some (.buf acts (.ok t) rel)) none none h = (.error exportsMsg, runActs (runActs h acts) rel))

theorem baInitPaths_proven : BaInitPaths := by
  intro h hx
  obtain ⟨h0, hbase, hd0, hx0⟩ := init_reset h hx
  have hs0 : h0.ba.size = 0 := by simp [BA.size, hd0]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro enc err
    refine ⟨h0, ?_, hd0⟩
    unfold baInitE; rw [hbase]
    simp [encNoArg, E.throw_app]
  · intro e
    refine ⟨h0, ?_, hd0⟩
    unfold baInitE; rw [hbase]
    simp [encNoArg, E.throw_app]
  · intro v enc
    refine ⟨h0, ?_, hd0⟩
    unfold baInitE; rw [hbase]
    simp only [encNoArg, Option.isSome_some, ↓reduceIte, E.bind_app, E.throw_app]
  · intro xs v ys hc hv hs
    have hl : ((xs.map (fun c : Nat => Obj.int (c : Int)) ++ .int v :: ys).length : Int) =
        ((xs.length + 1 + ys.length : Nat) : Int) := by simp; omega
    obtain ⟨r, hr, _, _⟩ := exportRule_proven.2.2.2 h0.ba
      (xs.map (fun c : Nat => Obj.int (c : Int)) ++ .int v :: ys).length (by omega) hx0 (by omega)
    obtain ⟨b', hb'⟩ := initFast_fail v ys hv xs 0 r hc
    refine ⟨(h0.put r).put (baReset b'), ?_, rfl⟩
    unfold baInitE; rw [hbase]
    simp only [encNoArg, Bool.false_eq_true, ↓reduceIte, E.pure_app, E.bind_app, Arg.indexCheck, Obj.index?,
      Option.isSome_none, Arg.bufferCheck, Obj.buffer?, resizeE, hr, E.get_app, put_ba, baInitFast, hb',
      E.modify_app, E.throw_app]
  · intro vs hc hne hs
    have hpos : 0 < vs.length := List.length_pos_iff.mpr hne
    obtain ⟨r, hr, _, hxr⟩ := exportRule_proven.2.2.2 h0.ba vs.length (by omega) hx0 (by omega)
    have hrsize : r.size = vs.length := by have := resize_len _ _ _ hr; simp [BA.size]; omega
    have hr0 := baResizeStrategy_proven.1 r (by omega) (by rw [hxr, hx0])
    obtain ⟨c, cs, rfl⟩ : ∃ c cs, vs = c :: cs := by
      cases vs with
      | nil => exact absurd rfl hne
      | cons c cs => exact ⟨c, cs, rfl⟩
    let h2 := (h0.put r).put { r with data := [], alloc := 0, offset := 0 }
    obtain ⟨h', e1, e2, _⟩ := initLoop_objs (fun c : Nat => Obj.index (c : Int)) (fun c _ => rfl) (c :: cs)
      (((c :: cs).map (fun c : Nat => Obj.index (c : Int))).map (fun x => (([] : List Act), Item.obj x)))
      0 (((c :: cs).map (fun c : Nat => Obj.index (c : Int))).map (fun x => (([] : List Act), Item.obj x))).length.succ
      h2 hc (by simp) (by simp) (by simp [h2, H.put, hxr, hx0]) (by simp only [h2, H.put]; simpa using hs)
    refine ⟨h', ?_, by rw [e2]; simp [h2, H.put]⟩
    unfold baInitE; rw [hbase]
    have hsz : ¬ ((h0.put r).ba.size = 0) := by simp [H.put]; omega
    have hr' : baResize h0.ba ((Obj.index (c : Int) :: cs.map (fun c : Nat => Obj.index (c : Int))).length : Int) =
        .ok r := by simpa using hr
    simp only [encNoArg, Bool.false_eq_true, ↓reduceIte, E.pure_app, E.bind_app, Arg.indexCheck, Obj.index?,
      Option.isSome_none, Arg.bufferCheck, Obj.buffer?, resizeE, List.map_cons, hr', E.get_app]
    simp only [baInitFast, baInitFast.go, curSize, E.get_app, hsz, ↓reduceIte, put_ba, hr0, ne_eq,
      not_false_eq_true, E.bind_app]
    have hrs : ¬ r.size = 0 := by omega
    simp only [hrs, not_false_eq_true, ↓reduceIte, E.bind_app, resizeE, put_ba, hr0, E.lift_app, E.pure_app]
    exact e1
  · intro vs hc hpos hs
    obtain ⟨r, hr, hd, _⟩ := exportRule_proven.2.2.2 h0.ba vs.length (by omega) hx0 (by simpa using hs)
    have hne : ¬ ((vs.length : Int) = h0.ba.size) := by omega
    simp only [hne, ↓reduceIte, resizedData, hd0, List.take_nil, List.nil_append, List.length_nil,
      Nat.sub_zero] at hd
    have hl : (vs.length : Int).toNat = vs.length := by simp
    rw [hl] at hd
    have hf := initFast_ok vs 0 r [] hc (by simpa [List.length_map] using hd) rfl
    refine ⟨(h0.put r).put { r with data := [] ++ seqData vs }, ?_, rfl⟩
    unfold baInitE
    rw [hbase]
    simp [E.bind_app, encNoArg, Arg.indexCheck, Obj.index?, Arg.bufferCheck, Obj.buffer?, resizeE, hr, baInitFast,
      List.length_map, hf, put_ba]
  · intro vs hc hs
    obtain ⟨h', e1, e2, _⟩ := initLoop_objs (fun c => Obj.int (c : Int)) (fun c _ => rfl) vs
      ((vs.map (fun c : Nat => Obj.int (c : Int))).map (fun x => (([] : List Act), Item.obj x)))
      0 ((vs.map (fun c : Nat => Obj.int (c : Int))).map (fun x => (([] : List Act), Item.obj x))).length.succ
      h0 hc (by simp) (by simp) hx0 (by simp [hd0]; omega)
    refine ⟨h', ?_, by rw [e2, hd0]; rfl⟩
    unfold baInitE; rw [hbase]
    simp only [encNoArg, Bool.false_eq_true, ↓reduceIte, E.pure_app, E.bind_app, Arg.indexCheck, Obj.index?,
      Option.isSome_none, Arg.bufferCheck, Obj.buffer?]
    simp only [getIterE, E.bind_app, E.lift_app, getIterOr, iterItems?, iterFinish, E.pure_app]
    exact e1
  · intro hz acts rel t hs hx1
    have hb2 := init_reset_empty h hx hz
    let h1 := runActs h acts
    by_cases he : (t.length : Int) = h1.ba.size
    · refine ⟨{ h1 with ba := { h1.ba with data := seqData t } }, ?_, rfl⟩
      have hr : baResize h1.ba t.length = .ok h1.ba := by rw [he]; exact exportRule_proven.1 _
      unfold baInitE; rw [hb2]
      simp [encNoArg, E.bind_app, Arg.indexCheck, Arg.bufferCheck, getBuf_buf, E.attempt_app, resizeE, Buf.len,
        hr, put_self, Buf.read, runCb_app, E.modify_app, h1]
    · obtain ⟨r, hr, _, _⟩ := exportRule_proven.2.2.2 h1.ba t.length (by omega) hx1 hs
      refine ⟨{ h1.put r with ba := { r with data := seqData t } }, ?_, rfl⟩
      unfold baInitE; rw [hb2]
      simp [encNoArg, E.bind_app, Arg.indexCheck, Arg.bufferCheck, getBuf_buf, E.attempt_app, resizeE, Buf.len,
        hr, Buf.read, runCb_app, E.modify_app, h1, put_ba]
  · intro hz acts rel t hx1 hne
    have hb2 := init_reset_empty h hx hz
    let h1 := runActs h acts
    have hr := exportRule_proven.2.1 h1.ba t.length (by omega) hne hx1
    have hl : baResizeLeft h1.ba t.length = h1.ba := by simp [baResizeLeft, show h1.ba.exports > 0 from hx1]
    unfold baInitE; rw [hb2]
    simp [encNoArg, E.bind_app, Arg.indexCheck, Arg.bufferCheck, getBuf_buf, E.attempt_app, resizeE, Buf.len,
      hr, hl, put_self, runCb_app, E.throw_app, h1, exportsMsg]

/-! ## `bytearray_resize_storage` -/

theorem mm_nat (mem : List Int) (dst src cnt : Nat) (h3 : dst + cnt ≤ mem.length) (h4 : src + cnt ≤ mem.length) :
    Sequences.memmove mem (dst : Int) (src : Int) (cnt : Int) =
      .ok (mem.take dst ++ (mem.drop src).take cnt ++ mem.drop (dst + cnt)) := by
  unfold Sequences.memmove
  rw [if_pos ⟨by omega, by omega, by omega, by omega, by omega⟩]
  simp only [Int.toNat_natCast]
  rfl

/-- The memmoves of `bytearray_resize_storage`'s failure path (:240-255) bring the contents back to
`ob_bytes`, for every new size: the first `Py_SIZE` bytes of the buffer are the old contents; and the
first move alone already puts the bytes a successful resize keeps at the start. -/
theorem storage_moves (pre data : List Int) (n : Nat) (hn : 1 ≤ n) (ho : 0 < pre.length) :
    ∃ mem1 mem2,
      Sequences.memmove (pre ++ data) 0 (pre.length : Int) (min (n : Int) (data.length : Int)) = .ok mem1 ∧
      (if (pre.length : Int) ≠ 0 ∧ (n : Int) < data.length then
        Sequences.memmove mem1 n ((pre.length : Int) + n) ((data.length : Int) - n) else .ok mem1) = .ok mem2 ∧
      mem2.take data.length = data ∧ mem1.take (min n data.length) = data.take (min n data.length) := by
  have hdrop : (pre ++ data).drop pre.length = data := List.drop_left' rfl
  by_cases hs : n < data.length
  · have hmin : min (n : Int) (data.length : Int) = ((n : Nat) : Int) := by omega
    rw [hmin]
    have hm := mm_nat (pre ++ data) 0 pre.length n (by simp; omega) (by simp; omega)
    simp only [List.take_zero, List.nil_append, hdrop, Nat.zero_add] at hm
    have hm' : Sequences.memmove (pre ++ data) 0 (pre.length : Int) (n : Int) =
        .ok (data.take n ++ (pre ++ data).drop n) := hm
    have hlA : (data.take n).length = n := by simp; omega
    have hl1 : (data.take n ++ (pre ++ data).drop n).length = pre.length + data.length := by
      simp; omega
    have hm2 := mm_nat (data.take n ++ (pre ++ data).drop n) n (pre.length + n) (data.length - n)
      (by rw [hl1]; omega) (by rw [hl1]; omega)
    have e1 : (data.take n ++ (pre ++ data).drop n).take n = data.take n := List.take_left' hlA
    have hpd : ∀ k, k = pre.length + n → (pre ++ data).drop k = data.drop n := by
      intro k hk; subst hk; simp [List.drop_append]
    have e2 : (data.take n ++ (pre ++ data).drop n).drop (pre.length + n) = data.drop n := by
      rw [List.drop_append, List.drop_eq_nil_of_le (by rw [hlA]; omega), List.nil_append, hlA, List.drop_drop]
      exact hpd _ (by omega)
    have e3 : (data.drop n).take (data.length - n) = data.drop n := List.take_of_length_le (by simp)
    refine ⟨_, (data.take n ++ (pre ++ data).drop n).take n ++
      ((data.take n ++ (pre ++ data).drop n).drop (pre.length + n)).take (data.length - n) ++
      (data.take n ++ (pre ++ data).drop n).drop (n + (data.length - n)), hm', ?_, ?_, ?_⟩
    · rw [if_pos ⟨by omega, by omega⟩]
      have : ((pre.length : Int) + n) = ((pre.length + n : Nat) : Int) := by omega
      have h5 : ((data.length : Int) - n) = ((data.length - n : Nat) : Int) := by omega
      rw [this, h5, hm2]
    · rw [e1, e2, e3, List.take_append_drop]
      exact List.take_left' (by simp)
    · rw [Nat.min_eq_left (by omega)]
      exact List.take_left' hlA
  · have hmin : min (n : Int) (data.length : Int) = ((data.length : Nat) : Int) := by omega
    rw [hmin]
    have hm := mm_nat (pre ++ data) 0 pre.length data.length (by simp) (by simp)
    simp only [List.take_zero, List.nil_append, hdrop, Nat.zero_add,
      List.take_length] at hm
    have hm' : Sequences.memmove (pre ++ data) 0 (pre.length : Int) (data.length : Int) =
        .ok (data ++ (pre ++ data).drop data.length) := hm
    refine ⟨_, data ++ (pre ++ data).drop data.length, hm', ?_, List.take_left' rfl, ?_⟩
    · rw [if_neg (by omega)]
    · rw [Nat.min_eq_right (by omega), List.take_left' rfl, List.take_length]

/-- `bytearray_resize_storage`, :227-260, on the buffer `pre ++ data` (`pre` the bytes before
`ob_start`), for every object with `ob_start` inside the buffer and every new size `n ≥ 1`: when
`_PyBytes_ResizeKeepOnError` fails, the memmoves of the failure path leave `ob_start == ob_bytes`
and the `Py_SIZE` bytes there are the old contents (also for a shrink, where the tail is moved down
after the first move); when it succeeds, `ob_start == ob_bytes` and the first `min(n, size)` bytes,
those the resize keeps, are the old ones. -/
def BaResizeStorageSpec : Prop :=
  ∀ (b : BA) (pre : List Int) (n : Nat) (alloc : Int), (pre.length : Int) = b.offset → 1 ≤ n →
    (∀ e, baStorageCheck b.alloc alloc = .error e →
      ∃ mem, baResizeStorage b (pre ++ b.data) n alloc = (.error e, { b with offset := 0 }, mem)) ∧
    (baStorageCheck b.alloc alloc = .ok () →
      ∃ r mem, baResizeStorage b (pre ++ b.data) n alloc = (.ok (), r, mem) ∧ r.offset = 0 ∧
        r.data.take (min n b.data.length) = b.data.take (min n b.data.length))

theorem baResizeStorageSpec_proven : BaResizeStorageSpec := by
  intro b pre n alloc ho hn
  have hsz : b.size = (b.data.length : Int) := rfl
  by_cases hp : pre.length = 0
  · have hpe : pre = [] := List.eq_nil_of_length_eq_zero hp
    subst hpe
    have h0 : b.offset = 0 := by simp at ho; omega
    have hb : ({ b with offset := 0, data := b.data } : BA) = { b with offset := 0 } := rfl
    refine ⟨?_, ?_⟩
    · intro e he
      refine ⟨b.data, ?_⟩
      simp [baResizeStorage, h0, he, hsz]
    · intro he
      refine ⟨{ b with offset := 0 }, b.data, by simp [baResizeStorage, h0, he, hsz], rfl, rfl⟩
  · have hpos : 0 < pre.length := by omega
    have hoff : b.offset ≠ 0 := by omega
    obtain ⟨mem1, mem2, h1, h2, h3, h4⟩ := storage_moves pre b.data n hn hpos
    rw [ho] at h1 h2
    refine ⟨?_, ?_⟩
    · intro e he
      refine ⟨mem2, ?_⟩
      have h2' : (if b.offset ≠ 0 ∧ (n : Int) < b.size then
          Sequences.memmove mem1 n (b.offset + n) (b.size - n) else .ok mem1) = .ok mem2 := by
        rw [hsz]; exact h2
      simp only [baResizeStorage, hoff, ne_eq, not_false_eq_true, ↓reduceIte, hsz] at *
      rw [h1]
      simp only [he]
      rw [h2']
      simp only [Int.toNat_natCast, h3]
    · intro he
      refine ⟨{ b with offset := 0, data := mem1.take b.data.length }, mem1, ?_, rfl, ?_⟩
      · simp only [baResizeStorage, hoff, ne_eq, not_false_eq_true, ↓reduceIte, hsz]
        rw [h1]
        simp only [he, Int.toNat_natCast]
      · simp only [List.take_take]
        rw [Nat.min_eq_left (Nat.min_le_right _ _)]
        exact h4

/-- `baResizeLeft`, the object a failed `bytearray_resize_lock_held` leaves, is what the mirrored
failure path of `bytearray_resize_storage` leaves whenever the storage step is reached and fails:
for every object without exports, every new size other than 0 and the current one whose strategy
reallocates (`baNewAlloc` gives an allocation within `PyByteArray_SIZE_MAX`), and every failure. -/
def BaResizeLeftMirror : Prop :=
  ∀ (b : BA) (pre : List Int) (n a : Int) (e : PyExc), (pre.length : Int) = b.offset →
    0 < n → n ≠ b.size → b.exports = 0 → baNewAlloc b.alloc b.offset n = some a → ¬ a > baSizeMax →
    baStorageCheck b.alloc a = .error e →
    baResize b n = .error e ∧ baResizeLeft b n = (baResizeStorage b (pre ++ b.data) n a).2.1

theorem baResizeLeftMirror_proven : BaResizeLeftMirror := by
  intro b pre n a e ho hn hne hx hna hmax he
  have hn0 : ¬ n < 0 := by omega
  have hz : n ≠ 0 := by omega
  have hst : baStorageCheck b.alloc a = .error e := he
  refine ⟨?_, ?_⟩
  · simp [baResize, hn0, hne, canResize, hx, baResizeAlloc, hz, hna, hst, bind, Except.bind]
  · obtain ⟨mem, hm⟩ := (baResizeStorageSpec_proven b pre n.toNat a ho (by omega)).1 e hst
    rw [show ((n.toNat : Nat) : Int) = n by omega] at hm
    rw [hm]
    have hc : ¬ (n < 0 ∨ n = b.size ∨ b.exports > 0 ∨ n = 0) := by omega
    simp [baResizeLeft, hc, hna, hmax]

/-! ## `tp_new` and `tp_dealloc` -/

/-- Every export of the object is a view Python code holds. -/
def Balanced (h : H) : Prop := h.ba.exports = h.kept

theorem act_balanced (h : H) (a : Act) (hb : Balanced h) : Balanced (Act.run h a) := by
  unfold Balanced at *
  cases a with
  | set i v =>
    simp only [Act.run]
    split
    · rename_i r hr
      obtain ⟨k, x, e⟩ := baAssIndex_int_shape _ _ _ _ hr
      rw [put_exports, put_kept, e]
      exact hb
    · exact hb
  | resize n =>
    simp only [Act.run]
    split
    · rename_i r hr
      rw [put_exports, put_kept, baResizeMethod_exports _ _ _ hr]
      exact hb
    · rw [put_exports, put_kept, baResizeLeft_exports]
      exact hb
  | delFront k =>
    simp only [Act.run]
    split
    · rename_i r hr
      rw [put_exports, put_kept, assSlice_front_exports _ _ _ hr]
      exact hb
    · exact hb
  | grab => simp only [Act.run, baGetBuffer]; omega
  | drop =>
    simp only [Act.run]
    split
    · exact hb
    · simp only [baReleaseBuffer]; omega

theorem runActs_balanced (h : H) (acts : List Act) (hb : Balanced h) : Balanced (runActs h acts) := by
  induction acts generalizing h with
  | nil => exact hb
  | cons a rest ih =>
    simp only [runActs, List.foldl_cons]
    exact ih _ (act_balanced h a hb)

/-- `bytearray_dealloc`, :1277-1288: with exports it sets `SystemError('deallocated bytearray object has
exported buffers')` and prints it with `PyErr_Print` (to `sys.excepthook`), then drops the `bytes`
object and frees; without exports it prints nothing. From Python the first branch cannot be reached:
from a fresh object, every sequence of Python statements on it (writes, resizes, front deletions,
taking and releasing memoryviews) leaves exactly one export per view Python holds, so when the last
reference goes, which a view would keep, nothing is printed. -/
def BaDeallocSpec : Prop :=
  (∀ e : Int, 0 < e → baDealloc e = ["SystemError: deallocated bytearray object has exported buffers"]) ∧
  (∀ e : Int, e ≤ 0 → baDealloc e = []) ∧
  (∀ acts : List Act, let h := runActs { ba := baNewObject } acts;
    h.ba.exports = h.kept ∧ (h.kept = 0 → baDealloc h.ba.exports = []))

theorem baDeallocSpec_proven : BaDeallocSpec := by
  refine ⟨fun e he => by simp [baDealloc, he], fun e he => by simp [baDealloc, show ¬ e > 0 by omega], ?_⟩
  intro acts
  dsimp only
  have hb := runActs_balanced { ba := baNewObject } acts rfl
  refine ⟨hb, fun hk => ?_⟩
  unfold Balanced at hb
  rw [hb, hk]
  rfl

/-- A new bytearray, before `__init__`, is empty and has no storage and no exports, for every argument
list: `bytearray.__new__(bytearray, b'abc')` is `bytearray(b'')`, its `__alloc__()` is 0 and its
`__sizeof__()` the type's basic size; it iterates to nothing; `__init__()` without arguments leaves it
so; and its export count is balanced, so dropping it prints nothing. A failed allocation is
`MemoryError`. -/
def BaTpNewSpec : Prop :=
  ∀ (args : List Obj) (basic : Int),
    baTpNew args true = .error memoryError ∧
    ∃ b, baTpNew args false = .ok b ∧ b.data = [] ∧ b.exports = 0 ∧ baAllocMethod b = 0 ∧
      baSizeofT basic b = basic ∧ baDrain b 1 { index := 0 } = [] ∧
      baInitE none none none { ba := b } = (.ok (), { ba := b }) ∧ baDealloc b.exports = []

theorem baTpNewSpec_proven : BaTpNewSpec := by
  intro args basic
  refine ⟨rfl, baNewObject, rfl, rfl, rfl, rfl, ?_, rfl, ?_, rfl⟩
  · simp [baSizeofT, baNewObject]
  · have := init_reset_empty { ba := baNewObject } rfl rfl
    unfold baInitE
    rw [this]
    rfl

/-! ## Extended-slice deletion succeeds -/

theorem memmove_len (mem out : List Int) (dst src cnt : Int) (h : Sequences.memmove mem dst src cnt = .ok out) :
    out.length = mem.length := by
  unfold Sequences.memmove at h
  split at h
  · rename_i hc
    simp only [Except.ok.injEq] at h
    subst h
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  · simp at h

theorem memmove_some (mem : List Int) (dst src cnt : Int) (h0 : 0 ≤ dst) (h1 : 0 ≤ src) (h2 : 0 ≤ cnt)
    (h3 : dst + cnt ≤ mem.length) (h4 : src + cnt ≤ mem.length) :
    ∃ out, Sequences.memmove mem dst src cnt = .ok out := by
  unfold Sequences.memmove
  rw [if_pos ⟨h0, h1, h2, h3, h4⟩]
  exact ⟨_, rfl⟩

/-- The compaction loop of an extended deletion runs `m` more rounds and stays inside the buffer, when
the cursor's last round is before `stop ≤ size`. -/
theorem delLoop_ok (size step stop : Int) (hst : 0 < step) (hstop : stop ≤ size) :
    ∀ (m fuel : Nat) (mem : List Int) (cur i : Int), (mem.length : Int) = size → 0 ≤ i → i ≤ cur →
      stop ≤ cur + (m : Int) * step → (0 < m → cur + ((m : Int) - 1) * step < stop) → m < fuel →
      ∃ out, Sequences.delLoop size step stop fuel mem cur i = .ok out ∧ (out.length : Int) = size := by
  intro m
  induction m with
  | zero =>
    intro fuel mem cur i hl _ _ hend _ hf
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    refine ⟨mem, ?_, hl⟩
    unfold Sequences.delLoop
    rw [if_neg (by simp at hend; omega)]
  | succ m ih =>
    intro fuel mem cur i hl hi hic hend hlast hf
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    have hmul : ((m + 1 : Nat) : Int) * step = (m : Int) * step + step := by
      rw [show ((m + 1 : Nat) : Int) = (m : Int) + 1 by omega, Int.add_mul, Int.one_mul]
    have hmul2 : ((m : Int) - 1) * step = (m : Int) * step - step := by rw [Int.sub_mul, Int.one_mul]
    have hmul3 : (((m + 1 : Nat) : Int) - 1) * step = (m : Int) * step := by
      rw [show ((m + 1 : Nat) : Int) - 1 = (m : Int) by omega]
    have hm0 : 0 ≤ (m : Int) * step := Int.mul_nonneg (by omega) (by omega)
    have hl0 := hlast (by omega)
    rw [hmul3] at hl0
    have hc : cur < stop := by omega
    obtain ⟨mem1, hm1⟩ := memmove_some mem (cur - i) (cur + 1)
      (if cur + step ≥ size then size - cur - 1 else step - 1) (by omega) (by omega) (by split <;> omega)
      (by split <;> omega) (by split <;> omega)
    have hl1 := memmove_len _ _ _ _ _ hm1
    obtain ⟨out, ho, hol⟩ := ih k mem1 (cur + step) (i + 1) (by rw [hl1]; exact hl) (by omega) (by omega)
      (by rw [hmul] at hend; omega) (fun _ => by omega) (by omega)
    refine ⟨out, ?_, hol⟩
    unfold Sequences.delLoop
    rw [if_pos hc]
    simp only [hm1]
    exact ho

theorem adjustOne_pos (x n se : Int) (hn : 0 ≤ n) (hse : 0 < se) :
    0 ≤ RangeSlice.adjustOne x n se ∧ RangeSlice.adjustOne x n se ≤ n := by
  dsimp only [RangeSlice.adjustOne]
  split
  · split <;> (try split) <;> omega
  · split <;> (try split) <;> omega

theorem adjustOne_neg (x n se : Int) (hn : 0 ≤ n) (hse : se < 0) :
    -1 ≤ RangeSlice.adjustOne x n se ∧ RangeSlice.adjustOne x n se ≤ n - 1 := by
  dsimp only [RangeSlice.adjustOne]
  split
  · split <;> (try split) <;> omega
  · split <;> (try split) <;> omega

/-- The facts `PySlice_AdjustIndices` gives about a non-empty slice. -/
theorem adjust_pos (n st sp se : Int) (hn : 0 ≤ n) (hse : 0 < se)
    (hL : 0 < (RangeSlice.adjustIndices n st sp se).2.2) :
    0 ≤ (RangeSlice.adjustIndices n st sp se).1 ∧ (RangeSlice.adjustIndices n st sp se).2.1 ≤ n ∧
    (RangeSlice.adjustIndices n st sp se).1 + ((RangeSlice.adjustIndices n st sp se).2.2 - 1) * se <
      (RangeSlice.adjustIndices n st sp se).2.1 ∧
    (RangeSlice.adjustIndices n st sp se).2.1 ≤
      (RangeSlice.adjustIndices n st sp se).1 + (RangeSlice.adjustIndices n st sp se).2.2 * se := by
  have ha := adjustOne_pos st n se hn hse
  have hb := adjustOne_pos sp n se hn hse
  unfold RangeSlice.adjustIndices at hL ⊢
  simp only [show ¬ se < 0 by omega, ↓reduceIte] at hL ⊢
  generalize RangeSlice.adjustOne st n se = a at *
  generalize RangeSlice.adjustOne sp n se = b at *
  by_cases hab : a < b
  · simp only [hab, ↓reduceIte] at hL ⊢
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
    have h1 := Int.ediv_mul_le (b - a - 1) (show se ≠ 0 by omega)
    have h2 := Int.lt_ediv_add_one_mul_self (b - a - 1) hse
    refine ⟨ha.1, hb.2, ?_, ?_⟩
    · rw [Int.add_sub_cancel]; omega
    · omega
  · simp only [hab, ↓reduceIte] at hL; omega

theorem adjust_neg (n st sp se : Int) (hn : 0 ≤ n) (hse : se < 0)
    (hL : 0 < (RangeSlice.adjustIndices n st sp se).2.2) :
    (RangeSlice.adjustIndices n st sp se).1 ≤ n - 1 ∧ -1 ≤ (RangeSlice.adjustIndices n st sp se).2.1 ∧
    (RangeSlice.adjustIndices n st sp se).2.1 <
      (RangeSlice.adjustIndices n st sp se).1 + ((RangeSlice.adjustIndices n st sp se).2.2 - 1) * se ∧
    (RangeSlice.adjustIndices n st sp se).1 + (RangeSlice.adjustIndices n st sp se).2.2 * se ≤
      (RangeSlice.adjustIndices n st sp se).2.1 := by
  have ha := adjustOne_neg st n se hn hse
  have hb := adjustOne_neg sp n se hn hse
  unfold RangeSlice.adjustIndices at hL ⊢
  simp only [hse, ↓reduceIte] at hL ⊢
  generalize RangeSlice.adjustOne st n se = a at *
  generalize RangeSlice.adjustOne sp n se = b at *
  by_cases hab : b < a
  · simp only [hab, ↓reduceIte] at hL ⊢
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
    have h1 := Int.ediv_mul_le (a - b - 1) (show -se ≠ 0 by omega)
    have h2 := Int.lt_ediv_add_one_mul_self (a - b - 1) (show 0 < -se by omega)
    have e1 : ((a - b - 1) / -se + 1 - 1) * se = -((a - b - 1) / -se * -se) := by
      rw [Int.add_sub_cancel, Int.mul_neg, Int.neg_neg]
    have e2 : ((a - b - 1) / -se + 1) * se = -(((a - b - 1) / -se + 1) * -se) := by
      rw [Int.mul_neg, Int.neg_neg]
    refine ⟨ha.2, hb.1, ?_, ?_⟩
    · rw [e1]; omega
    · rw [e2]; omega
  · simp only [hab, ↓reduceIte] at hL; omega

/-- `del b[s]` for an extended slice of an object without exports succeeds for every slice whose
step is not 1 (and so, with `SliceDeleteAgrees`, does what `del list[s]` does): the compaction loop
of :893-922 and the tail move stay inside the buffer, and the shrink of :926 succeeds. With exports it
is `BufferError` (`BaAssExtendedSpec`). For every object below 2^45 bytes. -/
def BaAssSliceDelOk : Prop :=
  ∀ (b : BA) (sl : RangeSlice.Slice) (st sp se : Int), RangeSlice.sliceUnpack sl = .ok (st, sp, se) →
    se ≠ 1 → b.exports = 0 → b.size < 2 ^ 45 →
    ∃ r, baAssSlice b sl none = .ok r ∧ Sequences.listAssSubscript b.data sl none = .ok r.data

theorem delExtended_ok (mem : List Int) (a c se L : Int) (hse : se ≠ 0) (hL : 0 < L)
    (hpos : 0 < se → 0 ≤ a ∧ c ≤ mem.length ∧ a + (L - 1) * se < c ∧ c ≤ a + L * se)
    (hneg : se < 0 → a ≤ mem.length - 1 ∧ -1 ≤ c ∧ c < a + (L - 1) * se ∧ a + L * se ≤ c) :
    ∃ out, Sequences.delExtended mem a c se L = .ok out := by
  unfold Sequences.delExtended
  simp only [bind, Except.bind]
  have hLn : ((L.toNat : Nat) : Int) = L := by omega
  by_cases hs : se < 0
  · simp only [hs, ↓reduceIte]
    obtain ⟨h1, h2, h3, h4⟩ := hneg hs
    have hm2 : L * -se = -(L * se) := Int.mul_neg _ _
    have hm : ((L.toNat : Nat) : Int) * -se = -(L * se) := by rw [hLn, hm2]
    have e0 : (L - 1) * se = L * se - se := by rw [Int.sub_mul, Int.one_mul]
    have e1 : se * (L - 1) = L * se - se := by rw [Int.mul_sub, Int.mul_one, Int.mul_comm]
    have hk : 1 * -se ≤ L * -se := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ L by omega) (by omega)
    have hk2 : (L - 1) * 1 ≤ (L - 1) * -se := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ -se by omega) (by omega)
    have hk3 : (L - 1) * -se = -((L - 1) * se) := Int.mul_neg _ _
    simp only [Int.one_mul, Int.mul_one] at hk hk2
    obtain ⟨out, ho, hol⟩ := delLoop_ok mem.length (-se) (a + 1) (by omega) (by omega) L.toNat (L.toNat + 1) mem
      (a + 1 + se * (L - 1) - 1) 0 rfl (Int.le_refl _) (by omega)
      (by rw [hm]; omega) (fun _ => by rw [Int.sub_mul, Int.one_mul, hLn]; omega) (by omega)
    simp only [ho]
    by_cases hcur : a + 1 + se * (L - 1) - 1 + L * -se < (mem.length : Int)
    · rw [if_pos hcur]
      obtain ⟨out2, ho2⟩ := memmove_some out (a + 1 + se * (L - 1) - 1 + L * -se - L)
        (a + 1 + se * (L - 1) - 1 + L * -se) ((mem.length : Int) - (a + 1 + se * (L - 1) - 1 + L * -se))
        (by omega) (by omega) (by omega) (by rw [hol]; omega) (by rw [hol]; omega)
      simp only [ho2]
      exact ⟨_, rfl⟩
    · rw [if_neg hcur]
      exact ⟨_, rfl⟩
  · simp only [hs, ↓reduceIte]
    have hp : 0 < se := by omega
    obtain ⟨h1, h2, h3, h4⟩ := hpos hp
    have hLs : L * 1 ≤ L * se := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ se by omega) (by omega)
    have hm1 : 0 ≤ (L - 1) * se := Int.mul_nonneg (by omega) (by omega)
    simp only [Int.mul_one] at hLs
    obtain ⟨out, ho, hol⟩ := delLoop_ok mem.length se c hp h2 L.toNat (L.toNat + 1) mem a 0 rfl (Int.le_refl _) h1
      (by rw [hLn]; exact h4) (fun _ => by rw [hLn]; omega) (by omega)
    simp only [ho]
    by_cases hcur : a + L * se < (mem.length : Int)
    · rw [if_pos hcur]
      obtain ⟨out2, ho2⟩ := memmove_some out (a + L * se - L) (a + L * se) ((mem.length : Int) - (a + L * se))
        (by omega) (by omega) (by omega) (by rw [hol]; omega) (by rw [hol]; omega)
      simp only [ho2]
      exact ⟨_, rfl⟩
    · rw [if_neg hcur]
      exact ⟨_, rfl⟩

theorem sliceUnpack_step_ne (sl : RangeSlice.Slice) (st sp se : Int)
    (hu : RangeSlice.sliceUnpack sl = .ok (st, sp, se)) : se ≠ 0 := by
  unfold RangeSlice.sliceUnpack at hu
  cases hs : sl.step with
  | none => simp [hs, bind, Except.bind, pure, Except.pure] at hu; omega
  | some v =>
    simp only [hs, bind, Except.bind, pure, Except.pure] at hu
    by_cases hz : RangeSlice.clampSsize v = 0
    · simp [hz, throw, throwThe, MonadExceptOf.throw] at hu
    · simp only [hz, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hu
      have : ssizeMax = 9223372036854775807 := by decide
      split at hu <;> omega

theorem baAssSliceDelOk_proven : BaAssSliceDelOk := by
  intro b sl st sp se hu hse1 hx hs
  have hse0 := sliceUnpack_step_ne sl st sp se hu
  have hn : 0 ≤ b.size := by simp [BA.size]
  have hsz : b.size = (b.data.length : Int) := rfl
  obtain ⟨r, hr⟩ : ∃ r, baAssSlice b sl none = .ok r := by
    unfold baAssSlice
    simp only [bind, Except.bind, hu, pure, Except.pure]
    have hval : assValue b none = .ok none := rfl
    simp only [hval, Option.getD_none, hse1, ↓reduceIte]
    generalize hadj : RangeSlice.adjustIndices b.size st sp se = t
    obtain ⟨a, c, L⟩ := t
    simp only
    have hL0 := PyLean.Sequences.adjust_len_nonneg b.size st sp se
    rw [hadj] at hL0
    simp only at hL0
    have hsd : seqData [] = ([] : List Int) := rfl
    rw [hsd]
    by_cases hz : L = 0
    · subst hz
      exact ⟨b, (baAssExtendedSpec_proven b _ _ se 0 []).2.2.2 rfl hx rfl⟩
    · have hLp : 0 < L := by omega
      have hp := fun h => adjust_pos b.size st sp se hn h (by rw [hadj]; exact hLp)
      have hq := fun h => adjust_neg b.size st sp se hn h (by rw [hadj]; exact hLp)
      rw [hadj] at hp hq
      simp only at hp hq
      have hstop : (if (se < 0 ∧ a < c) ∨ (se > 0 ∧ a > c) then a else c) = c := by
        by_cases hsg : 0 < se
        · obtain ⟨_, _, h3, _⟩ := hp hsg
          have : 0 ≤ (L - 1) * se := Int.mul_nonneg (by omega) (by omega)
          rw [if_neg (by omega)]
        · obtain ⟨_, _, h3, _⟩ := hq (by omega)
          have : (L - 1) * se ≤ 0 := by
            have := Int.mul_le_mul_of_nonneg_left (show se ≤ 0 by omega) (show 0 ≤ L - 1 by omega)
            simpa using this
          rw [if_neg (by omega)]
      rw [hstop]
      have hLsize : L ≤ b.size := by
        by_cases hsg : 0 < se
        · obtain ⟨h1, h2, h3, _⟩ := hp hsg
          have := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ se by omega) (show 0 ≤ L - 1 by omega)
          simp at this; omega
        · obtain ⟨h1, h2, h3, _⟩ := hq (by omega)
          have := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ -se by omega) (show 0 ≤ L - 1 by omega)
          rw [Int.mul_neg] at this
          simp at this; omega
      obtain ⟨mem, hmem⟩ := delExtended_ok b.data a c se L hse0 hLp
        (fun h => by rw [← hsz]; exact hp h) (fun h => by rw [← hsz]; exact hq h)
      obtain ⟨r1, hr1⟩ := resize_small b (b.size - L) (by omega) hx (by omega)
      refine ⟨{ r1 with data := mem }, ?_⟩
      unfold baAssExtended
      simp [canResize, hx, hz, hmem, hr1, bind, Except.bind, pure, Except.pure]
  exact ⟨r, hr, sliceDeleteAgrees_proven b r sl hr⟩

/-! ## The documented `NULL` check of `PyByteArray_Size` -/

/-- Doc/c-api/bytearray.rst:76-78: `PyByteArray_Size` returns the size "after checking for a `NULL`
pointer", so `NULL` gives an error the caller can see rather than undefined behaviour. Refuted: the body
(:208-215) only `assert`s, and a release build dereferences `NULL` (a segmentation fault on 3.15.2 and
main). -/
def SizeChecksNull : Prop :=
  ∀ e : PyExc, baSizeC none = .error e → e.className ≠ "CUndefinedBehaviour"

theorem sizeChecksNull_refuted : ¬ SizeChecksNull := by
  intro hp
  exact hp _ rfl rfl

end PyLean.BytesObj.Bytes
