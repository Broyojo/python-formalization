import PyLean.BytesObj.Bytes.Specs3

/-!
What each caller does when a callback raises. The C code does not treat these alike, and the
differences are the content: `PyNumber_AsSsize_t` errors propagate from `find` and vanish in `in`, a
`TypeError` falls through in the constructors, `join` runs the iterator to its end before looking at
an item, and only some callers ask for a length hint.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-- The objects a generator of `vals` yields. -/
def asItems (vals : Seq) : List Obj := vals.map fun (c : Nat) => Obj.int (c : Int)

theorem asItems_mapM (vals : Seq) (h : ∀ c ∈ vals, c < 256) :
    (asItems vals).mapM getByteValue = .ok vals := by
  induction vals with
  | nil => rfl
  | cons c rest ih =>
    have h1 := getByte_ok c (h c (by simp))
    have h2 := ih fun x hx => h x (by simp [hx])
    simp only [asItems, List.map_cons, List.mapM_cons, h1, bind, Except.bind, pure, Except.pure] at h2 ⊢
    simp [h2]

/-! ## `__index__` -/

/-- `x in b` reports what `__index__` raised, as `b.find(x)` does: refuted, `_Py_bytes_contains`
clears it and tries the buffer protocol. -/
def ContainsKeepsIndexError : Prop :=
  ∀ (s : Seq) (e : PyExc), bytesContains s (.indexRaises e) = .error e

theorem containsKeepsIndexError_refuted : ¬ ContainsKeepsIndexError := by
  intro h
  have := h [] (.valueError "boom")
  simp [bytesContains, getBuffer, Obj.buffer?, Obj.index?, notBytesLike] at this

/-- What each caller does with an exception from `__index__`: `find`, `index`, `count`, the item
conversions and the `o x X` conversions pass it on, unchanged. `in` loses it (the refutation above);
`bytes(x)` and `bytearray(x)` fall through to the next protocol on `TypeError` only; `%c` passes it on
too, and only `%d` and its kin replace a `TypeError`, by the format's message. -/
def IndexRaisesRules : Prop :=
  ∀ (s : Seq) (e : PyExc) (st en : Option Int) (fwd : Bool) (fs : FS) (fl : Fl) (prec : Int) (t : Nat),
    let x := Obj.indexRaises e
    bytesFindObj s x st en fwd = .error e ∧ bytesIndexObj s x st en fwd = .error e ∧
    bytesCountObj s x st en = .error e ∧
    bytesContains s x = .error (notBytesLike x) ∧
    getByteValue x = .error e ∧ byteItem x = .error e ∧
    bytesNew (some x) none none =
      .error (if isTypeError e then .typeError "cannot convert 'BIdxRaises' object to bytes" else e) ∧
    (baInit {} (some x) none none).2 =
      some (if isTypeError e then .typeError "cannot convert 'BIdxRaises' object to bytearray" else e) ∧
    byteConverter fs x = .error e ∧
    (isTypeError e = false → formatLong fs x fl prec t = .error e)

theorem indexRaisesRules_proven : IndexRaisesRules := by
  intro s e st en fwd fs fl prec t
  dsimp only
  have hc0 : canResize ({} : BA) = .ok () := rfl
  have hr0 : baResize {} 0 = .ok {} := rfl
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, fun h => ?_⟩
  · cases h : isTypeError e
    · simp [bytesNew, Obj.index?, h]
    · simp [bytesNew, Obj.index?, h, bytesFromObject, Obj.buffer?, getIterOr, iterItems?, Obj.typeName,
        bind, Except.bind, pure, Except.pure]
      rfl
  · cases h : isTypeError e
    · simp [baInit, hc0, hr0, bind, Except.bind, Obj.index?, h]
    · simp [baInit, hc0, hr0, bind, Except.bind, Obj.index?, h, Obj.buffer?, getIterOr, iterItems?,
        Obj.typeName]
      rfl
  · simp only [formatLong, Obj.longValue?, Obj.isNumber]
    by_cases hc : t = 111 ∨ t = 120 ∨ t = 88
    · simp [hc, Obj.index?, h]
    · simp [hc, numberLong, Obj.index?, h]

/-- The value of `__index__` is read before anything else in the mutating methods, and its exception
leaves the object as it was (the methods return an error, no new object). -/
def MutatorsIndexRaises : Prop :=
  ∀ (b : BA) (e : PyExc) (i : Int), ssizeMin ≤ i → i ≤ ssizeMax →
    let x := Obj.indexRaises e
    baAppend b x = .error e ∧ baInsert b i x = .error e ∧ baRemove b x = .error e ∧
    baAssIndex b i (some x) = .error e ∧ baSetItemRaw b i (some x) = .error e

theorem mutatorsIndexRaises_proven : MutatorsIndexRaises := by
  intro b e i h1 h2
  dsimp only
  have hs : Sequences.subIndex i = .ok i := by
    simp only [Sequences.subIndex, Sequences.asSsizeExc]
    rw [if_pos ⟨h1, h2⟩]
  have ha : Sequences.asSsize i = .ok i := by
    simp only [Sequences.asSsize]
    first
      | rw [if_pos ⟨h1, h2⟩]
      | simp [Sequences.asSsizeExc, h1, h2]
  refine ⟨rfl, ?_, rfl, ?_, rfl⟩
  · simp only [baInsert, ha, bind, Except.bind]
    rfl
  · simp only [baAssIndex, hs, bind, Except.bind]
    rfl

/-! ## Iterators -/

/-- A failing iterator: `bytes(it)` and `extend` check each item as it comes, so with good items the
iterator's exception comes last, and `extend` writes nothing. `join` runs the iterator to its end
first, so the exception wins over a bad item, where `bytes` reports the item. For a generator the
exception is what its caller sees, `genRaised e`: a `StopIteration` raised in the generator is
`RuntimeError('generator raised StopIteration')` (PEP 479). For a C iterator (`map`) a
`StopIteration` is the normal end, so `bytes(it)` and `extend` give what the plain iterator of the
same items gives, and any other exception is the result. -/
def IterRaisesRules : Prop :=
  ∀ (vals : Seq) (e : PyExc), (∀ c ∈ vals, c < 256) →
    let xs := asItems vals
    bytesNew (some (.iterRaises xs e)) none none = .error (genRaised e) ∧
    (∀ (sep : Seq) (bad : List Obj), pyBytesJoin (.bytes sep) (.iterRaises bad e) = .error (genRaised e)) ∧
    (∀ self : BA, baExtend self (.iterRaises xs e) = .error (genRaised e)) ∧
    (excMatches e "StopIteration" = false → bytesNew (some (.mapRaises xs e)) none none = .error e ∧
      ∀ self : BA, baExtend self (.mapRaises xs e) = .error e) ∧
    (excMatches e "StopIteration" = true → bytesNew (some (.mapRaises xs e)) none none = .ok vals ∧
      ∀ self : BA, baExtend self (.mapRaises xs e) = baExtend self (.iter xs)) ∧
    (∀ (self : BA) (v : Int), v < 0 → ssizeMin ≤ v →
      baExtend self (.iterRaises (.int v :: xs) e) = .error (.valueError "byte must be in range(0, 256)")) ∧
    (∀ v : Int, v < 0 → ssizeMin ≤ v →
      bytesNew (some (.iterRaises (.int v :: xs) e)) none none =
        .error (.valueError "bytes must be in range(0, 256)"))

theorem clamp_neg (v : Int) (h1 : v < 0) (h2 : ssizeMin ≤ v) : clampSsize v = v := by
  unfold clampSsize ssizeMax at *
  omega

theorem iterRaisesRules_proven : IterRaisesRules := by
  intro vals e hv
  dsimp only
  have hb : bytesFromItems (asItems vals) = .ok vals := items_ok vals hv
  have hba := asItems_mapM vals hv
  have hbuf : bytesSizeCheck 32 = .ok () := by decide
  have hw : writerCreate 64 false = .ok { overallocate := true, size := 64 } := by decide
  refine ⟨?_, fun sep bad => ?_, fun self => ?_, fun he => ⟨?_, fun self => ?_⟩, fun he => ⟨?_, fun self => ?_⟩,
    fun self v h1 h2 => ?_, fun v h1 h2 => ?_⟩
  · simp [bytesNew, Obj.index?, bytesFromObject, Obj.buffer?, iterItems?, hb, getIterOr, lengthHint,
      iterFinish, hw, bind, Except.bind, pure, Except.pure]
  · have hm : mallocFails 64 = false := by decide
    simp [pyBytesJoin, stringlibJoin, sequenceFast, getIterOr, iterItems?, lengthHint, iterFinish, hm,
      bind, Except.bind]
  · simp [baExtend, Obj.buffer?, getIterOr, iterItems?, lengthHint, hbuf, hba, iterFinish, bind,
      Except.bind, Except.mapError]
  · simp [bytesNew, Obj.index?, bytesFromObject, Obj.buffer?, iterItems?, hb, getIterOr, lengthHint,
      iterFinish, hw, he, bind, Except.bind, pure, Except.pure]
  · simp [baExtend, Obj.buffer?, getIterOr, iterItems?, lengthHint, hbuf, hba, iterFinish, he, bind,
      Except.bind, Except.mapError]
  · simp [bytesNew, Obj.index?, bytesFromObject, Obj.buffer?, iterItems?, hb, getIterOr, lengthHint,
      iterFinish, hw, he, bind, Except.bind, pure, Except.pure]
  · simp [baExtend, Obj.buffer?, getIterOr, iterItems?, lengthHint, iterFinish, he]
  · have hg := getByte_bad v (Or.inl h1)
    simp [baExtend, Obj.buffer?, getIterOr, iterItems?, lengthHint, hbuf, hg, bind, Except.bind,
      Except.mapError, List.mapM_cons]
  · have hc := clamp_neg v h1 h2
    have hi : byteItem (.int v) = .error (.valueError "bytes must be in range(0, 256)") := by
      simp [byteItem, asSsizeClamp, Obj.index?, hc, h1, bind, Except.bind, pure, Except.pure]
      rfl
    simp [bytesNew, Obj.index?, bytesFromObject, Obj.buffer?, iterItems?, getIterOr, lengthHint,
      hw, bytesFromItems, hi, bind, Except.bind, pure, Except.pure]

/-- `__length_hint__`: `bytes(it)`, `extend` and `join` ask, before the first item, so a raising hint
wins over a bad item; a `TypeError` from it is ignored and a negative value is `ValueError`; a good
hint changes nothing, and one past what a bytes can hold is the writer's `OverflowError`.
`bytearray(it)` does not ask. -/
def HintRules : Prop :=
  ∀ (vals : Seq) (e : PyExc) (v : Int), (∀ c ∈ vals, c < 256) →
    let xs := asItems vals
    (isTypeError e = true →
      bytesNew (some (.iterHint xs (.error e))) none none = .ok vals) ∧
    (isTypeError e = false → ∀ bad : List Obj,
      bytesNew (some (.iterHint bad (.error e))) none none = .error e ∧
      (∀ self : BA, baExtend self (.iterHint bad (.error e)) = .error e) ∧
      (∀ sep : Seq, pyBytesJoin (.bytes sep) (.iterHint bad (.error e)) = .error e)) ∧
    (ssizeMin ≤ v → v < 0 → ∀ bad : List Obj,
      bytesNew (some (.iterHint bad (.ok v))) none none =
        .error (.valueError "BHint.__length_hint__() must return a non-negative int")) ∧
    (0 ≤ v → v + 33 < 2 ^ 47 → bytesNew (some (.iterHint xs (.ok v))) none none = .ok vals) ∧
    (baSizeMax < v → v ≤ ssizeMax → ∀ bad : List Obj, bytesNew (some (.iterHint bad (.ok v))) none none =
      .error (.overflowError "byte string is too large"))

theorem hintRules_proven : HintRules := by
  intro vals e v hv
  dsimp only
  have hb : bytesFromItems (asItems vals) = .ok vals := items_ok vals hv
  have hw : writerCreate 64 false = .ok { overallocate := true, size := 64 } := by decide
  refine ⟨fun h => ?_, fun h bad => ⟨?_, fun self => ?_, fun sep => ?_⟩, fun h1 h2 bad => ?_, fun h1 h2 => ?_,
    fun h1 h2 bad => ?_⟩
  · simp [bytesNew, Obj.index?, bytesFromObject, Obj.buffer?, iterItems?, hb, getIterOr, lengthHint, h,
      iterFinish, hw, bind, Except.bind, pure, Except.pure]
  · simp [bytesNew, Obj.index?, bytesFromObject, Obj.buffer?, iterItems?, getIterOr, lengthHint, h, bind,
      Except.bind, pure, Except.pure]
  · simp [baExtend, Obj.buffer?, getIterOr, iterItems?, lengthHint, h, bind, Except.bind]
  · simp [pyBytesJoin, stringlibJoin, sequenceFast, getIterOr, iterItems?, lengthHint, h, bind, Except.bind]
  · have h3 : ¬ (v < ssizeMin ∨ v > ssizeMax) := by unfold ssizeMax; omega
    simp [bytesNew, Obj.index?, bytesFromObject, Obj.buffer?, iterItems?, getIterOr, lengthHint, h3, h2,
      bind, Except.bind, pure, Except.pure]
    rfl
  · have h3 : ¬ (v < ssizeMin ∨ v > ssizeMax) := by
      unfold ssizeMin ssizeMax
      omega
    have h4 : ¬ v < 0 := by omega
    obtain ⟨n, rfl⟩ : ∃ n : Nat, v = n := ⟨v.toNat, by omega⟩
    obtain ⟨w, hw2, _⟩ := writerCreate_ok n h2
    simp [bytesNew, Obj.index?, bytesFromObject, Obj.buffer?, iterItems?, hb, getIterOr, lengthHint, h3, h4,
      hw2, iterFinish, bind, Except.bind, pure, Except.pure]
  · have hmax : baSizeMax = 9223372036854775774 := by decide
    have hmin : ssizeMin < 0 := by decide
    have h3 : ¬ (v < ssizeMin ∨ v > ssizeMax) := by omega
    have h4 : ¬ v < 0 := by omega
    have hc : writerCreate v false = .error (.overflowError "byte string is too large") := by
      have h5 : ¬ (v = 0) := by omega
      have h6 : v > ssizeMax - bytesObjectSize := by
        have : baSizeMax = ssizeMax - bytesObjectSize := rfl
        omega
      have h7 : ¬ (v ≤ smallBufferSize) := by rw [small_val]; omega
      have h8 : bytesSizeCheck v = .error (.overflowError "byte string is too large") := by
        unfold bytesSizeCheck
        rw [if_neg h5, if_pos h6]
      have h9 : v ≥ 1 := by omega
      simp [writerCreate, h4, h9, writerResizeRaw, writerAllocated, h7, writerObjResize, h8]
    simp [bytesNew, Obj.index?, bytesFromObject, Obj.buffer?, iterItems?, getIterOr, lengthHint, h3, h4,
      hc, bind, Except.bind, pure, Except.pure]

/-- `__iter__` raising: every caller keeps a non-`TypeError` and replaces a `TypeError` by its own
message. `__bytes__` raising: `bytes(x)` and `%b` pass it on, and `bytearray(x)` never calls it. -/
def CallRaisesRules : Prop :=
  ∀ (e : PyExc) (sep : Seq) (self : BA),
    bytesNew (some (.iterCallRaises e)) none none =
      .error (if isTypeError e then .typeError "cannot convert 'BIterCall' object to bytes" else e) ∧
    pyBytesJoin (.bytes sep) (.iterCallRaises e) =
      .error (if isTypeError e then .typeError "can only join an iterable" else e) ∧
    baExtend self (.iterCallRaises e) =
      .error (if isTypeError e then .typeError "can't extend bytearray with BIterCall" else e) ∧
    (baInit {} (some (.iterCallRaises e)) none none).2 =
      some (if isTypeError e then .typeError "cannot convert 'BIterCall' object to bytearray" else e) ∧
    bytesNew (some (.dunderRaises e)) none none = .error e ∧
    (∀ fs : FS, formatObj fs (.dunderRaises e) = .error e) ∧
    (baInit {} (some (.dunderRaises e)) none none).2 =
      some (.typeError "cannot convert 'BDunRaises' object to bytearray")

theorem callRaisesRules_proven : CallRaisesRules := by
  intro e sep self
  have hc0 : canResize ({} : BA) = .ok () := rfl
  have hr0 : baResize {} 0 = .ok {} := rfl
  refine ⟨?_, ?_, ?_, ?_, rfl, fun _ => rfl, ?_⟩
  · cases h : isTypeError e
    · simp [bytesNew, Obj.index?, bytesFromObject, Obj.buffer?, getIterOr, Obj.typeName, h, bind, Except.bind]
    · simp [bytesNew, Obj.index?, bytesFromObject, Obj.buffer?, getIterOr, Obj.typeName, h, bind, Except.bind]
      rfl
  · simp [pyBytesJoin, stringlibJoin, sequenceFast, getIterOr, bind, Except.bind]
  · cases h : isTypeError e
    · simp [baExtend, Obj.buffer?, getIterOr, Obj.typeName, h, bind, Except.bind]
    · simp [baExtend, Obj.buffer?, getIterOr, Obj.typeName, h, bind, Except.bind]
      rfl
  · cases h : isTypeError e
    · simp [baInit, hc0, hr0, bind, Except.bind, Obj.index?, Obj.buffer?, getIterOr, Obj.typeName, h]
    · simp [baInit, hc0, hr0, bind, Except.bind, Obj.index?, Obj.buffer?, getIterOr, Obj.typeName, h]
      rfl
  · simp [baInit, hc0, hr0, bind, Except.bind, Obj.index?, Obj.buffer?, getIterOr, iterItems?, Obj.typeName]
    rfl

end PyLean.BytesObj.Bytes
