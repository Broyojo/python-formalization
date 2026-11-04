import PyLean.BytesObj.Seq.TupleRows

/-!
`tuple.__getnewargs__`, and the C API that builds tuples in place: `PyTuple_New`, `PyTuple_SetItem` and
`_PyTuple_Resize`, with the `ob_hash` cache they leave alone (Objects/tupleobject.c, CPython 3.15.2).
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α : Type}

/-- `t.__getnewargs__()` (`tuple___getnewargs___impl`, tupleobject.c:960-965) is a fresh 1-tuple
(`Py_BuildValue("(N)", ...)`) holding `tuple_slice(self, 0, len)`: for an exact tuple that is `self`
(:528-530), and for a subclass instance, which is what pickling uses it for, a new exact tuple of its
items (the singleton when it has none), tracked iff an item may be. Hypothesis: the tuple's length is
one `tuple_alloc` gives (type invariant). -/
def TupleGetnewargs : Prop :=
  ∀ (α : Type) (mt : α → Bool) (a : Tup α), (a.items.length : Int) ≤ tupleLimit →
    (a.exact = true → tupleGetnewargs mt a = .ok { items := [.arg 0], tracked := true }) ∧
    (a.exact = false → a.items ≠ [] → tupleGetnewargs mt a =
      .ok { items := [.fresh { items := a.items, tracked := a.items.any mt }], tracked := true }) ∧
    (a.exact = false → a.items = [] → tupleGetnewargs mt a = .ok { items := [.empty], tracked := true })

theorem tupleGetnewargs_proven : TupleGetnewargs := by
  intro α mt a hl
  have e1 : max (0 : Int) 0 = 0 := rfl
  have e2 : max (min (a.items.length : Int) a.items.length) 0 = a.items.length := by omega
  have hL : a.items = (a.items.drop (max (0 : Int) 0).toNat).take
      (max (min (a.items.length : Int) a.items.length) (max 0 0) - max 0 0).toNat := by
    rw [e1, e2]; simp
  have hs := tupleSlice_eq mt a 0 a.items.length hl a.items hL
  rw [e1, e2] at hs
  refine ⟨fun he => ?_, fun he hne => ?_, fun he hn => ?_⟩
  · rw [if_pos ⟨rfl, rfl, he⟩] at hs
    simp only [tupleGetnewargs, hs]
  · rw [if_neg (by simp [he]), if_neg hne] at hs
    simp only [tupleGetnewargs, hs]
  · rw [if_neg (by simp [he]), if_pos hn] at hs
    simp only [tupleGetnewargs, hs]

/-- The C API that builds a tuple in place, on every branch, for every element type:

* `PyTuple_New(n)` (tupleobject.c:74-90): the singleton for `0` (:78-80); `SystemError` for a
  negative size and `MemoryError` past `tupleLimit` (`tuple_alloc`, :39-56); otherwise `n` `NULL`
  slots, tracked;
* `PyTuple_SetItem(op, i, v)` (:117-135): `SystemError` for a non-tuple and for a tuple that is not
  uniquely referenced, `IndexError("tuple assignment index out of range")` outside `[0, len)`, and
  otherwise the item replaced and nothing else: the type, the GC flag and `ob_hash` stay. So a tuple
  hashed before keeps that hash whatever item is stored (`TupleSetItemHashFresh`);
* `_PyTuple_Resize(&v, n)` (:1045-1123): `SystemError` for `NULL`, for an object that is not exactly a
  tuple, for a negative size, and for a non-empty tuple that is not uniquely referenced (the empty one
  is shared and not asked); the same size leaves `v` alone; size 0 gives the singleton; the empty
  tuple is replaced by `PyTuple_New(n)`; past `tupleLimit` `MemoryError`; otherwise the tuple keeps
  its first `n` items, gains `NULL` slots, is tracked, and keeps its `ob_hash`. -/
def CApiTupleObj : Prop :=
  ∀ (α : Type) (n i : Int) (t : Tup α) (v : α) (u : Tup (Option α)) (hashE : α → Py Int) (unique : Bool),
    (n < 0 → pyTupleNew n = (.error systemError : Py (TRes (Option α)))) ∧
    pyTupleNew 0 = (.ok .empty : Py (TRes (Option α))) ∧
    (0 < n → n ≤ tupleLimit →
      pyTupleNew n = (.ok (.fresh { items := List.replicate n.toNat none, tracked := true }) :
        Py (TRes (Option α)))) ∧
    (tupleLimit < n → pyTupleNew n = (.error memoryError : Py (TRes (Option α)))) ∧
    pyTupleSetItem (none : Option (Tup α)) unique i v = .error systemError ∧
    pyTupleSetItem (some t) false i v = .error systemError ∧
    ((i < 0 ∨ i ≥ t.items.length) →
      pyTupleSetItem (some t) true i v = .error (.indexError "tuple assignment index out of range")) ∧
    (0 ≤ i → i < t.items.length →
      pyTupleSetItem (some t) true i v = .ok { t with items := t.items.set i.toNat v }) ∧
    (∀ t', toUhash t.hash ≠ U64 - 1 → pyTupleSetItem (some t) true i v = .ok t' →
      tupleHash hashE t' = .ok (t.hash, t')) ∧
    tupleResize (none : Option (Tup (Option α))) unique n = .error systemError ∧
    (u.exact = false → tupleResize (some u) unique n = .error systemError) ∧
    (n < 0 → tupleResize (some u) unique n = .error systemError) ∧
    (u.items ≠ [] → tupleResize (some u) false n = .error systemError) ∧
    (u.exact = true → (u.items.length : Int) = n → (u.items ≠ [] → unique = true) →
      tupleResize (some u) unique n = .ok (.arg 0)) ∧
    (u.exact = true → u.items ≠ [] → tupleResize (some u) true 0 = .ok .empty) ∧
    (u.exact = true → u.items = [] → 0 < n → tupleResize (some u) unique n = pyTupleNew n) ∧
    (u.exact = true → u.items ≠ [] → 0 < n → n ≤ tupleLimit → (u.items.length : Int) ≠ n →
      tupleResize (some u) true n = .ok (.fresh { u with
        items := u.items.take n.toNat ++ List.replicate (n - u.items.length).toNat none, tracked := true })) ∧
    (u.exact = true → u.items ≠ [] → tupleLimit < n → (u.items.length : Int) ≠ n →
      tupleResize (some u) true n = .error memoryError)

theorem cApiTupleObj_proven : CApiTupleObj := by
  intro α n i t v u hashE unique
  have hlim : 0 < tupleLimit := by decide
  have hlim' : tupleLimit = (ssizeMax - tupleBase) / 8 := rfl
  refine ⟨fun h => ?_, rfl, fun h0 h1 => ?_, fun h => ?_, rfl, rfl, fun h => ?_, fun h0 h1 => ?_,
    fun t' hc h => ?_, rfl, fun he => ?_, fun h => ?_, fun hne => ?_, fun he hl hu => ?_, fun he hne => ?_,
    fun he hn h0 => ?_, fun he hne h0 h1 hl => ?_, fun he hne h1 hl => ?_⟩
  · unfold pyTupleNew; rw [if_neg (by omega), tupleAlloc_neg n h]
  · unfold pyTupleNew; rw [if_neg (by omega), tupleAlloc_ok n (by omega) h1]
  · unfold pyTupleNew; rw [if_neg (by omega), tupleAlloc_big n (by omega) h]
  · simp only [pyTupleSetItem, Bool.not_true, Bool.false_eq_true, if_false]; rw [if_pos h]
  · simp only [pyTupleSetItem, Bool.not_true, Bool.false_eq_true, if_false]; rw [if_neg (by omega)]
  · simp only [pyTupleSetItem, Bool.not_true, Bool.false_eq_true, if_false] at h
    split at h
    · cases h
    · cases h
      unfold tupleHash
      rw [if_pos hc]
  · simp [tupleResize, he]
  · simp [tupleResize, h]
  · have : (u.items.length : Int) ≠ 0 := by
      have := List.length_pos_iff.mpr hne; omega
    simp [tupleResize, hne]
  · have hn : ¬ n < 0 := by omega
    by_cases h0 : u.items = []
    · have hz : (u.items.length : Int) = 0 := by simp [h0]
      have hn00 : n = 0 := by omega
      subst hn00
      simp [tupleResize, he, h0]
    · simp [tupleResize, he, hn, hu h0, hl]
  · have : (u.items.length : Int) ≠ 0 := by
      have := List.length_pos_iff.mpr hne; omega
    simp [tupleResize, he, hne]
  · have hz : (u.items.length : Int) = 0 := by simp [hn]
    have hn0 : ¬ n < 0 := by omega
    have hne0 : (0 : Int) ≠ n := by omega
    have hn0' : n ≠ 0 := by omega
    simp [tupleResize, he, hz, hn0, hne0, hn0']
  · have h00 : (u.items.length : Int) ≠ 0 := by
      have := List.length_pos_iff.mpr hne; omega
    have hn0 : ¬ n < 0 := by omega
    have hn0' : n ≠ 0 := by omega
    have hb : ¬ n > (ssizeMax - tupleBase) / 8 := by omega
    simp [tupleResize, he, hne, hn0, hn0', hl, hb]
  · have h00 : (u.items.length : Int) ≠ 0 := by
      have := List.length_pos_iff.mpr hne; omega
    have hn0 : ¬ n < 0 := by omega
    have hn0' : n ≠ 0 := by omega
    have hb : n > (ssizeMax - tupleBase) / 8 := by omega
    simp [tupleResize, he, hne, hn0, hn0', hl, hb]

/-- `t[a:b]` on an exact tuple under `BINARY_SLICE` (`_PyTuple_BinarySlice`, tupleobject.c:534-551,
with `_PyEval_UnpackIndices`, Python/ceval.c:2981-2999), for every pair of bounds, including objects
with `__index__`: `start` is converted first, and its exception (from `__index__`, or the `TypeError`
for an object that is neither an int, `None` nor has `__index__`) is the result whatever `stop` is;
then `stop`'s; otherwise the result has the items of `t[slice(a, b)]` for the values `a` and `b`
(`TupleBinarySlice`), and it is the tuple itself (`Py_NewRef(container)`, :543-545) exactly when the
bounds cover it: `a` is `None`, `0` or at most `-len`, and `b` is `None` or at least `len` (any bounds
for the empty tuple); otherwise it is a new tuple or the empty singleton, never `t`. Hypothesis: the
tuple's length is one `tuple_alloc` gives (type invariant). -/
def TupleBinarySliceObj : Prop :=
  ∀ (α : Type) (mt : α → Bool) (t : Tup α) (start stop : SIdx) (e : PyExc) (a b : Option Int),
    t.exact = true → (t.items.length : Int) ≤ tupleLimit →
    evalSliceIndex SIdx.other = .error (.typeError "slice indices must be integers or have an __index__ method") ∧
    evalSliceIndex (SIdx.index (.error e)) = .error e ∧
    (evalSliceIndex start = .error e → tupleBinarySliceObj mt t start stop = .error e) ∧
    (evalSliceIndex start = .ok a → evalSliceIndex stop = .error e → tupleBinarySliceObj mt t start stop = .error e) ∧
    (evalSliceIndex start = .ok a → evalSliceIndex stop = .ok b →
      ∃ r r', tupleBinarySliceObj mt t start stop = .ok r ∧ tupleGetSlice t ⟨a, b, none⟩ = .ok r' ∧
        r.items t.items [] = r'.items t.items []) ∧
    (evalSliceIndex start = .ok a → evalSliceIndex stop = .ok b →
      (tupleBinarySliceObj mt t start stop = .ok (.arg 0) ↔
        (t.items = [] ∨ ((a = none ∨ a = some 0 ∨ ∃ v, a = some v ∧ v ≤ -(t.items.length : Int)) ∧
          (b = none ∨ ∃ v, b = some v ∧ (t.items.length : Int) ≤ v)))))

theorem tupleFromArray_ne_arg (mt : α → Bool) (L : List α) (k : Nat) :
    tupleFromArray mt L ≠ .ok (.arg k) := by
  unfold tupleFromArray
  split
  · simp
  · cases tupleAlloc (L.length : Int) <;> simp

theorem tupleBinarySlice_arg (mt : α → Bool) (t : Tup α) (a b : Option Int)
    (hl : (t.items.length : Int) ≤ tupleLimit) :
    tupleBinarySlice mt t ⟨a, b, none⟩ = .ok (.arg 0) ↔
      (t.items = [] ∨ ((a = none ∨ a = some 0 ∨ ∃ v, a = some v ∧ v ≤ -(t.items.length : Int)) ∧
        (b = none ∨ ∃ v, b = some v ∧ (t.items.length : Int) ≤ v))) := by
  have hlim : tupleLimit = (ssizeMax - tupleBase) / 8 := rfl
  have hM : ssizeMax = 9223372036854775807 := by decide
  have hm : ssizeMin = -9223372036854775808 := by decide
  have hB : tupleBase = 32 := rfl
  have key : tupleBinarySlice mt t ⟨a, b, none⟩ = .ok (.arg 0) ↔
      (unpackIndices t.items.length ⟨a, b, none⟩).1 = 0 ∧
        (unpackIndices t.items.length ⟨a, b, none⟩).2 = t.items.length := by
    cases hp : unpackIndices (t.items.length : Int) ⟨a, b, none⟩ with
    | mk x y =>
    have e1 : tupleBinarySlice mt t ⟨a, b, none⟩ = if x = 0 ∧ y = (t.items.length : Int) then .ok (.arg 0)
        else tupleFromArray mt ((t.items.drop x.toNat).take ((if y < x then x else y) - x).toNat) := by
      simp only [tupleBinarySlice, hp]
    rw [e1]
    simp only
    by_cases h : x = 0 ∧ y = (t.items.length : Int)
    · simp [h]
    · rw [if_neg h]
      simp only [h, iff_false]
      exact tupleFromArray_ne_arg mt _ 0
  rw [key]
  have he : t.items = [] ↔ (t.items.length : Int) = 0 := by simp
  rw [he]
  have hn0 : 0 ≤ (t.items.length : Int) := by omega
  rw [hlim, hM, hB] at hl
  generalize (t.items.length : Int) = n at hl hn0 ⊢
  cases a <;> cases b <;>
    simp [unpackIndices, RangeSlice.adjustIndices, RangeSlice.adjustOne, RangeSlice.clampSsize, hM, hm] <;>
    (repeat' split) <;> omega

theorem tupleBinarySliceObj_proven : TupleBinarySliceObj := by
  intro α mt t start stop e a b he hl
  refine ⟨rfl, rfl, fun h => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · simp only [tupleBinarySliceObj, h]
  · simp only [tupleBinarySliceObj, h1, h2]
  · obtain ⟨r, r', hr, hr', hi⟩ := tupleBinarySlice_proven α mt t a b he hl
    exact ⟨r, r', by simp only [tupleBinarySliceObj, h1, h2, hr], hr', hi⟩
  · have : tupleBinarySliceObj mt t start stop = tupleBinarySlice mt t ⟨a, b, none⟩ := by
      simp only [tupleBinarySliceObj, h1, h2]
    rw [this]
    exact tupleBinarySlice_arg mt t a b hl

/-- After `PyTuple_SetItem` on a uniquely referenced tuple, `hash` agrees with that of a fresh tuple
of the same items: the cache invariant of `ob_hash` ("Cached hash", Include/cpython/tupleobject.h),
which `tuple_alloc`, `tuple_subtype_new` and `_PyTuple_Recycle` keep by resetting it. Refuted:
`PyTuple_SetItem` (tupleobject.c:117-135) never resets `ob_hash`, so `t = PyTuple_New(1)`, `t[0] = 1`,
`hash(t)`, `t[0] = 2` leaves `hash(t)` at `hash((1,))` although `t == (2,)`, and `t` is not found in a
dict keyed by `(2,)`. `_PyTuple_Resize` keeps the hash the same way (`CApiTupleObj`). -/
def TupleSetItemHashFresh : Prop :=
  ∀ (α : Type) (hashE : α → Py Int) (t t1 t' : Tup α) (i : Int) (v : α) (h : Int),
    tupleHash hashE t = .ok (h, t1) → pyTupleSetItem (some t1) true i v = .ok t' →
    (tupleHash hashE t').map (·.1) = (tupleHash hashE { items := t'.items }).map (·.1)

theorem tupleSetItemHashFresh_refuted : ¬ TupleSetItemHashFresh := by
  intro hP
  have h1 : tupleHash (fun x : Int => (.ok x : Py Int)) ({ items := [1] } : Tup Int) =
      .ok (-6644214454873602895, { items := [1], hash := -6644214454873602895 }) := by decide
  have h2 : pyTupleSetItem (some ({ items := [1], hash := -6644214454873602895 } : Tup Int)) true 0 2 =
      .ok { items := [2], hash := -6644214454873602895 } := by decide
  have := hP Int (fun x => .ok x) _ _ _ 0 2 _ h1 h2
  revert this
  decide

end PyLean.BytesObj.Seq
