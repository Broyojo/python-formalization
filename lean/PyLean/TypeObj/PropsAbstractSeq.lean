import PyLean.TypeObj.PropsAbstractNum

/-!
The item, sequence, mapping and iteration protocols of `Objects/abstract.c`, every branch:
`PyObject_GetItem`, `PySequence_GetItem`/`SetItem`/`DelItem`, `_PySequence_IterSearch`,
`PySequence_Contains`, `PyMapping_Size`, `PyObject_GetIter`, `PyIter_Next`.

Every statement is over every `rt`: slot functions, `__index__`, `__len__`, `__eq__`,
`__iter__`, `__next__` and attribute lookups are arbitrary code that may raise and re-enter,
and the world each later step runs in is the world the earlier one left.
-/

namespace PyLean.TypeObj

/-! ## `PyObject_GetItem` -/

/-- **`PyObject_GetItem`, every branch, in source order.** `mp_subscript` first; else `sq_item`,
with an index key converted by `PyNumber_AsSsize_t(key, IndexError)` and passed to
`PySequence_GetItem`, and any other key refused; else, on a class, `type[...]` makes a
`types.GenericAlias`, other classes call `__class_getitem__` (a missing or `None` one, or a
failed lookup, refuses with the class's `tp_name` read after the lookup); anything else is not
subscriptable. `Objects/abstract.c:155-206`. -/
def GetItemExact : Prop :=
  ∀ (rt : Rt) (o key : Val) (w : World),
    (∀ f, slotIn w o .mp_subscript = some f →
      pyGetItem rt o key w = callMpSubscript rt f o key w) ∧
    (slotIn w o .mp_subscript = none → ∀ f, slotIn w o .sq_item = some f →
      pyGetItem rt o key w =
        if indexCheck w key then
          match numberAsSsize rt key (some B.IndexError) w with
          | .ok i w1 => pySequenceGetItem rt o i w1
          | .err e w1 => .err e w1
        else .err (.exc B.TypeError
          ("sequence index must be integer, not '" ++ trunc 200 (typeName w key) ++ "'") none) w) ∧
    (slotIn w o .mp_subscript = none → slotIn w o .sq_item = none →
      asType w o = some B.type →
      pyGetItem rt o key w =
        .ok (.obj w.heap.size) { w with heap := w.heap.push (.val { cls := B.genericAlias }) }) ∧
    (slotIn w o .mp_subscript = none → slotIn w o .sq_item = none →
      ∀ a, asType w o = some a → a ≠ B.type →
      pyGetItem rt o key w =
        match rt.getOptionalAttr o "__class_getitem__" w with
        | .err e w1 => .err e w1
        | .ok m w1 =>
          let refuse : R Val := .err (.exc B.TypeError
            ("type '" ++ trunc 200 (tpName w1 a) ++ "' is not subscriptable") none) w1
          match m with
          | some m => if m.is .none then refuse else rt.call m [key] [] w1
          | none => refuse) ∧
    (slotIn w o .mp_subscript = none → slotIn w o .sq_item = none → asType w o = none →
      pyGetItem rt o key w = .err (.exc B.TypeError
        ("'" ++ trunc 200 (typeName w o) ++ "' object is not subscriptable") none) w)

theorem getItemExact_proven : GetItemExact := by
  intro rt o key w
  refine ⟨fun f h => ?_, fun h1 f h2 => ?_, fun h1 h2 h3 => ?_, fun h1 h2 a h3 h4 => ?_,
    fun h1 h2 h3 => ?_⟩
  · simp [pyGetItem, h]
  · by_cases hi : indexCheck w key = true
    · simp only [pyGetItem, M.bind_app, getW_app, h1, h2, hi, ite_true]
      cases numberAsSsize rt key (some B.IndexError) w <;> rfl
    · simp [pyGetItem, h1, h2, hi, typeErr, raiseC]
  · simp [pyGetItem, h1, h2, h3, alloc, allocCell]
  · have h4' : (a == B.type) = false := by simp [h4]
    simp only [pyGetItem, M.bind_app, getW_app, h1, h2, h3, h4', Bool.false_eq_true, ite_false]
    cases rt.getOptionalAttr o "__class_getitem__" w with
    | err e w1 => rfl
    | ok m w1 =>
      cases m with
      | none => simp [typeErr, raiseC]
      | some m => by_cases hn : m.is .none = true <;> simp [hn, typeErr, raiseC]
  · simp [pyGetItem, h1, h2, h3, typeErr, raiseC]

/-! ## `PySequence_GetItem`, `PySequence_SetItem`, `PySequence_DelItem` -/

/-- **`PySequence_GetItem`, every branch**: with `sq_item`, a non-negative index goes to it as
it is; a negative one has `sq_length` added first when there is one (its exception
propagating), and goes as it is when there is none; without `sq_item`, a mapping is "not a
sequence" and anything else "does not support indexing". `Objects/abstract.c:1841-1868`. -/
def SequenceGetItemExact : Prop :=
  ∀ (rt : Rt) (s : Val) (i : Int) (w : World),
    (∀ f, slotIn w s .sq_item = some f → 0 ≤ i →
      pySequenceGetItem rt s i w = callSqItem rt f s i w) ∧
    (∀ f lf, slotIn w s .sq_item = some f → i < 0 → slotIn w s .sq_length = some lf →
      pySequenceGetItem rt s i w =
        match callLen rt lf s w with
        | .ok l w1 => callSqItem rt f s (i + l) w1
        | .err e w1 => .err e w1) ∧
    (∀ f, slotIn w s .sq_item = some f → i < 0 → slotIn w s .sq_length = none →
      pySequenceGetItem rt s i w = callSqItem rt f s i w) ∧
    (∀ f, slotIn w s .sq_item = none → slotIn w s .mp_subscript = some f →
      pySequenceGetItem rt s i w = .err (.exc B.TypeError
        (trunc 200 (typeName w s) ++ " is not a sequence") none) w) ∧
    (slotIn w s .sq_item = none → slotIn w s .mp_subscript = none →
      pySequenceGetItem rt s i w = .err (.exc B.TypeError
        ("'" ++ trunc 200 (typeName w s) ++ "' object does not support indexing") none) w)

theorem sequenceGetItemExact_proven : SequenceGetItemExact := by
  intro rt s i w
  refine ⟨fun f h hi => ?_, fun f lf h hi hl => ?_, fun f h hi hl => ?_, fun f h hm => ?_,
    fun h hm => ?_⟩
  · have : ¬ i < 0 := by omega
    simp [pySequenceGetItem, h, this]
  · simp only [pySequenceGetItem, M.bind_app, getW_app, h, hi, hl, ite_true, decide_true]
    cases callLen rt lf s w <;> rfl
  · simp [pySequenceGetItem, h, hi, hl]
  · simp [pySequenceGetItem, h, hm, typeErr, raiseC]
  · simp [pySequenceGetItem, h, hm, typeErr, raiseC]

/-- **`PySequence_SetItem` and `PySequence_DelItem`, every branch** (`value = none` deletes):
the same index rule as `PySequence_GetItem` before `sq_ass_item`; without it, a mapping with
`mp_ass_subscript` is "not a sequence", anything else "does not support item assignment" or
"doesn't support item deletion". `Objects/abstract.c:1893-1956`. -/
def SequenceSetItemExact : Prop :=
  ∀ (rt : Rt) (s : Val) (i : Int) (value : Option Val) (w : World),
    (∀ f, slotIn w s .sq_ass_item = some f → 0 ≤ i →
      pySequenceSetItem rt s i value w = callSqAssItem rt f s i value w) ∧
    (∀ f lf, slotIn w s .sq_ass_item = some f → i < 0 → slotIn w s .sq_length = some lf →
      pySequenceSetItem rt s i value w =
        match callLen rt lf s w with
        | .ok l w1 => callSqAssItem rt f s (i + l) value w1
        | .err e w1 => .err e w1) ∧
    (∀ f, slotIn w s .sq_ass_item = some f → i < 0 → slotIn w s .sq_length = none →
      pySequenceSetItem rt s i value w = callSqAssItem rt f s i value w) ∧
    (∀ f, slotIn w s .sq_ass_item = none → slotIn w s .mp_ass_subscript = some f →
      pySequenceSetItem rt s i value w = .err (.exc B.TypeError
        (trunc 200 (typeName w s) ++ " is not a sequence") none) w) ∧
    (slotIn w s .sq_ass_item = none → slotIn w s .mp_ass_subscript = none →
      pySequenceSetItem rt s i value w = .err (.exc B.TypeError
        ("'" ++ trunc 200 (typeName w s) ++ "' object " ++
          (if value.isSome then "does not support item assignment"
           else "doesn't support item deletion")) none) w)

theorem sequenceSetItemExact_proven : SequenceSetItemExact := by
  intro rt s i value w
  refine ⟨fun f h hi => ?_, fun f lf h hi hl => ?_, fun f h hi hl => ?_, fun f h hm => ?_,
    fun h hm => ?_⟩
  · have : ¬ i < 0 := by omega
    simp [pySequenceSetItem, h, this]
  · simp only [pySequenceSetItem, M.bind_app, getW_app, h, hi, hl, ite_true, decide_true]
    cases callLen rt lf s w <;> rfl
  · simp [pySequenceSetItem, h, hi, hl]
  · simp [pySequenceSetItem, h, hm, typeErr, raiseC]
  · cases value <;> simp [pySequenceSetItem, h, hm, typeErr, raiseC]

/-! ## `_PySequence_IterSearch` and `PySequence_Contains` -/

/-- **`_PySequence_IterSearch`, the iterator step.** A `TypeError` (or subclass) from
`PyObject_GetIter` is replaced by `argument of type '<T>' is not a container or iterable` for
`in` and `... is not iterable` for `count`/`index`, other exceptions pass; then the loop starts
from `n = 0`, not wrapped. `Objects/abstract.c:2149-2165`. -/
def IterSearchStart : Prop :=
  ∀ (rt : Rt) (seq obj : Val) (op : IterSearchOp) (w : World),
    pySequenceIterSearch rt seq obj op w =
      match rt.getIter seq w with
      | .ok it w1 => iterSearchLoop rt it obj op iterFuel 0 false w1
      | .err e w1 =>
        if excMatches w1 e B.TypeError then
          .err (.exc B.TypeError ("argument of type '" ++ trunc 200 (typeName w1 seq) ++
            (if op = .contains then "' is not a container or iterable" else "' is not iterable"))
            none) w1
        else .err e w1

theorem iterSearchStart_proven : IterSearchStart := by
  intro rt seq obj op w
  unfold pySequenceIterSearch
  simp only [M.bind_app, tryM_app]
  cases rt.getIter seq w with
  | ok it w1 => rfl
  | err e w1 =>
    simp only [getW_app]
    by_cases hm : excMatches w1 e B.TypeError = true
    · by_cases hc : op = .contains <;> simp [hm, hc, typeErr, raiseC]
    · simp [hm]

/-- **`_PySequence_IterSearch`, every branch of the loop.** `PyIter_Next` failing propagates;
exhaustion ends `COUNT` and `CONTAINS` with the counter and `INDEX` with the `ValueError`; a
failing comparison propagates; a match counts (with the `OverflowError` at `PY_SSIZE_T_MAX`),
ends `INDEX` with the position (or the `OverflowError` once the counter has wrapped) and ends
`CONTAINS` with 1; `INDEX` advances its counter on a miss, wrapping at `PY_SSIZE_T_MAX` and
remembering it. `Objects/abstract.c:2166-2219`. -/
def IterSearchLoopExact : Prop :=
  ∀ (rt : Rt) (it obj : Val) (op : IterSearchOp) (fuel : Nat) (n : Int) (wr : Bool)
    (w : World),
    iterSearchLoop rt it obj op (fuel + 1) n wr w =
      match rt.iterNext it w with
      | .err e w1 => .err e w1
      | .ok none w1 =>
        if op = .index then
          .err (.exc B.ValueError "sequence.index(x): x not in sequence" none) w1
        else .ok n w1
      | .ok (some item) w1 =>
        match richCompareBool rt item obj .eq w1 with
        | .err e w2 => .err e w2
        | .ok true w2 =>
          match op with
          | .count =>
            if n = PyLean.ssizeMax then
              .err (.exc B.OverflowError "count exceeds C integer size" none) w2
            else iterSearchLoop rt it obj op fuel (n + 1) wr w2
          | .index =>
            if wr then .err (.exc B.OverflowError "index exceeds C integer size" none) w2
            else .ok n w2
          | .contains => .ok 1 w2
        | .ok false w2 =>
          if op = .index then
            iterSearchLoop rt it obj op fuel
              (if n = PyLean.ssizeMax then PyLean.ssizeMin else n + 1)
              (wr || n = PyLean.ssizeMax) w2
          else iterSearchLoop rt it obj op fuel n wr w2

theorem iterSearchLoopExact_proven : IterSearchLoopExact := by
  intro rt it obj op fuel n wr w
  simp only [iterSearchLoop, M.bind_app]
  cases rt.iterNext it w with
  | err e w1 => rfl
  | ok x w1 =>
    cases x with
    | none => cases op <;> simp [valueErr, raiseC]
    | some item =>
      simp only [M.bind_app]
      cases richCompareBool rt item obj .eq w1 with
      | err e w2 => rfl
      | ok b w2 =>
        have hb : (n == PyLean.ssizeMax) = decide (n = PyLean.ssizeMax) := by
          by_cases hn : n = PyLean.ssizeMax <;> simp [hn]
        by_cases hn : n = PyLean.ssizeMax <;>
          cases b <;> cases op <;> cases wr <;> simp [hb, hn, ssizeInc, overflowErr, raiseC]

/-- **`PySequence_Contains`, every branch**: `sq_contains` when the type has one, whatever it
does; otherwise `_PySequence_IterSearch(..., PY_ITERSEARCH_CONTAINS)`, true exactly when it
gives a non-zero result. `Objects/abstract.c:2240-2250`. -/
def SequenceContainsExact : Prop :=
  ∀ (rt : Rt) (seq ob : Val) (w : World),
    (∀ f, slotIn w seq .sq_contains = some f →
      pySequenceContains rt seq ob w = callContains rt f seq ob w) ∧
    (slotIn w seq .sq_contains = none →
      pySequenceContains rt seq ob w =
        match pySequenceIterSearch rt seq ob .contains w with
        | .ok r w1 => .ok (r != 0) w1
        | .err e w1 => .err e w1)

theorem sequenceContainsExact_proven : SequenceContainsExact := by
  intro rt seq ob w
  refine ⟨fun f h => ?_, fun h => ?_⟩
  · simp [pySequenceContains, h]
  · simp only [pySequenceContains, M.bind_app, getW_app, h]
    cases pySequenceIterSearch rt seq ob .contains w <;> rfl

/-! ## `PyMapping_Size` -/

/-- **`PyMapping_Size`, every branch**: `mp_length` when there is one; a sequence with only
`sq_length` is "not a mapping"; anything else "has no len()". `Objects/abstract.c:2276-2297`. -/
def MappingSizeExact : Prop :=
  ∀ (rt : Rt) (o : Val) (w : World),
    (∀ f, slotIn w o .mp_length = some f → pyMappingSize rt o w = callLen rt f o w) ∧
    (∀ f, slotIn w o .mp_length = none → slotIn w o .sq_length = some f →
      pyMappingSize rt o w = .err (.exc B.TypeError
        (trunc 200 (typeName w o) ++ " is not a mapping") none) w) ∧
    (slotIn w o .mp_length = none → slotIn w o .sq_length = none →
      pyMappingSize rt o w = .err (.exc B.TypeError
        ("object of type '" ++ trunc 200 (typeName w o) ++ "' has no len()") none) w)

theorem mappingSizeExact_proven : MappingSizeExact := by
  intro rt o w
  refine ⟨fun f h => ?_, fun f h1 h2 => ?_, fun h1 h2 => ?_⟩
  · simp [pyMappingSize, h]
  · simp [pyMappingSize, h1, h2, typeErr, raiseC]
  · simp [pyMappingSize, h1, h2, typeErr, raiseC]

/-! ## `PyObject_GetIter` and `PyIter_Next` -/

/-- **`PyObject_GetIter`, every branch**: with no `tp_iter`, a sequence gets a new
`seqiterobject` at index 0 and anything else is "not iterable"; with `tp_iter`, its exception
propagates, an iterator result is returned as it is, and any other result is the `TypeError`
`<T>.__iter__() must return an iterator, not <U>`. `Objects/abstract.c:2813-2834`. -/
def GetIterExact : Prop :=
  ∀ (rt : Rt) (o : Val) (w : World),
    (slotOf w (typeOf w o) .tp_iter = none → pySequenceCheck w o = true →
      pyGetIter rt o w = .ok (.obj w.heap.size)
        { w with heap := w.heap.push (.val { cls := B.seqIter, body := .seqIter (some o) 0 }) }) ∧
    (slotOf w (typeOf w o) .tp_iter = none → pySequenceCheck w o = false →
      pyGetIter rt o w = .err (.exc B.TypeError
        ("'" ++ trunc 200 (typeName w o) ++ "' object is not iterable") none) w) ∧
    (∀ f, slotOf w (typeOf w o) .tp_iter = some f →
      pyGetIter rt o w =
        match callIter rt f o w with
        | .err e w1 => .err e w1
        | .ok res w1 =>
          if pyIterCheck w1 res then .ok res w1
          else .err (.exc B.TypeError (objFQN w1 o ++ ".__iter__() must return an iterator, not " ++
            objFQN w1 res) none) w1)

theorem getIterExact_proven : GetIterExact := by
  intro rt o w
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun f h => ?_⟩
  · simp [pyGetIter, h1, h2, pySeqIterNew, alloc, allocCell]
  · simp [pyGetIter, h1, h2, typeErr, raiseC]
  · simp only [pyGetIter, M.bind_app, getW_app, h]
    cases callIter rt f o w with
    | err e w1 => rfl
    | ok res w1 =>
      by_cases hc : pyIterCheck w1 res = true <;> simp [hc, typeErr, raiseC]

/-- **`PyIter_Next`, every path** (with `iternext`): an item is returned; `NULL` with no
exception is exhaustion; a `StopIteration` (or subclass, as `PyErr_ExceptionMatches` matches)
is cleared into exhaustion; any other exception propagates. For a class, the item is the result
of `__next__`. `Objects/abstract.c:2873-2928`. -/
def IterNextExact : Prop :=
  ∀ (rt : Rt) (it : Val) (w : World),
    (∀ f, slotOf w (typeOf w it) .tp_iternext = some f →
      pyIterNext rt it w =
        match callIterNext rt f it w with
        | .ok x w1 => .ok x w1
        | .err e w1 => if excMatches w1 e B.StopIteration then .ok none w1 else .err e w1) ∧
    (slotOf w (typeOf w it) .tp_iternext = some .generic → ∀ x w1,
      vectorcallMethod rt "__next__" [it] w = .ok x w1 → pyIterNext rt it w = .ok (some x) w1)

theorem iterNextExact_proven : IterNextExact := by
  intro rt it w
  refine ⟨fun f h => ?_, fun h x w1 hx => ?_⟩
  · simp only [pyIterNext, M.bind_app, getW_app, h, catchMatch, tryM_app]
    cases callIterNext rt f it w with
    | ok x w1 => rfl
    | err e w1 => by_cases hm : excMatches w1 e B.StopIteration = true <;> simp [hm]
  · simp [pyIterNext, h, catchMatch, callIterNext, hx]

end PyLean.TypeObj
