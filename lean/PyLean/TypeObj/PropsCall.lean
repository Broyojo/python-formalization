import PyLean.TypeObj.PropsProto

/-!
Properties of conversions, iteration, `isinstance`, instance creation, argument binding,
descriptors and class creation, for every class structure and every behaviour of user
code.
-/

namespace PyLean.TypeObj

/-! ## `__index__`, `__len__` -/

/-- `_PyNumber_Index` of an int is the int itself; no `__index__` runs. -/
def IndexOfIntIdentity : Prop :=
  ∀ (rt : Rt) (v : Val) (i : Int) (w : World),
    intOf w v = some i → numberIndex rt v w = .ok v w

theorem indexOfIntIdentity_proven : IndexOfIntIdentity := by
  intro rt v i w h
  simp [numberIndex, h]

/-- Without `__index__`, conversion fails with the exact `TypeError`. -/
def IndexRequiresDunder : Prop :=
  ∀ (rt : Rt) (v : Val) (w : World),
    intOf w v = none → indexCheck w v = false →
    numberIndex rt v w =
      (typeErr s!"'{trunc 200 (typeName w v)}' object cannot be interpreted as an integer" : M Val) w

theorem indexRequiresDunder_proven : IndexRequiresDunder := by
  intro rt v w h1 h2
  simp [numberIndex, h1, h2]

/-- `__index__` must return an int, for every `__index__`: a result that is not an int
raises `TypeError`, so `numberIndex` only ever returns ints. -/
def IndexResultIsInt : Prop :=
  ∀ (rt : Rt) (v r : Val) (w w' : World),
    numberIndex rt v w = .ok r w' → ∃ i, intOf w' r = some i

theorem indexResultIsInt_proven : IndexResultIsInt := by
  intro rt v r w w' h
  simp only [numberIndex, M.bind_app, getW_app] at h
  cases hv : intOf w v with
  | some i =>
    simp [hv] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨i, hv⟩
  | none =>
    simp only [hv] at h
    cases hc : indexCheck w v with
    | false => simp [hc, typeErr, raiseC] at h
    | true =>
      simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false] at h
      cases hs : slotOf w (typeOf w v) .nb_index with
      | none => simp [hs, gapAt] at h
      | some f =>
        simp only [hs, M.bind_app] at h
        cases hu : callUnaryNb rt .nb_index "__index__" f v w with
        | err e w1 => rw [hu] at h; simp at h
        | ok x w1 =>
          rw [hu] at h
          simp only [getW_app] at h
          cases hx : intOf w1 x with
          | none => simp [hx, typeErr, raiseC] at h
          | some j =>
            simp [hx] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨j, hx⟩

/-- **`PyNumber_AsSsize_t` clips or raises**: with `err = NULL` the result is in `Py_ssize_t`
range and has the sign of the input, with `err` set an out-of-range index raises `err`. -/
def AsSsizeClips : Prop :=
  ∀ (rt : Rt) (item : Val) (i : Int) (w w' : World),
    pyNumberIndex rt item w = .ok i w' →
    numberAsSsize rt item none w =
      .ok (if inSsize i then i else if i < 0 then PyLean.ssizeMin else PyLean.ssizeMax) w'

theorem asSsizeClips_proven : AsSsizeClips := by
  intro rt item i w w' h
  simp only [numberAsSsize, M.bind_app, h]
  by_cases hs : inSsize i = true <;> simp [hs]

/-- **`len()` of a Python-defined `__len__` is a non-negative `Py_ssize_t`**, for every
`__len__`: negative results raise `ValueError`, huge ones `OverflowError`. -/
def SlotLenInRange : Prop :=
  ∀ (rt : Rt) (self : Val) (n : Int) (w w' : World),
    slotSqLength rt self w = .ok n w' → 0 ≤ n ∧ n ≤ PyLean.ssizeMax

theorem slotLenInRange_proven : SlotLenInRange := by
  intro rt self n w w' h
  simp only [slotSqLength, M.bind_app] at h
  cases hv : vectorcallMethod rt "__len__" [self] w with
  | err e w1 => rw [hv] at h; simp at h
  | ok r w1 =>
    rw [hv] at h
    simp only at h
    cases hi : numberIndex rt r w1 with
    | err e w2 => rw [hi] at h; simp at h
    | ok v w2 =>
      rw [hi] at h
      obtain ⟨idx, hidx⟩ := indexResultIsInt_proven rt r v w1 w2 hi
      simp only [getW_app, hidx, Option.getD_some] at h
      by_cases hneg : idx < 0
      · simp [hneg, valueErr, raiseC] at h
      · have hn : numberIndex rt v w2 = .ok v w2 := by simp [numberIndex, hidx]
        simp only [hneg, ite_false, numberAsSsize, pyNumberIndex, M.bind_app, hn, getW_app,
          hidx, Option.getD_some] at h
        by_cases hs : inSsize idx = true
        · simp [hs] at h
          obtain ⟨rfl, _⟩ := h
          simp only [inSsize, Bool.and_eq_true, decide_eq_true_eq] at hs
          exact ⟨by omega, hs.2⟩
        · simp [hs, getW, raiseC] at h

/-- `PySequence_GetItem` adds `len(s)` once to a negative index, then calls `sq_item`:
`Objects/abstract.c:1849-1859`. -/
def SequenceGetItemNegativeIndex : Prop :=
  ∀ (rt : Rt) (s : Val) (i n : Int) (f lf : SlotFn) (w w1 : World),
    i < 0 → slotIn w s .sq_item = some f → slotIn w s .sq_length = some lf →
    callLen rt lf s w = .ok n w1 →
    pySequenceGetItem rt s i w = callSqItem rt f s (i + n) w1

theorem sequenceGetItemNegativeIndex_proven : SequenceGetItemNegativeIndex := by
  intro rt s i n f lf w w1 hi hf hl hc
  simp [pySequenceGetItem, hf, hl, hc, hi]

/-- `PyObject_GetItem` prefers the mapping protocol: with `mp_subscript` the sequence slot
never runs, so the key is passed unconverted, `Objects/abstract.c:161-166`. -/
def GetItemMappingFirst : Prop :=
  ∀ (rt : Rt) (o key : Val) (f : SlotFn) (w : World),
    slotIn w o .mp_subscript = some f →
    pyGetItem rt o key w = callMpSubscript rt f o key w

theorem getItemMappingFirst_proven : GetItemMappingFirst := by
  intro rt o key f w h
  simp [pyGetItem, h]

/-- **`__class_getitem__` applies only when the metaclass has no `__getitem__`**:
`C[k]` on a class without those slots calls `C.__class_getitem__(k)`. -/
def ClassGetitemFallback : Prop :=
  ∀ (rt : Rt) (o key m : Val) (oa : Addr) (w w1 : World),
    slotIn w o .mp_subscript = none → slotIn w o .sq_item = none →
    asType w o = some oa → oa ≠ B.type →
    rt.getOptionalAttr o "__class_getitem__" w = .ok (some m) w1 →
    m.is .none = false →
    pyGetItem rt o key w = rt.call m [key] [] w1

theorem classGetitemFallback_proven : ClassGetitemFallback := by
  intro rt o key m oa w w1 h1 h2 h3 h4 h5 h6
  simp [pyGetItem, h1, h2, h3, h4, h5, h6]

/-! ## Iteration -/

/-- `iter(x)` checks its result: an `__iter__` returning something that is not an iterator
raises the exact `TypeError`, for every `__iter__`. -/
def GetIterChecksResult : Prop :=
  ∀ (rt : Rt) (o r : Val) (f : SlotFn) (w w1 : World),
    slotOf w (typeOf w o) .tp_iter = some f →
    callIter rt f o w = .ok r w1 →
    pyIterCheck w1 r = false →
    pyGetIter rt o w =
      (typeErr s!"{objFQN w1 o}.__iter__() must return an iterator, not {objFQN w1 r}" : M Val) w1

theorem getIterChecksResult_proven : GetIterChecksResult := by
  intro rt o r f w w1 hf hc hi
  simp [pyGetIter, hf, hc, hi]

/-- The `__getitem__` fallback: a type with no `tp_iter` that is a sequence iterates through
a `seqiterobject` from index 0. -/
def GetIterSequenceFallback : Prop :=
  ∀ (rt : Rt) (o : Val) (w : World),
    slotOf w (typeOf w o) .tp_iter = none → pySequenceCheck w o = true →
    pyGetIter rt o w = pySeqIterNew o w

theorem getIterSequenceFallback_proven : GetIterSequenceFallback := by
  intro rt o w h1 h2
  simp [pyGetIter, h1, h2]

/-- **`__iter__ = None` disables the `__getitem__` fallback**, with the same `TypeError` as
a type that is not iterable, and `__getitem__` is never looked up (`Objects/typeobject.c:11208`
tests `attr_is_none` first): with a `__getitem__` descriptor whose `__get__` raises, CPython
3.15.2 still raises "'C' object is not iterable". -/
def IterNoneNotIterable : Prop :=
  ∀ (rt : Rt) (self : Val) (w w1 : World),
    maybeCallSpecial rt self "__iter__" [] true w = .ok .isNone w1 →
    slotTpIter rt self w =
      (typeErr s!"'{trunc 200 (typeName w1 self)}' object is not iterable" : M Val) w1

theorem iterNoneNotIterable_proven : IterNoneNotIterable := by
  intro rt self w w1 h1
  simp [slotTpIter, h1]

/-- A `seqiterobject` stays exhausted: once `it_seq` is cleared, `next` keeps returning
NULL without calling `__getitem__`, `Objects/iterobject.c:53`. -/
def SeqIterExhaustionSticky : Prop :=
  ∀ (rt : Rt) (a : Addr) (o : Obj) (i : Int) (w : World),
    w.get a = .val o → o.body = .seqIter none i →
    seqIterNext rt a w = .ok none w

theorem seqIterExhaustionSticky_proven : SeqIterExhaustionSticky := by
  intro rt a o i w h1 h2
  cases o with
  | mk c d sv b =>
    simp only at h2
    subst h2
    simp [seqIterNext, h1]

/-- `x in y` uses `__contains__` when the type has it: `Objects/abstract.c:2243`. -/
def ContainsUsesSlot : Prop :=
  ∀ (rt : Rt) (seq ob : Val) (f : SlotFn) (w : World),
    slotIn w seq .sq_contains = some f →
    pySequenceContains rt seq ob w = callContains rt f seq ob w

theorem containsUsesSlot_proven : ContainsUsesSlot := by
  intro rt seq ob f w h
  simp [pySequenceContains, h]

/-- `__contains__ = None` blocks the iteration fallback,
`Objects/typeobject.c:10796-10801`. -/
def ContainsNoneNotContainer : Prop :=
  ∀ (rt : Rt) (self value : Val) (w w1 : World),
    maybeCallSpecial rt self "__contains__" [value] true w = .ok .isNone w1 →
    slotSqContains rt self value w =
      (typeErr s!"'{trunc 200 (typeName w1 self)}' object is not a container" : M Bool) w1

theorem containsNoneNotContainer_proven : ContainsNoneNotContainer := by
  intro rt self value w w1 h
  simp [slotSqContains, h]

/-- The iteration fallback of `in` compares with identity first: the `PyObject_RichCompareBool`
at `Objects/abstract.c:2175`, so a search finds an object by identity whatever its
`__eq__` says. The loop stops at the first item identical to `obj`. -/
def IterSearchIdentity : Prop :=
  ∀ (rt : Rt) (it obj : Val) (fuel : Nat) (n : Int) (wrapped : Bool) (w w1 : World),
    rt.iterNext it w = .ok (some obj) w1 →
    iterSearchLoop rt it obj .contains (fuel + 1) n wrapped w = .ok 1 w1

theorem iterSearchIdentity_proven : IterSearchIdentity := by
  intro rt it obj fuel n wrapped w w1 h
  simp [iterSearchLoop, h, richCompareBool, Val.is_refl]

/-! ## `isinstance`, `issubclass` -/

/-- **Exact type match is a shortcut.** `isinstance(x, type(x))` is true without looking up
`__instancecheck__`, so a metaclass cannot override it, `Objects/abstract.c:2642`. -/
def IsinstanceExactType : Prop :=
  ∀ (rt : Rt) (x : Val) (w : World),
    typeCheck w (.obj (typeOf w x)) = true →
    pyIsInstance rt x (.obj (typeOf w x)) w = .ok true w

theorem isinstanceExactType_proven : IsinstanceExactType := by
  intro rt x w h
  have hobj : Val.is (Val.obj (typeOf w x)) (.obj (typeOf w x)) = true := Val.is_refl _
  have ha : asType w (.obj (typeOf w x)) = some (typeOf w x) := by simp [asType, h]
  simp [pyIsInstance, walkFuel, objectRecursiveIsinstance, ha, hobj]

/-- A custom metaclass decides `isinstance` through `__instancecheck__`, whose result goes
through truth testing. -/
def IsinstanceUsesChecker : Prop :=
  ∀ (rt : Rt) (inst cls checker r : Val) (fuel : Nat) (b : Bool) (w w1 w2 w3 : World),
    (Val.obj (typeOf w inst)).is cls = false → typeOf w cls ≠ B.type →
    unionCheck w cls = false → tupleOf w cls = none →
    lookupSpecial rt cls "__instancecheck__" w = .ok (some checker) w1 →
    rt.call checker [inst] [] w1 = .ok r w2 →
    rt.isTrue r w2 = .ok b w3 →
    objectRecursiveIsinstance rt (fuel + 1) inst cls w = .ok b w3

theorem isinstanceUsesChecker_proven : IsinstanceUsesChecker := by
  intro rt inst cls checker r fuel b w w1 w2 w3 h0 h1 hu h2 h3 h4 h5
  simp [objectRecursiveIsinstance, h0, h1, hu, h2, h3, h4, h5]

/-- `type(x) is cls`-free part of `object_isinstance`: real subtyping is the first test
when `cls` is a class. -/
def ObjectIsinstanceSubtype : Prop :=
  ∀ (rt : Rt) (inst cls : Val) (ca : Addr) (w : World),
    asType w cls = some ca → isSubtype w (typeOf w inst) ca = true →
    objectIsinstance rt inst cls w = .ok true w

theorem objectIsinstanceSubtype_proven : ObjectIsinstanceSubtype := by
  intro rt inst cls ca w h1 h2
  simp [objectIsinstance, h1, h2]

/-- `issubclass(C, D)` on real classes is `D in C.__mro__`, `Objects/abstract.c:2714`. -/
def RecursiveIssubclassMro : Prop :=
  ∀ (rt : Rt) (derived cls : Val) (c d : Addr) (w : World),
    asType w cls = some c → asType w derived = some d →
    recursiveIssubclass rt derived cls w = .ok (isSubtype w d c) w

theorem recursiveIssubclassMro_proven : RecursiveIssubclassMro := by
  intro rt derived cls c d w h1 h2
  simp [recursiveIssubclass, h1, h2]

/-! ## `object.__new__`, `object.__init__` -/

/-- `excess_args` is exactly "some argument was passed". -/
def ExcessArgsIffAny : Prop :=
  ∀ (args : List Val) (kw : Kw), excessArgs args kw = false ↔ args = [] ∧ kw = []

theorem excessArgsIffAny_proven : ExcessArgsIffAny := by
  intro args kw
  simp [excessArgs]

/-- **The table of object's excess-argument errors.** For a class that overrides neither
`__new__` nor `__init__`, `C(1)` raises `C() takes no arguments`. If it overrides `__new__`
but not `__init__`, then `object.__init__` accepts extra arguments (they went to
`__new__`), and similarly if it overrides `__init__` only, then `object.__new__` accepts
them. If it overrides both, each complains on an explicit call. See the comment before
`excess_args` in `Objects/typeobject.c`. -/
def ObjectNewInitTable : Prop :=
  ∀ (rt : Rt) (t : Addr) (self : Val) (args : List Val) (kw : Kw) (w : World),
    excessArgs args kw = true → typeOf w self = t → (tdata w t).isAbstract = false →
    (slotOf w t .tp_new = some (.c .object) → slotOf w t .tp_init = some (.c .object) →
      objectNew rt t args kw w = (typeErr s!"{trunc 200 (tpName w t)}() takes no arguments" : M Val) w ∧
      objectInit self args kw w =
        (typeErr s!"{trunc 200 (tpName w t)}.__init__() takes exactly one argument (the instance to initialize)" : M Unit) w) ∧
    (slotOf w t .tp_new ≠ some (.c .object) → slotOf w t .tp_init = some (.c .object) →
      objectNew rt t args kw w =
        (typeErr "object.__new__() takes exactly one argument (the type to instantiate)" : M Val) w ∧
      objectInit self args kw w = .ok () w) ∧
    (slotOf w t .tp_new = some (.c .object) → slotOf w t .tp_init ≠ some (.c .object) →
      (∃ v w', objectNew rt t args kw w = .ok v w') ∧
      objectInit self args kw w =
        (typeErr "object.__init__() takes exactly one argument (the instance to initialize)" : M Unit) w)

theorem objectNewInitTable_proven : ObjectNewInitTable := by
  intro rt t self args kw w hx ht ha
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2
    constructor
    · simp [objectNew, hx, h1, h2, typeErr, raiseC]
    · simp [objectInit, hx, ht, h1, h2, typeErr, raiseC]
  · intro h1 h2
    constructor
    · simp [objectNew, hx, h1, typeErr, raiseC]
    · simp [objectInit, hx, ht, h1, h2]
  · intro h1 h2
    constructor
    · simp [objectNew, hx, h1, h2, ha, alloc, allocCell]
    · simp [objectInit, hx, ht, h2, typeErr, raiseC]

/-- `type(x)` with one argument never constructs anything: `Objects/typeobject.c:2486`. -/
def TypeCallOneArg : Prop :=
  ∀ (rt : Rt) (x : Val) (w : World), typeCall rt B.type [x] [] w = .ok (.obj (typeOf w x)) w

theorem typeCallOneArg_proven : TypeCallOneArg := by
  intro rt x w
  simp [typeCall]

/-- **`__init__` is skipped when `__new__` returns a non-instance**,
`Objects/typeobject.c:2519`, for every `__new__` and `__init__`. -/
def TypeCallSkipsInit : Prop :=
  ∀ (rt : Rt) (t : Addr) (f : SlotFn) (obj : Val) (args : List Val) (kw : Kw) (w w1 : World),
    t ≠ B.type → slotOf w t .tp_new = some f →
    callTpNew rt f t args kw w = .ok obj w1 →
    isSubtype w1 (typeOf w1 obj) t = false →
    typeCall rt t args kw w = .ok obj w1

theorem typeCallSkipsInit_proven : TypeCallSkipsInit := by
  intro rt t f obj args kw w w1 h0 h1 h2 h3
  simp [typeCall, h0, h1, h2, h3]

/-- ... and it runs on the type of the result, not on the type called. -/
def TypeCallInitsResultType : Prop :=
  ∀ (rt : Rt) (t : Addr) (f g : SlotFn) (obj : Val) (args : List Val) (kw : Kw) (w w1 w2 : World),
    t ≠ B.type → slotOf w t .tp_new = some f →
    callTpNew rt f t args kw w = .ok obj w1 →
    isSubtype w1 (typeOf w1 obj) t = true →
    slotOf w1 (typeOf w1 obj) .tp_init = some g →
    callTpInit rt g obj args kw w1 = .ok () w2 →
    typeCall rt t args kw w = .ok obj w2

theorem typeCallInitsResultType_proven : TypeCallInitsResultType := by
  intro rt t f g obj args kw w w1 w2 h0 h1 h2 h3 h4 h5
  simp [typeCall, h0, h1, h2, h3, h4, h5]

/-- A non-`None` result of `__init__` is a `TypeError`, `Objects/typeobject.c:11285`. -/
def InitMustReturnNone : Prop :=
  ∀ (rt : Rt) (self res : Val) (args : List Val) (kw : Kw) (w w1 : World),
    callMethod rt self "__init__" args kw w = .ok res w1 →
    res.is .none = false →
    slotTpInit rt self args kw w =
      (typeErr s!"__init__() should return None, not '{trunc 200 (typeName w1 res)}'" : M Unit) w1

theorem initMustReturnNone_proven : InitMustReturnNone := by
  intro rt self res args kw w w1 h1 h2
  simp [slotTpInit, h1, h2]

/-! ## Functions and methods -/

/-- **`__get__` of a function**: from an instance it binds; from the class it returns the
function, `Objects/funcobject.c:1267`. `None` is treated as no instance. -/
def FunctionBinding : Prop :=
  ∀ (f o : Val) (w : World),
    funcDescrGet f none w = .ok f w ∧ funcDescrGet f (some .none) w = .ok f w ∧
    (o.is .none = false → funcDescrGet f (some o) w = pyMethodNew f o w)

theorem functionBinding_proven : FunctionBinding := by
  intro f o w
  refine ⟨by simp [funcDescrGet], by simp [funcDescrGet], ?_⟩
  intro h
  cases o <;> first | (simp [Val.is] at h; done) | simp [funcDescrGet]

/-- **A bound method call prepends `self`**: `method_vectorcall`,
`Objects/classobject.c:47`. -/
def BoundMethodPrependsSelf : Prop :=
  ∀ (rt : Rt) (m func self : Val) (args : List Val) (kw : Kw) (w : World),
    payloadOf w m = some (.bound func self) →
    callTpCall rt (.c .method) m args kw w = rt.call func (self :: args) kw w

theorem boundMethodPrependsSelf_proven : BoundMethodPrependsSelf := by
  intro rt m func self args kw w h
  simp [callTpCall, h]

/-- `classmethod` binds the class whether reached from the class or an instance, and
`staticmethod` returns the callable unchanged, `Objects/funcobject.c:1535`, `:1799`. -/
def ClassStaticBinding : Prop :=
  ∀ (cm sm f g o ty : Val) (w : World),
    payloadOf w cm = some (.classmethod f) → payloadOf w sm = some (.staticmethod g) →
    cmDescrGet cm none (some ty) w = pyMethodNew f ty w ∧
    cmDescrGet cm (some o) (some ty) w = pyMethodNew f ty w ∧
    cmDescrGet cm (some o) none w = pyMethodNew f (.obj (typeOf w o)) w ∧
    smDescrGet sm w = .ok g w

theorem classStaticBinding_proven : ClassStaticBinding := by
  intro cm sm f g o ty w h1 h2
  simp [cmDescrGet, smDescrGet, h1, h2]

/-- **`property`**: from the class the property itself, from an instance `fget(obj)`,
`Objects/descrobject.c:1685`. -/
def PropertyGet : Prop :=
  ∀ (rt : Rt) (p o : Val) (w : World),
    propertyDescrGet rt p none w = .ok p w ∧ propertyDescrGet rt p (some .none) w = .ok p w ∧
    (∀ fget fs fd doc name gd, o.is .none = false →
      propertyFields w p = some (fget, fs, fd, doc, name, gd) → fget.is .none = false →
      propertyDescrGet rt p (some o) w = rt.call fget [o] [] w)

theorem propertyGet_proven : PropertyGet := by
  intro rt p o w
  refine ⟨by simp [propertyDescrGet], by simp [propertyDescrGet], ?_⟩
  intro fget fs fd doc name gd h1 h2 h3
  have hf : fget ≠ .none := by
    intro h; subst h; simp [Val.is] at h3
  have ho : o ≠ .none := by
    intro h; subst h; simp [Val.is] at h1
  cases o <;> first
    | exact (ho rfl).elim
    | simp only [propertyDescrGet, M.bind_app, getW_app, h2]

/-- `super` searches strictly after `__thisclass__` in the MRO of the object's type:
`Objects/typeobject.c:12712-12722`. -/
def SuperSkipsThisClass : Prop :=
  ∀ (w : World) (pre post : List Addr) (su ot : Addr) (n : Name) (last : Addr),
    (tdata w ot).mro = some (pre ++ su :: post ++ [last]) →
    su ∉ pre →
    superLookupDescr w su ot n = findInMroList w (post ++ [last]) n

theorem findIdx_after (pre rest : List Addr) (su : Addr) (hp : su ∉ pre) :
    (pre ++ su :: rest).findIdx? (· == su) = some pre.length := by
  induction pre with
  | nil => simp [List.findIdx?_cons]
  | cons x xs ih =>
    have hx : x ≠ su := fun h => hp (by simp [h])
    have hxs : su ∉ xs := fun h => hp (by simp [h])
    simp [List.findIdx?_cons, hx, ih hxs]

theorem drop_after (pre rest : List Addr) (x : Addr) :
    (pre ++ x :: rest).drop (pre.length + 1) = rest := by
  induction pre with
  | nil => simp
  | cons y ys ih => simpa using ih

theorem superSkipsThisClass_proven : SuperSkipsThisClass := by
  intro w pre post su ot n last hm hp
  have h1 : (pre ++ su :: post) ++ [last] = pre ++ su :: (post ++ [last]) := by simp
  simp only [superLookupDescr, hm]
  rw [List.dropLast_concat, findIdx_after _ _ _ hp, h1]
  simp only [drop_after]

/-! ## Refutations -/

/-- **`.setter` keeps an explicit docstring.** Refuted for subclasses of `property`:
`property_init_impl` keeps their doc in the instance dict, and `property_copy` reads
`prop_doc`, which is NULL there. The statement: the `doc` argument of the copy is the
docstring the object shows, for a property whose doc did not come from its getter. -/
def PropertyCopyKeepsDoc : Prop :=
  ∀ (w : World) (p d g s dl doc : Val) (name : Option Val),
    propertyFields w p = some (g, s, dl, doc, name, false) →
    instDictGet w p "__doc__" = some d →
    copyDocArg false g doc = d

/-- A `property` subclass instance after `P(None, None, None, "doc")`. -/
def docWorld : World :=
  { heap := #[.ty 0 { name := "P", dictoffset := -1, mro := some [0] },
              .val { cls := 1, body := .dict [(.str "__doc__", .str "doc")] },
              .val { cls := 0, dict := some 1,
                     body := .property .none .none .none .none none false }] }

theorem propertyCopyKeepsDoc_refuted : ¬PropertyCopyKeepsDoc := by
  intro h
  have := h docWorld (.obj 2) (.str "doc") .none .none .none .none none (by rfl) (by rfl)
  simp [copyDocArg] at this

/-- **Too-many-arguments errors report a non-negative minimum.** Refuted: `__defaults__`
can be longer than the parameter list. -/
def TooManyPositionalBound : Prop := ∀ f : FuncData, 0 ≤ tooManyAtLeast f

theorem tooManyPositionalBound_refuted : ¬TooManyPositionalBound := by
  intro h
  have := h { argcount := 1, defaults := [.int 1, .int 2, .int 3] }
  simp [tooManyAtLeast] at this

end PyLean.TypeObj
