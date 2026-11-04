import PyLean.TypeObj.PropsObjExact

/-!
`object_richcompare`, `object.__format__`, `_PyObject_GetNewArguments` and `_PyType_GetSlotNames`
(`Objects/typeobject.c`, CPython 3.15.2), on every branch.
-/

namespace PyLean.TypeObj

/-! ## `object_richcompare` -/

/-- **`object_richcompare`, every branch.** `Objects/typeobject.c:7576-7618`, with
`_Py_BaseObject_RichCompare` (`:7621-7624`), which is the same function:
* `==` is `True` for the same object and `NotImplemented` otherwise, by identity, not value: two
  distinct heap objects are `NotImplemented` whatever their contents, and so are distinct
  values; where the model cannot tell whether equal values are one object (a big `int`), it says
  nothing (`identityKnown`);
* `!=` asks `tp_richcompare(self, other, ==)` of the type of `self` (`NotImplemented` when that
  slot is NULL): `NotImplemented` passes through, any other result is negated by its truth
  value, and exceptions from either call propagate;
* every ordering is `NotImplemented`. -/
def ObjectRichcompareExact : Prop :=
  ∀ (rt : Rt) (eqSlot : M Val) (self other : Val) (w : World),
    (∀ a b, self = .obj a → other = .obj b →
      objectRichcompare rt eqSlot self other .eq w = .ok (if a = b then .bool true else .notImpl) w) ∧
    (identityKnown self other = some true → objectRichcompare rt eqSlot self other .eq w = .ok (.bool true) w) ∧
    (identityKnown self other = some false → objectRichcompare rt eqSlot self other .eq w = .ok .notImpl w) ∧
    (∀ w1, eqSlot w = .ok .notImpl w1 → objectRichcompare rt eqSlot self other .ne w = .ok .notImpl w1) ∧
    (∀ e w1, eqSlot w = .err e w1 → objectRichcompare rt eqSlot self other .ne w = .err e w1) ∧
    (∀ r w1, eqSlot w = .ok r w1 → r.is .notImpl = false →
      (∀ b w2, rt.isTrue r w1 = .ok b w2 → objectRichcompare rt eqSlot self other .ne w = .ok (.bool (!b)) w2) ∧
      (∀ e w2, rt.isTrue r w1 = .err e w2 → objectRichcompare rt eqSlot self other .ne w = .err e w2)) ∧
    (∀ op, op ≠ .eq → op ≠ .ne → objectRichcompare rt eqSlot self other op w = .ok .notImpl w)

theorem objectRichcompareExact_proven : ObjectRichcompareExact := by
  intro rt eqSlot self other w
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b ha hb
    subst ha hb
    by_cases hab : a = b
    · subst hab; simp [objectRichcompare, identityKnown, identityDetermined, Val.is]
    · have : (a == b) = false := by simpa using hab
      simp [objectRichcompare, identityKnown, Val.is, this, hab]
  · intro h; simp [objectRichcompare, h]
  · intro h; simp [objectRichcompare, h]
  · intro w1 h; simp [objectRichcompare, h]
  · intro e w1 h; simp [objectRichcompare, h]
  · intro r w1 h hn
    have hr : r ≠ .notImpl := by intro h'; subst h'; simp [Val.is] at hn
    refine ⟨fun b w2 hb => ?_, fun e w2 he => ?_⟩
    · simp only [objectRichcompare, M.bind_app, h]
      cases r <;> first | exact (hr rfl).elim | simp [hb]
    · simp only [objectRichcompare, M.bind_app, h]
      cases r <;> first | exact (hr rfl).elim | simp [he]
  · intro op h1 h2
    cases op <;> first | exact (h1 rfl).elim | exact (h2 rfl).elim | rfl

/-! ## `object.__format__` -/

/-- **`object.__format__`, every branch.** `Objects/typeobject.c:8501-8513`: a non-empty format
spec raises "unsupported format string passed to %.200s.__format__"; an empty one returns
`str(self)`, and an exception from `str(self)` propagates. -/
def ObjectFormatExact : Prop :=
  ∀ (rt : Rt) (self : Val) (spec : String) (w : World),
    (spec.length > 0 → objectFormat rt self spec w =
      (typeErr s!"unsupported format string passed to {trunc 200 (typeName w self)}.__format__" : M Val) w) ∧
    (spec = "" →
      (∀ s w1, rt.str self w = .ok s w1 → objectFormat rt self spec w = .ok (.str s) w1) ∧
      (∀ e w1, rt.str self w = .err e w1 → objectFormat rt self spec w = .err e w1))

theorem objectFormatExact_proven : ObjectFormatExact := by
  intro rt self spec w
  refine ⟨fun h => by simp [objectFormat, h, typeErr, raiseC], fun h => ?_⟩
  subst h
  exact ⟨fun s w1 hs => by simp [objectFormat, hs, Functor.map, M.bind, M.pure],
    fun e w1 he => by simp [objectFormat, he, Functor.map, M.bind]⟩

/-! ## `_PyObject_GetNewArguments` -/

/-- **`_PyObject_GetNewArguments`, every branch.** `Objects/typeobject.c:8146-8234`:
`__getnewargs_ex__` is looked up on the type first (an exception from the lookup or its `__get__`
propagates, `:8202-8204`); if present it is called (its exception propagates, `:8159-8163`) and the
result is checked by `checkNewargsEx` (`CheckNewargsExExact`), and `__getnewargs__` is never
consulted, even when the call fails. Only if `__getnewargs_ex__` is missing is `__getnewargs__`
looked up and called likewise (`:8210-8222`), its result required to be a tuple; with neither,
both results are NULL. -/
def GetNewArgumentsExact : Prop :=
  ∀ (rt : Rt) (obj : Val) (w w1 : World),
    (∀ e, lookupSpecial rt obj "__getnewargs_ex__" w = .err e w1 → getNewArguments rt obj w = .err e w1) ∧
    (∀ m, lookupSpecial rt obj "__getnewargs_ex__" w = .ok (some m) w1 →
      (∀ e w2, rt.call m [] [] w1 = .err e w2 → getNewArguments rt obj w = .err e w2) ∧
      (∀ r w2, rt.call m [] [] w1 = .ok r w2 →
        getNewArguments rt obj w = (do let (a, k) ← checkNewargsEx r; pure (some a, some k)) w2)) ∧
    (lookupSpecial rt obj "__getnewargs_ex__" w = .ok none w1 →
      (∀ e w2, lookupSpecial rt obj "__getnewargs__" w1 = .err e w2 → getNewArguments rt obj w = .err e w2) ∧
      (∀ w2, lookupSpecial rt obj "__getnewargs__" w1 = .ok none w2 → getNewArguments rt obj w = .ok (none, none) w2) ∧
      (∀ m w2, lookupSpecial rt obj "__getnewargs__" w1 = .ok (some m) w2 →
        (∀ e w3, rt.call m [] [] w2 = .err e w3 → getNewArguments rt obj w = .err e w3) ∧
        (∀ a w3, rt.call m [] [] w2 = .ok a w3 → (tupleOf w3 a).isSome = true →
          getNewArguments rt obj w = .ok (some a, none) w3) ∧
        (∀ a w3, rt.call m [] [] w2 = .ok a w3 → tupleOf w3 a = none →
          getNewArguments rt obj w =
            (typeErr s!"__getnewargs__ should return a tuple, not '{trunc 200 (typeName w3 a)}'" : M (Option Val × Option Val)) w3)))

theorem getNewArgumentsExact_proven : GetNewArgumentsExact := by
  intro rt obj w w1
  refine ⟨fun e h => by simp [getNewArguments, h], fun m h => ⟨fun e w2 hc => by simp [getNewArguments, h, hc],
    fun r w2 hc => by simp [getNewArguments, h, hc]⟩, fun h => ⟨fun e w2 h2 => by simp [getNewArguments, h, h2],
    fun w2 h2 => by simp [getNewArguments, h, h2], fun m w2 h2 => ⟨fun e w3 hc => by simp [getNewArguments, h, h2, hc],
    fun a w3 hc ht => ?_, fun a w3 hc ht => by simp [getNewArguments, h, h2, hc, ht, typeErr, raiseC]⟩⟩⟩
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ht
  simp [getNewArguments, h, h2, hc, hx]

/-- **The checks on `__getnewargs_ex__`'s result.** `Objects/typeobject.c:8164-8200`, in order:
not a tuple raises "should return a tuple, not '%.200s'"; a tuple of length other than 2 raises
`ValueError` "should return a tuple of length 2, not %zd"; a first item that is not a tuple, then a
second that is not a dict, raise their `TypeError`s; otherwise the pair. -/
def CheckNewargsExExact : Prop :=
  ∀ (r : Val) (w : World),
    (tupleOf w r = none → checkNewargsEx r w =
      (typeErr s!"__getnewargs_ex__ should return a tuple, not '{trunc 200 (typeName w r)}'" : M (Val × Val)) w) ∧
    (∀ xs, tupleOf w r = some xs → xs.length ≠ 2 → checkNewargsEx r w =
      (valueErr s!"__getnewargs_ex__ should return a tuple of length 2, not {xs.length}" : M (Val × Val)) w) ∧
    (∀ a k, tupleOf w r = some [a, k] →
      (tupleOf w a = none → checkNewargsEx r w =
        (typeErr s!"first item of the tuple returned by __getnewargs_ex__ must be a tuple, not '{trunc 200 (typeName w a)}'" : M (Val × Val)) w) ∧
      ((tupleOf w a).isSome = true → dictOf w k = none → checkNewargsEx r w =
        (typeErr s!"second item of the tuple returned by __getnewargs_ex__ must be a dict, not '{trunc 200 (typeName w k)}'" : M (Val × Val)) w) ∧
      ((tupleOf w a).isSome = true → (dictOf w k).isSome = true → checkNewargsEx r w = .ok (a, k) w))

theorem checkNewargsExExact_proven : CheckNewargsExExact := by
  intro r w
  refine ⟨fun h => by simp [checkNewargsEx, h, typeErr, raiseC], fun xs h hl => ?_, fun a k h => ⟨?_, ?_, ?_⟩⟩
  · match xs, hl with
    | [], _ => simp [checkNewargsEx, h, valueErr, raiseC]
    | [_], _ => simp [checkNewargsEx, h, valueErr, raiseC]
    | _ :: _ :: _ :: _, _ => simp [checkNewargsEx, h, valueErr, raiseC]
    | [_, _], hl => simp at hl
  · intro ha; simp [checkNewargsEx, h, ha, typeErr, raiseC]
  · intro ha hk
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ha
    simp [checkNewargsEx, h, hx, hk, typeErr, raiseC]
  · intro ha hk
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hk
    simp [checkNewargsEx, h, hx, hy]

/-! ## `_PyType_GetSlotNames` -/

/-- **`_PyType_GetSlotNames`, every branch.** `Objects/typeobject.c:7930-7977`: a cached
`__slotnames__` in the class dict is returned if it is a list or `None` and refused with the
exact message otherwise; without one, `copyreg._slotnames(cls)` is called *through the module*
(`:7955-7963`), so a replaced `copyreg._slotnames` runs, its exception propagates, and a result
that is neither a list nor `None` raises "copyreg._slotnames didn't return a list or None"
(`:7968-7972`; on 3.15.2, `copyreg._slotnames = lambda cls: 42` makes `__reduce_ex__(2)` raise
it). With the stock function, its result is checked the same way. -/
def SlotNamesExact : Prop :=
  ∀ (rt : Rt) (cls : Addr) (w : World),
    (∀ s, NameDict.get? (tdata w cls).dict "__slotnames__" = some s →
      ((s.is .none = true ∨ (listOf w s).isSome = true) → typeGetSlotNames rt cls w = .ok s w) ∧
      (s.is .none = false → (listOf w s).isSome = false → typeGetSlotNames rt cls w =
        (typeErr s!"{trunc 200 (tpName w cls)}.__slotnames__ should be a list or None, not {trunc 200 (typeName w s)}" : M Val) w)) ∧
    (NameDict.get? (tdata w cls).dict "__slotnames__" = none →
      (∀ f, w.copyregSlotnames = some f →
        (∀ e w1, rt.call f [.obj cls] [] w = .err e w1 → typeGetSlotNames rt cls w = .err e w1) ∧
        (∀ s w1, rt.call f [.obj cls] [] w = .ok s w1 →
          ((s.is .none = true ∨ (listOf w1 s).isSome = true) → typeGetSlotNames rt cls w = .ok s w1) ∧
          (s.is .none = false → (listOf w1 s).isSome = false → typeGetSlotNames rt cls w =
            (typeErr "copyreg._slotnames didn't return a list or None" : M Val) w1))) ∧
      (w.copyregSlotnames = none →
        (∀ e w1, copyregSlotnames rt cls w = .err e w1 → typeGetSlotNames rt cls w = .err e w1) ∧
        (∀ s w1, copyregSlotnames rt cls w = .ok s w1 →
          ((s.is .none = true ∨ (listOf w1 s).isSome = true) → typeGetSlotNames rt cls w = .ok s w1) ∧
          (s.is .none = false → (listOf w1 s).isSome = false → typeGetSlotNames rt cls w =
            (typeErr "copyreg._slotnames didn't return a list or None" : M Val) w1))))

theorem slotNamesExact_proven : SlotNamesExact := by
  intro rt cls w
  refine ⟨fun s hd => ⟨fun h1 => ?_, fun h1 h2 => ?_⟩, fun hd => ⟨fun f hf => ⟨fun e w1 hc => ?_,
    fun s w1 hc => ⟨fun h1 => ?_, fun h1 h2 => ?_⟩⟩, fun hf => ⟨fun e w1 hc => ?_,
    fun s w1 hc => ⟨fun h1 => ?_, fun h1 h2 => ?_⟩⟩⟩⟩
  · rcases h1 with h1 | h1 <;> simp [typeGetSlotNames, hd, h1]
  · simp [typeGetSlotNames, hd, h1, h2, typeErr, raiseC]
  · simp [typeGetSlotNames, hd, hf, hc]
  · rcases h1 with h1 | h1 <;> simp [typeGetSlotNames, hd, hf, hc, h1]
  · simp [typeGetSlotNames, hd, hf, hc, h1, h2, typeErr, raiseC]
  · simp [typeGetSlotNames, hd, hf, hc]
  · rcases h1 with h1 | h1 <;> simp [typeGetSlotNames, hd, hf, hc, h1]
  · simp [typeGetSlotNames, hd, hf, hc, h1, h2, typeErr, raiseC]

end PyLean.TypeObj
