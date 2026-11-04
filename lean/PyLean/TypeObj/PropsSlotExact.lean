import PyLean.TypeObj.MroSpec2
import PyLean.TypeObj.PropsType2

/-!
Every branch of the `slot_*` dispatchers of `Objects/typeobject.c` (CPython 3.15.2) that call a
special method: what each returns when the method succeeds, when it is missing or `None`, and
when its lookup, its `__get__` or the call raises. Each statement is an equation for every
`rt : Rt`, so it holds for every behaviour of user code, and a dispatcher that differed on any
branch (dropped the exception, defaulted a result, skipped the fallback) would fail it.
-/

namespace PyLean.TypeObj

/-! ## `maybe_call_special_no_args` / `_one_arg` -/

/-- **`maybe_call_special_*`, every branch.** `Objects/typeobject.c:3204-3243` with
`lookup_maybe_method` (`:3038-3080`): the special method is looked up on the type, not the
instance;
* missing: `.missing`, nothing run;
* a method descriptor (`Py_TPFLAGS_METHOD_DESCRIPTOR`) is called unbound with `self` first;
* another descriptor is bound by its `__get__` and the bound value called with the arguments;
  an `AttributeError` from `__get__` counts as missing, any other exception propagates;
* a value without `__get__` is called as it is;
* with `checkNone` (`attr_is_none != NULL`) a found value that is `None` is reported, not
  called. -/
def MaybeCallSpecialExact : Prop :=
  ∀ (rt : Rt) (self : Val) (attr : Name) (args : List Val) (checkNone : Bool) (w : World),
    (findInMro w (typeOf w self) attr = none →
      maybeCallSpecial rt self attr args checkNone w = .ok .missing w) ∧
    (∀ f, findInMro w (typeOf w self) attr = some f →
      (tdata w (typeOf w f)).methodDescriptor = true →
      maybeCallSpecial rt self attr args checkNone w =
        (if checkNone && f.is .none then pure .isNone
         else Maybe.res <$> rt.call f (self :: args) []) w) ∧
    (∀ f, findInMro w (typeOf w self) attr = some f →
      (tdata w (typeOf w f)).methodDescriptor = false →
      slotOf w (typeOf w f) .tp_descr_get = none →
      maybeCallSpecial rt self attr args checkNone w =
        (if checkNone && f.is .none then pure .isNone
         else Maybe.res <$> rt.call f args []) w) ∧
    (∀ f g v w', findInMro w (typeOf w self) attr = some f →
      (tdata w (typeOf w f)).methodDescriptor = false →
      slotOf w (typeOf w f) .tp_descr_get = some g →
      callDescrGet rt g f (some self) (some (.obj (typeOf w self))) w = .ok v w' →
      maybeCallSpecial rt self attr args checkNone w =
        (if checkNone && v.is .none then pure .isNone
         else Maybe.res <$> rt.call v args []) w') ∧
    (∀ f g e w', findInMro w (typeOf w self) attr = some f →
      (tdata w (typeOf w f)).methodDescriptor = false →
      slotOf w (typeOf w f) .tp_descr_get = some g →
      callDescrGet rt g f (some self) (some (.obj (typeOf w self))) w = .err e w' →
      maybeCallSpecial rt self attr args checkNone w =
        (if excMatches w' e B.AttributeError then .ok .missing w' else .err e w'))

theorem maybeCallSpecialExact_proven : MaybeCallSpecialExact := by
  intro rt self attr args checkNone w
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    simp [maybeCallSpecial, lookupMethodEx, h]
  · intro f h hm
    simp only [maybeCallSpecial, lookupMethodEx, M.bind_app, getW_app, h, hm, ite_true,
      M.pure_app, Bool.false_eq_true]
    by_cases hn : f.is .none = true <;> cases checkNone <;> simp [hn, callUnbound]
  · intro f h hm hg
    simp only [maybeCallSpecial, lookupMethodEx, M.bind_app, getW_app, h, hm, hg,
      Bool.false_eq_true, ite_false, M.pure_app]
    by_cases hn : f.is .none = true <;> cases checkNone <;> simp [hn, callUnbound]
  · intro f g v w' h hm hg hd
    simp only [maybeCallSpecial, lookupMethodEx, M.bind_app, getW_app, h, hm, hg,
      Bool.false_eq_true, ite_false, catchMatch, tryM_app, hd, M.pure_app]
    by_cases hn : v.is .none = true <;> cases checkNone <;> simp [hn, callUnbound]
  · intro f g e w' h hm hg hd
    simp only [maybeCallSpecial, lookupMethodEx, M.bind_app, getW_app, h, hm, hg,
      Bool.false_eq_true, ite_false, catchMatch, tryM_app, hd]
    cases hx : excMatches w' e B.AttributeError <;> simp [hx]

/-! ## `slot_tp_hash` -/

/-- **`slot_tp_hash`, every branch.** `Objects/typeobject.c:11002-11039`:
* an exception from looking up or calling `__hash__` propagates (`:11008-11011`);
* `__hash__ = None`, or no usable `__hash__`, is `PyObject_HashNotImplemented` (`:11012`);
* a result that is not an `int` raises the exact `TypeError` (`:11014-11019`);
* an `int` in `Py_ssize_t` range is the hash, except `-1`, which becomes `-2` (`:11034-11035`);
* an `int` outside that range is hashed by `long.__hash__`: the sign times `|i| mod (2**61 - 1)`,
  then `-1` becomes `-2` (`:11026-11033`). -/
def SlotTpHashExact : Prop :=
  ∀ (rt : Rt) (self : Val) (w w1 : World),
    (∀ e, maybeCallSpecial rt self "__hash__" [] true w = .err e w1 →
      slotTpHash rt self w = .err e w1) ∧
    ((maybeCallSpecial rt self "__hash__" [] true w = .ok .isNone w1 ∨
        maybeCallSpecial rt self "__hash__" [] true w = .ok .missing w1) →
      slotTpHash rt self w = (hashNotImplemented self : M Int) w1) ∧
    (∀ r, maybeCallSpecial rt self "__hash__" [] true w = .ok (.res r) w1 → intOf w1 r = none →
      slotTpHash rt self w = (typeErr "__hash__ method should return an integer" : M Int) w1) ∧
    (∀ r i, maybeCallSpecial rt self "__hash__" [] true w = .ok (.res r) w1 → intOf w1 r = some i →
      slotTpHash rt self w =
        .ok (if inSsize i then (if i = -1 then -2 else i)
             else (let h : Int := (i.natAbs % (2 ^ 61 - 1) : Nat)
                   let r : Int := if i < 0 then -h else h
                   if r == -1 then -2 else r)) w1)

theorem slotTpHashExact_proven : SlotTpHashExact := by
  intro rt self w w1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e h; simp [slotTpHash, h]
  · intro h
    rcases h with h | h <;> simp [slotTpHash, h]
  · intro r h hi; simp [slotTpHash, h, hi]
  · intro r i h hi
    have hne : (longHash i == -1) = false := by
      unfold longHash
      by_cases hr : ((if i < 0 then -(((i.natAbs % hashModulus : Nat)) : Int)
          else ((i.natAbs % hashModulus : Nat) : Int)) == -1) = true
      · simp only [hr, ite_true]; decide
      · simp only [Bool.not_eq_true] at hr
        simp only [hr, Bool.false_eq_true, ite_false]
    simp only [slotTpHash, M.bind_app, h, getW_app, hi, M.pure_app, hashOfInt]
    by_cases hs : inSsize i = true
    · by_cases h1 : i = -1
      · subst h1; simp [hs]
      · simp [hs, h1]
    · simp only [hs, Bool.false_eq_true, ite_false, hne]
      rfl

/-! ## `slot_nb_bool` -/

/-- **`slot_nb_bool`, every branch.** `Objects/typeobject.c:10903-10944`:
* `__bool__ = None` raises "'%.200s' cannot be interpreted as a boolean" (`:10910-10915`);
* a `bool` result is the truth value; any other result raises the exact `TypeError`
  (`:10935-10941`);
* an exception from `__bool__` (lookup, `__get__` or call) propagates;
* without `__bool__`, `__len__` is called and its result's truth is the answer; without
  `__len__` the object is true (`:10916-10921`); an exception from `__len__` propagates. -/
def SlotNbBoolExact : Prop :=
  ∀ (rt : Rt) (self : Val) (w w1 : World),
    (maybeCallSpecial rt self "__bool__" [] true w = .ok .isNone w1 →
      slotNbBool rt self w =
        (typeErr s!"'{trunc 200 (typeName w1 self)}' cannot be interpreted as a boolean" : M Bool) w1) ∧
    (∀ b, maybeCallSpecial rt self "__bool__" [] true w = .ok (.res (.bool b)) w1 →
      slotNbBool rt self w = .ok b w1) ∧
    (∀ v, maybeCallSpecial rt self "__bool__" [] true w = .ok (.res v) w1 → (∀ b, v ≠ .bool b) →
      slotNbBool rt self w =
        (typeErr s!"{objFQN w1 self}.__bool__() must return a bool, not {objFQN w1 v}" : M Bool) w1) ∧
    (∀ e, maybeCallSpecial rt self "__bool__" [] true w = .err e w1 → slotNbBool rt self w = .err e w1) ∧
    (maybeCallSpecial rt self "__bool__" [] true w = .ok .missing w1 →
      (∀ v w2, maybeCallSpecial rt self "__len__" [] false w1 = .ok (.res v) w2 →
        slotNbBool rt self w = rt.isTrue v w2) ∧
      (∀ w2, maybeCallSpecial rt self "__len__" [] false w1 = .ok .missing w2 →
        slotNbBool rt self w = .ok true w2) ∧
      (∀ e w2, maybeCallSpecial rt self "__len__" [] false w1 = .err e w2 →
        slotNbBool rt self w = .err e w2))

theorem slotNbBoolExact_proven : SlotNbBoolExact := by
  intro rt self w w1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [slotNbBool, h]
  · intro b h; simp [slotNbBool, h]
  · intro v h hv
    cases v <;> simp_all [slotNbBool]
  · intro e h; simp [slotNbBool, h]
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro v w2 h2; simp [slotNbBool, h, h2]
    · intro w2 h2; simp [slotNbBool, h, h2]
    · intro e w2 h2; simp [slotNbBool, h, h2]

/-! ## `slot_sq_contains` -/

/-- **`slot_sq_contains`, every branch.** `Objects/typeobject.c:10790-10811`:
* `__contains__ = None` raises "'%.200s' object is not a container";
* a result's truth (`PyObject_IsTrue`) is the answer;
* an exception from `__contains__` propagates;
* without `__contains__`, `_PySequence_IterSearch(self, value, PY_ITERSEARCH_CONTAINS)` decides
  (`:10805-10806`): iteration, with identity or equality per item. -/
def SlotSqContainsExact : Prop :=
  ∀ (rt : Rt) (self value : Val) (w w1 : World),
    (maybeCallSpecial rt self "__contains__" [value] true w = .ok .isNone w1 →
      slotSqContains rt self value w =
        (typeErr s!"'{trunc 200 (typeName w1 self)}' object is not a container" : M Bool) w1) ∧
    (∀ r, maybeCallSpecial rt self "__contains__" [value] true w = .ok (.res r) w1 →
      slotSqContains rt self value w = rt.isTrue r w1) ∧
    (∀ e, maybeCallSpecial rt self "__contains__" [value] true w = .err e w1 →
      slotSqContains rt self value w = .err e w1) ∧
    (maybeCallSpecial rt self "__contains__" [value] true w = .ok .missing w1 →
      slotSqContains rt self value w =
        (do let r ← pySequenceIterSearch rt self value .contains; pure (r != 0)) w1)

theorem slotSqContainsExact_proven : SlotSqContainsExact := by
  intro rt self value w w1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; simp [slotSqContains, h]
  · intro r h; simp [slotSqContains, h]
  · intro e h; simp [slotSqContains, h]
  · intro h; simp [slotSqContains, h]

/-! ## `slot_tp_init` -/

/-- **`slot_tp_init`, every branch.** `Objects/typeobject.c:11279-11294`: `__init__` is called
through `call_method`; a `None` result is success, with the world `__init__` left; any other
result raises "__init__() should return None, not '%.200s'"; an exception from the lookup or
the call propagates. -/
def SlotTpInitExact : Prop :=
  ∀ (rt : Rt) (self : Val) (args : List Val) (kw : Kw) (w w1 : World),
    (callMethod rt self "__init__" args kw w = .ok .none w1 →
      slotTpInit rt self args kw w = .ok () w1) ∧
    (∀ r, callMethod rt self "__init__" args kw w = .ok r w1 → r.is .none = false →
      slotTpInit rt self args kw w =
        (typeErr s!"__init__() should return None, not '{trunc 200 (typeName w1 r)}'" : M Unit) w1) ∧
    (∀ e, callMethod rt self "__init__" args kw w = .err e w1 →
      slotTpInit rt self args kw w = .err e w1)

theorem slotTpInitExact_proven : SlotTpInitExact := by
  intro rt self args kw w w1
  refine ⟨?_, ?_, ?_⟩
  · intro h; simp [slotTpInit, h, Val.is]
  · intro r h hn; simp [slotTpInit, h, hn]
  · intro e h; simp [slotTpInit, h]

/-! ## `slot_tp_iter` -/

/-- **`slot_tp_iter`, every branch.** `Objects/typeobject.c:11197-11216`, with
`has_dunder_getitem` (`:11184-11194`):
* an `__iter__` result is returned as it is (`PyObject_GetIter` checks it later);
* an exception from `__iter__` propagates;
* `__iter__ = None` raises "'%.200s' object is not iterable" without looking up `__getitem__`;
* without `__iter__`, a found `__getitem__` gives a sequence iterator from index 0, a missing one
  the `TypeError`, and an exception from looking it up (a raising `__get__`) is replaced by the
  `TypeError`. -/
def SlotTpIterExact : Prop :=
  ∀ (rt : Rt) (self : Val) (w w1 : World),
    (∀ r, maybeCallSpecial rt self "__iter__" [] true w = .ok (.res r) w1 →
      slotTpIter rt self w = .ok r w1) ∧
    (∀ e, maybeCallSpecial rt self "__iter__" [] true w = .err e w1 →
      slotTpIter rt self w = .err e w1) ∧
    (maybeCallSpecial rt self "__iter__" [] true w = .ok .isNone w1 →
      slotTpIter rt self w =
        (typeErr s!"'{trunc 200 (typeName w1 self)}' object is not iterable" : M Val) w1) ∧
    (maybeCallSpecial rt self "__iter__" [] true w = .ok .missing w1 →
      (∀ w2, lookupMethodEx rt self "__getitem__" false w1 = .ok .missing w2 →
        slotTpIter rt self w =
          (typeErr s!"'{trunc 200 (typeName w2 self)}' object is not iterable" : M Val) w2) ∧
      (∀ l w2, lookupMethodEx rt self "__getitem__" false w1 = .ok l w2 →
        (∀ f, l = .unbound f ∨ l = .bound f → slotTpIter rt self w = pySeqIterNew self w2)) ∧
      (∀ c m v w2, lookupMethodEx rt self "__getitem__" false w1 = .err (.exc c m v) w2 →
        slotTpIter rt self w =
          (typeErr s!"'{trunc 200 (typeName w2 self)}' object is not iterable" : M Val) w2))

theorem slotTpIterExact_proven : SlotTpIterExact := by
  intro rt self w w1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r h; simp [slotTpIter, h]
  · intro e h; simp [slotTpIter, h]
  · intro h; simp [slotTpIter, h]
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro w2 h2; simp [slotTpIter, h, hasDunderGetitem, h2]
    · intro l w2 h2 f hf
      rcases hf with rfl | rfl <;> simp [slotTpIter, h, hasDunderGetitem, h2]
    · intro c m v w2 h2; simp [slotTpIter, h, hasDunderGetitem, h2]

/-! ## `slot_sq_length` -/

/-- **`slot_sq_length`, every branch.** `Objects/typeobject.c:10718-10745`: `__len__` is called;
its result goes through `_PyNumber_Index` (so a non-integer raises that function's `TypeError`,
and an `int` subclass is kept); a negative value raises
`ValueError("__len__() should return >= 0")`; a value above `PY_SSIZE_T_MAX` raises
`OverflowError` naming the type of the result; otherwise it is the length. Exceptions from
`__len__` and `__index__` propagate. -/
def SlotSqLengthExact : Prop :=
  ∀ (rt : Rt) (self : Val) (w w1 : World),
    (∀ e, vectorcallMethod rt "__len__" [self] w = .err e w1 → slotSqLength rt self w = .err e w1) ∧
    (∀ r, vectorcallMethod rt "__len__" [self] w = .ok r w1 →
      (∀ e w2, numberIndex rt r w1 = .err e w2 → slotSqLength rt self w = .err e w2) ∧
      (∀ v i w2, numberIndex rt r w1 = .ok v w2 → intOf w2 v = some i →
        (i < 0 → slotSqLength rt self w = (valueErr "__len__() should return >= 0" : M Int) w2) ∧
        (0 ≤ i → i ≤ PyLean.ssizeMax → slotSqLength rt self w = .ok i w2) ∧
        (PyLean.ssizeMax < i → slotSqLength rt self w =
          (raiseC B.OverflowError s!"cannot fit '{trunc 200 (typeName w2 v)}' into an index-sized integer" : M Int) w2)))

theorem slotSqLengthExact_proven : SlotSqLengthExact := by
  intro rt self w w1
  refine ⟨?_, ?_⟩
  · intro e h; simp [slotSqLength, h]
  · intro r h
    refine ⟨?_, ?_⟩
    · intro e w2 h2; simp [slotSqLength, h, h2]
    · intro v i w2 h2 hi
      have hn : numberIndex rt v w2 = .ok v w2 := by simp [numberIndex, hi]
      have hp : pyNumberIndex rt v w2 = .ok i w2 := by simp [pyNumberIndex, hn, hi]
      refine ⟨?_, ?_, ?_⟩
      · intro hneg; simp [slotSqLength, h, h2, hi, hneg]
      · intro h0 hmax
        have hnn : ¬ i < 0 := by omega
        have hs : inSsize i = true := by
          simp only [inSsize, Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · have : PyLean.ssizeMin ≤ 0 := by decide
            omega
          · exact hmax
        simp [slotSqLength, h, h2, hi, hnn, numberAsSsize, hp, hs]
      · intro hbig
        have hnn : ¬ i < 0 := by
          have : (0 : Int) ≤ PyLean.ssizeMax := by decide
          omega
        have hs : inSsize i = false := by
          simp only [inSsize, Bool.and_eq_false_iff, decide_eq_false_iff_not]
          right; omega
        simp [slotSqLength, h, h2, hi, hnn, numberAsSsize, hp, hs]

/-! ## `slot_nb_index` -/

/-- **`slot_nb_index` calls `__index__` and returns its result unchanged.**
`Objects/typeobject.c:10948-10952` is `vectorcall_method(__index__, [self])` (`:3156-3175`, with
`lookup_method`, `:3038-3080`): `__index__` is looked up on the type; missing raises
`AttributeError('__index__')`; a method descriptor is called with `self`; another descriptor is
bound by `__get__` (whose exceptions, `AttributeError` included, propagate) and called; a plain
value is called. The call's result is returned whatever it is: checking it is
`_PyNumber_Index`'s job (`Objects/abstract.c:1422-1427`). Stated on `callUnaryNb` with the generic
slot, the dispatch through `nb_index`. -/
def SlotNbIndexExact : Prop :=
  ∀ (rt : Rt) (self : Val) (w : World),
    (findInMro w (typeOf w self) "__index__" = none →
      callUnaryNb rt .nb_index "__index__" .generic self w = (attrErr "__index__" : M Val) w) ∧
    (∀ f, findInMro w (typeOf w self) "__index__" = some f →
      (tdata w (typeOf w f)).methodDescriptor = true →
      callUnaryNb rt .nb_index "__index__" .generic self w = rt.call f [self] [] w) ∧
    (∀ f, findInMro w (typeOf w self) "__index__" = some f →
      (tdata w (typeOf w f)).methodDescriptor = false →
      slotOf w (typeOf w f) .tp_descr_get = none →
      callUnaryNb rt .nb_index "__index__" .generic self w = rt.call f [] [] w) ∧
    (∀ f g w', findInMro w (typeOf w self) "__index__" = some f →
      (tdata w (typeOf w f)).methodDescriptor = false →
      slotOf w (typeOf w f) .tp_descr_get = some g →
      (∀ v, callDescrGet rt g f (some self) (some (.obj (typeOf w self))) w = .ok v w' →
        callUnaryNb rt .nb_index "__index__" .generic self w = rt.call v [] [] w') ∧
      (∀ e, callDescrGet rt g f (some self) (some (.obj (typeOf w self))) w = .err e w' →
        callUnaryNb rt .nb_index "__index__" .generic self w = .err e w'))

theorem slotNbIndexExact_proven : SlotNbIndexExact := by
  intro rt self w
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; simp [callUnaryNb, vectorcallMethod, lookupMethodEx, h, attrErr, raiseC]
  · intro f h hm; simp [callUnaryNb, vectorcallMethod, lookupMethodEx, h, hm, callUnbound]
  · intro f h hm hg; simp [callUnaryNb, vectorcallMethod, lookupMethodEx, h, hm, hg, callUnbound]
  · intro f g w' h hm hg
    refine ⟨fun v hd => ?_, fun e hd => ?_⟩
    · simp [callUnaryNb, vectorcallMethod, lookupMethodEx, h, hm, hg, hd, callUnbound]
    · simp [callUnaryNb, vectorcallMethod, lookupMethodEx, h, hm, hg, hd]

/-! ## `method_is_overloaded` -/

/-- **`method_is_overloaded`, every branch.** `Objects/typeobject.c:10643-10670`: the name is
looked up on the type of the right operand, then of the left one; missing on the right is
`false`, missing on the left (only) is `true`, both present is `a != b` by
`PyObject_RichCompareBool` (identity first, then `__ne__`); a lookup or comparison exception
propagates. -/
def MethodIsOverloadedExact : Prop :=
  ∀ (rt : Rt) (l r : Val) (n : Name) (w w1 w2 : World),
    (rt.getOptionalAttr (.obj (typeOf w r)) n w = .ok none w1 →
      methodIsOverloaded rt l r n w = .ok false w1) ∧
    (∀ e, rt.getOptionalAttr (.obj (typeOf w r)) n w = .err e w1 →
      methodIsOverloaded rt l r n w = .err e w1) ∧
    (∀ b, rt.getOptionalAttr (.obj (typeOf w r)) n w = .ok (some b) w1 →
      (rt.getOptionalAttr (.obj (typeOf w1 l)) n w1 = .ok none w2 →
        methodIsOverloaded rt l r n w = .ok true w2) ∧
      (∀ e, rt.getOptionalAttr (.obj (typeOf w1 l)) n w1 = .err e w2 →
        methodIsOverloaded rt l r n w = .err e w2) ∧
      (∀ a, rt.getOptionalAttr (.obj (typeOf w1 l)) n w1 = .ok (some a) w2 →
        methodIsOverloaded rt l r n w = richCompareBool rt a b .ne w2))

theorem methodIsOverloadedExact_proven : MethodIsOverloadedExact := by
  intro rt l r n w w1 w2
  refine ⟨?_, ?_, ?_⟩
  · intro h; simp [methodIsOverloaded, h]
  · intro e h; simp [methodIsOverloaded, h]
  · intro b h
    refine ⟨?_, ?_, ?_⟩
    · intro h2; simp [methodIsOverloaded, h, h2]
    · intro e h2; simp [methodIsOverloaded, h, h2]
    · intro a h2; simp [methodIsOverloaded, h, h2]

/-! ## `wrap_binaryfunc_l`, `wrap_binaryfunc_r` -/

/-- **`wrap_binaryfunc_l` and `_r`, both branches.** `Objects/typeobject.c:9996-10018`: anything
but exactly one argument raises `check_num_args`'s `TypeError` ("expected 1 argument, got N");
with one argument `other`, `x.__add__(other)` calls the slot function with `(x, other)` and
`x.__radd__(other)` with `(other, x)`. Precondition: `wrap_binaryfunc_l` serves number slots only,
a fact of the `slotdefs` table. -/
def WrapBinaryExact : Prop :=
  ∀ (rt : Rt) (p : SlotDef) (f : SlotFn) (self : Val) (args : List Val) (w : World),
    (p.wrapper = some .binaryR →
      (args.length ≠ 1 → wrapperApply rt p f self args [] w = (typeErr (argCountMsg 1 args.length) : M Val) w) ∧
      (∀ other, args = [other] → wrapperApply rt p f self args [] w = callNbBinary rt p.slot f other self w)) ∧
    (p.wrapper = some .binaryL → p.slot.group = .number →
      (args.length ≠ 1 → wrapperApply rt p f self args [] w = (typeErr (argCountMsg 1 args.length) : M Val) w) ∧
      (∀ other, args = [other] → wrapperApply rt p f self args [] w = callNbBinary rt p.slot f self other w))

theorem wrapBinaryExact_proven : WrapBinaryExact := by
  intro rt p f self args w
  refine ⟨fun h => ⟨fun hl => ?_, fun other ho => ?_⟩, fun h hg => ⟨fun hl => ?_, fun other ho => ?_⟩⟩
  · exact wrapperArity1_proven rt p f self args .eq .binaryR w h (by simp) hl
  · subst ho; exact (wrapBinarySwaps_proven rt p f self other w).1 h
  · obtain ⟨n, s, g, wr⟩ := p
    simp only at h
    subst h
    simp [wrapperApply, checkNumArgs, hl, typeErr, raiseC]
  · subst ho; exact (wrapBinarySwaps_proven rt p f self other w).2 h hg

end PyLean.TypeObj
