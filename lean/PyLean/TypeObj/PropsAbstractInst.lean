import PyLean.TypeObj.PropsAbstractSeq

/-!
`isinstance` and `issubclass` in `Objects/abstract.c`, every branch: `abstract_get_bases`,
`abstract_issubclass`, `object_isinstance`, `object_recursive_isinstance` (with the union
branch) and `recursive_issubclass`.

The hooks are the runtime's: `PyObject_GetOptionalAttr` for `__bases__` and `__class__`,
`_PyObject_LookupSpecial` for `__instancecheck__`, `PyObject_Call` and `PyObject_IsTrue`. Each
may raise, re-enter, or change the world, and later steps see the world it left. `fuel` stands
for the recursion limit (`_Py_EnterRecursiveCall`); running out is not a Python outcome.
-/

namespace PyLean.TypeObj

/-- **`abstract_get_bases`, every branch**: a failed lookup propagates; a missing `__bases__` is
`NULL`; a tuple (or tuple subclass) is returned; any other object is `NULL` with no error.
`Objects/abstract.c:2522-2532`. -/
def AbstractGetBasesExact : Prop :=
  ∀ (rt : Rt) (cls : Val) (w : World),
    (∀ e w1, rt.getOptionalAttr cls "__bases__" w = .err e w1 →
      abstractGetBases rt cls w = .err e w1) ∧
    (∀ w1, rt.getOptionalAttr cls "__bases__" w = .ok none w1 →
      abstractGetBases rt cls w = .ok none w1) ∧
    (∀ b xs w1, rt.getOptionalAttr cls "__bases__" w = .ok (some b) w1 → tupleOf w1 b = some xs →
      abstractGetBases rt cls w = .ok (some xs) w1) ∧
    (∀ b w1, rt.getOptionalAttr cls "__bases__" w = .ok (some b) w1 → tupleOf w1 b = none →
      abstractGetBases rt cls w = .ok none w1)

theorem abstractGetBasesExact_proven : AbstractGetBasesExact := by
  intro rt cls w
  refine ⟨fun e w1 h => ?_, fun w1 h => ?_, fun b xs w1 h ht => ?_, fun b w1 h ht => ?_⟩
  · simp [abstractGetBases, h]
  · simp [abstractGetBases, h]
  · simp [abstractGetBases, h, ht]
  · simp [abstractGetBases, h, ht]

/-- **`abstract_issubclass`, every branch.** `derived is cls` answers true with no lookup;
otherwise the bases of `derived`: a failed lookup propagates, none or `()` answers false, one base
continues the walk from it, and several are tried in order, stopping at the first true answer or
exception. `Objects/abstract.c:2536-2584`. -/
def AbstractIssubclassExact : Prop :=
  ∀ (rt : Rt) (fuel : Nat) (d c : Val) (w : World),
    (d.is c = true → abstractIssubclass rt (fuel + 1) d c w = .ok true w) ∧
    (d.is c = false →
      abstractIssubclass rt (fuel + 1) d c w =
        match abstractGetBases rt d w with
        | .err e w1 => .err e w1
        | .ok none w1 => .ok false w1
        | .ok (some []) w1 => .ok false w1
        | .ok (some [b]) w1 => abstractIssubclass rt fuel b c w1
        | .ok (some (b1 :: b2 :: bs)) w1 => abstractAny rt fuel (b1 :: b2 :: bs) c w1) ∧
    abstractAny rt fuel [] c w = .ok false w ∧
    (∀ b rest, abstractAny rt (fuel + 1) (b :: rest) c w =
      match abstractIssubclass rt (fuel + 1) b c w with
      | .ok true w1 => .ok true w1
      | .ok false w1 => abstractAny rt fuel rest c w1
      | .err e w1 => .err e w1)

theorem abstractIssubclassExact_proven : AbstractIssubclassExact := by
  intro rt fuel d c w
  refine ⟨fun h => ?_, fun h => ?_, ?_, fun b rest => ?_⟩
  · simp [abstractIssubclass, h]
  · simp only [abstractIssubclass, h, Bool.false_eq_true, ite_false, M.bind_app]
    cases abstractGetBases rt d w with
    | err e w1 => rfl
    | ok bs w1 =>
      rcases bs with _ | ⟨_ | ⟨b, _ | ⟨b2, bs⟩⟩⟩ <;> rfl
  · simp [abstractAny]
  · simp only [abstractAny, M.bind_app]
    cases abstractIssubclass rt (fuel + 1) b c w with
    | err e w1 => rfl
    | ok x w1 => cases x <;> rfl

/-- `check_class(cls, msg)`, `Objects/abstract.c:2587-2600`, written out: `NULL` bases with no
error set is the `TypeError` `msg`, a lookup error propagates. -/
def checkClassSpec (rt : Rt) (cls : Val) (msg : String) (w : World) : R Unit :=
  match abstractGetBases rt cls w with
  | .err e w1 => .err e w1
  | .ok none w1 => .err (.exc B.TypeError msg none) w1
  | .ok (some _) w1 => .ok () w1

theorem checkClass_spec (rt : Rt) (cls : Val) (msg : String) (w : World) :
    checkClass rt cls msg w = checkClassSpec rt cls msg w := by
  unfold checkClass checkClassSpec
  simp only [M.bind_app]
  cases abstractGetBases rt cls w with
  | err e w1 => rfl
  | ok b w1 => cases b <;> simp [typeErr, raiseC]

/-- **`object_isinstance`, every branch.** For a class: a real subtype answers true with no
lookup; otherwise `inst.__class__` is read (an exception propagates, a missing one is false) and
counts only if it is a class other than `type(inst)` (re-read after the lookup) and a subtype.
For a non-class: `check_class` with the `isinstance() arg 2` message, then `inst.__class__`,
then `abstract_issubclass`. `Objects/abstract.c:2603-2636`. -/
def ObjectIsinstanceExact : Prop :=
  ∀ (rt : Rt) (inst cls : Val) (w : World),
    (∀ ca, asType w cls = some ca → isSubtype w (typeOf w inst) ca = true →
      objectIsinstance rt inst cls w = .ok true w) ∧
    (∀ ca, asType w cls = some ca → isSubtype w (typeOf w inst) ca = false →
      objectIsinstance rt inst cls w =
        match rt.getOptionalAttr inst "__class__" w with
        | .err e w1 => .err e w1
        | .ok none w1 => .ok false w1
        | .ok (some icls) w1 =>
          .ok (match asType w1 icls with
            | some ia => ia != typeOf w1 inst && isSubtype w1 ia ca
            | none => false) w1) ∧
    (asType w cls = none →
      objectIsinstance rt inst cls w =
        match checkClassSpec rt cls
            "isinstance() arg 2 must be a type, a tuple of types, or a union" w with
        | .err e w1 => .err e w1
        | .ok () w1 =>
          match rt.getOptionalAttr inst "__class__" w1 with
          | .err e w2 => .err e w2
          | .ok none w2 => .ok false w2
          | .ok (some icls) w2 => abstractIssubclass rt walkFuel icls cls w2)

theorem objectIsinstanceExact_proven : ObjectIsinstanceExact := by
  intro rt inst cls w
  refine ⟨fun ca h1 h2 => ?_, fun ca h1 h2 => ?_, fun h => ?_⟩
  · simp [objectIsinstance, h1, h2]
  · simp only [objectIsinstance, M.bind_app, getW_app, h1, h2, Bool.false_eq_true, ite_false]
    cases rt.getOptionalAttr inst "__class__" w with
    | err e w1 => rfl
    | ok ic w1 =>
      cases ic with
      | none => rfl
      | some icls =>
        simp only [M.bind_app, getW_app]
        cases hia : asType w1 icls with
        | none => simp
        | some ia => by_cases hne : ia = typeOf w1 inst <;> simp [hne]
  · simp only [objectIsinstance, M.bind_app, getW_app, h, ← checkClass_spec]
    cases checkClass rt cls "isinstance() arg 2 must be a type, a tuple of types, or a union" w with
    | err e w1 => rfl
    | ok u w1 =>
      cases u
      simp only
      cases rt.getOptionalAttr inst "__class__" w1 with
      | err e w2 => rfl
      | ok ic w2 => cases ic <;> rfl

/-- **`object_recursive_isinstance`, every branch, in source order.** `type(inst) is cls`
answers true; an exact `type` second argument goes to `object_isinstance`; a union is replaced
by its `args` tuple; a tuple (or tuple subclass) is "any", stopping at the first true answer or
exception; otherwise `__instancecheck__` looked up on the type of `cls` decides through the truth
of its result (a failed lookup propagates), and with no checker `object_isinstance` decides.
`Objects/abstract.c:2639-2700`. -/
def IsinstanceExact : Prop :=
  ∀ (rt : Rt) (fuel : Nat) (inst cls : Val) (w : World),
    ((Val.obj (typeOf w inst)).is cls = true →
      objectRecursiveIsinstance rt (fuel + 1) inst cls w = .ok true w) ∧
    ((Val.obj (typeOf w inst)).is cls = false →
      (typeOf w cls = B.type →
        objectRecursiveIsinstance rt (fuel + 1) inst cls w = objectIsinstance rt inst cls w) ∧
      (typeOf w cls ≠ B.type → unionCheck w cls = true →
        objectRecursiveIsinstance rt (fuel + 1) inst cls w =
          objectRecursiveIsinstance.anyTuple rt fuel inst (unionArgs w cls) w) ∧
      (∀ xs, typeOf w cls ≠ B.type → unionCheck w cls = false → tupleOf w cls = some xs →
        objectRecursiveIsinstance rt (fuel + 1) inst cls w =
          objectRecursiveIsinstance.anyTuple rt fuel inst xs w) ∧
      (typeOf w cls ≠ B.type → unionCheck w cls = false → tupleOf w cls = none →
        objectRecursiveIsinstance rt (fuel + 1) inst cls w =
          match lookupSpecial rt cls "__instancecheck__" w with
          | .err e w1 => .err e w1
          | .ok (some checker) w1 =>
            match rt.call checker [inst] [] w1 with
            | .ok r w2 => rt.isTrue r w2
            | .err e w2 => .err e w2
          | .ok none w1 => objectIsinstance rt inst cls w1)) ∧
    objectRecursiveIsinstance.anyTuple rt fuel inst [] w = .ok false w ∧
    (∀ x xs, objectRecursiveIsinstance.anyTuple rt fuel inst (x :: xs) w =
      match objectRecursiveIsinstance rt fuel inst x w with
      | .ok true w1 => .ok true w1
      | .ok false w1 => objectRecursiveIsinstance.anyTuple rt fuel inst xs w1
      | .err e w1 => .err e w1)

theorem isinstanceExact_proven : IsinstanceExact := by
  intro rt fuel inst cls w
  refine ⟨fun h => ?_, fun h => ⟨fun ht => ?_, fun ht hu => ?_, fun xs ht hu hx => ?_,
    fun ht hu hx => ?_⟩, ?_, fun x xs => ?_⟩
  · simp [objectRecursiveIsinstance, h]
  · simp [objectRecursiveIsinstance, h, ht]
  · have ht' : (typeOf w cls == B.type) = false := by simp [ht]
    simp [objectRecursiveIsinstance, h, ht, hu, tupleOf]
  · have ht' : (typeOf w cls == B.type) = false := by simp [ht]
    simp [objectRecursiveIsinstance, h, ht, hu, hx]
  · have ht' : (typeOf w cls == B.type) = false := by simp [ht]
    simp only [objectRecursiveIsinstance, M.bind_app, getW_app, h, ht', hu, hx,
      Bool.false_eq_true, ite_false]
    cases lookupSpecial rt cls "__instancecheck__" w with
    | err e w1 => rfl
    | ok ch w1 =>
      cases ch with
      | none => rfl
      | some checker =>
        simp only [M.bind_app]
        cases rt.call checker [inst] [] w1 <;> rfl
  · simp [objectRecursiveIsinstance.anyTuple]
  · simp only [objectRecursiveIsinstance.anyTuple, M.bind_app]
    cases objectRecursiveIsinstance rt fuel inst x w with
    | err e w1 => rfl
    | ok b w1 => cases b <;> rfl

/-- **`recursive_issubclass`, every branch.** Two classes: `PyType_IsSubtype`, with no lookup.
Otherwise `check_class(derived)` with the `arg 1` message; then, unless `cls` is a union,
`check_class(cls)` with the `arg 2` message; then `abstract_issubclass`.
`Objects/abstract.c:2712-2729`. -/
def RecursiveIssubclassExact : Prop :=
  ∀ (rt : Rt) (derived cls : Val) (w : World),
    (∀ c d, asType w cls = some c → asType w derived = some d →
      recursiveIssubclass rt derived cls w = .ok (isSubtype w d c) w) ∧
    ((asType w cls = none ∨ asType w derived = none) →
      recursiveIssubclass rt derived cls w =
        match checkClassSpec rt derived "issubclass() arg 1 must be a class" w with
        | .err e w1 => .err e w1
        | .ok () w1 =>
          if unionCheck w1 cls then abstractIssubclass rt walkFuel derived cls w1
          else match checkClassSpec rt cls
              "issubclass() arg 2 must be a class, a tuple of classes, or a union" w1 with
            | .err e w2 => .err e w2
            | .ok () w2 => abstractIssubclass rt walkFuel derived cls w2)

theorem recursiveIssubclassExact_proven : RecursiveIssubclassExact := by
  intro rt derived cls w
  refine ⟨fun c d h1 h2 => ?_, fun h => ?_⟩
  · simp [recursiveIssubclass, h1, h2]
  · unfold recursiveIssubclass
    simp only [M.bind_app, getW_app]
    cases hc : asType w cls <;> cases hd : asType w derived <;>
      (try (rcases h with h | h <;> simp_all; done)) <;>
      simp only [M.bind_app, checkClass_spec] <;>
      (cases checkClassSpec rt derived "issubclass() arg 1 must be a class" w with
        | err e w1 => rfl
        | ok u w1 =>
          cases u
          simp only [getW_app]
          by_cases hu : unionCheck w1 cls = true
          · simp [hu]
          · simp only [hu, Bool.not_false, ite_true, M.bind_app, checkClass_spec,
              Bool.false_eq_true, ite_false]
            cases checkClassSpec rt cls
              "issubclass() arg 2 must be a class, a tuple of classes, or a union" w1 <;> rfl)

end PyLean.TypeObj
