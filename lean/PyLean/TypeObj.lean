import PyLean.Registry
import PyLean.TypeObj.Diff
import PyLean.TypeObj.PropsTypeNew
import PyLean.TypeObj.PropsBuffer
import PyLean.TypeObj.PropsType2
import PyLean.TypeObj.ExcProps
import PyLean.TypeObj.PropsList
import PyLean.TypeObj.PropsDict
import PyLean.TypeObj.PropsReduce
import PyLean.TypeObj.PropsTotal

/-!
The data model: `Objects/typeobject.c`, `Objects/object.c`, `Objects/abstract.c`,
`Objects/descrobject.c`, `Objects/funcobject.c`, `Objects/methodobject.c`,
`Objects/classobject.c`, `Objects/call.c`, `Objects/exceptions.c`, CPython 3.14.7.

`TypeObj/Model.lean` is the object model and its documented API. `Attr`, `Protocol`,
`TypeNew`, `Call`, `Exceptions` mirror the C code; `Interp` ties the recursion;
`Builtins` builds the builtin types from `BuiltinTable` (generated from CPython);
`Harness` runs difftest scenarios.

Properties are stated over all worlds and all `rt : Rt`, that is, for every class structure
and every behaviour of user-defined methods. Hypotheses state which class structure a case
is about (where a name is found, what kind of descriptor it is). Well-formedness hypotheses
(`SubtypeOrder`, `Linearized`) are documented type invariants.
-/

namespace PyLean.TypeObj

open PyLean.Registry

private def p (id file : String) (fns : List String) (statement source : String)
    (prop thm : Lean.Name) (notes : String := "") : Entry :=
  { id := id, pyFile := file, pyFns := fns, statement := statement, source := source,
    status := .proven, prop := prop, thm := some thm, notes := notes }

private def ty := "Objects/typeobject.c"
private def ob := "Objects/object.c"
private def ab := "Objects/abstract.c"
private def ca := "Objects/call.c"

def entries : List Entry := [
  -- C3
  p "typeobj-c3-local-precedence" ty
    ["tail_contains", "pmerge", "mro_implementation_unlocked"]
    "For all bases and base MROs, a successful slow-path linearization lists the bases in their declared order."
    "typeobject.c:3131-3133 (local precedence order)"
    ``C3LocalPrecedence ``c3LocalPrecedence_proven,
  p "typeobj-c3-monotonic" ty ["pmerge", "mro_implementation_unlocked"]
    "For all bases and base MROs, the slow-path MRO extends the MRO of every base without reordering."
    "typeobject.c:3135-3137 (monotonicity)"
    ``C3Monotonic ``c3Monotonic_proven,
  p "typeobj-c3-monotonic-transitive" ty ["pmerge", "mro_implementation_unlocked"]
    "In every hierarchy linearized by mro_implementation, for every class t and every s in its MRO, the MRO of s is a sublist of the MRO of t."
    "typeobject.c:3135-3137; precondition Linearized is the type invariant of classes with the default mro()"
    ``C3MonotonicTransitive ``c3MonotonicTransitive_proven,
  p "typeobj-c3-self-head" ty []
    "In a linearized hierarchy each class is the first entry of its own MRO."
    "invariant: the fast path and pmerge both start with the class"
    ``C3SelfHead ``c3SelfHead_proven,
  p "typeobj-c3-terminates" ty ["pmerge"]
    "pmerge stops within as many steps as there are items, for all inputs: the `goto again` loop always removes one."
    "invariant: no hang"
    ``C3Terminates ``c3Terminates_proven,
  p "typeobj-c3-nodup" ty ["pmerge"]
    "A successful merge of duplicate-free lists has no duplicates."
    "invariant"
    ``C3NoDuplicates ``c3NoDuplicates_proven,
  p "typeobj-c3-complete" ty ["pmerge"]
    "A class is in the merge result exactly when it is in some input list."
    "invariant"
    ``C3Complete ``c3Complete_proven,
  p "typeobj-c3-fast-path" ty ["mro_implementation_unlocked"]
    "With one base whose MRO starts with it and has no repeats, the fast path at :3352 gives what pmerge gives."
    "fast path vs slow path, typeobject.c:3352-3372"
    ``C3FastPathAgrees ``c3FastPathAgrees_proven
    "A custom mro() can break the precondition; class creation then fails or keeps the custom order. Reached only through a metaclass overriding mro().",
  p "typeobj-c3-failure-rule" ty ["pmerge", "set_mro_error"]
    "pmerge reports a conflict exactly when no list head is free of all tails while some list is non-empty."
    "typeobject.c:3318-3321"
    ``C3FailureRule ``c3FailureRule_proven,
  p "typeobj-c3-duplicate-bases" ty ["check_duplicates"]
    "A duplicate-free tuple of bases passes check_duplicates."
    "typeobject.c:3126-3127"
    ``C3DuplicateBaseRejected ``c3DuplicateBaseRejected_proven,
  -- metaclass
  p "typeobj-metaclass-winner" ty ["_PyType_CalculateMetaclass"]
    "Under a reflexive transitive subtype order, the winner is a subclass of the given metaclass and of the metaclass of every base."
    "typeobject.c:3919 (most derived metatype); SubtypeOrder holds for C3 hierarchies"
    ``MetaclassWinner ``metaclassWinner_proven,
  p "typeobj-metaclass-conflict" ty ["_PyType_CalculateMetaclass"]
    "A metaclass conflict means two metaclasses, neither a subclass of the other."
    "typeobject.c:3945"
    ``MetaclassConflictReal ``metaclassConflictReal_proven,
  -- hash and classes
  p "typeobj-hash-none-eq" ty ["type_ready_set_hash"]
    "A class with no tp_hash and no __hash__ in its dict gets __hash__ = None and tp_hash = PyObject_HashNotImplemented."
    "typeobject.c:8775-8779"
    ``HashNoneWhenEqDefined ``hashNoneWhenEqDefined_proven,
  p "typeobj-overrides-hash" ty []
    "A class dict with __eq__ or __hash__ blocks the joint inheritance of tp_richcompare and tp_hash."
    "typeobject.c:8381-8394"
    ``OverridesHashBlocksInherit ``overridesHashBlocksInherit_proven,
  p "typeobj-dunder-name" ty []
    "is_dunder_name accepts only names longer than 4 starting with two underscores."
    "typeobject.c:5776"
    ``IsDunderNameShape ``isDunderNameShape_proven,
  p "typeobj-mangle-dunders" ty []
    "_Py_Mangle leaves a __slots__ name unchanged unless it starts with __ and does not end with __."
    "language reference, private name mangling"
    ``MangleKeepsDunders ``mangleKeepsDunders_proven,
  p "typeobj-slots-must-be-str" ty []
    "A non-string __slots__ item raises TypeError with the message of :3870."
    "typeobject.c:3868-3872"
    ``SlotNotesIdentifier ``slotNotesIdentifier_proven,
  -- attribute lookup
  p "typeobj-lookup-first-in-mro" ty ["find_name_in_mro", "_PyType_Lookup"]
    "The type lookup of a name returns the value in the first class of the MRO whose dict has it."
    "docs: Customizing attribute access; typeobject.c:5748-5763"
    ``TypeLookupFirstInMro ``typeLookupFirstInMro_proven,
  p "typeobj-getattr-data-descr" ob ["_PyObject_GenericGetAttrWithDict"]
    "If the MRO provides a data descriptor, generic getattr calls its __get__ and never reads the instance dict, for every instance dict and __get__."
    "docs: Invoking Descriptors"
    ``GenericGetattrDataDescriptorFirst ``genericGetattrDataDescriptorFirst_proven,
  p "typeobj-getattr-instance-dict" ob ["_PyObject_GenericGetAttrWithDict", "_PyObject_GetDictPtr"]
    "With no data descriptor, a name in the instance dict is returned, with no __get__ call."
    "docs: Invoking Descriptors"
    ``GenericGetattrInstanceDictNext ``genericGetattrInstanceDictNext_proven,
  p "typeobj-getattr-nondata-descr" ob ["_PyObject_GenericGetAttrWithDict"]
    "With no data descriptor and nothing in the instance dict, a non-data descriptor is bound."
    "docs: Invoking Descriptors"
    ``GenericGetattrNonDataDescriptor ``genericGetattrNonDataDescriptor_proven,
  p "typeobj-getattr-class-attr" ob ["_PyObject_GenericGetAttrWithDict"]
    "A plain class attribute is returned unchanged when the instance dict lacks the name."
    "docs: Invoking Descriptors"
    ``GenericGetattrPlainClassAttr ``genericGetattrPlainClassAttr_proven,
  p "typeobj-getattr-suppress" ob ["_PyObject_GenericGetAttrWithDict"]
    "With suppress set, a missing name returns NULL with no exception."
    "object.c:1815"
    ``GenericGetattrMissingSuppressed ``genericGetattrMissingSuppressed_proven,
  p "typeobj-type-getattro-meta-data" ty ["_Py_type_getattro_impl"]
    "A data descriptor on the metaclass wins over the class's own attributes."
    "docs: Invoking Descriptors; typeobject.c:6132"
    ``TypeGetattroMetaDataDescriptorFirst ``typeGetattroMetaDataDescriptorFirst_proven,
  p "typeobj-type-getattro-class-attr" ty ["_Py_type_getattro_impl"]
    "Without a metaclass data descriptor, the class's own attribute is bound with obj = NULL."
    "typeobject.c:6146-6160"
    ``TypeGetattroClassAttrNext ``typeGetattroClassAttrNext_proven,
  p "typeobj-setattr-descr" ob []
    "If the type has a descriptor with tp_descr_set, generic setattr calls it, for every instance dict state."
    "docs: Invoking Descriptors"
    ``GenericSetattrDescriptorFirst ``genericSetattrDescriptorFirst_proven,
  -- comparison
  p "typeobj-swapped-op" ob []
    "_Py_SwappedOp is an involution."
    "object.c:1039"
    ``SwappedInvolution ``swappedInvolution_proven,
  p "typeobj-richcomparebool-identity" ob ["PyObject_RichCompareBool"]
    "For every object, PyObject_RichCompareBool(x, x, ==) is true and (x, x, !=) false, with no user code run and the world unchanged."
    "object.c:1124-1125 (Guarantees that identity implies equality)"
    ``RichCompareBoolIdentity ``richCompareBoolIdentity_proven,
  p "typeobj-container-reflexive" "Objects/listobject.c" ["list_richcompare_impl", "tuple_richcompare"]
    "For every list of values, whatever their __eq__, xs == xs, not xs != xs, xs <= xs and not xs < xs, with no user code run."
    "docs: Comparisons (identity implies equality for container items)"
    ``ContainerEqReflexive ``containerEqReflexive_proven,
  p "typeobj-contains-identity" ab ["PySequence_Contains"]
    "A list or tuple membership test that returns False proves no item is identical to x."
    "docs: Membership test operations"
    ``ContainsIdentity ``containsIdentity_proven,
  p "typeobj-richcompare-subclass-first" ob ["do_richcompare", "PyObject_RichCompare"]
    "When type(u) is a proper subclass of type(v), the reflected comparison runs first and a non-NotImplemented result is final."
    "docs: Basic customization, __lt__ family; object.c:1052"
    ``RichcompareSubclassFirst ``richcompareSubclassFirst_proven,
  p "typeobj-richcompare-left-first" ob ["do_richcompare"]
    "Otherwise the left operand's slot runs first and a non-NotImplemented result is final."
    "object.c:1061"
    ``RichcompareLeftFirst ``richcompareLeftFirst_proven,
  p "typeobj-richcompare-defaults" ob ["do_richcompare", "object_richcompare", "_Py_BaseObject_RichCompare"]
    "For distinct objects of one type with object_richcompare, == is False and ordering raises the exact TypeError."
    "object.c:1073-1089"
    ``RichcompareDefaults ``richcompareDefaults_proven,
  p "typeobj-object-ne" ty ["object_richcompare"]
    "object.__ne__ negates the truth of tp_richcompare(==) unless that is NotImplemented."
    "typeobject.c:6981-6982"
    ``ObjectNeInvertsEq ``objectNeInvertsEq_proven,
  -- truth
  p "typeobj-istrue-singletons" ob []
    "True, False and None answer without any slot."
    "object.c:2063-2068"
    ``IsTrueSingletons ``isTrueSingletons_proven,
  p "typeobj-istrue-default" ob ["PyObject_IsTrue"]
    "An object with no nb_bool, mp_length and sq_length is true, with no user code run."
    "docs: Truth Value Testing"
    ``IsTrueDefaultTrue ``isTrueDefaultTrue_proven,
  p "typeobj-istrue-len" ob ["PyObject_IsTrue"]
    "With no nb_bool, truth is mp_length(x) > 0."
    "docs: Truth Value Testing"
    ``IsTrueLengthFallback ``isTrueLengthFallback_proven,
  p "typeobj-nb-bool-type" ty ["slot_nb_bool"]
    "A __bool__ returning a non-bool raises the exact TypeError."
    "typeobject.c:10234-10239"
    ``NbBoolMustReturnBool ``nbBoolMustReturnBool_proven,
  -- hash
  p "typeobj-slot-hash-not-minus-one" ty ["slot_tp_hash", "maybe_call_special_no_args"]
    "slot_tp_hash never returns -1, for every __hash__."
    "typeobject.c:10333 (-1 is reserved for errors)"
    ``SlotHashNotMinusOne ``slotHashNotMinusOne_proven,
  p "typeobj-slot-hash-range" ty ["slot_tp_hash"]
    "__hash__ results in Py_ssize_t range other than -1 are preserved."
    "typeobject.c:10320-10324"
    ``SlotHashPreservesRange ``slotHashPreservesRange_proven,
  p "typeobj-slot-hash-non-int" ty ["slot_tp_hash"]
    "A non-int __hash__ result raises the exact TypeError."
    "typeobject.c:10316"
    ``SlotHashNonInt ``slotHashNonInt_proven,
  p "typeobj-slot-hash-none" ty ["slot_tp_hash"]
    "__hash__ = None raises unhashable type."
    "docs: object.__hash__"
    ``SlotHashNoneUnhashable ``slotHashNoneUnhashable_proven,
  -- operators
  p "typeobj-binop-same-type" ab ["binary_op1"]
    "For operands of one type, a NotImplemented from the left slot is the result: the reflected method never runs."
    "docs: Emulating numeric types, note on identical types"
    ``BinaryOp1SameType ``binaryOp1SameType_proven,
  p "typeobj-binop-subclass-priority" ab ["binary_op1"]
    "If type(u) is a proper subclass of type(v) with a different slot, that slot runs first; a non-NotImplemented answer is final."
    "docs: Emulating numeric types, note on subclasses; abstract.c:957"
    ``BinaryOp1SubclassPriority ``binaryOp1SubclassPriority_proven,
  p "typeobj-binop-subclass-then-left" ab ["binary_op1"]
    "After the subclass slot says NotImplemented, only the left slot runs."
    "abstract.c:961-970"
    ``BinaryOp1SubclassThenLeft ``binaryOp1SubclassThenLeft_proven,
  p "typeobj-binop-left-then-right" ab ["binary_op1"]
    "For unrelated types the left slot runs, then the right."
    "abstract.c:919-927"
    ``BinaryOp1LeftThenRight ``binaryOp1LeftThenRight_proven,
  p "typeobj-binop-shared-slot" ab ["binary_op1"]
    "Operands sharing a slot function get one call."
    "abstract.c:947"
    ``BinaryOp1SharedSlotOnce ``binaryOp1SharedSlotOnce_proven,
  p "typeobj-binop-no-notimpl" ab ["binary_op", "binop_type_error"]
    "binary_op never returns NotImplemented."
    "invariant: NotImplemented is internal to the dispatch"
    ``BinaryOpNeverNotImplemented ``binaryOpNeverNotImplemented_proven,
  p "typeobj-add-concat" ab ["PyNumber_Add"]
    "sq_concat runs only after the number slots answered NotImplemented, and only for the left operand."
    "abstract.c:1128-1143"
    ``NumberAddConcatFallback ``numberAddConcatFallback_proven,
  p "typeobj-seq-repeat-index" ab []
    "A repeat count without __index__ raises the exact TypeError."
    "abstract.c:1157"
    ``SequenceRepeatNeedsIndex ``sequenceRepeatNeedsIndex_proven,
  p "typeobj-multiply-both-sides" ab ["PyNumber_Multiply"]
    "x * seq repeats seq by x when x has no sq_repeat."
    "abstract.c:1176-1178"
    ``NumberMultiplyBothSides ``numberMultiplyBothSides_proven,
  { id := "typeobj-imul-matches-mul", pyFile := ab, pyFns := ["PyNumber_InPlaceMultiply", "binary_iop1"]
    statement := "x *= seq takes the same sequence fallback as x * seq when x has no repeat slot."
    source := "the twin PyNumber_Multiply, abstract.c:1176, and the comment at abstract.c:1337-1339",
    status := .refuted, prop := ``InPlaceMultiplyMatchesMultiply,
    thm := some ``inPlaceMultiplyMatchesMultiply_refuted, bug := some "typeobj-imul-sequence-fallback" },
  -- conversions
  p "typeobj-index-identity" ab ["_PyNumber_Index"]
    "_PyNumber_Index of an int returns it without running __index__."
    "abstract.c:1406"
    ``IndexOfIntIdentity ``indexOfIntIdentity_proven,
  p "typeobj-index-required" ab ["_PyNumber_Index"]
    "Without __index__ the exact TypeError is raised."
    "abstract.c:1409-1413"
    ``IndexRequiresDunder ``indexRequiresDunder_proven,
  p "typeobj-index-result-int" ab ["_PyNumber_Index", "slot_nb_index"]
    "Whatever __index__ returns, _PyNumber_Index returns an int or raises."
    "abstract.c:1422-1427"
    ``IndexResultIsInt ``indexResultIsInt_proven,
  p "typeobj-as-ssize-clips" ab ["PyNumber_AsSsize_t"]
    "With err = NULL the result is the value clipped to Py_ssize_t range by sign."
    "abstract.c:1485-1494"
    ``AsSsizeClips ``asSsizeClips_proven,
  p "typeobj-len-range" ty ["slot_sq_length"]
    "For every __len__, slot_sq_length returns a value in [0, PY_SSIZE_T_MAX] or raises."
    "docs: object.__len__; typeobject.c:10032-10040"
    ``SlotLenInRange ``slotLenInRange_proven,
  p "typeobj-seq-getitem-negative" ab ["PySequence_GetItem"]
    "A negative index gets len(s) added once before sq_item."
    "abstract.c:1840-1849"
    ``SequenceGetItemNegativeIndex ``sequenceGetItemNegativeIndex_proven,
  p "typeobj-getitem-mapping-first" ab ["PyObject_GetItem"]
    "mp_subscript takes precedence over sq_item."
    "abstract.c:159-164"
    ``GetItemMappingFirst ``getItemMappingFirst_proven,
  p "typeobj-class-getitem" ab ["PyObject_GetItem"]
    "On a class without __getitem__ on its metaclass, C[k] calls C.__class_getitem__(k)."
    "docs: Emulating generic types"
    ``ClassGetitemFallback ``classGetitemFallback_proven,
  -- iteration
  p "typeobj-iter-checks" ab ["PyObject_GetIter"]
    "An __iter__ result that is not an iterator raises the exact TypeError."
    "abstract.c:2819-2825"
    ``GetIterChecksResult ``getIterChecksResult_proven,
  p "typeobj-iter-seq-fallback" ab ["PyObject_GetIter"]
    "A sequence with no tp_iter iterates through a seqiterobject."
    "abstract.c:2812-2814"
    ``GetIterSequenceFallback ``getIterSequenceFallback_proven,
  p "typeobj-iter-none" ty ["slot_tp_iter"]
    "__iter__ = None disables the __getitem__ fallback."
    "docs: object.__iter__, None blocks fallback; typeobject.c:10507"
    ``IterNoneNotIterable ``iterNoneNotIterable_proven,
  p "typeobj-seqiter-sticky" "Objects/iterobject.c" ["iter_iternext"]
    "An exhausted seqiterobject stays exhausted."
    "iterator protocol, docs: Iterator Types"
    ``SeqIterExhaustionSticky ``seqIterExhaustionSticky_proven,
  p "typeobj-contains-slot" ab []
    "x in y uses sq_contains when present."
    "abstract.c:2234"
    ``ContainsUsesSlot ``containsUsesSlot_proven,
  p "typeobj-contains-none" ty ["slot_sq_contains"]
    "__contains__ = None raises instead of falling back to iteration."
    "docs: object.__contains__; typeobject.c:10094"
    ``ContainsNoneNotContainer ``containsNoneNotContainer_proven,
  p "typeobj-itersearch-identity" ab ["_PySequence_IterSearch"]
    "An item identical to the searched object is found, whatever its __eq__."
    "abstract.c:2166"
    ``IterSearchIdentity ``iterSearchIdentity_proven,
  -- isinstance
  p "typeobj-isinstance-exact" ab ["object_recursive_isinstance"]
    "isinstance(x, type(x)) is true with no __instancecheck__ lookup."
    "abstract.c:2634-2637"
    ``IsinstanceExactType ``isinstanceExactType_proven,
  p "typeobj-isinstance-checker" ab ["object_recursive_isinstance"]
    "On a non-class second argument with __instancecheck__, the result is the truth of its call."
    "docs: Customizing instance and subclass checks"
    ``IsinstanceUsesChecker ``isinstanceUsesChecker_proven,
  p "typeobj-object-isinstance" ab ["object_isinstance"]
    "A real subtype answers true without reading __class__."
    "abstract.c:2600-2602"
    ``ObjectIsinstanceSubtype ``objectIsinstanceSubtype_proven,
  p "typeobj-issubclass-mro" ab ["recursive_issubclass"]
    "issubclass on classes is membership in the MRO."
    "abstract.c:2707-2709"
    ``RecursiveIssubclassMro ``recursiveIssubclassMro_proven,
  -- instance creation
  p "typeobj-excess-args" ty []
    "excess_args is false exactly when no argument was passed."
    "typeobject.c:6825"
    ``ExcessArgsIffAny ``excessArgsIffAny_proven,
  p "typeobj-object-new-init-table" ty ["object_new", "object_init", "excess_args"]
    "The table of excess-argument errors: overriding neither, __new__ only, or __init__ only gives the three behaviours of the comment before excess_args."
    "typeobject.c:6790-6830"
    ``ObjectNewInitTable ``objectNewInitTable_proven,
  p "typeobj-type-one-arg" ty []
    "type(x) returns the type of x with no __new__ call."
    "typeobject.c:2346-2354"
    ``TypeCallOneArg ``typeCallOneArg_proven,
  p "typeobj-init-skipped" ty ["type_call"]
    "__init__ is skipped when __new__ returns something that is not an instance of the class."
    "docs: object.__new__"
    ``TypeCallSkipsInit ``typeCallSkipsInit_proven,
  p "typeobj-init-result-type" ty ["type_call"]
    "tp_init comes from the type of the result of __new__."
    "typeobject.c:2382-2384"
    ``TypeCallInitsResultType ``typeCallInitsResultType_proven,
  p "typeobj-init-returns-none" ty ["slot_tp_init"]
    "A non-None __init__ result raises the exact TypeError."
    "docs: object.__init__"
    ``InitMustReturnNone ``initMustReturnNone_proven,
  -- binding
  p "typeobj-function-binding" "Objects/funcobject.c" []
    "A function binds from an instance and returns itself from the class."
    "docs: Functions and methods (descriptor howto)"
    ``FunctionBinding ``functionBinding_proven,
  p "typeobj-bound-method-self" "Objects/classobject.c" []
    "Calling a bound method calls the function with self prepended."
    "docs: Instance methods"
    ``BoundMethodPrependsSelf ``boundMethodPrependsSelf_proven,
  p "typeobj-classmethod-staticmethod" "Objects/funcobject.c" []
    "classmethod binds the class from class or instance; staticmethod returns the callable."
    "docs: Static Methods, Class Methods"
    ``ClassStaticBinding ``classStaticBinding_proven,
  p "typeobj-property-get" "Objects/descrobject.c" ["property_descr_get"]
    "A property from the class is itself, from an instance it calls fget."
    "docs: property"
    ``PropertyGet ``propertyGet_proven,
  { id := "typeobj-property-copy-doc", pyFile := "Objects/descrobject.c",
    pyFns := ["property_copy"]
    statement := "p.setter(f) keeps an explicit docstring of p, for property and its subclasses."
    source := "the twin behaviour of exact property; docs: property", status := .refuted,
    prop := ``PropertyCopyKeepsDoc, thm := some ``propertyCopyKeepsDoc_refuted,
    bug := some "typeobj-property-subclass-doc-lost" },
  { id := "typeobj-too-many-positional-bound", pyFile := "Python/ceval.c",
    pyFns := ["too_many_positional"]
    statement := "The minimum in the too-many-arguments message is not negative."
    source := "invariant", status := .refuted,
    prop := ``TooManyPositionalBound, thm := some ``tooManyPositionalBound_refuted,
    bug := some "typeobj-too-many-positional-negative-bound" },
  p "typeobj-special-lookup-type-only" ty []
    "If no class in the MRO has a special method, it is not found, even with the name in the instance dict."
    "docs: Special method lookup"
    ``SpecialLookupIgnoresInstance ``specialLookupIgnoresInstance_proven,
  p "typeobj-lookup-method-unbound" ty []
    "A method descriptor found on the type stays unbound and is called with self first."
    "typeobject.c:2910-2913"
    ``LookupMethodDescriptorUnbound ``lookupMethodDescriptorUnbound_proven,
  p "typeobj-missing-method" ty []
    "A missing method raises AttributeError(name) through lookup_method and gives NotImplemented through vectorcall_maybe."
    "typeobject.c:2903-2905, :3050"
    ``MissingMethodOutcomes ``missingMethodOutcomes_proven,
  p "typeobj-maybe-call-none" ty []
    "A special method set to None reads as defined-None for callers that pass attr_is_none."
    "typeobject.c:3073-3077"
    ``MaybeCallNone ``maybeCallNone_proven,
  p "typeobj-getattr-hook-found" ty ["_Py_slot_tp_getattr_hook"]
    "__getattr__ does not run when the default lookup finds the name."
    "docs: object.__getattr__"
    ``GetattrHookNotCalledWhenFound ``getattrHookNotCalledWhenFound_proven,
  p "typeobj-getattr-hook-missing" ty ["_Py_slot_tp_getattr_hook"]
    "__getattr__ runs, with the name, when the default lookup misses."
    "docs: object.__getattr__"
    ``GetattrHookCalledWhenMissing ``getattrHookCalledWhenMissing_proven,
  p "typeobj-getattribute-fallback" ty ["_Py_slot_tp_getattr_hook", "call_attribute"]
    "A __getattribute__ raising AttributeError falls back to __getattr__; any other exception propagates."
    "docs: object.__getattribute__"
    ``GetattributeAttributeErrorFallback ``getattributeAttributeErrorFallback_proven,
  p "typeobj-no-hook-dispatch" ty ["_Py_slot_tp_getattr_hook"]
    "With no __getattr__ the hook behaves as the plain dispatcher."
    "typeobject.c:10401-10407"
    ``NoHookSimpleDispatch ``noHookSimpleDispatch_proven,
  p "typeobj-optional-attr-agrees" ob ["PyObject_GetOptionalAttr", "PyObject_GetAttr"]
    "On a found attribute the suppressing and raising generic lookups return the same value and the same state."
    "fast path vs raising path, object.c:1336-1345"
    ``OptionalAttrAgrees ``optionalAttrAgrees_proven,
  p "typeobj-slot-setattr" ty []
    "Assignment goes to __setattr__, deletion to __delattr__."
    "typeobject.c:10448-10454"
    ``SlotSetattrDispatch ``slotSetattrDispatch_proven,
  p "typeobj-slot-descr-set" ty []
    "Assignment goes to __set__, deletion to __delete__."
    "typeobject.c:10556-10562"
    ``SlotDescrSetDispatch ``slotDescrSetDispatch_proven,
  p "typeobj-slot-descr-get" ty []
    "__get__ receives None for a missing instance; a descriptor whose __get__ is gone returns itself."
    "typeobject.c:10529-10543"
    ``SlotDescrGetArgs ``slotDescrGetArgs_proven,
  p "typeobj-slot-richcompare" ty []
    "A missing comparison method answers NotImplemented."
    "typeobject.c:10474-10479"
    ``SlotRichcompareMissing ``slotRichcompareMissing_proven,
  p "typeobj-slot-new" ty []
    "__new__ is found with getattr on the class and called with the class first."
    "typeobject.c:10592-10597"
    ``SlotNewPrependsType ``slotNewPrependsType_proven,
  p "typeobj-slot1bin-same-type" ty []
    "Same operand types: NotImplemented from __op__ is final, __rop__ does not run."
    "typeobject.c:10001-10003"
    ``Slot1BinSameType ``slot1BinSameType_proven,
  p "typeobj-method-is-overloaded" ty ["method_is_overloaded"]
    "A right type lacking the name is not overloaded; having it while the left lacks it is."
    "typeobject.c:9949-9962"
    ``MethodIsOverloadedTable ``methodIsOverloadedTable_proven,
  p "typeobj-wrap-binary" ty ["wrap_binaryfunc_l", "wrap_binaryfunc_r"]
    "x.__op__(y) calls the slot with (x, y) and x.__rop__(y) with (y, x)."
    "typeobject.c:9304-9326"
    ``WrapBinarySwaps ``wrapBinarySwaps_proven,
  p "typeobj-wrap-arity" ty []
    "A zero-argument wrapper called with arguments raises the exact TypeError."
    "typeobject.c:9229-9231"
    ``WrapperArityChecked ``wrapperArityChecked_proven,
  p "typeobj-wrap-keywords" "Objects/descrobject.c" []
    "Wrappers other than __call__ and __init__ refuse keywords."
    "descrobject.c:526-531"
    ``WrapperRejectsKeywords ``wrapperRejectsKeywords_proven,
  p "typeobj-attr-string-forms" ob []
    "The C string forms equal the object-name forms."
    "object.c:1174-1232"
    ``AttrStringForms ``attrStringForms_proven,
  p "typeobj-hasattr" ob []
    "hasattr is whether PyObject_GetOptionalAttr found the name."
    "object.c:1417-1437"
    ``HasAttrIffOptional ``hasAttrIffOptional_proven,
  p "typeobj-not" ob []
    "PyObject_Not negates PyObject_IsTrue."
    "object.c:2088"
    ``NotNegates ``notNegates_proven,
  p "typeobj-callable" ob []
    "Calling an object whose type has no tp_call raises the exact TypeError."
    "call.c:196"
    ``CallableCheck ``callableCheck_proven,
  p "typeobj-py-is" ob []
    "Py_Is is reflexive."
    "object.c:3275"
    ``IsReflexive ``isReflexive_proven,
  p "typeobj-seq-concat" ab []
    "A non-sequence without sq_concat cannot be concatenated."
    "abstract.c:1728-1734"
    ``SequenceConcatFallback ``sequenceConcatFallback_proven,
  p "typeobj-seq-repeat" ab []
    "A non-sequence without sq_repeat cannot be repeated."
    "abstract.c:1754-1765"
    ``SequenceRepeatFallback ``sequenceRepeatFallback_proven,
  p "typeobj-seq-iconcat" ab []
    "sq_inplace_concat takes precedence."
    "abstract.c:1776"
    ``SequenceInPlaceConcatOrder ``sequenceInPlaceConcatOrder_proven,
  p "typeobj-mapping-optional" ab []
    "KeyError from __getitem__ reads as absent."
    "abstract.c:213-222"
    ``MappingOptionalItem ``mappingOptionalItem_proven,
  p "typeobj-call-object" ca []
    "NULL args call with no arguments; a tuple is unpacked."
    "call.c:460"
    ``CallObjectArgs ``callObjectArgs_proven,
  p "typeobj-call-family" ca []
    "The call helpers reduce to PyObject_Call."
    "call.c:102, :386, :478"
    ``CallFamily ``callFamily_proven,
  p "typeobj-vectorcall-nargs" ca ["PyVectorcall_NARGS"]
    "PyVectorcall_NARGS clears PY_VECTORCALL_ARGUMENTS_OFFSET and keeps the count."
    "call.c:1127"
    ``VectorcallNargs ``vectorcallNargs_proven,
  p "typeobj-best-base" ty ["best_base"]
    "Under the subtype order, best_base returns one of the bases, whose solid base is a subclass of every base's solid base."
    "typeobject.c:3610-3611"
    ``BestBaseMostDerived ``bestBaseMostDerived_proven,
  p "typeobj-best-base-final" ty ["best_base"]
    "A base without Py_TPFLAGS_BASETYPE is refused."
    "typeobject.c:3638"
    ``BestBaseRefusesFinal ``bestBaseRefusesFinal_proven,
  p "typeobj-no-slots-dict-weak" ty []
    "Without __slots__ a class adds a dict and a weakref unless its base provides them."
    "docs: __slots__"
    ``NoSlotsAddsDictWeak ``noSlotsAddsDictWeak_proven,
  p "typeobj-slots-string" ty []
    "A string __slots__ is one name."
    "docs: __slots__"
    ``SlotsStringIsOneName ``slotsStringIsOneName_proven,
  p "typeobj-slots-dict-twice" ty []
    "__dict__ twice in __slots__ raises the exact TypeError."
    "typeobject.c:3990"
    ``SlotDictTwiceRejected ``slotDictTwiceRejected_proven,
  p "typeobj-wrap-new-function" ty ["type_new_staticmethod", "type_new_classmethod"]
    "Only plain functions are wrapped."
    "typeobject.c:4354, :4381"
    ``WrapInDictOnlyFunctions ``wrapInDictOnlyFunctions_proven,
  p "typeobj-ready-new" ty []
    "An existing tp_new is kept."
    "typeobject.c:8847-8863"
    ``TypeReadyNewInherited ``typeReadyNewInherited_proven,
  p "typeobj-update-slot-cleared" ty ["update_one_slot", "fixup_slot_dispatchers", "update_slots_callback", "slotptr"]
    "If no special method of a slot exists in the MRO, the slot becomes NULL (except tp_iternext)."
    "typeobject.c:11274-11278"
    ``UpdateSlotCleared ``updateSlotCleared_proven,
  p "typeobj-update-hash-none" ty ["update_one_slot"]
    "__hash__ = None anywhere first in the MRO makes tp_hash PyObject_HashNotImplemented."
    "typeobject.c:11392-11397"
    ``UpdateHashNone ``updateHashNone_proven,
  p "typeobj-subtype-mro" ty []
    "For a finished class, subtyping is membership in the MRO."
    "typeobject.c:2807-2819"
    ``SubtypeIsMroMember ``subtypeIsMroMember_proven,
  p "typeobj-set-class-checks" ty ["object_set_class"]
    "Deleting __class__ and assigning a non-class raise the exact TypeErrors."
    "typeobject.c:7228-7238"
    ``SetClassChecks ``setClassChecks_proven,
  p "typeobj-set-class-immutable" ty ["object_set_class_world_stopped"]
    "__class__ assignment to or from an immutable type is refused."
    "typeobject.c:7178-7186"
    ``SetClassImmutable ``setClassImmutable_proven,
  p "typeobj-object-format" ty ["object___format___impl"]
    "A non-empty spec raises; the empty spec is str(self)."
    "typeobject.c:7880-7886"
    ``ObjectFormatSpec ``objectFormatSpec_proven,
  p "typeobj-type-init" ty []
    "type.__init__ takes one or three arguments."
    "typeobject.c:3895"
    ``TypeInitArity ``typeInitArity_proven,
  p "typeobj-type-two-args" ty []
    "type() with two arguments is refused."
    "typeobject.c:2359"
    ``TypeCallTwoArgs ``typeCallTwoArgs_proven,
  p "typeobj-new-wrapper" ty []
    "X.__new__ needs a type as first argument."
    "typeobject.c:9833-9846"
    ``NewWrapperChecks ``newWrapperChecks_proven,
  p "typeobj-descr-check" "Objects/descrobject.c" []
    "A descriptor of C refuses an object that is not a C."
    "descrobject.c:80-91"
    ``DescrCheckRefuses ``descrCheckRefuses_proven,
  p "typeobj-descr-from-class" "Objects/descrobject.c" []
    "From the class a descriptor is itself."
    "descrobject.c:141, :166, :187, :207"
    ``DescriptorFromClass ``descriptorFromClass_proven,
  p "typeobj-slot-member-unset" "Objects/descrobject.c" []
    "An unset __slots__ member raises AttributeError."
    "docs: __slots__"
    ``SlotMemberUnset ``slotMemberUnset_proven,
  p "typeobj-buffer-fill-strides" ab ["PyBuffer_FillContiguousStrides", "_IsCContiguous", "_IsFortranContiguous"]
    "Strides filled for order F are F-contiguous and those for C are C-contiguous, for every shape."
    "docs: PyBuffer_FillContiguousStrides, PyBuffer_IsContiguous"
    ``FillStridesContiguous ``fillStridesContiguous_proven,
  p "typeobj-buffer-is-contiguous" ab ["PyBuffer_IsContiguous"]
    "A view with suboffsets is not contiguous, nor is one asked about an unknown order."
    "abstract.c:521, :529"
    ``IsContiguousGuards ``isContiguousGuards_proven,
  p "typeobj-buffer-odometer-range" ab ["_Py_add_one_to_index_F", "_Py_add_one_to_index_C"]
    "The index odometer keeps every digit within the shape."
    "invariant of PyBuffer_FromContiguous and PyObject_CopyData"
    ``AddOneInRange ``addOneInRange_proven,
  p "typeobj-buffer-odometer-wrap" ab ["_Py_add_one_to_index_F"]
    "From all-maximal indices the odometer wraps to zero."
    "abstract.c:554-562"
    ``AddOneWraps ``addOneWraps_proven,
  { id := "typeobj-copydata-bounds", pyFile := ab, pyFns := ["PyObject_CopyData"]
    statement := "With dest.len >= src.len, every element copied by PyObject_CopyData lands inside dest."
    source := "invariant: no out-of-bounds write; docs: PyObject_CopyData", status := .refuted,
    prop := ``CopyDataInBounds, thm := some ``copyDataInBounds_refuted,
    bug := some "typeobj-copydata-shape-mismatch" },
  p "typeobj-repr-str-result" ob ["PyObject_Repr"]
    "repr() of an object whose __repr__ returns a non-str raises the exact TypeError."
    "object.c:788"
    ``ReprMustReturnStr ``reprMustReturnStr_proven,
  p "typeobj-str-result" ob ["PyObject_Str"]
    "str() of an object whose __str__ returns a non-str raises the exact TypeError."
    "object.c:831"
    ``StrMustReturnStr ``strMustReturnStr_proven,
  p "typeobj-str-exact" ob []
    "str(s) of an exact str returns s with no slot call."
    "object.c:806"
    ``StrExactShortcut ``strExactShortcut_proven,
  p "typeobj-hash-no-slot" ob []
    "A type with no tp_hash is unhashable."
    "object.c:1170"
    ``HashNoSlot ``hashNoSlot_proven,
  p "typeobj-long-hash" "Objects/longobject.c" ["long_hash"]
    "hash(i) is never -1 for an int."
    "object.c docs: hash values"
    ``LongHashNotMinusOne ``longHashNotMinusOne_proven,
  p "typeobj-attr-context" ob []
    "Exceptions other than AttributeError pass through unchanged."
    "object.c:1266"
    ``AttrContextOnlyAttributeError ``attrContextOnlyAttributeError_proven,
  p "typeobj-setattr-no-slot" ob []
    "A type with tp_getattro and no tp_setattro has read-only attributes."
    "object.c:1480"
    ``SetAttrNoSlot ``setAttrNoSlot_proven,
  p "typeobj-get-method" ob ["_PyObject_GetMethod", "_PyObject_GetMethodStackRef"]
    "LOAD_ATTR method form: a method descriptor stays unbound unless the instance dict shadows it."
    "object.c:1568-1577"
    ``GetMethodDescriptor ``getMethodDescriptor_proven,
  p "typeobj-setdict" ty []
    "__dict__ can only be set to a dict."
    "typeobject.c:3767"
    ``SetDictRequiresDict ``setDictRequiresDict_proven,
  p "typeobj-getdict" ty []
    "__dict__ on an object without one raises."
    "dictobject.c:7616"
    ``GetDictRequiresDictPtr ``getDictRequiresDictPtr_proven,
  p "typeobj-size-order" ab ["PyObject_Size", "PyMapping_Size"]
    "len() uses sq_length, then mp_length, then raises."
    "abstract.c:57-72"
    ``ObjectSizeOrder ``objectSizeOrder_proven,
  p "typeobj-size-protocols" ab []
    "PySequence_Size refuses a pure mapping and PyMapping_Size a pure sequence."
    "abstract.c:1695, :2281"
    ``SizeProtocolsDistinct ``sizeProtocolsDistinct_proven,
  p "typeobj-length-hint-default" ab ["PyObject_LengthHint"]
    "With no __len__ and no __length_hint__ the default is returned."
    "abstract.c:88-92"
    ``LengthHintDefault ``lengthHintDefault_proven,
  p "typeobj-length-hint-notimpl" ab ["PyObject_LengthHint"]
    "NotImplemented from __length_hint__ means the default."
    "abstract.c:130"
    ``LengthHintNotImplemented ``lengthHintNotImplemented_proven,
  p "typeobj-setitem-mapping" ab []
    "Item assignment and deletion prefer mp_ass_subscript."
    "abstract.c:233"
    ``SetItemMappingFirst ``setItemMappingFirst_proven,
  p "typeobj-seq-setitem-negative" ab ["PySequence_SetItem", "PySequence_DelItem"]
    "Negative indices get len(s) added before sq_ass_item."
    "abstract.c:1893-1901"
    ``SequenceSetItemNegative ``sequenceSetItemNegative_proven,
  p "typeobj-ternary-no-slots" ab []
    "pow with no slot anywhere names two types when the modulus is None."
    "abstract.c:1091-1098"
    ``TernaryNoSlots ``ternaryNoSlots_proven,
  p "typeobj-inplace-first" ab ["binary_iop1", "binary_iop", "PyNumber_InPlaceAdd"]
    "__iop__ goes first, and a non-NotImplemented result is final."
    "abstract.c:1203-1215"
    ``InPlaceFirst ``inPlaceFirst_proven,
  p "typeobj-inplace-pow" ab ["ternary_iop", "PyNumber_InPlacePower", "_PyNumber_InPlacePowerNoMod", "slot_nb_inplace_power"]
    "__ipow__ gets two arguments, whatever the third operand."
    "typeobject.c:10270-10274"
    ``InplacePowerTwoArgs ``inplacePowerTwoArgs_proven,
  p "typeobj-number-long" ab ["PyNumber_Long"]
    "An exact int is returned; a non-int __int__ result raises the exact TypeError."
    "abstract.c:1519, :1532"
    ``NumberLongChecks ``numberLongChecks_proven,
  p "typeobj-number-check" ab []
    "PyNumber_Check tests the three conversion slots."
    "abstract.c:903"
    ``NumberCheckSlots ``numberCheckSlots_proven,
  p "typeobj-iter-next-stop" ab ["PyIter_Next"]
    "StopIteration means exhausted; other exceptions propagate."
    "abstract.c:2880"
    ``IterNextStop ``iterNextStop_proven,
  p "typeobj-iter-check" ab []
    "A type with _PyObject_NextNotImplemented is not an iterator."
    "abstract.c:2853"
    ``IterCheckNotImplemented ``iterCheckNotImplemented_proven,
  p "typeobj-tuple-of-tuple" ab []
    "tuple(t) of an exact tuple does not iterate."
    "abstract.c:2005"
    ``TupleOfTuple ``tupleOfTuple_proven,
  p "typeobj-abstract-issubclass" ab ["abstract_issubclass", "abstract_get_bases"]
    "A class is a subclass of itself; a class without __bases__ of nothing else."
    "abstract.c:2536, :2546"
    ``AbstractIssubclass ``abstractIssubclass_proven,
  p "typeobj-isinstance-empty-tuple" ab ["object_recursive_isinstance"]
    "isinstance(x, ()) is False."
    "docs: isinstance"
    ``IsinstanceEmptyTuple ``isinstanceEmptyTuple_proven,
  p "typeobj-wrap-next" ty []
    "NULL from the slot with no exception raises StopIteration."
    "typeobject.c:9696"
    ``WrapNextStops ``wrapNextStops_proven,
  p "typeobj-wrap-descr-get" ty []
    "__get__(None, None) is refused."
    "typeobject.c:9714"
    ``WrapDescrGetNoneNone ``wrapDescrGetNoneNone_proven,
  p "typeobj-hackcheck" ty []
    "object.__setattr__ on an instance skips the type check."
    "typeobject.c:9580"
    ``HackcheckInstances ``hackcheckInstances_proven,
  p "typeobj-getindex" ty []
    "A non-negative index passes through getindex."
    "typeobject.c:9404"
    ``GetIndexNonNegative ``getIndexNonNegative_proven,
  p "typeobj-slot-call" ty []
    "slot_tp_call is __call__ on the type."
    "typeobject.c:10343"
    ``SlotCallDispatch ``slotCallDispatch_proven,
  p "typeobj-slot-repr" ty []
    "Without __repr__ on the type the default text is used."
    "typeobject.c:10296"
    ``SlotReprDefault ``slotReprDefault_proven,
  p "typeobj-supercheck" ty ["supercheck"]
    "A subclass of type gives itself; an instance gives its type."
    "typeobject.c:11959-11965"
    ``SupercheckCases ``supercheckCases_proven,
  p "typeobj-super-get-bound" ty []
    "__get__ of a bound super object returns it."
    "typeobject.c:12038"
    ``SuperGetBound ``superGetBound_proven,
  p "typeobj-compat-reflexive" ty []
    "Assigning __class__ to the same class passes the layout test."
    "invariant"
    ``CompatibleReflexive ``compatibleReflexive_proven,
  p "typeobj-special-attr-immutable" ty []
    "Special attributes of immutable types cannot be set."
    "typeobject.c:1421"
    ``TypeDocSet ``typeDocSet_proven,
  p "typeobj-wrapper-arity0" ty []
    "Zero-argument wrappers called with arguments raise the exact TypeError."
    "typeobject.c:9229"
    ``WrapperArity0 ``wrapperArity0_proven,
  p "typeobj-wrapper-arity1" ty []
    "One-argument wrappers called with another count raise the exact TypeError."
    "typeobject.c:9229"
    ``WrapperArity1 ``wrapperArity1_proven,
  p "typeobj-wrapper-pow" ty []
    "__pow__ wrappers accept one or two arguments."
    "typeobject.c:9250"
    ``WrapperArityPow ``wrapperArityPow_proven,
  p "typeobj-wrap-init" ty []
    "__init__ through the wrapper returns None."
    "typeobject.c:9817"
    ``WrapInitReturnsNone ``wrapInitReturnsNone_proven,
  p "typeobj-wrap-len-hash" ty []
    "__len__ and __hash__ wrappers return the slot result as an int."
    "typeobject.c:9275, :9637"
    ``WrapLenHash ``wrapLenHash_proven,
  p "typeobj-wrap-richcmp" ty []
    "__eq__ and friends apply tp_richcompare with their op."
    "typeobject.c:9661-9670"
    ``WrapRichcmp ``wrapRichcmp_proven,
  p "typeobj-wrapperdescr-self" "Objects/descrobject.c" []
    "An unbound slot wrapper refuses a first argument of another class."
    "descrobject.c:554"
    ``WrapperDescrSelfChecked ``wrapperDescrSelfChecked_proven,
  p "typeobj-type-new-args" ty ["type_new"]
    "type.__new__ argument count and name type are checked with the exact messages."
    "typeobject.c:4774"
    ``TypeNewArgs ``typeNewArgs_proven,
  p "typeobj-type-new-empty-bases" ty []
    "Empty bases mean (object,)."
    "typeobject.c:4699-4707"
    ``TypeNewEmptyBases ``typeNewEmptyBases_proven,
  p "typeobj-type-new-mro-entries" ty []
    "type() refuses a base with __mro_entries__."
    "typeobject.c:4715-4724"
    ``TypeNewMroEntries ``typeNewMroEntries_proven,
  p "typeobj-classcell" ty ["type_new_set_classcell", "type_new_set_classdictcell"]
    "__classcell__ must be a cell."
    "typeobject.c:4485"
    ``ClassCellChecked ``classCellChecked_proven,
  p "typeobj-type-getters" ty []
    "__bases__ and __mro__ read tp_bases and tp_mro."
    "typeobject.c:1686-1705"
    ``TypeGetters ``typeGetters_proven,
  p "typeobj-type-name-getters" ty []
    "__name__ and __qualname__ of a heap type are ht_name and ht_qualname."
    "typeobject.c:1460, :1473"
    ``TypeNameGetters ``typeNameGetters_proven,
  p "typeobj-object-get-class" ty []
    "obj.__class__ through the descriptor is type(obj)."
    "typeobject.c:7017"
    ``ObjectGetClass ``objectGetClass_proven,
  p "typeobj-type-repr" ty []
    "repr of a heap class is <class 'module.qualname'>."
    "typeobject.c:2318"
    ``TypeReprHeap ``typeReprHeap_proven,
  p "typeobj-object-str" ty []
    "object.__str__ uses tp_repr."
    "typeobject.c:6956"
    ``ObjectStrUsesRepr ``objectStrUsesRepr_proven,
  { id := "typeobj-super-bind-null-type", pyFile := ty, pyFns := ["super_descr_get"]
    statement := "Binding the object super.__new__(super) allocates never reaches supercheck with a NULL type."
    source := "invariant: pure Python does not crash the interpreter", status := .refuted,
    prop := ``SuperBindHasType, thm := some ``superBindHasType_refuted,
    bug := some "typeobj-super-uninitialized-get" },
  p "typeobj-list-extend-loop" "Objects/listobject.c" ["list_extend_iter_lock_held"]
    "For every __next__, an item is in the list before __next__ runs again, and a raising __next__ ends the loop in the world it raised in."
    "listobject.c:1262-1283"
    ``ListExtendLoopStep ``listExtendLoopStep_proven,
  p "typeobj-list-extend-self" "Objects/listobject.c" ["_list_extend", "list_inplace_concat"]
    "Extending a list with itself doubles it and runs no Python code."
    "listobject.c:1407"
    ``ListExtendSelf ``listExtendSelf_proven,
  p "typeobj-list-reserve" "Objects/listobject.c" ["list_extend_iter_lock_held"]
    "A length hint that overflows m + n is ignored; otherwise an unservable total is a MemoryError."
    "listobject.c:1241-1259"
    ``ListReserveRule ``listReserveRule_proven,
  p "typeobj-list-extend-iter-first" "Objects/listobject.c" []
    "A failing __iter__ ends the extension before the length hint runs."
    "listobject.c:1227-1234"
    ``ListExtendIterFirst ``listExtendIterFirst_proven,
  p "typeobj-list-init-clears" "Objects/listobject.c" []
    "list.__init__ empties the list before it extends it."
    "listobject.c:3491-3497"
    ``ListInitClearsFirst ``listInitClearsFirst_proven,
  p "typeobj-dict-lookup-other-hash" "Objects/dictobject.c" ["compare_generic", "dictkeys_generic_lookup"]
    "A key that is no entry and shares no entry's hash is reported absent and no comparison runs, for every __eq__."
    "dictobject.c:1107-1126"
    ``DictProbeSkipsOtherHashes ``dictProbeSkipsOtherHashes_proven,
  p "typeobj-dict-lookup-identity" "Objects/dictobject.c" ["compare_generic", "dictkeys_generic_lookup"]
    "A key object already in the dict is found without running Python code when no earlier entry shares its hash."
    "dictobject.c:1107"
    ``DictProbeFindsIdentical ``dictProbeFindsIdentical_proven,
  p "typeobj-reduce-newargs-validated" ty ["_PyObject_GetNewArguments"]
    "Whatever __getnewargs_ex__ returned, only a pair of a tuple and a dict is accepted, and nothing else happens."
    "typeobject.c:7538-7574"
    ``NewargsExValidated ``newargsExValidated_proven,
  p "typeobj-slotnames-typed" ty ["_PyType_GetSlotNames"]
    "For every class and Rt, a value _PyType_GetSlotNames returns is None or a list."
    "invariant: typeobject.c:7381"
    ``SlotNamesWellTyped ``slotNamesWellTyped_proven,
  p "typeobj-getstate-guard" ty ["object_getstate_default"]
    "If the slot loop of object_getstate_default completes, __slotnames__ has its original size, for every getter."
    "typeobject.c:7440"
    ``GetstateSlotsGuard ``getstateSlotsGuard_proven,
  p "typeobj-best-base-decides" ty ["best_base"]
    "One acceptable base wins, an unacceptable base is the exact TypeError, and two unrelated solid bases are the layout conflict."
    "typeobject.c:3624-3662"
    ``BestBaseDecides ``bestBaseDecides_proven,
  p "typeobj-ready-hash-accepts" ty ["type_ready_set_hash"]
    "type_ready_set_hash leaves a type with tp_hash alone, and always succeeds."
    "typeobject.c:8781"
    ``TypeReadySetHashAccepts ``typeReadySetHashAccepts_proven,
  p "typeobj-exc-init-accepts" "Objects/exceptions.c"
    ["StopIteration_init", "SystemExit_init", "NameError_init", "AttributeError_init", "ImportError_init"]
    "These __init__s succeed on any positional arguments and the keywords they define."
    "exceptions.c:754-769"
    ``ExcInitAccepts ``excInitAccepts_proven,
  p "typeobj-exc-chain-accepts" "Objects/exceptions.c"
    ["BaseException___cause___set_impl", "BaseException___context___set_impl"]
    "__cause__ and __context__ accept None or an exception, and any other value is the exact TypeError."
    "exceptions.c:445-478"
    ``ExcChainSetAccepts ``excChainSetAccepts_proven,
  p "typeobj-getnewargs-order" ty ["_PyObject_GetNewArguments"]
    "__getnewargs_ex__ is checked first, __getnewargs__ only if it is absent and must give a tuple, and two absences give no arguments."
    "typeobject.c:7520-7609"
    ``GetNewArgumentsOrder ``getNewArgumentsOrder_proven,
  p "typeobj-super-null-branch" ty ["super_descr_get"]
    "The state superBindsNullType describes runs super_descr_get into the branch where C dereferences NULL."
    "typeobject.c:12049"
    ``SuperBindNullIsTheBranch ``superBindNullIsTheBranch_proven,
  p "typeobj-super-skips" ty ["_super_lookup_descr", "do_super_lookup", "super_getattro"]
    "super looks strictly after __thisclass__ in the MRO of the object's type."
    "docs: super"
    ``SuperSkipsThisClass ``superSkipsThisClass_proven ] ++ excEntries

end PyLean.TypeObj
