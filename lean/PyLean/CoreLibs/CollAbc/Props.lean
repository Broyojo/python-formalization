import PyLean.CoreLibs.CollAbc.Builtins

/-!
Properties of the `_collections_abc` mixins, and proofs.
-/

namespace PyLean.CoreLibs.CollAbc

open PyLean

/-! ### `_check_methods` and the hooks -/

/-- The binding `C.__dict__`-lookup along the MRO finds first. -/
def firstBinding (mro : List ClassDict) (m : String) : Option Bool :=
  mro.findSome? (fun B => B.lookup m)

theorem checkOne_val_iff (m : String) : ∀ mro : List ClassDict,
    checkOne m mro = .val () ↔ firstBinding mro m = some false
  | [] => by simp [checkOne, firstBinding]
  | B :: rest => by
    have ih := checkOne_val_iff m rest
    simp only [firstBinding] at ih ⊢
    simp only [checkOne, List.findSome?_cons]
    cases h : B.lookup m with
    | none => simpa using ih
    | some b => cases b <;> simp

theorem checkMethods_true_iff (mro : List ClassDict) : ∀ ms : List String,
    checkMethods mro ms = .val true ↔ ∀ m ∈ ms, firstBinding mro m = some false
  | [] => by simp [checkMethods]
  | m :: ms => by
    have ih := checkMethods_true_iff mro ms
    have h1 := checkOne_val_iff m mro
    simp only [checkMethods, List.mem_cons, forall_eq_or_imp]
    cases h : checkOne m mro with
    | notImplemented =>
      have : ¬ firstBinding mro m = some false := by
        rw [← h1, h]; simp
      simp [this]
    | val u =>
      have : firstBinding mro m = some false := h1.mp (by rw [h])
      simpa [this] using ih

theorem checkMethods_ne_false (mro : List ClassDict) : ∀ ms : List String,
    checkMethods mro ms ≠ .val false
  | [] => by simp [checkMethods]
  | m :: ms => by
    simp only [checkMethods]
    cases checkOne m mro with
    | notImplemented => simp
    | val u => exact checkMethods_ne_false mro ms

/-- `_check_methods(C, *methods)` answers `True` exactly when, for every method, the first
definition along the MRO exists and is not `None`, and otherwise `NotImplemented`; it never
answers `False`. Invariant from the source and from the ABC docs ("set a method to None to
opt out"). -/
def CheckMethodsSpec : Prop :=
  ∀ (mro : List ClassDict) (ms : List String),
    (checkMethods mro ms = .val true ↔ ∀ m ∈ ms, firstBinding mro m = some false) ∧
    checkMethods mro ms ≠ .val false

theorem checkMethodsSpec_proven : CheckMethodsSpec :=
  fun mro ms => ⟨checkMethods_true_iff mro ms, checkMethods_ne_false mro ms⟩

/-- `checkMethods` answers `True` or `NotImplemented`, nothing else. -/
theorem checkMethods_cases (mro : List ClassDict) : ∀ ms : List String,
    checkMethods mro ms = .val true ∨ checkMethods mro ms = .notImplemented
  | [] => Or.inl rfl
  | m :: ms => by
    simp only [checkMethods]
    cases checkOne m mro with
    | notImplemented => exact Or.inr rfl
    | val u => exact checkMethods_cases mro ms

/-- Each ABC's hook with the methods its source passes to `_check_methods`, Lib/_collections_abc.py:131, 146, 189,
207, 228, 275-276, 295, 316, 348, 395-396, 414, 429, 442, 457, 540. -/
def hookSpec : List (String × List String) :=
  [("Hashable", ["__hash__"]), ("Awaitable", ["__await__"]),
   ("Coroutine", ["__await__", "send", "throw", "close"]), ("AsyncIterable", ["__aiter__"]),
   ("AsyncIterator", ["__anext__", "__aiter__"]),
   ("AsyncGenerator", ["__aiter__", "__anext__", "asend", "athrow", "aclose"]),
   ("Iterable", ["__iter__"]), ("Iterator", ["__iter__", "__next__"]),
   ("Reversible", ["__reversed__", "__iter__"]),
   ("Generator", ["__iter__", "__next__", "send", "throw", "close"]),
   ("Sized", ["__len__"]), ("Container", ["__contains__"]),
   ("Collection", ["__len__", "__iter__", "__contains__"]), ("Buffer", ["__buffer__"]),
   ("Callable", ["__call__"])]

/-- The fifteen `__subclasshook__`s. Asked about its own ABC, a hook answers `True` exactly when every method of its
list has a first definition along `C`'s MRO that is not `None`, and `NotImplemented` otherwise, never `False`; asked by
any other class (a subclass of the ABC, which inherits the hook), it answers `NotImplemented`. Quantified over every
class, given as its MRO of dictionaries; the lists are the source's, so a hook that always answers `NotImplemented`, or
tests one method too many or too few, fails. Invariant from the source and the ABC docs. -/
def HookExact : Prop :=
  (∀ p ∈ hookSpec, ∀ mro : List ClassDict,
    (subclasshook p.1 p.1 mro = .val true ↔ ∀ m ∈ p.2, firstBinding mro m = some false) ∧
    (subclasshook p.1 p.1 mro = .notImplemented ↔ ¬ ∀ m ∈ p.2, firstBinding mro m = some false) ∧
    subclasshook p.1 p.1 mro ≠ .val false) ∧
  (∀ (x cls : String) (mro : List ClassDict), cls ≠ x → subclasshook x cls mro = .notImplemented)

theorem hookExact_proven : HookExact := by
  refine ⟨?_, ?_⟩
  · intro p hp mro
    have hm : hookMethods p.1 = p.2 := by
      simp only [hookSpec, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> rfl
    simp only [subclasshook, ite_true, hm]
    refine ⟨checkMethods_true_iff mro p.2, ?_, checkMethods_ne_false mro p.2⟩
    rw [← checkMethods_true_iff mro p.2]
    rcases checkMethods_cases mro p.2 with h | h <;> simp [h]
  · intro x cls mro h
    simp [subclasshook, h]

/-! ### Abstract bodies -/

def stubGetitem {K α : Type} (e : PyExc) : K → Py α := fun _ => .error e

/-- The `Sequence` an object has when it relies on the abstract `__getitem__` and `__len__`. -/
def stubSeq (α : Type) : Seq α := ⟨stubGetitem (.indexError ""), .ok 0⟩

/-- The `Mapping` an object has when it relies on the abstract primitives. -/
def stubMap (K V : Type) : MapV K V := { getitem := stubGetitem (.keyError ""), iter := .ok [], len := .ok 0 }

/-- The abstract bodies, reachable by `super()`, describe the empty collection: `len` 0, nothing
contained, empty iteration; the abstract `__getitem__`s raise the very exceptions the mixins catch,
so the mixins built on them see an empty `Sequence` and an empty `Mapping`. -/
def StubsAreEmpty : Prop :=
  stubBody "Sized.__len__" = some (.returnsInt 0) ∧
  stubBody "Hashable.__hash__" = some (.returnsInt 0) ∧
  stubBody "Container.__contains__" = some (.returnsBool false) ∧
  stubBody "Callable.__call__" = some (.returnsBool false) ∧
  stubBody "Iterable.__iter__" = some (.yieldsNones 0) ∧
  stubBody "Reversible.__reversed__" = some (.yieldsNones 0) ∧
  stubBody "Awaitable.__await__" = some (.yieldsNones 1) ∧
  stubBody "Iterator.__next__" = some (.raises "StopIteration") ∧
  stubBody "Generator.send" = some (.raises "StopIteration") ∧
  stubBody "Coroutine.send" = some (.raises "StopIteration") ∧
  stubBody "AsyncIterator.__anext__" = some (.raises "StopAsyncIteration") ∧
  stubBody "AsyncGenerator.asend" = some (.raises "StopAsyncIteration") ∧
  stubBody "AsyncIterable.__aiter__" = some (.raises "TypeError") ∧
  stubBody "Buffer.__buffer__" = some (.raises "NotImplementedError") ∧
  stubBody "MutableSet.add" = some (.raises "NotImplementedError") ∧
  stubBody "MutableSet.discard" = some (.raises "NotImplementedError") ∧
  stubBody "Mapping.__getitem__" = some (.raises "KeyError") ∧
  stubBody "MutableMapping.__setitem__" = some (.raises "KeyError") ∧
  stubBody "MutableMapping.__delitem__" = some (.raises "KeyError") ∧
  stubBody "Sequence.__getitem__" = some (.raises "IndexError") ∧
  stubBody "MutableSequence.__setitem__" = some (.raises "IndexError") ∧
  stubBody "MutableSequence.__delitem__" = some (.raises "IndexError") ∧
  stubBody "MutableSequence.insert" = some (.raises "IndexError") ∧
  (∀ (α : Type) (fuel : Nat), (stubSeq α).iterFrom (fuel + 1) 0 = .ok []) ∧
  (∀ (α : Type) (E : EqOps α) (v : α) (fuel : Nat),
    (stubSeq α).containsFrom E v (fuel + 1) 0 = .ok false) ∧
  (∀ (K V : Type) (k : K) (d : V), (stubMap K V).get k d = .ok d) ∧
  (∀ (K V : Type) (k : K), (stubMap K V).contains k = .ok false)

theorem stubsAreEmpty_proven : StubsAreEmpty := by
  refine ⟨by simp [stubBody], by simp [stubBody], by simp [stubBody], by simp [stubBody],
    by simp [stubBody], by simp [stubBody], by simp [stubBody], by simp [stubBody],
    by simp [stubBody], by simp [stubBody], by simp [stubBody], by simp [stubBody],
    by simp [stubBody], by simp [stubBody], by simp [stubBody], by simp [stubBody],
    by simp [stubBody], by simp [stubBody], by simp [stubBody], by simp [stubBody],
    by simp [stubBody], by simp [stubBody], by simp [stubBody], ?_, ?_, ?_, ?_⟩
  · intro α fuel; simp [Seq.iterFrom, stubSeq, stubGetitem, isIndexError]
  · intro α E v fuel; simp [Seq.containsFrom, stubSeq, stubGetitem, isIndexError]
  · intro K V k d; simp [MapV.get, stubMap, stubGetitem, isKeyError]
  · intro K V k; simp [MapV.contains, stubMap, stubGetitem, isKeyError]

/-! ### `throw`, `close` -/

/-- An argument as the `raise` statement's documentation has it: an exception class whose call with no arguments makes
an instance of it, or an exception instance with no traceback attached. -/
def TObj.plain : TObj → Prop
  | .excClass n (.obj (.excInst m false)) => m = n
  | .excInst _ false => True
  | _ => False

/-- The class name of an object. -/
def TObj.cname : TObj → String
  | .excClass n _ => n
  | .excInst n _ => n
  | .other t _ _ => t

def TObj.isCls : TObj → Bool
  | .excClass .. => true
  | _ => false

theorem plain_cases {t : TObj} (h : t.plain) :
    (∃ n, t = .excClass n (.obj (.excInst n false))) ∨ (∃ n, t = .excInst n false) := by
  match t, h with
  | .excClass n (.obj (.excInst m false)), h => exact Or.inl ⟨n, by simp only [TObj.plain] at h; rw [h]⟩
  | .excInst n false, _ => exact Or.inr ⟨n, rfl⟩

/-- `throw(typ, val, tb)` with documented arguments (`TObj.plain`): it raises the exception it was asked to, `val`'s
when given and else `typ`'s, exactly when `tb` is `None`, or when `tb` is a traceback and the object it is attached to
can take it (`typ` a class to call, `val` an instance); the traceback is then attached exactly when it was given. In
every other case it raises something else. Docstring of `Generator.throw` with the `raise` statement's contract. -/
def ThrowRaisesGiven : Prop :=
  ∀ (typ : TObj) (val : Option TObj) (tb : TbArg) (r : Raised), typ.plain → (∀ v, val = some v → v.plain) →
    (throwBody typ val tb = .ok r ↔
      (r = ⟨(val.getD typ).cname, tb = .traceback⟩ ∧
        (tb = .absent ∨ (tb = .traceback ∧ (match val with | none => typ.isCls | some v => !v.isCls) = true))))

theorem throwRaisesGiven_proven : ThrowRaisesGiven := by
  intro typ val tb r ht hv
  rcases plain_cases ht with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · cases val with
    | none =>
      cases tb <;> simp [throwBody, raiseObj, callNoArgs, withTraceback, TMade.toPy, TObj.cname, TObj.isCls,
        bind, Except.bind, eq_comm]
    | some v =>
      rcases plain_cases (hv v rfl) with ⟨m, rfl⟩ | ⟨m, rfl⟩ <;>
        cases tb <;> simp [throwBody, raiseObj, callNoArgs, withTraceback, TMade.toPy, TObj.cname, TObj.isCls,
          bind, Except.bind, eq_comm]
  · cases val with
    | none =>
      cases tb <;> simp [throwBody, raiseObj, callNoArgs, withTraceback, TMade.toPy, TObj.cname, TObj.isCls,
        bind, Except.bind, eq_comm]
    | some v =>
      rcases plain_cases (hv v rfl) with ⟨m, rfl⟩ | ⟨m, rfl⟩ <;>
        cases tb <;> simp [throwBody, raiseObj, callNoArgs, withTraceback, TMade.toPy, TObj.cname, TObj.isCls,
          bind, Except.bind, eq_comm]

/-- Forget the value `close()` returns. -/
def dropVal {α : Type} : Py α → Py Unit
  | .ok _ => .ok ()
  | .error e => .error e

/-- `Generator.close` and `Coroutine.close` have the same outcome and the same effect on the generator as the builtin
`generator.close()` and `coroutine.close()`, messages included, up to the returned value: they raise the same exception
and leave the generator in the same state. Twin property, over every generator given as a state machine. -/
def CloseMatchesBuiltinUpToValue : Prop :=
  ∀ (σ V : Type) (G : Gen σ V) (s : σ),
    ((G.close genCloseMsg s).2 = (builtinClose G builtinGenCloseMsg s).2 ∧
      (G.close genCloseMsg s).1 = dropVal (builtinClose G builtinGenCloseMsg s).1) ∧
    ((G.close coroCloseMsg s).2 = (builtinClose G builtinCoroCloseMsg s).2 ∧
      (G.close coroCloseMsg s).1 = dropVal (builtinClose G builtinCoroCloseMsg s).1)

theorem closeMatchesBuiltinUpToValue_proven : CloseMatchesBuiltinUpToValue := by
  intro σ V G s
  have h1 : genCloseMsg = builtinGenCloseMsg := rfl
  have h2 : coroCloseMsg = builtinCoroCloseMsg := rfl
  rw [← h1, ← h2]
  simp only [Gen.close, builtinClose]
  cases G.throwExit s with
  | mk st s' =>
    cases st with
    | yielded v => simp [dropVal]
    | stopped v => simp [dropVal]
    | raised e =>
      by_cases h : isGeneratorExit e <;> simp [dropVal, h]

/-- The mixin `close()` result as an optional value: always `None` on success. -/
def mixinCloseValue {σ V : Type} (G : Gen σ V) (s : σ) : Py (Option V) :=
  match (G.close genCloseMsg s).1 with
  | .ok () => .ok none
  | .error e => .error e

/-- The `Generator.close` mixin returns what the builtin `generator.close()` returns. False: since
3.13 the builtin returns the value of a generator that catches `GeneratorExit` and returns, and
the mixin discards it. -/
def CloseReturnsSameValue : Prop :=
  ∀ (G : Gen Unit Int) (s : Unit), mixinCloseValue G s = (builtinClose G builtinGenCloseMsg s).1

theorem closeReturnsSameValue_refuted : ¬CloseReturnsSameValue := by
  intro h
  have := h ⟨fun s _ => (.stopped 0, s), fun s => (.stopped 7, s)⟩ ()
  simp [mixinCloseValue, Gen.close, builtinClose] at this

/-- `AsyncGenerator.aclose` awaited is the builtin `async_generator.aclose()` awaited: the same outcome and the same
state. False: when the generator yields instead of closing, the mixin's `RuntimeError` says "asynchronous generator
ignored GeneratorExit" (Lib/_collections_abc.py:270) and the builtin's "async generator ignored GeneratorExit"
(Objects/genobject.c:64-65, 2398-2403). -/
def AcloseMatchesBuiltin : Prop :=
  ∀ (σ V : Type) (G : Gen σ V) (s : σ), G.close asyncCloseMsg s = builtinAclose G s

theorem acloseMatchesBuiltin_refuted : ¬AcloseMatchesBuiltin := by
  intro h
  have := h Unit Unit ⟨fun s _ => (.yielded (), s), fun s => (.yielded (), s)⟩ ()
  simp [Gen.close, builtinAclose, asyncCloseMsg, builtinAsyncCloseMsg] at this

/-- `AsyncGenerator.aclose` and the builtin `aclose()` agree up to the message: the same state afterwards, and the same
outcome, except that a generator that yields while closing gets each side's own `RuntimeError` message. Twin
property, over every generator given as a state machine that does not await while closing. -/
def AcloseMatchesBuiltinUpToMessage : Prop :=
  ∀ (σ V : Type) (G : Gen σ V) (s : σ),
    (G.close asyncCloseMsg s).2 = (builtinAclose G s).2 ∧
    ((G.close asyncCloseMsg s).1 = (builtinAclose G s).1 ∨
      ((G.close asyncCloseMsg s).1 = .error (.named "RuntimeError" "asynchronous generator ignored GeneratorExit") ∧
        (builtinAclose G s).1 = .error (.named "RuntimeError" "async generator ignored GeneratorExit")))

theorem acloseMatchesBuiltinUpToMessage_proven : AcloseMatchesBuiltinUpToMessage := by
  intro σ V G s
  simp only [Gen.close, builtinAclose]
  cases G.throwExit s with
  | mk st s' =>
    cases st with
    | yielded v => simp [asyncCloseMsg, builtinAsyncCloseMsg]
    | stopped v => simp
    | raised e => simp

/-- `Generator.__next__` and `AsyncGenerator.__anext__` are `send(None)`: a generator advanced by
`next` and by `send(None)` takes the same step. Docs of `generator.__next__`. -/
def NextIsSendNone : Prop :=
  ∀ (σ V : Type) (G : Gen σ V) (none : V) (s : σ), G.next none s = G.send s none

theorem nextIsSendNone_proven : NextIsSendNone := fun _ _ _ _ _ => rfl

/-! ### `Callable[...]` -/

/-- `_is_param_expr` is `True` for `...`, for any `list` (a subclass too), and for an object whose type is
`typing.ParamSpec` or `typing._ConcatenateGenericAlias` by module and name, and `False` for a tuple and for every other
type, including one of those names from another module. The source's test, Lib/_collections_abc.py:520-526. -/
def IsParamExprSpec : Prop :=
  isParamExpr .ellipsis = true ∧
  (∀ items, isParamExpr (.list items) = true) ∧
  (∀ items, isParamExpr (.tuple items) = false) ∧
  (∀ r, isParamExpr (.obj "typing" "ParamSpec" r) = true) ∧
  (∀ r, isParamExpr (.obj "typing" "_ConcatenateGenericAlias" r) = true) ∧
  (∀ m n r, isParamExpr (.obj m n r) = true → m = "typing" ∧ (n = "ParamSpec" ∨ n = "_ConcatenateGenericAlias"))

theorem isParamExprSpec_proven : IsParamExprSpec := by
  refine ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_⟩
  intro m n r h
  simp only [isParamExpr, Bool.and_eq_true, beq_iff_eq, List.any_cons, List.any_nil, Bool.or_false,
    Bool.or_eq_true] at h
  exact ⟨h.1, h.2.elim (fun e => Or.inl e) (fun e => Or.inr e)⟩

/-- `_CallableGenericAlias.__new__`, every path: anything but a tuple of two is the `TypeError` "Callable must be used
as Callable[[arg, ...], result]."; a list or tuple of arguments is flattened before the result; `...`, a `ParamSpec`
or a `Concatenate` is kept as the first argument; anything else is the `TypeError` "Expected a list of types, ...".
Lib/_collections_abc.py:473-483. -/
def CallableNewPaths : Prop :=
  callableNew none = .error (.typeError "Callable must be used as Callable[[arg, ...], result].") ∧
  (∀ items r, callableNew (some (.list items, r)) = .ok (items ++ [r]) ∧
    callableNew (some (.tuple items, r)) = .ok (items ++ [r])) ∧
  (∀ r, callableNew (some (.ellipsis, r)) = .ok [.ellipsis, r]) ∧
  (∀ n p r, (n = "ParamSpec" ∨ n = "_ConcatenateGenericAlias") →
    callableNew (some (.obj "typing" n p, r)) = .ok [.obj "typing" n p, r]) ∧
  (∀ m n p r, isParamExpr (.obj m n p) = false → (callableNew (some (.obj m n p, r))).raises "TypeError")

theorem callableNewPaths_proven : CallableNewPaths := by
  refine ⟨rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, ?_, ?_⟩
  · intro n p r h
    rcases h with rfl | rfl <;> rfl
  · intro m n p r h
    refine ⟨.typeError "~Expected a list of types, an ellipsis, ParamSpec, or Concatenate. Got ", ?_, rfl⟩
    simp [callableNew, h]

/-- The first argument of `__args__` is a list nested in the argument list, `Callable[[[...]], r]`. -/
def nestedListFirst (args : List CArg) : Prop := ∃ items r, args = [.list items, r]

/-- Pickling round-trip: `__reduce__` gives arguments from which `_CallableGenericAlias(Callable, args)` rebuilds the
same `__args__`, for every alias that `Callable[t_args, r]` makes. False: for `Callable[[[int]], str]` the `__args__`
are `([int], str)`, `_is_param_expr([int])` holds, so `__reduce__` returns them as they are, and rebuilding flattens
them to `(int, str)`; `copy.copy` of the alias is not equal to it. -/
def CallableReduceRoundTrip : Prop :=
  ∀ (t r : CArg) (args : List CArg), callableNew (some (t, r)) = .ok args →
    (callableReduce args >>= fun a => callableNew (asPair a)) = .ok args

theorem callableReduceRoundTrip_refuted : ¬CallableReduceRoundTrip := by
  intro h
  have := h (.list [.list [.obj "builtins" "type" "int"]]) (.obj "builtins" "type" "str")
    [.list [.obj "builtins" "type" "int"], .obj "builtins" "type" "str"] rfl
  simp [callableReduce, callableNew, asPair, isParamExpr, bind, Except.bind] at this

/-- The round-trip of `__reduce__` holds for every alias whose first argument is not a list nested in the argument
list (a list is not a type, which the documentation requires there), including `...`, `ParamSpec` and `Concatenate`
aliases, and `Callable[[], r]`. -/
def CallableReduceRoundTripNarrow : Prop :=
  ∀ (t r : CArg) (args : List CArg), callableNew (some (t, r)) = .ok args → ¬ nestedListFirst args →
    (callableReduce args >>= fun a => callableNew (asPair a)) = .ok args

theorem callableNew_ne_nil {t r : CArg} {args : List CArg} (h : callableNew (some (t, r)) = .ok args) :
    args ≠ [] := by
  cases t with
  | ellipsis => simp [callableNew, isParamExpr] at h; subst h; simp
  | list items => simp [callableNew] at h; subst h; simp
  | tuple items => simp [callableNew] at h; subst h; simp
  | obj m n p =>
    cases hp : isParamExpr (.obj m n p) <;> simp [callableNew, hp] at h
    subst h; simp

theorem reduce_flat (init : List CArg) (last : CArg)
    (hc : ¬ ((init ++ [last]).length = 2 ∧ isParamExpr ((init ++ [last]).headD .ellipsis) = true)) :
    (callableReduce (init ++ [last]) >>= fun a => callableNew (asPair a)) = .ok (init ++ [last]) := by
  simp only [callableReduce, if_neg hc, List.getLast?_append, List.getLast?_singleton, Option.some_or,
    List.dropLast_concat, bind, Except.bind, asPair, callableNew]

theorem callableReduceRoundTripNarrow_proven : CallableReduceRoundTripNarrow := by
  intro t r args h hn
  by_cases hc : args.length = 2 ∧ isParamExpr (args.headD .ellipsis) = true
  · obtain ⟨hl, hp⟩ := hc
    match args, hl with
    | [a, b], _ =>
      have hp' : isParamExpr a = true := by simpa [List.headD] using hp
      have hb : callableReduce [a, b] = .ok [a, b] := by simp [callableReduce, hp']
      rw [hb]
      simp only [bind, Except.bind, asPair]
      cases a with
      | ellipsis => rfl
      | list items => exact absurd ⟨items, b, rfl⟩ hn
      | tuple items => simp [isParamExpr] at hp'
      | obj m n p => simp [callableNew, hp']
  · have hne : args ≠ [] := callableNew_ne_nil h
    have e := (List.dropLast_concat_getLast hne).symm
    rw [e] at hc ⊢
    exact reduce_flat _ _ hc

/-- `_CallableGenericAlias.__repr__`, with the branch computed from `__args__`: an alias of a flattened argument list
shows it in brackets with `type_repr`, unless that list is one parameter expression; an alias `(p, r)` whose first
argument is a parameter expression has the default `GenericAlias` repr. Lib/_collections_abc.py:485-491. -/
def CallableReprSpec : Prop :=
  ∀ (tr : CArg → String) (ga : List CArg → String),
    (∀ (items : List CArg) (r : CArg), ¬ (∃ x, items = [x] ∧ isParamExpr x = true) →
      callableRepr tr ga (items ++ [r]) =
        .ok s!"collections.abc.Callable[[{", ".intercalate (items.map tr)}], {tr r}]") ∧
    (∀ p r, isParamExpr p = true → callableRepr tr ga [p, r] = .ok (ga [p, r]))

theorem callableReprSpec_proven : CallableReprSpec := by
  intro tr ga
  refine ⟨?_, ?_⟩
  · intro items r h
    have hc : ¬ ((items ++ [r]).length = 2 ∧ isParamExpr ((items ++ [r]).headD .ellipsis) = true) := by
      rintro ⟨hl, hp⟩
      cases items with
      | nil => simp at hl
      | cons x xs =>
        cases xs with
        | nil => exact h ⟨x, rfl, by simpa using hp⟩
        | cons y ys => simp at hl
    simp only [callableRepr, if_neg hc, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      List.dropLast_concat]
  · intro p r h
    simp [callableRepr, h]

/-- `_CallableGenericAlias.__getitem__` after the substitution: `new_args` whose first item is not a list or tuple are
regrouped and flattened back to themselves; a first item that is a list or tuple (PEP 612, `Z[[int, str, bool]]`) is
flattened before the result when there are exactly two, so `[[a, b], r]` gives `(a, b, r)` and `[[a], [b]]` gives
`(a, [b])`; with another count it is the `TypeError` of `__new__`. Lib/_collections_abc.py:499-514. -/
def CallableGetitemPaths : Prop :=
  (∀ (a : CArg) (rest : List CArg), a.isSeq = false → callableGetitem (a :: rest) = .ok (a :: rest)) ∧
  (∀ (items : List CArg) (r : CArg), callableGetitem [.list items, r] = .ok (items ++ [r]) ∧
    callableGetitem [.tuple items, r] = .ok (items ++ [r])) ∧
  (∀ (a : CArg) (rest : List CArg), a.isSeq = true → rest.length ≠ 1 →
    callableGetitem (a :: rest) = .error (.typeError "Callable must be used as Callable[[arg, ...], result].")) ∧
  callableGetitem [] = .error (.indexError "tuple index out of range")

theorem callableGetitemPaths_proven : CallableGetitemPaths := by
  refine ⟨?_, fun _ _ => ⟨rfl, rfl⟩, ?_, rfl⟩
  · intro a rest h
    have hne : a :: rest ≠ [] := by simp
    simp only [callableGetitem, h, Bool.not_false, ite_true, asPair, callableNew]
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne, Option.getD_some,
      List.dropLast_concat_getLast hne]
  · intro a rest h hl
    simp only [callableGetitem, h, Bool.not_true, Bool.false_eq_true, ite_false]
    match rest, hl with
    | [], _ => rfl
    | _ :: _ :: _, _ => rfl

end PyLean.CoreLibs.CollAbc
