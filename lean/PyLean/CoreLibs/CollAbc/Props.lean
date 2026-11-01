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

/-- Subclass and superclass ABC pairs of the hierarchy that has a hook on both sides. -/
def abcChain : List (String × String) :=
  [("Iterator", "Iterable"), ("Reversible", "Iterable"), ("Generator", "Iterator"),
   ("Coroutine", "Awaitable"), ("AsyncIterator", "AsyncIterable"),
   ("AsyncGenerator", "AsyncIterator"), ("Collection", "Sized"), ("Collection", "Iterable"),
   ("Collection", "Container")]

/-- The fifteen `__subclasshook__`s: a hook answers only for its own ABC, so a user subclass of
an ABC does not get the structural test; and the structural tests respect the ABC hierarchy, so
a class that passes a sub-ABC's test passes each super-ABC's test. `Collection`'s test is exactly
the conjunction of `Sized`, `Iterable` and `Container`. Quantified over every class, given as its
MRO of dictionaries. Invariant of the hierarchy. -/
def HookFamily : Prop :=
  (∀ (x cls : String) (mro : List ClassDict), cls ≠ x → subclasshook x cls mro = .notImplemented) ∧
  (∀ (mro : List ClassDict), ∀ p ∈ abcChain,
    subclasshook p.1 p.1 mro = .val true → subclasshook p.2 p.2 mro = .val true) ∧
  (∀ mro : List ClassDict, subclasshook "Collection" "Collection" mro = .val true ↔
    (subclasshook "Sized" "Sized" mro = .val true ∧
     subclasshook "Iterable" "Iterable" mro = .val true ∧
     subclasshook "Container" "Container" mro = .val true))

theorem hookFamily_proven : HookFamily := by
  refine ⟨?_, ?_, ?_⟩
  · intro x cls mro h
    simp [subclasshook, h]
  · intro mro p hp h
    simp only [subclasshook, ite_true, checkMethods_true_iff] at h ⊢
    simp only [abcChain, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · simp [hookMethods] at h ⊢
        try simp_all
  · intro mro
    simp only [subclasshook, ite_true, checkMethods_true_iff]
    simp [hookMethods]

/-! ### Abstract bodies -/

def stubGetitem {K α : Type} (e : PyExc) : K → Py α := fun _ => .error e

/-- The `Sequence` an object has when it relies on the abstract `__getitem__` and `__len__`. -/
def stubSeq (α : Type) : Seq α := ⟨stubGetitem (.indexError ""), .ok 0⟩

/-- The `Mapping` an object has when it relies on the abstract primitives. -/
def stubMap (K V : Type) : MapV K V := ⟨stubGetitem (.keyError ""), .ok [], .ok 0⟩

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

def ExcArg.name? : ExcArg → Option String
  | .cls n | .inst n => some n
  | .other => none

/-- `throw(typ, val, tb)` raises what it was given: `val`'s class when `val` is given, else
`typ`'s, with `tb` attached exactly when `tb` was given. Every other outcome is a `TypeError` or
`AttributeError` from the misuse. Docstring of `Generator.throw`. -/
def ThrowRaisesGiven : Prop :=
  ∀ (typ : ExcArg) (val : Option ExcArg) (tb : Bool) (r : Raised),
    throwBody typ val tb = .ok r →
    r.tracebackSet = tb ∧ some r.name = (val.getD typ).name?

theorem throwRaisesGiven_proven : ThrowRaisesGiven := by
  intro typ val tb r h
  cases val with
  | none =>
    cases tb <;> cases typ <;> simp_all [throwBody, raiseArg, ExcArg.name?] <;>
      (cases h; simp)
  | some v =>
    cases tb <;> cases v <;> simp_all [throwBody, raiseArg, ExcArg.name?] <;>
      (cases h; simp)

/-- Forget the value `close()` returns. -/
def dropVal {α : Type} : Py α → Py Unit
  | .ok _ => .ok ()
  | .error e => .error e

/-- `Generator.close`, `Coroutine.close` and `AsyncGenerator.aclose` have the same outcome and the
same effect on the generator as the builtin `close()`, up to the returned value: they raise the
same exception and leave the generator in the same state. Twin property, over every generator
given as a state machine. The close message is a parameter because the three differ. -/
def CloseMatchesBuiltinUpToValue : Prop :=
  ∀ (σ V : Type) (G : Gen σ V) (s : σ),
    (G.close genCloseMsg s).2 = (builtinClose G s).2 ∧
    (G.close genCloseMsg s).1 = dropVal (builtinClose G s).1

theorem closeMatchesBuiltinUpToValue_proven : CloseMatchesBuiltinUpToValue := by
  intro σ V G s
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
  ∀ (G : Gen Unit Int) (s : Unit), mixinCloseValue G s = (builtinClose G s).1

theorem closeReturnsSameValue_refuted : ¬CloseReturnsSameValue := by
  intro h
  have := h ⟨fun s _ => (.stopped 0, s), fun s => (.stopped 7, s)⟩ ()
  simp [mixinCloseValue, Gen.close, builtinClose] at this

/-- `Generator.__next__` and `AsyncGenerator.__anext__` are `send(None)`: a generator advanced by
`next` and by `send(None)` takes the same step. Docs of `generator.__next__`. -/
def NextIsSendNone : Prop :=
  ∀ (σ V : Type) (G : Gen σ V) (none : V) (s : σ), G.next none s = G.send s none

theorem nextIsSendNone_proven : NextIsSendNone := fun _ _ _ _ _ => rfl

/-! ### `Callable[...]` -/

/-- `Callable.__class_getitem__`: `__args__` flattens the argument list before the result;
`__reduce__` rebuilds the same alias (the pickling round-trip); the repr of a flattened
alias lists the arguments in brackets; and substitution, `__getitem__`, reflattens. -/
def CallableRoundTrip : Prop :=
  (∀ (items : List String) (r : String),
    callableNew (some (.tupleOrList items, r)) = .ok (items ++ [r]) ∧
    callableNew (some (callableReduceArgs (items ++ [r]) false)) = .ok (items ++ [r]) ∧
    callableRepr (items ++ [r]) false =
      s!"collections.abc.Callable[[{", ".intercalate items}], {r}]") ∧
  (∀ r : String, callableNew (some (.ellipsis, r)) = .ok ["...", r] ∧
    callableNew (some (callableReduceArgs ["...", r] true)) = .ok ["...", r]) ∧
  (∀ (p r : String), p ≠ "..." → callableNew (some (.paramExpr p, r)) = .ok [p, r] ∧
    callableNew (some (callableReduceArgs [p, r] true)) = .ok [p, r]) ∧
  (∀ (names : List String), names ≠ [] →
    callableGetitem (names.map SubstArg.typ) = .ok names) ∧
  (∀ (a : CallArg), isParamExpr false a = true ↔
    (a = .ellipsis ∨ ∃ p, a = .paramExpr p))

theorem reduce_false (l : List String) :
    callableReduceArgs l false = (.tupleOrList l.dropLast, (l.getLast?).getD "") := by
  unfold callableReduceArgs; split <;> simp_all

theorem repr_false (l : List String) :
    callableRepr l false =
      s!"collections.abc.Callable[[{", ".intercalate l.dropLast}], {(l.getLast? |>.getD "")}]" := by
  unfold callableRepr; split <;> simp_all

theorem repr_typ (l : List String) : (l.map SubstArg.typ).map SubstArg.repr = l := by
  induction l with
  | nil => rfl
  | cons a as ih => simpa [SubstArg.repr] using ih

theorem getitem_typ : ∀ l : List String, callableGetitem (l.map SubstArg.typ) =
    callableNew (some (.tupleOrList l.dropLast, l.getLast?.getD ""))
  | [] => by simp [callableGetitem]
  | [x] => by simp [callableGetitem, SubstArg.repr]
  | x :: y :: ys => by
    have h := repr_typ (x :: y :: ys)
    simp only [List.map_cons] at h
    simp only [callableGetitem, List.map_cons, h]

theorem callableRoundTrip_proven : CallableRoundTrip := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro items r
    refine ⟨by simp [callableNew], ?_, ?_⟩
    · rw [reduce_false]; simp [callableNew]
    · rw [repr_false]; simp
  · intro r
    simp [callableNew, callableReduceArgs, isParamExpr]
  · intro p r h
    simp [callableNew, callableReduceArgs, isParamExpr, h]
  · intro names h
    rw [getitem_typ]
    simp only [callableNew]
    rw [List.getLast?_eq_some_getLast h, Option.getD_some, List.dropLast_concat_getLast]
  · intro a
    cases a <;> simp [isParamExpr]

end PyLean.CoreLibs.CollAbc
