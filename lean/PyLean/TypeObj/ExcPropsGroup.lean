import PyLean.TypeObj.ExcPropsSplit
import PyLean.TypeObj.ExcPropsRest
import PyLean.TypeObj.Builtins

/-!
Properties of `BaseExceptionGroup` other than the split recursion: construction, `str` and
`repr`, `exceptiongroup_subset`, the matcher, `_PyExc_PrepReraiseStar`, and the Unicode C API
getters that remain. Hypotheses are explained in `ExcPropsBase`.
-/

namespace PyLean.TypeObj

/-! ## Construction -/

/-- **Every item is checked, in order.** The first item that is not an exception instance is
a `ValueError` naming its index, whatever user code ran for the items before it. -/
def EgRejectsNonException : Prop :=
  ∀ (rt : Rt) (i : Nat) (nested : Bool) (x : Val) (xs : List Val) (w : World),
    excInstanceCheck w x = false →
    egCheckItems rt i nested (x :: xs) w =
      .err (.exc B.ValueError s!"Item {i} of second argument (exceptions) is not an exception" none) w

theorem egRejectsNonException_proven : EgRejectsNonException := by
  intro rt i nested x xs w h
  simp [egCheckItems, h, valueErr, raiseC]

/-- **No `BaseException` in an `Exception` group.** If an item is not an `Exception`
(`nested`), the class chosen never derives from `Exception`: `ExceptionGroup` and its
subclasses are refused with `TypeError`, whatever the class hierarchy. The hypothesis is the
fact about the builtin classes that `BaseExceptionGroup` is not an `Exception`. -/
def EgNoBaseInExceptionGroup : Prop :=
  ∀ (t c : Addr) (w w' : World),
    isSubtype w B.BaseExceptionGroup B.Exception = false →
    isSubtype w B.ExceptionGroup B.Exception = true →
    egChooseClass t true w = .ok c w' → isSubtype w' c B.Exception = false

theorem egNoBaseInExceptionGroup_proven : EgNoBaseInExceptionGroup := by
  intro t c w w' h1 _ h
  simp only [egChooseClass, M.bind_app, getW_app] at h
  by_cases h2 : t = B.ExceptionGroup
  · simp [h2, typeErr, raiseC] at h
  · have h2' : (t == B.ExceptionGroup) = false := by simpa using h2
    by_cases h3 : t = B.BaseExceptionGroup
    · have h3' : (t == B.BaseExceptionGroup) = true := by simpa using h3
      simp [h2', h3'] at h
      obtain ⟨h4, h5⟩ := h
      subst h4 h5
      subst h3
      exact h1
    · have h3' : (t == B.BaseExceptionGroup) = false := by simpa using h3
      by_cases h4 : isSubtype w t B.Exception = true
      · simp [h2', h3', h4, typeErr, raiseC] at h
      · simp [h2', h3', h4] at h
        obtain ⟨h5, h6⟩ := h
        subst h5 h6
        simpa using h4

/-- **`BaseExceptionGroup` wraps in `ExceptionGroup` when it can.** With no `BaseException`
inside, `BaseExceptionGroup(...)` makes an `ExceptionGroup`; every other class is kept. -/
def EgWrapsInExceptionGroup : Prop :=
  (∀ (w : World), egChooseClass B.BaseExceptionGroup false w = .ok B.ExceptionGroup w) ∧
  (∀ (t : Addr) (w : World), t ≠ B.BaseExceptionGroup → egChooseClass t false w = .ok t w)

theorem egWrapsInExceptionGroup_proven : EgWrapsInExceptionGroup := by
  refine ⟨?_, ?_⟩
  · intro w
    simp [egChooseClass, B.BaseExceptionGroup, B.ExceptionGroup]
  · intro t w h
    have h' : (t == B.BaseExceptionGroup) = false := by simpa using h
    by_cases h2 : t = B.ExceptionGroup
    · simp [egChooseClass, h2]
    · have h2' : (t == B.ExceptionGroup) = false := by simpa using h2
      simp [egChooseClass, h2', h']

/-- **An empty group is refused**, for lists and tuples, after the type checks. The hypotheses
are the type invariants of `str` and `tuple`. -/
def EgRejectsEmpty : Prop :=
  ∀ (rt : Rt) (t : Addr) (m : String) (w : World),
    excSeqCheck w (.tuple []) = true →
    baseExceptionGroupNew rt t [.str m, .tuple []] w =
      .err (.exc B.ValueError "second argument (exceptions) must be a non-empty sequence" none) w

theorem egRejectsEmpty_proven : EgRejectsEmpty := by
  intro rt t m w h
  simp [baseExceptionGroupNew, egNewParse, argCount, argU, strOf, h, tupleOf, excSeqTuple, valueErr, raiseC]

/-- **`str(eg)`** is the `str` of the message and the count, with the plural only above one. -/
def EgStrFormat : Prop :=
  ∀ (rt : Rt) (self : Val) (w w' : World) (m : String),
    rt.str ((excDataOf w self).egMessage.getD .none) w = .ok m w' →
    let n := (excDataOf w self).egExceptions.length
    baseExceptionGroupStr rt self w =
      .ok (.str s!"{m} ({n} sub-exception{if n > 1 then "s" else ""})") w'

theorem egStrFormat_proven : EgStrFormat := by
  intro rt self w w' m h
  simp only [baseExceptionGroupStr, M.bind_app, getW_app, h]
  rfl

/-- `__init__` of a group rejects keywords and otherwise stores `args` only. -/
def EgInitKeepsMembers : Prop :=
  (∀ (a : Addr) (d : ExcData) (args : List Val) (w w' : World), IsExc w a d →
    baseExceptionGroupInit (.obj a) args [] w = .ok () w' →
    (excDataOf w' (.obj a)).args = args ∧
    (excDataOf w' (.obj a)).egMessage = d.egMessage ∧
    (excDataOf w' (.obj a)).egExceptions = d.egExceptions) ∧
  (∀ (self : Val) (args : List Val) (k : Name) (x : Val) (w : World),
    baseExceptionGroupInit self args [(k, x)] w =
      .err (.exc B.TypeError s!"{typeName w self}() takes no keyword arguments" none) w)

theorem egInitKeepsMembers_proven : EgInitKeepsMembers := by
  refine ⟨?_, ?_⟩
  · intro a d args w w' hx h
    simp [baseExceptionGroupInit, baseExceptionInit, argNoKeywords, excUpdate_app] at h
    subst h
    simp [excUpdW_data hx]
  · intro self args k x w
    simp [baseExceptionGroupInit, argNoKeywords, typeErr, raiseC]

/-! ## `repr` -/

/-- **`BaseExceptionGroup_repr` looks at `args[1]` only when there are two `args`.** `args` is
writable and `__init__` replaces it, so `eg.args = ()` leaves a group with any `args`. Then `repr`
is the tuple form of `eg.exceptions`, for every `args` that is not two items long. -/
def EgReprAnyArgs : Prop :=
  ∀ (rt : Rt) (self : Val) (r m : String) (w w1 w2 : World),
    (excDataOf w self).egExcsStr = none → (excDataOf w self).args.length ≠ 2 →
    rt.repr (.tuple (excDataOf w self).egExceptions) w = .ok r w1 →
    rt.repr ((excDataOf w self).egMessage.getD .none) w1 = .ok m w2 →
    baseExceptionGroupRepr rt self w =
      .ok (.str s!"{pyTypeName w1 (typeOf w1 self)}({m}, {r})") w2

theorem egReprAnyArgs_proven : EgReprAnyArgs := by
  intro rt self r m w w1 w2 h1 h2 h3 h4
  have hl : egArgsShowList w (excDataOf w self) = false := by
    simp [egArgsShowList, h2]
  simp only [baseExceptionGroupRepr, M.bind_app, getW_app, h1, hl, Bool.false_eq_true, if_false,
    h3, h4]
  rfl

/-- `__new__` leaves two `args`, so the list test looks at the second for every group fresh from
`BaseExceptionGroup_new`. -/
def EgReprInBoundsAfterNew : Prop :=
  ∀ (rt : Rt) (t : Addr) (args : List Val) (v : Val) (w w' : World),
    baseExceptionGroupNew rt t args w = .ok v w' →
    args.length = 2 ∧ (excDataOf w' v).args.length = 2

theorem argCount_ok (f : Option String) (min max n : Nat) (u : Unit) (w w' : World)
    (h : argCount f min max n w = .ok u w') : min ≤ n ∧ n ≤ max ∧ w' = w := by
  simp only [argCount, M.bind_app] at h
  by_cases hc : (decide (n < min) || decide (max < n)) = true
  · simp [hc, typeErr, raiseC] at h
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hc
    simp [show ¬(n < min ∨ max < n) by omega] at h
    exact ⟨hc.1, hc.2, h.symm⟩

theorem egNewParse_length (rt : Rt) (t : Addr) (args : List Val) (r) (w w' : World)
    (h : egNewParse rt t args w = .ok r w') : args.length = 2 := by
  simp only [egNewParse, M.bind_app] at h
  cases hc : argCount (some "BaseExceptionGroup.__new__") 2 2 args.length w with
  | err e w1 => simp [hc] at h
  | ok u w1 =>
    obtain ⟨h1, h2, _⟩ := argCount_ok _ _ _ _ _ _ _ hc
    omega

theorem egReprInBoundsAfterNew_proven : EgReprInBoundsAfterNew := by
  intro rt t args v w w' h
  simp only [baseExceptionGroupNew, M.bind_app] at h
  cases hp : egNewParse rt t args w with
  | err e w1 => simp [hp] at h
  | ok r w1 =>
    have hl := egNewParse_length _ _ _ _ _ _ hp
    obtain ⟨msg, excs, str, cls⟩ := r
    simp only [hp] at h
    rw [alloc_app] at h
    simp at h
    obtain ⟨h1, h2⟩ := h
    subst h1 h2
    refine ⟨hl, ?_⟩
    rw [(isExc_alloc w1 cls _).data]
    simp [hl]

/-! ## `exceptiongroup_subset` -/

theorem Val.is_none_iff (v : Val) : v.is .none = true ↔ v = .none := by
  cases v <;> simp [Val.is]

theorem excData_update_ne (w : World) (a b : Addr) (f : ExcData → ExcData) (h : a ≠ b) :
    excDataOf (excUpdW w a f) (.obj b) = excDataOf w (.obj b) := by
  simp [excDataOf, payloadOf, get_excUpdW_ne _ _ _ _ h]

/-- **The metadata goes across.** After `exceptiongroup_subset`'s copy, the new group has the
`__context__` and `__cause__` of the original, and its `__traceback__` if it has one. Holds when
`derive` returned any group, the original included. -/
def SubsetCopiesMetadata : Prop :=
  ∀ (o a : Addr) (d dO : ExcData) (w w' : World), IsExc w a d → IsExc w o dO →
    subsetCopyMeta (.obj o) (.obj a) w = .ok () w' →
    (excDataOf w' (.obj a)).context = dO.context ∧
    (excDataOf w' (.obj a)).cause = dO.cause ∧
    (dO.traceback ≠ .none → (excDataOf w' (.obj a)).traceback = dO.traceback)

theorem tracebackSet_some (a : Addr) (tb : Val) (w w1 : World) (hn : tb ≠ .none)
    (h : baseExceptionTracebackSet (.obj a) (some tb) w = .ok () w1) :
    w1 = excUpdW w a (fun d => { d with traceback := tb }) := by
  simp only [baseExceptionTracebackSet, M.bind_app, getW_app] at h
  by_cases h1 : tracebackCheck w tb = true
  · simp [h1, excUpdate_app] at h
    exact h.symm
  · have h1' : tracebackCheck w tb = false := by simpa using h1
    have h2 : tb.is .none = false := by
      cases hb : tb.is .none with
      | false => rfl
      | true => exact absurd ((Val.is_none_iff tb).1 hb) hn
    simp [h1', h2, typeErr, raiseC] at h

theorem subsetCopiesMetadata_proven : SubsetCopiesMetadata := by
  intro o a d dO w w' hx hO h
  simp only [subsetCopyMeta, M.bind_app, getW_app] at h
  cases hg : pyExceptionGetTraceback w (.obj o) with
  | none =>
    have hd := hO.data
    simp [hg, pyExceptionSetContext, pyExceptionSetCause, excUpdate_app, pyExceptionGetContext,
      pyExceptionGetCause, hd] at h
    subst h
    have h1 := hx.update (fun e => { e with context := dO.context })
    rw [excUpdW_data h1]
    refine ⟨rfl, rfl, ?_⟩
    intro hn
    simp only [pyExceptionGetTraceback, hd] at hg
    cases ht : dO.traceback with
    | none => exact absurd ht hn
    | _ => simp [ht] at hg
  | some tb =>
    have hd := hO.data
    have hne : tb ≠ .none := by
      intro he
      subst he
      simp only [pyExceptionGetTraceback, hd] at hg
      cases ht : dO.traceback <;> simp [ht] at hg
    have htb : dO.traceback = tb := by
      simp only [pyExceptionGetTraceback, hd] at hg
      cases ht : dO.traceback <;> simp_all
    simp only [hg] at h
    cases ht : baseExceptionTracebackSet (.obj a) (some tb) w with
    | err e w1 => simp [ht] at h
    | ok u w1 =>
      have hw := tracebackSet_some a tb w w1 hne ht
      subst hw
      have h1 := hx.update (fun e => { e with traceback := tb })
      have hctx : excDataOf (excUpdW w a (fun e => { e with traceback := tb })) (.obj o) =
          (if o = a then { dO with traceback := tb } else dO) := by
        by_cases hoa : o = a
        · subst hoa
          have hdd : d = dO := by
            have := hx.data
            rw [hO.data] at this
            exact this.symm
          subst hdd
          simp [excUpdW_data hx]
        · simp [excData_update_ne _ _ _ _ (Ne.symm hoa), hoa, hd]
      have hc1 : (excDataOf (excUpdW w a (fun e => { e with traceback := tb })) (.obj o)).context =
          dO.context := by
        rw [hctx]
        split <;> rfl
      have hc2 : (excDataOf (excUpdW w a (fun e => { e with traceback := tb })) (.obj o)).cause =
          dO.cause := by
        rw [hctx]
        split <;> rfl
      simp [ht, pyExceptionSetContext, pyExceptionSetCause, excUpdate_app, pyExceptionGetContext,
        pyExceptionGetCause, hc1, hc2] at h
      subst h
      have h2 := h1.update (fun e => { e with context := dO.context })
      rw [excUpdW_data h2]
      exact ⟨rfl, rfl, fun _ => htb.symm⟩

/-- **`__suppress_context__` goes across too.** FALSE: the cause is copied with
`PyException_SetCause`, which sets `suppress_context` on the new group whatever the original's
is, so `split`, `subgroup` and `except*` hide a `__context__` that the original would show. -/
def SubsetCopiesSuppressContext : Prop :=
  ∀ (o a : Addr) (d dO : ExcData) (w w' : World), IsExc w a d → IsExc w o dO →
    subsetCopyMeta (.obj o) (.obj a) w = .ok () w' →
    (excDataOf w' (.obj a)).suppressContext = dO.suppressContext

theorem subsetCopiesSuppressContext_refuted : ¬SubsetCopiesSuppressContext := by
  intro h
  let d : ExcData := {}
  let c : Cell := .val { body := .exc d }
  let w : World := { heap := #[c, c] }
  have h0 : IsExc w 0 d := by
    constructor
    · simp [w]
    · simp [payloadOf, World.get, w, c]
  have h1 : IsExc w 1 d := by
    constructor
    · simp [w]
    · simp [payloadOf, World.get, w, c]
  have hg : pyExceptionGetTraceback w (.obj 0) = none := by
    simp [pyExceptionGetTraceback, h0.data, d]
  have hs : subsetCopyMeta (.obj 0) (.obj 1) w =
      .ok () (excUpdW (excUpdW w 1 (fun e => { e with context := none }))
        1 (fun e => { e with suppressContext := true, cause := none })) := by
    simp [subsetCopyMeta, hg, pyExceptionSetContext, pyExceptionSetCause, excUpdate_app,
      pyExceptionGetContext, pyExceptionGetCause, h0.data, d]
  have := h 0 1 d d w _ h1 h0 hs
  have h2 := h1.update (fun e => { e with context := none })
  rw [excUpdW_data h2] at this
  simp [d] at this

/-- **An empty part is NULL without calling `derive`**, and a `derive` that does not return a
group is a `TypeError`. -/
def SubsetChecks : Prop :=
  (∀ (rt : Rt) (orig : Val) (w : World), exceptiongroupSubset rt orig [] w = .ok none w) ∧
  (∀ (rt : Rt) (orig x g : Val) (xs : List Val) (w w1 : World),
    callMethodO rt orig "derive" (.obj w.heap.size)
      { w with heap := w.heap.push (.val { cls := B.list, body := .list (x :: xs) }) } = .ok g w1 →
    egCheck w1 g = false →
    exceptiongroupSubset rt orig (x :: xs) w =
      .err (.exc B.TypeError "derive must return an instance of BaseExceptionGroup" none) w1)

theorem subsetChecks_proven : SubsetChecks := by
  refine ⟨?_, ?_⟩
  · intro rt orig w
    simp [exceptiongroupSubset]
  · intro rt orig x g xs w w1 h1 h2
    have hE : (x :: xs).isEmpty = false := rfl
    simp only [exceptiongroupSubset, hE, M.bind_app]
    try simp only [Bool.false_eq_true, if_false, M.bind_app]
    rw [alloc_app]
    dsimp only
    rw [h1]
    dsimp only
    simp only [getW_app]
    simp [h2, typeErr, raiseC]

/-! ## The matcher -/

/-- **`get_matcher_type` classifies its argument.** A non-class callable is a predicate, an
exception class or a tuple of them matches by type, and everything else is the `TypeError`. -/
def GetMatcherTypeClassifies : Prop :=
  (∀ (v : Val) (w : World), excCallableCheck w v = true → typeCheck w v = false →
    ∃ w', getMatcherType v w = .ok .byPredicate w' ∧ w' = w) ∧
  (∀ (v : Val) (w : World), (excCallableCheck w v = false ∨ typeCheck w v = true) →
    excClassCheck w v = true → ∃ w', getMatcherType v w = .ok .byType w' ∧ w' = w) ∧
  (∀ (xs : List Val) (w : World), excCallableCheck w (.tuple xs) = false →
    excClassCheck w (.tuple xs) = false → xs.all (excClassCheck w) = true →
    ∃ w', getMatcherType (.tuple xs) w = .ok .byType w' ∧ w' = w) ∧
  (∀ (i : Int) (w : World), excCallableCheck w (.int i) = false →
    excClassCheck w (.int i) = false →
    getMatcherType (.int i) w = .err (.exc B.TypeError
      "expected an exception type, a tuple of exception types, or a callable (other than a class)" none) w)

theorem getMatcherTypeClassifies_proven : GetMatcherTypeClassifies := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v w h1 h2
    exact ⟨w, by simp [getMatcherType, h1, h2], rfl⟩
  · intro v w h1 h2
    refine ⟨w, ?_, rfl⟩
    rcases h1 with h | h <;> simp [getMatcherType, h, h2]
  · intro xs w h1 h2 h3
    refine ⟨w, ?_, rfl⟩
    have h3' : ∀ x ∈ xs, excClassCheck w x = true := by simpa using h3
    simp [getMatcherType, h1, h2, h3']
    rw [if_pos h3']
    rfl
  · intro i w h1 h2
    simp [getMatcherType, h1, h2, typeErr, raiseC]

/-- **Matching by type is `isinstance` for exception classes.** For an exception instance and
an exception class, `PyErr_GivenExceptionMatches` is the subclass test. -/
def MatchByTypeIsSubclass : Prop :=
  ∀ (w : World) (e : Val) (c : Addr), excInstanceCheck w e = true →
    typeCheck w (.obj (typeOf w e)) = true → typeCheck w (.obj c) = true →
    isSubtype w c B.BaseException = true →
    givenMatchesClass w e (.obj c) = isSubtype w (typeOf w e) c

theorem matchByTypeIsSubclass_proven : MatchByTypeIsSubclass := by
  intro w e c h1 h2 h3 h4
  have h1' : isSubtype w (typeOf w e) B.BaseException = true := h1
  simp [givenMatchesClass, h1, asType, h2, h3, h1', h4]

/-! ## `except*` -/

/-- **`collect_exception_group_leaf_ids`** ignores `None` and adds a leaf as itself. -/
def CollectLeafIdsBase : Prop :=
  (∀ (w : World) (f : Nat), collectLeafIds w (f + 1) .none = []) ∧
  (∀ (w : World) (f : Nat) (v : Val), v.is .none = false → egCheck w v = false →
    collectLeafIds w (f + 1) v = [v])

theorem collectLeafIdsBase_proven : CollectLeafIdsBase := by
  refine ⟨?_, ?_⟩
  · intro w f
    simp [collectLeafIds, Val.is]
  · intro w f v h1 h2
    simp [collectLeafIds, h1, h2]

/-- **The matcher of `except*` selects leaves only**: a group is never matched by
`EXCEPTION_GROUP_MATCH_INSTANCE_IDS`, and a leaf is matched exactly when its id is in the set. -/
def InstanceIdsMatchLeaves : Prop :=
  (∀ (rt : Rt) (ids : List Val) (mv exc : Val) (w : World), egCheck w exc = true →
    splitCheckMatch rt exc (.instanceIds ids) mv w = .ok false w) ∧
  (∀ (rt : Rt) (ids : List Val) (mv exc : Val) (w : World), egCheck w exc = false →
    splitCheckMatch rt exc (.instanceIds ids) mv w = .ok (ids.any (Val.is · exc)) w)

theorem instanceIdsMatchLeaves_proven : InstanceIdsMatchLeaves := by
  refine ⟨?_, ?_⟩
  · intro rt ids mv exc w h
    simp [splitCheckMatch, h]
  · intro rt ids mv exc w h
    simp [splitCheckMatch, h]

/-- **`_PyExc_PrepReraiseStar`'s two short paths.** No exceptions give `None`, and with a naked
exception caught, the first entry is returned as is. -/
def PrepReraiseStarShortPaths : Prop :=
  (∀ (rt : Rt) (orig : Val) (w : World), excPrepReraiseStar rt orig [] w = .ok .none w) ∧
  (∀ (rt : Rt) (orig e : Val) (es : List Val) (w : World), egCheck w orig = false →
    excPrepReraiseStar rt orig (e :: es) w = .ok e w)

theorem prepReraiseStarShortPaths_proven : PrepReraiseStarShortPaths := by
  refine ⟨?_, ?_⟩
  · intro rt orig w
    simp [excPrepReraiseStar]
  · intro rt orig e es w h
    simp [excPrepReraiseStar, h]

/-- **`PyUnstable_Exc_PrepReraiseStar` validates before it runs**: `orig` must be an exception,
`excs` a list of exceptions or `None`, and `orig` must have a traceback. -/
def PrepReraiseStarValidates : Prop :=
  (∀ (rt : Rt) (orig excs : Val) (w : World), excInstanceCheck w orig = false →
    pyUnstableExcPrepReraiseStar rt orig excs w =
      .err (.exc B.TypeError "orig must be an exception instance" none) w) ∧
  (∀ (rt : Rt) (orig excs : Val) (w : World), excInstanceCheck w orig = true →
    listOf w excs = none →
    pyUnstableExcPrepReraiseStar rt orig excs w =
      .err (.exc B.TypeError "excs must be a list of exception instances" none) w) ∧
  (∀ (rt : Rt) (orig excs : Val) (xs : List Val) (w : World), excInstanceCheck w orig = true →
    listOf w excs = some xs → firstNonExc w 0 xs = none →
    pyExceptionGetTraceback w orig = none →
    pyUnstableExcPrepReraiseStar rt orig excs w =
      .err (.exc B.ValueError "orig must be a raised exception" none) w)

theorem prepReraiseStarValidates_proven : PrepReraiseStarValidates := by
  refine ⟨?_, ?_, ?_⟩
  · intro rt orig excs w h
    simp [pyUnstableExcPrepReraiseStar, h, typeErr, raiseC]
  · intro rt orig excs w h1 h2
    simp [pyUnstableExcPrepReraiseStar, h1, h2, typeErr, raiseC]
  · intro rt orig excs xs w h1 h2 h3 h4
    simp [pyUnstableExcPrepReraiseStar, h1, h2, h3, h4, valueErr, raiseC]

/-- **`is_same_exception_metadata` is reflexive**: an exception is a re-raise of itself. -/
def SameMetadataReflexive : Prop :=
  ∀ (w : World) (v : Val), isSameExceptionMetadata w v v = true

theorem sameRef_refl (x : Option Val) : sameRef x x = true := by
  cases x <;> simp [sameRef, Val.is_refl]

theorem sameMetadataReflexive_proven : SameMetadataReflexive := by
  intro w v
  simp [isSameExceptionMetadata, sameRef_refl, Val.is_refl]

/-- **"Same metadata" includes the notes.** `is_same_exception_metadata` compares `notes`, so
two exceptions it calls the same should have the same `__notes__`. FALSE: the field it compares
is the unused C field, and `add_note` writes the instance attribute. An `except*` handler that
adds a note and re-raises is classified as a re-raise, and the note is dropped. -/
def SameMetadataComparesNotes : Prop :=
  ∀ (w : World) (a b : Val), isSameExceptionMetadata w a b = true →
    instDictGet w a "__notes__" = instDictGet w b "__notes__"

theorem sameMetadataComparesNotes_refuted : ¬SameMetadataComparesNotes := by
  intro h
  let ty : Cell := .ty 0 { dictoffset := 16 }
  let e1 : Cell := .val { cls := 0, dict := some 3, body := .exc {} }
  let e2 : Cell := .val { cls := 0, body := .exc {} }
  let dc : Cell := .val { cls := B.dict, body := .dict [(.str "__notes__", .int 1)] }
  let w : World := { heap := #[ty, e1, e2, dc] }
  have hs : isSameExceptionMetadata w (.obj 1) (.obj 2) = true := by
    simp [isSameExceptionMetadata, excDataOf, payloadOf, World.get, w, e1, e2, sameRef, Val.is]
  have h1 : instDictGet w (.obj 1) "__notes__" = some (.int 1) := by
    simp [instDictGet, hasDictPtr, typeOf, tdata, World.get, w, ty, e1, instDictAddr, dictOf,
      payloadOf, dc, dictLookup, Val.is]
  have h2 : instDictGet w (.obj 2) "__notes__" = none := by
    simp [instDictGet, hasDictPtr, typeOf, tdata, World.get, w, ty, e2, instDictAddr]
  have := h w _ _ hs
  rw [h1, h2] at this
  simp at this

/-! ## Remaining cases -/

/-- **`_PyException_AddNote` checks its argument** before anything else, and
`PyExceptionClass_Name` is `tp_name`. -/
def PyExceptionMiscApi : Prop :=
  (∀ (rt : Rt) (exc note : Val) (w : World), excInstanceCheck w exc = false →
    pyExceptionAddNote rt exc note w =
      .err (.exc B.TypeError s!"exc must be an exception, not '{typeName w exc}'" none) w) ∧
  (∀ (w : World) (t : Addr), pyExceptionClassName w t = tpName w t)

theorem pyExceptionMiscApi_proven : PyExceptionMiscApi := by
  refine ⟨?_, ?_⟩
  · intro rt exc note w h
    simp [pyExceptionAddNote, h, typeErr, raiseC]
  · intro w t
    rfl

/-- **`AttributeError_init` stores both keywords.** -/
def AttributeErrorInitKeywords : Prop :=
  ∀ (a : Addr) (d : ExcData) (args : List Val) (n o : Val) (w w' : World), IsExc w a d →
    attributeErrorInit (.obj a) args [("name", n), ("obj", o)] w = .ok () w' →
    excArgs w' (.obj a) = args ∧ memGet (excDataOf w' (.obj a)) "name" = some n ∧
    memGet (excDataOf w' (.obj a)) "obj" = some o

theorem attributeErrorInitKeywords_proven : AttributeErrorInitKeywords := by
  intro a d args n o w w' hx h
  simp [attributeErrorInit, baseExceptionInit, argNoKeywords, argKeywordOnly, excUpdate_app,
    NameDict.get?] at h
  subst h
  have h1 := hx.update (fun d => { d with args := args })
  have h2 := isExc_memSet h1 "name" (some n)
  rw [(isExc_memSet h2 "obj" (some o)).data]
  refine ⟨by simp [excArgs, excDataOf, (isExc_memSet h2 "obj" (some o)).body, memSet], ?_, ?_⟩
  · rw [memGet_memSet_ne _ _ _ _ (by decide)]
    exact memGet_memSet_same _ _ _
  · exact memGet_memSet_same _ _ _

/-- **`SyntaxError(msg, info)` checks `info`.** Fewer than four or more than seven items is the
arity `TypeError`, and five items is refused because `end_offset` is missing. -/
def SyntaxErrorInitChecks : Prop :=
  (∀ (rt : Rt) (self : Val) (items : List Val) (w : World),
    (items.length < 4 ∨ 7 < items.length) →
    ∃ s, syntaxErrorParseInfo rt self (.tuple items) w = .err (.exc B.TypeError s none) w) ∧
  (∀ (rt : Rt) (a : Addr) (v0 v1 v2 v3 v4 : Val) (w : World),
    ∃ w', syntaxErrorParseInfo rt (.obj a) (.tuple [v0, v1, v2, v3, v4]) w =
      .err (.exc B.TypeError "end_offset must be provided when end_lineno is provided" none) w')

theorem excUpdate_total (a : Addr) (f : ExcData → ExcData) (w : World) :
    ∃ w', excUpdate (.obj a) f w = .ok () w' := ⟨_, excUpdate_app w a f⟩

theorem syntaxErrorStoreInfo_ok (a : Addr) (info : List Val) (w : World) :
    ∃ w', syntaxErrorStoreInfo (.obj a) info w = .ok () w' := by
  obtain ⟨w1, h1⟩ := excUpdate_total a (memSet "filename" info[0]?) w
  obtain ⟨w2, h2⟩ := excUpdate_total a (memSet "lineno" info[1]?) w1
  obtain ⟨w3, h3⟩ := excUpdate_total a (memSet "offset" info[2]?) w2
  obtain ⟨w4, h4⟩ := excUpdate_total a (memSet "text" info[3]?) w3
  obtain ⟨w5, h5⟩ := excUpdate_total a (memSet "end_lineno" info[4]?) w4
  obtain ⟨w6, h6⟩ := excUpdate_total a (memSet "end_offset" info[5]?) w5
  obtain ⟨w7, h7⟩ := excUpdate_total a (memSet "_metadata" info[6]?) w6
  exact ⟨w7, by simp only [syntaxErrorStoreInfo, M.bind_app, h1, h2, h3, h4, h5, h6, h7]⟩

theorem syntaxErrorInitChecks_proven : SyntaxErrorInitChecks := by
  refine ⟨?_, ?_⟩
  · intro rt self items w hn
    obtain ⟨s, hs⟩ := argCount_err none 4 7 items.length w hn
    refine ⟨s, ?_⟩
    simp only [syntaxErrorParseInfo, M.bind_app, excSeqTuple, M.pure_app, hs]
  · intro rt a v0 v1 v2 v3 v4 w
    obtain ⟨w1, h1⟩ := syntaxErrorStoreInfo_ok a [v0, v1, v2, v3, v4] w
    refine ⟨w1, ?_⟩
    have hc : argCount none 4 7 5 w = .ok () w := by simp [argCount]
    simp only [syntaxErrorParseInfo, M.bind_app, excSeqTuple, M.pure_app, List.length_cons,
      List.length_nil, h1]
    simp [hc, typeErr, raiseC]
    rw [h1]

/-- **A `SyntaxError` without location is its message**: no `str` filename and no exact `int`
line number give `str(msg)`, or `str(None)` when `msg` is unset. -/
def SyntaxErrorStrPlain : Prop :=
  ∀ (rt : Rt) (v : Val) (w : World), memGet (excDataOf w v) "filename" = none →
    memGet (excDataOf w v) "lineno" = none →
    syntaxErrorStr rt v w = (Val.str <$> rt.str (orNone (memGet (excDataOf w v) "msg"))) w

theorem syntaxErrorStrPlain_proven : SyntaxErrorStrPlain := by
  intro rt v w h1 h2
  simp [syntaxErrorStr, h1, h2]

/-- **An uninitialised Unicode error prints as the empty string.** With `object` NULL (made by
`__new__` without `__init__`), all three `__str__`s return `""` without looking at `reason`. -/
def UnicodeStrUninitialized : Prop :=
  ∀ (rt : Rt) (v : Val) (w : World), memGet (excDataOf w v) "object" = none →
    unicodeEncodeErrorStr rt v w = .ok (.str "") w ∧
    unicodeDecodeErrorStr rt v w = .ok (.str "") w ∧
    unicodeTranslateErrorStr rt v w = .ok (.str "") w

theorem unicodeStrUninitialized_proven : UnicodeStrUninitialized := by
  intro rt v w h
  simp [unicodeEncodeErrorStr, unicodeDecodeErrorStr, unicodeTranslateErrorStr, h]

/-- **`__init__` stores `args` first, for the other two Unicode errors as well.** -/
def UnicodeInitArgsFirstOthers : Prop :=
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (args : List Val) (w : World), IsExc w a d →
    args.length ≠ 5 →
    ∃ w' e, unicodeDecodeErrorInit rt (.obj a) args [] w = .err e w' ∧
      excArgs w' (.obj a) = args) ∧
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (args : List Val) (w : World), IsExc w a d →
    args.length ≠ 4 →
    ∃ w' e, unicodeTranslateErrorInit rt (.obj a) args [] w = .err e w' ∧
      excArgs w' (.obj a) = args)

theorem unicodeInitArgsFirstOthers_proven : UnicodeInitArgsFirstOthers := by
  refine ⟨?_, ?_⟩
  · intro rt a d args w hx hn
    obtain ⟨m, hm⟩ := argCount_err none 5 5 args.length
      (excUpdW w a (fun d => { d with args := args })) (by omega)
    have h0 : baseExceptionInit (.obj a) args [] w =
        .ok () (excUpdW w a (fun d => { d with args := args })) := by
      simp [baseExceptionInit, argNoKeywords, excUpdate_app]
    refine ⟨excUpdW w a (fun d => { d with args := args }), .exc B.TypeError m none, ?_, ?_⟩
    · simp only [unicodeDecodeErrorInit, M.bind_app, h0, hm]
    · simp [excArgs, excUpdW_data hx]
  · intro rt a d args w hx hn
    obtain ⟨m, hm⟩ := argCount_err none 4 4 args.length
      (excUpdW w a (fun d => { d with args := args })) (by omega)
    have h0 : baseExceptionInit (.obj a) args [] w =
        .ok () (excUpdW w a (fun d => { d with args := args })) := by
      simp [baseExceptionInit, argNoKeywords, excUpdate_app]
    refine ⟨excUpdW w a (fun d => { d with args := args }), .exc B.TypeError m none, ?_, ?_⟩
    · simp only [unicodeTranslateErrorInit, M.bind_app, h0, hm]
    · simp [excArgs, excUpdW_data hx]

/-- **A saved `exceptions_str` is used as is**, which is why the repr of a group built from a
custom sequence does not change when the sequence does. -/
def EgReprSavedString : Prop :=
  ∀ (rt : Rt) (self : Val) (s m : String) (w w' : World),
    (excDataOf w self).egExcsStr = some s →
    rt.repr ((excDataOf w self).egMessage.getD .none) w = .ok m w' →
    baseExceptionGroupRepr rt self w =
      .ok (.str s!"{pyTypeName w (typeOf w self)}({m}, {s})") w'

theorem egReprSavedString_proven : EgReprSavedString := by
  intro rt self s m w w' h1 h2
  simp only [baseExceptionGroupRepr, M.bind_app, getW_app, h1, M.pure_app, h2]

/-! ## The rest of the C API -/

/-- **Groups are created by calling `BaseExceptionGroup`.** `derive` and
`_PyExc_CreateExceptionGroup` both go through the class, so subclasses are not preserved by
`derive` unless they override it. -/
def EgCreatedThroughClass : Prop :=
  (∀ (rt : Rt) (self excs : Val) (w : World), baseExceptionGroupDerive rt self excs w =
    rt.call (.obj B.BaseExceptionGroup) [(excDataOf w self).egMessage.getD .none, excs] [] w) ∧
  (∀ (rt : Rt) (m : String) (excs : Val) (w : World), createExceptionGroup rt m excs w =
    rt.call (.obj B.BaseExceptionGroup) [.str m, excs] [] w)

theorem egCreatedThroughClass_proven : EgCreatedThroughClass := by
  refine ⟨?_, ?_⟩
  · intro rt self excs w
    rfl
  · intro rt m excs w
    rfl

/-- **`ExceptionGroup` derives from both.** `create_exception_group_class` gives the bases
`(BaseExceptionGroup, Exception)`, and the table row has them in that order. -/
def ExceptionGroupBases : Prop :=
  exceptionGroupBases = [B.BaseExceptionGroup, B.Exception] ∧
  (rowMro 100 B.ExceptionGroup).contains B.Exception = true ∧
  (rowMro 100 B.ExceptionGroup).contains B.BaseExceptionGroup = true

theorem exceptionGroupBases_proven : ExceptionGroupBases := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

/-- **`PyUnicode*Error_SetReason` and `GetReason` agree**, and `GetEncoding`, `GetObject` and
`GetReason` return the attribute once the type and attribute checks pass. -/
def UnicodeCapiAttributes : Prop :=
  (∀ (k : UKind) (self : Val) (w : World), isSubtype w (typeOf w self) B.UnicodeError = false →
    pyUnicodeErrorGetReason k self w =
      .err (.exc B.TypeError s!"expecting a {k.name} object, got {typeFQN w (typeOf w self)}" none) w) ∧
  (∀ (k : UKind) (a : Addr) (d : ExcData) (r : String) (w w' : World), IsExc w a d →
    pyUnicodeErrorSetReason k (.obj a) r w = .ok () w' →
    memGet (excDataOf w' (.obj a)) "reason" = some (.str r)) ∧
  (∀ (k : UKind) (self : Val) (w : World), isSubtype w (typeOf w self) B.UnicodeError = false →
    pyUnicodeErrorGetEncoding k self w =
      .err (.exc B.TypeError s!"expecting a {k.name} object, got {typeFQN w (typeOf w self)}" none) w) ∧
  (∀ (k : UKind) (self : Val) (w : World), isSubtype w (typeOf w self) B.UnicodeError = false →
    pyUnicodeErrorGetObject k self w =
      .err (.exc B.TypeError s!"expecting a {k.name} object, got {typeFQN w (typeOf w self)}" none) w)

theorem unicodeCapiAttributes_proven : UnicodeCapiAttributes := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k self w h
    simp [pyUnicodeErrorGetReason, checkUnicodeErrorType, h, typeErr, raiseC]
  · intro k a d r w w' hx h
    simp only [pyUnicodeErrorSetReason, M.bind_app] at h
    cases hc : checkUnicodeErrorType (.obj a) k.name w with
    | err e w1 => simp [hc] at h
    | ok u w1 =>
      have hw := checkUnicodeErrorType_world _ _ _ _ _ hc
      subst hw
      simp only [hc, unicodeErrorSetReasonImpl, excUpdate_app] at h
      simp at h
      subst h
      rw [excUpdW_data hx]
      exact memGet_memSet_same _ _ _
  · intro k self w h
    simp [pyUnicodeErrorGetEncoding, checkUnicodeErrorType, h, typeErr, raiseC]
  · intro k self w h
    simp [pyUnicodeErrorGetObject, checkUnicodeErrorType, h, typeErr, raiseC]

/-- **The creators call the class with the formatted arguments**, so the constructor's checks
apply to them. -/
def UnicodeCreateCallsClass : Prop :=
  (∀ (rt : Rt) (o : Val) (s e : Int) (r : String) (w : World),
    pyUnicodeTranslateErrorCreate rt o s e r w =
      rt.call (.obj B.UnicodeTranslateError) [o, .int s, .int e, .str r] [] w) ∧
  (∀ (rt : Rt) (enc : String) (b : List Nat) (s e : Int) (r : String) (w : World),
    pyUnicodeDecodeErrorCreate rt enc b s e r w =
      rt.call (.obj B.UnicodeDecodeError)
        [.str enc, .obj w.heap.size, .int s, .int e, .str r] []
        { w with heap := w.heap.push (.val { cls := B.bytes, body := .bytes b }) })

theorem unicodeCreateCallsClass_proven : UnicodeCreateCallsClass := by
  refine ⟨?_, ?_⟩
  · intro rt o s e r w
    rfl
  · intro rt enc b s e r w
    rfl

end PyLean.TypeObj
