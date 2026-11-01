import PyLean.TypeObj.ExcCore

/-!
`BaseExceptionGroup`: `Objects/exceptions.c:878-1789`. Construction, `str`/`repr`, `derive`,
`exceptiongroup_subset`, the split recursion, and `_PyExc_PrepReraiseStar`.

The recursion of `exceptiongroup_split_recursive` is `splitRecursive`, one level of it being
`splitKids` over `eg->excs`. `splitKids` is parametric in the recursive call so that the
proofs in `ExcProps` can induct on the fuel with one lemma about the list.
-/

namespace PyLean.TypeObj

/-- `Item %zd of second argument (exceptions) is not an exception` and the
`nested_base_exceptions` flag, `Objects/exceptions.c:937-957`. -/
def egCheckItems (rt : Rt) : Nat → Bool → List Val → M Bool
  | _, nested, [] => pure nested
  | i, nested, exc :: rest => do
    let w ← getW
    unless excInstanceCheck w exc do
      valueErr s!"Item {i} of second argument (exceptions) is not an exception"
    let nonbase ← excIsInstanceOf rt exc B.Exception
    egCheckItems rt (i + 1) (nested || !nonbase) rest

/-- The class of the new group, `Objects/exceptions.c:959-989`. -/
def egChooseClass (t : Addr) (nested : Bool) : M Addr := do
  let w ← getW
  if t == B.ExceptionGroup then
    if nested then typeErr "Cannot nest BaseExceptions in an ExceptionGroup"
    else pure t
  else if t == B.BaseExceptionGroup then
    pure (if nested then t else B.ExceptionGroup)
  else if nested then
    if isSubtype w t B.Exception then
      typeErr s!"Cannot nest BaseExceptions in '{trunc 200 (tpName w t)}'"
    else pure t
  else pure t

/-- `BaseExceptionGroup_new`, `Objects/exceptions.c:896-996`: everything before the object is
made. The result is the message, the items, `exceptions_str` and the class. -/
def egNewParse (rt : Rt) (t : Addr) (args : List Val) :
    M (Val × List Val × Option String × Addr) := do
  let fname := "BaseExceptionGroup.__new__"
  argCount (some fname) 2 2 args.length
  let message := args.headD .none
  let exceptions := (args.drop 1).headD .none
  argU (some fname) 1 message
  let w ← getW
  unless excSeqCheck w exceptions do
    typeErr "second argument (exceptions) must be a sequence"
  let isListOrTuple := (listOf w exceptions).isSome || (tupleOf w exceptions).isSome
  let excsStr ← if isListOrTuple then pure none else some <$> rt.repr exceptions
  let excs ← excSeqTuple rt exceptions
  if excs.isEmpty then
    valueErr "second argument (exceptions) must be a non-empty sequence"
  let nested ← egCheckItems rt 0 false excs
  let cls ← egChooseClass t nested
  pure (message, excs, excsStr, cls)

/-- `BaseExceptionGroup_new`, `Objects/exceptions.c:886`. -/
def baseExceptionGroupNew (rt : Rt) (t : Addr) (args : List Val) : M Val := do
  let (message, excs, excsStr, cls) ← egNewParse rt t args
  alloc cls (.exc { args := args, egMessage := some message, egExceptions := excs,
                    egExcsStr := excsStr })

/-- `_PyExc_CreateExceptionGroup`, `Objects/exceptions.c:1014`. -/
def createExceptionGroup (rt : Rt) (msg : String) (excs : Val) : M Val :=
  rt.call (.obj B.BaseExceptionGroup) [.str msg, excs] []

/-- `BaseExceptionGroup_init`, `Objects/exceptions.c:1031`. -/
def baseExceptionGroupInit (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  let w ← getW
  argNoKeywords (typeName w self) kw
  baseExceptionInit self args kw

/-- `BaseExceptionGroup_str`, `Objects/exceptions.c:1071`. -/
def baseExceptionGroupStr (rt : Rt) (self : Val) : M Val := do
  let w ← getW
  let d := excDataOf w self
  let m ← rt.str (d.egMessage.getD .none)
  let n := d.egExceptions.length
  pure (.str s!"{m} ({n} sub-exception{if n > 1 then "s" else ""})")

/-- Does `BaseExceptionGroup_repr` read `args[1]` out of bounds? `self->args` is writable
and `__init__` replaces it, but `:1103` indexes it with `PyTuple_GET_ITEM`. -/
def egReprOutOfBounds (d : ExcData) : Bool :=
  d.egExcsStr.isNone && decide (d.args.length < 2)

/-- `BaseExceptionGroup_repr`, `Objects/exceptions.c:1085`. In 3.14.7 an out-of-bounds read
at `:1103` is undefined behaviour (a crash in practice), which is not a Python outcome, so
the model stops there: see `egReprOutOfBounds`. -/
def baseExceptionGroupRepr (rt : Rt) (self : Val) : M Val := do
  let w ← getW
  let d := excDataOf w self
  let exStr ← match d.egExcsStr with
    | some s => pure s
    | none =>
      if egReprOutOfBounds d then raise .fuel
      else
        if (listOf w (d.args.getD 1 .none)).isSome then
          let l ← alloc B.list (.list d.egExceptions)
          rt.repr l
        else rt.repr (.tuple d.egExceptions)
  let w ← getW
  let m ← rt.repr (d.egMessage.getD .none)
  pure (.str s!"{pyTypeName w (typeOf w self)}({m}, {exStr})")

/-- `BaseExceptionGroup_derive_impl`, `Objects/exceptions.c:1140`. -/
def baseExceptionGroupDerive (rt : Rt) (self excs : Val) : M Val := do
  let w ← getW
  rt.call (.obj B.BaseExceptionGroup) [(excDataOf w self).egMessage.getD .none, excs] []

/-- `PyObject_CallMethod(obj, name, "(O)", arg)`, `Objects/call.c:630`. -/
def callMethodO (rt : Rt) (obj : Val) (name : Name) (arg : Val) : M Val := do
  let f ← rt.getAttr obj name
  let w ← getW
  unless excCallableCheck w f do
    typeErr s!"attribute of type '{trunc 200 (typeName w f)}' is not callable"
  rt.call f [arg] []

/-- The metadata part of `exceptiongroup_subset`, `Objects/exceptions.c:1191-1200`. The cause
goes through `PyException_SetCause`, which also sets `suppress_context`. -/
def subsetCopyMeta (orig eg : Val) : M Unit := do
  let w ← getW
  match pyExceptionGetTraceback w orig with
  | some tb => baseExceptionTracebackSet eg (some tb)
  | none => pure ()
  let w ← getW
  pyExceptionSetContext eg (pyExceptionGetContext w orig)
  pyExceptionSetCause eg (pyExceptionGetCause w orig)

/-- `exceptiongroup_subset`, `Objects/exceptions.c:1155`. `excs` is the list being wrapped;
`PySequence_Size` of an exact list cannot fail. `none` is `*result == NULL`. -/
def exceptiongroupSubset (rt : Rt) (orig : Val) (excs : List Val) : M (Option Val) := do
  if excs.isEmpty then return none
  let lst ← alloc B.list (.list excs)
  let eg ← callMethodO rt orig "derive" lst
  let w ← getW
  unless egCheck w eg do
    typeErr "derive must return an instance of BaseExceptionGroup"
  subsetCopyMeta orig eg
  match ← rt.getOptionalAttr orig "__notes__" with
  | none => pure (some eg)
  | some notes =>
    let w ← getW
    if excSeqCheck w notes then
      let c ← excSeqList rt notes
      let cv ← alloc B.list (.list c)
      rt.setAttr eg "__notes__" (some cv)
      pure (some eg)
    else pure (some eg)

/-- `_exceptiongroup_split_matcher_type`, `Objects/exceptions.c:1236`. The set of leaf ids is
the list of the leaves themselves. -/
inductive MatcherType where
  | byType
  | byPredicate
  | instanceIds (ids : List Val)

/-- `get_matcher_type`, `Objects/exceptions.c:1249`. -/
def getMatcherType (value : Val) : M MatcherType := do
  let w ← getW
  if excCallableCheck w value && !typeCheck w value then return .byPredicate
  if excClassCheck w value then return .byType
  match value with
  | .tuple xs =>
    if xs.all (excClassCheck w) then return .byType
  | _ => pure ()
  typeErr "expected an exception type, a tuple of exception types, or a callable (other than a class)"

/-- `PyErr_GivenExceptionMatches`, `Python/errors.c:332`, for one class `exc`. -/
def givenMatchesClass (w : World) (err exc : Val) : Bool :=
  let e : Val := if excInstanceCheck w err then .obj (typeOf w err) else err
  match asType w e, asType w exc with
  | some a, some b =>
    if isSubtype w a B.BaseException && isSubtype w b B.BaseException then isSubtype w a b
    else e.is exc
  | _, _ => e.is exc

/-- `PyErr_GivenExceptionMatches`. `get_matcher_type` admits only a class or a tuple of
classes here, so the tuple recursion is one level deep. -/
def givenExceptionMatches (w : World) (err exc : Val) : Bool :=
  match tupleOf w exc with
  | some xs => xs.any (givenMatchesClass w err)
  | none => givenMatchesClass w err exc

/-- `exceptiongroup_split_check_match`, `Objects/exceptions.c:1283`. -/
def splitCheckMatch (rt : Rt) (exc : Val) (mt : MatcherType) (mv : Val) : M Bool := do
  match mt with
  | .byType =>
    let w ← getW
    pure (givenExceptionMatches w exc mv)
  | .byPredicate =>
    let r ← rt.call mv [exc] []
    rt.isTrue r
  | .instanceIds ids =>
    let w ← getW
    if egCheck w exc then pure false else pure (ids.any (Val.is · exc))

/-- The loop over `eg->excs`, `Objects/exceptions.c:1378-1411`. -/
def splitKids (rec : Val → M (Option Val × Option Val)) :
    List Val → List Val → List Val → M (List Val × List Val)
  | [], ml, rl => pure (ml, rl)
  | e :: es, ml, rl => do
    let (m, r) ← rec e
    splitKids rec es (ml ++ m.toList) (rl ++ r.toList)

/-- Recursion bound: `_Py_EnterRecursiveCall` raises `RecursionError` long before it. -/
def excRecFuel : Nat := 2000

/-- `exceptiongroup_split_recursive`, `Objects/exceptions.c:1326`. The result is
`(result->match, result->rest)`. -/
def splitRecursive (rt : Rt) (mt : MatcherType) (mv : Val) (constructRest : Bool) :
    Nat → Val → M (Option Val × Option Val)
  | 0, _ => raise .fuel
  | fuel + 1, exc => do
    let isMatch ← splitCheckMatch rt exc mt mv
    if isMatch then return (some exc, none)
    let w ← getW
    if !egCheck w exc then
      return (none, if constructRest then some exc else none)
    let (ml, rl) ← splitKids (splitRecursive rt mt mv constructRest fuel)
      (excDataOf w exc).egExceptions [] []
    let m ← exceptiongroupSubset rt exc ml
    if constructRest then
      let r ← exceptiongroupSubset rt exc rl
      pure (m, r)
    else pure (m, none)

/-- `BaseExceptionGroup_split_impl`, `Objects/exceptions.c:1444`. -/
def baseExceptionGroupSplit (rt : Rt) (self mv : Val) : M Val := do
  let mt ← getMatcherType mv
  let (m, r) ← splitRecursive rt mt mv true excRecFuel self
  pure (.tuple [m.getD .none, r.getD .none])

/-- `BaseExceptionGroup_subgroup_impl`, `Objects/exceptions.c:1479`. -/
def baseExceptionGroupSubgroup (rt : Rt) (self mv : Val) : M Val := do
  let mt ← getMatcherType mv
  let (m, _) ← splitRecursive rt mt mv false excRecFuel self
  pure (m.getD .none)

/-- `collect_exception_group_leaf_ids`, `Objects/exceptions.c:1505`. -/
def collectLeafIds (w : World) : Nat → Val → List Val
  | 0, _ => []
  | fuel + 1, exc =>
    if exc.is .none then []
    else if !egCheck w exc then [exc]
    else
      let rec go : List Val → List Val
        | [] => []
        | e :: es => collectLeafIds w fuel e ++ go es
      go (excDataOf w exc).egExceptions

/-- `exception_group_projection`, `Objects/exceptions.c:1549`. -/
def exceptionGroupProjection (rt : Rt) (eg : Val) (keep : List Val) : M Val := do
  let w ← getW
  let ids := keep.flatMap (collectLeafIds w excRecFuel)
  let (m, _) ← splitRecursive rt (.instanceIds ids) .none false excRecFuel eg
  pure (m.getD .none)

/-- Pointer equality of two optional fields. -/
def sameRef : Option Val → Option Val → Bool
  | none, none => true
  | some a, some b => a.is b
  | _, _ => false

/-- `is_same_exception_metadata`, `Objects/exceptions.c:1587`. The `notes` it compares is the
unused C field, not `__notes__`. -/
def isSameExceptionMetadata (w : World) (exc1 exc2 : Val) : Bool :=
  let e1 := excDataOf w exc1
  let e2 := excDataOf w exc2
  sameRef e1.notes e2.notes && e1.traceback.is e2.traceback &&
    sameRef e1.cause e2.cause && sameRef e1.context e2.context

/-- `_PyExc_PrepReraiseStar`, `Objects/exceptions.c:1618`. -/
def excPrepReraiseStar (rt : Rt) (orig : Val) (excs : List Val) : M Val := do
  if excs.isEmpty then return .none
  let w ← getW
  if !egCheck w orig then return excs.headD .none
  let live := excs.filter (fun e => !e.is .none)
  let reraised := live.filter (fun e => isSameExceptionMetadata w e orig)
  let raised := live.filter (fun e => !isSameExceptionMetadata w e orig)
  let reraisedEg ← exceptionGroupProjection rt orig reraised
  if raised.isEmpty then return reraisedEg
  let l := if reraisedEg.is .none then raised else raised ++ [reraisedEg]
  if l.length > 1 then
    let lv ← alloc B.list (.list l)
    createExceptionGroup rt "" lv
  else pure (l.headD .none)

/-- The index of the first item that is neither an exception nor `None`. -/
def firstNonExc (w : World) : Nat → List Val → Option Nat
  | _, [] => none
  | i, e :: es =>
    if excInstanceCheck w e || e.is .none then firstNonExc w (i + 1) es else some i

/-- `PyUnstable_Exc_PrepReraiseStar`, `Objects/exceptions.c:1711`. -/
def pyUnstableExcPrepReraiseStar (rt : Rt) (orig excs : Val) : M Val := do
  let w ← getW
  unless excInstanceCheck w orig do typeErr "orig must be an exception instance"
  match listOf w excs with
  | none => typeErr "excs must be a list of exception instances"
  | some xs =>
    match firstNonExc w 0 xs with
    | some i => typeErr s!"item {i} of excs is not an exception"
    | none =>
      match pyExceptionGetTraceback w orig with
      | none => valueErr "orig must be a raised exception"
      | some _ => excPrepReraiseStar rt orig xs

/-- `create_exception_group_class`, `Objects/exceptions.c:1774`: the bases, in order. `rowBases`
and `rowMro` of `Builtins.lean` use the same pair. -/
def exceptionGroupBases : List Addr := [B.BaseExceptionGroup, B.Exception]

end PyLean.TypeObj
