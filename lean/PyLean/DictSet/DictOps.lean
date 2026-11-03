import PyLean.DictSet.Table

/-!
The operations of `Objects/dictobject.c` on top of the table: the C API family,
the Python methods, `update`/`merge`, `fromkeys`, comparison, repr, iterators.
Line numbers refer to `Objects/dictobject.c`. Functions that differ from a sibling only
in locking or reference counting share one definition; its docstring names them.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type}

/-- `PyErr_BadInternalCall()`: `SystemError` with `file:line` in the message. -/
def badInternalCall : PyExc := badInternalCallT

section
variable [DecidableEq K] (P : Proto K (PyDict K V))

/-- `dict_getitem` (:2389-2431), behind `PyDict_GetItem` and `PyDict_GetItemString`:
every error is swallowed. -/
def dictGetitemSuppress (isDict : Bool) (key : K) : DM K V (Option V) :=
  if !isDict then pure none else fun mp0 =>
  let mp := P.hashEff key mp0
  (match P.hash key with
  | .error _ => pure none
  | .ok hash =>
    M.tryCatch (do
      let r ← dictLookup P key hash
      return r.2) (fun _ => pure none) : DM K V (Option V)) mp

/-- `dict_getitem` with what it reports: `(value, unraisable)`, the second being the exception
passed to `PyErr_FormatUnraisable` (:2399, :2425). An exception from the lookup that
`PyErr_GivenExceptionMatches(exc2, PyExc_KeyError)` accepts, a `KeyError` or an instance of a
subclass, is dropped without a report (:2424). `isKeyError` is that test, a property of the
exception's class. -/
def dictGetitemFull (isKeyError : PyExc → Bool) (isDict : Bool) (key : K) :
    DM K V (Option V × Option PyExc) :=
  if !isDict then pure (none, none) else fun mp0 =>
  let mp1 := P.hashEff key mp0
  (match P.hash key with
  | .error e => pure (none, some e)
  | .ok hash => fun mp =>
    match dictLookup P key hash mp with
    | (.ok r, s) => (.ok (r.2, none), s)
    | (.error e, s) =>
      if isKeyError e then (.ok (none, none), s) else (.ok (none, some e), s) :
    DM K V (Option V × Option PyExc)) mp1

/-- `PyErr_GivenExceptionMatches(e, PyExc_KeyError)` for the exceptions the models raise
themselves. -/
def isKeyErrorExact : PyExc → Bool
  | .keyError _ => true
  | _ => false

/-- `_PyDict_GetItem_KnownHash` (:2489-2509). -/
def dictGetItemKnownHash (isDict : Bool) (key : K) (hash : Int) : DM K V (Option V) := do
  if !isDict then M.throw badInternalCall
  let r ← dictLookup P key hash
  return r.2

/-- `_PyDict_GetItemRef_KnownHash_LockHeld` (:2515-2532), `_PyDict_GetItemRef_KnownHash`
(:2538-2562): `some v` is return value 1, `none` is 0, an exception is -1. -/
def dictGetItemRefKnownHash (key : K) (hash : Int) : DM K V (Option V) := do
  let r ← dictLookup P key hash
  match r.2 with
  | none => return none
  | some v => return some v

/-- `PyDict_GetItemRef` (:2564-2581). -/
def pyDictGetItemRef (isDict : Bool) (key : K) : DM K V (Option V) := do
  if !isDict then M.throw badInternalCall
  let hash ← hashKey P key
  dictGetItemRefKnownHash P key hash

/-- `_PyDict_GetItemRef_Unicode_LockHeld` (:2583-2609). -/
def dictGetItemRefUnicode (key : K) : DM K V (Option V) := do
  let hash ← hashKey P key
  let r ← dictLookup P key hash
  match r.2 with
  | none => return none
  | some v => return some v

/-- `PyDict_GetItemWithError` (:2615-2641). -/
def pyDictGetItemWithError (isDict : Bool) (key : K) : DM K V (Option V) := do
  if !isDict then M.throw badInternalCall
  let hash ← hashKey P key
  let r ← dictLookup P key hash
  return r.2

/-- `_PyDict_GetItemWithError` (:2643-2652): `tp_hash`, then the known-hash lookup. -/
def dictGetItemWithErrorUnchecked (key : K) : DM K V (Option V) := do
  let hash ← hashCall P key
  dictGetItemKnownHash P true key hash

/-- `_PyDict_LookupIndex` (:2462-2483). -/
def dictLookupIndex (key : K) : DM K V Int := do
  let hash ← hashKey P key
  let r ← dictLookup P key hash
  return r.1

/-- Key made from a C string (`PyUnicode_FromString`, which may fail), then an action:
`_PyDict_GetItemStringWithError` (:2654-2665), `PyDict_GetItemStringRef` (:5523-5534),
`PyDict_DelItemString` (:5551-5562), `PyDict_SetItemString` (:5536-5549),
`PyDict_ContainsString` (:5258-5268). -/
def withCKey {α : Type} (mk : Py K) (act : K → DM K V α) : DM K V α := do
  let k ← M.lift mk
  act k

/-- `PyDict_GetItemString` (:5505-5521): both failures are swallowed. -/
def pyDictGetItemString (isDict : Bool) (mk : Py K) : DM K V (Option V) :=
  match mk with
  | .error _ => pure none
  | .ok k => dictGetitemSuppress P isDict k

/-- `_PyDict_Contains_KnownHash` (:5270-5292). -/
def dictContainsKnownHash (key : K) (hash : Int) : DM K V Bool := do
  let r ← dictLookup P key hash
  return r.1 != DKIX_EMPTY && r.2.isSome

/-- `dict_contains` (:5234-5244), behind `dict.__contains__` (:4725-4737). -/
def pyDictContains (key : K) : DM K V Bool := do
  let hash ← hashKey P key
  dictContainsKnownHash P key hash

/-- `PyDict_Contains` (:5247-5256): the test `dict_contains` does not make. -/
def pyDictContainsChecked (isAny : Bool) (key : K) : DM K V Bool :=
  if isAny then pyDictContains P key else M.throw badInternalCall

/-- The branch of `_PyDict_SubscriptKnownHash` for a key that is not there (:3765-3780). `missing` is `none` for
an exact dict. Otherwise it is `_PyObject_LookupSpecial(mp, "__missing__")`, which may raise, with
the method it finds; both may change the dict. -/
def subscriptMissing (missing : Option (DM K V (Option (K → DM K V V)))) (key : K) : DM K V V :=
  match missing with
  | none => M.throw (keyErr P key)
  | some look => do
    match ← look with
    | some f => f key
    | none => M.throw (keyErr P key)

/-- `_PyDict_Subscript` (:3785-3794), `_PyDict_SubscriptKnownHash` (:3755-3783). -/
def dictSubscript (missing : Option (DM K V (Option (K → DM K V V)))) (key : K) : DM K V V := do
  let hash ← hashKey P key
  let r ← dictLookup P key hash
  match r.2 with
  | some v => if r.1 == DKIX_EMPTY then subscriptMissing P missing key else return v
  | none => subscriptMissing P missing key

/-- `_PyDict_StoreSubscript` (:3796-3803). -/
def dictAssSub (key : K) (w : Option V) : DM K V Unit :=
  match w with
  | none => dictDelItem P key
  | some v => dictSetItem P key v

/-- `dict.get` (`dict_get_impl`, :4749-4769). -/
def dictGet (key : K) (dflt : V) : DM K V V := do
  let hash ← hashKey P key
  let r ← dictLookup P key hash
  match r.2 with
  | some v => return (if r.1 == DKIX_EMPTY then dflt else v)
  | none => return dflt

/-- `delitemif_lock_held` (:2981-3017) and `_PyDict_DelItemIf`: `pred` may raise. -/
def dictDelItemIf (pred : V → Py Bool) (key : K) : DM K V Bool := do
  let hash ← hashCall P key
  let r ← dictLookup P key hash
  match r.2 with
  | none => return false
  | some old =>
    if r.1 == DKIX_EMPTY then return false
    let res ← M.lift (pred old)
    if res then
      delitemCommon hash r.1.toNat
      return true
    else return false

/-- `_PyDict_Pop_KnownHash` (:3232-3275): `some v` is 1, `none` is 0. -/
def dictPopKnownHash (key : K) (hash : Int) : DM K V (Option V) := fun mp =>
  if mp.used == 0 then (.ok none, mp) else
  match dictLookup P key hash mp with
  | (.error e, s) => (.error e, s)
  | (.ok (ix, old), s) =>
    match old with
    | none => (.ok none, s)
    | some v =>
      if ix == DKIX_EMPTY then (.ok none, s)
      else
        match delitemCommon hash ix.toNat s with
        | (.ok _, s') => (.ok (some v), s')
        | (.error e, s') => (.error e, s')

/-- `pop_lock_held` (:3277-3311), `PyDict_Pop` (:3313-3322). An empty dict answers before
the key is hashed. -/
def pyDictPop (isAny : Bool) (key : K) : DM K V (Option V) := fun mp =>
  if !isAny then (.error badInternalCall, mp)
  else if mp.frozen then (.error (frozendictNoSupport "deletion"), mp)
  else if mp.used == 0 then (.ok none, mp)
  else
    let mp := P.hashEff key mp
    match P.hash key with
    | .error e => (.error (dictUnhashableType P mp.frozen key e), mp)
    | .ok hash => dictPopKnownHash P key hash mp

/-- `dict_pop_default` (:3342-3354), `_PyDict_Pop`, `dict.pop`. -/
def dictPopDefault (key : K) (dflt : Option V) : DM K V V := do
  match ← pyDictPop P true key with
  | some v => return v
  | none =>
    match dflt with
    | some d => return d
    | none => M.throw (keyErr P key)

/-- `dict_setdefault_ref_lock_held` (:4771-4871): the status and `*result`. Status 1 is
"already present", as in C. `result`/`incref` model the `result != NULL` and
`incref_result` arguments.

The branch at :4843 tests `ix == DKIX_EMPTY` only. For a split table and a key that is
not an exact `str`, `_Py_dict_lookup` can return `ix >= 0` with `*value_addr == NULL`
(key in the shared keys, no value in this dict); the code then runs on to :4865-4869
with `value == NULL`, and `Py_NewRef(NULL)` dies. -/
def dictSetdefaultRef (key : K) (dflt : V) (result incref : Bool) : DM K V (Nat × Option V) := do
  let hash ← hashKey P key
  let mp ← M.get
  if mp.body.isEmptyKeys then
    insertToEmptyDict P key hash dflt
    return (0, some dflt)
  let continueAt : Int → Option V → DM K V (Nat × Option V) := fun ix value => do
    if ix == DKIX_EMPTY then
      insertCombinedDict P.toKeyOps hash key dflt
      M.modify fun mp => { mp with used := mp.used + 1 }
      return (0, some dflt)
    match value with
    | some v => return (1, some v)
    | none =>
      -- assert(value != NULL) is compiled out
      if result && incref then M.throw (crash "dict_setdefault_ref_lock_held: Py_NewRef(NULL)")
      return (1, none)
  match mp.body with
  | .split keys vals =>
    if P.isStr key then
      let (ix, keys') ← M.lift (insertSplitKey P keys key hash)
      M.put { mp with body := .split keys' vals }
      if ix != DKIX_EMPTY then
        match vals.get ix.toNat with
        | some v => return (1, some v)
        | none =>
          insertSplitValue dflt ix.toNat
          return (0, some dflt)
      continueAt ix none
    else
      let r ← dictLookup P key hash
      continueAt r.1 r.2
  | .combined _ =>
    let r ← dictLookup P key hash
    continueAt r.1 r.2

/-- `dict_setdefault_ref_lock_held` with its `PyDict_Check` (:4775-4786). -/
def dictSetdefaultRefChecked (isAny : Bool) (key : K) (dflt : V) (result incref : Bool) :
    DM K V (Nat × Option V) := fun mp =>
  if !isAny then (.error badInternalCall, mp)
  else if mp.frozen then (.error (frozendictNoSupport "assignment"), mp)
  else dictSetdefaultRef P key dflt result incref mp

/-- `dict.setdefault` (`dict_setdefault_impl`, :4907-4915), `PyDict_SetDefaultRef`
(:4873-4882). -/
def dictSetdefault (key : K) (dflt : V) : DM K V V := do
  let r ← dictSetdefaultRef P key dflt true true
  match r.2 with
  | some v => return v
  | none => M.unreachable

/-- `PyDict_SetDefault` (:4884-4892): no `Py_NewRef`, so a NULL result is simply
returned; `none` is that NULL. -/
def pyDictSetDefault (key : K) (dflt : V) : DM K V (Option V) := do
  let r ← dictSetdefaultRef P key dflt true false
  return r.2

end

/-- The backwards scan of `dict_popitem_impl` (:5003-5006, @3.14.7:4652-4655): the last live
entry below `i`. -/
def lastLive (es : List (Option (Ent K V))) : Nat → Option (Nat × Ent K V)
  | 0 => none
  | i + 1 =>
    match es[i]? with
    | some (some e) => some (i, e)
    | _ => lastLive es i

/-- The part of `dict_popitem_impl` after the table is known to be combined (:4996-5042). -/
def popLast (k : Keys K V) (mp : PyDict K V) : Py (K × V) × PyDict K V :=
  match lastLive k.entries k.nentries with
  | none => (.error .modelFuel, mp)
  | some (i, e) =>
    match lookdictIndex k e.hash i with
    | .error x => (.error x, mp)
    | .ok j =>
      if j < 0 then (.error .modelFuel, mp)
      else
        (.ok (e.key, e.value), { mp with
          used := mp.used - 1
          body := .combined { (k.setIndex j.toNat DKIX_DUMMY) with
            entries := k.entries.take i
            version := 0 } })

/-- `dict_popitem_impl` (:4963-5045). -/
def dictPopitem : DM K V (K × V) := fun mp =>
  if mp.used == 0 then (.error (.keyError "'popitem(): dictionary is empty'"), mp)
  else
    match mp.body with
    | .combined k => popLast k mp
    | .split _ _ =>
      -- Convert split table to combined table.
      match dictResize mp.body.log2Size true mp with
      | (.error e, s) => (.error e, s)
      | (.ok _, s) =>
        match s.body with
        | .combined k => popLast k s
        | .split _ _ => (.error .modelFuel, s)

/-- `clear_embedded_values` (:3065-3078). -/
def clearEmbeddedValues (v : Values V) (nentries : Nat) : Values V :=
  { v with
    values := v.values.zipIdx.map (fun p => if p.2 < nentries then none else p.1)
    order := [] }

/-- `clear_lock_held` (:3080-3124), behind `PyDict_Clear`, `_PyDict_Clear_LockHeld`,
`dict.clear`. -/
def dictClear (mp : PyDict K V) : PyDict K V :=
  if mp.body.isEmptyKeys then mp
  else
    match mp.body with
    | .combined _ => { mp with used := 0, body := .combined emptyKeys }
    | .split k v =>
      if v.embedded then
        { mp with used := 0, body := .split k (clearEmbeddedValues v k.nentries) }
      else
        { mp with used := 0, body := .combined emptyKeys }

/-- `dict_dealloc` (:3605-3638). The `PyDict_EVENT_DEALLOCATED` watchers run on the live dict (:3609)
and may change it and keep a reference. `watch` is that run: whether the dict was resurrected, and the
dict it left. Then `_PyObject_ResurrectEnd` (:3610) ends the function, leaving the dict as it is; the
rest only drops references. The result is the dict that lives on, if any. -/
def dictDealloc (watch : PyDict K V → Bool × PyDict K V) (mp : PyDict K V) : Option (PyDict K V) :=
  match watch mp with
  | (true, s) => some s
  | (false, _) => none

/-- `clear_lock_held` returns at once on something that is not a dict (:3083-3085). -/
def dictClearChecked (isDict : Bool) (mp : PyDict K V) : PyDict K V :=
  if isDict then dictClear mp else mp

/-- `copy_values` (:4411-4430). -/
def copyValues (v : Values V) : Values V :=
  { v with embedded := false }

/-- `clone_combined_dict_keys` (:987-1050): a bitwise copy of the keys object, but for `dk_version`
(:1009-1011). -/
def cloneCombinedDictKeys (id : Nat) (k : Keys K V) : Keys K V :=
  { k with ident := id, version := 0 }

section Merge
variable [DecidableEq K] (P : Proto K (PyDict K V))

/-- Return value `-2` of `dict_merge`, with `*dupkey` set, which is no exception: the int status
travels in the error channel so that every loop stops as it does in C, and
`_PyEval_FormatKwargsError` (`Python/ceval.c:3415`) makes the `TypeError`. `dupkey` is non-`NULL` only
from `_PyDict_MergeUniq`, the one caller with `override` 2, and every other caller passes `NULL` with
`override` 0 or 1, so `override != 0` here stands for `dupkey != NULL` at :4236. -/
def mergeDup (key : K) : DM K V Unit := fun mp =>
  (.error mergeDupExc, { mp with dupkey := some key })

/-- The body of the loop of `dict_dict_merge` (:4227-4243). -/
def mergeStep (override : Nat) (key : K) (hash : Int) (value : V) : DM K V Unit :=
  if override == 1 then
    insertDict P key hash value
  else do
    let err ← dictContainsKnownHash P key hash
    if !err then
      insertDict P key hash value
    else if override != 0 then
      mergeDup key

/-- The message of :4250-4251. -/
def mergeMutated : PyExc := runtimeError "dict mutated during update"

/-- The loop of `dict_dict_merge` (:4223-4254). `_PyDict_Next` reads the source as it stands
now, so what a callback did to it shows at the next step; the test at :4249 comes after the
error test at :4246, and compares only the number of items. Running out of `fuel` is a limit
of the model, never a Python outcome. -/
def mergeLive (override origSize : Nat) : Nat → Int → DM K V Unit
  | 0, _ => M.throw .modelFuel
  | fuel + 1, pos => fun mp =>
    match mp.peer with
    | none => (.error .modelFuel, mp)
    | some src =>
      match dictNext src.toDict pos with
      | none => (.ok (), mp)
      | some (pos', key, value, hash) =>
        match mergeStep P override key hash value mp with
        | (.error e, s) => (.error e, s)
        | (.ok _, s) =>
          match s.peer with
          | none => (.error .modelFuel, s)
          | some src' =>
            if origSize != src'.used then (.error mergeMutated, s)
            else mergeLive override origSize fuel pos' s

/-- `mergeLive` on a source that stays put: the list of its items. The proofs use this form. -/
def mergeLoop (override : Nat) : List (K × V × Int) → DM K V Unit
  | [] => pure ()
  | (key, value, hash) :: rest => do
    mergeStep P override key hash value
    mergeLoop override rest

/-- More steps than a source of this shape can take. -/
def mergeFuel (other : PyDict K V) : Nat :=
  other.body.nentries + other.used + 2 ^ other.body.log2Size + 64

/-- The tail of `dict_dict_merge` (:4206-4255): one big resize, then the loop. From here on
`peer` holds the source, and the caller reads the source's final state from it. -/
def mergeRest (other : PyDict K V) (override : Nat) : DM K V Unit := fun mp =>
  match (if usableFraction (2 ^ mp.body.log2Size) < other.used then
           dictResize (estimateLog2Keysize (mp.used + other.used)) other.body.isUnicode mp
         else (.ok (), mp)) with
  | (.error e, s) => (.error e, s)
  | (.ok _, s) =>
    mergeLive P override other.used (mergeFuel other) 0 { s with peer := some other.toPeer }

/-- `dict_dict_merge` (:4169-4256). -/
def dictDictMerge (other : PyDict K V) (override : Nat) : DM K V Unit := fun mp =>
  if other.ident == mp.ident || other.used == 0 then (.ok (), mp)
  else if mp.used == 0 then
    -- `override = 1`: the target is empty, so the test is unnecessary (:4178-4183).
    match mp.body, other.body with
    | .combined _, .combined okeys =>
      if other.used == okeys.nentries &&
          (okeys.log2Size == PyDict_LOG_MINSIZE ||
            decide (usableFraction (okeys.size / 2) < other.used)) then
        (.ok (), { mp with
          nextId := mp.nextId + 1
          used := other.used
          body := .combined (cloneCombinedDictKeys mp.nextId okeys) })
      else mergeRest P other 1 mp
    | _, _ => mergeRest P other 1 mp
  else mergeRest P other override mp

/-- The right operand of `dict_merge` (:4258-4354). -/
inductive MergeArg (K V : Type) where
  /-- `PyAnyDict_Check(b) && Py_TYPE(b)->tp_iter == dict_iter`. -/
  | dict (d : PyDict K V)
  /-- Otherwise: `PyMapping_Keys(b)` and `PyObject_GetItem`. Both run Python code, so both may
  raise and may change the receiver. `PyMapping_Keys` hands back the object `keys()` returned when
  it is an exact list (`Objects/abstract.c:2439-2441`), so the list can grow or shrink while the
  loop runs: `keys` gives the iterator the loop runs over, as `PyObject_GetIter` and `PyIter_Next`
  (:4298, :4305) see it, step by step, after whatever the previous turn did. -/
  | mapping (keys : DM K V (ReIter (PyDict K V) K)) (getitem : K → DM K V V)

/-- The iterator over a list no callback touches. -/
def ReIter.ofKeys {σ : Type} (ks : List K) : ReIter σ K :=
  { steps := ks.map fun k => pure (some k) }

/-- The slow loop of `dict_merge` (:4305-4341). Each step is one `PyIter_Next` on the keys list: it
may raise, which ends the loop with that error (:4342-4346), and `none` is its end. -/
def mergeGenericLoop (getitem : K → DM K V V) (override : Nat) :
    List (DM K V (Option K)) → DM K V Unit
  | [] => pure ()
  | step :: rest => do
    match ← step with
    | none => pure ()
    | some key =>
      let skip ← (if override != 1 then do
        let status ← pyDictContains P key
        if status then
          if override == 0 then
            pure true
          else do
            mergeDup key
            pure true
        else pure false
      else pure false)
      if !skip then
        let value ← getitem key
        dictSetItem P key value
      mergeGenericLoop getitem override rest

/-- `dict_merge` (:4258-4354), behind `PyDict_Update` (override 1), `PyDict_Merge`
(`override != 0`) and `_PyDict_MergeUniq` (override 2). -/
def dictMerge (b : MergeArg K V) (override : Nat) : DM K V Unit :=
  match b with
  | .dict other => dictDictMerge P other override
  | .mapping keys getitem => do
    let it ← keys
    it.getIter
    mergeGenericLoop P getitem override it.steps

/-- The right operand of `dict_merge` as an object: whether it passes the test at :4268, what it
holds as a dict, and how the slow path reads it. -/
structure MergeObj (K V : Type) where
  isDict : Bool
  /-- `Py_TYPE(b)->tp_iter == dict_iter`. -/
  iterIsDict : Bool
  asDict : PyDict K V
  keys : DM K V (ReIter (PyDict K V) K)
  getitem : K → DM K V V

/-- The route `dict_merge` takes on it (:4268). -/
def MergeObj.route (b : MergeObj K V) : MergeArg K V :=
  if b.isDict && b.iterIsDict then .dict b.asDict else .mapping b.keys b.getitem

/-- `dict_merge_api` (:4356-4377), the entry test `dict_merge` itself gave up, and `dict_merge`
(:4258-4354). `dict_update_arg` and the copies call `dict_merge` directly. -/
def dictMergeChecked (aIsAny : Bool) (b : Option (MergeObj K V)) (override : Nat) :
    DM K V Unit := fun mp =>
  if !aIsAny then (.error badInternalCall, mp)
  else if mp.frozen then (.error (frozendictNoSupport "assignment"), mp)
  else
    match b with
    | some arg => dictMerge P arg.route override mp
    | none => (.error badInternalCall, mp)

/-- One element of the iterable given to `dict.update`, after `PySequence_Fast`. -/
inductive Seq2Item (K V : Type) where
  /-- `PySequence_Fast` raised `e`; `isTypeError` is `PyErr_ExceptionMatches(PyExc_TypeError)` of it
  (:4083), true for a `TypeError` and for an instance of a subclass. -/
  | notSeq (e : PyExc) (isTypeError : Bool)
  | wrongLen (n : Nat)
  | pair (k : K) (v : V)

/-- The note `merge_from_seq2_lock_held` adds to a `TypeError` from `PySequence_Fast` (:4083-4088). -/
def seq2Note (i : Nat) : String :=
  s!"Cannot convert dictionary update sequence element #{i} to a sequence"

/-- The loop of `merge_from_seq2_lock_held` (:4068-4126). Each step is one `PyIter_Next`: it
may raise and may change the receiver, and `none` is exhaustion. -/
def seq2Loop (override : Bool) : Nat → List (DM K V (Option (Seq2Item K V))) → DM K V Unit
  | _, [] => pure ()
  | i, step :: rest => do
    match ← step with
    | none => pure ()
    | some item =>
      match item with
      | .notSeq e isTE =>
        if isTE then M.modify fun mp => { mp with note := some (seq2Note i) }
        M.throw e
      | .wrongLen n =>
        M.throw (.valueError s!"dictionary update sequence element #{i} has length {n}; 2 is required")
      | .pair k v =>
        if override then
          dictSetItem P k v
        else
          let _ ← dictSetdefaultRef P k v false false
      seq2Loop override (i + 1) rest

/-- `merge_from_seq2_lock_held` (:4051-4138), `dict_merge_from_seq2` (:4140-4149). -/
def mergeFromSeq2 (seq2 : ReIter (PyDict K V) (Seq2Item K V)) (override : Bool) : DM K V Unit := do
  seq2.getIter
  seq2Loop P override 0 seq2.steps

/-- The argument of `dict.update`, `dict()`, `|=`. -/
inductive UpdateArg (K V : Type) where
  /-- `PyDict_CheckExact(arg)`. -/
  | exact (d : PyDict K V)
  /-- Anything else: `PyObject_HasAttrWithError(arg, "keys")`, then the mapping route or
  the sequence route. -/
  | other (hasKeys : DM K V Bool) (asMapping : MergeArg K V)
      (seq2 : ReIter (PyDict K V) (Seq2Item K V))

/-- `PyDict_MergeFromSeq2` (:4151-4167). -/
def pyDictMergeFromSeq2 (isAny : Bool) (seq2 : ReIter (PyDict K V) (Seq2Item K V)) (override : Bool) :
    DM K V Unit := fun mp =>
  if !isAny then (.error badInternalCall, mp)
  else if mp.frozen then (.error (frozendictNoSupport "assignment"), mp)
  else mergeFromSeq2 P seq2 override mp

/-- `dict_update_arg` (:3990-4005). -/
def dictUpdateArg (arg : UpdateArg K V) : DM K V Unit :=
  match arg with
  | .exact d => dictMerge P (.dict d) 1
  | .other hasKeys asMapping seq2 => do
    let h ← hasKeys
    if h then dictMerge P asMapping 1 else mergeFromSeq2 P seq2 true

/-- `_PyDict_HasOnlyStringKeys` (:1797-1810). -/
def dictHasOnlyStringKeys (KO : KeyOps K) (d : PyDict K V) : Bool :=
  d.body.kind != .general || (dictItems d).all fun e => KO.isStrLike e.1

/-- `dict_update_common` (:4007-4028), behind `dict.update` (:4033-4039) and `dict_init`
(:5356-5360). `kwds` is the keyword dict. -/
def dictUpdateCommon (args : List (UpdateArg K V)) (kwds : Option (PyDict K V))
    (methname : String) : DM K V Unit := do
  match args with
  | [] => pure ()
  | [arg] => dictUpdateArg P arg
  | _ => M.throw (.typeError s!"{methname} expected at most 1 argument, got {args.length}")
  match kwds with
  | none => pure ()
  | some kw =>
    if dictHasOnlyStringKeys P.toKeyOps kw then
      dictMerge P (.dict kw) 1
    else
      M.throw (.typeError "keywords must be strings")

/-- `dict_vectorcall` (:5362-5392), after `dict_new` (:5344-5354) made the empty dict. -/
def dictVectorcall (args : List (UpdateArg K V)) (kw : List (K × V)) : DM K V Unit := do
  match args with
  | [] => pure ()
  | [arg] => dictUpdateArg P arg
  | _ => M.throw (.typeError s!"dict expected at most 1 argument, got {args.length}")
  for (k, v) in kw do
    dictSetItem P k v

/-- `copy_lock_held_untracked` (:4432-4546), `PyDict_Copy` (:4548-4564), `dict.copy`: the copy, as
a new object with identity `id`. `iterOverridden` is `Py_TYPE(mp)->tp_iter != dict_iter`,
which sends the copy down `dict_merge`'s slow path through `as_`. -/
def dictCopy (mp : PyDict K V) (id : Nat) (iterOverridden : Bool) (as_ : MergeArg K V) :
    Py (PyDict K V) :=
  if mp.used == 0 then .ok { ident := id, nextId := mp.nextId }
  else
    match mp.body with
    | .split k v =>
      .ok { ident := id, used := mp.used, body := .split k (copyValues v), nextId := mp.nextId }
    | .combined k =>
      if !iterOverridden && decide (mp.used ≥ k.nentries * 2 / 3) then
        .ok { ident := id, used := mp.used, nextId := mp.nextId + 1
              body := .combined (cloneCombinedDictKeys mp.nextId k) }
      else
        let arg := if iterOverridden then as_ else .dict mp
        (dictMerge P arg 1 { ident := id, nextId := mp.nextId }) |> fun r =>
          match r with
          | (.ok _, d) => .ok d
          | (.error e, _) => .error e

/-- `PyDict_Copy` (:4549-4564): a frozendict is refused here, unlike `anydict_copy_untracked`. -/
def pyDictCopy (isDict : Bool) (mp : PyDict K V) (id : Nat) : Py (PyDict K V) :=
  if isDict && !mp.frozen then dictCopy P mp id false (.dict mp) else .error badInternalCall

/-- `_PyDict_Or` (:5150-5166): `none` is `NotImplemented`. The copy is a frozendict exactly when
`self` is (`anydict_copy_untracked`, :4569-4583). -/
def dictOr (self : PyDict K V) (id : Nat) (other : Option (PyDict K V))
    (otherArg : UpdateArg K V) : Py (Option (PyDict K V)) :=
  match other with
  | none => .ok none
  | some _ =>
    match dictCopy P self id false (.dict self) with
    | .error e => .error e
    | .ok new =>
      match dictUpdateArg P otherArg { new with frozen := self.frozen } with
      | (.ok _, d) => .ok (some d)
      | (.error e, _) => .error e

/-- `frozendict_or` (:5168-5188) for exact frozendict `self` and an exact dict or frozendict
`other`: an empty side gives back the other object, without a copy. -/
def frozendictOr (self other : PyDict K V) (id : Nat) (otherArg : UpdateArg K V) :
    Py (Option (PyDict K V)) :=
  if self.frozen && self.used == 0 && other.frozen then .ok (some other)
  else if self.frozen && other.used == 0 then .ok (some self)
  else dictOr P self id (some other) otherArg

/-- `frozendict_vectorcall` (:5394-5436) with an exact `frozendict` type. `shell` is the empty
object of `frozendict_new_untracked` (:8454-8466). -/
def frozendictVectorcall (shell : PyDict K V) (args : List (UpdateArg K V)) (kw : List (K × V)) :
    Py (PyDict K V) :=
  let build : DM K V Unit := do
    match args with
    | [arg] => dictUpdateArg P arg
    | _ => pure ()
    for (k, v) in kw do
      dictSetItem P k v
  match args, kw with
  | _ :: _ :: _, _ =>
    .error (.typeError s!"frozendict expected at most 1 argument, got {args.length}")
  | [.exact x], [] =>
    if x.frozen then .ok x
    else
      match build shell with
      | (.ok _, d) => .ok d
      | (.error e, _) => .error e
  | _, _ =>
    match build shell with
    | (.ok _, d) => .ok d
    | (.error e, _) => .error e

/-- `_PyDict_IOr` (:5190-5198). -/
def dictIor (other : UpdateArg K V) : DM K V Unit := dictUpdateArg P other

/-- The loop of `dict_dict_fromkeys` (:3380-3385) and `dict_set_fromkeys` (:3406-3411). -/
def fromkeysLoop (value : V) : List (K × Int) → DM K V Unit
  | [] => pure ()
  | (key, hash) :: rest => do
    insertDict P key hash value
    fromkeysLoop value rest

/-- `iterable` of `_PyDict_FromKeys`, by the branch it takes. -/
inductive FromKeysArg (K V : Type) where
  /-- `PyDict_CheckExact(iterable)` -/
  | dict (d : PyDict K V)
  /-- `PyAnySet_CheckExact(iterable)`: its size and `(key, hash)` in table order. -/
  | set (size : Nat) (es : List (K × Int))
  | iter (it : Iterable K)

/-- `_PyDict_FromKeys` (:3415-3600) for `cls` whose instances are exact dicts, with
`dict_dict_fromkeys` (:3362-3387) and `dict_set_fromkeys` (:3389-3413); `dict.fromkeys`
(:3983-3988). The state is the fresh dict. -/
def dictFromKeys (iterable : FromKeysArg K V) (value : V) : DM K V Unit := do
  match iterable with
  | .dict d =>
    let mp ← M.get
    dictResize (max (estimateLog2Keysize d.used) mp.body.log2Size) d.body.isUnicode
    fromkeysLoop P value ((dictItems d).map fun e => (e.1, e.2.2))
  | .set size es =>
    let mp ← M.get
    dictResize (max (estimateLog2Keysize size) mp.body.log2Size) false
    fromkeysLoop P value es
  | .iter it =>
    match it.getIter with
    | some e => M.throw e
    | none =>
      for key in it.items do
        dictSetItem P key value
      match it.stop with
      | some e => M.throw e
      | none => pure ()

/-- The loop of `dict_equal_lock_held` (:4633-4679) over `a`'s entries in table order;
the state is `b`. -/
def dictEqualLoop (veq : V → V → Py Bool) : List (K × Option V × Int) → DM K V Bool
  | [] => pure true
  | (key, aval, hash) :: rest => do
    match aval with
    | none => dictEqualLoop veq rest
    | some av =>
      let r ← dictLookup P key hash
      match r.2 with
      | none => return false
      | some bv =>
        let c ← M.lift (veq av bv)
        if !c then return false
        dictEqualLoop veq rest

/-- `a`'s entries by table index (not insertion order, for a split table). -/
def tableOrder (a : PyDict K V) : List (K × Option V × Int) :=
  match a.body with
  | .combined k => k.entries.filterMap fun e => e.map fun e => (e.key, some e.value, e.hash)
  | .split k v =>
    k.entries.zipIdx.filterMap fun p =>
      p.1.map fun e => (e.key, v.get p.2, e.hash)

/-- `dict_equal_lock_held` (:4621-4681), `dict_equal`. The state is `b`. -/
def dictEqual (veq : V → V → Py Bool) (a : PyDict K V) : DM K V Bool := do
  let b ← M.get
  if a.used != b.used then return false
  dictEqualLoop P veq (tableOrder a)

/-- `dict_richcompare` (:4694-4712) on two dicts, for `==` (`ne = false`) and `!=`. -/
def dictRichcompare (veq : V → V → Py Bool) (a : PyDict K V) (ne : Bool) : DM K V Bool := do
  let c ← dictEqual P veq a
  return c != ne

end Merge

/-- `anydict_repr_impl` (:3641-3724), behind `dict_repr` and `frozendict_repr`. `inRepr` is `Py_ReprEnter`
reporting a cycle. A repr that mutates the dict is out of scope. -/
def dictRepr (krepr : K → Py String) (vrepr : V → Py String) (inRepr : Bool)
    (mp : PyDict K V) : Py String :=
  if inRepr then .ok "{...}"
  else if mp.used == 0 then .ok "{}"
  else
    let rec go : List (K × V × Int) → Bool → String → Py String
      | [], _, acc => .ok (acc ++ "}")
      | (k, v, _) :: rest, first, acc =>
        let acc := if first then acc else acc ++ ", "
        match krepr k with
        | .error e => .error e
        | .ok ks =>
          match vrepr v with
          | .error e => .error e
          | .ok vs => go rest false (acc ++ ks ++ ": " ++ vs)
    go (dictItems mp) true "{"

/-- `frozendict_repr` (:8341-8359), for an exact frozendict. -/
def frozendictRepr (krepr : K → Py String) (vrepr : V → Py String) (inRepr : Bool)
    (mp : PyDict K V) : Py String :=
  if mp.used == 0 then .ok "frozendict()"
  else
    match dictRepr krepr vrepr inRepr mp with
    | .error e => .error e
    | .ok r => .ok s!"frozendict({r})"

/-- `_shuffle_bits` (:8362-8366), on `Py_uhash_t`. -/
def frozendictShuffle (h : Nat) : Nat :=
  (((h ^^^ 89869747) ^^^ ((h <<< 16) % 2 ^ 64)) * 3644798167) % 2 ^ 64

/-- `_PyTuple_HASH_XXROTATE`. -/
def xxRotate (x : Nat) : Nat := ((x <<< 31) % 2 ^ 64) ||| (x >>> 33)

/-- `frozendict_pair_hash` (:8368-8398), once the value's hash is in hand: `hash((key, value))`. -/
def frozendictPairHash (keyHash valueHash : Int) : Int :=
  let p1 : Nat := 11400714785074694791
  let p2 : Nat := 14029467366897019727
  let p5 : Nat := 2870177450012600261
  let m : Nat := 2 ^ 64
  let lane (acc v : Nat) : Nat := (xxRotate ((acc + v * p2) % m) * p1) % m
  let acc := lane (lane p5 (toU64 keyHash)) (toU64 valueHash)
  let acc := (acc + (2 ^^^ (p5 ^^^ 3527539))) % m
  if acc == m - 1 then 1546275796 else toI64 acc

/-- The hash of the items of `frozendict_hash` (:8402-8449). `vhash` is `PyObject_Hash(value)`, a
callback that may raise, `RecursionError` from the guard at :8419 included. -/
def frozendictHashItems (vhash : V → Py Int) : Nat → List (K × V × Int) → Py Nat
  | acc, [] => .ok acc
  | acc, (_, v, kh) :: rest =>
    match vhash v with
    | .error e => .error e
    | .ok h =>
      frozendictHashItems vhash (acc ^^^ frozendictShuffle (toU64 (frozendictPairHash kh h))) rest

/-- `frozendict_hash` (:8402-8449). The result is cached in `ma_hash`; a failure is not. -/
def frozendictHash (vhash : V → Py Int) : DM K V Int := fun mp =>
  if mp.fhash != -1 then (.ok mp.fhash, mp)
  else
    match frozendictHashItems vhash 0 (dictItems mp) with
    | .error e => (.error e, mp)
    | .ok h0 =>
      let m : Nat := 2 ^ 64
      let h1 := h0 ^^^ (((mp.used + 1) * 1927868237) % m)
      let h2 := h1 ^^^ (h1 >>> 11) ^^^ (h1 >>> 25)
      let h3 := (h2 * 69069 + 907133923) % m
      let h4 := if h3 == m - 1 then 590923713 else h3
      (.ok (toI64 h4), { mp with fhash := toI64 h4 })

/-- `keys_lock_held` (:3811-3847), `PyDict_Keys`. -/
def dictKeysList (mp : PyDict K V) : List K := (dictItems mp).map (·.1)
/-- `values_lock_held` (:3860-3896), `PyDict_Values`. -/
def dictValuesList (mp : PyDict K V) : List V := (dictItems mp).map (·.2.1)
/-- `items_lock_held` (:3908-3959), `PyDict_Items`. -/
def dictItemsList (mp : PyDict K V) : List (K × V) := (dictItems mp).map fun e => (e.1, e.2.1)

/-- Dict iterator flavour: which of the six iterator types. -/
inductive IterKind where
  | key | value | item
  deriving DecidableEq, Repr, Inhabited

/-- What one `next()` hands back. -/
inductive IterItem (K V : Type) where
  | key (k : K)
  | value (v : V)
  | item (k : K) (v : V)
  deriving Repr, DecidableEq

/-- The difference between the three bodies: the key, the value, or a pair. -/
def IterKind.result {K V : Type} : IterKind → K × V → IterItem K V
  | .key, p => .key p.1
  | .value, p => .value p.2
  | .item, p => .item p.1 p.2

/-- `dictiterobject` (:5566-5573). `alive` is `di_dict != NULL`. -/
structure DictIter where
  alive : Bool := true
  used : Int
  pos : Int
  len : Int
  kind : IterKind
  rev : Bool
  deriving Repr, Inhabited

/-- `dictiter_new` (:5575-5614), behind `dict_iter`, `dict.__reversed__` and the views'
`__iter__`/`__reversed__`. -/
def dictiterNew (mp : PyDict K V) (kind : IterKind) (rev : Bool) : DictIter :=
  { used := mp.used, len := mp.used, kind, rev
    pos := if rev then
        (if mp.body.isSplit then (mp.used : Int) - 1 else (mp.body.nentries : Int) - 1)
      else 0 }

/-- `dictiter_len` (:5636-5644): `PyLong_FromSize_t(len)`, so a negative `len` wraps. -/
def dictiterLen (mp : PyDict K V) (di : DictIter) : Nat :=
  if di.alive && decide (di.used = mp.used) then toU64 di.len else 0

/-- `dictiter_iternextkey_lock_held` (:5670-5735), `dictiter_iternextvalue_lock_held`
(:5795-5858), `dictiter_iternextitem_lock_held` (:5916-5990) and their callers
`dictiter_iternextkey` (:5739-5758), `dictiter_iternextvalue` (:5862-5881),
`dictiter_iternextitem` (:6145-6179): the three bodies differ only in what they hand back.
`.ok none` is exhaustion. -/
def dictiterNextForward (d : PyDict K V) (di : DictIter) : Py (Option (K × V)) × DictIter :=
  if !di.alive then (.ok none, di) else
  if di.used != d.used then
    (.error (runtimeError "dictionary changed size during iteration"), { di with used := -1 })
  else
    let i := di.pos
    let dead := { di with alive := false }
    let found : Option (Nat × K × V) :=
      match d.body with
      | .split k v =>
        if i ≥ d.used then none
        else
          let index := v.indexFromOrder i.toNat
          match k.entry index, v.get index with
          | some e, some x => some (i.toNat, e.key, x)
          | _, _ => none
      | .combined k =>
        match scanFrom (k.entries.drop i.toNat) i.toNat with
        | some (j, e) => some (j, e.key, e.value)
        | none => none
    match found with
    | none => (.ok none, dead)
    | some (j, key, value) =>
      -- We found an element, but did not expect it
      if di.len == 0 then
        (.error (runtimeError "dictionary keys changed during iteration"), dead)
      else
        (.ok (some (key, value)), { di with pos := (j : Int) + 1, len := di.len - 1 })

/-- The backwards scan of `dictreviter_iter_lock_held` (:6250-6256): the first live entry
at or below `i`. -/
def scanDown (es : List (Option (Ent K V))) : Nat → Option (Nat × Ent K V)
  | 0 =>
    match es[0]? with
    | some (some e) => some (0, e)
    | _ => none
  | i + 1 =>
    match es[i + 1]? with
    | some (some e) => some (i + 1, e)
    | _ => scanDown es i

/-- `dictreviter_iter_lock_held` (:6217-6314), `dictreviter_iternext` (:6316-6331).
Since gh-158254 it has the `di->len == 0` test of the forward iterators (:6272-6277). -/
def dictiterNextReverse (d : PyDict K V) (di : DictIter) : Py (Option (K × V)) × DictIter :=
  if !di.alive then (.ok none, di) else
  if di.used != d.used then
    (.error (runtimeError "dictionary changed size during iteration"), { di with used := -1 })
  else
    let i := di.pos
    let dead := { di with alive := false }
    if i < 0 then (.ok none, dead) else
    let found : Option (Nat × K × V) :=
      match d.body with
      | .split k v =>
        let index := v.indexFromOrder i.toNat
        match k.entry index, v.get index with
        | some e, some x => some (i.toNat, e.key, x)
        | _, _ => none
      | .combined k =>
        if i ≥ k.nentries then none
        else
          match scanDown k.entries i.toNat with
          | some (j, e) => some (j, e.key, e.value)
          | none => none
    match found with
    | none => (.ok none, dead)
    | some (j, key, value) =>
      -- We found an element, but did not expect it
      if di.len == 0 then
        (.error (runtimeError "dictionary keys changed during iteration"), dead)
      else
        (.ok (some (key, value)), { di with pos := (j : Int) - 1, len := di.len - 1 })

def dictiterNext (d : PyDict K V) (di : DictIter) : Py (Option (K × V)) × DictIter :=
  if di.rev then dictiterNextReverse d di else dictiterNextForward d di

/-- `next(it)`, with what the iterator's flavour hands back. -/
def dictiterYield (d : PyDict K V) (di : DictIter) : Py (Option (IterItem K V)) × DictIter :=
  match dictiterNext d di with
  | (.ok (some p), di') => (.ok (some (di.kind.result p)), di')
  | (.ok none, di') => (.ok none, di')
  | (.error e, di') => (.error e, di')

/-- `PyObject_LengthHint` on a dict iterator, as `list(it)` runs it first
(`Objects/abstract.c`): a hint that does not fit `Py_ssize_t` raises. -/
def dictiterLengthHint (mp : PyDict K V) (di : DictIter) : Py Nat :=
  let h := dictiterLen mp di
  if h ≥ 2 ^ 63 then .error (.overflowError "Python int too large to convert to C ssize_t")
  else .ok h

/-- Drain an iterator: `PySequence_List` after the hint. -/
def dictiterDrain (d : PyDict K V) : Nat → DictIter → List (K × V) → Py (List (K × V)) × DictIter
  | 0, di, _ => (.error .modelFuel, di)
  | fuel + 1, di, acc =>
    match dictiterNext d di with
    | (.error e, di') => (.error e, di')
    | (.ok none, di') => (.ok acc.reverse, di')
    | (.ok (some x), di') => dictiterDrain d fuel di' (x :: acc)

/-- `list(it)`. -/
def dictiterToList (d : PyDict K V) (di : DictIter) : Py (List (K × V)) × DictIter :=
  match dictiterLengthHint d di with
  | .error e => (.error e, di)
  | .ok _ => dictiterDrain d (d.body.nentries + d.used + 2) di []

/-- `dictiter_reduce` (:6360-6373): drain a copy, leaving `di` itself untouched. -/
def dictiterReduce (d : PyDict K V) (di : DictIter) : Py (List (K × V)) :=
  (dictiterToList d di).1

/-- `_PyDict_NewPresized` and `dict_new_presized` (:2307-2339). -/
def dictNewPresized (id minused : Nat) (unicode : Bool) : PyDict K V :=
  let log2MaxPresize := 17
  let maxPresize := 2 ^ log2MaxPresize
  if minused ≤ usableFraction PyDict_MINSIZE then { ident := id }
  else
    let log2 :=
      if minused > usableFraction maxPresize then log2MaxPresize
      else estimateLog2Keysize minused
    { ident := id, nextId := 2, body := .combined (newKeysObject 1 log2 unicode) }

section
variable [DecidableEq K] (P : Proto K (PyDict K V))

/-- `_PyDict_FromItems` (:2341-2377), the `BUILD_MAP` entry point. -/
def dictFromItems (id : Nat) (items : List (K × V)) : Py (PyDict K V) :=
  let unicode := items.all fun i => P.isStr i.1
  let start : PyDict K V := dictNewPresized id items.length unicode
  let run : DM K V Unit := do
    for (k, v) in items do
      dictSetItem P k v
  match run start with
  | (.ok _, d) => .ok d
  | (.error e, _) => .error e

/-- `_PyDict_LoadGlobalStackRef` (:2667-2692):
globals, then builtins. `none` is "not found, no exception" (a `NameError` in the caller). -/
def dictLoadGlobal (globals builtins : PyDict K V) (key : K) : Py (Option V) :=
  match P.hash key with
  | .error e => .error e
  | .ok hash =>
    match (dictLookup P key hash globals).1 with
    | .error e => .error e
    | .ok (ix, value) =>
      if ix != DKIX_EMPTY && value.isSome then .ok value
      else
        match (dictLookup P key hash builtins).1 with
        | .error e => .error e
        | .ok (_, v) => .ok v

/-- `_PyDict_GetMethodStackRef` (:1751-1795) in the GIL build. -/
def dictGetMethod (mp : PyDict K V) (key : K) (method : Option V) : Py (Bool × Option V) :=
  match P.hash key with
  | .error e => .error e
  | .ok hash =>
    match (dictLookup P key hash mp).1 with
    | .error e => .error e
    | .ok (ix, obj) =>
      match obj with
      | some o => if ix ≥ 0 then .ok (true, some o) else .ok (false, method)
      | none => .ok (false, method)

/-- `_PyDict_LoadBuiltinsFromGlobals` (:2694-2726): `globals["__builtins__"]`, or the
frame's builtins; a module stands for its dict (`moduleDict`). -/
def dictLoadBuiltinsFromGlobals (isDict : Bool) (globals : PyDict K V) (key : K) (hash : Int)
    (dflt : V) (moduleDict : V → Option V) : Py V :=
  if !isDict then .error badInternalCall else
  match (dictLookup P key hash globals).1 with
  | .error e => .error e
  | .ok (_, none) => .ok dflt
  | .ok (_, some b) =>
    match moduleDict b with
    | some d => .ok d
    | none => .ok b

end

/-- `_PyDictKeys_StringLookup` (:1268-1276): `DKIX_ERROR` is `none`. -/
def dictKeysStringLookup [DecidableEq K] (P : Proto K (PyDict K V)) {W : Type} (dk : Keys K W)
    (key : K) (hash : Int) : Py (Option Int) :=
  -- check_keys_unicode (:1215-1219), hash_unicode_key (:1221-1231)
  if !(P.isStr key && dk.kind != .general) then .ok none
  else
    match unicodekeysLookupUnicode P dk key hash with
    | .ok ix => .ok (some ix)
    | .error e => .error e

end PyLean.DictSet
