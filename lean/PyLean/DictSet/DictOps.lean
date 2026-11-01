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
def badInternalCall : PyExc := systemError "~bad argument to internal function"

section
variable [DecidableEq K] (P : Proto K (PyDict K V))

/-- `dict_getitem` (:2300-2342), behind `PyDict_GetItem` and `PyDict_GetItemString`:
every error is swallowed. -/
def dictGetitemSuppress (isDict : Bool) (key : K) : DM K V (Option V) :=
  if !isDict then pure none else
  match P.hash key with
  | .error _ => pure none
  | .ok hash =>
    M.tryCatch (do
      let r ← dictLookup P key hash
      return r.2) (fun _ => pure none)

/-- `_PyDict_GetItem_KnownHash` (:2389-2409). -/
def dictGetItemKnownHash (isDict : Bool) (key : K) (hash : Int) : DM K V (Option V) := do
  if !isDict then M.throw badInternalCall
  let r ← dictLookup P key hash
  return r.2

/-- `_PyDict_GetItemRef_KnownHash_LockHeld` (:2415-2432), `_PyDict_GetItemRef_KnownHash`
(:2438-2462): `some v` is return value 1, `none` is 0, an exception is -1. -/
def dictGetItemRefKnownHash (key : K) (hash : Int) : DM K V (Option V) := do
  let r ← dictLookup P key hash
  match r.2 with
  | none => return none
  | some v => return some v

/-- `PyDict_GetItemRef` (:2464-2481). -/
def pyDictGetItemRef (isDict : Bool) (key : K) : DM K V (Option V) := do
  if !isDict then M.throw badInternalCall
  let hash ← hashKey P key
  dictGetItemRefKnownHash P key hash

/-- `_PyDict_GetItemRef_Unicode_LockHeld` (:2483-2509). -/
def dictGetItemRefUnicode (key : K) : DM K V (Option V) := do
  let hash ← hashKey P key
  let r ← dictLookup P key hash
  match r.2 with
  | none => return none
  | some v => return some v

/-- `PyDict_GetItemWithError` (:2515-2541). -/
def pyDictGetItemWithError (isDict : Bool) (key : K) : DM K V (Option V) := do
  if !isDict then M.throw badInternalCall
  let hash ← hashKey P key
  let r ← dictLookup P key hash
  return r.2

/-- `_PyDict_GetItemWithError` (:2543-2552): `tp_hash`, then the known-hash lookup. -/
def dictGetItemWithErrorUnchecked (key : K) : DM K V (Option V) := do
  let hash ← M.lift (P.hash key)
  dictGetItemKnownHash P true key hash

/-- `_PyDict_LookupIndex` (:2368-2383). -/
def dictLookupIndex (key : K) : DM K V Int := do
  let hash ← hashKey P key
  let r ← dictLookup P key hash
  return r.1

/-- Key made from a C string (`PyUnicode_FromString`, which may fail), then an action:
`_PyDict_GetItemStringWithError` (:2566-2577), `PyDict_GetItemStringRef` (:5061-5072),
`PyDict_DelItemString` (:5108-5119), `PyDict_SetItemString` (:5084-5097),
`PyDict_ContainsString` (:4848-4858), `_PyDict_GetItemIdWithError` (:2554-2564),
`_PyDict_SetItemId` (:5074-5082), `_PyDict_DelItemId` (:5099-5106),
`_PyDict_ContainsId` (:4884-4892). -/
def withCKey {α : Type} (mk : Py K) (act : K → DM K V α) : DM K V α := do
  let k ← M.lift mk
  act k

/-- `PyDict_GetItemString` (:5043-5059): both failures are swallowed. -/
def pyDictGetItemString (isDict : Bool) (mk : Py K) : DM K V (Option V) :=
  match mk with
  | .error _ => pure none
  | .ok k => dictGetitemSuppress P isDict k

/-- `_PyDict_Contains_KnownHash` (:4860-4882). -/
def dictContainsKnownHash (key : K) (hash : Int) : DM K V Bool := do
  let r ← dictLookup P key hash
  return r.1 != DKIX_EMPTY && r.2.isSome

/-- `PyDict_Contains` (:4835-4846), behind `dict.__contains__` (:4362-4374). -/
def pyDictContains (key : K) : DM K V Bool := do
  let hash ← hashKey P key
  dictContainsKnownHash P key hash

/-- `dict_subscript` (:3504-3538). `missing` is `__missing__` of a subclass:
`none` for an exact dict or a subclass without it. -/
def dictSubscript (missing : Option (K → Py V)) (key : K) : DM K V V := do
  let hash ← hashKey P key
  let r ← dictLookup P key hash
  match r.2 with
  | some v =>
    if r.1 == DKIX_EMPTY then M.throw (keyErr P key)
    return v
  | none =>
    match missing with
    | some f => M.lift (f key)
    | none => M.throw (keyErr P key)

/-- `dict_ass_sub` (:3540-3547). -/
def dictAssSub (key : K) (w : Option V) : DM K V Unit :=
  match w with
  | none => dictDelItem P key
  | some v => dictSetItem P key v

/-- `dict.get` (`dict_get_impl`, :4386-4406). -/
def dictGet (key : K) (dflt : V) : DM K V V := do
  let hash ← hashKey P key
  let r ← dictLookup P key hash
  match r.2 with
  | some v => return (if r.1 == DKIX_EMPTY then dflt else v)
  | none => return dflt

/-- `delitemif_lock_held` (:2887-2925) and `_PyDict_DelItemIf`: `pred` may raise. -/
def dictDelItemIf (pred : V → Py Bool) (key : K) : DM K V Bool := do
  let hash ← M.lift (P.hash key)
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

/-- `_PyDict_Pop_KnownHash` (:3110-3155): `some v` is 1, `none` is 0. -/
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

/-- `pop_lock_held` (:3157-3187), `PyDict_Pop` (:3189-3198). An empty dict answers before
the key is hashed. -/
def pyDictPop (isDict : Bool) (key : K) : DM K V (Option V) := fun mp =>
  if !isDict then (.error badInternalCall, mp)
  else if mp.used == 0 then (.ok none, mp)
  else
    match P.hash key with
    | .error e => (.error (dictUnhashableType P key e), mp)
    | .ok hash => dictPopKnownHash P key hash mp

/-- `dict_pop_default` (:3218-3230), `_PyDict_Pop`, `dict.pop`. -/
def dictPopDefault (key : K) (dflt : Option V) : DM K V V := do
  match ← pyDictPop P true key with
  | some v => return v
  | none =>
    match dflt with
    | some d => return d
    | none => M.throw (keyErr P key)

/-- `dict_setdefault_ref_lock_held` (:4408-4505): the status and `*result`. Status 1 is
"already present", as in C. `result`/`incref` model the `result != NULL` and
`incref_result` arguments.

The branch at :4477 tests `ix == DKIX_EMPTY` only. For a split table and a key that is
not an exact `str`, `_Py_dict_lookup` can return `ix >= 0` with `*value_addr == NULL`
(key in the shared keys, no value in this dict); the code then runs on to :4499-4503
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

/-- `dict.setdefault` (`dict_setdefault_impl`, :4541-4549), `PyDict_SetDefaultRef`
(:4507-4516). -/
def dictSetdefault (key : K) (dflt : V) : DM K V V := do
  let r ← dictSetdefaultRef P key dflt true true
  match r.2 with
  | some v => return v
  | none => M.unreachable

/-- `PyDict_SetDefault` (:4518-4526): no `Py_NewRef`, so a NULL result is simply
returned; `none` is that NULL. -/
def pyDictSetDefault (key : K) (dflt : V) : DM K V (Option V) := do
  let r ← dictSetdefaultRef P key dflt true false
  return r.2

end

/-- The backwards scan of `dict_popitem_impl` (:4637-4640, :4652-4655): the last live
entry below `i`. -/
def lastLive (es : List (Option (Ent K V))) : Nat → Option (Nat × Ent K V)
  | 0 => none
  | i + 1 =>
    match es[i]? with
    | some (some e) => some (i, e)
    | _ => lastLive es i

/-- The part of `dict_popitem_impl` after the table is known to be combined (:4630-4676). -/
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

/-- `dict_popitem_impl` (:4596-4679). -/
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

/-- `clear_embedded_values` (:2944-2957). -/
def clearEmbeddedValues (v : Values V) (nentries : Nat) : Values V :=
  { v with
    values := v.values.zipIdx.map (fun p => if p.2 < nentries then none else p.1)
    order := [] }

/-- `clear_lock_held` (:2959-3002), behind `PyDict_Clear`, `_PyDict_Clear_LockHeld`,
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

/-- `copy_values` (:4125-4144). -/
def copyValues (v : Values V) : Values V :=
  { v with embedded := false }

/-- `clone_combined_dict_keys` (:912-969): a bitwise copy of the keys object. -/
def cloneCombinedDictKeys (id : Nat) (k : Keys K V) : Keys K V :=
  { k with ident := id }

section Merge
variable [DecidableEq K] (P : Proto K (PyDict K V))

/-- The loop of `dict_dict_merge` (:3952-3986) over `other`'s items. The check
`orig_size != other->ma_used` (:3981) cannot fire here, since a comparison can only
reach the receiver in this model; see `Diff.lean`. -/
def mergeLoop (override : Nat) : List (K × V × Int) → DM K V Unit
  | [] => pure ()
  | (key, value, hash) :: rest => do
    if override == 1 then
      insertDict P key hash value
    else
      let err ← dictContainsKnownHash P key hash
      if !err then
        insertDict P key hash value
      else if override != 0 then
        M.throw (keyErr P key)
    mergeLoop override rest

/-- The tail of `dict_dict_merge` (:3934-3987): one big resize, then the insertions. -/
def mergeRest (other : PyDict K V) (override : Nat) : DM K V Unit := fun mp =>
  match (if usableFraction (2 ^ mp.body.log2Size) < other.used then
           dictResize (estimateLog2Keysize (mp.used + other.used)) other.body.isUnicode mp
         else (.ok (), mp)) with
  | (.error e, s) => (.error e, s)
  | (.ok _, s) => mergeLoop P override (dictItems other) s

/-- `dict_dict_merge` (:3891-3988). -/
def dictDictMerge (other : PyDict K V) (override : Nat) : DM K V Unit := fun mp =>
  if other.ident == mp.ident || other.used == 0 then (.ok (), mp)
  else if mp.used == 0 then
    -- `override = 1`: the target is empty, so the test is unnecessary (:3900-3905).
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

/-- The right operand of `dict_merge` (:3990-4088). -/
inductive MergeArg (K V : Type) where
  /-- `PyDict_Check(b) && Py_TYPE(b)->tp_iter == dict_iter`. -/
  | dict (d : PyDict K V)
  /-- Otherwise: `PyMapping_Keys(b)` (a list, or the error) and `PyObject_GetItem`. -/
  | mapping (keys : Py (List K)) (getitem : K → Py V)

/-- The slow loop of `dict_merge` (:4042-4075). -/
def mergeGenericLoop (getitem : K → Py V) (override : Nat) : List K → DM K V Unit
  | [] => pure ()
  | key :: rest => do
    let skip ← (if override != 1 then do
      let status ← pyDictContains P key
      if status then
        if override == 0 then
          pure true
        else
          M.throw (keyErr P key)
      else pure false
    else pure false)
    if !skip then
      let value ← M.lift (getitem key)
      dictSetItem P key value
    mergeGenericLoop getitem override rest

/-- `dict_merge` (:3990-4088), behind `PyDict_Update` (override 1), `PyDict_Merge`
(`override != 0`) and `_PyDict_MergeEx` (override as given). -/
def dictMerge (b : MergeArg K V) (override : Nat) : DM K V Unit :=
  match b with
  | .dict other => dictDictMerge P other override
  | .mapping keys getitem => do
    let ks ← M.lift keys
    mergeGenericLoop P getitem override ks

/-- One element of the iterable given to `dict.update`, after `PySequence_Fast`. -/
inductive Seq2Item (K V : Type) where
  /-- `PySequence_Fast` raised. -/
  | notSeq (e : PyExc)
  | wrongLen (n : Nat)
  | pair (k : K) (v : V)

/-- The loop of `merge_from_seq2_lock_held` (:3810-3866). The note added at :3826 does
not change `str(e)`. -/
def seq2Loop (override : Bool) : Nat → List (Seq2Item K V) → Option PyExc → DM K V Unit
  | _, [], stop =>
    match stop with
    | some e => M.throw e
    | none => pure ()
  | i, item :: rest, stop => do
    match item with
    | .notSeq e => M.throw e
    | .wrongLen n =>
      M.throw (.valueError s!"dictionary update sequence element #{i} has length {n}; 2 is required")
    | .pair k v =>
      if override then
        dictSetItem P k v
      else
        let _ ← dictSetdefaultRef P k v false false
    seq2Loop override (i + 1) rest stop

/-- `merge_from_seq2_lock_held` (:3794-3878), `PyDict_MergeFromSeq2` (:3880-3889). -/
def mergeFromSeq2 (seq2 : Iterable (Seq2Item K V)) (override : Bool) : DM K V Unit :=
  match seq2.getIter with
  | some e => M.throw e
  | none => seq2Loop P override 0 seq2.items seq2.stop

/-- The argument of `dict.update`, `dict()`, `|=`. -/
inductive UpdateArg (K V : Type) where
  /-- `PyDict_CheckExact(arg)`. -/
  | exact (d : PyDict K V)
  /-- Anything else: `PyObject_HasAttrWithError(arg, "keys")`, then the mapping route or
  the sequence route. -/
  | other (hasKeys : Py Bool) (asMapping : MergeArg K V) (seq2 : Iterable (Seq2Item K V))

/-- `dict_update_arg` (:3733-3748). -/
def dictUpdateArg (arg : UpdateArg K V) : DM K V Unit :=
  match arg with
  | .exact d => dictMerge P (.dict d) 1
  | .other hasKeys asMapping seq2 => do
    let h ← M.lift hasKeys
    if h then dictMerge P asMapping 1 else mergeFromSeq2 P seq2 true

/-- `_PyDict_HasOnlyStringKeys` (:1717-1730). -/
def dictHasOnlyStringKeys (KO : KeyOps K) (d : PyDict K V) : Bool :=
  d.body.kind != .general || (dictItems d).all fun e => KO.isStrLike e.1

/-- `dict_update_common` (:3750-3771), behind `dict.update` (:3776-3782) and `dict_init`
(:4940-4944). `kwds` is the keyword dict. -/
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

/-- `dict_vectorcall` (:4946-4975), after `dict_new` (:4913-4938) made the empty dict. -/
def dictVectorcall (args : List (UpdateArg K V)) (kw : List (K × V)) : DM K V Unit := do
  match args with
  | [] => pure ()
  | [arg] => dictUpdateArg P arg
  | _ => M.throw (.typeError s!"dict expected at most 1 argument, got {args.length}")
  for (k, v) in kw do
    dictSetItem P k v

/-- `copy_lock_held` (:4146-4225), `PyDict_Copy` (:4227-4242), `dict.copy`: the copy, as
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

/-- `dict_or` (:4775-4790): `none` is `NotImplemented`. -/
def dictOr (self : PyDict K V) (id : Nat) (other : Option (PyDict K V))
    (otherArg : UpdateArg K V) : Py (Option (PyDict K V)) :=
  match other with
  | none => .ok none
  | some _ =>
    match dictCopy P self id false (.dict self) with
    | .error e => .error e
    | .ok new =>
      match dictUpdateArg P otherArg new with
      | (.ok _, d) => .ok (some d)
      | (.error e, _) => .error e

/-- `dict_ior` (:4792-4799). -/
def dictIor (other : UpdateArg K V) : DM K V Unit := dictUpdateArg P other

/-- The loop of `dict_dict_fromkeys` (:3255-3261) and `dict_set_fromkeys` (:3281-3286). -/
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

/-- `_PyDict_FromKeys` (:3290-3360) for `cls` whose instances are exact dicts, with
`dict_dict_fromkeys` (:3238-3263) and `dict_set_fromkeys` (:3265-3288); `dict.fromkeys`
(:3726-3731). The state is the fresh dict. -/
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

/-- The loop of `dict_equal_lock_held` (:4270-4316) over `a`'s entries in table order;
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

/-- `dict_equal_lock_held` (:4258-4318), `dict_equal`. The state is `b`. -/
def dictEqual (veq : V → V → Py Bool) (a : PyDict K V) : DM K V Bool := do
  let b ← M.get
  if a.used != b.used then return false
  dictEqualLoop P veq (tableOrder a)

/-- `dict_richcompare` (:4331-4349) on two dicts, for `==` (`ne = false`) and `!=`. -/
def dictRichcompare (veq : V → V → Py Bool) (a : PyDict K V) (ne : Bool) : DM K V Bool := do
  let c ← dictEqual P veq a
  return c != ne

end Merge

/-- `dict_repr_lock_held` (:3402-3486), `dict_repr`. `inRepr` is `Py_ReprEnter`
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

/-- `keys_lock_held` (:3555-3591), `PyDict_Keys`. -/
def dictKeysList (mp : PyDict K V) : List K := (dictItems mp).map (·.1)
/-- `values_lock_held` (:3604-3640), `PyDict_Values`. -/
def dictValuesList (mp : PyDict K V) : List V := (dictItems mp).map (·.2.1)
/-- `items_lock_held` (:3652-3703), `PyDict_Items`. -/
def dictItemsList (mp : PyDict K V) : List (K × V) := (dictItems mp).map fun e => (e.1, e.2.1)

/-- Dict iterator flavour: which of the six iterator types. -/
inductive IterKind where
  | key | value | item
  deriving DecidableEq, Repr, Inhabited

/-- `dictiterobject` (:5123-5130). `alive` is `di_dict != NULL`. -/
structure DictIter where
  alive : Bool := true
  used : Int
  pos : Int
  len : Int
  kind : IterKind
  rev : Bool
  deriving Repr, Inhabited

/-- `dictiter_new` (:5132-5171), behind `dict_iter`, `dict.__reversed__` and the views'
`__iter__`/`__reversed__`. -/
def dictiterNew (mp : PyDict K V) (kind : IterKind) (rev : Bool) : DictIter :=
  { used := mp.used, len := mp.used, kind, rev
    pos := if rev then
        (if mp.body.isSplit then (mp.used : Int) - 1 else (mp.body.nentries : Int) - 1)
      else 0 }

/-- `dictiter_len` (:5193-5201): `PyLong_FromSize_t(len)`, so a negative `len` wraps. -/
def dictiterLen (mp : PyDict K V) (di : DictIter) : Nat :=
  if di.alive && decide (di.used = mp.used) then toU64 di.len else 0

/-- `dictiter_iternextkey_lock_held` (:5227-5292), `dictiter_iternextvalue_lock_held`
(:5352-5415), `dictiter_iternextitem_lock_held` (:5473-5547) and their callers
`dictiter_iternextkey` (:5296-5315), `dictiter_iternextvalue` (:5419-5438),
`dictiter_iternextitem` (:5697-5738): the three bodies differ only in what they hand back.
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

/-- The backwards scan of `dictreviter_iter_lock_held` (:5809-5815): the first live entry
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

/-- `dictreviter_iter_lock_held` (:5776-5872), `dictreviter_iternext` (:5874-5889).
Unlike the forward iterators, 3.14.7 has no `di->len == 0` check here. -/
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
      (.ok (some (key, value)), { di with pos := (j : Int) - 1, len := di.len - 1 })

def dictiterNext (d : PyDict K V) (di : DictIter) : Py (Option (K × V)) × DictIter :=
  if di.rev then dictiterNextReverse d di else dictiterNextForward d di

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

/-- `dictiter_reduce` (:5918-5931): drain a copy, leaving `di` itself untouched. -/
def dictiterReduce (d : PyDict K V) (di : DictIter) : Py (List (K × V)) :=
  (dictiterToList d di).1

/-- `_PyDict_NewPresized` and `dict_new_presized` (:2216-2249). -/
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

/-- `_PyDict_FromItems` (:2251-2288), the `BUILD_MAP` entry point. -/
def dictFromItems (id : Nat) (items : List (K × V)) : Py (PyDict K V) :=
  let unicode := items.all fun i => P.isStr i.1
  let start : PyDict K V := dictNewPresized id items.length unicode
  let run : DM K V Unit := do
    for (k, v) in items do
      dictSetItem P k v
  match run start with
  | (.ok _, d) => .ok d
  | (.error e, _) => .error e

/-- `_PyDict_LoadGlobal` (:2591-2614), `_PyDict_LoadGlobalStackRef` (:2616-2640):
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

/-- `_PyDict_GetMethodStackRef` (:1671-1715) in the GIL build. -/
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

/-- `_PyDict_LoadBuiltinsFromGlobals` (:2642-2674): `globals["__builtins__"]`, or the
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

/-- `_PyDictKeys_StringLookup` (:1188-1196): `DKIX_ERROR` is `none`. -/
def dictKeysStringLookup [DecidableEq K] (P : Proto K (PyDict K V)) {W : Type} (dk : Keys K W)
    (key : K) (hash : Int) : Py (Option Int) :=
  -- check_keys_unicode (:1135-1139), hash_unicode_key (:1141-1151)
  if !(P.isStr key && dk.kind != .general) then .ok none
  else
    match unicodekeysLookupUnicode P dk key hash with
    | .ok ix => .ok (some ix)
    | .error e => .error e

end PyLean.DictSet
