import PyLean.DictSet.DictOps

/-!
Instance dictionaries (`Objects/dictobject.c:6785-7643`): shared keys, inline values, the lazily
materialized `__dict__`, and detaching. Line numbers refer to `Objects/dictobject.c`.

`ObjSt` is the state one operation sees: the class's cached keys, and the instance. A dict whose
`ma_values` is the instance's inline array holds them in its own `Body.split` with
`embedded = true`, and `inlineV` is stale until `sync` writes them back; that aliasing is the
pointer equality `dict->ma_values == values` of the C code.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type}

/-- The instance: inline values and `_PyObject_ManagedDictPointer(obj)->dict`. -/
structure Inst (K V : Type) where
  inlineV : Values V
  dict : Option (PyDict K V) := none
  deriving Repr, Inhabited

structure ObjSt (K V : Type) where
  keys : Keys K Unit
  inst : Inst K V
  nextDict : Nat := 1000
  deriving Repr, Inhabited

abbrev IM (K V : Type) := M (ObjSt K V)

/-- `dict->ma_values == _PyObject_InlineValues(obj)`. -/
def isInlineDict (d : PyDict K V) : Bool :=
  match d.body with
  | .split _ v => v.embedded
  | .combined _ => false

/-- The inline array as C sees it. -/
def Inst.values (i : Inst K V) : Values V :=
  match i.dict with
  | some d =>
    match d.body with
    | .split _ v => if v.embedded then v else i.inlineV
    | .combined _ => i.inlineV
  | none => i.inlineV

/-- `invalidate_and_clear_inline_values` (:2040-2048), `clear_inline_values` (:7274-7283). -/
def invalidateInline (v : Values V) : Values V :=
  { v with valid := false, values := v.values.map fun _ => none, order := [] }

/-- After a dict operation on an instance dict: the shared keys may have grown, and a resize
that left the split form has invalidated the inline values (:2138-2142). -/
def syncDict (before : Bool) (d : PyDict K V) (s : ObjSt K V) : ObjSt K V :=
  let inst' : Inst K V :=
    match d.body with
    | .split _ v =>
      if v.embedded then { s.inst with dict := some d, inlineV := v }
      else { s.inst with dict := some d }
    | .combined _ =>
      if before then { s.inst with dict := some d, inlineV := invalidateInline s.inst.inlineV }
      else { s.inst with dict := some d }
  match d.body with
  | .split k _ => { s with keys := k, inst := inst' }
  | .combined _ => { s with inst := inst' }

/-- Bring a dict's view of the shared keys up to date: another instance may have added keys. -/
def refreshKeys (keys : Keys K Unit) (d : PyDict K V) : PyDict K V :=
  match d.body with
  | .split _ v => { d with body := .split keys v }
  | .combined _ => d

/-- Run a dict operation on the instance's materialized dict. -/
def onInstDict {α : Type} (m : DM K V α) (d : PyDict K V) : IM K V α := fun s =>
  let before := isInlineDict d
  match m (refreshKeys s.keys d) with
  | (r, d') => (r, syncDict before d' s)

section
variable [DecidableEq K] (P : Proto K (PyDict K V))

/-- `_PyDict_NewKeysForClass` (:6787-6818): `attrs` is `__static_attributes__`. -/
def dictNewKeysForClass (attrs : List K) : Keys K Unit :=
  let k0 : Keys K Unit :=
    { (newKeysObject 1 NEXT_LOG2_SHARED_KEYS_MAX_SIZE true : Keys K Unit) with
      usable := SHARED_KEYS_MAX_SIZE, kind := .split }
  let rec go : List K → Keys K Unit → Keys K Unit
    | [], k => k
    | a :: rest, k =>
      if P.isStr a then
        match P.hash a with
        | .ok h =>
          match insertSplitKey P k a h with
          | .ok (ix, k') => if ix == DKIX_EMPTY then k else go rest k'
          | .error _ => k
        | .error _ => go rest k
      else go rest k
  go attrs k0

end

/-- `_PyObject_InitInlineValues` (:6820-6854): `keys` shrink by one each time, so later
instances get smaller arrays. -/
def initInlineValues (keys : Keys K Unit) : Keys K Unit × Inst K V :=
  let keys' := if keys.usable > 1 then { keys with usable := keys.usable - 1 } else keys
  let size := sharedKeysUsableSize keys'
  (keys', { inlineV := { values := List.replicate size none, order := [], embedded := true } })

/-- `make_dict_from_instance_attributes` (:6856-6871). -/
def makeDictFromInstanceAttributes (id : Nat) (keys : Keys K Unit) (values : Values V) : PyDict K V :=
  { ident := id
    used := (values.values.filter Option.isSome).length
    body := .split keys values
    nextId := 2 }

/-- `new_dict_with_shared_keys` (:896-909). -/
def newDictWithSharedKeys (id : Nat) (keys : Keys K Unit) : PyDict K V :=
  { ident := id, used := 0, nextId := 2
    body := .split keys (Values.new (sharedKeysUsableSize keys)) }

/-- `_PyObject_MaterializeManagedDict_LockHeld` (:6873-6893),
`_PyObject_MaterializeManagedDict` (:6895-6919). -/
def materializeManagedDict : IM K V (PyDict K V) := do
  let s ← M.get
  match s.inst.dict with
  | some d => return d
  | none =>
    let d : PyDict K V :=
      if s.inst.inlineV.valid then makeDictFromInstanceAttributes s.nextDict s.keys s.inst.inlineV
      else { ident := s.nextDict }
    M.put { s with inst := { s.inst with dict := some d }, nextDict := s.nextDict + 1 }
    return d

/-- `ensure_managed_dict` (:7541-7572), `PyObject_GenericGetDict` (:7606-7623) for a type with a
managed dict; `ensure_nonmanaged_dict` (:7574-7604) is this minus the inline branch. -/
def ensureManagedDict : IM K V (PyDict K V) := do
  let s ← M.get
  match s.inst.dict with
  | some d => return d
  | none =>
    if s.inst.inlineV.valid then materializeManagedDict
    else
      let d : PyDict K V := newDictWithSharedKeys s.nextDict s.keys
      M.put { s with inst := { s.inst with dict := some d }, nextDict := s.nextDict + 1 }
      return d

section
variable [DecidableEq K] (P : Proto K (PyDict K V))

/-- `_PyDict_SetItem_LockHeld` (:6921-6934): `value = none` deletes. -/
def dictSetItemLockHeld (name : K) (value : Option V) : DM K V Unit :=
  match value with
  | none => do
    let hash ← hashKey P name
    dictDelItemKnownHash P name hash
  | some v => dictSetItem P name v

/-- The fast path of `store_instance_attr_lock_held` (:7003-7033), when the key is in the
shared keys at `ix`. The inline values are the dict's if a dict is attached. -/
def storeAtIndex (tpName : String) (name : K) (value : Option V) (ix : Nat) : IM K V Unit := do
  let s ← M.get
  let values := s.inst.values
  let old := values.get ix
  match old, value with
  | none, none =>
    M.throw (attributeError s!"'{tpName}' object has no attribute {P.reprStr name}")
  | _, _ =>
    let v1 := values.set ix value
    let v2 := match old, value with
      | none, _ => v1.addToOrder ix
      | some _, none => v1.deleteIndex ix
      | some _, some _ => v1
    let delta : Int := match old, value with
      | none, _ => 1
      | some _, none => -1
      | some _, some _ => 0
    let dict' := s.inst.dict.map fun d =>
      match d.body with
      | .split k _ =>
        { d with body := .split k v2, used := ((d.used : Int) + delta).toNat }
      | .combined _ => d
    M.put { s with inst := { s.inst with inlineV := v2, dict := dict' } }

/-- `store_instance_attr_lock_held` (:6939-7035). -/
def storeInstanceAttr (tpName : String) (name : K) (value : Option V) : IM K V Unit := do
  let s ← M.get
  let ix ← (if P.isStr name then do
      let hash ← M.lift (P.hash name)
      let (ix, keys') ← M.lift (insertSplitKey P s.keys name hash)
      M.put { s with keys := keys' }
      pure ix
    else pure DKIX_EMPTY)
  if ix == DKIX_EMPTY then
    let s ← M.get
    match s.inst.dict with
    | none =>
      -- Make the dict but don't publish it until the store has worked (:6978-6991).
      let d : PyDict K V := makeDictFromInstanceAttributes s.nextDict s.keys s.inst.inlineV
      match dictSetItemLockHeld P name value d with
      | (.error e, _) => M.throw e
      | (.ok _, d') =>
        M.put { (syncDict true d' s) with nextDict := s.nextDict + 1 }
    | some d => onInstDict (dictSetItemLockHeld P name value) d
  else
    storeAtIndex P tpName name value ix.toNat

/-- `store_instance_attr_dict` (:7037-7051). -/
def storeInstanceAttrDict (tpName : String) (d : PyDict K V) (name : K) (value : Option V) :
    IM K V Unit :=
  if isInlineDict d then storeInstanceAttr P tpName name value
  else onInstDict (dictSetItemLockHeld P name value) d

/-- `_PyObject_StoreInstanceAttribute` (:7053-7101). -/
def storeInstanceAttribute (tpName : String) (name : K) (value : Option V) : IM K V Unit := do
  let s ← M.get
  if !s.inst.values.valid then
    let d ← ensureManagedDict
    storeInstanceAttrDict P tpName d name value
  else
    storeInstanceAttr P tpName name value

/-- `_PyDictKeys_StringLookupSplit` (:1216-1230). -/
def dictKeysStringLookupSplit (keys : Keys K Unit) (key : K) : Py Int :=
  match P.hash key with
  | .error _ => .ok (-3)
  | .ok hash => unicodekeysLookupUnicode P keys key hash

/-- `_PyObject_TryGetInstanceAttribute` (:7136-7213): `none` is "ask the dict", `some r` is the
answer from the inline values, with `r = none` meaning the attribute is absent. -/
def tryGetInstanceAttribute (s : ObjSt K V) (name : K) : Py (Option (Option V)) :=
  let values := s.inst.values
  if !values.valid then .ok none
  else
    match dictKeysStringLookupSplit P s.keys name with
    | .error e => .error e
    | .ok ix =>
      if ix == DKIX_EMPTY then .ok (some none)
      else .ok (some (values.get ix.toNat))

end

/-- The instance branch of `_PyObject_GenericGetAttrWithDict` (`Objects/object.c:1856-1870`),
what `getattr` runs. It is not a pure read: a name that is not an exact `str`, or inline values
that are no longer valid, materialize the dict, as a plain empty dict in the second case. -/
def genericGetAttr [DecidableEq K] (P : Proto K (PyDict K V)) (name : K) : IM K V (Option V) := do
  let viaDict : IM K V (Option V) := do
    let d ← materializeManagedDict
    let s ← M.get
    M.lift ((pyDictGetItemRef P true name (refreshKeys s.keys d)).1)
  if P.isStr name then
    let s ← M.get
    match ← M.lift (tryGetInstanceAttribute P s name) with
    | some r => return r
    | none => viaDict
  else viaDict

/-- `_PyObject_IsInstanceDictEmpty` (:7215-7247), for a type with inline values. -/
def isInstanceDictEmpty (s : ObjSt K V) : Bool :=
  let values := s.inst.values
  if values.valid then
    (values.values.take s.keys.nentries).all Option.isNone
  else
    match s.inst.dict with
    | none => true
    | some d => d.used == 0

/-- `detach_dict_from_object` (:7455-7485), `_PyDict_DetachFromObject` (:7533-7539). -/
def detachDictFromObject (s : ObjSt K V) (d : PyDict K V) : ObjSt K V × PyDict K V :=
  if !isInlineDict d then (s, d)
  else
    match d.body with
    | .split k v =>
      let d' := { d with body := .split k (copyValues v) }
      ({ s with inst := { s.inst with inlineV := invalidateInline v, dict := some d' } }, d')
    | .combined _ => (s, d)

/-- `set_dict_inline_values` (:7285-7296). -/
def setDictInlineValues (s : ObjSt K V) (new : Option (PyDict K V)) : ObjSt K V :=
  let v := s.inst.inlineV
  { s with inst := { inlineV := if v.valid then invalidateInline v else v, dict := new } }

/-- `_PyObject_SetManagedDict` (:7373-7453), the GIL inline-values branch: `o.__dict__ = new`,
`del o.__dict__`. -/
def setManagedDict (s : ObjSt K V) (new : Option (PyDict K V)) : ObjSt K V :=
  match s.inst.dict with
  | none => setDictInlineValues s new
  | some d =>
    let (s', _) := detachDictFromObject s d
    { s' with inst := { s'.inst with dict := new } }

/-- `PyObject_ClearManagedDict` (:7488-7531), run when the instance dies: the dict, if anyone
else holds it, keeps its contents, detached. -/
def clearManagedDict (s : ObjSt K V) : ObjSt K V × Option (PyDict K V) :=
  match s.inst.dict with
  | none =>
    ({ s with inst := { s.inst with inlineV := invalidateInline s.inst.inlineV } }, none)
  | some d =>
    let (s', d') := detachDictFromObject s d
    ({ s' with inst := { s'.inst with dict := none } }, some d')

end PyLean.DictSet
