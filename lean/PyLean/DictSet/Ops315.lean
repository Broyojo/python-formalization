import PyLean.DictSet.Views

/-!
Bodies of `Objects/dictobject.c` (CPython 3.15.2) that run Python code in the middle and read
the tables again afterwards: `fromkeys`, `copy`, `|`, `==`, `repr`, and the C API entry points
around `pop`, `setdefault` and `update`. Line numbers refer to `Objects/dictobject.c`.

Where C reads a second dict while callbacks run (the source of `fromkeys`, the left operand of
`==`), that dict is the `peer` of the state, as in `dict_dict_merge`: a key's `__eq__` or a value's
`__eq__` can change it, and the loop reads it again at the next step. When the two are one object
(`d == d`, or `cls()` returning the iterable itself), the loop reads the state itself (`alias`).
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type}

section
variable [DecidableEq K] (P : Proto K (PyDict K V))

/-! ## `pop` -/

/-- `PyDict_PopString` (:3325-3339): `PyUnicode_FromString` may fail, and then `*result` is NULL
and the dict is not touched. -/
def pyDictPopString (isAny : Bool) (mk : Py K) : DM K V (Option V) := fun mp =>
  match mk with
  | .error e => (.error e, mp)
  | .ok k => pyDictPop P isAny k mp

/-! ## `setdefault` through the C API -/

/-- `PyDict_SetDefaultRef` (:4873-4882): `dict_setdefault_ref_lock_held` with `incref_result` 1
and a `result` pointer. -/
def pyDictSetDefaultRef (isAny : Bool) (key : K) (dflt : V) : DM K V (Nat × Option V) :=
  dictSetdefaultRefChecked P isAny key dflt true true

/-- `PyDict_SetDefault` (:4884-4892): the status is dropped and `result` is returned as it is, a
borrowed reference; `none` is NULL. With an exception set, NULL is the error result here. -/
def pyDictSetDefaultC (isAny : Bool) (key : K) (dflt : V) : DM K V (Option V) := do
  let r ← dictSetdefaultRefChecked P isAny key dflt true false
  return r.2

/-! ## `update` and the C API merges -/

/-- `dict_update` (:4033-4039): `dict_update_common(self, args, kwds, "update")`. -/
def dictUpdate (args : List (UpdateArg K V)) (kwds : Option (PyDict K V)) : DM K V Unit :=
  dictUpdateCommon P args kwds "update"

/-- `PyDict_Update` (:4379-4383): `dict_merge_api(a, b, 1, NULL)`. -/
def pyDictUpdate (aIsAny : Bool) (b : Option (MergeObj K V)) : DM K V Unit :=
  dictMergeChecked P aIsAny b 1

/-- `PyDict_Merge` (:4385-4390): `dict_merge_api(a, b, override != 0, NULL)`; every override but
0 is 1, so 2 overwrites like 1 does. -/
def pyDictMerge (aIsAny : Bool) (b : Option (MergeObj K V)) (override : Int) : DM K V Unit :=
  dictMergeChecked P aIsAny b (if override != 0 then 1 else 0)

/-- `_PyDict_MergeUniq` (:4392-4396): `dict_merge_api(a, b, 2, dupkey)`, the `f(**a, **b)` merge. -/
def pyDictMergeUniq (aIsAny : Bool) (b : Option (MergeObj K V)) : DM K V Unit :=
  dictMergeChecked P aIsAny b 2

/-- `dict_merge_from_seq2` (:4140-4149), the critical section around
`merge_from_seq2_lock_held`, which `dict_update_arg` calls. -/
def dictMergeFromSeq2Locked (seq2 : ReIter (PyDict K V) (Seq2Item K V)) (override : Bool) :
    DM K V Unit :=
  mergeFromSeq2 P seq2 override

/-- `PyDict_MergeFromSeq2` (:4151-4167): `dict_merge_from_seq2` after the `PyDict_Check`. -/
def pyDictMergeFromSeq2C (isAny : Bool) (seq2 : ReIter (PyDict K V) (Seq2Item K V))
    (override : Bool) : DM K V Unit := fun mp =>
  if !isAny then (.error badInternalCall, mp)
  else if mp.frozen then (.error (frozendictNoSupport "assignment"), mp)
  else dictMergeFromSeq2Locked P seq2 override mp

/-! ## `copy` -/

/-- `copy_lock_held_untracked(o, as_frozendict)` (:4432-4546). `iterIsDict` is
`Py_TYPE(mp)->tp_iter == dict_iter`; with it overridden the last route is the slow path of
`dict_merge`, through `asMap` (`o.keys()` and `o[key]`). The copy is new, with identity `id`,
and a frozendict exactly when `asFrozen`. On the merge route a key's `__eq__` can change the
source, which the loop of `dict_dict_merge` then reads (`peer`). -/
def copyLockHeldUntracked (mp : PyDict K V) (id : Nat) (asFrozen iterIsDict : Bool)
    (asMap : MergeArg K V) : Py (PyDict K V) :=
  if mp.used == 0 then
    -- The dict is empty; just return a new dict (:4444-4455).
    .ok { ident := id, nextId := mp.nextId, frozen := asFrozen }
  else
    match mp.body with
    | .split k v =>
      -- :4457-4488: the shared keys and a copy of the values.
      .ok { ident := id, used := mp.used, body := .split k (copyValues v), nextId := mp.nextId,
            frozen := asFrozen }
    | .combined k =>
      if iterIsDict && decide (mp.used ≥ k.nentries * 2 / 3) then
        -- :4490-4529: fast copy, `clone_combined_dict_keys`.
        .ok { ident := id, used := mp.used, nextId := mp.nextId + 1, frozen := asFrozen
              body := .combined (cloneCombinedDictKeys mp.nextId k) }
      else
        -- :4531-4545: `dict_merge(copy, o, 1, NULL)` into an empty dict or frozendict.
        let arg : MergeArg K V := if iterIsDict then .dict mp else asMap
        match dictMerge P arg 1 { ident := id, nextId := mp.nextId, frozen := asFrozen } with
        | (.ok _, d) => .ok { d with peer := none }
        | (.error e, _) => .error e

/-- `PyDict_Copy` (:4548-4564): only a dict, not a frozendict, gets past `PyDict_Check`. -/
def pyDictCopyC (isAny : Bool) (mp : PyDict K V) (id : Nat) (iterIsDict : Bool)
    (asMap : MergeArg K V) : Py (PyDict K V) :=
  if !isAny || mp.frozen then .error badInternalCall
  else copyLockHeldUntracked P mp id false iterIsDict asMap

/-- `dict_copy_impl` (:4404-4408): `dict.copy`, which is `PyDict_Copy(self)`. -/
def dictCopyImpl (self : PyDict K V) (id : Nat) (iterIsDict : Bool) (asMap : MergeArg K V) :
    Py (PyDict K V) :=
  pyDictCopyC P true self id iterIsDict asMap

/-- `anydict_copy_untracked` (:4566-4583): a frozendict gives a frozendict. -/
def anydictCopyUntracked (o : PyDict K V) (id : Nat) (iterIsDict : Bool) (asMap : MergeArg K V) :
    Py (PyDict K V) :=
  if o.frozen then copyLockHeldUntracked P o id true iterIsDict asMap
  else copyLockHeldUntracked P o id false iterIsDict asMap

/-- `_PyDict_CopyAsDict` (:4585-4602): always a dict. -/
def dictCopyAsDict (o : PyDict K V) (id : Nat) (iterIsDict : Bool) (asMap : MergeArg K V) :
    Py (PyDict K V) :=
  if o.frozen then copyLockHeldUntracked P o id false iterIsDict asMap
  else copyLockHeldUntracked P o id false iterIsDict asMap

/-- `frozendict_copy_impl` (:8520-8535): an exact frozendict is its own copy; an instance of a
subclass is copied into an exact frozendict. -/
def frozendictCopyImpl (self : PyDict K V) (exact : Bool) (id : Nat) (iterIsDict : Bool)
    (asMap : MergeArg K V) : Py (PyDict K V) :=
  if exact then .ok self else anydictCopyUntracked P self id iterIsDict asMap

/-! ## `|` and `|=` -/

/-- `_PyDict_Or` (:5150-5166): `none` is `NotImplemented`. The copy is `anydict_copy_untracked`, so
the result is a frozendict exactly when `self` is; then `dict_update_arg(new, other)`. -/
def pyDictOr (selfIsAny otherIsAny : Bool) (self : PyDict K V) (id : Nat) (selfIterIsDict : Bool)
    (selfMap : MergeArg K V) (otherArg : UpdateArg K V) : Py (Option (PyDict K V)) :=
  if !selfIsAny || !otherIsAny then .ok none
  else
    match anydictCopyUntracked P self id selfIterIsDict selfMap with
    | .error e => .error e
    | .ok new =>
      match dictUpdateArg P otherArg new with
      | (.ok _, d) => .ok (some { d with peer := none })
      | (.error e, _) => .error e

/-- An operand of `frozendict_or`, as its tests read it. -/
structure OrOperand (K V : Type) where
  /-- `PyAnyDict_Check`. -/
  isAny : Bool
  /-- `PyAnyDict_CheckExact`: an exact `dict` or `frozendict`. -/
  exact : Bool
  d : PyDict K V

/-- `frozendict_or` (:5168-5188), `nb_or` of `frozendict`. Either operand may be anything, since a
reflected `|` lands here too. -/
def frozendictOr315 (self other : OrOperand K V) (id : Nat) (selfIterIsDict : Bool)
    (selfMap : MergeArg K V) (otherArg : UpdateArg K V) : Py (Option (PyDict K V)) :=
  if self.isAny && self.exact && self.d.frozen then
    -- frozendict() | frozendict(...) => frozendict(...)
    if self.d.used == 0 && other.isAny && other.exact && other.d.frozen then .ok (some other.d)
    -- frozendict(...) | frozendict() => frozendict(...)
    else if other.isAny && other.exact && other.d.used == 0 then .ok (some self.d)
    else pyDictOr P self.isAny other.isAny self.d id selfIterIsDict selfMap otherArg
  else pyDictOr P self.isAny other.isAny self.d id selfIterIsDict selfMap otherArg

/-- `_PyDict_IOr` (:5190-5198): `dict_update_arg(self, other)`, then `self`. -/
def pyDictIOr (other : UpdateArg K V) : DM K V (PyDict K V) := do
  dictUpdateArg P other
  let d ← M.get
  return d

/-! ## `==` -/

/-- The dict read as `a` while `dict_equal_lock_held` runs on `b`: the state itself when they are
one object, its `peer` otherwise. -/
def eqLeft (alias : Bool) (b : PyDict K V) : Option (PyDict K V) :=
  if alias then some b else b.peer.map (·.toDict)

/-- Entry `i` of `a` as the loop of `dict_equal_lock_held` reads it (:4636-4653): the key and hash
of `dk_entries[i]`, and the value from `ma_values` for a split table, from the entry otherwise.
`none` is a NULL key. -/
def eqEntry (a : PyDict K V) (i : Nat) : Option (K × Option V × Int) :=
  match a.body.entryKH i with
  | none => none
  | some (key, hash) => some (key, a.body.valueAt i, hash)

/-- The loop of `dict_equal_lock_held` (:4633-4679). The bound `LOAD_KEYS_NENTRIES(a->ma_keys)` and
the entry are read from `a` as it is now, so what a comparison did to `a` shows at the next step.
`veq` is `PyObject_RichCompareBool(aval, bval, Py_EQ)`, a callback that may raise and change either
dict. Running out of `fuel` is a limit of the model. -/
def dictEqualLive (veq : V → V → DM K V Bool) (alias : Bool) : Nat → Nat → DM K V Bool
  | 0, _ => M.throw .modelFuel
  | fuel + 1, i => fun b =>
    match eqLeft alias b with
    | none => (.error .modelFuel, b)
    | some a =>
      if i ≥ a.body.nentries then (.ok true, b)
      else
        match eqEntry a i with
        | none => dictEqualLive veq alias fuel (i + 1) b
        | some (_, none, _) => dictEqualLive veq alias fuel (i + 1) b
        | some (key, some aval, hash) =>
          -- reuse the known hash value (:4662-4663)
          match dictLookup P key hash b with
          | (.error e, s) => (.error e, s)
          | (.ok (_, none), s) => (.ok false, s)
          | (.ok (_, some bval), s) =>
            match veq aval bval s with
            | (.error e, s') => (.error e, s')
            | (.ok false, s') => (.ok false, s')
            | (.ok true, s') => dictEqualLive veq alias fuel (i + 1) s'

/-- `dict_equal_lock_held` (:4621-4681) and `dict_equal` (:4683-4692), on state `b` with `a` in
`peer` (or `b` itself when `alias`). -/
def dictEqual315 (veq : V → V → DM K V Bool) (alias : Bool) (fuel : Nat) : DM K V Bool := fun b =>
  match eqLeft alias b with
  | none => (.error .modelFuel, b)
  | some a =>
    if a.used != b.used then (.ok false, b)
    else dictEqualLive P veq alias fuel 0 b

/-- `dict_richcompare` (:4694-4712): `none` is `NotImplemented`. -/
def dictRichcompare315 (vIsAny wIsAny : Bool) (op : CmpOp) (veq : V → V → DM K V Bool)
    (alias : Bool) (fuel : Nat) : DM K V (Option Bool) :=
  if !vIsAny || !wIsAny then pure none
  else if op == .eq || op == .ne then do
    let cmp ← dictEqual315 P veq alias fuel
    return some (cmp == (op == .eq))
  else pure none

/-! ## `fromkeys` -/

/-- The loop of `dict_dict_fromkeys` (:3380-3385): `_PyDict_Next` on the iterable as it is now,
`insertdict` with the stored hash. Unlike `dict_dict_merge` there is no count test. -/
def fromkeysLive (value : V) (alias : Bool) : Nat → Int → DM K V Unit
  | 0, _ => M.throw .modelFuel
  | fuel + 1, pos => fun mp =>
    match eqLeft alias mp with
    | none => (.error .modelFuel, mp)
    | some src =>
      match dictNext src pos with
      | none => (.ok (), mp)
      | some (pos', key, _, hash) =>
        match insertDict P key hash value mp with
        | (.error e, s) => (.error e, s)
        | (.ok _, s) => fromkeysLive value alias fuel pos' s

/-- More steps than the iterable of `dict_dict_fromkeys` has at the start. -/
def fromkeysFuel (src : PyDict K V) : Nat :=
  src.body.nentries + src.used + 2 ^ src.body.log2Size + 64

/-- `dict_dict_fromkeys` (:3362-3387), from an exact dict or an exact frozendict `src`. -/
def dictDictFromkeys (src : PyDict K V) (value : V) : DM K V Unit := fun mp =>
  let alias := src.ident == mp.ident
  let unicode := src.body.isUnicode
  let newSize := max (estimateLog2Keysize src.used) mp.body.log2Size
  match dictResize newSize unicode mp with
  | (.error e, s) => (.error e, s)
  | (.ok _, s) =>
    let s := if alias then s else { s with peer := some src.toPeer }
    fromkeysLive P value alias (fromkeysFuel src) 0 s

/-- `dict_set_fromkeys` (:3389-3413), from an exact set or frozenset of `size` entries, `es` in table
order. The set is read as it stood at the start: a callback that changes it while it is read is out
of the model. -/
def dictSetFromkeys (size : Nat) (es : List (K × Int)) (value : V) : DM K V Unit := do
  let mp ← M.get
  dictResize (max (estimateLog2Keysize size) mp.body.log2Size) false
  fromkeysLoop P value es

/-- An object `cls()` may return, as `_PyDict_FromKeys` tests it. -/
structure FkObj (K V : Type) where
  /-- The dict part; `d.frozen` is `PyFrozenDict_Check`. For an object that is no dict only
  `d.ident` means anything. -/
  d : PyDict K V
  /-- `PyAnyDict_Check`. -/
  isAny : Bool := true
  /-- The type is exactly `dict` or `frozendict`. -/
  exact : Bool := true
  /-- `_PyObject_GC_IS_TRACKED`. -/
  tracked : Bool := true
  /-- `Py_TYPE(d)->tp_iter == dict_iter`. -/
  iterIsDict : Bool := true
  deriving Inhabited

namespace FkObj
def dictExact (o : FkObj K V) : Bool := o.isAny && !o.d.frozen && o.exact
def frozenExact (o : FkObj K V) : Bool := o.isAny && o.d.frozen && o.exact
def frozenAny (o : FkObj K V) : Bool := o.isAny && o.d.frozen
end FkObj

/-- `cls` of `_PyDict_FromKeys`. Calling it runs Python code. -/
structure FkCls (K V : Type) where
  /-- `cls == (PyObject*)&PyFrozenDict_Type`. -/
  isFrozendictType : Bool
  /-- `_PyObject_CallNoArgs(cls)`. -/
  call : Py (FkObj K V)
  /-- `_PyObject_CallOneArg(cls, d)`. -/
  callWith : FkObj K V → Py (FkObj K V)
  /-- `PyObject_SetItem(d, key, value)` on what is neither an exact dict nor a frozendict. -/
  setItem : K → V → DM K V Unit
  /-- `PyMapping_Keys` and `PyObject_GetItem` on an instance whose `tp_iter` is overridden. -/
  instMap : MergeArg K V

/-- The iterable of `_PyDict_FromKeys`: the branch it takes, and what `PyObject_GetIter` and
`PyIter_NextItem` give, which may raise and may change the dict being filled. -/
inductive FkFast (K V : Type) where
  /-- `PyDict_CheckExact(iterable)` or `PyFrozenDict_CheckExact(iterable)`. -/
  | dict (src : PyDict K V)
  /-- `PyAnySet_CheckExact(iterable)`: its size and `(key, hash)` in table order. -/
  | set (size : Nat) (es : List (K × Int))

structure FkIter (K V : Type) where
  fast : Option (FkFast K V)
  iter : ReIter (PyDict K V) K

/-- `frozendict_new_untracked(&PyFrozenDict_Type)` (:8454-8466). -/
def frozendictNewUntracked (id : Nat) : FkObj K V :=
  { d := { ident := id, frozen := true }, tracked := false }

/-- The loops of `_PyDict_FromKeys` over `PyIter_NextItem` (:3510-3575), with the store of the
branch: `setitem_lock_held`, `setitem_take2_lock_held` or `PyObject_SetItem`. -/
def fromkeysIterLoop (store : K → DM K V Unit) : List (DM K V (Option K)) → DM K V Unit
  | [] => pure ()
  | step :: rest => do
    match ← step with
    | none => pure ()
    | some key =>
      store key
      fromkeysIterLoop store rest

/-- `_PyDict_FromKeys` (:3415-3600), behind `dict.fromkeys` and `frozendict.fromkeys`
(`dict_fromkeys_impl`, :3983-3988). The result, and the objects the function hands to Python
code: the one argument of `cls(d)` at :3593, if that call is made. -/
def pyDictFromKeys (cls : FkCls K V) (iterable : FkIter K V) (value : V) (id : Nat) :
    Py (FkObj K V) × List (FkObj K V) :=
  -- :3423-3433
  let made : Py (FkObj K V) :=
    if cls.isFrozendictType then .ok (frozendictNewUntracked id) else cls.call
  match made with
  | .error e => (.error e, [])
  | .ok d0 =>
    -- :3443-3455: a tracked frozendict is replaced by an untracked copy.
    let copied : Py (FkObj K V × Bool) :=
      if d0.frozenAny && d0.tracked then
        let arg : MergeArg K V := if d0.iterIsDict then .dict d0.d else cls.instMap
        match dictMerge P arg 1 { ident := id + 1, frozen := true } with
        | (.ok _, c) => .ok ({ d := { c with peer := none }, tracked := false }, true)
        | (.error e, _) => .error e
      else .ok (d0, false)
    match copied with
    | .error e => (.error e, [])
    | .ok (d, needCopy) =>
      -- `peer` of the result holds the iterable as the callbacks left it, for the caller.
      let run (m : DM K V Unit) : Py (FkObj K V) :=
        match m d.d with
        | (.ok _, x) => .ok { d with d := x }
        | (.error e, _) => .error e
      let fast : Option (DM K V Unit) :=
        if d.dictExact || d.frozenExact then
          match iterable.fast with
          | some (.dict src) => some (dictDictFromkeys P src value)
          | some (.set size es) => some (dictSetFromkeys P size es value)
          | none => none
        else none
      let filled : Py (FkObj K V) :=
        match fast with
        | some m => run m
        | none =>
          let store : K → DM K V Unit :=
            if d.dictExact || d.frozenAny then fun key => dictSetItem P key value
            else fun key => cls.setItem key value
          run (do
            iterable.iter.getIter
            fromkeysIterLoop store iterable.iter.steps)
      match filled with
      | .error e => (.error e, [])
      | .ok d' =>
        -- Done (:3587-3599)
        if needCopy then (cls.callWith d', [d'])
        else (.ok (if d'.tracked then d' else { d' with tracked := true }), [])

/-- `dict_fromkeys_impl` (:3983-3988), the classmethod `fromkeys`. -/
def dictFromkeysImpl (cls : FkCls K V) (iterable : FkIter K V) (value : V) (id : Nat) :
    Py (FkObj K V) × List (FkObj K V) :=
  pyDictFromKeys P cls iterable value id

end

/-! ## `repr` -/

/-- The loop of `anydict_repr_impl` (:3670-3708): `_PyDict_Next` on the dict as the last `repr`
left it. `krepr`/`vrepr` are `PyObject_Repr`, which may raise and may change the dict ("Note that
repr may mutate the dict", :3668-3669). -/
def anydictReprLoop (krepr : K → DM K V String) (vrepr : V → DM K V String) :
    Nat → Int → Bool → String → DM K V String
  | 0, _, _, _ => M.throw .modelFuel
  | fuel + 1, i, first, acc => fun mp =>
    match dictNext mp i with
    | none => (.ok (acc ++ "}"), mp)
    | some (i', key, value, _) =>
      let acc := if first then acc else acc ++ ", "
      match krepr key mp with
      | (.error e, s) => (.error e, s)
      | (.ok ks, s) =>
        match vrepr value s with
        | (.error e, s') => (.error e, s')
        | (.ok vs, s') => anydictReprLoop krepr vrepr fuel i' false (acc ++ ks ++ ": " ++ vs) s'

/-- `anydict_repr_impl` (:3641-3724), `dict_repr_lock_held` and `dict_repr` (:3726-3741).
`reprEnter` is `Py_ReprEnter(self)`: `true` when `self` is already being printed further up. -/
def anydictRepr (reprEnter : Py Bool) (krepr : K → DM K V String) (vrepr : V → DM K V String)
    (fuel : Nat) : DM K V String := fun mp =>
  match reprEnter with
  | .error e => (.error e, mp)
  | .ok true => (.ok "{...}", mp)
  | .ok false =>
    if mp.used == 0 then (.ok "{}", mp)
    else anydictReprLoop krepr vrepr fuel 0 true "{" mp

/-- `frozendict_repr` (:8341-8359): `tpName` is `Py_TYPE(self)->tp_name`. -/
def frozendictRepr315 (tpName : String) (reprEnter : Py Bool) (krepr : K → DM K V String)
    (vrepr : V → DM K V String) (fuel : Nat) : DM K V String := fun mp =>
  if mp.used == 0 then (.ok s!"{tpName}()", mp)
  else
    match anydictRepr reprEnter krepr vrepr fuel mp with
    | (.error e, s) => (.error e, s)
    | (.ok r, s) => (.ok s!"{tpName}({r})", s)

/-- The pairs `k: v`, separated by `", "`, the first one with no separator when `first`. -/
def reprTail (kr : K → String) (vr : V → String) : Bool → List (K × V × Int) → String
  | _, [] => ""
  | first, e :: rest =>
    (if first then "" else ", ") ++ kr e.1 ++ ": " ++ vr e.2.1 ++ reprTail kr vr false rest

/-- What `repr` writes for a list of items whose reprs do not touch the dict. -/
def reprRender (kr : K → String) (vr : V → String) (items : List (K × V × Int)) : String :=
  "{" ++ reprTail kr vr true items ++ "}"

end PyLean.DictSet
