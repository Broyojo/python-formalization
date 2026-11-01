import PyLean.DictSet.Views

/-!
`Objects/odictobject.c` (CPython 3.14.7): the doubly linked list of nodes on top of a dict,
`od_fast_nodes`, and the iterator. Line numbers refer to `Objects/odictobject.c`.

The list is `nodes`, first to last; node pointers are `Node.id`. `od_fast_nodes` mirrors the
dict's entry table by index. The dict underneath stays reachable, so `dict.__delitem__(od, k)`
and `dict.popitem(od)` are ordinary operations here, and the state where list and dict
disagree can be reached and reasoned about.
-/

namespace PyLean.DictSet

open PyLean

structure Node (K : Type) where
  id : Nat
  key : K
  hash : Int
  deriving Repr, Inhabited, DecidableEq

/-- `PyODictObject` (:489-503). `sentinel` is `od_resize_sentinel`, `none` is NULL. -/
structure ODict (K V : Type) where
  d : PyDict K V
  nodes : List (Node K) := []
  fastNodes : List (Option (Node K)) := []
  fastSize : Nat := 0
  sentinel : Option Nat := none
  state : Nat := 0
  nextNode : Nat := 0
  /-- `PyODict_CheckExact`. -/
  exact : Bool := true
  deriving Repr, Inhabited

abbrev OM (K V : Type) := M (ODict K V)

variable {K V : Type}

/-- Run a dict operation on the underlying dict. -/
def onDict {α : Type} (m : DM K V α) : OM K V α := fun od =>
  match m od.d with
  | (r, d') => (r, { od with d := d' })

/-- `_odict_EMPTY(od)` (:531): the list is empty, whatever the dict holds. -/
def ODict.isEmpty (od : ODict K V) : Bool := od.nodes.isEmpty

section
variable [DecidableEq K] (P : Proto K (PyDict K V))

/-- `_odict_get_index_raw` (:536-556). An exception is the `-1` return. -/
def odictGetIndexRaw (key : K) (hash : Int) : OM K V Nat := do
  let r ← onDict (dictLookup P key hash)
  if r.1 == DKIX_EMPTY then
    let od ← M.get
    return od.d.body.nentries
  return r.1.toNat

/-- The loop of `_odict_resize` (:579-587). -/
def odictResizeLoop : List (Node K) → List (Option (Node K)) → OM K V (List (Option (Node K)))
  | [], fast => pure fast
  | node :: rest, fast => do
    let i ← odictGetIndexRaw P node.key node.hash
    odictResizeLoop rest (fast.set i (some node))

/-- `_odict_resize` (:561-595). -/
def odictResize : OM K V Unit := do
  let od ← M.get
  let size := 2 ^ od.d.body.log2Size
  let fast ← odictResizeLoop P od.nodes (List.replicate size none)
  let od ← M.get
  M.put { od with fastNodes := fast, fastSize := size, sentinel := some od.d.body.ident }

/-- `_odict_get_index` (:598-616). -/
def odictGetIndex (key : K) (hash : Int) : OM K V Nat := do
  let od ← M.get
  let keys := od.d.body
  if od.sentinel != some keys.ident || od.fastSize != 2 ^ keys.log2Size then
    odictResize P
  odictGetIndexRaw P key hash

/-- `od_fast_nodes[i]`. -/
def ODict.fastAt (od : ODict K V) (i : Nat) : Option (Node K) := (od.fastNodes[i]?).join

/-- `_odict_find_node_hash` (:619-632). -/
def odictFindNodeHash (key : K) (hash : Int) : OM K V (Option (Node K)) := do
  let od ← M.get
  if od.isEmpty then return none
  let index ← odictGetIndex P key hash
  let od ← M.get
  return od.fastAt index

/-- `_odict_find_node` (:634-651). -/
def odictFindNode (key : K) : OM K V (Option (Node K)) := do
  let od ← M.get
  if od.isEmpty then return none
  let hash ← M.lift (P.hash key)
  let index ← odictGetIndex P key hash
  let od ← M.get
  return od.fastAt index

end

/-- `_odict_add_head` (:653-665). -/
def odictAddHead (od : ODict K V) (node : Node K) : ODict K V :=
  { od with nodes := node :: od.nodes, state := od.state + 1 }

/-- `_odict_add_tail` (:667-679). -/
def odictAddTail (od : ODict K V) (node : Node K) : ODict K V :=
  { od with nodes := od.nodes ++ [node], state := od.state + 1 }

/-- `_odict_remove_node` (:727-744). -/
def odictRemoveNode [DecidableEq K] (od : ODict K V) (node : Node K) : ODict K V :=
  { od with nodes := od.nodes.filter (fun n => n.id != node.id), state := od.state + 1 }

/-- `_odict_clear_nodes` (:795-814). -/
def odictClearNodes (od : ODict K V) : ODict K V :=
  { od with fastNodes := [], fastSize := 0, sentinel := none, nodes := [], state := od.state + 1 }

section
variable [DecidableEq K] (P : Proto K (PyDict K V))

/-- `_odict_add_new_node` (:682-717). -/
def odictAddNewNode (key : K) (hash : Int) : OM K V Unit := do
  let i ← odictGetIndex P key hash
  let od ← M.get
  if (od.fastAt i).isSome then return ()
  let node : Node K := ⟨od.nextNode, key, hash⟩
  let od' := odictAddTail { od with nextNode := od.nextNode + 1 } node
  M.put { od' with fastNodes := od'.fastNodes.set i (some node) }

/-- `_odict_clear_node` (:762-793). -/
def odictClearNode (node : Option (Node K)) (key : K) (hash : Int) : OM K V Unit := do
  let od ← M.get
  if od.isEmpty then return ()
  let i ← odictGetIndex P key hash
  let od ← M.get
  match (match node with
         | some n => some n
         | none => od.fastAt i) with
  | none => return ()
  | some n =>
    let od' := odictRemoveNode od n
    M.put { od' with fastNodes := od'.fastNodes.set i none }

/-- `_PyODict_SetItem_KnownHash_LockHeld` (:1638-1654). -/
def odictSetItemKnownHash (key : K) (value : V) (hash : Int) : OM K V Unit := do
  onDict (dictSetItemKnownHash P key value hash)
  odictAddNewNode P key hash

/-- `PyODict_SetItem_LockHeld` (:1657-1666), `PyODict_SetItem` (:1668-1676). -/
def odictSetItem (key : K) (value : V) : OM K V Unit := do
  let hash ← M.lift (P.hash key)
  odictSetItemKnownHash P key value hash

/-- `PyODict_DelItem_LockHeld` (:1678-1690), `PyODict_DelItem` (:1692-1700). -/
def odictDelItem (key : K) : OM K V Unit := do
  let hash ← M.lift (P.hash key)
  odictClearNode P none key hash
  onDict (dictDelItemKnownHash P key hash)

/-- `odict_mp_ass_sub` (:873-880). -/
def odictAssSub (key : K) (w : Option V) : OM K V Unit :=
  match w with
  | none => odictDelItem P key
  | some v => odictSetItem P key v

/-- `_odict_popkey_hash` (:1079-1113). `failobj = none` is NULL: line 1098 then runs
`Py_NewRef(NULL)` if the node was found but the dict has no such key, which `dict.popitem(od)`
or `dict.pop(od, k)` can arrange. -/
def odictPopkeyHash (key : K) (failobj : Option V) (hash : Int) : OM K V V := do
  match ← odictFindNodeHash P key hash with
  | some node =>
    odictClearNode P (some node) key hash
    match ← onDict (dictPopKnownHash P key hash) with
    | some v => return v
    | none =>
      match failobj with
      | some f => return f
      | none => M.throw (crash "_odict_popkey_hash: Py_NewRef(NULL)")
  | none =>
    match failobj with
    | some f => return f
    | none => M.throw (keyErr P key)

/-- `OrderedDict.pop` (`OrderedDict_pop_impl`, :1129-1138). -/
def odictPop (key : K) (dflt : Option V) : OM K V V := do
  let hash ← M.lift (P.hash key)
  odictPopkeyHash P key dflt hash

/-- `OrderedDict.popitem` (`OrderedDict_popitem_impl`, :1155-1180). -/
def odictPopitem (last : Bool) : OM K V (K × V) := do
  let od ← M.get
  match (if last then od.nodes.getLast? else od.nodes.head?) with
  | none => M.throw (.keyError "'dictionary is empty'")
  | some node =>
    let value ← odictPopkeyHash P node.key none node.hash
    return (node.key, value)

/-- `OrderedDict.setdefault` (`OrderedDict_setdefault_impl`, :1040-1075). -/
def odictSetdefault (key : K) (dflt : V) : OM K V V := do
  let od ← M.get
  if od.exact then
    match ← onDict (pyDictGetItemWithError P true key) with
    | some v => return v
    | none =>
      odictSetItem P key dflt
      return dflt
  else
    let exists_ ← onDict (pyDictContains P key)
    if exists_ then
      onDict (dictSubscript P none key)
    else
      odictSetItem P key dflt
      return dflt

/-- `OrderedDict.clear` (`OrderedDict_clear_impl`, :1223-1230), and `odict_tp_clear`
(:1492-1501). -/
def odictClear (od : ODict K V) : ODict K V :=
  odictClearNodes { od with d := dictClear od.d }

/-- `OrderedDict.move_to_end` (`OrderedDict_move_to_end_impl`, :1341-1375). -/
def odictMoveToEnd (key : K) (last : Bool) : OM K V Unit := do
  let od ← M.get
  match (if last then od.nodes.getLast? else od.nodes.head?) with
  | none => M.throw (keyErr P key)
  | some endNode =>
    if key != endNode.key then
      match ← odictFindNode P key with
      | none => M.throw (keyErr P key)
      | some node =>
        let od ← M.get
        if last then
          if od.nodes.getLast? != some node then
            M.put (odictAddTail (odictRemoveNode od node) node)
        else
          if od.nodes.head? != some node then
            M.put (odictAddHead (odictRemoveNode od node) node)

/-- `PyODict_New` (:1632-1636). -/
def odictNew (ident : Nat) (exact : Bool := true) : ODict K V :=
  { d := { ident }, exact }

/-- The `_odict_FOREACH` loops of `OrderedDict_copy_impl` (:1261-1295): the state is the
copy; `od` does not change in this model, so the `od_state` check (gh-148660) stays quiet. -/
def odictCopyLoop (od : ODict K V) : List (Node K) → OM K V Unit
  | [] => pure ()
  | node :: rest => do
    match (pyDictGetItemWithError P true node.key od.d).1 with
    | .error e => M.throw e
    | .ok none => M.throw (keyErr P node.key)
    | .ok (some v) =>
      if od.exact then
        odictSetItemKnownHash P node.key v node.hash
      else
        odictSetItem P node.key v
      odictCopyLoop od rest

/-- `OrderedDict.copy` (`OrderedDict_copy_impl`, :1242-1305). -/
def odictCopy (od : ODict K V) (id : Nat) : Py (ODict K V) :=
  match odictCopyLoop P od od.nodes (odictNew id od.exact) with
  | (.ok _, c) => .ok c
  | (.error e, _) => .error e

/-- The loop of `_odict_keys_equal` (:830-863). `state_a`/`state_b` cannot change here. -/
def odictKeysEqualLoop : List (Node K) → List (Node K) → DM K V Bool
  | [], [] => pure true
  | [], _ :: _ => pure false
  | _ :: _, [] => pure false
  | a :: as, b :: bs => do
    let res ← P.eq a.key b.key
    if !res then return false
    odictKeysEqualLoop as bs

/-- `_odict_keys_equal` (:819-864). -/
def odictKeysEqual (a b : ODict K V) : Py Bool :=
  (odictKeysEqualLoop P a.nodes b.nodes a.d).1

/-- `odict_richcompare_lock_held` (:1505-1537), `odict_richcompare` (:1539-1547), with `w`
an `OrderedDict`. -/
def odictRichcompare (veq : V → V → Py Bool) (v w : ODict K V) (ne : Bool) : Py Bool :=
  match (dictRichcompare P veq v.d ne w.d).1 with
  | .error e => .error e
  | .ok cmp =>
    if !ne && !cmp then .ok false
    else if ne && cmp then .ok true
    else
      match odictKeysEqual P v w with
      | .error e => .error e
      | .ok eq => .ok (eq != ne)

/-- `odict_richcompare` when `w` is a plain dict: order is ignored. -/
def odictEqDict (veq : V → V → Py Bool) (v : ODict K V) (w : PyDict K V) (ne : Bool) : Py Bool :=
  (dictRichcompare P veq v.d ne w).1

/-- One item of the iterable given to `mutablemapping_add_pairs`. -/
inductive PairItem (K V : Type) where
  | notIter (e : PyExc)
  | pair (k : K) (v : V)
  /-- Too few or too many values: 0, 1 or 3. -/
  | wrong (n : Nat)

/-- The loop of `mutablemapping_add_pairs` (:2237-2279). -/
def addPairsLoop : List (PairItem K V) → Option PyExc → OM K V Unit
  | [], stop =>
    match stop with
    | some e => M.throw e
    | none => pure ()
  | item :: rest, stop => do
    match item with
    | .notIter e => M.throw e
    | .wrong 0 => M.throw (.valueError "need more than 0 values to unpack")
    | .wrong 1 => M.throw (.valueError "need more than 1 value to unpack")
    | .wrong _ => M.throw (.valueError "too many values to unpack (expected 2)")
    | .pair k v => odictSetItem P k v
    addPairsLoop rest stop

/-- `mutablemapping_add_pairs` (:2226-2286). -/
def addPairs (pairs : Iterable (PairItem K V)) : OM K V Unit :=
  match pairs.getIter with
  | some e => M.throw e
  | none => addPairsLoop P pairs.items pairs.stop

/-- The argument of `mutablemapping_update_arg`, by the branch it selects. -/
inductive ODictArg (K V : Type) where
  /-- `PyDict_CheckExact(arg)`: `PyDict_Items`. -/
  | exact (d : PyDict K V)
  /-- Has `keys` (:2305-2333). -/
  | keysObj (keys : Iterable K) (getitem : K → Py V)
  /-- No `keys`, has `items` (:2337-2346); `it` is what iterating the object gives, which
  only the pure-Python class looks at. -/
  | itemsObj (items : Iterable (PairItem K V)) (it : Iterable (PairItem K V))
  /-- Neither (:2347). -/
  | pairs (it : Iterable (PairItem K V))

/-- The `keys` loop of `mutablemapping_update_arg` (:2317-2327). -/
def keysLoop (getitem : K → Py V) : List K → Option PyExc → OM K V Unit
  | [], stop =>
    match stop with
    | some e => M.throw e
    | none => pure ()
  | key :: rest, stop => do
    let value ← M.lift (getitem key)
    odictSetItem P key value
    keysLoop getitem rest stop

/-- `mutablemapping_update_arg` (:2288-2349). -/
def mutablemappingUpdateArg (arg : ODictArg K V) : OM K V Unit :=
  match arg with
  | .exact d =>
    addPairs P { items := (dictItemsList d).map fun p => .pair p.1 p.2 }
  | .keysObj keys getitem =>
    match keys.getIter with
    | some e => M.throw e
    | none => keysLoop P getitem keys.items keys.stop
  | .itemsObj items _ => addPairs P items
  | .pairs it => addPairs P it

/-- `mutablemapping_update` (:2351-2388), `odict_update`. -/
def mutablemappingUpdate (args : List (ODictArg K V)) (kwargs : List (K × V)) : OM K V Unit := do
  match args with
  | [] => pure ()
  | [other] => mutablemappingUpdateArg P other
  | _ =>
    M.throw (.typeError s!"update() takes at most 1 positional argument ({args.length} given)")
  if !kwargs.isEmpty then
    addPairs P { items := kwargs.map fun p => .pair p.1 p.2 }

/-- `odict_init` (:1559-1581): `OrderedDict.__init__`. -/
def odictInit (args : List (ODictArg K V)) (kwargs : List (K × V)) : OM K V Unit := do
  if args.length > 1 then
    M.throw (.typeError s!"expected at most 1 argument, got {args.length}")
  mutablemappingUpdate P args kwargs

/-- `odict_inplace_or` (:924-931). -/
def odictInplaceOr (other : ODictArg K V) : OM K V Unit := mutablemappingUpdateArg P other

/-- `odict_or` (:897-922): `other` must be a dict (otherwise `NotImplemented`), and the
result is `type(left)(left)` updated from `right`. -/
def odictOr (left : ODict K V) (id : Nat) (right : ODictArg K V) : Py (ODict K V) :=
  let start : ODict K V := odictNew id left.exact
  let run : OM K V Unit := do
    mutablemappingUpdateArg P (.keysObj { items := left.nodes.map (·.key) }
      (fun k => match (pyDictGetItemWithError P true k left.d).1 with
        | .ok (some v) => .ok v
        | .ok none => .error (keyErr P k)
        | .error e => .error e))
    mutablemappingUpdateArg P right
  match run start with
  | (.ok _, r) => .ok r
  | (.error e, _) => .error e

/-- `OrderedDict.fromkeys` (`OrderedDict_fromkeys_impl`, :957-962): `_PyDict_FromKeys` takes
the generic branch because `od` is not an exact dict. -/
def odictFromkeys (id : Nat) (it : Iterable K) (value : V) : Py (ODict K V) :=
  let run : OM K V Unit := do
    match it.getIter with
    | some e => M.throw e
    | none =>
      for key in it.items do
        odictSetItem P key value
      match it.stop with
      | some e => M.throw e
      | none => pure ()
  match run (odictNew id) with
  | (.ok _, r) => .ok r
  | (.error e, _) => .error e

end

/-- `OrderedDict___sizeof___impl` (:969-979). `sizeof(PyODictObject)` is 112 and
`sizeof(_ODictNode)` is 32. -/
def odictSizeOf (od : ODict K V) : Nat :=
  let dictPart := dictSizeOf od.d - 48 + 112
  dictPart + 8 * od.fastSize + (if od.isEmpty then 0 else 32 * od.d.used)

/-- `odictiterobject` (:1706-1714). `alive` is `di_odict != NULL`; `current` is `di_current`. -/
structure ODictIter (K : Type) where
  kind : IterKind
  rev : Bool
  current : Option K
  size : Int
  state : Nat
  alive : Bool := true
  deriving Repr, Inhabited

/-- `odictiter_new` (:1942-1973), `odict_iter`, `odict_reversed`, and the views'
`__iter__`/`__reversed__` (:1977-1997, :2046-2066, :2115-2135). -/
def odictiterNew (od : ODict K V) (kind : IterKind) (rev : Bool) : ODictIter K :=
  { kind, rev
    current := (if rev then od.nodes.getLast? else od.nodes.head?).map (·.key)
    size := od.d.used
    state := od.state }

section
variable [DecidableEq K] (P : Proto K (PyDict K V))

/-- The neighbour of a node in the list. -/
def nextNode (nodes : List (Node K)) (node : Node K) (rev : Bool) : Option (Node K) :=
  let l := if rev then nodes.reverse else nodes
  let rec go : List (Node K) → Option (Node K)
    | [] => none
    | [_] => none
    | a :: b :: t => if a.id == node.id then some b else go (b :: t)
  go l

/-- `odictiter_nextkey_lock_held` (:1741-1792), `odictiter_nextkey` (:1795-1807): the result,
the iterator afterwards, the odict afterwards. `.ok none` ends the iteration. -/
def odictiterNextkey (od : ODict K V) (di : ODictIter K) :
    Py (Option K) × ODictIter K × ODict K V :=
  if !di.alive then (.ok none, di, od) else
  match di.current with
  | none => (.ok none, { di with alive := false }, od)
  | some cur =>
    if od.state != di.state then
      (.error (runtimeError "OrderedDict mutated during iteration"), { di with alive := false }, od)
    else if di.size != od.d.used then
      (.error (runtimeError "OrderedDict changed size during iteration"), { di with size := -1 }, od)
    else
      match odictFindNode P cur od with
      | (.error e, od') => (.error e, { di with current := none }, od')
      | (.ok none, od') => (.error (keyErr P cur), { di with current := none }, od')
      | (.ok (some node), od') =>
        (.ok (some cur), { di with current := (nextNode od'.nodes node di.rev).map (·.key) }, od')

/-- `odictiter_iternext_lock_held` (:1809-1867), `odictiter_iternext` (:1869-1877). -/
def odictiterIternext (od : ODict K V) (di : ODictIter K) :
    Py (Option (K × Option V)) × ODictIter K × ODict K V :=
  match odictiterNextkey P od di with
  | (.error e, di', od') => (.error e, di', od')
  | (.ok none, di', od') => (.ok none, di', od')
  | (.ok (some key), di', od') =>
    if di.kind == .key then (.ok (some (key, none)), di', od')
    else
      let dead := { di' with current := none, alive := false }
      match pyDictGetItemRef P true key od'.d with
      | (.error e, d') => (.error e, dead, { od' with d := d' })
      | (.ok none, d') => (.error (keyErr P key), dead, { od' with d := d' })
      | (.ok (some v), d') => (.ok (some (key, some v)), di', { od' with d := d' })

/-- `PySequence_List(it)`, also what `odictiter_reduce` (:1884-1902) runs on a copy. -/
def odictiterDrain : Nat → ODict K V → ODictIter K → List (K × Option V) →
    Py (List (K × Option V)) × ODictIter K × ODict K V
  | 0, od, di, _ => (.error .modelFuel, di, od)
  | fuel + 1, od, di, acc =>
    match odictiterIternext P od di with
    | (.error e, di', od') => (.error e, di', od')
    | (.ok none, di', od') => (.ok acc.reverse, di', od')
    | (.ok (some x), di', od') => odictiterDrain fuel od' di' (x :: acc)

/-- `list(itertools.islice(it, n))`: at most `n` steps, unlike `odictiterDrain` a normal way
to stop. The difftest needs it because iteration need not terminate. -/
def odictiterTake : Nat → ODict K V → ODictIter K → List (K × Option V) →
    Py (List (K × Option V)) × ODictIter K × ODict K V
  | 0, od, di, acc => (.ok acc.reverse, di, od)
  | n + 1, od, di, acc =>
    match odictiterIternext P od di with
    | (.error e, di', od') => (.error e, di', od')
    | (.ok none, di', od') => (.ok acc.reverse, di', od')
    | (.ok (some x), di', od') => odictiterTake n od' di' (x :: acc)

/-- `list(od)` and friends. -/
def odictToList (od : ODict K V) (kind : IterKind) (rev : Bool) : Py (List (K × Option V)) :=
  (odictiterDrain P (od.nodes.length + od.d.used + 2) od (odictiterNew od kind rev) []).1

/-- `odict_repr` (:1440-1468): `PyDict_Copy(self)` goes down `dict_merge`'s slow path because
`tp_iter` is not `dict_iter`, so the copy follows the list, not the entries. -/
def odictRepr (krepr : K → Py String) (vrepr : V → Py String) (tname : String) (inRepr : Bool)
    (od : ODict K V) : Py String :=
  if od.d.used == 0 then .ok s!"{tname}()"
  else if inRepr then .ok "..."
  else
    match odictToList P od .key false with
    | .error e => .error e
    | .ok ks =>
      let getitem : K → Py V := fun k => (dictSubscript P none k od.d).1
      match mergeGenericLoop P getitem 1 (ks.map (·.1)) ({} : PyDict K V) with
      | (.error e, _) => .error e
      | (.ok _, dcopy) =>
        match dictRepr krepr vrepr false dcopy with
        | .error e => .error e
        | .ok r => .ok s!"{tname}({r})"

/-- `OrderedDict___reduce___impl` (:988-1022): the items the pickle will replay. -/
def odictReduceItems (od : ODict K V) : Py (List (K × Option V)) := odictToList P od .item false

end

end PyLean.DictSet
