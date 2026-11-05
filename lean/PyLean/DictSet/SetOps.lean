import PyLean.DictSet.SetModel

/-!
The algebra of `Objects/setobject.c`: `update`, `union`, `intersection`, `difference`,
`symmetric_difference`, their in-place and operator forms, subset tests, comparison,
construction. Line numbers refer to `Objects/setobject.c`.

Functions that differ only in which locks they take share one definition:
`set_update_lock_held`, `set_update_local` and `set_update_internal` are `setUpdate`;
`set_merge_lock_held` is `setMerge`.
-/

namespace PyLean.DictSet

open PyLean

variable {K : Type}

/-- An exact dict or frozendict as `setobject.c` sees it: its size, the walk of `_PyDict_Next`, and
`_PyDict_Contains_KnownHash`. The walk is a script of actions, so a comparison that changed the dict
under it, or the set, is a script like any other. -/
structure DictArg (K : Type) where
  size : Nat
  walk : List (SM K (Option (K × Int)))
  contains : K → Int → SM K Bool
  /-- The keys, for the routes that take `PyObject_GetIter(dict)`. -/
  keys : List K

/-- The non-self argument of a set method, by the branch it selects. -/
inductive SetArg (K : Type) where
  /-- `PyAnySet_Check(other)`, with `set`'s own `__iter__`: an exact set or frozenset, or a subclass
  that does not override `__iter__` (`s.exact` says which). -/
  | set (s : SetObj K)
  /-- `PyAnySet_Check(other)` but not `PyAnySet_CheckExact(other)`: an instance of a subclass whose
  type's `__iter__` is the script `it`. The branches that take `PyAnySet_Check` walk its table;
  `PyObject_GetIter(other)` runs `it`. -/
  | sub (s : SetObj K) (it : ReIter (SetObj K) K)
  /-- `PyAnyDict_CheckExact(other)`. -/
  | dict (d : DictArg K)
  /-- Any other iterable, with no callback of its own. -/
  | iter (it : Iterable K)
  /-- Any other iterable, whose `__iter__` and `__next__` run Python code. -/
  | live (it : ReIter (SetObj K) K)

/-- `PyObject_GetIter(other)` for any argument. -/
def SetArg.toReIter : SetArg K → ReIter (SetObj K) K
  | .set s => ReIter.ofIterable { items := (setEntries s).map (·.1) }
  | .sub _ it => it
  | .dict d => ReIter.ofIterable { items := d.keys }
  | .iter it => ReIter.ofIterable it
  | .live it => it

/-- The argument as a plain iterable, for the view operations, which run no callback of their own. -/
def SetArg.toIterable : SetArg K → Iterable K
  | .set s => { items := (setEntries s).map (·.1) }
  | .sub s _ => { items := (setEntries s).map (·.1) }
  | .dict d => { items := d.keys }
  | .iter it => it
  | .live _ => { items := [] }

/-- `make_new_set_basetype(Py_TYPE(so), NULL)` (:1400-1408). -/
def newBasetype (so : SetBody K) (id : Nat) : SetObj K :=
  { ident := id, frozen := so.frozen, tname := if so.frozen then "frozenset" else "set" }

/-- `set_swap_bodies` (:1511-1568), seen from `a`: `b` is about to be dropped. -/
def setSwapBodies (a b : SetObj K) : SetObj K :=
  { a with
    fill := b.fill, used := b.used, mask := b.mask, table := b.table
    tableId := b.tableId
    hash := if a.frozen && b.frozen then b.hash else -1 }

namespace SetObj

/-- The set with this identity as it stands now: the focus, or a peer. -/
def live (so : SetObj K) (id : Nat) : SetBody K :=
  if so.ident == id then so.toSetBody
  else (so.peers.find? (·.ident == id)).getD so.toSetBody

/-- Make the set with this identity the focus. The old focus takes its place among the peers. -/
def swapIn (so : SetObj K) (id : Nat) : SetObj K :=
  if so.ident == id then so
  else
    match so.peers.find? (·.ident == id) with
    | none => so
    | some b =>
      { toSetBody := b
        peers := so.peers.map fun p => if p.ident == id then so.toSetBody else p }

end SetObj

/-- Run an operation of the set with this identity: `set_contains_entry(other, ...)` while `result` is
in hand. -/
def onSet {α : Type} (id : Nat) (m : SM K α) : SM K α := fun so =>
  match m (so.swapIn id) with
  | (r, s) => (r, s.swapIn so.ident)

/-- Keep `o` reachable while `m` runs. A set already in the state stays where it is, and one that was
not goes away after, since nothing else can reach it. -/
def withPeer {α : Type} (o : SetObj K) (m : SM K α) : SM K α := fun so =>
  if so.ident == o.ident || so.peers.any (·.ident == o.ident) then m so
  else
    match m { so with peers := so.peers ++ [o.toSetBody] } with
    | (r, s) => (r, { s with peers := s.peers.dropLast })

/-- Run `m` on a new object `r`, with the current set among the peers, and hand `r` back. What `m`
leaves in the current set stands, success or not. -/
def onResult {α : Type} (r : SetObj K) (m : SM K α) : SM K (α × SetObj K) := fun so =>
  match m { r with peers := so.toSetBody :: so.peers } with
  | (res, s) =>
    let so' : SetObj K :=
      match s.peers with
      | b :: rest => { toSetBody := b, peers := rest }
      | [] => so
    match res with
    | .ok a => (.ok (a, { s with peers := [] }), so')
    | .error e => (.error e, so')

/-- The identity of a temporary set made while `id` is in hand: C objects have different addresses. -/
def tempId (id : Nat) : Nat := id + 2 ^ 32

/-- Enough turns of a `set_next` loop, however the set changes under it within reason. -/
def setLoopFuel (so : SetObj K) (id : Nat) : Nat := 4 * ((so.live id).mask + 1) + 64

section
variable [DecidableEq K] (P : Proto K (SetObj K))

/-- `while ((key = PyIter_Next(it)) != NULL) { ... }`: the body answers whether to stop, and so does
the loop, `false` on exhaustion. A step that raises is the `PyErr_Occurred()` after the loop. -/
def forIter (body : K → SM K Bool) : List (SM K (Option K)) → SM K Bool
  | [] => pure false
  | step :: rest => do
    match ← step with
    | none => return false
    | some key =>
      if ← body key then return true
      forIter body rest

/-- `while (set_next(id, &pos, &entry)) { ... }` (:709-731) with the body's answer as in `forIter`.
Each turn reads the table and mask of the set as they stand, since the body may have changed them. -/
def forNext (id : Nat) (body : K → Int → SM K Bool) : Nat → Nat → SM K Bool
  | 0, _ => M.throw .modelFuel
  | fuel + 1, pos => do
    let so ← M.get
    let o := so.live id
    match setNext o.table o.mask (o.mask + 2) pos with
    | none => return false
    | some (pos', key, hash) =>
      if ← body key hash then return true
      forNext id body fuel pos'

/-- The last loop of `set_merge_lock_held` (:883-890): `other->mask` and `other->table` again at each
turn. -/
def setMergeLoop (id : Nat) : Nat → Nat → SM K Unit
  | 0, _ => M.throw .modelFuel
  | fuel + 1, i => do
    let so ← M.get
    let o := so.live id
    if i > o.mask then return ()
    match o.table.getD i .null with
    | .active key hash =>
      setAddEntry P key hash
      setMergeLoop id fuel (i + 1)
    | _ => setMergeLoop id fuel (i + 1)

/-- What comes after the one big resize of `set_merge_lock_held` (:853-897). -/
def setMergeRest (o : SetBody K) : SM K Unit := do
  let so ← M.get
  if so.fill == 0 && so.mask == o.mask && o.fill == o.used then
    M.put { so with table := o.table, fill := o.fill, used := o.used }
    return ()
  if so.fill == 0 then
    let t ← M.lift (reinsertAll so.mask so.table o.table)
    M.put { so with table := t, fill := o.used, used := o.used }
    return ()
  setMergeLoop P o.ident (setLoopFuel so o.ident) 0

/-- `set_merge_lock_held` (:828-898) from the set with this identity. -/
def setMergeIn (id : Nat) : SM K Unit := do
  let so ← M.get
  let o := so.live id
  if o.ident == so.ident || o.used == 0 then return ()
  if (so.fill + o.used) * 5 ≥ so.mask * 3 then
    setTableResize ((so.used + o.used) * 2)
  setMergeRest P o

/-- `set_merge_lock_held`. -/
def setMerge (other : SetObj K) : SM K Unit := withPeer other (setMergeIn P other.ident)

/-- The walk of `_PyDict_Next` with the body at :1214 or :2241-2251. -/
def forWalk (body : K → Int → SM K Unit) : List (SM K (Option (K × Int))) → SM K Unit
  | [] => pure ()
  | step :: rest => do
    match ← step with
    | none => pure ()
    | some (key, hash) =>
      body key hash
      forWalk body rest

/-- `set_update_dict_lock_held` (:1186-1219). -/
def setUpdateDict (other : DictArg K) : SM K Unit := do
  let so ← M.get
  if (so.fill + other.size) * 5 ≥ so.mask * 3 then
    setTableResize ((so.used + other.size) * 2)
  forWalk (setAddEntry P) other.walk

/-- `set_update_iterable_lock_held` (:1221-1244). -/
def setUpdateIterable (it : ReIter (SetObj K) K) : SM K Unit := do
  it.getIter
  let _ ← forIter (fun key => do setAddKey P key; return false) it.steps

/-- `set_update_lock_held` (:1246-1256), `set_update_local` (:1259-1281),
`set_update_internal` (:1283-1317), `_PySet_Update` (:3168-3176). -/
def setUpdate (other : SetArg K) : SM K Unit :=
  match other with
  | .set o => setMerge P o
  | .sub o _ => setMerge P o
  | .dict d => setUpdateDict P d
  | .iter it => setUpdateIterable P (ReIter.ofIterable it)
  | .live it => setUpdateIterable P it

/-- `set.update` (`set_update_impl`, :1327-1340). -/
def setUpdateMulti : List (SetArg K) → SM K Unit
  | [] => pure ()
  | o :: rest => do
    setUpdate P o
    setUpdateMulti rest

/-- Run on a new object and hand it back, or the exception. -/
def runNew (m : SM K Unit) (s : SetObj K) : Py (SetObj K) :=
  match m s with
  | (.ok _, s') => .ok s'
  | (.error e, _) => .error e

/-- `make_new_set` (:1378-1386): a new object of the given shape filled from `iterable`. -/
def makeNewSet (shell : SetObj K) (iterable : Option (SetArg K)) : Py (SetObj K) :=
  match iterable with
  | none => .ok shell
  | some it => runNew (setUpdate P it) shell

/-- `set_copy_untracked_lock_held` (:1570-1583), `set_copy_impl` (:1593-1602), of the current set. -/
def setCopy (id : Nat) : SM K (SetObj K) := do
  let so ← M.get
  let r ← onResult (newBasetype so.toSetBody id) (setMerge P so)
  return r.2

/-- `frozenset_copy_impl` (:1612-1620): an exact frozenset is its own copy. -/
def frozensetCopy (id : Nat) : SM K (SetObj K) := do
  let so ← M.get
  if so.frozenExact then return { so with peers := [] }
  setCopy P id

/-- `set_union_impl` (:1646-1671). -/
def setUnion (others : List (SetArg K)) (id : Nat) : SM K (SetObj K) := do
  let so ← M.get
  let r ← setCopy P id
  let r ← others.foldlM (fun r other => do
    let same := match other with
      | .set o => o.ident == so.ident
      | .sub o _ => o.ident == so.ident
      | _ => false
    if same then return r
    let x ← onResult r (setUpdate P other)
    return x.2) r
  return r

/-- `set_or` (:1673-1693) on two sets (otherwise `NotImplemented`). -/
def setOr (other : SetObj K) (id : Nat) : SM K (SetObj K) := do
  let so ← M.get
  let r ← setCopy P id
  if so.ident == other.ident then return r
  let x ← onResult r (setUpdate P (.set other))
  return x.2

/-- The loop of `set_intersection` over two sets (:1733-1751), with the result in focus. -/
def setInterLoop (a b : Nat) : SM K Bool := do
  let s ← M.get
  forNext b (fun key hash => do
    let rv ← onSet a (setContainsEntry P key hash)
    if rv then setAddEntry P key hash
    return false) (setLoopFuel s b) 0

/-- One turn of the generic loop of `set_intersection` (:1763-1777), with the result in focus: a key
that makes the result as large as `so` stops the loop, so a later bad element is never hashed. -/
def interIterStep (soId : Nat) (key : K) : SM K Bool := do
  let hash ← P.hashM key
  let rv ← onSet soId (setContainsEntry P key hash)
  if rv then
    setAddEntry P key hash
    let s ← M.get
    if s.used ≥ (s.live soId).used then return true
  return false

/-- The branch of `set_intersection` for two sets (:1723-1755). The swap at :1727-1731 happens once,
on the sizes as they are then. -/
def setIntersectionSets (o : SetObj K) (id : Nat) : SM K (SetObj K) := do
  let so ← M.get
  let o' := so.live o.ident
  let a := if o'.used > so.used then o'.ident else so.ident
  let b := if o'.used > so.used then so.ident else o'.ident
  let r ← onResult (newBasetype so.toSetBody id) (setInterLoop P a b)
  return r.2

/-- The generic branch of `set_intersection` (:1756-1790), with the result in focus:
`PyObject_GetIter(other)`, then the loop of `interIterStep`; the loop's own exception, or the
iterator's, is the result. -/
def setInterIter (soId : Nat) (it : ReIter (SetObj K) K) : SM K Bool := do
  it.getIter
  forIter (interIterStep P soId) it.steps

/-- `set_intersection` (:1708-1791): `so == other` is a copy (:1716-1717); a set (`PyAnySet_Check`,
:1723) takes the two-set branch; anything else the generic one. The result takes the focus while
the loops run. Scope: an exact dict argument is iterated as the script of its keys; the set model's
world holds sets only, so an `__eq__` cannot change the dict under its iterator. -/
def setIntersection (other : SetArg K) (id : Nat) : SM K (SetObj K) := do
  let so ← M.get
  match other with
  | .set o =>
    if o.ident == so.ident then setCopy P id
    else withPeer o (setIntersectionSets P o id)
  | .sub o _ =>
    if o.ident == so.ident then setCopy P id
    else withPeer o (setIntersectionSets P o id)
  | _ =>
    let r ← onResult (newBasetype so.toSetBody id) (setInterIter P so.ident other.toReIter)
    return r.2

/-- `set_intersection_multi_impl` (:1801-1826). -/
def setIntersectionMulti (others : List (SetArg K)) (id : Nat) : SM K (SetObj K) := do
  match others with
  | [] => setCopy P id
  | first :: rest =>
    let r ← setIntersection P first id
    let rec go : List (SetArg K) → Nat → SetObj K → SM K (SetObj K)
      | [], _, r => pure r
      | other :: t, id', r => do
        let x ← onResult r (setIntersection P other (tempId id'))
        go t (tempId id') x.1
    go rest id r

/-- `set_intersection_update` (:1828-1839), `set_iand` (:1881-1898). -/
def setIntersectionUpdate (other : SetArg K) (id : Nat) : SM K Unit := do
  let tmp ← setIntersection P other id
  M.modify fun so => setSwapBodies so tmp

/-- `set_intersection_update_multi_impl` (:1849-1864). -/
def setIntersectionUpdateMulti (others : List (SetArg K)) (id : Nat) : SM K Unit := do
  let tmp ← setIntersectionMulti P others id
  M.modify fun so => setSwapBodies so tmp

/-- The branch of `set_isdisjoint_impl` for an exact set (:1924-1946). -/
def setDisjointSets (o : SetObj K) : SM K Bool := do
  let so ← M.get
  let o' := so.live o.ident
  let a := if o'.used > so.used then o'.ident else so.ident
  let b := if o'.used > so.used then so.ident else o'.ident
  let hit ← forNext b (fun key hash => onSet a (setContainsEntry P key hash)) (setLoopFuel so b) 0
  return !hit

/-- The generic branch of `set_isdisjoint_impl` (:1948-1967): `PyObject_GetIter(other)`, then
`set_contains_key` on each item until one is found. -/
def setDisjointIter (it : ReIter (SetObj K) K) : SM K Bool := do
  it.getIter
  let hit ← forIter (setContainsKey P) it.steps
  return !hit

/-- `PyIter_Next` over `set_iter(o)` (:1171-1184), for a set `o` whose type keeps `set`'s `__iter__`,
with `body` run on each key until it answers yes: every step is `setiter_iternext` (:1095-1136) on `o`
as it stands in the state then, so a change of size made by `body` (an `__eq__` that grew or shrank
`o`) raises `RuntimeError("Set changed size during iteration")` at the next step. -/
def setIterLoop (oid : Nat) (body : K → SM K Bool) : Nat → SetIter → SM K Bool
  | 0, _ => M.throw .modelFuel
  | fuel + 1, si => do
    let s ← M.get
    match setiterNext ({ toSetBody := s.live oid } : SetObj K) si with
    | (.error e, _) => M.throw e
    | (.ok none, _) => return false
    | (.ok (some k), si') =>
      if ← body k then return true
      setIterLoop oid body fuel si'

/-- The generic branch of `set_isdisjoint_impl` (:1948-1967) on a set that is not exact but keeps
`set`'s `__iter__`: `o` is in the state, so `__eq__` can change it under the iterator. -/
def setDisjointSetIter (o : SetObj K) : SM K Bool :=
  withPeer o (do
    let s ← M.get
    let hit ← setIterLoop o.ident (setContainsKey P) (setLoopFuel s o.ident)
      (setIterNew ({ toSetBody := s.live o.ident } : SetObj K))
    return !hit)

/-- `set_isdisjoint_impl` (:1910-1968): `so == other` answers whether `so` is empty (:1917-1922);
`PyAnySet_CheckExact(other)` (:1924), not `PyAnySet_Check`, takes the two-set branch, so a set
subclass goes through its own `__iter__`, or through `set_iter` on the live object when it keeps
`set`'s. Scope: a dict argument's iteration is the script of its keys (`DictArg.keys`); the set
model's world holds sets only, so an `__eq__` cannot change the dict under its iterator, and
"dictionary changed size during iteration" is not expressible. -/
def setIsdisjoint (other : SetArg K) : SM K Bool := do
  let so ← M.get
  let same := match other with
    | .set o => o.ident == so.ident
    | .sub o _ => o.ident == so.ident
    | _ => false
  if same then return so.used == 0
  let fast := match other with
    | .set o => if o.exact then some o else none
    | _ => none
  match fast with
  | some o => withPeer o (setDisjointSets P o)
  | none =>
    match other with
    | .set o => setDisjointSetIter P o
    | _ => setDisjointIter P other.toReIter

/-- The tail of `set_difference_update_internal` (:2025-2028): more than a quarter dummies. -/
def setPurgeDummies : SM K Unit := do
  let so ← M.get
  if so.fill - so.used ≤ so.mask / 4 then return ()
  setGrow

/-- `set_discard_entry` over the entries of a set nothing else can reach (:1995-2004). -/
def discardList : List (K × Int) → SM K Unit
  | [] => pure ()
  | (k, h) :: rest => do
    let _ ← setDiscardEntry P k h
    discardList rest

/-- The set branch of `set_difference_update_internal` (:1995-2004). -/
def setDiscardLoop (id : Nat) : SM K Bool := do
  let s ← M.get
  forNext id (fun key hash => do
    let _ ← setDiscardEntry P key hash
    return false) (setLoopFuel s id) 0

/-- The branch of `set_difference_update_internal` for a set (:1979-2006). -/
def setDiffUpdateSets (o : SetObj K) (id : Nat) : SM K Unit := do
  let so ← M.get
  let o' := so.live o.ident
  if o'.used >>> 3 > so.used then
    let tmp ← setIntersection P (.set o) id
    discardList P (setEntries tmp)
  else
    let _ ← setDiscardLoop P o.ident

/-- `set_difference_update_internal` (:1970-2029). -/
def setDifferenceUpdateInternal (other : SetArg K) (id : Nat) : SM K Unit := do
  let so ← M.get
  let same := match other with
    | .set o => o.ident == so.ident
    | .sub o _ => o.ident == so.ident
    | _ => false
  if same then
    M.put (setClearInternal so)
    return ()
  match other with
  | .set o => withPeer o (setDiffUpdateSets P o id)
  | .sub o _ => withPeer o (setDiffUpdateSets P o id)
  | _ =>
    let it := other.toReIter
    it.getIter
    let _ ← forIter (fun key => do
      let _ ← setDiscardKey P key
      return false) it.steps
  setPurgeDummies

/-- `set_difference_update_impl` (:2039-2057). -/
def setDifferenceUpdateMulti (others : List (SetArg K)) (id : Nat) : SM K Unit := do
  for o in others do
    setDifferenceUpdateInternal P o id

/-- `set_copy_and_difference_untracked` (:2059-2071). -/
def setCopyAndDifference (other : SetArg K) (id : Nat) : SM K (SetObj K) := do
  let r ← setCopy P id
  let x ← onResult r (setDifferenceUpdateInternal P other (tempId id))
  return x.2

/-- The loop of `set_difference_untracked` over two sets (:2127-2145), with the result in focus: what
`id` holds of the set `src` that `o` does not. -/
def setDiffLoop (o src : Nat) : SM K Bool := do
  let s ← M.get
  forNext src (fun key hash => do
    let rv ← onSet o (setContainsEntry P key hash)
    if !rv then setAddEntry P key hash
    return false) (setLoopFuel s src) 0

/-- That branch of `set_difference_untracked`. -/
def setDifferenceSets (o : SetObj K) (id : Nat) : SM K (SetObj K) := do
  let so ← M.get
  let r ← onResult (newBasetype so.toSetBody id) (setDiffLoop P o.ident so.ident)
  return r.2

/-- `set_difference_untracked` (:2073-2147). -/
def setDifference (other : SetArg K) (id : Nat) : SM K (SetObj K) := do
  let so ← M.get
  let otherSize : Option Nat := match other with
    | .set o => some o.used
    | .sub o _ => some o.used
    | .dict d => some d.size
    | _ => none
  match otherSize with
  | none => setCopyAndDifference P other id
  | some sz =>
    if so.used >>> 2 > sz then setCopyAndDifference P other id
    else
      let result := newBasetype so.toSetBody id
      match other with
      | .dict d =>
        let r ← onResult result (do
          let s ← M.get
          forNext so.ident (fun key hash => do
            let rv ← d.contains key hash
            if !rv then setAddEntry P key hash
            return false) (setLoopFuel s so.ident) 0)
        return r.2
      | .set o => withPeer o (setDifferenceSets P o id)
      | .sub o _ => withPeer o (setDifferenceSets P o id)
      | _ => setCopyAndDifference P other id

/-- `set_difference_multi_impl` (:2158-2190). -/
def setDifferenceMulti (others : List (SetArg K)) (id : Nat) : SM K (SetObj K) := do
  match others with
  | [] => setCopy P id
  | o :: rest =>
    let r ← setDifference P o id
    let x ← onResult r (do
      for y in rest do
        setDifferenceUpdateInternal P y (tempId id))
    return x.2

/-- The body of `set_symmetric_difference_update_dict` (:2241-2251) and of
`set_symmetric_difference_update_set` (:2268-2278). -/
def symDiffStep (key : K) (hash : Int) : SM K Unit := do
  let found ← setDiscardEntry P key hash
  if !found then setAddEntry P key hash

/-- That body over the entries of a set nothing else can reach. -/
def symList : List (K × Int) → SM K Unit
  | [] => pure ()
  | (k, h) :: rest => do
    symDiffStep P k h
    symList rest

/-- `set_symmetric_difference_update_set` (:2257-2282). -/
def symDiffSet (id : Nat) : SM K Unit := do
  let s ← M.get
  let _ ← forNext id (fun key hash => do
    symDiffStep P key hash
    return false) (setLoopFuel s id) 0

/-- `set_symmetric_difference_update_impl` (:2294-2334), `set_ixor` (:2377-2391). -/
def setSymmetricDifferenceUpdate (other : SetArg K) (id : Nat) : SM K Unit := do
  let so ← M.get
  match other with
  | .set o =>
    if o.ident == so.ident then
      M.put (setClearInternal so)
    else
      withPeer o (symDiffSet P o.ident)
  | .sub o _ =>
    if o.ident == so.ident then
      M.put (setClearInternal so)
    else
      withPeer o (symDiffSet P o.ident)
  | .dict d => forWalk (symDiffStep P) d.walk
  | _ =>
    let x ← onResult (newBasetype so.toSetBody id) (setUpdate P other)
    symList P (setEntries x.2)

/-- `set_symmetric_difference_impl` (:2347-2366), `set_xor` (:2368-2375). -/
def setSymmetricDifference (other : SetArg K) (id : Nat) : SM K (SetObj K) := do
  let so ← M.get
  let x ← onResult (newBasetype so.toSetBody id) (do
    setUpdate P other
    symDiffSet P so.ident)
  return x.2

/-- The branch of `set_issubset_impl` for a set (:2420-2435). -/
def setSubsetSets (o : SetObj K) : SM K Bool := do
  let so ← M.get
  let o' := so.live o.ident
  if so.used > o'.used then return false
  let miss ← forNext so.ident (fun key hash => do
    let rv ← onSet o.ident (setContainsEntry P key hash)
    return !rv) (setLoopFuel so so.ident) 0
  return !miss

/-- `set_issubset_impl` (:2403-2436). -/
def setIssubset (other : SetArg K) (id : Nat) : SM K Bool := do
  let so ← M.get
  match other with
  | .set o => withPeer o (setSubsetSets P o)
  | .sub o _ => withPeer o (setSubsetSets P o)
  | _ =>
    let tmp ← setIntersection P other id
    let so' ← M.get
    return tmp.used == so'.used

/-- `set_issuperset_impl` (:2448-2477). -/
def setIssuperset (other : SetArg K) (id : Nat) : SM K Bool := do
  let so ← M.get
  match other with
  | .set o => withPeer o (onSet o.ident (setIssubset P (.set so) id))
  | .sub o _ => withPeer o (onSet o.ident (setIssubset P (.set so) id))
  | _ =>
    let it := other.toReIter
    it.getIter
    let miss ← forIter (fun key => do
      let rv ← setContainsKey P key
      return !rv) it.steps
    return !miss

/-- Comparison operators. -/
inductive CmpOp where
  | lt | le | eq | ne | gt | ge
  deriving DecidableEq, Repr, Inhabited

/-- `set_richcompare` (:2479-2521) on two sets (otherwise `NotImplemented`). -/
def setRichcompare (w : SetObj K) (op : CmpOp) (id : Nat) : SM K Bool := do
  let v ← M.get
  let eq : SM K Bool :=
    if v.used != w.used then pure false
    else if v.hash != -1 && w.hash != -1 && v.hash != w.hash then pure false
    else setIssubset P (.set w) id
  match op with
  | .eq => eq
  | .ne =>
    let r ← eq
    return !r
  | .le => setIssubset P (.set w) id
  | .ge => setIssuperset P (.set w) id
  | .lt => if v.used ≥ w.used then return false else setIssubset P (.set w) id
  | .gt => if v.used ≤ w.used then return false else setIssuperset P (.set w) id

/-- `frozenset_hash_impl(key)` for a key that `PySet_Check` says is a set: `keySet key s` is that
set's body as it stands in state `s`, or `none` when the key is not a set. The body comes from the
state, so whatever `__hash__` did to the key itself is seen. -/
def keySetHash (keySet : K → SetObj K → Option (SetBody K)) (key : K) (s : SetObj K) : Option Int :=
  (keySet key s).map fun b => frozensetHashImpl ({ toSetBody := b } : SetObj K)

/-- `!PySet_Check(key) || !PyErr_ExceptionMatches(PyExc_TypeError)` (:2551, :2611, :2648, :2688):
the retry is for a `set` key and an exception that is `TypeError` or a subclass of it. -/
def retryHash (keySet : K → SetObj K → Option (SetBody K)) (key : K) (e : PyExc) (s : SetObj K) :
    Option Int :=
  if P.isTypeError e then keySetHash keySet key s else none

/-- `set_remove_impl` (:2646-2657) and `set_discard_impl` (:2686-2697): when `set_discard_key`
fails for a `set` key with a `TypeError` (or a subclass), the error is cleared and the key is looked
up again by the hash of the equal frozenset. The failure may come from `__hash__` (already through
`set_unhashable_type`) or from `__eq__` during the lookup. -/
def retryAsFrozen {α : Type} (keySet : K → SetObj K → Option (SetBody K)) (key : K) (first : SM K α)
    (retry : Int → SM K α) : SM K α :=
  M.tryCatch first fun e s =>
    match retryHash P keySet key e s with
    | some h => retry h s
    | none => (.error e, s)

/-- The opening of `_PySet_Contains` (:2549-2562) and `frozenset___contains___impl` (:2609-2619):
`_PyObject_HashFast(key)`, whose `__hash__` may change the state; a failure is retried with
`frozenset_hash_impl(key)` only for a `set` key and a `TypeError` or subclass
(`PyErr_ExceptionMatches`), and otherwise goes through `set_unhashable_type`, whose own test is the
exact type. A `TypeError` from `__eq__` comes later and is not retried. -/
def containsHash (keySet : K → SetObj K → Option (SetBody K)) (key : K) : SM K Int := fun s =>
  match P.hashM key s with
  | (.ok h, s') => (.ok h, s')
  | (.error e, s') =>
    match retryHash P keySet key e s' with
    | some h => (.ok h, s')
    | none => (.error (setUnhashableType P key e), s')

/-- `_PySet_Contains` (:2544-2564): the hash, then `set_contains_entry`. -/
def setContains (keySet : K → SetObj K → Option (SetBody K)) (key : K) : SM K Bool := do
  let hash ← containsHash P keySet key
  setContainsEntry P key hash

/-- `set_contains` (:2566-2571), the `sq_contains` slot that `key in so` calls through
`PySequence_Contains`: the `int` `_PySet_Contains` gives, `-1` for an exception. -/
def setSqContains (keySet : K → SetObj K → Option (SetBody K)) (key : K) : SM K Int := fun s =>
  match setContains P keySet key s with
  | (.ok b, s') => (.ok (if b then 1 else 0), s')
  | (.error e, s') => (.error e, s')

/-- `set___contains___impl` (:2584-2593), `set.__contains__(so, key)`: `NULL` when `result < 0`,
else `PyBool_FromLong(result)`. -/
def setDunderContains (keySet : K → SetObj K → Option (SetBody K)) (key : K) : SM K Bool := fun s =>
  match setSqContains P keySet key s with
  | (.ok r, s') => (.ok (r != 0), s')
  | (.error e, s') => (.error e, s')

/-- The tail of `frozenset___contains___impl` (:2620-2625): `set_do_lookup(so, so->table, so->mask,
key, hash, &entry, set_compare_frozenset)`, then `PyBool_FromLong(status)`. -/
def frozenLookup (key : K) (hash : Int) : SM K Bool := do
  let so ← M.get
  let u := toU64 hash
  match ← lookOuter P true key hash so.mask (setProbeFuel so.mask) (u &&& so.mask) u with
  | none => M.throw .modelFuel
  | some s =>
    let so' ← M.get
    match so'.slot s with
    | .null => return false
    | _ => return true

/-- `frozenset.__contains__` (`frozenset___contains___impl`, :2606-2626): the same hash and retry as
`_PySet_Contains`, then one `set_do_lookup` with `set_compare_frozenset` on any frozenset, a subclass
too. (`in` on a frozenset subclass reaches the same function: the subclass's `sq_contains` is
`slot_sq_contains`, which calls `frozenset.__contains__`; `set_lookkey` and its
`PyFrozenSet_CheckExact` test are what `set_contains_entry` takes.) The answer is read from
the slot where the walk stopped, which is `status` (:2621-2625): `set_compare_frozenset` ends a
block only at a NULL or at an entry it found, and nothing can change a frozenset's table in
between. -/
def frozensetContains (keySet : K → SetObj K → Option (SetBody K)) (key : K) : SM K Bool := do
  let hash ← containsHash P keySet key
  frozenLookup P key hash


/-- `set_remove_impl` (:2640-2665). -/
def setRemove (keySet : K → SetObj K → Option (SetBody K)) (key : K) : SM K Unit := do
  let rv ← retryAsFrozen P keySet key (setDiscardKey P key) (setDiscardEntry P key)
  if !rv then M.throw (keyErr P key)

/-- `set_discard_impl` (:2680-2700). -/
def setDiscard (keySet : K → SetObj K → Option (SetBody K)) (key : K) : SM K Unit := do
  let _ ← retryAsFrozen P keySet key (setDiscardKey P key) (setDiscardEntry P key)

/-- `PyErr_BadInternalCall()`. -/
def setBadInternalCall : PyExc := systemError "~bad argument to internal function"

/-- `PySet_Contains` (:3065-3080): no retry for a `set` key. -/
def pySetContains (isAny : Bool) (key : K) : SM K Bool :=
  if isAny then setContainsKey P key else M.throw setBadInternalCall

/-- `PySet_Discard` (:3082-3095). -/
def pySetDiscard (isSet : Bool) (key : K) : SM K Bool :=
  if isSet then setDiscardKey P key else M.throw setBadInternalCall

/-- `PySet_Add` (:3097-3123): a frozenset only while nothing else refers to it. -/
def pySetAdd (isSet frozenUnique : Bool) (key : K) : SM K Unit :=
  if isSet || frozenUnique then setAddKey P key else M.throw setBadInternalCall

/-- `set_init` (:2752-2779), the fresh and the re-init branches. -/
def setInit (args : List (SetArg K)) (hasKw : Bool) : SM K Unit := do
  if hasKw then M.throw (.typeError "set() takes no keyword arguments")
  let self ← M.get
  match args with
  | [] =>
    M.put { (if self.fill != 0 then setClearInternal self else self) with hash := -1 }
  | [it] =>
    M.put { (if self.fill != 0 then setClearInternal self else self) with hash := -1 }
    setUpdate P it
  | _ => M.throw (.typeError s!"{self.tname} expected at most 1 argument, got {args.length}")

/-- `set_vectorcall` (:2781-2801). -/
def setVectorcall (id : Nat) (args : List (SetArg K)) (hasKw : Bool) : Py (SetObj K) :=
  if hasKw then .error (.typeError "set() takes no keyword arguments")
  else
    match args with
    | [] => makeNewSet P { ident := id } none
    | [a] => makeNewSet P { ident := id } (some a)
    | _ => .error (.typeError s!"set expected at most 1 argument, got {args.length}")

/-- `frozenset_vectorcall` (:1466-1481) with `make_new_frozenset` (:1430-1446):
`frozenset(f)` is `f`. -/
def frozensetVectorcall (id : Nat) (args : List (SetArg K)) (hasKw : Bool) : Py (SetObj K) :=
  let shell : SetObj K := { ident := id, frozen := true, tname := "frozenset" }
  if hasKw then .error (.typeError "frozenset() takes no keyword arguments")
  else
    match args with
    | [] => makeNewSet P shell none
    | [.set s] => if s.frozenExact then .ok s else makeNewSet P shell (some (.set s))
    | [a] => makeNewSet P shell (some a)
    | _ => .error (.typeError s!"frozenset expected at most 1 argument, got {args.length}")

end

end PyLean.DictSet
