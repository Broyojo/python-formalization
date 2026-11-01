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

/-- An exact dict as `setobject.c` sees it: its size, `_PyDict_Next`, and
`_PyDict_Contains_KnownHash`. -/
structure DictArg (K : Type) where
  size : Nat
  items : List (K × Int)
  contains : K → Int → Py Bool

/-- The non-self argument of a set method, by the branch it selects. -/
inductive SetArg (K : Type) where
  /-- `PyAnySet_Check(other)`. -/
  | set (s : SetObj K)
  /-- `PyDict_CheckExact(other)`. -/
  | dict (d : DictArg K)
  /-- Any other iterable. -/
  | iter (it : Iterable K)

/-- `PyObject_GetIter(other)` for any argument. -/
def SetArg.toIterable : SetArg K → Iterable K
  | .set s => { items := (setEntries s).map (·.1) }
  | .dict d => { items := d.items.map (·.1) }
  | .iter it => it

/-- `make_new_set_basetype(Py_TYPE(so), NULL)` (:1388-1408). -/
def newBasetype (so : SetObj K) (id : Nat) : SetObj K :=
  { ident := id, frozen := so.frozen, tname := if so.frozen then "frozenset" else "set" }

/-- `set_swap_bodies` (:1511-1568), seen from `a`: `b` is about to be dropped. -/
def setSwapBodies (a b : SetObj K) : SetObj K :=
  { a with
    fill := b.fill, used := b.used, mask := b.mask, table := b.table
    tableId := b.tableId
    hash := if a.frozen && b.frozen then b.hash else -1 }

section
variable [DecidableEq K] (P : Proto K (SetObj K))

/-- `set_merge_lock_held` (:828-898). -/
def setMerge (other : SetObj K) : SM K Unit := do
  let so ← M.get
  if other.ident == so.ident || other.used == 0 then return ()
  if (so.fill + other.used) * 5 ≥ so.mask * 3 then
    setTableResize ((so.used + other.used) * 2)
  let so ← M.get
  if so.fill == 0 && so.mask == other.mask && other.fill == other.used then
    M.put { so with table := other.table, fill := other.fill, used := other.used }
    return ()
  if so.fill == 0 then
    let t ← M.lift (reinsertAll so.mask so.table other.table)
    M.put { so with table := t, fill := other.used, used := other.used }
    return ()
  for (key, hash) in setEntries other do
    setAddEntry P key hash

/-- `set_update_dict_lock_held` (:1186-1219). -/
def setUpdateDict (other : DictArg K) : SM K Unit := do
  let so ← M.get
  if (so.fill + other.size) * 5 ≥ so.mask * 3 then
    setTableResize ((so.used + other.size) * 2)
  for (key, hash) in other.items do
    setAddEntry P key hash

/-- `set_update_iterable_lock_held` (:1221-1244). -/
def setUpdateIterable (it : Iterable K) : SM K Unit := do
  match it.getIter with
  | some e => M.throw e
  | none =>
    for key in it.items do
      setAddKey P key
    match it.stop with
    | some e => M.throw e
    | none => pure ()

/-- `set_update_lock_held` (:1246-1256), `set_update_local` (:1259-1281),
`set_update_internal` (:1283-1317), `_PySet_Update` (:3168-3176). -/
def setUpdate (other : SetArg K) : SM K Unit :=
  match other with
  | .set o => setMerge P o
  | .dict d => setUpdateDict P d
  | .iter it => setUpdateIterable P it

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

/-- `make_new_set` (:1350-1386): a new object of the given shape filled from `iterable`. -/
def makeNewSet (shell : SetObj K) (iterable : Option (SetArg K)) : Py (SetObj K) :=
  match iterable with
  | none => .ok shell
  | some it => runNew (setUpdate P it) shell

/-- `set_copy_untracked_lock_held` (:1570-1583), `set_copy_impl` (:1593-1602). -/
def setCopy (so : SetObj K) (id : Nat) : Py (SetObj K) :=
  runNew (setMerge P so) (newBasetype so id)

/-- `frozenset_copy_impl` (:1612-1620): an exact frozenset is its own copy. -/
def frozensetCopy (so : SetObj K) (id : Nat) : Py (SetObj K) :=
  if so.frozenExact then .ok so else setCopy P so id

/-- `set_union_impl` (:1646-1671). -/
def setUnion (so : SetObj K) (others : List (SetArg K)) (id : Nat) : Py (SetObj K) :=
  match makeNewSet P (newBasetype so id) (some (.set so)) with
  | .error e => .error e
  | .ok r =>
    runNew (do
      for other in others do
        let same := match other with
          | .set o => o.ident == so.ident
          | _ => false
        if !same then setUpdate P other) r

/-- `set_or` (:1673-1693) on two sets (otherwise `NotImplemented`). -/
def setOr (self other : SetObj K) (id : Nat) : Py (SetObj K) :=
  match setCopy P self id with
  | .error e => .error e
  | .ok r =>
    if self.ident == other.ident then .ok r
    else runNew (setUpdate P (.set other)) r

/-- A lookup in a set that is not the state of the running computation. -/
def containsIn (s : SetObj K) (key : K) (hash : Int) : Py Bool :=
  (setContainsEntry P key hash s).1

/-- The loop at :1733-1751: keep what `so` contains. -/
def interLoop (so : SetObj K) : List (K × Int) → SM K Unit
  | [] => pure ()
  | (key, hash) :: rest => do
    let rv ← M.lift (containsIn P so key hash)
    if rv then setAddEntry P key hash
    interLoop so rest

/-- The generic loop at :1762-1778, which stops early once `result` is as large as `so`:
a later bad element is then never hashed, and an `__iter__` that would raise is not
reached. -/
def interIterLoop (so : SetObj K) : List K → Option PyExc → SM K Unit
  | [], stop =>
    match stop with
    | some e => M.throw e
    | none => pure ()
  | key :: rest, stop => do
    let hash ← M.lift (P.hash key)
    let rv ← M.lift (containsIn P so key hash)
    if rv then
      setAddEntry P key hash
      let r ← M.get
      if r.used ≥ so.used then return ()
    interIterLoop so rest stop

/-- `set_intersection` (:1708-1791). -/
def setIntersection (so : SetObj K) (other : SetArg K) (id : Nat) : Py (SetObj K) :=
  match other with
  | .set o =>
    if o.ident == so.ident then setCopy P so id
    else
      let result := newBasetype so id
      let (a, b) := if o.used > so.used then (o, so) else (so, o)
      runNew (interLoop P a (setEntries b)) result
  | _ =>
    let result := newBasetype so id
    let it := other.toIterable
    match it.getIter with
    | some e => .error e
    | none => runNew (interIterLoop P so it.items it.stop) result

/-- `set_intersection_multi_impl` (:1801-1826). -/
def setIntersectionMulti (so : SetObj K) (others : List (SetArg K)) (id : Nat) : Py (SetObj K) :=
  match others with
  | [] => setCopy P so id
  | _ =>
    others.foldlM (fun r other => setIntersection P r other id) so

/-- `set_intersection_update` (:1828-1839), `set_iand` (:1881-1898). -/
def setIntersectionUpdate (other : SetArg K) (id : Nat) : SM K Unit := do
  let so ← M.get
  let tmp ← M.lift (setIntersection P so other id)
  M.put (setSwapBodies so tmp)

/-- `set_intersection_update_multi_impl` (:1849-1864). -/
def setIntersectionUpdateMulti (others : List (SetArg K)) (id : Nat) : SM K Unit := do
  let so ← M.get
  let tmp ← M.lift (setIntersectionMulti P so others id)
  M.put (setSwapBodies so tmp)

/-- `set_isdisjoint_impl` (:1910-1968). `PyAnySet_CheckExact` here, not `PyAnySet_Check`. -/
def setIsdisjoint (so : SetObj K) (other : SetArg K) : Py Bool :=
  let same := match other with
    | .set o => o.ident == so.ident
    | _ => false
  if same then .ok (so.used == 0)
  else
    let fast := match other with
      | .set o => if o.exact then some o else none
      | _ => none
    match fast with
    | some o =>
      let (a, b) := if o.used > so.used then (o, so) else (so, o)
      let rec go : List (K × Int) → Py Bool
        | [] => .ok true
        | (key, hash) :: rest =>
          match containsIn P a key hash with
          | .error e => .error e
          | .ok rv => if rv then .ok false else go rest
      go (setEntries b)
    | none =>
      let it := other.toIterable
      match it.getIter with
      | some e => .error e
      | none =>
        let rec goIter : List K → Py Bool
          | [] =>
            match it.stop with
            | some e => .error e
            | none => .ok true
          | key :: rest =>
            match (setContainsKey P key so).1 with
            | .error e => .error e
            | .ok rv => if rv then .ok false else goIter rest
        goIter it.items

/-- The tail of `set_difference_update_internal` (:2025-2028): more than a quarter dummies. -/
def setPurgeDummies : SM K Unit := do
  let so ← M.get
  if so.fill - so.used ≤ so.mask / 4 then return ()
  setGrow

/-- `set_difference_update_internal` (:1970-2029). -/
def setDifferenceUpdateInternal (other : SetArg K) (id : Nat) : SM K Unit := do
  let so ← M.get
  let same := match other with
    | .set o => o.ident == so.ident
    | _ => false
  if same then
    M.put (setClearInternal so)
    return ()
  match other with
  | .set o =>
    let o' ← (if o.used >>> 3 > so.used then M.lift (setIntersection P so (.set o) id) else pure o)
    for (key, hash) in setEntries o' do
      let _ ← setDiscardEntry P key hash
  | _ =>
    let it := other.toIterable
    match it.getIter with
    | some e => M.throw e
    | none =>
      for key in it.items do
        let _ ← setDiscardKey P key
      match it.stop with
      | some e => M.throw e
      | none => pure ()
  setPurgeDummies

/-- `set_difference_update_impl` (:2039-2057). -/
def setDifferenceUpdateMulti (others : List (SetArg K)) (id : Nat) : SM K Unit := do
  for o in others do
    setDifferenceUpdateInternal P o id

/-- `set_copy_and_difference_untracked` (:2059-2071). -/
def setCopyAndDifference (so : SetObj K) (other : SetArg K) (id : Nat) : Py (SetObj K) :=
  match setCopy P so id with
  | .error e => .error e
  | .ok r => runNew (setDifferenceUpdateInternal P other id) r

/-- `set_difference_untracked` (:2073-2147). -/
def setDifference (so : SetObj K) (other : SetArg K) (id : Nat) : Py (SetObj K) :=
  let otherSize : Option Nat := match other with
    | .set o => some o.used
    | .dict d => some d.size
    | .iter _ => none
  match otherSize with
  | none => setCopyAndDifference P so other id
  | some sz =>
    if so.used >>> 2 > sz then setCopyAndDifference P so other id
    else
      let result := newBasetype so id
      match other with
      | .dict d =>
        runNew (do
          for (key, hash) in setEntries so do
            let rv ← M.lift (d.contains key hash)
            if !rv then setAddEntry P key hash) result
      | .set o =>
        runNew (do
          for (key, hash) in setEntries so do
            let rv ← M.lift (containsIn P o key hash)
            if !rv then setAddEntry P key hash) result
      | .iter _ => setCopyAndDifference P so other id

/-- `set_difference_multi_impl` (:2159-2190). -/
def setDifferenceMulti (so : SetObj K) (others : List (SetArg K)) (id : Nat) : Py (SetObj K) :=
  match others with
  | [] => setCopy P so id
  | o :: rest =>
    match setDifference P so o id with
    | .error e => .error e
    | .ok r =>
      runNew (do
        for x in rest do
          setDifferenceUpdateInternal P x id) r

/-- `set_symmetric_difference_update_dict` (:2226-2255) and
`set_symmetric_difference_update_set` (:2257-2282): one loop over `(key, hash)`. -/
def symDiffLoop : List (K × Int) → SM K Unit
  | [] => pure ()
  | (key, hash) :: rest => do
    let found ← setDiscardEntry P key hash
    if !found then setAddEntry P key hash
    symDiffLoop rest

/-- `set_symmetric_difference_update_impl` (:2294-2334), `set_ixor` (:2377-2391). -/
def setSymmetricDifferenceUpdate (other : SetArg K) (id : Nat) : SM K Unit := do
  let so ← M.get
  match other with
  | .set o =>
    if o.ident == so.ident then
      M.put (setClearInternal so)
    else
      symDiffLoop P (setEntries o)
  | .dict d => symDiffLoop P d.items
  | .iter it =>
    let otherset ← M.lift (makeNewSet P (newBasetype so id) (some (.iter it)))
    symDiffLoop P (setEntries otherset)

/-- `set_symmetric_difference_impl` (:2347-2366), `set_xor` (:2368-2375). -/
def setSymmetricDifference (so : SetObj K) (other : SetArg K) (id : Nat) : Py (SetObj K) :=
  runNew (do
    setUpdate P other
    symDiffLoop P (setEntries so)) (newBasetype so id)

/-- `set_issubset_impl` (:2403-2436). -/
def setIssubset (so : SetObj K) (other : SetArg K) (id : Nat) : Py Bool :=
  match other with
  | .set o =>
    if so.used > o.used then .ok false
    else
      let rec go : List (K × Int) → Py Bool
        | [] => .ok true
        | (key, hash) :: rest =>
          match containsIn P o key hash with
          | .error e => .error e
          | .ok rv => if rv then go rest else .ok false
      go (setEntries so)
  | _ =>
    match setIntersection P so other id with
    | .error e => .error e
    | .ok tmp => .ok (tmp.used == so.used)

/-- `set_issuperset_impl` (:2448-2477). -/
def setIssuperset (so : SetObj K) (other : SetArg K) (id : Nat) : Py Bool :=
  match other with
  | .set o => setIssubset P o (.set so) id
  | _ =>
    let it := other.toIterable
    match it.getIter with
    | some e => .error e
    | none =>
      let rec go : List K → Py Bool
        | [] =>
          match it.stop with
          | some e => .error e
          | none => .ok true
        | key :: rest =>
          match (setContainsKey P key so).1 with
          | .error e => .error e
          | .ok rv => if rv then go rest else .ok false
      go it.items

/-- Comparison operators. -/
inductive CmpOp where
  | lt | le | eq | ne | gt | ge
  deriving DecidableEq, Repr, Inhabited

/-- `set_richcompare` (:2479-2521) on two sets (otherwise `NotImplemented`). -/
def setRichcompare (v w : SetObj K) (op : CmpOp) (id : Nat) : Py Bool :=
  let eq : Py Bool :=
    if v.used != w.used then .ok false
    else if v.hash != -1 && w.hash != -1 && v.hash != w.hash then .ok false
    else setIssubset P v (.set w) id
  match op with
  | .eq => eq
  | .ne =>
    match eq with
    | .error e => .error e
    | .ok r => .ok (!r)
  | .le => setIssubset P v (.set w) id
  | .ge => setIssuperset P v (.set w) id
  | .lt => if v.used ≥ w.used then .ok false else setIssubset P v (.set w) id
  | .gt => if v.used ≤ w.used then .ok false else setIssuperset P v (.set w) id

/-- Retry with the frozenset hash when `key` is a `set`: `setHash key` is
`PySet_Check(key) ? some (frozenset_hash_impl(key)) : none`. -/
def retryAsFrozen {α : Type} (setHash : K → Option Int) (key : K) (first : SM K α)
    (retry : Int → SM K α) : SM K α :=
  M.tryCatch first fun e =>
    match setHash key, e with
    | some h, .typeError _ => retry h
    | _, _ => M.throw e

/-- `set_contains_lock_held` (@3.14.7:2269-2286), `_PySet_Contains`, `set_contains`,
`set.__contains__` (:2583-2593), `frozenset.__contains__` (:2605-2626). -/
def setContains (setHash : K → Option Int) (key : K) : SM K Bool :=
  retryAsFrozen setHash key (setContainsKey P key) (setContainsEntry P key)

/-- `set_remove_impl` (:2640-2665). -/
def setRemove (setHash : K → Option Int) (key : K) : SM K Unit := do
  let rv ← retryAsFrozen setHash key (setDiscardKey P key) (setDiscardEntry P key)
  if !rv then M.throw (keyErr P key)

/-- `set_discard_impl` (:2680-2700). -/
def setDiscard (setHash : K → Option Int) (key : K) : SM K Unit := do
  let _ ← retryAsFrozen setHash key (setDiscardKey P key) (setDiscardEntry P key)

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
