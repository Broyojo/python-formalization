import PyLean.DictSet.Common

/-!
The hash table of `Objects/setobject.c` (CPython 3.14.7): linear probes, the perturbed
recurrence, dummies, `set_table_resize`, `pop`'s finger, iteration, the frozenset hash.
Line numbers refer to `Objects/setobject.c`.
-/

namespace PyLean.DictSet

open PyLean

/-- A `setentry`: NULL key (`hash` 0), `dummy` (`hash` -1), or active. -/
inductive Slot (K : Type) where
  | null
  | dummy
  | active (key : K) (hash : Int)
  deriving Repr, Inhabited, DecidableEq

/-- `PySetObject`. `tableId` stands for the pointer `so->table`: 0 is `so->smalltable`,
which is exactly the case `mask == 7`. `ident` is the object's address. `frozen` is
`PyFrozenSet_Check`, `exact` is `PyAnySet_CheckExact`, `tname` is `tp_name`. -/
structure SetObj (K : Type) where
  ident : Nat := 0
  fill : Nat := 0
  used : Nat := 0
  mask : Nat := 7
  table : List (Slot K) := List.replicate 8 .null
  hash : Int := -1
  finger : Nat := 0
  tableId : Nat := 0
  nextId : Nat := 1
  frozen : Bool := false
  exact : Bool := true
  tname : String := "set"
  deriving Repr, Inhabited

def LINEAR_PROBES : Nat := 9
def PySet_MINSIZE : Nat := 8

abbrev SM (K : Type) := M (SetObj K)

variable {K : Type}

namespace SetObj
def slot (so : SetObj K) (i : Nat) : Slot K := so.table.getD i .null
/-- `PyFrozenSet_CheckExact(so)`. -/
def frozenExact (so : SetObj K) : Bool := so.frozen && so.exact
/-- `sizeof(PySetObject)` is 200 on a 64-bit build; `set___sizeof___impl` (:2741-2750). -/
def sizeOf (so : SetObj K) : Nat := if so.tableId != 0 then 200 + (so.mask + 1) * 16 else 200
end SetObj

/-- The set probe recurrence (:244-245): `perturb >>= PERTURB_SHIFT;
i = (i * 5 + 1 + perturb) & mask`. -/
def setProbeStep (mask i perturb : Nat) : Nat × Nat :=
  let p := perturb >>> PERTURB_SHIFT
  ((i * 5 + 1 + p) &&& mask, p)

/-- `probes = (i + LINEAR_PROBES <= mask) ? LINEAR_PROBES : 0` (:232). -/
def linearProbes (i mask : Nat) : Nat := if i + LINEAR_PROBES ≤ mask then LINEAR_PROBES else 0

/-- What one `do { ... } while (probes--)` block of `set_lookkey` ends with. -/
inductive LookScan where
  | found (slot : Nat)
  | restart
  | next (mask : Nat)
  deriving Repr, Inhabited

section Look
variable [DecidableEq K] (P : Proto K (SetObj K))

/-- Is the entry still what it was before the comparison?
`table != so->table || entry->key != startkey` (@3.14.7:118). -/
def setChanged (so : SetObj K) (table slot : Nat) (startkey : K) : Bool :=
  decide (table ≠ so.tableId) ||
    match so.slot slot with
    | .active k _ => decide (k ≠ startkey)
    | _ => true

/-- One pass of the body of the `do` loop of `set_lookkey` (@3.14.7:95-125): `.inl` ends the block, `.inr`
carries on at the next entry with this `mask`. -/
def lookStep (frozen : Bool) (key : K) (hash : Int) (slot mask : Nat) : SM K (LookScan ⊕ Nat) := do
  let so ← M.get
  match so.slot slot with
  | .null => return .inl (.found slot)
  | .dummy => return .inr mask
  | .active startkey h =>
    if h = hash then
      if startkey = key then return .inl (.found slot)
      if P.isStr startkey && P.isStr key && P.strEq startkey key then return .inl (.found slot)
      let table := so.tableId
      let cmp ← P.eq startkey key
      if !frozen then
        let so' ← M.get
        if setChanged so' table slot startkey then return .inl .restart
      if cmp then return .inl (.found slot)
      let so' ← M.get
      return .inr so'.mask
    else return .inr mask

/-- The inner loop of `set_lookkey` (:233-243): `do { ... } while (probes--)`. -/
def lookScan (frozen : Bool) (key : K) (hash : Int) : Nat → Nat → Nat → SM K LookScan
  | 0, slot, mask => do
    match ← lookStep P frozen key hash slot mask with
    | .inl r => return r
    | .inr m => return .next m
  | p + 1, slot, mask => do
    match ← lookStep P frozen key hash slot mask with
    | .inl r => return r
    | .inr m => lookScan frozen key hash p (slot + 1) m

/-- The outer loop of `set_lookkey` (:230-246). -/
def lookOuter (frozen : Bool) (key : K) (hash : Int) : Nat → Nat → Nat → Nat → SM K (Option Nat)
  | 0, _, _, _ => M.throw .modelFuel
  | fuel + 1, i, perturb, mask => do
    let r ← lookScan P frozen key hash (linearProbes i mask) i mask
    match r with
    | .found s => return some s
    | .restart => return none
    | .next mask' =>
      let n := setProbeStep mask' i perturb
      lookOuter frozen key hash fuel n.1 n.2 mask'

def setProbeFuel (mask : Nat) : Nat := mask + 15

/-- `set_lookkey` (@3.14.7:78-130): the slot where the search stopped; an exception is the NULL
return. A restart is the recursive call at @3.14.7:119. -/
def setLookkeyAux (key : K) (hash : Int) : Nat → SM K Nat
  | 0 => M.throw .modelFuel
  | restarts + 1 => do
    let so ← M.get
    let u := toU64 hash
    let r ← lookOuter P so.frozenExact key hash (setProbeFuel so.mask) (u &&& so.mask) u so.mask
    match r with
    | some s => return s
    | none => setLookkeyAux key hash restarts

def setLookkey (key : K) (hash : Int) : SM K Nat := setLookkeyAux P key hash 256

end Look

/-- The first-NULL search inside one block of `set_insert_clean` (:392-401). -/
def cleanScan (table : List (Slot K)) (i j : Nat) : Option Nat :=
  match j with
  | 0 => none
  | j + 1 =>
    match table.getD (i + LINEAR_PROBES - j) .null with
    | .null => some (i + LINEAR_PROBES - j)
    | _ => cleanScan table i j

/-- `set_insert_clean` (:383-408): the slot. -/
def setInsertCleanSlot (table : List (Slot K)) (mask : Nat) : Nat → Nat → Nat → Py Nat
  | 0, _, _ => .error .modelFuel
  | fuel + 1, i, perturb =>
    match table.getD i .null with
    | .null => .ok i
    | _ =>
      let hit := if i + LINEAR_PROBES ≤ mask then cleanScan table i LINEAR_PROBES else none
      match hit with
      | some s => .ok s
      | none =>
        let n := setProbeStep mask i perturb
        setInsertCleanSlot table mask fuel n.1 n.2

def setInsertClean (table : List (Slot K)) (mask : Nat) (key : K) (hash : Int) : Py (List (Slot K)) :=
  let u := toU64 hash
  match setInsertCleanSlot table mask (setProbeFuel mask) (u &&& mask) u with
  | .ok s => .ok (table.set s (.active key hash))
  | .error e => .error e

/-- Reinsert the active entries in table order (:543-556). -/
def reinsertAll (mask : Nat) : List (Slot K) → List (Slot K) → Py (List (Slot K))
  | acc, [] => .ok acc
  | acc, .active k h :: rest =>
    match setInsertClean acc mask k h with
    | .ok t => reinsertAll mask t rest
    | .error e => .error e
  | acc, _ :: rest => reinsertAll mask acc rest

/-- The smallest table size greater than `minused` (:497-500). -/
def setNewSize (minused : Nat) : Nat → Nat → Nat
  | 0, n => n
  | f + 1, n => if n ≤ minused then setNewSize minused f (n <<< 1) else n

/-- `set_table_resize` (:483-563). -/
def setTableResize (minused : Nat) : SM K Unit := do
  let so ← M.get
  let newsize := setNewSize minused 64 PySet_MINSIZE
  if newsize == PySet_MINSIZE && so.mask + 1 == PySet_MINSIZE && so.fill == so.used then
    return ()
  -- `PyMem_NEW(setentry, newsize)` (:527): a request above PY_SSIZE_T_MAX / sizeof(setentry)
  -- fails without calling the allocator; an allocator that gives up earlier is not modelled.
  if newsize > (2 ^ 63 - 1) / 16 then M.throw (.named "MemoryError" "")
  let fresh : List (Slot K) := List.replicate newsize .null
  let t ← M.lift (reinsertAll (newsize - 1) fresh so.table)
  M.put { so with
    mask := newsize - 1
    table := t
    fill := so.used
    tableId := if newsize == PySet_MINSIZE then 0 else so.nextId
    nextId := so.nextId + 1 }

/-- The resize at the end of `set_add_entry_takeref` (:324-326) and of
`set_difference_update_internal` (:2028). -/
def setGrow : SM K Unit := do
  let so ← M.get
  setTableResize (if so.used > 50000 then so.used * 2 else so.used * 4)

/-- What one block of `set_add_entry_takeref` ends with. -/
inductive AddScan where
  | unused (slot : Nat) (freeslot : Option Nat) (mask : Nat)
  | active
  | restart
  | next (freeslot : Option Nat) (mask : Nat)
  deriving Repr, Inhabited

section Add
variable [DecidableEq K] (P : Proto K (SetObj K))

/-- One pass of the body of the `do` loop of `set_add_entry_takeref` (:275-302). -/
def addStep (key : K) (hash : Int) (slot mask : Nat) (freeslot : Option Nat) :
    SM K (AddScan ⊕ (Nat × Option Nat)) := do
  let so ← M.get
  match so.slot slot with
  | .null => return .inl (.unused slot freeslot mask)
  | .dummy =>
    -- else if (entry->hash == -1): the last dummy seen wins
    return .inr (mask, some slot)
  | .active startkey h =>
    if h = hash then
      if startkey = key then return .inl .active
      if P.isStr startkey && P.isStr key && P.strEq startkey key then return .inl .active
      let table := so.tableId
      let cmp ← P.eq startkey key
      if cmp then return .inl .active
      let so' ← M.get
      if setChanged so' table slot startkey then return .inl .restart
      return .inr (so'.mask, freeslot)
    else return .inr (mask, freeslot)

/-- The inner loop of `set_add_entry_takeref` (:274-303). -/
def addScan (key : K) (hash : Int) : Nat → Nat → Nat → Option Nat → SM K AddScan
  | 0, slot, mask, freeslot => do
    match ← addStep P key hash slot mask freeslot with
    | .inl r => return r
    | .inr (m, fs) => return .next fs m
  | p + 1, slot, mask, freeslot => do
    match ← addStep P key hash slot mask freeslot with
    | .inl r => return r
    | .inr (m, fs) => addScan key hash p (slot + 1) m fs

def addOuter (key : K) (hash : Int) : Nat → Nat → Nat → Nat → Option Nat → SM K AddScan
  | 0, _, _, _, _ => M.throw .modelFuel
  | fuel + 1, i, perturb, mask, freeslot => do
    let r ← addScan P key hash (linearProbes i mask) i mask freeslot
    match r with
    | .next fs mask' =>
      let n := setProbeStep mask' i perturb
      addOuter key hash fuel n.1 n.2 mask' fs
    | r => return r

/-- `set_add_entry_takeref` (:252-335), `set_add_entry` (:337-343). -/
def setAddEntryAux (key : K) (hash : Int) : Nat → SM K Unit
  | 0 => M.throw .modelFuel
  | restarts + 1 => do
    let so ← M.get
    let u := toU64 hash
    let r ← addOuter P key hash (setProbeFuel so.mask) (u &&& so.mask) u so.mask none
    match r with
    | .active => return ()
    | .restart => setAddEntryAux key hash restarts
    | .next _ _ => M.unreachable
    | .unused slot freeslot mask =>
      let so ← M.get
      match freeslot with
      | none =>
        -- found_unused
        let so' := { so with
          fill := so.fill + 1
          used := so.used + 1
          table := so.table.set slot (.active key hash) }
        M.put so'
        if so'.fill * 5 < mask * 3 then return ()
        setGrow
      | some fs =>
        match so.slot fs with
        | .dummy =>
          M.put { so with used := so.used + 1, table := so.table.set fs (.active key hash) }
        | _ => setAddEntryAux key hash restarts

def setAddEntry (key : K) (hash : Int) : SM K Unit := setAddEntryAux P key hash 256

/-- `set_unhashable_type` (:345-359). -/
def setUnhashableType (key : K) (e : PyExc) : PyExc :=
  match e with
  | .typeError m => .typeError s!"cannot use '{P.typeName key}' as a set element ({m})"
  | e => e

/-- `_PyObject_HashFast` plus `set_unhashable_type`. -/
def setHashKey (key : K) : SM K Int :=
  match P.hash key with
  | .ok h => pure h
  | .error e => M.throw (setUnhashableType P key e)

/-- `set_add_key` (:600-609), `_PySet_AddTakeRef` (:361-373), `PySet_Add` (:3097-3123),
`set.add` (:2535-2542). -/
def setAddKey (key : K) : SM K Unit := do
  let hash ← setHashKey P key
  setAddEntry P key hash

/-- `set_contains_entry` (:565-574). -/
def setContainsEntry (key : K) (hash : Int) : SM K Bool := do
  let s ← setLookkey P key hash
  let so ← M.get
  match so.slot s with
  | .null => return false
  | _ => return true

/-- `set_contains_key` (:611-620), `PySet_Contains` (:3065-3080). -/
def setContainsKey (key : K) : SM K Bool := do
  let hash ← setHashKey P key
  setContainsEntry P key hash

/-- `set_discard_entry` (:579-598): `true` is `DISCARD_FOUND`. -/
def setDiscardEntry (key : K) (hash : Int) : SM K Bool := do
  let s ← setLookkey P key hash
  let so ← M.get
  match so.slot s with
  | .null => return false
  | _ =>
    M.put { so with used := so.used - 1, table := so.table.set s .dummy }
    return true

/-- `set_discard_key` (:622-631), `PySet_Discard` (:3082-3095). -/
def setDiscardKey (key : K) : SM K Bool := do
  let hash ← setHashKey P key
  setDiscardEntry P key hash

end Add

/-- `set_empty_to_minsize` (:633-643). -/
def setEmptyToMinsize (so : SetObj K) : SetObj K :=
  { so with
    table := List.replicate 8 .null
    fill := 0
    used := 0
    mask := PySet_MINSIZE - 1
    tableId := 0
    hash := -1 }

/-- `set_clear_internal` (:645-694), `_PySet_ClearInternal`, `PySet_Clear`, `set.clear`. -/
def setClearInternal (so : SetObj K) : SetObj K :=
  if so.tableId != 0 then setEmptyToMinsize so
  else if so.fill > 0 then setEmptyToMinsize so
  else so

/-- `set_next` (:709-731): `(pos after, key, hash)`. -/
def setNext (table : List (Slot K)) (mask : Nat) : Nat → Nat → Option (Nat × K × Int)
  | 0, _ => none
  | fuel + 1, i =>
    if i > mask then none
    else
      match table.getD i .null with
      | .active k h => some (i + 1, k, h)
      | _ => setNext table mask fuel (i + 1)

/-- The active entries in table order: the `while (set_next(...))` loops, and
`_PySet_NextEntry` / `_PySet_NextEntryRef` (:3125-3156). -/
def setEntries (so : SetObj K) : List (K × Int) :=
  so.table.filterMap fun
    | .active k h => some (k, h)
    | _ => none

/-- `set_len` (:821-826), `PySet_Size`. -/
def setLen (so : SetObj K) : Nat := so.used

/-- `set_pop_impl` (:910-934), `PySet_Pop`. -/
def setPop : SM K K := do
  let so ← M.get
  if so.used == 0 then M.throw (.keyError "'pop from an empty set'")
  let rec scan : Nat → Nat → Option (Nat × K)
    | 0, _ => none
    | f + 1, i =>
      match so.slot i with
      | .active k _ => some (i, k)
      | _ => scan f (if i + 1 > so.mask then 0 else i + 1)
  match scan (so.mask + 2) (so.finger &&& so.mask) with
  | none => M.unreachable
  | some (i, key) =>
    M.put { so with
      table := so.table.set i .dummy
      used := so.used - 1
      finger := i + 1 }
    return key

/-- `_shuffle_bits` (:953-957) on `Py_uhash_t`. -/
def shuffleBits (h : Nat) : Nat :=
  (((h ^^^ 89869747) ^^^ ((h <<< 16) % 2 ^ 64)) * 3644798167) % 2 ^ 64

/-- `entry->hash` of a slot as `Py_uhash_t`. -/
def Slot.hashU : Slot K → Nat
  | .null => 0
  | .dummy => toU64 (-1)
  | .active _ h => toU64 h

/-- `frozenset_hash_impl` (:972-1012). It runs on sets too (`set_contains_lock_held`). -/
def frozensetHashImpl (so : SetObj K) : Int :=
  let h0 := so.table.foldl (fun h s => h ^^^ shuffleBits s.hashU) 0
  let h1 := if (so.mask + 1 - so.fill) % 2 == 1 then h0 ^^^ shuffleBits 0 else h0
  let h2 := if (so.fill - so.used) % 2 == 1 then h1 ^^^ shuffleBits (toU64 (-1)) else h1
  let h3 := h2 ^^^ (((so.used + 1) * 1927868237) % 2 ^ 64)
  let h4 := h3 ^^^ ((h3 >>> 11) ^^^ (h3 >>> 25))
  let h5 := (h4 * 69069 + 907133923) % 2 ^ 64
  let h6 := if h5 == 2 ^ 64 - 1 then 590923713 else h5
  toI64 h6

/-- `frozenset_hash` (:1014-1027): the hash and the object caching it. -/
def frozensetHash (so : SetObj K) : Int × SetObj K :=
  if so.hash != -1 then (so.hash, so)
  else
    let h := frozensetHashImpl so
    (h, { so with hash := h })

/-- `setiterobject` (:1031-1037). `alive` is `si_set != NULL`. -/
structure SetIter where
  alive : Bool := true
  used : Int
  pos : Nat := 0
  len : Int
  deriving Repr, Inhabited

/-- `set_iter` (:1171-1184). -/
def setIterNew (so : SetObj K) : SetIter := { used := so.used, len := so.used }

/-- `setiter_len` (:1057-1065): `PyLong_FromSsize_t(len)`; 3.14.7 can return a negative
number here, see `setIterLenNonneg`. -/
def setiterLen (so : SetObj K) (si : SetIter) : Int :=
  if si.alive && decide (si.used = so.used) then si.len else 0

/-- `setiter_iternext` (:1095-1136). -/
def setiterNext (so : SetObj K) (si : SetIter) : Py (Option K) × SetIter :=
  if !si.alive then (.ok none, si)
  else if si.used != so.used then
    (.error (runtimeError "Set changed size during iteration"), { si with used := -1 })
  else
    match setNext so.table so.mask (so.mask + 2) si.pos with
    | some (pos', k, _) => (.ok (some k), { si with pos := pos', len := si.len - 1 })
    | none => (.ok none, { si with alive := false, pos := so.mask + 2 })

/-- `PyObject_LengthHint` as `list(it)` runs it first (`Objects/abstract.c`): a negative
hint raises `ValueError`. -/
def setiterLengthHint (so : SetObj K) (si : SetIter) : Py Nat :=
  let h := setiterLen so si
  if h < 0 then .error (.valueError "__length_hint__() should return >= 0")
  else .ok h.toNat

def setiterDrain (so : SetObj K) : Nat → SetIter → List K → Py (List K) × SetIter
  | 0, si, _ => (.error .modelFuel, si)
  | fuel + 1, si, acc =>
    match setiterNext so si with
    | (.error e, si') => (.error e, si')
    | (.ok none, si') => (.ok acc.reverse, si')
    | (.ok (some x), si') => setiterDrain so fuel si' (x :: acc)

/-- `list(it)`. -/
def setiterToList (so : SetObj K) (si : SetIter) : Py (List K) × SetIter :=
  match setiterLengthHint so si with
  | .error e => (.error e, si)
  | .ok _ => setiterDrain so (so.mask + 3) si []

/-- `setiter_reduce` (@3.14.7:875-891): drain a copy. -/
def setiterReduce (so : SetObj K) (si : SetIter) : Py (List K) := (setiterToList so si).1

/-- `set_repr_lock_held` (@3.14.7:565-617), `set_repr`. -/
def setRepr (krepr : K → Py String) (inRepr : Bool) (so : SetObj K) : Py String :=
  if inRepr then .ok s!"{so.tname}(...)"
  else if so.used == 0 then .ok s!"{so.tname}()"
  else
    match (setEntries so).mapM (fun e => krepr e.1) with
    | .error e => .error e
    | .ok rs =>
      let listrepr := ", ".intercalate rs
      if !(!so.frozen && so.exact) then .ok s!"{so.tname}(\{{listrepr}})"
      else .ok s!"\{{listrepr}}"

end PyLean.DictSet
