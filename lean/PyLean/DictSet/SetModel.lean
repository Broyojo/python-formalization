import PyLean.DictSet.Common

/-!
The hash table of `Objects/setobject.c` (CPython 3.15.2): linear probes, the perturbed
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
`PyFrozenSet_Check`, `exact` is `PyAnySet_CheckExact`, `tname` is `tp_name`. `reuse` is the
allocator, as an oracle: the blocks `PyMem_NEW` hands this set's next malloc'ed tables, in order, each
an address and the bytes it still holds, and once it is empty a new address (`nextId`) with nothing
in it. Nothing stops it from handing back the block of a table that was freed, with another size:
CPython's allocator does (bugs/dictset-set-lookup-table-aba). `stale` is what the block holds past
the end of the current table: the freed table's entries from `mask + 1` on. -/
structure SetBody (K : Type) where
  ident : Nat := 0
  fill : Nat := 0
  used : Nat := 0
  mask : Nat := 7
  table : List (Slot K) := List.replicate 8 .null
  hash : Int := -1
  finger : Nat := 0
  tableId : Nat := 0
  nextId : Nat := 1
  reuse : List (Nat × List (Slot K)) := []
  stale : List (Slot K) := []
  frozen : Bool := false
  exact : Bool := true
  tname : String := "set"
  deriving Repr, Inhabited

/-- The set a primitive works on, and the others a callback can reach while it does: `__eq__` and an
iterator run Python code, so an operation on two sets has both in its state, and `set_add_entry` on a
new result has the operands too. The field has no counterpart in C. -/
structure SetObj (K : Type) extends SetBody K where
  peers : List (SetBody K) := []
  deriving Repr, Inhabited

def LINEAR_PROBES : Nat := 9
def PySet_MINSIZE : Nat := 8

abbrev SM (K : Type) := M (SetObj K)

variable {K : Type}

namespace SetObj
def slot (so : SetObj K) (i : Nat) : Slot K := so.table.getD i .null
/-- `PyFrozenSet_CheckExact(so)`. -/
def frozenExact (so : SetObj K) : Bool := so.frozen && so.exact
/-- The entry at index `i` as C reads it through `&table[i]`: in the table, the table's; past its
end, the bytes the block still holds there (`stale`), NULL where it holds none. The set model reads
entries only this way; `slot` is the table's own view (iteration, the theorems on well-formed tables,
where the two agree: `mem_lt`, `mem_active`, `mem_of_ne_null`). -/
def mem (so : SetObj K) (i : Nat) : Slot K :=
  if i < so.table.length then so.slot i else so.stale.getD (i - so.table.length) .null

/-- A store through `&table[i]`: in the table, or past its end into the stale bytes. -/
def storeAt (so : SetObj K) (i : Nat) (x : Slot K) : SetObj K :=
  if i < so.table.length then { so with table := so.table.set i x }
  else { so with stale := so.stale.set (i - so.table.length) x }

theorem mem_lt (so : SetObj K) {i : Nat} (h : i < so.table.length) : so.mem i = so.slot i := by
  simp [mem, h]

theorem mem_active (so : SetObj K) {i : Nat} {k : K} {hh : Int} (h : so.slot i = .active k hh) :
    so.mem i = .active k hh := by
  unfold mem
  split
  · exact h
  · rename_i hn
    have : so.table[i]? = none := List.getElem?_eq_none (by omega)
    simp [slot, List.getD, this] at h

theorem mem_of_ne_null (so : SetObj K) {i : Nat} (h : so.slot i ≠ .null) : so.mem i = so.slot i := by
  unfold mem
  split
  · rfl
  · rename_i hn
    have : so.table[i]? = none := List.getElem?_eq_none (by omega)
    simp [slot, List.getD, this] at h

theorem storeAt_lt (so : SetObj K) {i : Nat} (x : Slot K) (h : i < so.table.length) :
    so.storeAt i x = { so with table := so.table.set i x } := by
  simp [storeAt, h]

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

/-- What one `do { ... } while (probes--)` block of `set_do_lookup` ends with. -/
inductive LookScan where
  | found (slot : Nat)
  /-- `SET_LOOKKEY_CHANGED`. -/
  | restart
  | next
  deriving Repr, Inhabited, DecidableEq

section Look
variable [DecidableEq K] (P : Proto K (SetObj K))

/-- Is the entry still what it was before the comparison?
`table != so->table || entry->key != startkey` (:159). -/
def setChanged (so : SetObj K) (table slot : Nat) (startkey : K) : Bool :=
  decide (table ≠ so.tableId) ||
    match so.mem slot with
    | .active k _ => decide (k ≠ startkey)
    | _ => true

/-- `set_compare_entry_lock_held` (:137-165): `.inl` ends the block, `.inr ()` carries on at the next
entry. `SET_LOOKKEY_EMPTY` and `SET_LOOKKEY_FOUND` both end it at this slot. -/
def compareLocked (key : K) (hash : Int) (slot : Nat) : SM K (LookScan ⊕ Unit) := do
  let so ← M.get
  match so.mem slot with
  | .null => return .inl (.found slot)
  | .dummy => return .inr ()
  | .active startkey h =>
    if h = hash then
      if startkey = key then return .inl (.found slot)
      if P.isStr startkey && P.isStr key && P.strEq startkey key then return .inl (.found slot)
      let table := so.tableId
      let cmp ← P.eq startkey key
      let so' ← M.get
      if setChanged so' table slot startkey then return .inl .restart
      if cmp then return .inl (.found slot)
      return .inr ()
    else return .inr ()

/-- `set_compare_frozenset` (:171-192): no check for a change, no shortcut for `str`, and the
identity test comes before the hash test, so a key found by identity need not have kept its hash. -/
def compareFrozen (key : K) (hash : Int) (slot : Nat) : SM K (LookScan ⊕ Unit) := do
  let so ← M.get
  match so.mem slot with
  | .null => return .inl (.found slot)
  | .dummy => return .inr ()
  | .active startkey h =>
    if startkey = key then return .inl (.found slot)
    if h = hash then
      let cmp ← P.eq startkey key
      if cmp then return .inl (.found slot)
      return .inr ()
    else return .inr ()

/-- The `compare_func` passed to `set_do_lookup`. -/
def lookStep (frozen : Bool) (key : K) (hash : Int) (slot : Nat) : SM K (LookScan ⊕ Unit) :=
  if frozen then compareFrozen P key hash slot else compareLocked P key hash slot

/-- The inner loop of `set_do_lookup` (:233-243): `do { ... } while (probes--)`. -/
def lookScan (frozen : Bool) (key : K) (hash : Int) : Nat → Nat → SM K LookScan
  | 0, slot => do
    match ← lookStep P frozen key hash slot with
    | .inl r => return r
    | .inr _ => return .next
  | p + 1, slot => do
    match ← lookStep P frozen key hash slot with
    | .inl r => return r
    | .inr _ => lookScan frozen key hash p (slot + 1)

/-- The outer loop of `set_do_lookup` (:220-248). `mask` is the argument, fixed for the whole search:
a table that was replaced comes back as `SET_LOOKKEY_CHANGED`. -/
def lookOuter (frozen : Bool) (key : K) (hash : Int) (mask : Nat) :
    Nat → Nat → Nat → SM K (Option Nat)
  | 0, _, _ => M.throw .modelFuel
  | fuel + 1, i, perturb => do
    let r ← lookScan P frozen key hash (linearProbes i mask) i
    match r with
    | .found s => return some s
    | .restart => return none
    | .next =>
      let n := setProbeStep mask i perturb
      lookOuter frozen key hash mask fuel n.1 n.2

def setProbeFuel (mask : Nat) : Nat := mask + 15

/-- The `do { ... } while (status == SET_LOOKKEY_CHANGED)` of `set_lookkey` (:422-426), with
`set_compare_entry_lock_held`: each turn passes `so->table` and `so->mask` as they are then, so a
restart walks the table `__eq__` left. `256` turns stand for "until no `__eq__` changes the table".

`setChanged` compares `tableId`, the table's address: the allocator (`SetBody.reuse`) can hand
back a freed table's address with another mask, and then, as in CPython, the test passes and the
walk goes on with the old mask (`aba_probe`, bugs/dictset-set-lookup-table-aba.yaml). The re-check
and the entry functions read through the pointer (`SetObj.mem`): past the end of the table, the
freed block's stale bytes. Every read of an entry in the probe walks (`compareLocked`,
`compareFrozen`, `addStep`, the `freeslot` test) and in the entry functions goes through
`SetObj.mem`, and every store of the add and discard through `storeAt`, as C reads and writes
through `&table[i]`. -/
def setLookkeyAux (key : K) (hash : Int) : Nat → SM K Nat
  | 0 => M.throw .modelFuel
  | restarts + 1 => do
    let so ← M.get
    let u := toU64 hash
    let r ← lookOuter P false key hash so.mask (setProbeFuel so.mask) (u &&& so.mask) u
    match r with
    | some s => return s
    | none => setLookkeyAux key hash restarts

/-- `set_lookkey` (:413-433): the slot where the search stopped, whose key says whether it was
found; an exception is `SET_LOOKKEY_ERROR`. `PyFrozenSet_CheckExact(so)` (:417) takes one
`set_do_lookup` with `set_compare_frozenset` (:418-420), which never answers
`SET_LOOKKEY_CHANGED` (`lookOuter_frozen_ne_restart`); anything else, a frozenset subclass too,
takes the locked loop. -/
def setLookkey (key : K) (hash : Int) : SM K Nat := do
  let so ← M.get
  if so.frozenExact then
    let u := toU64 hash
    let r ← lookOuter P true key hash so.mask (setProbeFuel so.mask) (u &&& so.mask) u
    match r with
    | some s => return s
    | none => M.unreachable
  else setLookkeyAux P key hash 256

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
    tableId := if newsize == PySet_MINSIZE then 0
      else match so.reuse with
        | (a, _) :: _ => a
        | [] => so.nextId
    stale := if newsize == PySet_MINSIZE then []
      else match so.reuse with
        | (_, b) :: _ => b.drop newsize
        | [] => []
    reuse := if newsize == PySet_MINSIZE then so.reuse else so.reuse.tail
    nextId := so.nextId + 1 }

/-- The resize at the end of `set_add_entry_takeref` (:324-326) and of
`set_difference_update_internal` (:2025-2028). -/
def setGrow : SM K Unit := do
  let so ← M.get
  setTableResize (if so.used > 50000 then so.used * 2 else so.used * 4)

/-- What one block of `set_add_entry_takeref` ends with. -/
inductive AddScan where
  | unused (slot : Nat) (freeslot : Option Nat) (mask : Nat)
  | active
  | restart
  | next (freeslot : Option Nat) (mask : Nat)
  deriving Repr, Inhabited, DecidableEq

section Add
variable [DecidableEq K] (P : Proto K (SetObj K))

/-- One pass of the body of the `do` loop of `set_add_entry_takeref` (:275-302): NULL ends the
walk (:275-276); an entry with the hash is the same object, an equal exact `str`, or is compared
(:277-297), and after a "no" the table and key are tested (:294-295) before `mask` is read again
(:296); a dummy becomes `freeslot` (:298-301). The table test has the scope of `setLookkeyAux`. -/
def addStep (key : K) (hash : Int) (slot mask : Nat) (freeslot : Option Nat) :
    SM K (AddScan ⊕ (Nat × Option Nat)) := do
  let so ← M.get
  match so.mem slot with
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

/-- The inner loop of `set_add_entry_takeref` (:274-303): `do { ... entry++; } while (probes--)`. -/
def addScan (key : K) (hash : Int) : Nat → Nat → Nat → Option Nat → SM K AddScan
  | 0, slot, mask, freeslot => do
    match ← addStep P key hash slot mask freeslot with
    | .inl r => return r
    | .inr (m, fs) => return .next fs m
  | p + 1, slot, mask, freeslot => do
    match ← addStep P key hash slot mask freeslot with
    | .inl r => return r
    | .inr (m, fs) => addScan key hash p (slot + 1) m fs

/-- The `while (1)` of `set_add_entry_takeref` (:271-306): a block of `linearProbes i mask` entries
from `i`, then `perturb >>= PERTURB_SHIFT; i = (i * 5 + 1 + perturb) & mask` with the mask as the
block left it (:304-305). -/
def addOuter (key : K) (hash : Int) : Nat → Nat → Nat → Nat → Option Nat → SM K AddScan
  | 0, _, _, _, _ => M.throw .modelFuel
  | fuel + 1, i, perturb, mask, freeslot => do
    let r ← addScan P key hash (linearProbes i mask) i mask freeslot
    match r with
    | .next fs mask' =>
      let n := setProbeStep mask' i perturb
      addOuter key hash fuel n.1 n.2 mask' fs
    | r => return r

/-- `set_add_entry_takeref` (:252-335), `set_add_entry` (:337-343). Each turn is the `restart:`
label (:264-269): `mask`, `i`, `perturb` from `so` as it is now and `freeslot = NULL`. The walk
ends at `found_active` (:328-330), at a restart (:294-295), or at a NULL: with no `freeslot` the
key goes there and the table may grow (:319-326); with one, a `freeslot` that `__eq__` refilled
(`freeslot->hash != -1`, :311-313) restarts, and otherwise the key goes in the dummy (:314-317). -/
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
        let so' := { so.storeAt slot (.active key hash) with
          fill := so.fill + 1
          used := so.used + 1 }
        M.put so'
        if so'.fill * 5 < mask * 3 then return ()
        setGrow
      | some fs =>
        match so.mem fs with
        | .dummy =>
          M.put { so.storeAt fs (.active key hash) with used := so.used + 1 }
        | _ => setAddEntryAux key hash restarts

def setAddEntry (key : K) (hash : Int) : SM K Unit := setAddEntryAux P key hash 256

/-- `set_unhashable_type` (:345-359): only an exception whose type is exactly `TypeError`
(`Py_IS_TYPE`, :350) is replaced, by `TypeError("cannot use '%T' as a set element (%S)")`, where
`%S` is `str(exc)`, here the message; a subclass of `TypeError` and anything else is re-raised as it
was (:351-352). -/
def setUnhashableType (key : K) (e : PyExc) : PyExc :=
  match e with
  | .typeError m => .typeError s!"cannot use '{P.typeName key}' as a set element ({m})"
  | e => e

/-- `_PyObject_HashFast(key)` and, when it fails, `set_unhashable_type(key)` (:603-607, :614-618,
:625-629): `__hash__` runs as Python code, so whatever it did to the state stands, whether it then
answered or raised. -/
def setHashKey (key : K) : SM K Int :=
  M.tryCatch (P.hashM key) fun e => M.throw (setUnhashableType P key e)

/-- `set_add_key` (:600-609), `_PySet_AddTakeRef` (:361-373), `PySet_Add` (:3097-3123),
`set.add` (:2535-2542). -/
def setAddKey (key : K) : SM K Unit := do
  let hash ← setHashKey P key
  setAddEntry P key hash

/-- `set_contains_entry` (:565-574). -/
def setContainsEntry (key : K) (hash : Int) : SM K Bool := do
  let s ← setLookkey P key hash
  let so ← M.get
  match so.mem s with
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
  match so.mem s with
  | .null => return false
  | _ =>
    M.put { so.storeAt s .dummy with used := so.used - 1 }
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
    stale := []
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

/-- `frozenset_hash_impl` (:972-1012). It runs on sets too (`_PySet_Contains`). -/
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

/-- `setiter_len` (:1057-1065): `PyLong_FromSsize_t(len)`; 3.15.2 can return a negative
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
  if h < 0 then .error (.valueError "set_iterator.__length_hint__() must return a non-negative int")
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

/-- `setiter_reduce` (:1070-1085): drain a copy. -/
def setiterReduce (so : SetObj K) (si : SetIter) : Py (List K) := (setiterToList so si).1

/-- `set_repr_lock_held` (:757-808), `set_repr`. -/
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
