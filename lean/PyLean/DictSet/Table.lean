import PyLean.DictSet.Common

/-!
The compact dict table of `Objects/dictobject.c` (CPython 3.15.2): `dk_indices`,
insertion-ordered `dk_entries`, combined and split forms, the probe sequence,
`USABLE_FRACTION`, `GROWTH_RATE`, `dictresize`, insertion, deletion with
`DKIX_DUMMY`. Line numbers refer to `Objects/dictobject.c` unless stated.
-/

namespace PyLean.DictSet

open PyLean

/-- `DictKeysKind` (`pycore_dict.h:193-197`). -/
inductive Kind where
  | general | unicode | split
  deriving DecidableEq, Repr, Inhabited

/-- `PyDictKeyEntry`. A `PyDictUnicodeEntry` has no hash field: C reads the hash
cached in the string (`unicode_get_hash`, :440-444), which is this field. -/
structure Ent (K V : Type) where
  key : K
  hash : Int
  value : V
  deriving Repr, Inhabited

/-- `PyDictKeysObject`. `entries` is `dk_entries[0 .. dk_nentries)`, so
`dk_nentries` is its length; `none` is a slot whose key and value are NULL.
`ident` is the object's address, used by `dk == mp->ma_keys` (:1142) and by odict's
`od_resize_sentinel`. For a split table `V` is `Unit`: the values live in the dict. -/
structure Keys (K V : Type) where
  ident : Nat
  log2Size : Nat
  kind : Kind
  usable : Int
  indices : List Int
  entries : List (Option (Ent K V))
  version : Nat := 0
  deriving Repr, Inhabited

/-- `DKIX_EMPTY`, `DKIX_DUMMY`, `DKIX_KEY_CHANGED` (`pycore_dict.h:184-190`).
`DKIX_ERROR` is an exception in `M`. -/
def DKIX_EMPTY : Int := -1
def DKIX_DUMMY : Int := -2
def DKIX_KEY_CHANGED : Int := -4

def PyDict_LOG_MINSIZE : Nat := 3
def PyDict_MINSIZE : Nat := 8
def SHARED_KEYS_MAX_SIZE : Nat := 30
def NEXT_LOG2_SHARED_KEYS_MAX_SIZE : Nat := 6

/-- `USABLE_FRACTION(n)` (:581). -/
def usableFraction (n : Nat) : Nat := (n <<< 1) / 3

/-- `GROWTH_RATE(d)` (:628). -/
def growthRate (used : Nat) : Nat := used * 3

/-- `calculate_log2_keysize` (:584-604), the 64-bit `_Py_bit_length` branch. -/
def calculateLog2Keysize (minsize : Nat) : Nat :=
  bitLength (max minsize PyDict_MINSIZE - 1)

/-- `estimate_log2_keysize` (:611-615). -/
def estimateLog2Keysize (n : Nat) : Nat := calculateLog2Keysize ((n * 3 + 1) / 2)

/-- `dk_log2_index_bytes` as chosen by `new_keys_object` (:803-816). -/
def log2IndexBytes (log2Size : Nat) : Nat :=
  if log2Size < 8 then log2Size
  else if log2Size < 16 then log2Size + 1
  else if log2Size >= 32 then log2Size + 3
  else log2Size + 2

/-- `new_keys_object` (:793-847). -/
def newKeysObject {K V : Type} (ident log2Size : Nat) (unicode : Bool) : Keys K V :=
  { ident, log2Size
    kind := if unicode then .unicode else .general
    usable := usableFraction (2 ^ log2Size)
    indices := List.replicate (2 ^ log2Size) DKIX_EMPTY
    entries := []
    version := 0 }

/-- `Py_EMPTY_KEYS` (:636-651). `dk_log2_size` is 0, which no allocated table has,
so `log2Size = 0` is the test `keys == Py_EMPTY_KEYS`. -/
def emptyKeys {K V : Type} : Keys K V :=
  { ident := 0, log2Size := 0, kind := .unicode, usable := 0
    indices := [DKIX_EMPTY], entries := [], version := 1 }

namespace Keys
variable {K V : Type}

/-- `DK_SIZE(k)`. -/
def size (k : Keys K V) : Nat := 2 ^ k.log2Size
/-- `DK_MASK(k)`. -/
def mask (k : Keys K V) : Nat := k.size - 1
/-- `dk_nentries`. -/
def nentries (k : Keys K V) : Nat := k.entries.length
/-- `DK_IS_UNICODE(k)` (`pycore_dict.h:287`). -/
def isUnicode (k : Keys K V) : Bool := k.kind != .general
/-- `dictkeys_get_index` (:517-539). The C width switch is storage only; the widths are
checked by `indexWidthFits`. -/
def getIndex (k : Keys K V) (i : Nat) : Int := k.indices.getD i DKIX_EMPTY
/-- `dictkeys_set_index` (:542-567). -/
def setIndex (k : Keys K V) (i : Nat) (ix : Int) : Keys K V :=
  { k with indices := k.indices.set i ix }
/-- `DK_ENTRIES(k)[ix]`, if `me_key` is not NULL. -/
def entry (k : Keys K V) (ix : Nat) : Option (Ent K V) := (k.entries[ix]?).join
/-- Is this `Py_EMPTY_KEYS`? -/
def isEmpty (k : Keys K V) : Bool := k.log2Size == 0
/-- `_PyDict_KeysSize` (:5126-5135): 32 is `sizeof(PyDictKeysObject)`, 24 and 16 the
entry sizes on a 64-bit build. -/
def bytes (k : Keys K V) : Nat :=
  let es := if k.kind == .general then 24 else 16
  32 + 2 ^ (if k.isEmpty then 3 else log2IndexBytes k.log2Size) + usableFraction k.size * es

end Keys

/-- `PyDictValues` (`pycore_dict.h:257`). `order` is the insertion-order array, so
`size` is its length. `capacity` is `values.length`. -/
structure Values (V : Type) where
  values : List (Option V)
  order : List Nat
  embedded : Bool := false
  valid : Bool := true
  deriving Repr, Inhabited

namespace Values
variable {V : Type}
def capacity (v : Values V) : Nat := v.values.length
/-- `get_index_from_order` (:662-669). -/
def indexFromOrder (v : Values V) (i : Nat) : Nat := v.order.getD i 0
/-- `_PyDictValues_AddToInsertionOrder` (`pycore_dict.h:337-347`). -/
def addToOrder (v : Values V) (ix : Nat) : Values V := { v with order := v.order ++ [ix] }
/-- `delete_index_from_values` (:2864-2880): find `ix`, shift the rest down. -/
def deleteIndex (v : Values V) (ix : Nat) : Values V := { v with order := v.order.erase ix }
/-- `values->values[ix]`. -/
def get (v : Values V) (ix : Nat) : Option V := (v.values[ix]?).join
def set (v : Values V) (ix : Nat) (x : Option V) : Values V :=
  { v with values := v.values.set ix x }
/-- `new_values` (:878-891), all slots NULL (`new_dict_with_shared_keys`, :980-982). -/
def new (size : Nat) : Values V := { values := List.replicate size none, order := [] }
end Values

/-- `values_size_from_count` (:866-874). -/
def valuesSizeFromCount (count : Nat) : Nat :=
  let suffix := (count + 7) / 8 * 8
  (count + 1) * 8 + suffix

/-- `shared_keys_usable_size` (`pycore_dict.h:353-365`). -/
def sharedKeysUsableSize {K V : Type} (k : Keys K V) : Nat :=
  (k.entries.length + k.usable).toNat

/-- `ma_keys` and `ma_values`: a combined table, or shared keys plus values. -/
inductive Body (K V : Type) where
  | combined (k : Keys K V)
  | split (k : Keys K Unit) (v : Values V)
  deriving Repr, Inhabited

/-- What stands for the `-2` of `dict_merge` in the error channel. -/
def mergeDupExc : PyExc := .named "dict_merge returned -2" ""

/-- `PyErr_BadInternalCall()`. -/
def badInternalCallT : PyExc := systemError "~bad argument to internal function"

/-- The macro `frozendict_does_not_support` (:2728-2730). -/
def frozendictNoSupport (what : String) : PyExc :=
  .typeError s!"frozendict object does not support item {what}"

/-- A second `PyDictObject`, as a callback sees it: the fields of `PyDict` without `peer`. -/
structure PeerDict (K V : Type) where
  ident : Nat
  used : Nat
  body : Body K V
  nextId : Nat
  deriving Repr, Inhabited

/-- `PyDictObject`. `ident` is its address; `nextId` is the allocator handing out
fresh `Keys.ident`s.

`peer` is not a field of the C struct. The state of `DM` is what a callback can reach, and
during `dict_dict_merge` that is two objects: the receiver and the source, which a key's
`__eq__` may mutate (`orig_size` at :4249 exists for this). `peer` carries the source; every
table operation leaves it alone, so only a callback, through `Proto.eq`, can change it. -/
structure PyDict (K V : Type) where
  ident : Nat := 0
  used : Nat := 0
  body : Body K V := .combined emptyKeys
  nextId : Nat := 1
  peer : Option (PeerDict K V) := none
  /-- The note `_PyErr_FormatNote` put on the exception being raised. Not a field of the C struct:
  `PyExc` has no notes, and an operation that raises can carry one here. -/
  note : Option String := none
  /-- `PyFrozenDict_Check(op)`. A frozendict is a `PyDictObject` with `ma_hash` after it. -/
  frozen : Bool := false
  /-- `ma_hash` (`Include/cpython/dictobject.h`): `-1` until `frozendict_hash` has run. -/
  fhash : Int := -1
  /-- `*dupkey` of `dict_merge`, written when it returns `-2`. Not a field of the C struct. -/
  dupkey : Option K := none
  deriving Repr, Inhabited

def PyDict.toPeer {K V : Type} (d : PyDict K V) : PeerDict K V :=
  { ident := d.ident, used := d.used, body := d.body, nextId := d.nextId }

def PeerDict.toDict {K V : Type} (p : PeerDict K V) : PyDict K V :=
  { ident := p.ident, used := p.used, body := p.body, nextId := p.nextId }

namespace Body
variable {K V : Type}

def ident : Body K V → Nat
  | .combined k => k.ident
  | .split k _ => k.ident
def log2Size : Body K V → Nat
  | .combined k => k.log2Size
  | .split k _ => k.log2Size
def kind : Body K V → Kind
  | .combined k => k.kind
  | .split k _ => k.kind
def usable : Body K V → Int
  | .combined k => k.usable
  | .split k _ => k.usable
def nentries : Body K V → Nat
  | .combined k => k.nentries
  | .split k _ => k.nentries
def getIndex : Body K V → Nat → Int
  | .combined k, i => k.getIndex i
  | .split k _, i => k.getIndex i
def mask (b : Body K V) : Nat := 2 ^ b.log2Size - 1
def isUnicode (b : Body K V) : Bool := b.kind != .general
/-- `_PyDict_HasSplitTable(mp)`. -/
def isSplit : Body K V → Bool
  | .combined _ => false
  | .split _ _ => true
/-- `mp->ma_keys == Py_EMPTY_KEYS`. -/
def isEmptyKeys (b : Body K V) : Bool := b.log2Size == 0
/-- Key and hash of `dk_entries[ix]`. -/
def entryKH : Body K V → Nat → Option (K × Int)
  | .combined k, ix => (k.entry ix).map fun e => (e.key, e.hash)
  | .split k _, ix => (k.entry ix).map fun e => (e.key, e.hash)
/-- `*value_addr` of `_Py_dict_lookup` (:1365-1375, :1382-1387). -/
def valueAt : Body K V → Nat → Option V
  | .combined k, ix => (k.entry ix).map (·.value)
  | .split _ v, ix => v.get ix
end Body

variable {K V : Type}

/-- The fuel that suffices for any probe loop on a table of `2^log2` slots with an
empty slot: at most 13 shifts bring a 64-bit `perturb` to 0, and `5*i+1` then has full
period (`Probe.lean`). -/
def probeFuel (log2 : Nat) : Nat := 2 ^ log2 + 14

/-- `do_lookup` (:1081-1123): the probe loop, over any `check_lookup`. The two copies of
the loop body in C are a manual unrolling; `check` returning a negative value is
`DKIX_KEY_CHANGED` (exceptions travel in `M`). The index table is re-read at every step
because `dk` is a pointer: a comparison that leaves `dk == mp->ma_keys` may still have
written through it. -/
def doLookup {σ : Type} (getIx : σ → Nat → Int) (check : Nat → M σ Int) :
    Nat → Nat → Nat → Nat → M σ Int
  | 0, _, _, _ => M.throw .modelFuel
  | fuel + 1, mask, i, perturb => fun s =>
    let ix := getIx s i
    let next := probeStep mask i perturb
    if ix ≥ 0 then
      match check ix.toNat s with
      | (.error e, s') => (.error e, s')
      | (.ok cmp, s') =>
        if cmp < 0 then (.ok cmp, s')
        else if cmp != 0 then (.ok ix, s')
        else doLookup getIx check fuel mask next.1 next.2 s'
    else if ix == DKIX_EMPTY then (.ok DKIX_EMPTY, s)
    else doLookup getIx check fuel mask next.1 next.2 s

abbrev DM (K V : Type) := M (PyDict K V)

section Lookup
variable [DecidableEq K] (P : Proto K (PyDict K V))

/-- After a comparison: `dk == mp->ma_keys && ep->me_key == startkey` (:1142, :1198). -/
def stillThere (mp : PyDict K V) (dk ix : Nat) (startkey : K) : Bool :=
  decide (mp.body.ident = dk) &&
    match mp.body.entryKH ix with
    | some (k, _) => decide (k = startkey)
    | none => false

/-- `compare_unicode_generic` (:1125-1151). -/
def compareUnicodeGeneric (ix : Nat) (key : K) (hash : Int) : DM K V Int := fun mp =>
  match mp.body.entryKH ix with
  | none => (.error .modelFuel, mp)
  | some (epKey, epHash) =>
    if epHash = hash then
      match P.eq epKey key mp with
      | (.error e, mp') => (.error e, mp')
      | (.ok cmp, mp') =>
        if stillThere mp' mp.body.ident ix epKey then (.ok (if cmp then 1 else 0), mp')
        else (.ok DKIX_KEY_CHANGED, mp')
    else (.ok 0, mp)

/-- `compare_generic` (:1181-1207). -/
def compareGeneric (ix : Nat) (key : K) (hash : Int) : DM K V Int := fun mp =>
  match mp.body.entryKH ix with
  | none => (.error .modelFuel, mp)
  | some (epKey, epHash) =>
    if epKey = key then (.ok 1, mp)
    else if epHash = hash then
      match P.eq epKey key mp with
      | (.error e, mp') => (.error e, mp')
      | (.ok cmp, mp') =>
        if stillThere mp' mp.body.ident ix epKey then (.ok (if cmp then 1 else 0), mp')
        else (.ok DKIX_KEY_CHANGED, mp')
    else (.ok 0, mp)

/-- `compare_unicode_unicode` (:1160-1173). No callback can run here. -/
def compareUnicodeUnicode (e : Option (K × Int)) (key : K) (hash : Int) : Bool :=
  match e with
  | some (epKey, epHash) => decide (epKey = key) || (decide (epHash = hash) && P.strEq epKey key)
  | none => false

/-- `unicodekeys_lookup_unicode` (:1175-1179) on a keys object, with no dict at hand. -/
def unicodekeysLookupUnicode {W : Type} (dk : Keys K W) (key : K) (hash : Int) : Py Int :=
  let u := toU64 hash
  (doLookup (σ := Unit) (fun _ i => dk.getIndex i)
    (fun ix => pure (if compareUnicodeUnicode P ((dk.entry ix).map fun e => (e.key, e.hash)) key hash
                     then 1 else 0))
    (probeFuel dk.log2Size) dk.mask (u &&& dk.mask) u ()).1

/-- `dictkeys_get_index(dk, i)` on the dict's current keys. -/
def bodyIx (s : PyDict K V) (i : Nat) : Int := s.body.getIndex i

/-- `check_lookup` of `unicodekeys_lookup_unicode` on the dict's current keys. -/
def checkUnicode (key : K) (hash : Int) : Nat → DM K V Int := fun ix s =>
  (.ok (if compareUnicodeUnicode P (s.body.entryKH ix) key hash then 1 else 0), s)

/-- `unicodekeys_lookup_generic` (:1154-1158). -/
def unicodekeysLookupGeneric (mask : Nat) (fuel : Nat) (key : K) (hash : Int) : DM K V Int :=
  let u := toU64 hash
  doLookup bodyIx (fun ix => compareUnicodeGeneric P ix key hash) fuel mask (u &&& mask) u

/-- `dictkeys_generic_lookup` (:1209-1213). -/
def dictkeysGenericLookup (mask : Nat) (fuel : Nat) (key : K) (hash : Int) : DM K V Int :=
  let u := toU64 hash
  doLookup bodyIx (fun ix => compareGeneric P ix key hash) fuel mask (u &&& mask) u

/-- How many times `goto start` may run in the model. -/
def restartFuel : Nat := 256

/-- `_Py_dict_lookup` (:1327-1391): `(ix, *value_addr)`. An exception here is
`DKIX_ERROR`. The value is read after the loop, from the current state. -/
def dictLookupAux (key : K) (hash : Int) : Nat → DM K V (Int × Option V)
  | 0 => M.throw .modelFuel
  | restarts + 1 => fun mp =>
    let mask := mp.body.mask
    let fuel := probeFuel mp.body.log2Size
    let u := toU64 hash
    let r : Py Int × PyDict K V :=
      if mp.body.kind != .general then
        if P.isStr key then
          doLookup bodyIx (checkUnicode P key hash) fuel mask (u &&& mask) u mp
        else
          unicodekeysLookupGeneric P mask fuel key hash mp
      else
        dictkeysGenericLookup P mask fuel key hash mp
    match r with
    | (.error e, mp') => (.error e, mp')
    | (.ok ix, mp') =>
      if ix == DKIX_KEY_CHANGED then dictLookupAux key hash restarts mp'
      else (.ok (ix, if ix ≥ 0 then mp'.body.valueAt ix.toNat else none), mp')

def dictLookup (key : K) (hash : Int) : DM K V (Int × Option V) :=
  dictLookupAux P key hash restartFuel

end Lookup

/-- `lookdict_index` (:1059-1079): the slot holding entry `index`, or `DKIX_EMPTY`. -/
def lookdictIndexLoop (indices : List Int) (mask index : Nat) : Nat → Nat → Nat → Py Int
  | 0, _, _ => .error .modelFuel
  | fuel + 1, i, perturb =>
    let ix := indices.getD i DKIX_EMPTY
    if ix == (index : Int) then .ok i
    else if ix == DKIX_EMPTY then .ok DKIX_EMPTY
    else
      let next := probeStep mask i perturb
      lookdictIndexLoop indices mask index fuel next.1 next.2

def lookdictIndex {W : Type} (k : Keys K W) (hash : Int) (index : Nat) : Py Int :=
  let u := toU64 hash
  lookdictIndexLoop k.indices k.mask index (probeFuel k.log2Size) (u &&& k.mask) u

/-- The loop of `find_empty_slot` (:1853-1857) and of `build_indices_*` (:2107-2110,
@3.14.7:2032-2035): walk the probe sequence until `stop (slot)`. -/
def probeUntil (stop : Int → Bool) (indices : List Int) (mask : Nat) : Nat → Nat → Nat → Py Nat
  | 0, _, _ => .error .modelFuel
  | fuel + 1, i, perturb =>
    if stop (indices.getD i DKIX_EMPTY) then .ok i
    else
      let next := probeStep mask i perturb
      probeUntil stop indices mask fuel next.1 next.2

/-- `is_unusable_slot` (:1832-1840), the GIL build: a slot with an entry. -/
def isUnusableSlot (ix : Int) : Bool := decide (ix ≥ 0)

/-- `find_empty_slot` (:1845-1859): the first slot that holds no entry, reusing a
`DKIX_DUMMY`. -/
def findEmptySlot {W : Type} (k : Keys K W) (hash : Int) : Py Nat :=
  let u := toU64 hash
  probeUntil (fun ix => !isUnusableSlot ix) k.indices k.mask (probeFuel k.log2Size)
    (u &&& k.mask) u

/-- `build_indices_generic` / `build_indices_unicode` (:2100-2129): the two differ only
in where the hash is read from. -/
def buildIndices (mask fuel : Nat) : List Int → Nat → List Int → Py (List Int)
  | indices, _, [] => .ok indices
  | indices, ix, h :: hs =>
    let u := toU64 h
    match probeUntil (fun v => v == DKIX_EMPTY) indices mask fuel (u &&& mask) u with
    | .ok i => buildIndices mask fuel (indices.set i ix) (ix + 1) hs
    | .error e => .error e

/-- The entries a split table holds for this dict, in insertion order
(:2203-2210, :2216-2222). -/
def splitLive (k : Keys K Unit) (v : Values V) (numentries : Nat) : List (Ent K V) :=
  (v.order.take numentries).filterMap fun index =>
    match k.entry index, v.get index with
    | some e, some x => some ⟨e.key, e.hash, x⟩
    | _, _ => none

/-- The live entries of a combined table: the `while (ep->me_value == NULL) ep++`
loops of `dictresize` (:2248-2253, :2265-2270, :2276-2284); when nothing was deleted
this is the `memcpy` branch. -/
def liveEntries (k : Keys K V) : List (Ent K V) := k.entries.filterMap id

/-- `dictresize` (:2155-2305). -/
def dictResize (log2New : Nat) (unicode : Bool) : DM K V Unit := fun mp =>
  if log2New ≥ 64 then (.error memoryError, mp) else
  let unicode := if mp.body.isUnicode then unicode else false
  let newkeys : Keys K V := newKeysObject mp.nextId log2New unicode
  let numentries := mp.used
  let live : List (Ent K V) :=
    match mp.body with
    | .split k v => splitLive k v numentries
    | .combined k => (liveEntries k).take numentries
  match buildIndices newkeys.mask (probeFuel log2New) newkeys.indices 0 (live.map (·.hash)) with
  | .error e => (.error e, mp)
  | .ok idx =>
    (.ok (), { mp with
      nextId := mp.nextId + 1
      body := .combined { newkeys with
        indices := idx
        entries := live.map some
        usable := newkeys.usable - numentries } })

/-- `insertion_resize` (:1861-1865). -/
def insertionResize (unicode : Bool) : DM K V Unit := fun mp =>
  dictResize (calculateLog2Keysize (growthRate mp.used)) unicode mp

/-- The body of `insert_combined_dict` after any resize (@3.14.7:1806-1826). -/
def appendEntry (k : Keys K V) (key : K) (hash : Int) (value : V) : Py (Keys K V) :=
  match findEmptySlot k hash with
  | .ok hashpos =>
    .ok { (k.setIndex hashpos k.nentries) with
      entries := k.entries ++ [some ⟨key, hash, value⟩]
      usable := k.usable - 1
      version := 0 }
  | .error e => .error e

/-- `insert_combined_dict` (:1867-1909). -/
def insertCombinedDict (KO : KeyOps K) (hash : Int) (key : K) (value : V) : DM K V Unit := fun mp0 =>
  -- gh-140551: the dict may have been cleared during the lookup.
  match (if mp0.body.isUnicode && !KO.isStr key then insertionResize false mp0
         else (.ok (), mp0)) with
  | (.error e, s) => (.error e, s)
  | (.ok _, mp1) =>
    match (if mp1.body.usable ≤ 0 then insertionResize true mp1 else (.ok (), mp1)) with
    | (.error e, s) => (.error e, s)
    | (.ok _, mp2) =>
      match mp2.body with
      | .combined k =>
        match appendEntry k key hash value with
        | .ok k' => (.ok (), { mp2 with body := .combined k' })
        | .error e => (.error e, mp2)
      | .split _ _ => (.error .modelFuel, mp2)

section Split
variable [DecidableEq K] (P : Proto K (PyDict K V))

/-- `insert_split_key` (:1911-1940): `(ix, shared keys after)`. -/
def insertSplitKey (keys : Keys K Unit) (key : K) (hash : Int) : Py (Int × Keys K Unit) :=
  match unicodekeysLookupUnicode P keys key hash with
  | .error e => .error e
  | .ok ix =>
    if ix == DKIX_EMPTY && decide (keys.usable > 0) then
      match appendEntry keys key hash () with
      | .ok keys' => .ok (keys.nentries, keys')
      | .error e => .error e
    else .ok (ix, keys)

/-- `_PyDict_InsertSplitValue` (:1942-1963). `replace_value` (:1966-1992) is `storeValue`. -/
def insertSplitValue (value : V) (ix : Nat) : DM K V Unit := do
  let mp ← M.get
  match mp.body with
  | .split k v =>
    match v.get ix with
    | none =>
      M.put { mp with
        used := mp.used + 1
        body := .split k ((v.set ix (some value)).addToOrder ix) }
    | some _ =>
      M.put { mp with body := .split k (v.set ix (some value)) }
  | .combined _ => M.unreachable

/-- Overwrite the value at `ix` (@3.14.7:1931-1947). -/
def storeValue (value : V) (ix : Nat) : DM K V Unit := fun mp =>
  match mp.body with
  | .split k v => (.ok (), { mp with body := .split k (v.set ix (some value)) })
  | .combined k =>
    match k.entries[ix]? with
    | some (some e) =>
      (.ok (), { mp with
        body := .combined { k with entries := k.entries.set ix (some { e with value := value }) } })
    | _ => (.error .modelFuel, mp)

/-- The tail of `insertdict` (:2025-2043), after the lookup. -/
def insertAfterLookup (key : K) (hash : Int) (value : V) (ix : Int) (old : Option V) :
    DM K V Unit := fun mp =>
  match old with
  | none =>
    match insertCombinedDict P.toKeyOps hash key value mp with
    | (.ok _, s) => (.ok (), { s with used := s.used + 1 })
    | (.error e, s) => (.error e, s)
  | some _ => storeValue value ix.toNat mp

/-- `insertdict` (:2000-2049). -/
def insertDict (key : K) (hash : Int) (value : V) : DM K V Unit := fun mp =>
  let viaLookup : Py Unit × PyDict K V :=
    match dictLookup P key hash mp with
    | (.ok (ix, old), mp') => insertAfterLookup P key hash value ix old mp'
    | (.error e, mp') => (.error e, mp')
  match mp.body with
  | .split keys vals =>
    if P.isStr key then
      match insertSplitKey P keys key hash with
      | .error e => (.error e, mp)
      | .ok (ix, keys') =>
        let mp' := { mp with body := .split keys' vals }
        if ix != DKIX_EMPTY then insertSplitValue value ix.toNat mp'
        -- No space in shared keys.
        else insertAfterLookup P key hash value ix none mp'
    else viaLookup
  | .combined _ => viaLookup

/-- `insert_to_emptydict` (:2051-2095). -/
def insertToEmptyDict (key : K) (hash : Int) (value : V) : DM K V Unit := fun mp =>
  let unicode := P.isStr key
  let newkeys : Keys K V := newKeysObject mp.nextId PyDict_LOG_MINSIZE unicode
  let hashpos := toU64 hash &&& (PyDict_MINSIZE - 1)
  (.ok (), { mp with
    used := mp.used + 1
    nextId := mp.nextId + 1
    body := .combined { (newkeys.setIndex hashpos 0) with
      entries := [some ⟨key, hash, value⟩]
      usable := newkeys.usable - 1 } })

/-- `dict_unhashable_type` (:2441-2460): only an exact `TypeError` is rewritten. -/
def dictUnhashableType (frozen : Bool) (key : K) (e : PyExc) : PyExc :=
  match e with
  | .typeError m =>
    let what := if frozen then "frozendict" else "dict"
    .typeError s!"cannot use '{P.typeName key}' as a {what} key ({m})"
  | e => e

/-- `_PyObject_HashFast(key)` followed by `dict_unhashable_type` on failure, the
opening of most entry points. -/
def hashKey (key : K) : DM K V Int := fun mp =>
  match P.hash key with
  | .ok h => (.ok h, mp)
  | .error e => (.error (dictUnhashableType P mp.frozen key e), mp)

/-- `setitem_take2_lock_held` (:2732-2760), with `PyDict_SetItem`, `setitem_lock_held`
and `_PyDict_SetItem_Take2`, which differ only in reference counting. -/
def dictSetItem (key : K) (value : V) : DM K V Unit := fun mp =>
  match P.hash key with
  | .error e => (.error (dictUnhashableType P mp.frozen key e), mp)
  | .ok hash =>
    if mp.body.isEmptyKeys then insertToEmptyDict P key hash value mp
    else insertDict P key hash value mp

/-- `_PyDict_SetItem_KnownHash_LockHeld` (:2828-2837). -/
def dictSetItemKnownHash (key : K) (value : V) (hash : Int) : DM K V Unit := do
  let mp ← M.get
  if mp.body.isEmptyKeys then
    insertToEmptyDict P key hash value
  else
    insertDict P key hash value

/-- `delitem_common` (:2882-2923). -/
def delitemCommon (hash : Int) (ix : Nat) : DM K V Unit := fun mp =>
  match mp.body with
  | .split k v =>
    match lookdictIndex k hash ix with
    | .error e => (.error e, mp)
    | .ok hashpos =>
      if hashpos < 0 then (.error .modelFuel, mp)
      else (.ok (), { mp with
        used := mp.used - 1
        body := .split k ((v.set ix none).deleteIndex ix) })
  | .combined k =>
    match lookdictIndex k hash ix with
    | .error e => (.error e, mp)
    | .ok hashpos =>
      if hashpos < 0 then (.error .modelFuel, mp)
      else (.ok (), { mp with
        used := mp.used - 1
        body := .combined { (k.setIndex hashpos.toNat DKIX_DUMMY) with
          entries := k.entries.set ix none
          version := 0 } })

/-- `_PyDict_DelItem_KnownHash_LockHeld` (:2938-2969), and `_PyDict_DelItem_KnownHash`. -/
def dictDelItemKnownHash (key : K) (hash : Int) : DM K V Unit := fun mp =>
  match dictLookup P key hash mp with
  | (.error e, s) => (.error e, s)
  | (.ok (ix, old), s) =>
    match old with
    | some _ =>
      if ix == DKIX_EMPTY then (.error (keyErr P key), s)
      else delitemCommon hash ix.toNat s
    | none => (.error (keyErr P key), s)

/-- `_PyDict_DelItem_KnownHash_LockHeld` with its `PyDict_Check` (:2941-2949). -/
def dictDelItemKnownHashChecked (isAny : Bool) (key : K) (hash : Int) : DM K V Unit := fun mp =>
  if !isAny then (.error badInternalCallT, mp)
  else if mp.frozen then (.error (frozendictNoSupport "deletion"), mp)
  else dictDelItemKnownHash P key hash mp

/-- `PyDict_DelItem` (:2925-2936). -/
def dictDelItem (key : K) : DM K V Unit := fun mp =>
  match P.hash key with
  | .error e => (.error (dictUnhashableType P mp.frozen key e), mp)
  | .ok hash => dictDelItemKnownHash P key hash mp

/-- `PyDict_DelItem` (:2926-2936) on any object: the key is hashed before the check in the callee. -/
def dictDelItemChecked (isAny : Bool) (key : K) : DM K V Unit := fun mp =>
  match P.hash key with
  | .error e => (.error (dictUnhashableType P mp.frozen key e), mp)
  | .ok hash => dictDelItemKnownHashChecked P isAny key hash mp

/-- `PyDict_SetItem` (:2789-2806). -/
def dictSetItemChecked (isAny : Bool) (key : K) (value : V) : DM K V Unit := fun mp =>
  if !isAny then (.error badInternalCallT, mp)
  else if mp.frozen then (.error (frozendictNoSupport "assignment"), mp)
  else dictSetItem P key value mp

end Split

/-- The scan of `_PyDict_Next` (:3174-3177): first non-NULL slot at or after `i`. -/
def scanFrom : List (Option (Ent K V)) → Nat → Option (Nat × Ent K V)
  | [], _ => none
  | none :: t, i => scanFrom t (i + 1)
  | some e :: _, i => some (i, e)

/-- `_PyDict_Next` (:3144-3205): `(new pos, key, value, hash)`. -/
def dictNext (mp : PyDict K V) (pos : Int) : Option (Int × K × V × Int) :=
  let i := pos
  match mp.body with
  | .split k v =>
    if i < 0 ∨ i ≥ mp.used then none
    else
      let index := v.indexFromOrder i.toNat
      match v.get index, k.entry index with
      | some value, some e => some (i + 1, e.key, value, e.hash)
      | _, _ => none
  | .combined k =>
    if i < 0 ∨ i ≥ k.nentries then none
    else
      match scanFrom (k.entries.drop i.toNat) i.toNat with
      | some (j, e) => some ((j : Int) + 1, e.key, e.value, e.hash)
      | none => none

/-- The `while (_PyDict_Next(...))` loop of `keys_lock_held`, `values_lock_held`,
`items_lock_held` and of every other full iteration in the file. -/
def dictNextAll (mp : PyDict K V) : Nat → Int → List (K × V × Int)
  | 0, _ => []
  | fuel + 1, pos =>
    match dictNext mp pos with
    | some (pos', k, v, h) => (k, v, h) :: dictNextAll mp fuel pos'
    | none => []

/-- All `(key, value, hash)` triples in iteration order. -/
def dictItems (mp : PyDict K V) : List (K × V × Int) :=
  dictNextAll mp (mp.body.nentries + mp.used + 1) 0

/-- `_PyDict_SizeOf_LockHeld` (:5088-5104). `sizeof(PyDictObject)` is 48. A split dict's
keys are shared (with the type at least), so `dk_refcnt != 1`. -/
def dictSizeOf (mp : PyDict K V) : Nat :=
  let base := if mp.frozen then 56 else 48
  match mp.body with
  | .split k _ => base + sharedKeysUsableSize k * 8
  | .combined k => if k.isEmpty then base else base + k.bytes

end PyLean.DictSet
