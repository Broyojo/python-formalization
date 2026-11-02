import PyLean.CoreLibs.Functools.Lru

/-!
The bounded wrapper of `lru_cache` with its links as a real heap, Lib/functools.py:650-716 and
Modules/_functoolsmodule.c:1348-1374 and :1408-1617.

`Lru.lean` keeps the queue as a list, which is enough while the dict and the queue agree. They stop agreeing when a
dict operation runs a key's `__eq__` and that `__eq__` calls the cached function again, which is what the comments at
Lib/functools.py:701-703 and Modules/_functoolsmodule.c:1494-1498 are about, and after a failed `del` at
Lib/functools.py:699. A list cannot hold a dict entry that points at a link outside the ring, or the root in the dict.
So here a link is a cell with `prev` and `next`, as in the source, and each statement of the source is one heap write.
Nothing stops at a state the source can reach.

Comparisons: `__eq__` runs when a lookup meets an entry of the same hash that is another key. Which entries it meets
depends on the table: a freed slot is taken again by the next insertion on that chain, and a resize lays the chain out
again in entry order. So `DT` mirrors the table of Objects/dictobject.c for a combined dict: the probe sequence of
`do_lookup`, `find_empty_slot`, `dk_usable`, and `dictresize` with `GROWTH_RATE`. The lookup itself runs here as
`compare_generic` does: after the comparison it goes on down the chain, and restarts only if the keys object changed or
that entry no longer holds that key. So a lookup can miss a key stored behind it by the `__eq__`, which is then stored
a second time. `trig` is a one-shot countdown over the comparisons, and when it reaches one the `hook` program runs
inside the `__eq__`: it can call the wrapper, clear it, or raise, which is then the outcome of the dict operation.
-/

namespace PyLean.CoreLibs.Functools

open PyLean

/-- `[PREV, NEXT, KEY, RESULT]`, or `lru_list_elem`. The root's key and result are `None`. -/
structure Link (K V : Type) where
  prev : Nat
  next : Nat
  key : Option K
  result : Option V
  deriving Repr, DecidableEq, Inhabited

/-- A combined dict from keys to link numbers, Objects/dictobject.c: `dk_indices` with `-1` for empty and `-2` for a
dummy, `dk_entries` with a freed entry as `none`, `dk_usable` and `ma_used`. `gen` says which keys object this is. -/
structure DT (K : Type) where
  log2 : Nat
  table : List Int
  ents : List (Option (K × Nat × Nat))
  usable : Nat
  used : Nat
  gen : Nat
  deriving Repr, DecidableEq

/-- `Py_EMPTY_KEYS`: one empty slot and nothing usable, so that the first insertion resizes. -/
def DT.empty {K : Type} (gen : Nat := 0) : DT K := ⟨0, [-1], [], 0, 0, gen⟩

/-- The state of one wrapper. C's root is cell `0` for ever; Python's `root` variable moves. `full` is Python's flag. -/
structure LS (K V : Type) where
  links : List (Link K V)
  root : Nat
  cache : DT K
  hits : Nat
  misses : Nat
  full : Bool
  trig : Option Nat
  deriving Repr, DecidableEq

def LS.empty {K V : Type} (trig : Option Nat := none) : LS K V :=
  ⟨[⟨0, 0, none, none⟩], 0, DT.empty, 0, 0, false, trig⟩

/-- The configuration: `f` takes the key and the miss count, as in `Cfg`. `hash` is the key's hash as a `size_t`, and
`none` is the value `None`. -/
structure PCfg (K V : Type) where
  maxsize : Nat
  f : K → Nat → Prog K V
  hash : K → Nat
  hook : Prog K V
  none : V

/-- Where a walk down the chain stopped. -/
inductive Scan where
  | found (slot : Nat)
  | absent
  /-- At a slot whose entry has the same hash and is another key, with the `perturb` of that slot. -/
  | cmp (slot perturb : Nat)
  deriving Repr, DecidableEq

section
variable {K V : Type} [DecidableEq K]

def LS.link [Inhabited V] (s : LS K V) (i : Nat) : Link K V := s.links.getD i ⟨0, 0, none, none⟩

def LS.setNext [Inhabited V] (s : LS K V) (i n : Nat) : LS K V :=
  { s with links := s.links.set i { s.link i with next := n } }

def LS.setPrev [Inhabited V] (s : LS K V) (i p : Nat) : LS K V :=
  { s with links := s.links.set i { s.link i with prev := p } }

def LS.setKV [Inhabited V] (s : LS K V) (i : Nat) (k : Option K) (v : Option V) : LS K V :=
  { s with links := s.links.set i { s.link i with key := k, result := v } }

def DT.mask (t : DT K) : Nat := 2 ^ t.log2 - 1

/-- Probes of one walk, far more than a small table needs. -/
def probeFuel : Nat := 300

/-- The next slot of a chain, `perturb >>= 5; i = mask & (i*5 + perturb + 1)`, with the new `perturb`. -/
def nextProbe (mask i perturb : Nat) : Nat × Nat :=
  let p := perturb >>> 5
  ((i * 5 + p + 1) &&& mask, p)

/-- `do_lookup`, Objects/dictobject.c:1082-1124, up to the next comparison that can run code. A dummy or a freed entry
is passed, and so is an entry of another hash. -/
def DT.scan (t : DT K) (key : K) (h : Nat) : Nat → Nat → Nat → Scan
  | 0, _, _ => .absent
  | fuel + 1, i, perturb =>
    let n := nextProbe t.mask i perturb
    let ix := t.table.getD i (-1)
    if ix = -1 then .absent
    else if ix < 0 then t.scan key h fuel n.1 n.2
    else
      match t.ents.getD ix.toNat none with
      | some (k, eh, _) =>
        if k = key then .found i
        else if eh = h then .cmp i perturb
        else t.scan key h fuel n.1 n.2
      | none => t.scan key h fuel n.1 n.2

/-- The entry number in a slot. -/
def DT.ixAt (t : DT K) (i : Nat) : Nat := (t.table.getD i (-1)).toNat

/-- The key of an entry. -/
def DT.keyAt (t : DT K) (ix : Nat) : Option K :=
  match t.ents.getD ix none with
  | some (k, _, _) => some k
  | none => none

/-- The link an entry refers to. -/
def DT.linkAt (t : DT K) (slot : Nat) : Option Nat :=
  match t.ents.getD (t.ixAt slot) none with
  | some (_, _, l) => some l
  | none => none

/-- The walk from the head of the chain. -/
def DT.scan0 (t : DT K) (key : K) (h : Nat) : Scan := t.scan key h probeFuel (h &&& t.mask) h

/-- `find_empty_slot`, :1846-1859, and with `-1` only, `build_indices`: the first free slot on the chain. -/
def slotFree (table : List Int) (mask : Nat) : Nat → Nat → Nat → Nat
  | 0, i, _ => i
  | fuel + 1, i, perturb =>
    if table.getD i (-1) < 0 then i
    else
      let n := nextProbe mask i perturb
      slotFree table mask fuel n.1 n.2

/-- `dictresize` with `GROWTH_RATE`, :628 and :585-598: the live entries in order, in a fresh table. -/
def DT.resize (t : DT K) : DT K :=
  let log2 := bitLength (max (t.used * 3) 8 - 1)
  let live := t.ents.filterMap id
  let size := 2 ^ log2
  let table := live.zipIdx.foldl (fun (tb : List Int) p =>
    tb.set (slotFree tb (size - 1) probeFuel (p.1.2.1 &&& (size - 1)) p.1.2.1) (p.2 : Int)) (List.replicate size (-1))
  ⟨log2, table, live.map some, (size * 2) / 3 - t.used, t.used, t.gen + 1⟩

/-- `insertdict` after its lookup, which gave `slot`: an existing key keeps its entry; otherwise
`insert_combined_dict`, Objects/dictobject.c:1868-1909. -/
def DT.storeAt (t : DT K) (slot : Option Nat) (key : K) (h l : Nat) : DT K :=
  match slot with
  | some i => { t with ents := t.ents.set (t.ixAt i) (some (key, h, l)) }
  | none =>
    let t := if t.usable = 0 then t.resize else t
    let free := slotFree t.table t.mask probeFuel (h &&& t.mask) h
    { t with table := t.table.set free (t.ents.length : Int), ents := t.ents ++ [some (key, h, l)],
             usable := t.usable - 1, used := t.used + 1 }

/-- `delitem_common`: the slot becomes a dummy, and the entry is freed. Nothing is given back to `dk_usable`. -/
def DT.deleteAt (t : DT K) (slot : Nat) : DT K :=
  { t with table := t.table.set slot (-2), ents := t.ents.set (t.ixAt slot) none, used := t.used - 1 }

/-- Whether a dict operation on `key` starts with a comparison that can run an `__eq__`. -/
def needEq (cfg : PCfg K V) (key : K) (s : LS K V) : Bool :=
  match s.cache.scan0 key (cfg.hash key) with
  | .cmp _ _ => true
  | _ => false

/-- The slot of `key`, for a key whose walk meets no comparison. -/
def LS.slot (s : LS K V) (h : K → Nat) (key : K) : Option Nat :=
  match s.cache.scan0 key (h key) with
  | .found i => some i
  | _ => none

variable [Inhabited V]

/-- `lru_cache_extract_link`, Modules/_functoolsmodule.c:1348-1352. -/
def LS.extract (s : LS K V) (l : Nat) : LS K V :=
  let k := s.link l
  let s := s.setNext k.prev k.next
  s.setPrev k.next k.prev

/-- `lru_cache_append_link`, :1354-1363: before the root, as the newest. -/
def LS.append (s : LS K V) (l : Nat) : LS K V :=
  let last := (s.link s.root).prev
  let s := s.setNext last l
  let s := s.setPrev s.root l
  let s := s.setPrev l last
  s.setNext l s.root

/-- `lru_cache_prepend_link`, :1365-1374: after the root, as the oldest. -/
def LS.prepend (s : LS K V) (l : Nat) : LS K V :=
  let first := (s.link s.root).next
  let s := s.setPrev first l
  let s := s.setNext s.root l
  let s := s.setPrev l s.root
  s.setNext l first

/-- `cache_clear`, Lib/functools.py:723-730, and `lru_cache_cache_clear`, Modules/_functoolsmodule.c:1796-1807. The
`root` stays where it is, which is not cell `0` after an eviction in Python. `PyDict_Clear` installs new keys. -/
def LS.clear (s : LS K V) : LS K V :=
  let r := s.root
  let links := s.links.set r ⟨r, r, none, none⟩
  { s with links, cache := DT.empty (s.cache.gen + 1), hits := 0, misses := 0, full := false }

/-- `ma_used`. -/
def LS.size (s : LS K V) : Nat := s.cache.used

mutual
  /-- A lookup from slot `i`, as `do_lookup` with `compare_generic` runs it. After the comparison the walk goes on from
  that slot, unless the keys object changed or the entry no longer holds that key, and then it starts again. -/
  def findP (cfg : PCfg K V) : Nat → K → Nat → Nat → LS K V → Py (Option Nat) × LS K V
    | 0, _, _, _, s => (.error .modelFuel, s)
    | fuel + 1, key, i, p, s =>
      let h := cfg.hash key
      match s.cache.scan key h probeFuel i p with
      | .found slot => (.ok (some slot), s)
      | .absent => (.ok none, s)
      | .cmp j q =>
        let ix := s.cache.ixAt j
        let startkey := s.cache.keyAt ix
        let gen := s.cache.gen
        let n := nextProbe s.cache.mask j q
        match s.trig with
        | some 1 =>
          match runPtrP cfg fuel cfg.hook { s with trig := none } with
          | (.error e, s) => (.error e, s)
          | (.ok _, s) =>
            if s.cache.gen = gen ∧ s.cache.keyAt ix = startkey then findP cfg fuel key n.1 n.2 s
            else findP cfg fuel key (h &&& s.cache.mask) h s
        | some (m + 2) => findP cfg fuel key n.1 n.2 { s with trig := some (m + 1) }
        | _ => findP cfg fuel key n.1 n.2 s

  /-- `wrapper`, Lib/functools.py:650-716, as far as the user function. -/
  def callPtrP (cfg : PCfg K V) : Nat → K → LS K V → Py V × LS K V
    | 0, _, s => (.error .modelFuel, s)
    | fuel + 1, key, s =>
      match findP cfg fuel key (cfg.hash key &&& s.cache.mask) (cfg.hash key) s with
      | (.error e, s) => (.error e, s)
      | (.ok slot, s) =>
        match slot.bind s.cache.linkAt with
        | some l =>
          -- :659-668
          let L := s.link l
          let s := s.setNext L.prev L.next
          let s := s.setPrev L.next L.prev
          let last := (s.link s.root).prev
          let s := s.setNext last l
          let s := s.setPrev s.root l
          let s := s.setPrev l last
          let s := s.setNext l s.root
          (.ok (L.result.getD cfg.none), { s with hits := s.hits + 1 })
        | none =>
          let s := { s with misses := s.misses + 1 }
          match runPtrP cfg fuel (cfg.f key s.misses) s with
          | (.error e, s) => (.error e, s)
          | (.ok result, s) => updatePtrP cfg fuel key result s

  /-- Lib/functools.py:674-714: the second `with lock`. -/
  def updatePtrP (cfg : PCfg K V) : Nat → K → V → LS K V → Py V × LS K V
    | 0, _, _, s => (.error .modelFuel, s)
    | fuel + 1, key, result, s =>
      let h := cfg.hash key
      match findP cfg fuel key (h &&& s.cache.mask) h s with
      | (.error e, s) => (.error e, s)
      | (.ok (some _), s) => (.ok result, s)
      | (.ok none, s) =>
        if s.full then
          -- :683-704
          let oldroot := s.root
          let s := s.setKV oldroot (some key) (some result)
          let s := { s with root := (s.link oldroot).next }
          let oldkey := (s.link s.root).key
          let s := s.setKV s.root none none
          match oldkey with
          | none => (.error (.keyError "None"), s)     -- `del cache[None]`
          | some ok =>
            match findP cfg fuel ok (cfg.hash ok &&& s.cache.mask) (cfg.hash ok) s with
            | (.error e, s) => (.error e, s)
            | (.ok none, s) => (.error (.keyError "~key"), s)
            | (.ok (some slot), s) =>
              let s := { s with cache := s.cache.deleteAt slot }
              match findP cfg fuel key (h &&& s.cache.mask) h s with
              | (.error e, s) => (.error e, s)
              | (.ok slot, s) => (.ok result, { s with cache := s.cache.storeAt slot key h oldroot })
        else
          -- :708-714: `last[NEXT] = root[PREV] = cache[key] = link` assigns left to right
          let last := (s.link s.root).prev
          let l := s.links.length
          let s := { s with links := s.links ++ [(⟨last, s.root, some key, some result⟩ : Link K V)] }
          let s := s.setNext last l
          let s := s.setPrev s.root l
          match findP cfg fuel key (h &&& s.cache.mask) h s with
          | (.error e, s) => (.error e, s)
          | (.ok slot, s) =>
            let s := { s with cache := s.cache.storeAt slot key h l }
            (.ok result, { s with full := decide (s.size ≥ cfg.maxsize) })

  def runPtrP (cfg : PCfg K V) : Nat → Prog K V → LS K V → Py V × LS K V
    | 0, _, s => (.error .modelFuel, s)
    | _ + 1, .ret v, s => (.ok v, s)
    | _ + 1, .raise e, s => (.error e, s)
    | fuel + 1, .call k c, s =>
      match callPtrP cfg fuel k s with
      | (r, s') => runPtrP cfg fuel (c r) s'
    | fuel + 1, .clear c, s => runPtrP cfg fuel c s.clear
end

mutual
  /-- The lookup, as in `findP`. -/
  def findC (cfg : PCfg K V) : Nat → K → Nat → Nat → LS K V → Py (Option Nat) × LS K V
    | 0, _, _, _, s => (.error .modelFuel, s)
    | fuel + 1, key, i, p, s =>
      let h := cfg.hash key
      match s.cache.scan key h probeFuel i p with
      | .found slot => (.ok (some slot), s)
      | .absent => (.ok none, s)
      | .cmp j q =>
        let ix := s.cache.ixAt j
        let startkey := s.cache.keyAt ix
        let gen := s.cache.gen
        let n := nextProbe s.cache.mask j q
        match s.trig with
        | some 1 =>
          match runPtrC cfg fuel cfg.hook { s with trig := none } with
          | (.error e, s) => (.error e, s)
          | (.ok _, s) =>
            if s.cache.gen = gen ∧ s.cache.keyAt ix = startkey then findC cfg fuel key n.1 n.2 s
            else findC cfg fuel key (h &&& s.cache.mask) h s
        | some (m + 2) => findC cfg fuel key n.1 n.2 { s with trig := some (m + 1) }
        | _ => findC cfg fuel key n.1 n.2 s

  /-- `bounded_lru_cache_wrapper`, Modules/_functoolsmodule.c:1589-1617, with `bounded_lru_cache_get_lock_held`,
  :1408-1440. -/
  def callPtrC (cfg : PCfg K V) : Nat → K → LS K V → Py V × LS K V
    | 0, _, s => (.error .modelFuel, s)
    | fuel + 1, key, s =>
      match findC cfg fuel key (cfg.hash key &&& s.cache.mask) (cfg.hash key) s with
      | (.error e, s) => (.error e, s)
      | (.ok slot, s) =>
        match slot.bind s.cache.linkAt with
        | some l =>
          let L := s.link l
          let s := (s.extract l).append l
          (.ok (L.result.getD cfg.none), { s with hits := s.hits + 1 })
        | none =>
          let s := { s with misses := s.misses + 1 }
          match runPtrC cfg fuel (cfg.f key s.misses) s with
          | (.error e, s) => (.error e, s)
          | (.ok result, s) => updatePtrC cfg fuel key result s

  /-- `bounded_lru_cache_update_lock_held`, :1443-1586. -/
  def updatePtrC (cfg : PCfg K V) : Nat → K → V → LS K V → Py V × LS K V
    | 0, _, _, s => (.error .modelFuel, s)
    | fuel + 1, key, result, s =>
      let h := cfg.hash key
      match findC cfg fuel key (h &&& s.cache.mask) h s with
      | (.error e, s) => (.error e, s)
      | (.ok (some _), s) => (.ok result, s)
      | (.ok none, s) =>
        if s.size < cfg.maxsize ∨ (s.link s.root).next = s.root then
          -- :1479-1505: the dict first, then the link
          let l := s.links.length
          let s := { s with links := s.links ++ [(⟨0, 0, some key, some result⟩ : Link K V)] }
          match findC cfg fuel key (h &&& s.cache.mask) h s with
          | (.error e, s) => (.error e, s)
          | (.ok slot, s) => (.ok result, LS.append { s with cache := s.cache.storeAt slot key h l } l)
        else
          let l := (s.link s.root).next
          let s := s.extract l
          match (s.link l).key with
          | none => (.error .modelFuel, s)
          | some ok =>
            match findC cfg fuel ok (cfg.hash ok &&& s.cache.mask) (cfg.hash ok) s with
            -- :1531-1541: back to the oldest position
            | (.error e, s) => (.error e, s.prepend l)
            -- :1542-1550: an orphan: the result is returned, and neither link nor key is kept
            | (.ok none, s) => (.ok result, s)
            | (.ok (some slot), s) =>
              let s := { s with cache := s.cache.deleteAt slot }
              let s := s.setKV l (some key) (some result)
              match findC cfg fuel key (h &&& s.cache.mask) h s with
              -- :1569-1578: short one link
              | (.error e, s) => (.error e, s)
              | (.ok slot, s) => (.ok result, LS.append { s with cache := s.cache.storeAt slot key h l } l)

  def runPtrC (cfg : PCfg K V) : Nat → Prog K V → LS K V → Py V × LS K V
    | 0, _, s => (.error .modelFuel, s)
    | _ + 1, .ret v, s => (.ok v, s)
    | _ + 1, .raise e, s => (.error e, s)
    | fuel + 1, .call k c, s =>
      match callPtrC cfg fuel k s with
      | (r, s') => runPtrC cfg fuel (c r) s'
    | fuel + 1, .clear c, s => runPtrC cfg fuel c s.clear
end

end

end PyLean.CoreLibs.Functools
