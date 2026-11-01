import PyLean.CoreLibs.Functools.LruProps
import PyLean.CoreLibs.Functools.LruPtr

/-!
Properties of the heap model of `lru_cache`: the paths that only a re-entrant or raising `__eq__` reaches.
-/

namespace PyLean.CoreLibs.Functools

open PyLean

/-- A run of several calls. -/
def ptrSeq {V : Type} {K : Type} (call : K → LS K V → Py V × LS K V) : List K → LS K V → List (Py V) × LS K V
  | [], s => ([], s)
  | k :: ks, s =>
    let (r, s1) := call k s
    let (rs, s2) := ptrSeq call ks s1
    (r :: rs, s2)

/-- The ring from the oldest link: the links `next` reaches from the root, at most `n` of them. -/
def ringFrom {K V : Type} [Inhabited V] (s : LS K V) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, i => if i = s.root then [] else i :: ringFrom s n (s.link i).next

def ring {K V : Type} [Inhabited V] (s : LS K V) : List Nat := ringFrom s s.links.length (s.link s.root).next

/-- The link of the dict's entry for `key`, read from the entries. -/
def entryLink {K : Type} [DecidableEq K] (t : DT K) (key : K) : Option Nat :=
  t.ents.findSome? (fun e => match e with
    | some (k, _, l) => if k = key then some l else none
    | none => none)

/-- `hash((h,))` as a `size_t` for the keys of the reproducers, where key `k` has hash `1000` if it is `0` or `2`, and
`k` otherwise. A key of `lru_cache` that is not a `str` or an `int` is a one-item tuple, or a `_HashedSeq` with the hash
of that tuple. -/
def reHash (k : Nat) : Nat :=
  [4990548550112884342, 11802529618835948721, 4990548550112884342, 13417096345965250780, 8524022316992554414,
    10633305690110184711, 17140946446212183136].getD k 0

/-- The configuration of the reproducer: size 3, keys `0` and `2` collide, and the third comparison, which is the
store of key `0`, calls the wrapper with key `0` again. -/
def reCfg : PCfg Nat Int :=
  ⟨3, fun k _ => .ret ((k : Int) * 10), reHash, .call 0 (fun _ => .ret 0), -1⟩

/-- A raising `__eq__`: the size is 2, keys `0` and `2` collide. With `[2, 0, 2, 5]` and a countdown of 4, the `__eq__`
that raises is the one of the eviction of key `0`, whose entry comes after that of key `2`. -/
def raiseCfg : PCfg Nat Int :=
  ⟨2, fun k _ => .ret ((k : Int) * 10), reHash, .raise (.valueError "eq"), -1⟩

/-- The two twins of the bounded wrapper give the same results for any sequence of calls, with any `__eq__`. Refuted:
with a re-entrant `__eq__` in the store, the last call of `[2, 0, 3, 4, 5, 6]` returns `60` in C and raises `KeyError`
in Python, out of `del cache[oldkey]` at Lib/functools.py:699. C has the orphan branch at
Modules/_functoolsmodule.c:1542-1550, and Python has no such branch. -/
def LruTwinsReentrantEq : Prop :=
  ∀ (cfg : PCfg Nat Int) (ks : List Nat) (t : Option Nat), 0 < cfg.maxsize →
    (ptrSeq (callPtrC cfg 40) ks (LS.empty t)).1 = (ptrSeq (callPtrP cfg 40) ks (LS.empty t)).1

theorem lruTwinsReentrantEq_refuted : ¬LruTwinsReentrantEq := by
  intro h
  have := h reCfg [2, 0, 3, 4, 5, 6] (some 3) (by decide)
  have h2 := congrArg (fun l : List (Py Int) => (l.getLast?.map Except.toBool)) this
  revert h2
  decide +kernel

/-- The orphan is real, in both twins. In the run above, after the second call, the dict holds two keys and the ring
holds three links, two of them for key `0`: the comment at Modules/_functoolsmodule.c:1494-1498. C's dict refers to the
newer of the two links and Python's to the older, because Python links first and stores last. -/
def LruOrphanReached : Prop :=
  let c := (ptrSeq (callPtrC reCfg 40) [2, 0] (LS.empty (some 3))).2
  let p := (ptrSeq (callPtrP reCfg 40) [2, 0] (LS.empty (some 3))).2
  c.size = 2 ∧ (ring c).length = 3 ∧ p.size = 2 ∧ (ring p).length = 3 ∧
  entryLink c.cache 0 = (ring c).getLast? ∧ entryLink p.cache 0 = (ring p)[1]?

theorem lruOrphanReached_proven : LruOrphanReached := by
  unfold LruOrphanReached
  decide +kernel

/-- Python's `del` that raises, at the same place as C's `_PyDict_Pop_KnownHash`: the twins keep different states, so
the results differ afterwards. C put the link back, and Python has already moved the root, so that the next call of
key `0` returns `0` in C and `None` in Python. Refuted by the calls `[2, 0, 2, 5, 0]`. -/
def LruTwinsRaisingEq : Prop :=
  ∀ (cfg : PCfg Nat Int) (ks : List Nat) (t : Option Nat) (e : PyExc), cfg.hook = .raise e →
    (ptrSeq (callPtrC cfg 40) ks (LS.empty t)).1 = (ptrSeq (callPtrP cfg 40) ks (LS.empty t)).1

theorem lruTwinsRaisingEq_refuted : ¬LruTwinsRaisingEq := by
  intro h
  have := h raiseCfg [2, 0, 2, 5, 0] (some 4) (.valueError "eq") rfl
  have h2 := congrArg (fun l : List (Py Int) => (l.getLast?.map Except.toOption)) this
  revert h2
  decide +kernel

/-- `next` from the root comes back to the root, in at most `n` steps: what `lru_cache_tp_traverse` needs to end. -/
def closesFrom {K V : Type} [Inhabited V] (s : LS K V) : Nat → Nat → Bool
  | 0, _ => false
  | n + 1, i => if i = s.root then true else closesFrom s n (s.link i).next

def ringCloses {K V : Type} [Inhabited V] (s : LS K V) : Bool :=
  closesFrom s (s.links.length + 1) (s.link s.root).next

/-- The reproducer of `corelibs-lru-evicted-hit-gc-hang`: size 2, keys `1` and `2` have equal hashes, and the fourth
comparison, which is in the pop of key `2`, calls the wrapper with key `2` and raises. -/
def gcCfg : PCfg Nat Int :=
  ⟨2, fun k _ => .ret (k : Int), fun k => if k = 3 then 11802529618835948721 else 9693246245718318424,
    .call 2 (fun _ => .raise (.valueError "eq")), -1⟩

/-- The C wrapper's list stays a ring through the root, for any calls and any `__eq__`. Refuted: `[1, 2, 1, 3]`. In the
fourth call the oldest link is unlinked and its key popped, Modules/_functoolsmodule.c:1523-1530. The pop runs `__eq__`,
which calls the wrapper with that key: a hit, since the dict still has it, so the link is appended. Then `__eq__` raises,
and the error path prepends the same link, :1531-1541. The list has a cycle without the root, and
`lru_cache_tp_traverse` never ends. -/
def LruRingCloses : Prop :=
  ∀ (cfg : PCfg Nat Int) (ks : List Nat) (t : Option Nat),
    ringCloses (ptrSeq (callPtrC cfg 40) ks (LS.empty t)).2 = true

theorem lruRingCloses_refuted : ¬LruRingCloses := by
  intro h
  have := h gcCfg [1, 2, 1, 3] (some 4)
  revert this
  decide +kernel

section General
variable {K V : Type} [DecidableEq K] [Inhabited V]

theorem findC_plain (cfg : PCfg K V) (fuel : Nat) (key : K) (s : LS K V) (h : needEq cfg key s = false) :
    findC cfg (fuel + 1) key (cfg.hash key &&& s.cache.mask) (cfg.hash key) s = (.ok (s.slot cfg.hash key), s) := by
  rw [findC]
  simp only [needEq, DT.scan0, LS.slot] at h ⊢
  split
  · next r => simp only [r]
  · next r => simp only [r]
  · next r => simp only [r] at h; cases h

theorem findP_plain (cfg : PCfg K V) (fuel : Nat) (key : K) (s : LS K V) (h : needEq cfg key s = false) :
    findP cfg (fuel + 1) key (cfg.hash key &&& s.cache.mask) (cfg.hash key) s = (.ok (s.slot cfg.hash key), s) := by
  rw [findP]
  simp only [needEq, DT.scan0, LS.slot] at h ⊢
  split
  · next r => simp only [r]
  · next r => simp only [r]
  · next r => simp only [r] at h; cases h

/-- A first comparison that raises, in a lookup. -/
theorem findC_raises (cfg : PCfg K V) (fuel : Nat) (key : K) (s : LS K V) (e : PyExc) (h : needEq cfg key s = true)
    (ht : s.trig = some 1) (hh : cfg.hook = .raise e) :
    findC cfg (fuel + 2) key (cfg.hash key &&& s.cache.mask) (cfg.hash key) s =
      (.error e, { s with trig := none }) := by
  rw [findC]
  simp only [needEq, DT.scan0] at h ⊢
  split
  · next r => simp only [r] at h; cases h
  · next r => simp only [r] at h; cases h
  · simp [ht, hh, runPtrC]

theorem findP_raises (cfg : PCfg K V) (fuel : Nat) (key : K) (s : LS K V) (e : PyExc) (h : needEq cfg key s = true)
    (ht : s.trig = some 1) (hh : cfg.hook = .raise e) :
    findP cfg (fuel + 2) key (cfg.hash key &&& s.cache.mask) (cfg.hash key) s =
      (.error e, { s with trig := none }) := by
  rw [findP]
  simp only [needEq, DT.scan0] at h ⊢
  split
  · next r => simp only [r] at h; cases h
  · next r => simp only [r] at h; cases h
  · simp [ht, hh, runPtrP]

theorem extract_cache (s : LS K V) (l : Nat) : (s.extract l).cache = s.cache := rfl

end General

/-- C's orphan branch, for any state in which these lookups meet no `__eq__`: with a full cache and an oldest link whose
key is no longer in the dict, the update returns the computed result, the link is gone, and the new key is not stored,
Modules/_functoolsmodule.c:1542-1550. -/
def LruOrphanC : Prop :=
  ∀ (K V : Type) [DecidableEq K] [Inhabited V] (cfg : PCfg K V) (fuel : Nat) (key ok : K) (result : V) (s : LS K V),
    let l := (s.link s.root).next
    needEq cfg key s = false → s.slot cfg.hash key = none → ¬(s.size < cfg.maxsize ∨ l = s.root) →
    ((s.extract l).link l).key = some ok → needEq cfg ok (s.extract l) = false → (s.extract l).slot cfg.hash ok = none →
    updatePtrC cfg (fuel + 2) key result s = (.ok result, s.extract l)

theorem lruOrphanC_proven : LruOrphanC := by
  intro K V _ _ cfg fuel key ok result s l h1 h2 h3 h4 h5 h6
  rw [updatePtrC]
  simp only []
  rw [findC_plain _ _ _ _ h1, h2]
  simp only [l] at h3 h4 h5 h6 ⊢
  simp only [h3, ↓reduceIte, h4]
  have h7 := findC_plain cfg fuel ok _ h5
  rw [h7, h6]

/-- The same state in Python: the root has already moved, and `del cache[oldkey]` raises `KeyError`, Lib/functools.py:699.
There is no branch for it, so the exception reaches the caller of the cached function. -/
def LruOrphanP : Prop :=
  ∀ (K V : Type) [DecidableEq K] [Inhabited V] (cfg : PCfg K V) (fuel : Nat) (key ok : K) (result : V) (s : LS K V),
    let s1 := s.setKV s.root (some key) (some result)
    let s2 : LS K V := { s1 with root := (s1.link s.root).next }
    let s3 := s2.setKV s2.root none none
    needEq cfg key s = false → s.slot cfg.hash key = none → s.full = true → (s2.link s2.root).key = some ok →
    needEq cfg ok s3 = false → s3.slot cfg.hash ok = none →
    updatePtrP cfg (fuel + 2) key result s = (.error (.keyError "~key"), s3)

theorem lruOrphanP_proven : LruOrphanP := by
  intro K V _ _ cfg fuel key ok result s s1 s2 s3 h1 h2 h3 h4 h5 h6
  rw [updatePtrP]
  simp only []
  rw [findP_plain _ _ _ _ h1, h2]
  simp only [h3, ↓reduceIte]
  simp only [s2, s1] at h4
  simp only [h4]
  have h7 := findP_plain cfg fuel ok s3 h5
  simp only [s3, s2, s1] at h7 h6 ⊢
  rw [h7, h6]

/-- A `__eq__` that raises in the eviction, in C: the link goes back to the oldest place, the dict is unchanged, and the
exception propagates, Modules/_functoolsmodule.c:1531-1541. -/
def LruPopRaisesC : Prop :=
  ∀ (K V : Type) [DecidableEq K] [Inhabited V] (cfg : PCfg K V) (fuel : Nat) (key ok : K) (result : V) (s : LS K V)
    (e : PyExc),
    let l := (s.link s.root).next
    cfg.hook = .raise e → s.trig = some 1 → needEq cfg key s = false → s.slot cfg.hash key = none →
    ¬(s.size < cfg.maxsize ∨ l = s.root) → ((s.extract l).link l).key = some ok →
    needEq cfg ok (s.extract l) = true →
    updatePtrC cfg (fuel + 3) key result s = (.error e, LS.prepend { s.extract l with trig := none } l)

theorem lruPopRaisesC_proven : LruPopRaisesC := by
  intro K V _ _ cfg fuel key ok result s e l h1 h2 h3 h4 h5 h6 h7
  rw [updatePtrC]
  simp only []
  rw [findC_plain _ _ _ _ h3, h4]
  simp only [l] at h5 h6 h7 ⊢
  simp only [h5, ↓reduceIte, h6]
  have h8 := findC_raises cfg fuel ok _ e h7 h2 h1
  rw [h8]

/-- A `__eq__` that raises in the `del`, in Python: the dict still has the key, the root has moved and carries no key,
Lib/functools.py:690-699. So the key's dict entry is the root, and the next call with that key is a hit on the root that
returns `None`. -/
def LruDelRaisesP : Prop :=
  ∀ (K V : Type) [DecidableEq K] [Inhabited V] (cfg : PCfg K V) (fuel : Nat) (key ok : K) (result : V) (s : LS K V)
    (e : PyExc),
    let s1 := s.setKV s.root (some key) (some result)
    let s2 : LS K V := { s1 with root := (s1.link s.root).next }
    let s3 := s2.setKV s2.root none none
    cfg.hook = .raise e → s.trig = some 1 → needEq cfg key s = false → s.slot cfg.hash key = none → s.full = true →
    (s2.link s2.root).key = some ok → needEq cfg ok s3 = true →
    updatePtrP cfg (fuel + 3) key result s = (.error e, { s3 with trig := none })

theorem lruDelRaisesP_proven : LruDelRaisesP := by
  intro K V _ _ cfg fuel key ok result s e s1 s2 s3 h1 h2 h3 h4 h5 h6 h7
  rw [updatePtrP]
  simp only []
  rw [findP_plain _ _ _ _ h3, h4]
  simp only [h5, ↓reduceIte]
  simp only [s2, s1] at h6
  simp only [h6]
  have h8 := findP_raises cfg fuel ok s3 e h7 h2 h1
  simp only [s3, s2, s1] at h8 ⊢
  rw [h8]

/-- `cache_clear`: both twins empty the dict, reset the counters and leave the root alone, wherever it is. -/
def LruClearResets : Prop :=
  ∀ (K V : Type) [DecidableEq K] [Inhabited V] (s : LS K V), s.root < s.links.length →
    s.clear.cache = DT.empty (s.cache.gen + 1) ∧ s.clear.size = 0 ∧ s.clear.hits = 0 ∧ s.clear.misses = 0 ∧ s.clear.full = false ∧
    s.clear.root = s.root ∧ s.clear.link s.root = ⟨s.root, s.root, none, none⟩ ∧ s.clear.trig = s.trig

theorem lruClearResets_proven : LruClearResets := by
  intro K V _ _ s h
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
  simp [LS.clear, LS.link, List.getD, h]

/-- The `maxsize == 0` branch, Lib/functools.py:624-630 and Modules/_functoolsmodule.c:1298-1307: every call is a miss
and runs the function, and there is no key, so nothing can be remembered and the function's exception propagates. -/
def LruUncachedRuns : Prop :=
  ∀ (K V : Type) [DecidableEq K] (f : K → Nat → Prog K V) (fuel m : Nat) (key : K) (v : V) (e : PyExc),
    (f key (m + 1) = .ret v → callNone f (fuel + 2) key m = (.ok v, m + 1)) ∧
    (f key (m + 1) = .raise e → callNone f (fuel + 2) key m = (.error e, m + 1))

theorem lruUncachedRuns_proven : LruUncachedRuns := by
  intro K V _ f fuel m key v e
  constructor
  · intro h; simp [callNone, h, runNone]
  · intro h; simp [callNone, h, runNone]

/-- The `maxsize is None` branch, Lib/functools.py:634-646 and Modules/_functoolsmodule.c:1310-1345, which is `cache`: a
miss stores the result, and the next call is a hit that does not run the function. -/
def LruInfiniteMemo : Prop :=
  ∀ (K V : Type) [DecidableEq K] (f : K → Nat → Prog K V) (F : Faults K) (fuel : Nat) (key : K) (v : V)
    (s : CLru K V), F.get key s.cache = none → F.insert key s.cache = none → s.links.lookup key = none →
    f key (s.misses + 1) = .ret v →
    ∃ s', callInf f F (fuel + 2) key s = (.ok v, s') ∧ s'.misses = s.misses + 1 ∧ s'.links.lookup key = some v ∧
      (F.get key s'.cache = none → callInf f F (fuel + 1) key s' = (.ok v, { s' with hits := s'.hits + 1 }))

theorem lruInfiniteMemo_proven : LruInfiniteMemo := by
  intro K V _ f F fuel key v s h1 h2 h3 h4
  let c := if key ∈ s.cache then s.cache else s.cache ++ [key]
  refine ⟨{ s with misses := s.misses + 1, links := setKey s.links key v, cache := c }, ?_, rfl,
    setKey_lookup _ _ _, ?_⟩
  · simp [callInf, h1, h2, h3, h4, runInf, c]
  · intro h5
    rw [callInf]
    simp [h5, setKey_lookup]

end PyLean.CoreLibs.Functools
