import PyLean.TextLibs.StructPrep

/-!
The module-level `Struct` cache, `cache_struct_converter` and `_clearcache_impl`
(`Modules/_struct.c:2614-2680`), as a dictionary keyed by the format objects themselves.

A key is an exact `str`, or a `str` subclass by what its `__eq__` says about another string. Its
`__hash__` is assumed to agree with its `__eq__` (a stated scope limit: a dictionary never compares
keys whose hashes differ). When a plain `str` meets a subclass key, Python asks the subclass's
`__eq__`, which is what `keyMatch` does. A `__hash__` or `__eq__` that raises is out of scope here; the
unhashable refusal is `cacheStruct`'s.
-/

namespace PyLean.TextLibs.Struct

open PyLean PyLean.TextLibs

/-- A cache key: `bytes` formats are decoded to an exact `str` first (2631-2636). -/
inductive CKey where
  | str (cps : List Nat)
  /-- A `str` subclass instance with value `cps`, whose `__eq__` accepts the strings `eqv` accepts. -/
  | sub (cps : List Nat) (eqv : List Nat → Bool)

def CKey.value : CKey → List Nat
  | .str c | .sub c _ => c

/-- `stored == query` as the dictionary compares them. -/
def keyMatch : CKey → CKey → Bool
  | .str a, .str b => a == b
  | .sub _ eq, q => eq q.value
  | .str a, .sub _ eq => eq a

def MAXCACHE : Nat := 100

abbrev Cache := List (CKey × SObj)

/-- `PyDict_GetItemRef`: the first stored key that matches. -/
def cacheFind (c : Cache) (k : CKey) : Option SObj :=
  (c.find? (fun p => keyMatch p.1 k)).map (·.2)

/-- `cache_struct_converter` on a key: a hit returns the cached object (2644-2648); a miss calls
`Struct(key)`, which reads the key's value (`PyUnicode_FromObject`), clears the cache when it holds
`MAXCACHE` entries (2652-2653) and stores the new object. -/
def cacheStructC (c : Cache) (k : CKey) : Py SObj × Cache :=
  match cacheFind c k with
  | some s => (.ok s, c)
  | none =>
    match structInit (.str k.value) with
    | .ok s => (.ok s, (if c.length ≥ MAXCACHE then [] else c) ++ [(k, s)])
    | .error e => (.error e, c)

/-- `_clearcache_impl` (2672-2680). -/
def clearCache (_ : Cache) : Cache := []

/-- `unpack(fmt, buf)` through the cache. -/
def modUnpackC (c : Cache) (k : CKey) (buf : List Nat) : Py (List SV) × Cache :=
  match cacheStructC c k with
  | (.ok s, c') => (structUnpack s buf, c')
  | (.error e, c') => (.error e, c')

/-- A cache every entry of which was made from an exact `str` key with that key's own struct. -/
def Coherent (c : Cache) : Prop := ∀ p ∈ c, ∃ v, p.1 = .str v ∧ structInit (.str v) = .ok p.2

/-- With only exact `str` keys in the cache, the cache changes nothing: a hit and a miss give the
struct of the format's value, the cache stays coherent and never holds more than `MAXCACHE` entries;
and after `_clearcache`, whatever the cache held, `unpack` depends only on the format's value again. -/
def CacheCoherent : Prop :=
  (∀ (c : Cache) (v : List Nat), Coherent c → c.length ≤ MAXCACHE →
    (cacheStructC c (.str v)).1 = structInit (.str v) ∧ Coherent (cacheStructC c (.str v)).2 ∧
    (cacheStructC c (.str v)).2.length ≤ MAXCACHE) ∧
  (∀ (c : Cache) (v buf : List Nat), (modUnpackC (clearCache c) (.str v) buf).1 = modUnpack (.str v) buf)

theorem find_coherent (c : Cache) (h : Coherent c) (v : List Nat) (s : SObj)
    (hf : cacheFind c (.str v) = some s) : structInit (.str v) = .ok s := by
  unfold cacheFind at hf
  cases hp : c.find? (fun p => keyMatch p.1 (.str v)) with
  | none => rw [hp] at hf; cases hf
  | some p =>
    rw [hp] at hf
    simp only [Option.map_some, Option.some.injEq] at hf
    have hm := List.find?_some hp
    have hmem := List.mem_of_find?_eq_some hp
    obtain ⟨w, hw, hs⟩ := h p hmem
    rw [hw] at hm
    simp only [keyMatch, beq_iff_eq] at hm
    subst hm; subst hf
    exact hs

theorem clear_law (c : Cache) (v buf : List Nat) :
    (modUnpackC (clearCache c) (.str v) buf).1 = modUnpack (.str v) buf := by
  simp only [clearCache, modUnpackC, cacheStructC, cacheFind, List.find?_nil, Option.map_none, CKey.value,
    modUnpack, cacheStruct, bind, Except.bind]
  cases structInit (.str v) <;> rfl

theorem cacheCoherent_proven : CacheCoherent := by
  refine ⟨fun c v h hl => ?_, clear_law⟩
  unfold cacheStructC
  cases hf : cacheFind c (.str v) with
  | some s =>
    exact ⟨(find_coherent c h v s hf).symm, h, hl⟩
  | none =>
    simp only [CKey.value]
    cases hi : structInit (.str v) with
    | error e => exact ⟨rfl, h, hl⟩
    | ok s =>
      refine ⟨rfl, ?_, ?_⟩
      · intro p hp
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | hp
        · split at hp
          · simp at hp
          · exact h p hp
        · subst hp; exact ⟨v, rfl, hi⟩
      · simp only [List.length_append, List.length_singleton]
        split <;> simp_all [MAXCACHE] <;> omega

/-- `unpack(fmt, buf)` depends only on the value of `fmt`, whatever the cache holds. False: a `str`
subclass whose `__eq__` ignores case leaves `Struct('B')` under its key, and a later plain `'b'` finds
it, so `unpack('b', b'\xff')` returns `255` until `_clearcache()`. -/
def CacheValueOnly : Prop :=
  ∀ (c : Cache) (k : CKey) (c' : Cache), (cacheStructC c k).2 = c' →
    ∀ (v : List Nat) (buf : List Nat), (modUnpackC c' (.str v) buf).1 = modUnpack (.str v) buf

/-- `str.lower` on ASCII code points. -/
def asciiLower (v : List Nat) : List Nat := v.map (fun x => if 65 ≤ x ∧ x ≤ 90 then x + 32 else x)

/-- `class CI(str)` with `__eq__` and `__hash__` on `self.lower()`. -/
def ciKey (v : List Nat) : CKey := .sub v (fun w => asciiLower w == asciiLower v)

theorem cacheValueOnly_refuted : ¬CacheValueOnly := by
  intro h
  have := h [] (ciKey ['B'.toNat]) _ rfl ['b'.toNat] [255]
  revert this
  decide +kernel

end PyLean.TextLibs.Struct
