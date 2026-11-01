import PyLean.DictSet.Merge
import PyLean.DictSet.Managed

/-!
Split tables refine the association list too.

An instance `__dict__` shares its keys with the other instances of the class and holds only a
values array and an insertion-order array. A key can be in the shared keys with no value in this
dict, which is what `dict.setdefault` gets wrong. `SplitWF` is the invariant of such a table: the
keys satisfy `Core`, and the order array lists, without repeats, exactly the slots with a value.

The list a split dict stands for is read through that order array, not through the shared keys, so
it can be in any order relative to `dk_entries`, and it says nothing of keys this dict lacks.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

/-- The value at `index` of a split table, with its shared key. -/
def slot (k : Keys K Unit) (v : Values V) (index : Nat) : Option (Ent K V) :=
  match k.entry index, v.get index with
  | some e, some x => some ⟨e.key, e.hash, x⟩
  | _, _ => none

omit [DecidableEq K] in
theorem splitLive_eq (k : Keys K Unit) (v : Values V) (n : Nat) :
    splitLive k v n = (v.order.take n).filterMap (slot k v) := rfl

/-- The invariant of a split table with `used` items. -/
structure SplitWF (hf : K → Int) (eqv : K → K → Bool) (isStr : K → Bool) (k : Keys K Unit)
    (v : Values V) (used : Nat) : Prop where
  core : Core hf eqv isStr k
  kind : k.kind = .split
  /-- Shared keys are never `Py_EMPTY_KEYS`, and are small (`SHARED_KEYS_MAX_SIZE` is 30). -/
  notEmpty : 0 < k.log2Size
  small : k.log2Size < 64
  /-- Shared keys are never deleted. -/
  entries : ∀ ix, ix < k.nentries → ∃ e, k.entry ix = some e
  /-- `shared_keys_usable_size` of the keys does not exceed the array, which is why :1857's
  assertion `ix < SHARED_KEYS_MAX_SIZE` is not what keeps the store inside it. -/
  cap : (k.nentries : Int) + k.usable ≤ v.capacity
  nent : (k.nentries : Int) + k.usable ≤ usableFraction k.size
  nodup : v.order.Nodup
  order : ∀ ix, ix ∈ v.order ↔ ix < k.nentries ∧ (v.get ix).isSome = true
  /-- Slots past the shared entries hold nothing yet. -/
  high : ∀ ix, k.nentries ≤ ix → v.get ix = none
  used : used = v.order.length

/-- A split dict that satisfies `SplitWF`. -/
def SplitInv (hf : K → Int) (eqv : K → K → Bool) (isStr : K → Bool) (d : PyDict K V) : Prop :=
  ∃ k v, d.body = .split k v ∧ SplitWF hf eqv isStr k v d.used

section Lookup
variable {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}

omit [DecidableEq K] in
theorem entryKH_split (mp : PyDict K V) (k : Keys K Unit) (v : Values V) (h : mp.body = .split k v)
    (ix : Nat) : mp.body.entryKH ix = (k.entry ix).map fun e => (e.key, e.hash) := by
  simp [h, Body.entryKH]

theorem stillThere_split (mp : PyDict K V) (k : Keys K Unit) (v : Values V)
    (h : mp.body = .split k v) (ix : Nat) (e : Ent K Unit) (he : k.entry ix = some e) :
    stillThere mp mp.body.ident ix e.key = true := by
  simp [stillThere, h, Body.entryKH, he]

theorem compareUnicodeGeneric_split (H : Honest P hf eqv) (mp : PyDict K V) (k : Keys K Unit)
    (v : Values V) (hb : mp.body = .split k v) (ix : Nat) (e : Ent K Unit)
    (he : k.entry ix = some e) (hh : e.hash = hf e.key) (key : K) :
    compareUnicodeGeneric P ix key (hf key) mp = (.ok (if eqv e.key key then 1 else 0), mp) := by
  have hkh := entryKH_split mp k v hb ix
  rw [he] at hkh
  simp only [compareUnicodeGeneric, hkh, Option.map_some]
  by_cases h2 : e.hash = hf key
  · simp only [h2, if_true, H.eq_ok]
    have hs := stillThere_split mp k v hb ix e he
    simp only [hs, if_true]
  · have hne : eqv e.key key = false := by
      cases hq : eqv e.key key with
      | false => rfl
      | true =>
        have := H.hash_cons _ _ hq
        exact absurd (hh.trans this) h2
    simp [h2, hne]

/-- `check_lookup` of the exact-str search on a split table. -/
theorem checkUnicode_split (H : Honest P hf eqv) (mp : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : mp.body = .split k v) (c : Core hf eqv P.isStr k) (hk : k.kind = .split) (key : K)
    (hs : P.isStr key = true) (t : Nat) (e : Ent K Unit) (h : k.entry t = some e) :
    checkUnicode P key (hf key) t mp = (.ok (if eqv e.key key then 1 else 0), mp) := by
  have hstr := c.strs t e (by simp [hk]) h
  have hkh := entryKH_split mp k v hb t
  rw [h] at hkh
  simp only [checkUnicode, hkh, Option.map_some]
  have hc : compareUnicodeUnicode P (some (e.key, e.hash)) key (hf key) = eqv e.key key := by
    simp only [compareUnicodeUnicode]
    by_cases h1 : e.key = key
    · subst h1
      simp [H.refl]
    · by_cases h2 : e.hash = hf key
      · simp [h1, h2, H.str_eq _ _ hstr hs]
      · have hne : eqv e.key key = false := by
          cases hq : eqv e.key key with
          | false => rfl
          | true =>
            have := H.hash_cons _ _ hq
            exact absurd ((c.hashes t e h).trans this) h2
        simp [h1, h2, hne]
  rw [hc]

/-- `_Py_dict_lookup` on a split table holding an equal key in its shared keys: it finds that slot
and reads this dict's value there, which may be NULL. -/
theorem lookupAux_split_found (H : Honest P hf eqv) (mp : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : mp.body = .split k v) (c : Core hf eqv P.isStr k) (hk : k.kind = .split) (key : K)
    (ix : Nat) (e : Ent K Unit) (he : k.entry ix = some e) (heq : eqv e.key key = true) (n : Nat) :
    dictLookupAux P key (hf key) (n + 1) mp = (.ok ((ix : Int), v.get ix), mp) := by
  have hmask : mp.body.mask = k.mask := by simp [Body.mask, Body.log2Size, hb, Keys.mask, Keys.size]
  have hfuel : mp.body.log2Size = k.log2Size := by simp [Body.log2Size, hb]
  have hkind : mp.body.kind = .split := by simp [Body.kind, hb, hk]
  have hget : ∀ i, bodyIx mp i = k.getIndex i := by
    intro i; simp [bodyIx, hb, Body.getIndex]
  have hval : mp.body.valueAt ix = v.get ix := by simp [hb, Body.valueAt]
  have hne : ((ix : Int) == DKIX_KEY_CHANGED) = false := by
    simp [DKIX_KEY_CHANGED]
  have hpos : (ix : Int) ≥ 0 := by omega
  have hg' : (Kind.split != Kind.general) = true := by decide
  simp only [dictLookupAux, hmask, hfuel, hkind, hg', if_true]
  by_cases hs : P.isStr key = true
  · simp only [hs, if_true]
    rw [search_found k c H bodyIx (checkUnicode P key (hf key)) mp key hget
      (fun t e' h => checkUnicode_split H mp k v hb c hk key hs t e' h) ix e he heq]
    simp [hne, hpos, hval]
  · simp only [hs, if_false, Bool.false_eq_true, unicodekeysLookupGeneric]
    rw [search_found k c H bodyIx (fun t => compareUnicodeGeneric P t key (hf key)) mp key hget
      (fun t e' h => compareUnicodeGeneric_split H mp k v hb t e' h (c.hashes t e' h) key) ix e he heq]
    simp [hne, hpos, hval]

theorem lookupAux_split_missing (H : Honest P hf eqv) (mp : PyDict K V) (k : Keys K Unit)
    (v : Values V) (hb : mp.body = .split k v) (c : Core hf eqv P.isStr k) (hk : k.kind = .split)
    (key : K) (hno : ∀ ix e, k.entry ix = some e → eqv e.key key = false) (n : Nat) :
    dictLookupAux P key (hf key) (n + 1) mp = (.ok (DKIX_EMPTY, none), mp) := by
  have hmask : mp.body.mask = k.mask := by simp [Body.mask, Body.log2Size, hb, Keys.mask, Keys.size]
  have hfuel : mp.body.log2Size = k.log2Size := by simp [Body.log2Size, hb]
  have hkind : mp.body.kind = .split := by simp [Body.kind, hb, hk]
  have hget : ∀ i, bodyIx mp i = k.getIndex i := by
    intro i; simp [bodyIx, hb, Body.getIndex]
  have hne : (DKIX_EMPTY == DKIX_KEY_CHANGED) = false := by decide
  have hneg : ¬ (DKIX_EMPTY ≥ 0) := by decide
  have hg' : (Kind.split != Kind.general) = true := by decide
  simp only [dictLookupAux, hmask, hfuel, hkind, hg', if_true]
  by_cases hs : P.isStr key = true
  · simp only [hs, if_true]
    rw [search_missing k c bodyIx (checkUnicode P key (hf key)) mp key hget
      (fun t e' h => checkUnicode_split H mp k v hb c hk key hs t e' h) hno]
    simp [hne, hneg]
  · simp only [hs, if_false, Bool.false_eq_true, unicodekeysLookupGeneric]
    rw [search_missing k c bodyIx (fun t => compareUnicodeGeneric P t key (hf key)) mp key hget
      (fun t e' h => compareUnicodeGeneric_split H mp k v hb t e' h (c.hashes t e' h) key) hno]
    simp [hne, hneg]

end Lookup

section Lists
variable {eqv : K → K → Bool}

omit [DecidableEq K] in
/-- The list of a split table is read through the order array, and the first match is the slot
of the equal key, if the order array holds it. -/
theorem find_slot (k : Keys K Unit) (v : Values V) (key : K) (ix : Nat) (e : Ent K Unit)
    (he : k.entry ix = some e) (heq : eqv e.key key = true)
    (huniq : ∀ i e', k.entry i = some e' → eqv e'.key key = true → i = ix) :
    ∀ order : List Nat,
      (order.filterMap (slot k v)).find? (fun x => eqv x.key key) =
        if ix ∈ order then (v.get ix).map fun x => (⟨e.key, e.hash, x⟩ : Ent K V) else none := by
  intro order
  induction order with
  | nil => simp
  | cons a t ih =>
    by_cases ha : a = ix
    · subst ha
      cases hv : v.get a with
      | none =>
        have hs : slot k v a = none := by simp [slot, he, hv]
        simp only [List.filterMap_cons, hs, ih]
        simp [hv]
      | some x =>
        have hs : slot k v a = some ⟨e.key, e.hash, x⟩ := by simp [slot, he, hv]
        simp [List.filterMap_cons, hs, heq]
    · have hmem : (ix ∈ a :: t) ↔ ix ∈ t := by
        simp only [List.mem_cons]
        constructor
        · rintro (h | h)
          · exact absurd h.symm ha
          · exact h
        · exact Or.inr
      simp only [hmem]
      cases hs : slot k v a with
      | none => simp only [List.filterMap_cons, hs, ih]
      | some y =>
        have hno : eqv y.key key = false := by
          cases hq : eqv y.key key with
          | false => rfl
          | true =>
            exfalso
            simp only [slot] at hs
            split at hs
            · rename_i e' x h1 h2
              simp only [Option.some.injEq] at hs
              subst hs
              exact ha (huniq a e' h1 hq)
            · simp at hs
        simp [List.filterMap_cons, hs, hno, ih]

omit [DecidableEq K] in
/-- With no equal key in the shared keys, nothing in the list matches. -/
theorem find_slot_none (k : Keys K Unit) (v : Values V) (key : K)
    (hno : ∀ ix e, k.entry ix = some e → eqv e.key key = false) :
    ∀ order : List Nat, (order.filterMap (slot k v)).find? (fun x => eqv x.key key) = none := by
  intro order
  induction order with
  | nil => simp
  | cons a t ih =>
    cases hs : slot k v a with
    | none => simp only [List.filterMap_cons, hs, ih]
    | some y =>
      have hn : eqv y.key key = false := by
        simp only [slot] at hs
        split at hs
        · rename_i e' x h1 h2
          simp only [Option.some.injEq] at hs
          subst hs
          exact hno a e' h1
        · simp at hs
      simp [List.filterMap_cons, hs, hn, ih]

end Lists

section Assoc
variable {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}

omit [DecidableEq K] in
theorem dictAssoc_split (d : PyDict K V) (k : Keys K Unit) (v : Values V) (hb : d.body = .split k v)
    (w : SplitWF hf eqv isStr k v d.used) :
    dictAssoc d = (v.order.filterMap (slot k v)).map fun e => (e.key, e.value) := by
  have ht : v.order.take d.used = v.order := by rw [w.used]; simp
  simp [dictAssoc, hb, splitLive_eq, ht]

/-- A value in a split dict is a value in the list. -/
theorem assocGet_split_found (d : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : d.body = .split k v) (w : SplitWF hf eqv P.isStr k v d.used) (H : Honest P hf eqv)
    (key : K) (ix : Nat) (e : Ent K Unit) (he : k.entry ix = some e) (heq : eqv e.key key = true) :
    assocGet eqv (dictAssoc d) key = v.get ix := by
  have huniq : ∀ i e', k.entry i = some e' → eqv e'.key key = true → i = ix := by
    intro i e' h1 h2
    refine w.core.uniq i e' ix e h1 he ?_
    exact H.trans _ key _ h2 (by rw [H.symm]; exact heq)
  have hix : ix < k.nentries := by
    have : (k.entries[ix]?).join = some e := he
    cases hg : k.entries[ix]? with
    | none => simp [hg] at this
    | some x => exact (List.getElem?_eq_some_iff.mp hg).1
  rw [dictAssoc_split d k v hb w]
  simp only [assocGet, List.find?_map, Function.comp_def]
  have := find_slot (V := V) (eqv := eqv) k v key ix e he heq huniq v.order
  simp only [this]
  by_cases hm : ix ∈ v.order
  · simp only [hm, if_true]
    cases hv : v.get ix <;> simp
  · have hv : v.get ix = none := by
      cases hv : v.get ix with
      | none => rfl
      | some x => exact absurd ((w.order ix).mpr ⟨hix, by simp [hv]⟩) hm
    simp [hm, hv]

theorem assocGet_split_none (d : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : d.body = .split k v) (w : SplitWF hf eqv P.isStr k v d.used) (key : K)
    (hno : ∀ ix e, k.entry ix = some e → eqv e.key key = false) :
    assocGet eqv (dictAssoc d) key = none := by
  rw [dictAssoc_split d k v hb w]
  simp only [assocGet, List.find?_map, Function.comp_def]
  have := find_slot_none (V := V) (eqv := eqv) k v key hno v.order
  simp [this]

/-- `_Py_dict_lookup` on a split dict agrees with the list, in both directions, for a key of any
kind. This is where a key in the shared keys with no value in this dict shows as absent. -/
theorem lookup_split (H : Honest P hf eqv) (d : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : d.body = .split k v) (w : SplitWF hf eqv P.isStr k v d.used) (key : K) :
    ∃ ix, dictLookup P key (hf key) d = (.ok (ix, assocGet eqv (dictAssoc d) key), d) := by
  rcases dichotomy (eqv := eqv) k key with ⟨ix, e, h1, h2⟩ | hno
  · refine ⟨ix, ?_⟩
    rw [assocGet_split_found d k v hb w H key ix e h1 h2]
    exact lookupAux_split_found H d k v hb w.core w.kind key ix e h1 h2 255
  · refine ⟨DKIX_EMPTY, ?_⟩
    rw [assocGet_split_none d k v hb w key hno]
    exact lookupAux_split_missing H d k v hb w.core w.kind key hno 255

end Assoc

namespace Values
variable {V : Type}

theorem get_set_self (v : Values V) (ix : Nat) (x : Option V) (h : ix < v.capacity) :
    (v.set ix x).get ix = x := by
  have h' : ix < v.values.length := h
  simp [Values.get, Values.set, h']

theorem get_set_ne (v : Values V) (ix j : Nat) (x : Option V) (h : j ≠ ix) :
    (v.set ix x).get j = v.get j := by
  simp only [Values.get, Values.set]
  rw [List.getElem?_set_ne (Ne.symm h)]

theorem capacity_set (v : Values V) (ix : Nat) (x : Option V) : (v.set ix x).capacity = v.capacity := by
  simp [Values.capacity, Values.set]

theorem lt_capacity (v : Values V) (ix : Nat) (x : V) (h : v.get ix = some x) : ix < v.capacity := by
  simp only [Values.get] at h
  cases hg : v.values[ix]? with
  | none => simp [hg] at h
  | some y => exact (List.getElem?_eq_some_iff.mp hg).1

end Values

/-- Two lists that hold equal keys, in the same order, with the same values. A split table keeps
the shared key object, so a store can leave an equal key rather than the one it was given. -/
inductive AssocEq (eqv : K → K → Bool) : List (K × V) → List (K × V) → Prop where
  | nil : AssocEq eqv [] []
  | cons {a b : K × V} {l l' : List (K × V)} : eqv a.1 b.1 = true → a.2 = b.2 → AssocEq eqv l l' →
      AssocEq eqv (a :: l) (b :: l')

omit [DecidableEq K] in
theorem AssocEq.refl {eqv : K → K → Bool} (hr : ∀ a, eqv a a = true) (l : List (K × V)) :
    AssocEq eqv l l := by
  induction l with
  | nil => exact .nil
  | cons a t ih => exact .cons (hr a.1) rfl ih

omit [DecidableEq K] in
/-- Lists that differ in the object of the last key, equal under `eqv`. -/
theorem AssocEq.append_last {eqv : K → K → Bool} (hr : ∀ a, eqv a a = true) (l : List (K × V))
    (a b : K) (x : V) (h : eqv a b = true) : AssocEq eqv (l ++ [(a, x)]) (l ++ [(b, x)]) := by
  induction l with
  | nil => exact .cons h rfl .nil
  | cons p t ih => exact .cons (hr p.1) rfl ih

section Append
variable {W : Type} {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}

/-- `appendEntry` on any keys object with room, for a key that is not in it. This is `insert_split_key`
adding a shared key, and it keeps `Core`. -/
theorem appendEntry_core (H : Honest P hf eqv) (k : Keys K W) (w : Core hf eqv P.isStr k)
    (hus : 0 < k.usable) (key : K) (v : W)
    (hno : ∀ ix e, k.entry ix = some e → eqv e.key key = false)
    (hstr : k.kind ≠ .general → P.isStr key = true) :
    ∃ k' : Keys K W, appendEntry k key (hf key) v = .ok k' ∧ Core hf eqv P.isStr k' ∧
      k'.kind = k.kind ∧ k'.nentries = k.nentries + 1 ∧ k'.usable = k.usable - 1 ∧
      k'.size = k.size ∧ k'.log2Size = k.log2Size ∧
      (∀ ix e', k.entry ix = some e' → k'.entry ix = some e') ∧
      k'.entry k.nentries = some ⟨key, hf key, v⟩ := by
  let e : Ent K W := ⟨key, hf key, v⟩
  obtain ⟨j0, hj0, hemp⟩ := w.stops (hf key)
  have hw := probeUntil_walk (fun ix => !isUnusableSlot ix) k.indices k.mask (toU64 (hf key))
    (probeFuel k.log2Size) 0
    ⟨j0, by omega, by omega, by
      have : k.indices.getD (probeState k.mask (toU64 (hf key)) j0).1 DKIX_EMPTY = DKIX_EMPTY := hemp
      rw [this]
      decide⟩
  obtain ⟨j, _, hj, hstop, hpre, hres⟩ := hw
  simp only [Nat.zero_add] at hj
  have hat : k.getIndex (k.pos (hf key) j) < 0 := by
    have : (!isUnusableSlot (k.getIndex (k.pos (hf key) j))) = true := hstop
    simpa [isUnusableSlot] using this
  have hslt : k.pos (hf key) j < k.indices.length := by rw [w.len]; exact k.pos_lt _ _
  let k' : Keys K W := { (k.setIndex (k.pos (hf key) j) k.nentries) with
    entries := k.entries ++ [some e]
    usable := k.usable - 1
    version := 0 }
  have hentry : ∀ ix e', k'.entry ix = some e' →
      (k.entry ix = some e') ∨ (ix = k.nentries ∧ e' = e) := by
    intro ix e' h
    have h' := (entry_iff k' ix e').mp h
    simp only [k', Keys.nentries] at h' ⊢
    by_cases hlt : ix < k.entries.length
    · rw [List.getElem?_append_left hlt] at h'
      exact Or.inl ((entry_iff k ix e').mpr h')
    · have hge : k.entries.length ≤ ix := by omega
      rw [List.getElem?_append_right hge] at h'
      by_cases hz : ix - k.entries.length = 0
      · have : e' = e := by simpa [hz] using h'.symm
        exact Or.inr ⟨by omega, this⟩
      · simp [hz] at h'
  have hold : ∀ ix e', k.entry ix = some e' → k'.entry ix = some e' := by
    intro ix e' h
    have h' := (entry_iff k ix e').mp h
    refine (entry_iff k' ix e').mpr ?_
    have hlt : ix < k.entries.length := (List.getElem?_eq_some_iff.mp h').1
    simp only [k']
    rw [List.getElem?_append_left hlt]
    exact h'
  have hnew : k'.entry k.nentries = some e := by
    refine (entry_iff k' _ e).mpr ?_
    simp [k', Keys.nentries]
  have hne' : ∀ ix e', k.entry ix = some e' → eqv e'.key e.key = false := hno
  have hc' : Chain k' := chain_add k w.toChain e (k.pos (hf key) j) j hj rfl hat
    (fun j' h => by
      have hb := hpre j' (by omega) h
      intro he
      apply hb
      have : k.indices.getD (probeState k.mask (toU64 (hf key)) j').1 DKIX_EMPTY = DKIX_EMPTY := he
      rw [this]
      decide) k' rfl rfl rfl
  refine ⟨k', ?_, ?_, rfl, by simp [k', Keys.nentries], rfl, rfl, rfl, hold, hnew⟩
  · simp only [appendEntry, findEmptySlot]
    have hr : probeUntil (fun ix => !isUnusableSlot ix) k.indices k.mask (probeFuel k.log2Size)
        (toU64 (hf key) &&& k.mask) (toU64 (hf key)) = .ok (k.pos (hf key) j) := hres
    simp only [hr]
    rfl
  · refine { toChain := hc', hashes := ?_, uniq := ?_, strs := ?_, load := ?_, usableNN := ?_ }
    · intro ix e' h
      rcases hentry ix e' h with h1 | ⟨_, rfl⟩
      · exact w.hashes ix e' h1
      · rfl
    · intro i1 e1 i2 e2 a b c
      rcases hentry i1 e1 a with h1 | ⟨h1, rfl⟩ <;> rcases hentry i2 e2 b with h2 | ⟨h2, rfl⟩
      · exact w.uniq i1 e1 i2 e2 h1 h2 c
      · rw [hne' i1 e1 h1] at c
        exact absurd c (by simp)
      · rw [H.symm, hne' i2 e2 h2] at c
        exact absurd c (by simp)
      · omega
    · intro ix e' hg h
      rcases hentry ix e' h with h1 | ⟨_, rfl⟩
      · exact w.strs ix e' hg h1
      · exact hstr hg
    · have h1 := filled_set k (k.pos (hf key) j) k.nentries hslt
      have h2 : k'.filled = (k.setIndex (k.pos (hf key) j) k.nentries).filled := rfl
      have h3 : k'.usable = k.usable - 1 := rfl
      have h4 : k'.size = k.size := rfl
      have h5 := w.load
      rw [h3, h4]
      omega
    · have h3 : k'.usable = k.usable - 1 := rfl
      rw [h3]
      omega

end Append

section Live
variable {hf : K → Int} {eqv : K → K → Bool} {isStr : K → Bool} {k : Keys K Unit} {v : Values V}
  {used : Nat}

/-- The entries of a split table, in insertion order. -/
def live (k : Keys K Unit) (v : Values V) : List (Ent K V) := v.order.filterMap (slot k v)

omit [DecidableEq K] in
theorem slot_some {k : Keys K Unit} {v : Values V} {ix : Nat} {e : Ent K V}
    (h : slot k v ix = some e) :
    ∃ e0 x, k.entry ix = some e0 ∧ v.get ix = some x ∧ e = ⟨e0.key, e0.hash, x⟩ := by
  simp only [slot] at h
  split at h
  · rename_i e0 x h1 h2
    simp only [Option.some.injEq] at h
    exact ⟨e0, x, h1, h2, h.symm⟩
  · simp at h

omit [DecidableEq K] in
theorem mem_live_slot {k : Keys K Unit} {v : Values V} {e : Ent K V} (h : e ∈ live k v) :
    ∃ ix e0 x, ix ∈ v.order ∧ k.entry ix = some e0 ∧ v.get ix = some x ∧ e = ⟨e0.key, e0.hash, x⟩ := by
  obtain ⟨ix, h1, h2⟩ := List.mem_filterMap.mp h
  obtain ⟨e0, x, h3, h4, h5⟩ := slot_some h2
  exact ⟨ix, e0, x, h1, h3, h4, h5⟩

omit [DecidableEq K] in
theorem length_filterMap_all {α β : Type} (f : α → Option β) :
    ∀ l : List α, (∀ a ∈ l, (f a).isSome = true) → (l.filterMap f).length = l.length := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    intro h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a (by simp))
    simp [List.filterMap_cons, hb, ih (fun x hx => h x (by simp [hx]))]

omit [DecidableEq K] in
theorem slot_of_order (w : SplitWF hf eqv isStr k v used) {ix : Nat} (h : ix ∈ v.order) :
    ∃ e0 x, k.entry ix = some e0 ∧ v.get ix = some x ∧
      slot k v ix = some ⟨e0.key, e0.hash, x⟩ := by
  obtain ⟨h1, h2⟩ := (w.order ix).mp h
  obtain ⟨e0, h3⟩ := w.entries ix h1
  obtain ⟨x, h4⟩ := Option.isSome_iff_exists.mp h2
  exact ⟨e0, x, h3, h4, by simp [slot, h3, h4]⟩

omit [DecidableEq K] in
theorem live_length (w : SplitWF hf eqv isStr k v used) : (live k v).length = used := by
  rw [w.used]
  apply length_filterMap_all
  intro a ha
  obtain ⟨_, _, _, _, h⟩ := slot_of_order w ha
  simp [h]

omit [DecidableEq K] in
theorem live_pairwise (c : Core hf eqv isStr k) :
    ∀ order : List Nat, order.Nodup →
      (order.filterMap (slot k v)).Pairwise (fun a b => eqv a.key b.key = false) := by
  intro order
  induction order with
  | nil => simp
  | cons a t ih =>
    intro hn
    have hn' := List.nodup_cons.mp hn
    cases hs : slot k v a with
    | none =>
      simp only [List.filterMap_cons, hs]
      exact ih hn'.2
    | some y =>
      simp only [List.filterMap_cons, hs]
      refine List.pairwise_cons.mpr ⟨?_, ih hn'.2⟩
      intro z hz
      obtain ⟨b, hb, hb2⟩ := List.mem_filterMap.mp hz
      obtain ⟨e1, x1, h1, _, rfl⟩ := slot_some hs
      obtain ⟨e2, x2, h2, _, rfl⟩ := slot_some hb2
      cases hq : eqv e1.key e2.key with
      | false => rfl
      | true =>
        have : a = b := c.uniq a e1 b e2 h1 h2 hq
        exact absurd (this ▸ hb) hn'.1

end Live

section Resize
variable {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}

/-- `dictresize` of a split dict: the first move of a split table to a combined one. The entries
keep the order of the insertion-order array, which is what the list says, and the result is
`unicode` or general as asked. -/
theorem dictResize_split (H : Honest P hf eqv) (mp : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : mp.body = .split k v) (w : SplitWF hf eqv P.isStr k v mp.used) (log2New : Nat)
    (hlt : log2New < 64) (hroom : mp.used ≤ usableFraction (2 ^ log2New)) (unicode : Bool) :
    ∃ k' : Keys K V, dictResize log2New unicode mp =
        (.ok (), { mp with nextId := mp.nextId + 1, body := .combined k' }) ∧
      WF hf eqv P.isStr k' ∧ liveEntries k' = live k v ∧ k'.log2Size = log2New ∧
      k'.usable = (usableFraction (2 ^ log2New) : Int) - mp.used ∧
      (unicode = false → k'.kind = .general) := by
  have hlen := live_length w
  let u' := unicode
  let k0 : Keys K V := newKeysObject mp.nextId log2New u'
  have hk0 : Chain k0 := chain_new _ _ _
  have hf0 : k0.filled = 0 := by
    simp [Keys.filled, k0, newKeysObject, List.countP_replicate, DKIX_EMPTY]
  have hsz0 : k0.size = 2 ^ log2New := rfl
  have hroom' : (live k v).length ≤ k0.size := by
    have := usableFraction_lt (2 ^ log2New) (Nat.pow_pos (by omega))
    rw [hsz0]
    omega
  obtain ⟨idx, h1, h2, h3⟩ := build_spec (live k v) k0 hk0 (by omega)
  have ht : v.order.take mp.used = v.order := by rw [w.used]; simp
  have hlv : splitLive k v mp.used = live k v := by rw [splitLive_eq, ht]; rfl
  let k' : Keys K V := { k0 with
    indices := idx
    entries := (live k v).map some
    usable := k0.usable - mp.used }
  have hentries : (k'.entries) = (live k v).map some := rfl
  have hent : ∀ ix e, k'.entry ix = some e → (live k v)[ix]? = some e := by
    intro ix e h
    have := (entry_iff k' ix e).mp h
    rw [hentries] at this
    simpa using this
  have hlive : liveEntries k' = live k v := by
    simp [liveEntries, k']
  have hpair := live_pairwise (V := V) (v := v) w.core v.order w.nodup
  have hmem : ∀ ix e, k'.entry ix = some e → e ∈ live k v := by
    intro ix e h
    exact List.mem_of_getElem? (hent ix e h)
  have hchain : Chain k' := by
    have hc := h2
    simp only [k0, newKeysObject, List.nil_append] at hc
    exact ⟨hc.len, hc.range, hc.inj, hc.reach⟩
  have hkind : k'.kind = if u' then .unicode else .general := rfl
  have hus : k'.usable = (usableFraction (2 ^ log2New) : Int) - mp.used := rfl
  refine ⟨k', ?_, ?_, hlive, rfl, hus, ?_⟩
  · simp only [dictResize]
    rw [if_neg (by omega)]
    have hu : (Body.split k v : Body K V).isUnicode = true := by
      simp [Body.isUnicode, Body.kind, w.kind]
    simp only [hb, hu, if_true, hlv]
    have h1' : buildIndices (newKeysObject mp.nextId log2New unicode : Keys K V).mask (probeFuel log2New)
        (newKeysObject mp.nextId log2New unicode : Keys K V).indices 0
        ((live k v).map (·.hash)) = .ok idx := h1
    rw [h1']
  · refine { toChain := hchain, hashes := ?_, uniq := ?_, strs := ?_, notSplit := ?_, load := ?_,
             nent := ?_, usableNN := ?_, small := hlt }
    · intro ix e h
      obtain ⟨t, e0, x, _, h4, _, rfl⟩ := mem_live_slot (hmem ix e h)
      exact w.core.hashes t e0 h4
    · intro i1 e1 i2 e2 a b c
      exact uniq_of_pairwise eqv H.symm _ hpair i1 i2 e1 e2 (hent i1 e1 a) (hent i2 e2 b) c
    · intro ix e _ h
      obtain ⟨t, e0, x, _, h4, _, rfl⟩ := mem_live_slot (hmem ix e h)
      exact w.core.strs t e0 (by simp [w.kind]) h4
    · rw [hkind]
      cases u' <;> simp
    · have : k'.filled ≤ (live k v).length := by
        have h3' : ({ k0 with indices := idx } : Keys K V).filled ≤ 0 + (live k v).length := by
          rw [hf0] at h3
          exact h3
        simpa [Keys.filled, k'] using h3'
      rw [hus]
      have hsz : k'.size = 2 ^ log2New := rfl
      rw [hsz]
      omega
    · have : k'.nentries = (live k v).length := by simp [Keys.nentries, k']
      rw [hus, this]
      have hsz : k'.size = 2 ^ log2New := rfl
      rw [hsz]
      omega
    · rw [hus]
      omega
  · intro hun
    rw [hkind]
    simp [u', hun]

/-- `insertion_resize` of a split dict: `MemoryError` with nothing changed, or a combined table with
room. -/
theorem insertionResize_split (H : Honest P hf eqv) (mp : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : mp.body = .split k v) (w : SplitWF hf eqv P.isStr k v mp.used) (unicode : Bool) :
    (TooBig mp.used ∧ insertionResize unicode mp = (.error memoryError, mp)) ∨
    ∃ k' : Keys K V, insertionResize unicode mp =
        (.ok (), { mp with nextId := mp.nextId + 1, body := .combined k' }) ∧
      WF hf eqv P.isStr k' ∧ liveEntries k' = live k v ∧ 0 < k'.usable ∧
      (unicode = false → k'.kind = .general) := by
  simp only [insertionResize]
  by_cases hlt : calculateLog2Keysize (growthRate mp.used) < 64
  · right
    have hr := growth_room mp.used
    obtain ⟨k', h1, h2, h3, _, h5, h6⟩ := dictResize_split H mp k v hb w _ hlt (by omega) unicode
    refine ⟨k', h1, h2, h3, ?_, h6⟩
    rw [h5]
    omega
  · left
    refine ⟨by simp only [TooBig]; omega, ?_⟩
    simp only [dictResize]
    rw [if_pos (by omega)]

end Resize

section ListFacts
variable {eqv : K → K → Bool}

omit [DecidableEq K] in
theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ l : List α, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    simp only [List.filterMap_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

omit [DecidableEq K] in
theorem any_of_assocGet (l : List (K × V)) (key : K) (y : V) (h : assocGet eqv l key = some y) :
    l.any (fun p => eqv p.1 key) = true := by
  simp only [assocGet] at h
  obtain ⟨p, hp, _⟩ := Option.map_eq_some_iff.mp h
  have hq : eqv p.1 key = true := by
    have := List.find?_some (p := fun p : K × V => eqv p.1 key) hp
    simpa using this
  exact List.any_eq_true.mpr ⟨p, List.mem_of_find?_eq_some hp, hq⟩

omit [DecidableEq K] in
theorem any_of_assocGet_none (l : List (K × V)) (key : K) (h : assocGet eqv l key = none) :
    l.any (fun p => eqv p.1 key) = false := by
  simp only [assocGet, Option.map_eq_none_iff] at h
  have := List.find?_eq_none.mp h
  exact List.any_eq_false.mpr (fun p hp hq => this p hp hq)

end ListFacts

section Store
variable {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}

omit [DecidableEq K] in
theorem pairs_store (k : Keys K Unit) (v : Values V) (key : K) (ix : Nat) (e : Ent K Unit) (x : V)
    (he : k.entry ix = some e) (heq : eqv e.key key = true) (hix : ix < v.capacity)
    (huniq : ∀ i e', k.entry i = some e' → eqv e'.key key = true → i = ix) :
    ∀ order : List Nat, (∀ j ∈ order, (v.get j).isSome = true) →
      (order.filterMap (slot k (v.set ix (some x)))).map (fun e => (e.key, e.value)) =
        ((order.filterMap (slot k v)).map (fun e => (e.key, e.value))).map
          (fun p => if eqv p.1 key then (p.1, x) else p) := by
  intro order
  induction order with
  | nil => intro _; rfl
  | cons a t ih =>
    intro hm
    have hrest := ih (fun j hj => hm j (by simp [hj]))
    by_cases ha : a = ix
    · subst ha
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hm a (by simp))
      have h1 : slot k (v.set a (some x)) a = some ⟨e.key, e.hash, x⟩ := by
        simp [slot, he, v.get_set_self a (some x) hix]
      have h2 : slot k v a = some ⟨e.key, e.hash, y⟩ := by simp [slot, he, hy]
      simp [List.filterMap_cons, h1, h2, heq, hrest]
    · have h1 : slot k (v.set ix (some x)) a = slot k v a := by
        simp only [slot, v.get_set_ne ix a (some x) ha]
      simp only [List.filterMap_cons, h1]
      cases hs : slot k v a with
      | none => simpa using hrest
      | some y =>
        obtain ⟨e0, z, h3, _, rfl⟩ := slot_some hs
        have hn : eqv e0.key key = false := by
          cases hq : eqv e0.key key with
          | false => rfl
          | true => exact absurd (huniq a e0 h3 hq) ha
        simp [hn, hrest]

/-- Storing over a value this dict has: the table stays split, and the list changes that value. -/
theorem split_store (H : Honest P hf eqv) (d : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : d.body = .split k v) (w : SplitWF hf eqv P.isStr k v d.used) (key : K) (ix : Nat)
    (e : Ent K Unit) (he : k.entry ix = some e) (heq : eqv e.key key = true) (y x : V)
    (hy : v.get ix = some y) :
    SplitInv hf eqv P.isStr { d with body := .split k (v.set ix (some x)) } ∧
      dictAssoc { d with body := .split k (v.set ix (some x)) } =
        assocSet eqv (dictAssoc d) key x := by
  have hix := v.lt_capacity ix y hy
  have huniq : ∀ i e', k.entry i = some e' → eqv e'.key key = true → i = ix := by
    intro i e' h1 h2
    exact w.core.uniq i e' ix e h1 he (H.trans _ key _ h2 (by rw [H.symm]; exact heq))
  have hget : ∀ j, ((v.set ix (some x)).get j).isSome = (v.get j).isSome := by
    intro j
    by_cases hj : j = ix
    · subst hj
      rw [v.get_set_self j (some x) hix, hy]
      rfl
    · rw [v.get_set_ne ix j (some x) hj]
  have hw : SplitWF hf eqv P.isStr k (v.set ix (some x)) d.used :=
    { core := w.core, kind := w.kind, notEmpty := w.notEmpty, small := w.small, entries := w.entries
      cap := by rw [v.capacity_set]; exact w.cap
      nent := w.nent, nodup := w.nodup
      order := fun j => by
        rw [hget j]
        exact w.order j
      high := fun j hj => by
        have hne : j ≠ ix := by
          intro h
          have := (w.high j hj)
          rw [h, hy] at this
          simp at this
        rw [v.get_set_ne ix j (some x) hne]
        exact w.high j hj
      used := w.used }
  refine ⟨⟨k, _, rfl, hw⟩, ?_⟩
  have hany := any_of_assocGet (eqv := eqv) (dictAssoc d) key y
    (by rw [assocGet_split_found d k v hb w H key ix e he heq, hy])
  have hl := dictAssoc_split (hf := hf) (isStr := P.isStr) { d with body := .split k (v.set ix (some x)) }
    k (v.set ix (some x)) rfl hw
  rw [hl]
  simp only [assocSet, hany, if_true]
  rw [dictAssoc_split d k v hb w]
  exact pairs_store k v key ix e x he heq hix huniq v.order
    (fun j hj => ((w.order j).mp hj).2)

/-- Storing a value at a slot this dict lacks, in shared keys `k'` that extend `k` or equal it. The
table stays split, the slot joins the end of the order array, and the list gains one pair, under
the shared key object. -/
theorem split_new (d : PyDict K V) (k k' : Keys K Unit) (v : Values V) (hb : d.body = .split k v)
    (w : SplitWF hf eqv P.isStr k v d.used) (core' : Core hf eqv P.isStr k') (kind' : k'.kind = .split)
    (log' : 0 < k'.log2Size) (small' : k'.log2Size < 64)
    (entries' : ∀ ix, ix < k'.nentries → ∃ e, k'.entry ix = some e)
    (cap' : (k'.nentries : Int) + k'.usable ≤ v.capacity)
    (nent' : (k'.nentries : Int) + k'.usable ≤ usableFraction k'.size)
    (hle : k.nentries ≤ k'.nentries)
    (hold : ∀ ix e, k.entry ix = some e → k'.entry ix = some e)
    (ix : Nat) (e' : Ent K Unit) (hix : ix < k'.nentries) (hent : k'.entry ix = some e')
    (hvn : v.get ix = none) (x : V) :
    let v' := (v.set ix (some x)).addToOrder ix
    let d' : PyDict K V := { d with used := d.used + 1, body := .split k' v' }
    SplitInv hf eqv P.isStr d' ∧ dictAssoc d' = dictAssoc d ++ [(e'.key, x)] := by
  intro v' d'
  have hcap : ix < v.capacity := by
    have := core'.usableNN
    omega
  have hnot : ix ∉ v.order := fun h => by
    have := ((w.order ix).mp h).2
    rw [hvn] at this
    simp at this
  have hgetv : ∀ j, v'.get j = (v.set ix (some x)).get j := fun _ => rfl
  have hcapv : v'.capacity = v.capacity := by
    simp [v', Values.capacity, Values.addToOrder, Values.set]
  have hw : SplitWF hf eqv P.isStr k' v' (d.used + 1) :=
    { core := core', kind := kind', notEmpty := log', small := small', entries := entries'
      cap := by rw [hcapv]; exact cap'
      nent := nent'
      nodup := by
        simp only [v', Values.addToOrder, Values.set]
        refine List.pairwise_append.mpr ⟨w.nodup, by simp, ?_⟩
        intro a ha b hb'
        simp only [List.mem_singleton] at hb'
        intro hab
        exact hnot (by rw [← hb', ← hab]; exact ha)
      order := fun j => by
        simp only [v', Values.addToOrder, Values.set, List.mem_append, List.mem_singleton]
        have hg := hgetv j
        simp only [v', Values.addToOrder, Values.set] at hg
        rw [hg]
        by_cases hj : j = ix
        · subst hj
          have : (v.set j (some x)).get j = some x := v.get_set_self j _ hcap
          simp only [Values.set] at this
          simp [this, hix]
        · have : (v.set ix (some x)).get j = v.get j := v.get_set_ne ix j _ hj
          simp only [Values.set] at this
          rw [this]
          constructor
          · rintro (h | h)
            · have := (w.order j).mp h
              exact ⟨by omega, this.2⟩
            · exact absurd h hj
          · rintro ⟨h1, h2⟩
            refine Or.inl ((w.order j).mpr ⟨?_, h2⟩)
            by_cases hlt : j < k.nentries
            · exact hlt
            · have := w.high j (by omega)
              rw [this] at h2
              simp at h2
      high := fun j hj => by
        have hne : j ≠ ix := by omega
        rw [hgetv, v.get_set_ne ix j _ hne]
        exact w.high j (by omega)
      used := by
        simp only [v', Values.addToOrder, Values.set, List.length_append, List.length_singleton]
        rw [w.used] }
  refine ⟨⟨k', v', rfl, hw⟩, ?_⟩
  have hl := dictAssoc_split (hf := hf) (isStr := P.isStr) d' k' v' rfl hw
  rw [hl, dictAssoc_split d k v hb w]
  have hcongr : v.order.filterMap (slot k' v') = v.order.filterMap (slot k v) := by
    apply filterMap_congr'
    intro j hj
    obtain ⟨e0, y, h1, h2, h3⟩ := slot_of_order w hj
    have hne : j ≠ ix := fun h => hnot (h ▸ hj)
    have hv : v'.get j = some y := by rw [hgetv, v.get_set_ne ix j _ hne, h2]
    rw [h3]
    simp [slot, hold j e0 h1, hv]
  have hlast : slot k' v' ix = some ⟨e'.key, e'.hash, x⟩ := by
    have hv : v'.get ix = some x := by rw [hgetv, v.get_set_self ix _ hcap]
    simp [slot, hent, hv]
  have horder : v'.order = v.order ++ [ix] := rfl
  rw [horder, List.filterMap_append, hcongr]
  simp [hlast]

end Store

section New
variable {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}

/-- The way out of a split table: the key is not in this dict and the table cannot take it, because
the key is not an exact str, or the shared keys are full. `insert_combined_dict` resizes to a
combined table and appends. -/
theorem insertNew_split (H : Honest P hf eqv) (d : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : d.body = .split k v) (w : SplitWF hf eqv P.isStr k v d.used) (key : K) (value : V) (ix : Int)
    (habs : assocGet eqv (dictAssoc d) key = none)
    (hroute : P.isStr key = false ∨ (P.isStr key = true ∧ k.usable ≤ 0)) :
    (TooBig d.used ∧ insertAfterLookup P key (hf key) value ix none d = (.error memoryError, d)) ∨
    ∃ d', insertAfterLookup P key (hf key) value ix none d = (.ok (), d') ∧
      DictInv hf eqv P.isStr d' ∧ dictAssoc d' = dictAssoc d ++ [(key, value)] := by
  have hlist : dictAssoc d = (live k v).map (fun e => (e.key, e.value)) :=
    dictAssoc_split d k v hb w
  have hno : ∀ e ∈ live k v, eqv e.key key = false := by
    intro e he
    rw [hlist] at habs
    simp only [assocGet, Option.map_eq_none_iff] at habs
    have := List.find?_eq_none.mp habs (e.key, e.value) (List.mem_map.mpr ⟨e, he, rfl⟩)
    simpa using this
  have hU : d.body.isUnicode = true := by simp [Body.isUnicode, Body.kind, hb, w.kind]
  have finish : ∀ (k' : Keys K V), WF hf eqv P.isStr k' → liveEntries k' = live k v → 0 < k'.usable →
      (k'.kind ≠ .general → P.isStr key = true) →
      ∃ k'' : Keys K V, appendEntry k' key (hf key) value = .ok k'' ∧ WF hf eqv P.isStr k'' ∧
        liveEntries k'' = live k v ++ [⟨key, hf key, value⟩] := by
    intro k' w' hl hus hstr
    obtain ⟨k'', h1, h2, h3, _, _⟩ := appendEntry_spec H k' w' hus key value
      (fun i e h => hno e (hl ▸ (mem_live k' e).mpr ⟨i, h⟩)) hstr
    exact ⟨k'', h1, h2, by rw [h3, hl]⟩
  have result : ∀ (k'' : Keys K V) (n : Nat), WF hf eqv P.isStr k'' →
      liveEntries k'' = live k v ++ [⟨key, hf key, value⟩] →
      DictInv hf eqv P.isStr { d with nextId := n, used := d.used + 1, body := .combined k'' } ∧
      dictAssoc ({ d with nextId := n, used := d.used + 1, body := .combined k'' } : PyDict K V) =
        dictAssoc d ++ [(key, value)] := by
    intro k'' n w'' hl
    constructor
    · refine ⟨⟨k'', rfl, w'', ?_⟩⟩
      rw [hl]
      simp [live_length w]
    · rw [hlist]
      simp [dictAssoc, Keys.items, hl]
  simp only [insertAfterLookup, insertCombinedDict]
  rcases hroute with hs | ⟨hs, hus⟩
  · have hc : (d.body.isUnicode && !P.toKeyOps.isStr key) = true := by
      have : P.toKeyOps.isStr key = false := hs
      simp [hU, this]
    rcases insertionResize_split H d k v hb w false with ⟨hbig, h⟩ | ⟨k', h1, h2, h3, h4, h5⟩
    · left
      refine ⟨hbig, ?_⟩
      simp only [hc, if_true, h]
    · have hgen := h5 rfl
      obtain ⟨k'', h6, h7, h8⟩ := finish k' h2 h3 h4 (fun h => absurd hgen h)
      have hus' : ¬ (({ d with nextId := d.nextId + 1, body := .combined k' } : PyDict K V).body.usable ≤ 0) := by
        simp only [Body.usable]
        omega
      right
      obtain ⟨g1, g2⟩ := result k'' (d.nextId + 1) h7 h8
      refine ⟨_, ?_, g1, g2⟩
      simp only [hc, if_true, h1]
      rw [if_neg hus']
      simp [h6]
  · have hc : (d.body.isUnicode && !P.toKeyOps.isStr key) = false := by
      have : P.toKeyOps.isStr key = true := hs
      simp [this]
    have huse : d.body.usable ≤ 0 := by simpa [Body.usable, hb] using hus
    rcases insertionResize_split H d k v hb w true with ⟨hbig, h⟩ | ⟨k', h1, h2, h3, h4, _⟩
    · left
      refine ⟨hbig, ?_⟩
      simp only [hc, Bool.false_eq_true, if_false]
      rw [if_pos huse, h]
    · obtain ⟨k'', h6, h7, h8⟩ := finish k' h2 h3 h4 (fun _ => hs)
      right
      obtain ⟨g1, g2⟩ := result k'' (d.nextId + 1) h7 h8
      refine ⟨_, ?_, g1, g2⟩
      simp only [hc, Bool.false_eq_true, if_false]
      rw [if_pos huse, h1]
      simp [h6]

end New

section Insert
variable {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}

theorem entry_lt {W : Type} (k : Keys K W) (ix : Nat) (e : Ent K W) (h : k.entry ix = some e) :
    ix < k.nentries :=
  (List.getElem?_eq_some_iff.mp ((entry_iff k ix e).mp h)).1

theorem cmpU (H : Honest P hf eqv) (ek : K) (eh : Int) (hh : eh = hf ek) (key : K)
    (hs : P.isStr key = true) (hstr : P.isStr ek = true) :
    compareUnicodeUnicode P (some (ek, eh)) key (hf key) = eqv ek key := by
  simp only [compareUnicodeUnicode]
  by_cases h1 : ek = key
  · subst h1
    simp [H.refl]
  · by_cases h2 : eh = hf key
    · simp [h1, h2, H.str_eq _ _ hstr hs]
    · have hne : eqv ek key = false := by
        cases hq : eqv ek key with
        | false => rfl
        | true => exact absurd (hh.trans (H.hash_cons _ _ hq)) h2
      simp [h1, h2, hne]

/-- `unicodekeys_lookup_unicode` on shared keys, found. -/
theorem lookupUnicode_found (H : Honest P hf eqv) (k : Keys K Unit) (c : Core hf eqv P.isStr k)
    (hk : k.kind = .split) (key : K) (hs : P.isStr key = true) (ix : Nat) (e : Ent K Unit)
    (he : k.entry ix = some e) (heq : eqv e.key key = true) :
    unicodekeysLookupUnicode P k key (hf key) = .ok (ix : Int) := by
  have h := search_found (P := P) (σ := Unit) k c H (fun _ i => k.getIndex i)
    (fun ix => pure (if compareUnicodeUnicode P ((k.entry ix).map fun e => (e.key, e.hash)) key (hf key)
      then 1 else 0)) () key (fun _ => rfl)
    (fun t e' h' => by
      simp only [h', Option.map_some]
      rw [cmpU H e'.key e'.hash (c.hashes t e' h') key hs (c.strs t e' (by simp [hk]) h')]
      rfl) ix e he heq
  simp only [unicodekeysLookupUnicode, h]

theorem lookupUnicode_missing (H : Honest P hf eqv) (k : Keys K Unit) (c : Core hf eqv P.isStr k)
    (hk : k.kind = .split) (key : K) (hs : P.isStr key = true)
    (hno : ∀ ix e, k.entry ix = some e → eqv e.key key = false) :
    unicodekeysLookupUnicode P k key (hf key) = .ok DKIX_EMPTY := by
  have h := search_missing (P := P) (σ := Unit) k c (fun _ i => k.getIndex i)
    (fun ix => pure (if compareUnicodeUnicode P ((k.entry ix).map fun e => (e.key, e.hash)) key (hf key)
      then 1 else 0)) () key (fun _ => rfl)
    (fun t e' h' => by
      simp only [h', Option.map_some]
      rw [cmpU H e'.key e'.hash (c.hashes t e' h') key hs (c.strs t e' (by simp [hk]) h')]
      rfl) hno
  simp only [unicodekeysLookupUnicode, h]

omit [DecidableEq K] in
theorem insertSplitValue_none (mp : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : mp.body = .split k v) (value : V) (ix : Nat) (hv : v.get ix = none) :
    insertSplitValue (K := K) value ix mp =
      (.ok (), { mp with
        used := mp.used + 1
        body := .split k ((v.set ix (some value)).addToOrder ix) }) := by
  simp [insertSplitValue, M.bind_run, hb, hv]

omit [DecidableEq K] in
theorem insertSplitValue_some (mp : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : mp.body = .split k v) (value y : V) (ix : Nat) (hv : v.get ix = some y) :
    insertSplitValue (K := K) value ix mp =
      (.ok (), { mp with body := .split k (v.set ix (some value)) }) := by
  simp [insertSplitValue, M.bind_run, hb, hv]

/-- `insertdict` on a split dict. The result is split while the store can stay in the table, and
combined otherwise; `MemoryError` changes nothing. The list is `assocSet`'s up to the object of a
key: an exact str that matches a shared key leaves the shared key. -/
theorem insertDict_split (H : Honest P hf eqv) (d : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : d.body = .split k v) (w : SplitWF hf eqv P.isStr k v d.used) (key : K) (value : V) :
    (TooBig d.used ∧ insertDict P key (hf key) value d = (.error memoryError, d)) ∨
    ∃ d', insertDict P key (hf key) value d = (.ok (), d') ∧
      (SplitInv hf eqv P.isStr d' ∨ DictInv hf eqv P.isStr d') ∧
      AssocEq eqv (dictAssoc d') (assocSet eqv (dictAssoc d) key value) := by
  have hself : ({ d with body := .split k v } : PyDict K V) = d := by
    cases d
    simp_all
  have hsetAbs : ∀ h : assocGet eqv (dictAssoc d) key = none,
      assocSet eqv (dictAssoc d) key value = dictAssoc d ++ [(key, value)] := by
    intro h
    simp [assocSet, any_of_assocGet_none _ _ h]
  have viaNew : ∀ (ix : Int), assocGet eqv (dictAssoc d) key = none →
      (P.isStr key = false ∨ (P.isStr key = true ∧ k.usable ≤ 0)) →
      ((TooBig d.used ∧ insertAfterLookup P key (hf key) value ix none d = (.error memoryError, d)) ∨
      ∃ d', insertAfterLookup P key (hf key) value ix none d = (.ok (), d') ∧
        (SplitInv hf eqv P.isStr d' ∨ DictInv hf eqv P.isStr d') ∧
        AssocEq eqv (dictAssoc d') (assocSet eqv (dictAssoc d) key value)) := by
    intro ix hn hr
    rcases insertNew_split H d k v hb w key value ix hn hr with h | ⟨d', h1, h2, h3⟩
    · exact Or.inl h
    · refine Or.inr ⟨d', h1, Or.inr h2, ?_⟩
      rw [h3, hsetAbs hn]
      exact AssocEq.refl H.refl _
  rcases dichotomy (eqv := eqv) k key with ⟨ix, e, he, heq⟩ | hno
  · have hlook : dictLookup P key (hf key) d = (.ok ((ix : Int), v.get ix), d) :=
      lookupAux_split_found H d k v hb w.core w.kind key ix e he heq 255
    have hget := assocGet_split_found d k v hb w H key ix e he heq
    by_cases hs : P.isStr key = true
    · have hl := lookupUnicode_found H k w.core w.kind key hs ix e he heq
      have h1 : ((ix : Int) == DKIX_EMPTY) = false := by simp [DKIX_EMPTY]
      have h2 : ((ix : Int) != DKIX_EMPTY) = true := by simp [DKIX_EMPTY]
      have hkey : insertSplitKey P k key (hf key) = .ok ((ix : Int), k) := by
        simp [insertSplitKey, hl, h1]
      have hI : insertDict P key (hf key) value d = insertSplitValue value ix d := by
        simp only [insertDict, hb, hs, if_true, hkey, h2, hself]
        rfl
      rw [hI]
      cases hv : v.get ix with
      | none =>
        right
        obtain ⟨g1, g2⟩ := split_new (P := P) d k k v hb w w.core w.kind w.notEmpty w.small w.entries w.cap
          w.nent (Nat.le_refl _) (fun _ _ h => h) ix e (entry_lt k ix e he) he hv value
        refine ⟨_, insertSplitValue_none d k v hb value ix hv, Or.inl g1, ?_⟩
        rw [g2, hsetAbs (by rw [hget, hv])]
        exact AssocEq.append_last H.refl _ _ _ _ heq
      | some y =>
        right
        obtain ⟨g1, g2⟩ := split_store H d k v hb w key ix e he heq y value hv
        refine ⟨_, insertSplitValue_some d k v hb value y ix hv, Or.inl g1, ?_⟩
        rw [g2]
        exact AssocEq.refl H.refl _
    · have hs' : P.isStr key = false := by simpa using hs
      have hI : insertDict P key (hf key) value d =
          insertAfterLookup P key (hf key) value ix (v.get ix) d := by
        simp only [insertDict, hb, hs', Bool.false_eq_true, if_false, hlook]
      rw [hI]
      cases hv : v.get ix with
      | none => exact viaNew _ (by rw [hget, hv]) (Or.inl hs')
      | some y =>
        right
        obtain ⟨g1, g2⟩ := split_store H d k v hb w key ix e he heq y value hv
        refine ⟨_, ?_, Or.inl g1, ?_⟩
        · simp [insertAfterLookup, storeValue, hb]
        · rw [g2]
          exact AssocEq.refl H.refl _
  · have hnone := assocGet_split_none d k v hb w key hno
    by_cases hs : P.isStr key = true
    · have hl := lookupUnicode_missing H k w.core w.kind key hs hno
      by_cases hus : k.usable ≤ 0
      · have h1 : decide (k.usable > 0) = false := by simp; omega
        have hkey : insertSplitKey P k key (hf key) = .ok (DKIX_EMPTY, k) := by
          simp [insertSplitKey, hl, h1]
        have hI : insertDict P key (hf key) value d =
            insertAfterLookup P key (hf key) value DKIX_EMPTY none d := by
          simp only [insertDict, hb, hs, if_true, hkey, bne_self_eq_false, Bool.false_eq_true,
            if_false, hself]
        rw [hI]
        exact viaNew _ hnone (Or.inr ⟨hs, hus⟩)
      · have hpos : 0 < k.usable := by omega
        obtain ⟨k', h1, c', hkind, hn, hu, hsz, hlog, hold, hnew⟩ :=
          appendEntry_core H k w.core hpos key () hno (fun _ => hs)
        have h2 : decide (k.usable > 0) = true := by simp; omega
        have hkey : insertSplitKey P k key (hf key) = .ok ((k.nentries : Int), k') := by
          simp [insertSplitKey, hl, h2, h1]
        have h3 : ((k.nentries : Int) != DKIX_EMPTY) = true := by simp [DKIX_EMPTY]
        have hv : v.get k.nentries = none := w.high _ (Nat.le_refl _)
        have hb' : ({ d with body := .split k' v } : PyDict K V).body = .split k' v := rfl
        have hI : insertDict P key (hf key) value d =
            insertSplitValue value k.nentries { d with body := .split k' v } := by
          simp only [insertDict, hb, hs, if_true, hkey, h3]
          rfl
        have hent' : ∀ ix, ix < k'.nentries → ∃ e, k'.entry ix = some e := by
          intro ix hix
          by_cases hlt : ix < k.nentries
          · obtain ⟨e, he⟩ := w.entries ix hlt
            exact ⟨e, hold ix e he⟩
          · have : ix = k.nentries := by omega
            exact ⟨_, this ▸ hnew⟩
        obtain ⟨g1, g2⟩ := split_new (P := P) d k k' v hb w c' (hkind.trans w.kind) (hlog ▸ w.notEmpty)
          (hlog ▸ w.small) hent' (by rw [hn, hu]; have := w.cap; omega) (by rw [hn, hu, hsz]; have := w.nent; omega)
          (by omega) hold k.nentries ⟨key, hf key, ()⟩ (by omega) hnew hv value
        right
        rw [hI]
        refine ⟨_, insertSplitValue_none _ k' v hb' value _ hv, Or.inl g1, ?_⟩
        rw [g2, hsetAbs hnone]
        exact AssocEq.refl H.refl _
    · have hs' : P.isStr key = false := by simpa using hs
      have hlook : dictLookup P key (hf key) d = (.ok (DKIX_EMPTY, none), d) :=
        lookupAux_split_missing H d k v hb w.core w.kind key hno 255
      have hI : insertDict P key (hf key) value d =
          insertAfterLookup P key (hf key) value DKIX_EMPTY none d := by
        simp only [insertDict, hb, hs', Bool.false_eq_true, if_false, hlook]
      rw [hI]
      exact viaNew _ hnone (Or.inl hs')

end Insert

section Delete
variable {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}

omit [DecidableEq K] in
theorem pairs_erase (k : Keys K Unit) (v : Values V) (key : K) (ix : Nat) (e : Ent K Unit)
    (he : k.entry ix = some e) (heq : eqv e.key key = true)
    (huniq : ∀ i e', k.entry i = some e' → eqv e'.key key = true → i = ix) :
    ∀ order : List Nat, order.Nodup → (∀ j ∈ order, (v.get j).isSome = true) →
      ((order.erase ix).filterMap (slot k (v.set ix none))).map (fun e => (e.key, e.value)) =
        ((order.filterMap (slot k v)).map (fun e => (e.key, e.value))).filter
          (fun p => !eqv p.1 key) := by
  intro order
  induction order with
  | nil => intro _ _; rfl
  | cons a t ih =>
    intro hn hm
    have hn' := List.nodup_cons.mp hn
    have hrest := ih hn'.2 (fun j hj => hm j (by simp [hj]))
    by_cases ha : a = ix
    · subst ha
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hm a (by simp))
      have h2 : slot k v a = some ⟨e.key, e.hash, y⟩ := by simp [slot, he, hy]
      rw [List.erase_of_not_mem hn'.1] at hrest
      simp [List.filterMap_cons, h2, heq, hrest]
    · have hne : ¬ (a == ix) = true := by simpa using ha
      rw [List.erase_cons_tail hne]
      have h1 : slot k (v.set ix none) a = slot k v a := by
        simp only [slot, v.get_set_ne ix a none ha]
      simp only [List.filterMap_cons, h1]
      cases hs : slot k v a with
      | none => simpa using hrest
      | some y =>
        obtain ⟨e0, z, h3, _, rfl⟩ := slot_some hs
        have hn0 : eqv e0.key key = false := by
          cases hq : eqv e0.key key with
          | false => rfl
          | true => exact absurd (huniq a e0 h3 hq) ha
        simp [hn0, hrest]

/-- `delitem_common` on a split table: the value goes, the slot leaves the order array, and the
shared keys are untouched, so the key stays there with no value. That is how the state the
setdefault crash needs arises from a plain `del`. -/
theorem split_del (H : Honest P hf eqv) (d : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : d.body = .split k v) (w : SplitWF hf eqv P.isStr k v d.used) (key : K) (ix : Nat)
    (e : Ent K Unit) (he : k.entry ix = some e) (heq : eqv e.key key = true) (y : V)
    (hy : v.get ix = some y) :
    let d' : PyDict K V :=
      { d with used := d.used - 1, body := .split k ((v.set ix none).deleteIndex ix) }
    SplitInv hf eqv P.isStr d' ∧ dictAssoc d' = assocDel eqv (dictAssoc d) key := by
  intro d'
  have hcap := v.lt_capacity ix y hy
  have hmem : ix ∈ v.order := (w.order ix).mpr ⟨entry_lt k ix e he, by simp [hy]⟩
  have huniq : ∀ i e', k.entry i = some e' → eqv e'.key key = true → i = ix := by
    intro i e' h1 h2
    exact w.core.uniq i e' ix e h1 he (H.trans _ key _ h2 (by rw [H.symm]; exact heq))
  let v' := (v.set ix none).deleteIndex ix
  have hget : ∀ j, v'.get j = (v.set ix none).get j := fun _ => rfl
  have horder : v'.order = v.order.erase ix := rfl
  have hw : SplitWF hf eqv P.isStr k v' (d.used - 1) :=
    { core := w.core, kind := w.kind, notEmpty := w.notEmpty, small := w.small, entries := w.entries
      cap := by
        have h1 : v'.capacity = v.capacity := by
          simp [v', Values.capacity, Values.deleteIndex, Values.set]
        rw [h1]
        exact w.cap
      nent := w.nent
      nodup := by
        rw [horder]
        exact List.Nodup.erase _ w.nodup
      order := fun j => by
        rw [horder, List.Nodup.mem_erase_iff w.nodup, hget]
        by_cases hj : j = ix
        · subst hj
          simp [v.get_set_self j none hcap]
        · rw [v.get_set_ne ix j none hj]
          simp only [ne_eq, hj, not_false_eq_true, true_and]
          exact w.order j
      high := fun j hj => by
        have hne : j ≠ ix := by
          have := entry_lt k ix e he
          omega
        rw [hget, v.get_set_ne ix j none hne]
        exact w.high j hj
      used := by
        rw [horder, List.length_erase_of_mem hmem, w.used] }
  refine ⟨⟨k, v', rfl, hw⟩, ?_⟩
  have hl := dictAssoc_split (hf := hf) (isStr := P.isStr) d' k v' rfl hw
  rw [hl, dictAssoc_split d k v hb w, assocDel]
  have hfilter : v'.order.filterMap (slot k v') =
      (v.order.erase ix).filterMap (slot k (v.set ix none)) := by
    rw [horder]
    rfl
  rw [hfilter]
  exact pairs_erase k v key ix e he heq huniq v.order w.nodup (fun j hj => ((w.order j).mp hj).2)

/-- `del d[key]` on a split dict. -/
theorem dictDelItem_split (H : Honest P hf eqv) (d : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : d.body = .split k v) (w : SplitWF hf eqv P.isStr k v d.used) (key : K) :
    (assocGet eqv (dictAssoc d) key = none ∧ dictDelItem P key d = (.error (keyErr P key), d)) ∨
    ∃ d', dictDelItem P key d = (.ok (), d') ∧ SplitInv hf eqv P.isStr d' ∧
      dictAssoc d' = assocDel eqv (dictAssoc d) key := by
  have hkh : dictDelItem P key d = dictDelItemKnownHash P key (hf key) d := by
    simp only [dictDelItem, H.hash_ok]
  rw [hkh]
  rcases dichotomy (eqv := eqv) k key with ⟨ix, e, he, heq⟩ | hno
  · have hlook : dictLookup P key (hf key) d = (.ok ((ix : Int), v.get ix), d) :=
      lookupAux_split_found H d k v hb w.core w.kind key ix e he heq 255
    have hget := assocGet_split_found d k v hb w H key ix e he heq
    cases hv : v.get ix with
    | none =>
      left
      refine ⟨by rw [hget, hv], ?_⟩
      simp [dictDelItemKnownHash, hlook, hv]
    | some y =>
      right
      obtain ⟨g1, g2⟩ := split_del H d k v hb w key ix e he heq y hv
      refine ⟨_, ?_, g1, g2⟩
      have hhash : e.hash = hf key := (w.core.hashes ix e he).trans (H.hash_cons _ _ heq)
      obtain ⟨s, _, _, hs⟩ := lookdictIndex_spec k w.core.toChain ix e he
      rw [hhash] at hs
      have h1 : ((ix : Int) == DKIX_EMPTY) = false := by simp [DKIX_EMPTY]
      simp [dictDelItemKnownHash, hlook, hv, h1, delitemCommon, hb, hs]
  · left
    have hlook : dictLookup P key (hf key) d = (.ok (DKIX_EMPTY, none), d) :=
      lookupAux_split_missing H d k v hb w.core w.kind key hno 255
    refine ⟨assocGet_split_none d k v hb w key hno, ?_⟩
    simp [dictDelItemKnownHash, hlook]

end Delete

section Rest
variable {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}

omit [DecidableEq K] in
theorem nodup_length_le : ∀ (n : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < n) → l.length ≤ n := by
  intro n
  induction n with
  | zero =>
    intro l _ h
    cases l with
    | nil => simp
    | cons a t => exact absurd (h a (by simp)) (by omega)
  | succ n ih =>
    intro l hn h
    by_cases hm : n ∈ l
    · have := ih (l.erase n) (List.Nodup.erase _ hn) (fun x hx => by
        have h1 := (List.Nodup.mem_erase_iff hn).mp hx
        have := h x h1.2
        omega)
      rw [List.length_erase_of_mem hm] at this
      omega
    · have := ih l hn (fun x hx => by
        have h1 := h x hx
        have : x ≠ n := fun e => hm (e ▸ hx)
        omega)
      omega

/-- `dict.popitem` on a split dict goes through a resize of the same size, so the last item of the
list is the one that was inserted last, not the last shared key. -/
theorem dictPopitem_split (H : Honest P hf eqv) (d : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : d.body = .split k v) (w : SplitWF hf eqv P.isStr k v d.used) :
    (dictAssoc d = [] ∧
      dictPopitem d = (.error (.keyError "'popitem(): dictionary is empty'"), d)) ∨
    ∃ p d', dictPopitem d = (.ok p, d') ∧ DictInv hf eqv P.isStr d' ∧
      dictAssoc d = dictAssoc d' ++ [p] := by
  have hlist : dictAssoc d = (live k v).map (fun e => (e.key, e.value)) :=
    dictAssoc_split d k v hb w
  by_cases h0 : d.used = 0
  · left
    have hnil : live k v = [] := List.length_eq_zero_iff.mp ((live_length w).trans h0)
    refine ⟨by simp [hlist, hnil], ?_⟩
    simp [dictPopitem, h0]
  · right
    have hle : d.used ≤ k.nentries := by
      rw [w.used]
      exact nodup_length_le _ _ w.nodup (fun x hx => ((w.order x).mp hx).1)
    have hroom : d.used ≤ usableFraction (2 ^ k.log2Size) := by
      have h1 := w.nent
      have h2 := w.core.usableNN
      have : k.size = 2 ^ k.log2Size := rfl
      rw [this] at h1
      omega
    obtain ⟨k', h1, h2, h3, _, _, _⟩ := dictResize_split H d k v hb w k.log2Size w.small hroom true
    let d1 : PyDict K V := { d with nextId := d.nextId + 1, body := .combined k' }
    have hd1 : DictInv hf eqv P.isStr d1 :=
      ⟨⟨k', rfl, h2, by simp only [d1]; rw [h3, live_length w]⟩⟩
    have ha : dictAssoc d1 = dictAssoc d := by
      rw [hlist]
      simp [dictAssoc, d1, Keys.items, h3]
    have hlog : d.body.log2Size = k.log2Size := by simp [Body.log2Size, hb]
    have hn0 : (d.used == 0) = false := by simpa using h0
    have hs : dictPopitem d = popLast k' d1 := by
      simp only [dictPopitem, hn0, Bool.false_eq_true, if_false, hb]
      have : dictResize (Body.split k v : Body K V).log2Size true d = (.ok (), d1) := h1
      simp only [this]
      rfl
    have hc : dictPopitem d1 = popLast k' d1 := by
      have : (d1.used == 0) = false := hn0
      simp only [dictPopitem, this, Bool.false_eq_true, if_false]
      rfl
    rcases dictPopitem_spec H d1 hd1 with ⟨h4, _⟩ | ⟨p, d', h4, h5, h6⟩
    · exfalso
      rw [ha, hlist] at h4
      have : (live k v).length = 0 := by simpa using congrArg List.length h4
      exact h0 ((live_length w).symm.trans this)
    · refine ⟨p, d', by rw [hs, ← hc]; exact h4, h5, ?_⟩
      rw [← ha]
      exact h6

omit [DecidableEq K] in
theorem clearEmbedded_get (v : Values V) (n j : Nat) :
    (clearEmbeddedValues v n).get j = if j < n then none else v.get j := by
  simp only [clearEmbeddedValues, Values.get, List.getElem?_map, List.getElem?_zipIdx]
  cases hg : v.values[j]? <;> by_cases hj : j < n <;> simp [hj]

/-- `dict.clear` on a split dict: embedded values stay in place and empty, which keeps the dict
split, and a dict with its own values goes back to the empty keys. -/
theorem dictClear_split (d : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : d.body = .split k v) (w : SplitWF hf eqv isStr k v d.used) :
    (SplitInv hf eqv isStr (dictClear d) ∨ DictInv hf eqv isStr (dictClear d)) ∧
      dictAssoc (dictClear d) = [] := by
  have hne : d.body.isEmptyKeys = false := by
    have := w.notEmpty
    simp only [Body.isEmptyKeys, Body.log2Size, hb, beq_eq_false_iff_ne]
    omega
  have hne' : (Body.split k v : Body K V).isEmptyKeys = false := by rw [← hb]; exact hne
  by_cases he : v.embedded = true
  · have hc : dictClear d =
        { d with used := 0, body := .split k (clearEmbeddedValues v k.nentries) } := by
      simp [dictClear, hne', hb, he]
    have hw : SplitWF hf eqv isStr k (clearEmbeddedValues v k.nentries) 0 :=
      { core := w.core, kind := w.kind, notEmpty := w.notEmpty, small := w.small, entries := w.entries
        cap := by
          have : (clearEmbeddedValues v k.nentries).capacity = v.capacity := by
            simp [clearEmbeddedValues, Values.capacity]
          rw [this]
          exact w.cap
        nent := w.nent
        nodup := by simp [clearEmbeddedValues]
        order := fun j => by
          simp only [clearEmbeddedValues, List.not_mem_nil, false_iff]
          have hg := clearEmbedded_get v k.nentries j
          simp only [clearEmbeddedValues] at hg
          rw [hg]
          intro ⟨h1, h2⟩
          simp [h1] at h2
        high := fun j hj => by
          rw [clearEmbedded_get, if_neg (by omega)]
          exact w.high j hj
        used := by simp [clearEmbeddedValues] }
    rw [hc]
    refine ⟨Or.inl ⟨k, _, rfl, hw⟩, ?_⟩
    simp [dictAssoc, splitLive_eq, clearEmbeddedValues]
  · have hc : dictClear d = { d with used := 0, body := .combined emptyKeys } := by
      simp [dictClear, hne', hb, he]
    rw [hc]
    constructor
    · exact Or.inr ⟨⟨emptyKeys, rfl, wf_empty hf eqv isStr, by simp [liveEntries, emptyKeys]⟩⟩
    · simp [dictAssoc, Keys.items, liveEntries, emptyKeys]

omit [DecidableEq K] in
/-- `_PyDict_Next` on a split dict walks the insertion-order array. -/
theorem dictNextAll_split (d : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : d.body = .split k v) (w : SplitWF hf eqv isStr k v d.used) :
    ∀ (fuel i : Nat), d.used < i + fuel →
      dictNextAll d fuel (i : Int) =
        ((v.order.drop i).filterMap (slot k v)).map fun e => (e.key, e.value, e.hash) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i h
    have hd : v.order.drop i = [] := List.drop_eq_nil_of_le (by rw [← w.used]; omega)
    simp [dictNextAll, hd]
  | succ fuel ih =>
    intro i h
    simp only [dictNextAll]
    by_cases hi : i < d.used
    · have hlen : i < v.order.length := by rw [← w.used]; exact hi
      have hmem : v.order[i] ∈ v.order := List.getElem_mem hlen
      obtain ⟨e0, x, h1, h2, h3⟩ := slot_of_order w hmem
      have hidx : v.indexFromOrder i = v.order[i] := by
        simp [Values.indexFromOrder, List.getD, hlen]
      have hnext : dictNext d (i : Int) = some ((i : Int) + 1, e0.key, x, e0.hash) := by
        simp only [dictNext, hb]
        rw [if_neg (by omega)]
        simp [hidx, h1, h2]
      simp only [hnext]
      have hdrop : v.order.drop i = v.order[i] :: v.order.drop (i + 1) :=
        List.drop_eq_getElem_cons hlen
      have hc : ((i : Int) + 1) = ((i + 1 : Nat) : Int) := by omega
      rw [hdrop, hc, ih (i + 1) (by omega)]
      simp only [List.filterMap_cons, h3, List.map_cons]
    · have hnext : dictNext d (i : Int) = none := by
        simp only [dictNext, hb]
        rw [if_pos (by omega)]
      have hd : v.order.drop i = [] := List.drop_eq_nil_of_le (by rw [← w.used]; omega)
      rw [hnext]
      simp [hd]

omit [DecidableEq K] in
/-- Every full iteration of a split dict gives the list, in the order of the order array. -/
theorem dictItems_split (d : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : d.body = .split k v) (w : SplitWF hf eqv isStr k v d.used) :
    dictItems d = (live k v).map fun e => (e.key, e.value, e.hash) := by
  have h := dictNextAll_split d k v hb w (d.body.nentries + d.used + 1) 0 (by omega)
  simpa [dictItems, live] using h

theorem dictSetItem_split (H : Honest P hf eqv) (d : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : d.body = .split k v) (w : SplitWF hf eqv P.isStr k v d.used) (key : K) (value : V) :
    dictSetItem P key value d = insertDict P key (hf key) value d := by
  have hne : d.body.isEmptyKeys = false := by
    have := w.notEmpty
    simp only [Body.isEmptyKeys, Body.log2Size, hb, beq_eq_false_iff_ne]
    omega
  simp [dictSetItem, H.hash_ok, hne]

end Rest

/-- A split dict refines the association list as a combined one does. Under the contract of
`__hash__` and `__eq__`, and for a key of any kind: the lookup agrees with the list; `d[key] = v`
keeps the invariant, split or combined, and does what `assocSet` does, up to the object of a key
equal to a shared one; `del d[key]`, `popitem` and `clear` do what the list does; and a full
iteration gives the list. -/
def SplitRefines : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ d : PyDict K V, SplitInv hf eqv P.isStr d → ∀ (key : K) (value : V),
      (∃ ix, dictLookup P key (hf key) d = (.ok (ix, assocGet eqv (dictAssoc d) key), d)) ∧
      ((TooBig d.used ∧ dictSetItem P key value d = (.error memoryError, d)) ∨
        ∃ d', dictSetItem P key value d = (.ok (), d') ∧
          (SplitInv hf eqv P.isStr d' ∨ DictInv hf eqv P.isStr d') ∧
          AssocEq eqv (dictAssoc d') (assocSet eqv (dictAssoc d) key value)) ∧
      ((assocGet eqv (dictAssoc d) key = none ∧ dictDelItem P key d = (.error (keyErr P key), d)) ∨
        ∃ d', dictDelItem P key d = (.ok (), d') ∧ SplitInv hf eqv P.isStr d' ∧
          dictAssoc d' = assocDel eqv (dictAssoc d) key) ∧
      ((dictAssoc d = [] ∧
          dictPopitem d = (.error (.keyError "'popitem(): dictionary is empty'"), d)) ∨
        ∃ p d', dictPopitem d = (.ok p, d') ∧ DictInv hf eqv P.isStr d' ∧
          dictAssoc d = dictAssoc d' ++ [p]) ∧
      ((SplitInv hf eqv P.isStr (dictClear d) ∨ DictInv hf eqv P.isStr (dictClear d)) ∧
        dictAssoc (dictClear d) = []) ∧
      (dictItems d).map (fun e => (e.1, e.2.1)) = dictAssoc d

theorem splitRefines_proven : SplitRefines := by
  intro K V _ P hf eqv H d hd key value
  obtain ⟨k, v, hb, w⟩ := hd
  refine ⟨lookup_split H d k v hb w key, ?_, dictDelItem_split H d k v hb w key,
    dictPopitem_split H d k v hb w, dictClear_split d k v hb w, ?_⟩
  · rw [dictSetItem_split H d k v hb w]
    exact insertDict_split H d k v hb w key value
  · rw [dictItems_split d k v hb w, dictAssoc_split d k v hb w]
    simp [live, Function.comp_def]

/-- Keys a `new_dict_with_shared_keys` can be given: well formed, shared, not `Py_EMPTY_KEYS`, and
with no hole in `dk_entries`, since shared keys are never deleted. -/
structure SharedOK (hf : K → Int) (eqv : K → K → Bool) (isStr : K → Bool) (k : Keys K Unit) :
    Prop where
  core : Core hf eqv isStr k
  kind : k.kind = .split
  notEmpty : 0 < k.log2Size
  small : k.log2Size < 64
  entries : ∀ ix, ix < k.nentries → ∃ e, k.entry ix = some e
  nent : (k.nentries : Int) + k.usable ≤ usableFraction k.size

section Fresh
variable {hf : K → Int} {eqv : K → K → Bool} {isStr : K → Bool}

omit [DecidableEq K] in
theorem newValues_get (n j : Nat) : (Values.new n : Values V).get j = none := by
  simp only [Values.get, Values.new]
  by_cases hj : j < n <;> simp [List.getElem?_replicate, hj]

/-- `new_values` of `shared_keys_usable_size` slots, all `NULL`, makes a well-formed split dict of no
items on any shared keys. -/
theorem newValues_wf {k : Keys K Unit} (w : SharedOK hf eqv isStr k) :
    SplitWF hf eqv isStr k (Values.new (sharedKeysUsableSize k) : Values V) 0 :=
  { core := w.core
    kind := w.kind
    notEmpty := w.notEmpty
    small := w.small
    entries := w.entries
    cap := by
      have h0 := w.core.usableNN
      have h1 : (Values.new (sharedKeysUsableSize k) : Values V).capacity =
          sharedKeysUsableSize k := by
        simp [Values.capacity, Values.new]
      rw [h1]
      simp only [sharedKeysUsableSize, Keys.nentries]
      omega
    nent := w.nent
    nodup := by simp [Values.new]
    order := fun j => by
      constructor
      · intro h
        simp [Values.new] at h
      · rintro ⟨_, h2⟩
        rw [newValues_get] at h2
        simp at h2
    high := fun j _ => newValues_get _ j
    used := by simp [Values.new] }

/-- The empty table `_PyDict_NewKeysForClass` starts from (:6792-6802). -/
def sharedKeys0 (K : Type) : Keys K Unit :=
  { (newKeysObject 1 NEXT_LOG2_SHARED_KEYS_MAX_SIZE true : Keys K Unit) with
    usable := SHARED_KEYS_MAX_SIZE, kind := .split }

theorem sharedOK_keys0 : SharedOK hf eqv isStr (sharedKeys0 K) := by
  let k : Keys K Unit := sharedKeys0 K
  have hc := chain_new (K := K) (V := Unit) 1 NEXT_LOG2_SHARED_KEYS_MAX_SIZE true
  have hnone : ∀ ix (e : Ent K Unit), k.entry ix = some e → False := by
    intro ix e h
    simp [k, sharedKeys0, Keys.entry, newKeysObject] at h
  have hn : k.nentries = 0 := by
    simp [k, sharedKeys0, Keys.nentries, newKeysObject]
  have hfilled : k.filled = 0 := by
    simp [k, sharedKeys0, Keys.filled, newKeysObject, List.countP_replicate, DKIX_EMPTY]
  have hus : k.usable = SHARED_KEYS_MAX_SIZE := rfl
  have hsz : k.size = 2 ^ NEXT_LOG2_SHARED_KEYS_MAX_SIZE := rfl
  have hlog : k.log2Size = NEXT_LOG2_SHARED_KEYS_MAX_SIZE := rfl
  exact
    { core :=
        { toChain := ⟨hc.len, hc.range, hc.inj, hc.reach⟩
          hashes := fun ix e h => (hnone ix e h).elim
          uniq := fun i _ _ _ h _ _ => (hnone i _ h).elim
          strs := fun ix e _ h => (hnone ix e h).elim
          load := by rw [hfilled, hus, hsz]; decide
          usableNN := by rw [hus]; decide }
      kind := rfl
      notEmpty := by rw [hlog]; decide
      small := by rw [hlog]; decide
      entries := fun ix hix => by
        rw [hn] at hix
        omega
      nent := by rw [hn, hus, hsz]; decide }

variable {V : Type} {P : Proto K (PyDict K V)}

/-- `insert_split_key` keeps keys fit for a new dict: found, or full, it leaves them; otherwise it
appends one more. -/
theorem sharedOK_insert (H : Honest P hf eqv) {k k' : Keys K Unit} (w : SharedOK hf eqv P.isStr k)
    (key : K) (hs : P.isStr key = true) (ix : Int)
    (h : insertSplitKey P k key (hf key) = .ok (ix, k')) : SharedOK hf eqv P.isStr k' := by
  rcases dichotomy (eqv := eqv) k key with ⟨jx, e, he, heq⟩ | hno
  · have hl := lookupUnicode_found H k w.core w.kind key hs jx e he heq
    have h1 : ((jx : Int) == DKIX_EMPTY) = false := by simp [DKIX_EMPTY]
    simp only [insertSplitKey, hl, h1, Bool.false_and, Bool.false_eq_true, if_false] at h
    have : k' = k := by
      injection h with h
      injection h with _ h
      exact h.symm
    rw [this]
    exact w
  · have hl := lookupUnicode_missing H k w.core w.kind key hs hno
    by_cases hus : k.usable ≤ 0
    · have h1 : decide (k.usable > 0) = false := by simp; omega
      simp only [insertSplitKey, hl, h1, Bool.and_false, Bool.false_eq_true, if_false] at h
      have : k' = k := by
        injection h with h
        injection h with _ h
        exact h.symm
      rw [this]
      exact w
    · have hpos : 0 < k.usable := by omega
      obtain ⟨k2, h1, c', hkind, hn, hu, hsz, hlog, hold, hnew⟩ :=
        appendEntry_core H k w.core hpos key () hno (fun _ => hs)
      have h2 : decide (k.usable > 0) = true := by simp; omega
      have h3 : k' = k2 := by
        have : insertSplitKey P k key (hf key) = .ok ((k.nentries : Int), k2) := by
          simp [insertSplitKey, hl, h2, h1]
        rw [this] at h
        injection h with h
        injection h with _ h
        exact h.symm
      rw [h3]
      exact
        { core := c'
          kind := by rw [hkind]; exact w.kind
          notEmpty := by rw [hlog]; exact w.notEmpty
          small := by rw [hlog]; exact w.small
          entries := fun jx hjx => by
            by_cases hlt : jx < k.nentries
            · obtain ⟨e, he⟩ := w.entries jx hlt
              exact ⟨e, hold jx e he⟩
            · have : jx = k.nentries := by omega
              exact ⟨_, this ▸ hnew⟩
          nent := by
            rw [hn, hu, hsz]
            have := w.nent
            omega }

/-- `_PyDict_NewKeysForClass`'s loop over the class's attributes (:6806-6815). -/
theorem sharedOK_go (H : Honest P hf eqv) : ∀ (attrs : List K) (k : Keys K Unit),
    SharedOK hf eqv P.isStr k → SharedOK hf eqv P.isStr (dictNewKeysForClass.go P attrs k) := by
  intro attrs
  induction attrs with
  | nil => intro k w; exact w
  | cons a rest ih =>
    intro k w
    simp only [dictNewKeysForClass.go]
    by_cases hs : P.isStr a = true
    · rw [if_pos hs, H.hash_ok]
      simp only
      cases hi : insertSplitKey P k a (hf a) with
      | error e => exact w
      | ok r =>
        obtain ⟨ix, k'⟩ := r
        simp only
        by_cases h0 : (ix == DKIX_EMPTY) = true
        · rw [if_pos h0]
          exact w
        · rw [if_neg h0]
          exact ih k' (sharedOK_insert H w a hs ix hi)
    · rw [if_neg hs]
      exact ih k w

end Fresh

/-- `new_dict_with_shared_keys` on any keys it can be given: a well-formed split dict of no items,
with as many value slots as `shared_keys_usable_size`, none of them filled. And the keys a class
builds from any attribute list are such keys, for any key protocol that keeps the hash contract. -/
def SplitFresh : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    (∀ (k : Keys K Unit), SharedOK hf eqv P.isStr k → ∀ id : Nat,
      let d := newDictWithSharedKeys (V := V) id k
      SplitInv hf eqv P.isStr d ∧ d.used = 0 ∧ dictAssoc d = [] ∧
        ∃ v, d.body = .split k v ∧ v.capacity = sharedKeysUsableSize k ∧ v.order = [] ∧
          ∀ ix, v.get ix = none) ∧
    (Honest P hf eqv → ∀ attrs : List K, SharedOK hf eqv P.isStr (dictNewKeysForClass P attrs))
theorem splitFresh_proven : SplitFresh := by
  intro K V _ P hf eqv
  refine ⟨fun k w id => ?_, fun H attrs => sharedOK_go H attrs (sharedKeys0 K) sharedOK_keys0⟩
  refine ⟨⟨k, _, rfl, newValues_wf w⟩, rfl, ?_, _, rfl, ?_, ?_, newValues_get _⟩
  · simp [dictAssoc, newDictWithSharedKeys, splitLive, Values.new]
  · simp [Values.capacity, Values.new]
  · rfl

/-- The state the `dict.setdefault` crash needs is an ordinary one: `del d[key]` on any well-formed
split dict leaves the key in the shared keys, no value in this dict, the invariant intact and the
key gone from the list. -/
def SplitDelKeepsKey : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (d : PyDict K V) (k : Keys K Unit) (v : Values V), d.body = .split k v →
      SplitWF hf eqv P.isStr k v d.used → ∀ (key : K) (ix : Nat) (e : Ent K Unit) (y : V),
      k.entry ix = some e → eqv e.key key = true → v.get ix = some y →
      let v' := (v.set ix none).deleteIndex ix
      let d' : PyDict K V := { d with used := d.used - 1, body := .split k v' }
      SplitInv hf eqv P.isStr d' ∧ k.entry ix = some e ∧ v'.get ix = none ∧
        dictAssoc d' = assocDel eqv (dictAssoc d) key
theorem splitDelKeepsKey_proven : SplitDelKeepsKey := by
  intro K V _ P hf eqv H d k v hb w key ix e y he heq hy v' d'
  obtain ⟨g1, g2⟩ := split_del H d k v hb w key ix e he heq y hy
  have hcap := v.lt_capacity ix y hy
  exact ⟨g1, he, v.get_set_self ix none hcap, g2⟩

end PyLean.DictSet
