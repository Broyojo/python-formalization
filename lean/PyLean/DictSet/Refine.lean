import PyLean.DictSet.Chain
import PyLean.DictSet.DictOps

/-!
The compact table refines an association list.

`Honest P hf eqv` is the hypothesis on the key type: hashing is a function `hf`, comparison is a
pure equivalence `eqv`, and equal keys have equal hashes. It is the contract of `__hash__` and
`__eq__` (`object.__hash__` in the data model). Nothing about the keys beyond that is used, so
these results hold for every hashable type that keeps the contract.

`WF` adds to `Chain` what keys contribute: stored hashes are right, no two live entries are
equal, a unicode table holds only exact strs, and the load is bounded. The load clause counts
slots that are not `DKIX_EMPTY`, dummies included, which is why the table always has an empty
slot and every search stops.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

/-- The contract of `__hash__` and `__eq__`. -/
structure Honest (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool) : Prop where
  hash_ok : ∀ k, P.hash k = .ok (hf k)
  eq_ok : ∀ a b s, P.eq a b s = (.ok (eqv a b), s)
  str_eq : ∀ a b, P.isStr a = true → P.isStr b = true → P.strEq a b = eqv a b
  refl : ∀ a, eqv a a = true
  symm : ∀ a b, eqv a b = eqv b a
  trans : ∀ a b c, eqv a b = true → eqv b c = true → eqv a c = true
  hash_cons : ∀ a b, eqv a b = true → hf a = hf b

/-- What any keys object satisfies, the shared keys of a split table included. A search needs no
more than this. -/
structure Core (hf : K → Int) (eqv : K → K → Bool) (isStr : K → Bool) (k : Keys K V) : Prop
    extends Chain k where
  hashes : ∀ ix e, k.entry ix = some e → e.hash = hf e.key
  uniq : ∀ i1 e1 i2 e2, k.entry i1 = some e1 → k.entry i2 = some e2 →
    eqv e1.key e2.key = true → i1 = i2
  strs : ∀ ix e, k.kind ≠ .general → k.entry ix = some e → isStr e.key = true
  load : (k.filled : Int) + k.usable ≤ usableFraction k.size
  usableNN : 0 ≤ k.usable

structure WF (hf : K → Int) (eqv : K → K → Bool) (isStr : K → Bool) (k : Keys K V) : Prop
    extends Chain k where
  hashes : ∀ ix e, k.entry ix = some e → e.hash = hf e.key
  uniq : ∀ i1 e1 i2 e2, k.entry i1 = some e1 → k.entry i2 = some e2 →
    eqv e1.key e2.key = true → i1 = i2
  strs : ∀ ix e, k.kind ≠ .general → k.entry ix = some e → isStr e.key = true
  notSplit : k.kind ≠ .split
  load : (k.filled : Int) + k.usable ≤ usableFraction k.size
  nent : (k.nentries : Int) + k.usable ≤ usableFraction k.size
  usableNN : 0 ≤ k.usable

theorem WF.toCore {hf : K → Int} {eqv : K → K → Bool} {isStr : K → Bool} {k : Keys K V}
    (w : WF hf eqv isStr k) : Core hf eqv isStr k :=
  { toChain := w.toChain, hashes := w.hashes, uniq := w.uniq, strs := w.strs, load := w.load
    usableNN := w.usableNN }

theorem usableFraction_lt (n : Nat) (h : 0 < n) : usableFraction n < n := by
  simp only [usableFraction, Nat.shiftLeft_eq]
  omega

theorem Keys.size_pos (k : Keys K V) : 0 < k.size := Nat.pow_pos (by omega)

theorem WF.filled_lt {hf : K → Int} {eqv : K → K → Bool} {isStr : K → Bool} {k : Keys K V}
    (w : WF hf eqv isStr k) : k.filled < k.size := by
  have h1 := w.load
  have h2 := w.usableNN
  have h3 := usableFraction_lt k.size k.size_pos
  omega

theorem Core.filled_lt {hf : K → Int} {eqv : K → K → Bool} {isStr : K → Bool} {k : Keys K V}
    (w : Core hf eqv isStr k) : k.filled < k.size := by
  have h1 := w.load
  have h2 := w.usableNN
  have h3 := usableFraction_lt k.size k.size_pos
  omega

theorem Core.stops {hf : K → Int} {eqv : K → K → Bool} {isStr : K → Bool} {k : Keys K V}
    (w : Core hf eqv isStr k) (h : Int) :
    ∃ j, j < probeFuel k.log2Size ∧ k.getIndex (k.pos h j) = DKIX_EMPTY :=
  exists_stop k w.toChain (exists_empty k w.toChain w.filled_lt) h

theorem WF.stops {hf : K → Int} {eqv : K → K → Bool} {isStr : K → Bool} {k : Keys K V}
    (w : WF hf eqv isStr k) (h : Int) :
    ∃ j, j < probeFuel k.log2Size ∧ k.getIndex (k.pos h j) = DKIX_EMPTY :=
  w.toCore.stops h

section Lookup
variable {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}

theorem entryKH_combined (mp : PyDict K V) (k : Keys K V) (h : mp.body = .combined k) (ix : Nat) :
    mp.body.entryKH ix = (k.entry ix).map fun e => (e.key, e.hash) := by
  simp [h, Body.entryKH]

theorem stillThere_same (mp : PyDict K V) (k : Keys K V) (h : mp.body = .combined k) (ix : Nat)
    (e : Ent K V) (he : k.entry ix = some e) : stillThere mp mp.body.ident ix e.key = true := by
  simp [stillThere, h, Body.entryKH, he]

/-- The three comparison routines agree with `eqv` on a live entry. -/
theorem compareGeneric_spec (H : Honest P hf eqv) (mp : PyDict K V) (k : Keys K V)
    (hb : mp.body = .combined k) (ix : Nat) (e : Ent K V) (he : k.entry ix = some e)
    (hh : e.hash = hf e.key) (key : K) :
    compareGeneric P ix key (hf key) mp = (.ok (if eqv e.key key then 1 else 0), mp) := by
  have hkh := entryKH_combined mp k hb ix
  rw [he] at hkh
  simp only [compareGeneric, hkh, Option.map_some]
  by_cases h1 : e.key = key
  · subst h1
    simp [H.refl]
  · by_cases h2 : e.hash = hf key
    · simp only [h1, if_false, h2, if_true, H.eq_ok]
      have hs := stillThere_same mp k hb ix e he
      simp only [hs, if_true]
    · have hne : eqv e.key key = false := by
        cases hq : eqv e.key key with
        | false => rfl
        | true =>
          have := H.hash_cons _ _ hq
          exact absurd (hh.trans this) h2
      simp [h1, h2, hne]

theorem compareUnicodeGeneric_spec (H : Honest P hf eqv) (mp : PyDict K V) (k : Keys K V)
    (hb : mp.body = .combined k) (ix : Nat) (e : Ent K V) (he : k.entry ix = some e)
    (hh : e.hash = hf e.key) (key : K) :
    compareUnicodeGeneric P ix key (hf key) mp = (.ok (if eqv e.key key then 1 else 0), mp) := by
  have hkh := entryKH_combined mp k hb ix
  rw [he] at hkh
  simp only [compareUnicodeGeneric, hkh, Option.map_some]
  by_cases h2 : e.hash = hf key
  · simp only [h2, if_true, H.eq_ok]
    have hs := stillThere_same mp k hb ix e he
    simp only [hs, if_true]
  · have hne : eqv e.key key = false := by
      cases hq : eqv e.key key with
      | false => rfl
      | true =>
        have := H.hash_cons _ _ hq
        exact absurd (hh.trans this) h2
    simp [h2, hne]

theorem compareUnicodeUnicode_spec (H : Honest P hf eqv) (e : Ent K V) (hh : e.hash = hf e.key)
    (key : K) (hk : P.isStr key = true) (hs : P.isStr e.key = true) :
    compareUnicodeUnicode P (some (e.key, e.hash)) key (hf key) = eqv e.key key := by
  simp only [compareUnicodeUnicode]
  by_cases h1 : e.key = key
  · subst h1
    simp [H.refl]
  · by_cases h2 : e.hash = hf key
    · simp [h1, h2, H.str_eq _ _ hs hk]
    · have hne : eqv e.key key = false := by
        cases hq : eqv e.key key with
        | false => rfl
        | true =>
          have := H.hash_cons _ _ hq
          exact absurd (hh.trans this) h2
      simp [h1, h2, hne]

/-- `idx` on the slots of the probe sequence of `key`. -/
private def seqIdx (k : Keys K V) (h : Int) (j : Nat) : Int := k.getIndex (k.pos h j)

/-- Where the search ends, for any check that agrees with `eqv`. -/
theorem search_found {σ W : Type} (k : Keys K W) (w : Core hf eqv P.isStr k) (H : Honest P hf eqv)
    (getIx : σ → Nat → Int) (check : Nat → M σ Int) (s : σ) (key : K)
    (hget : ∀ i, getIx s i = k.getIndex i)
    (hck : ∀ ix e, k.entry ix = some e → check ix s = (.ok (if eqv e.key key then 1 else 0), s))
    (ix : Nat) (e : Ent K W) (he : k.entry ix = some e) (heq : eqv e.key key = true) :
    doLookup getIx check (probeFuel k.log2Size) k.mask (toU64 (hf key) &&& k.mask) (toU64 (hf key)) s
      = (.ok (ix : Int), s) := by
  have hhash : e.hash = hf key := (w.hashes ix e he).trans (H.hash_cons _ _ heq)
  obtain ⟨j0, hj0, h1, h2⟩ := w.reach ix e he
  rw [hhash] at h1 h2
  let c : Nat → Bool := fun t => match k.entry t with
    | some e' => eqv e'.key key
    | none => false
  have hidxNat : ∀ j, seqIdx k (hf key) j ≥ 0 → ∃ (t : Nat) (e' : Ent K W),
      seqIdx k (hf key) j = (t : Int) ∧ k.entry t = some e' := by
    intro j hj
    rcases w.range (k.pos (hf key) j) (k.pos_lt _ _) with h | h | h
    · simp only [seqIdx] at hj; rw [h] at hj; simp [DKIX_EMPTY] at hj
    · simp only [seqIdx] at hj; rw [h] at hj; simp [DKIX_DUMMY] at hj
    · exact h
  have := doLookup_walk getIx check s k.mask (toU64 (hf key)) c (seqIdx k (hf key))
    (fun j => by simp only [seqIdx, hget]; rfl)
    (fun j hj => by
      obtain ⟨t, e', h3, h4⟩ := hidxNat j hj
      have hc : c t = eqv e'.key key := by simp [c, h4]
      rw [h3]
      simp only [Int.toNat_natCast]
      rw [hck t e' h4]
      simp only [hc])
    (probeFuel k.log2Size) 0
    ⟨j0, by omega, by omega, Or.inr ⟨by simp only [seqIdx]; rw [h1]; omega, by
      simp only [seqIdx]; rw [h1]; simp [c, he, heq]⟩⟩
  obtain ⟨j, _, _, h3, h4, h5⟩ := this
  have hval : seqIdx k (hf key) j = (ix : Int) := by
    rcases h3 with h3 | ⟨h3, h6⟩
    · -- an empty slot before the entry contradicts `reach`
      by_cases hlt : j < j0
      · exact absurd h3 (h2 j hlt)
      · by_cases he0 : j = j0
        · subst he0; exact h1
        · exact absurd (Or.inr ⟨by simp only [seqIdx]; rw [h1]; omega, by
            simp only [seqIdx]; rw [h1]; simp [c, he, heq]⟩) (h4 j0 (by omega) (by omega))
    · obtain ⟨t, e', h7, h8⟩ := hidxNat j h3
      rw [h7] at h6
      simp only [Int.toNat_natCast, c, h8] at h6
      have hk : eqv e'.key e.key = true := by
        apply H.trans _ key _ h6
        rw [H.symm]; exact heq
      rw [h7, w.uniq t e' ix e h8 he hk]
  rw [hval] at h5
  exact h5

theorem search_missing {σ W : Type} (k : Keys K W) (w : Core hf eqv P.isStr k)
    (getIx : σ → Nat → Int) (check : Nat → M σ Int) (s : σ) (key : K)
    (hget : ∀ i, getIx s i = k.getIndex i)
    (hck : ∀ ix e, k.entry ix = some e → check ix s = (.ok (if eqv e.key key then 1 else 0), s))
    (hno : ∀ ix e, k.entry ix = some e → eqv e.key key = false) :
    doLookup getIx check (probeFuel k.log2Size) k.mask (toU64 (hf key) &&& k.mask) (toU64 (hf key)) s
      = (.ok DKIX_EMPTY, s) := by
  obtain ⟨j0, hj0, h1⟩ := w.stops (hf key)
  have hidxNat : ∀ j, seqIdx k (hf key) j ≥ 0 → ∃ (t : Nat) (e' : Ent K W),
      seqIdx k (hf key) j = (t : Int) ∧ k.entry t = some e' := by
    intro j hj
    rcases w.range (k.pos (hf key) j) (k.pos_lt _ _) with h | h | h
    · simp only [seqIdx] at hj; rw [h] at hj; simp [DKIX_EMPTY] at hj
    · simp only [seqIdx] at hj; rw [h] at hj; simp [DKIX_DUMMY] at hj
    · exact h
  have := doLookup_walk getIx check s k.mask (toU64 (hf key)) (fun _ => false) (seqIdx k (hf key))
    (fun j => by simp only [seqIdx, hget]; rfl)
    (fun j hj => by
      obtain ⟨t, e', h3, h4⟩ := hidxNat j hj
      rw [h3]
      simp only [Int.toNat_natCast]
      rw [hck t e' h4, hno t e' h4])
    (probeFuel k.log2Size) 0 ⟨j0, by omega, by omega, Or.inl h1⟩
  obtain ⟨j, _, _, h3, _, h5⟩ := this
  rcases h3 with h3 | ⟨_, h6⟩
  · rw [h3] at h5
    exact h5
  · simp at h6

theorem lookupAux_found (H : Honest P hf eqv) (mp : PyDict K V) (k : Keys K V)
    (hb : mp.body = .combined k) (w : WF hf eqv P.isStr k) (key : K)
    (ix : Nat) (e : Ent K V) (he : k.entry ix = some e) (heq : eqv e.key key = true) (n : Nat) :
    dictLookupAux P key (hf key) (n + 1) mp = (.ok ((ix : Int), some e.value), mp) := by
  have hmask : mp.body.mask = k.mask := by simp [Body.mask, Body.log2Size, hb, Keys.mask, Keys.size]
  have hfuel : mp.body.log2Size = k.log2Size := by simp [Body.log2Size, hb]
  have hkind : mp.body.kind = k.kind := by simp [Body.kind, hb]
  have hget : ∀ i, bodyIx mp i = k.getIndex i := by
    intro i; simp [bodyIx, hb, Body.getIndex]
  have hval : mp.body.valueAt ix = some e.value := by simp [hb, Body.valueAt, he]
  have hne : ((ix : Int) == DKIX_KEY_CHANGED) = false := by
    simp [DKIX_KEY_CHANGED]
  have hpos : (ix : Int) ≥ 0 := by omega
  simp only [dictLookupAux, hmask, hfuel, hkind]
  by_cases hg : k.kind = .general
  · simp only [hg, bne_self_eq_false, Bool.false_eq_true, if_false, dictkeysGenericLookup]
    rw [search_found k w.toCore H bodyIx (fun t => compareGeneric P t key (hf key)) mp key hget
      (fun t e' h => compareGeneric_spec H mp k hb t e' h (w.hashes t e' h) key) ix e he heq]
    simp [hne, hpos, hval]
  · have hg' : (k.kind != .general) = true := by simpa using hg
    simp only [hg', if_true]
    by_cases hs : P.isStr key = true
    · simp only [hs, if_true]
      rw [search_found k w.toCore H bodyIx (checkUnicode P key (hf key)) mp key hget
        (fun t e' h => by
          have hstr := w.strs t e' hg h
          have hkh := entryKH_combined mp k hb t
          rw [h] at hkh
          simp only [checkUnicode, hkh, Option.map_some]
          rw [compareUnicodeUnicode_spec H e' (w.hashes t e' h) key hs hstr]) ix e he heq]
      simp [hne, hpos, hval]
    · simp only [hs, if_false, Bool.false_eq_true, unicodekeysLookupGeneric]
      rw [search_found k w.toCore H bodyIx (fun t => compareUnicodeGeneric P t key (hf key)) mp key hget
        (fun t e' h => compareUnicodeGeneric_spec H mp k hb t e' h (w.hashes t e' h) key) ix e he heq]
      simp [hne, hpos, hval]

theorem lookupAux_missing (H : Honest P hf eqv) (mp : PyDict K V) (k : Keys K V)
    (hb : mp.body = .combined k) (w : WF hf eqv P.isStr k) (key : K)
    (hno : ∀ ix e, k.entry ix = some e → eqv e.key key = false) (n : Nat) :
    dictLookupAux P key (hf key) (n + 1) mp = (.ok (DKIX_EMPTY, none), mp) := by
  have hmask : mp.body.mask = k.mask := by simp [Body.mask, Body.log2Size, hb, Keys.mask, Keys.size]
  have hfuel : mp.body.log2Size = k.log2Size := by simp [Body.log2Size, hb]
  have hkind : mp.body.kind = k.kind := by simp [Body.kind, hb]
  have hget : ∀ i, bodyIx mp i = k.getIndex i := by
    intro i; simp [bodyIx, hb, Body.getIndex]
  have hne : (DKIX_EMPTY == DKIX_KEY_CHANGED) = false := by decide
  have hneg : ¬ (DKIX_EMPTY ≥ 0) := by decide
  simp only [dictLookupAux, hmask, hfuel, hkind]
  by_cases hg : k.kind = .general
  · simp only [hg, bne_self_eq_false, Bool.false_eq_true, if_false, dictkeysGenericLookup]
    rw [search_missing k w.toCore bodyIx (fun t => compareGeneric P t key (hf key)) mp key hget
      (fun t e' h => compareGeneric_spec H mp k hb t e' h (w.hashes t e' h) key) hno]
    simp [hne, hneg]
  · have hg' : (k.kind != .general) = true := by simpa using hg
    simp only [hg', if_true]
    by_cases hs : P.isStr key = true
    · simp only [hs, if_true]
      rw [search_missing k w.toCore bodyIx (checkUnicode P key (hf key)) mp key hget
        (fun t e' h => by
          have hstr := w.strs t e' hg h
          have hkh := entryKH_combined mp k hb t
          rw [h] at hkh
          simp only [checkUnicode, hkh, Option.map_some]
          rw [compareUnicodeUnicode_spec H e' (w.hashes t e' h) key hs hstr]) hno]
      simp [hne, hneg]
    · simp only [hs, if_false, Bool.false_eq_true, unicodekeysLookupGeneric]
      rw [search_missing k w.toCore bodyIx (fun t => compareUnicodeGeneric P t key (hf key)) mp key hget
        (fun t e' h => compareUnicodeGeneric_spec H mp k hb t e' h (w.hashes t e' h) key) hno]
      simp [hne, hneg]

/-- `_Py_dict_lookup` on a table holding an equal key: it stops, finds that entry, runs no
restart and changes nothing. This is "lookup finds an inserted key". -/
theorem lookup_found (H : Honest P hf eqv) (mp : PyDict K V) (k : Keys K V)
    (hb : mp.body = .combined k) (w : WF hf eqv P.isStr k) (key : K)
    (ix : Nat) (e : Ent K V) (he : k.entry ix = some e) (heq : eqv e.key key = true) :
    dictLookup P key (hf key) mp = (.ok ((ix : Int), some e.value), mp) :=
  lookupAux_found H mp k hb w key ix e he heq 255

/-- `_Py_dict_lookup` on a table without an equal key: it stops at an empty slot. This is the
termination claim at `dictobject.c:145-150` and `:357-358`. -/
theorem lookup_missing (H : Honest P hf eqv) (mp : PyDict K V) (k : Keys K V)
    (hb : mp.body = .combined k) (w : WF hf eqv P.isStr k) (key : K)
    (hno : ∀ ix e, k.entry ix = some e → eqv e.key key = false) :
    dictLookup P key (hf key) mp = (.ok (DKIX_EMPTY, none), mp) :=
  lookupAux_missing H mp k hb w key hno 255

end Lookup

end PyLean.DictSet
