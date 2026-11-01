import PyLean.DictSet.Assoc

/-!
Dict operations on a well-formed combined table, stated against the association list.

`DictInv d` is the invariant every dict with a combined table keeps. `dictAssoc d` is the list it
stands for. The only way an operation here can fail is `MemoryError`, from a table that would
need `2**64` slots, and then the dict is unchanged. There is no "no overflow" hypothesis: that
case is in the statement.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

/-- The list a dict stands for: live entries in `dk_entries` order, or, for a split table, the
values the dict holds, in the order of its insertion-order array. -/
def dictAssoc (d : PyDict K V) : List (K × V) :=
  match d.body with
  | .combined k => k.items
  | .split k v => (splitLive k v d.used).map fun e => (e.key, e.value)

structure DictInv (hf : K → Int) (eqv : K → K → Bool) (isStr : K → Bool) (d : PyDict K V) : Prop where
  wf : ∃ k, d.body = .combined k ∧ WF hf eqv isStr k ∧ d.used = (liveEntries k).length

theorem wf_empty (hf : K → Int) (eqv : K → K → Bool) (isStr : K → Bool) :
    WF hf eqv isStr (emptyKeys : Keys K V) where
  toChain := chain_empty
  hashes := by intro ix e h; simp [Keys.entry, emptyKeys] at h
  uniq := by intro i1 e1 i2 e2 h; simp [Keys.entry, emptyKeys] at h
  strs := by intro ix e _ h; simp [Keys.entry, emptyKeys] at h
  notSplit := by simp [emptyKeys]
  load := by simp [emptyKeys, Keys.filled, Keys.size, usableFraction, DKIX_EMPTY]
  nent := by simp [emptyKeys, Keys.nentries, Keys.size, usableFraction]
  usableNN := by simp [emptyKeys]

/-- A new dict satisfies the invariant. -/
theorem dictInv_new (hf : K → Int) (eqv : K → K → Bool) (isStr : K → Bool) (id n : Nat) :
    DictInv hf eqv isStr ({ ident := id, nextId := n } : PyDict K V) :=
  ⟨⟨emptyKeys, rfl, wf_empty hf eqv isStr, by simp [liveEntries, emptyKeys]⟩⟩

section
variable {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}

theorem any_items (k : Keys K V) (key : K) :
    k.items.any (fun p => eqv p.1 key) = true ↔
      ∃ ix e, k.entry ix = some e ∧ eqv e.key key = true := by
  simp only [Keys.items, List.any_map, List.any_eq_true, Function.comp_def]
  constructor
  · rintro ⟨e, he, h⟩
    obtain ⟨ix, hix⟩ := (mem_live k e).mp he
    exact ⟨ix, e, hix, h⟩
  · rintro ⟨ix, e, h1, h2⟩
    exact ⟨e, (mem_live k e).mpr ⟨ix, h1⟩, h2⟩

theorem not_any_items (k : Keys K V) (key : K)
    (hno : ∀ ix e, k.entry ix = some e → eqv e.key key = false) :
    k.items.any (fun p => eqv p.1 key) = false := by
  cases h : k.items.any (fun p => eqv p.1 key) with
  | false => rfl
  | true =>
    obtain ⟨ix, e, h1, h2⟩ := (any_items k key).mp h
    rw [hno ix e h1] at h2
    exact absurd h2 (by simp)

theorem dichotomy (k : Keys K V) (key : K) :
    (∃ ix e, k.entry ix = some e ∧ eqv e.key key = true) ∨
    (∀ ix e, k.entry ix = some e → eqv e.key key = false) := by
  by_cases h : ∃ ix e, k.entry ix = some e ∧ eqv e.key key = true
  · exact Or.inl h
  · refine Or.inr fun ix e he => ?_
    cases hq : eqv e.key key with
    | false => rfl
    | true => exact absurd ⟨ix, e, he, hq⟩ h

/-- `d[key]` finds what the list holds. -/
theorem lookup_assoc (H : Honest P hf eqv) (d : PyDict K V)
    (hd : DictInv hf eqv P.isStr d) (key : K) :
    ∃ ix, dictLookup P key (hf key) d = (.ok (ix, assocGet eqv (dictAssoc d) key), d) ∧
      (assocGet eqv (dictAssoc d) key = none → ix = DKIX_EMPTY) ∧
      (∀ v, assocGet eqv (dictAssoc d) key = some v → 0 ≤ ix) := by
  obtain ⟨k, hb, w, hu⟩ := hd.wf
  have ha : dictAssoc d = k.items := by simp [dictAssoc, hb]
  rw [ha]
  rcases dichotomy (eqv := eqv) k key with ⟨ix, e, h1, h2⟩ | hno
  · have hget : assocGet eqv k.items key = some e.value := by
      -- the first match is the only match
      have hpair := pairwise_of_uniq eqv k.entries
        (fun i1 e1 i2 e2 a b c =>
          w.uniq i1 e1 i2 e2 ((entry_iff k i1 e1).mpr a) ((entry_iff k i2 e2).mpr b) c)
      have hmem : e ∈ liveEntries k := (mem_live k e).mpr ⟨ix, h1⟩
      simp only [assocGet, Keys.items, List.find?_map, Option.map_map]
      have hfind : (liveEntries k).find? (fun x => eqv x.key key) = some e := by
        have hex : (liveEntries k).find? (fun x => eqv x.key key) ≠ none := by
          intro hn
          have := List.find?_eq_none.mp hn e hmem
          simp [h2] at this
        cases hf0 : (liveEntries k).find? (fun x => eqv x.key key) with
        | none => exact absurd hf0 hex
        | some e0 =>
          have h3 : eqv e0.key key = true := by
            simpa using List.find?_some (p := fun x : Ent K V => eqv x.key key) hf0
          have h4 : e0 ∈ liveEntries k := List.mem_of_find?_eq_some hf0
          obtain ⟨t, ht⟩ := (mem_live k e0).mp h4
          have hee : eqv e0.key e.key = true := H.trans _ key _ h3 (by rw [H.symm]; exact h2)
          have : t = ix := w.uniq t e0 ix e ht h1 hee
          subst this
          rw [ht] at h1
          exact congrArg some (Option.some.inj h1)
      simp [hfind, Function.comp_def]
    refine ⟨ix, ?_, ?_, ?_⟩
    · rw [hget]
      exact lookup_found H d k hb w key ix e h1 h2
    · rw [hget]; simp
    · intro v _; omega
  · have hget : assocGet eqv k.items key = none := by
      simp only [assocGet, Option.map_eq_none_iff, List.find?_eq_none]
      intro p hp
      simp only [Keys.items, List.mem_map] at hp
      obtain ⟨e, he, rfl⟩ := hp
      obtain ⟨ix, hix⟩ := (mem_live k e).mp he
      simp [hno ix e hix]
    refine ⟨DKIX_EMPTY, ?_, fun _ => rfl, ?_⟩
    · rw [hget]
      exact lookup_missing H d k hb w key hno
    · intro v h
      rw [hget] at h
      simp at h

theorem storeValue_spec (H : Honest P hf eqv) (mp : PyDict K V) (k : Keys K V)
    (hb : mp.body = .combined k) (w : WF hf eqv P.isStr k) (hused : mp.used = (liveEntries k).length)
    (key : K) (v : V) (ix : Nat) (e : Ent K V) (he : k.entry ix = some e)
    (heq : eqv e.key key = true) :
    ∃ d', storeValue v ix mp = (.ok (), d') ∧ DictInv hf eqv P.isStr d' ∧
      dictAssoc d' = assocSet eqv k.items key v := by
  have he' := (entry_iff k ix e).mp he
  let k' : Keys K V := { k with entries := k.entries.set ix (some { e with value := v }) }
  have hent : ∀ t, k'.entry t = if t = ix then some { e with value := v } else k.entry t := by
    intro t
    simp only [Keys.entry, k', List.getElem?_set]
    by_cases h : t = ix
    · subst h
      have hlt : t < k.entries.length := (List.getElem?_eq_some_iff.mp he').1
      simp [hlt]
    · have h' : ix ≠ t := fun x => h x.symm
      simp [h, h']
  have hentOld : ∀ t e', k'.entry t = some e' → ∃ e0, k.entry t = some e0 ∧ e'.key = e0.key ∧ e'.hash = e0.hash := by
    intro t e' h
    rw [hent] at h
    by_cases ht : t = ix
    · simp only [ht, if_true, Option.some.injEq] at h
      subst h
      exact ⟨e, ht ▸ he, rfl, rfl⟩
    · simp only [ht, if_false] at h
      exact ⟨e', h, rfl, rfl⟩
  have hc : Chain k' := chain_setvalue k w.toChain k' rfl rfl (by
    intro t
    rw [hent]
    by_cases ht : t = ix
    · simp [ht, he]
    · simp [ht])
  have hw : WF hf eqv P.isStr k' := {
    toChain := hc
    hashes := by
      intro t e' h
      obtain ⟨e0, a, b, c⟩ := hentOld t e' h
      rw [b, c]
      exact w.hashes t e0 a
    uniq := by
      intro i1 e1 i2 e2 a b c
      obtain ⟨e3, a1, a2, _⟩ := hentOld i1 e1 a
      obtain ⟨e4, b1, b2, _⟩ := hentOld i2 e2 b
      rw [a2, b2] at c
      exact w.uniq i1 e3 i2 e4 a1 b1 c
    strs := by
      intro t e' hg h
      obtain ⟨e0, a, b, _⟩ := hentOld t e' h
      rw [b]
      exact w.strs t e0 hg a
    notSplit := w.notSplit
    load := w.load
    nent := by
      have : k'.nentries = k.nentries := by simp [k', Keys.nentries]
      rw [this]
      exact w.nent
    usableNN := w.usableNN }
  have hitems : k'.items = k.items.map fun p => if eqv p.1 key then (p.1, v) else p := by
    simp only [Keys.items, liveEntries, k']
    exact filterMap_set_value eqv key v k.entries ix e he' heq (fun j e' a b => by
      have hmatch : eqv e'.key e.key = true := H.trans _ key _ b (by rw [H.symm]; exact heq)
      exact w.uniq j e' ix e ((entry_iff k j e').mpr a) he hmatch)
  have hany : k.items.any (fun p => eqv p.1 key) = true := (any_items k key).mpr ⟨ix, e, he, heq⟩
  refine ⟨{ mp with body := .combined k' }, ?_, ⟨⟨k', rfl, hw, ?_⟩⟩, ?_⟩
  · simp only [storeValue, hb, he']
    rfl
  · have : (liveEntries k').length = (liveEntries k).length := by
      have h1 : k'.items.length = k.items.length := by rw [hitems]; simp
      simpa [Keys.items] using h1
    simpa [this] using hused
  · simp only [dictAssoc, assocSet, hany, if_true]
    exact hitems

/-- Inserting a key that is absent. -/
theorem insertCombined_spec (H : Honest P hf eqv) (mp : PyDict K V) (k : Keys K V)
    (hb : mp.body = .combined k) (w : WF hf eqv P.isStr k) (hused : mp.used = (liveEntries k).length)
    (key : K) (v : V) (hno : ∀ ix e, k.entry ix = some e → eqv e.key key = false) :
    insertCombinedDict P.toKeyOps (hf key) key v mp = (.error memoryError, mp) ∨
    ∃ k' : Keys K V, ∃ n, insertCombinedDict P.toKeyOps (hf key) key v mp =
        (.ok (), { mp with nextId := n, body := .combined k' }) ∧ WF hf eqv P.isStr k' ∧
      liveEntries k' = liveEntries k ++ [⟨key, hf key, v⟩] := by
  -- Step 3 of the C function, on any table with room.
  have tail : ∀ (m : PyDict K V) (k1 : Keys K V), m.body = .combined k1 → WF hf eqv P.isStr k1 →
      0 < k1.usable → (∀ ix e, k1.entry ix = some e → eqv e.key key = false) →
      (k1.kind ≠ .general → P.isStr key = true) →
      ∃ k' : Keys K V, (match m.body with
        | .combined k =>
          match appendEntry k key (hf key) v with
          | .ok k' => (.ok (), { m with body := .combined k' })
          | .error e => (.error e, m)
        | .split _ _ => (.error .modelFuel, m)) = (Except.ok (), { m with body := Body.combined k' }) ∧
        WF hf eqv P.isStr k' ∧ liveEntries k' = liveEntries k1 ++ [⟨key, hf key, v⟩] := by
    intro m k1 hb1 w1 hus1 hno1 hs1
    obtain ⟨k', a, b, c, _, _⟩ := appendEntry_spec H k1 w1 hus1 key v hno1 hs1
    exact ⟨k', by simp only [hb1, a], b, c⟩
  have hbU : mp.body.isUnicode = k.isUnicode := by simp [Body.isUnicode, Body.kind, hb, Keys.isUnicode]
  have hbUs : mp.body.usable = k.usable := by simp [Body.usable, hb]
  have noOf : ∀ k1 : Keys K V, liveEntries k1 = liveEntries k →
      ∀ ix e, k1.entry ix = some e → eqv e.key key = false := by
    intro k1 hl ix e he
    have : e ∈ liveEntries k := hl ▸ (mem_live k1 e).mpr ⟨ix, he⟩
    obtain ⟨t, ht⟩ := (mem_live k e).mp this
    exact hno t e ht
  simp only [insertCombinedDict]
  by_cases hA : (mp.body.isUnicode && !P.toKeyOps.isStr key) = true
  · simp only [hA, if_true]
    rcases insertionResize_spec H mp k hb w hused false with h | ⟨k1, h1, w1, l1, u1, _, g1⟩
    · left; simp only [h]
    · right
      simp only [h1]
      have hus : ¬ ({ mp with nextId := mp.nextId + 1, body := Body.combined k1 } : PyDict K V).body.usable ≤ 0 := by
        simp only [Body.usable]; omega
      rw [if_neg hus]
      obtain ⟨k', a, b, c⟩ := tail { mp with nextId := mp.nextId + 1, body := Body.combined k1 } k1 rfl w1 u1
        (noOf k1 l1) (fun hg => absurd (g1 rfl) hg)
      refine ⟨k', mp.nextId + 1, a, b, ?_⟩
      rw [c, l1]
  · simp only [hA, if_false, Bool.false_eq_true]
    have hstr : k.kind ≠ .general → P.isStr key = true := by
      intro hg
      have : mp.body.isUnicode = true := by simpa [hbU, Keys.isUnicode] using hg
      simpa [this] using hA
    by_cases hB : mp.body.usable ≤ 0
    · simp only [hB, if_true]
      rcases insertionResize_spec H mp k hb w hused true with h | ⟨k1, h1, w1, l1, u1, g1, _⟩
      · left; simp only [h]
      · right
        simp only [h1]
        obtain ⟨k', a, b, c⟩ := tail { mp with nextId := mp.nextId + 1, body := Body.combined k1 } k1 rfl w1 u1
          (noOf k1 l1) (fun hg => by
            rcases g1 with g | ⟨g, _⟩
            · exact absurd g hg
            · exact hstr g)
        refine ⟨k', mp.nextId + 1, a, b, ?_⟩
        rw [c, l1]
    · simp only [hB, if_false]
      right
      obtain ⟨k', a, b, c⟩ := tail mp k hb w (by rw [hbUs] at hB; omega) hno hstr
      exact ⟨k', mp.nextId, a, b, c⟩

/-- `insertdict`. -/
theorem insertDict_spec (H : Honest P hf eqv) (mp : PyDict K V) (k : Keys K V)
    (hb : mp.body = .combined k) (w : WF hf eqv P.isStr k) (hused : mp.used = (liveEntries k).length)
    (key : K) (v : V) :
    insertDict P key (hf key) v mp = (.error memoryError, mp) ∨
    ∃ d', insertDict P key (hf key) v mp = (.ok (), d') ∧ DictInv hf eqv P.isStr d' ∧
      dictAssoc d' = assocSet eqv k.items key v := by
  simp only [insertDict, hb]
  rcases dichotomy (eqv := eqv) k key with ⟨ix, e, h1, h2⟩ | hno
  · right
    rw [lookup_found H mp k hb w key ix e h1 h2]
    simp only [insertAfterLookup, Int.toNat_natCast]
    exact storeValue_spec H mp k hb w hused key v ix e h1 h2
  · rw [lookup_missing H mp k hb w key hno]
    simp only [insertAfterLookup]
    rcases insertCombined_spec H mp k hb w hused key v hno with h | ⟨k', n, a, b, c⟩
    · left; simp only [h]
    · right
      simp only [a]
      refine ⟨_, rfl, ⟨⟨k', rfl, b, ?_⟩⟩, ?_⟩
      · simp only [c, hused, List.length_append, List.length_cons, List.length_nil]
      · have hany := not_any_items (eqv := eqv) k key hno
        simp only [dictAssoc, assocSet, hany, Bool.false_eq_true, if_false]
        simp [Keys.items, c]

/-- `d[key] = v` on any dict with a combined table. The first entry is a new key on an empty
table; everything else goes through `insertdict`. -/
theorem dictSetItem_spec (H : Honest P hf eqv) (mp : PyDict K V)
    (hd : DictInv hf eqv P.isStr mp) (key : K) (v : V) :
    dictSetItem P key v mp = (.error memoryError, mp) ∨
    ∃ d', dictSetItem P key v mp = (.ok (), d') ∧ DictInv hf eqv P.isStr d' ∧
      dictAssoc d' = assocSet eqv (dictAssoc mp) key v := by
  obtain ⟨k, hb, w, hu⟩ := hd.wf
  have ha : dictAssoc mp = k.items := by simp [dictAssoc, hb]
  rw [ha]
  simp only [dictSetItem, H.hash_ok]
  by_cases hE : mp.body.isEmptyKeys = true
  · right
    rw [if_pos hE]
    have hlog : k.log2Size = 0 := by simpa [Body.isEmptyKeys, Body.log2Size, hb] using hE
    have hnil : k.entries = [] := by
      have h1 := w.nent
      have h2 := w.usableNN
      have hU : usableFraction k.size = 0 := by simp [Keys.size, hlog, usableFraction]
      rw [hU] at h1
      have : k.nentries = 0 := by omega
      exact List.length_eq_zero_iff.mp this
    have hitems : k.items = [] := by simp [Keys.items, liveEntries, hnil]
    have hused0 : mp.used = 0 := by simp [hu, liveEntries, hnil]
    let e : Ent K V := ⟨key, hf key, v⟩
    let k0 : Keys K V := newKeysObject mp.nextId PyDict_LOG_MINSIZE (P.isStr key)
    let k' : Keys K V := { (k0.setIndex (toU64 (hf key) &&& (PyDict_MINSIZE - 1)) 0) with
      entries := [some e]
      usable := k0.usable - 1 }
    have hk0 : Chain k0 := chain_new _ _ _
    have hpos : toU64 (hf key) &&& (PyDict_MINSIZE - 1) = k0.pos (hf key) 0 := rfl
    have hc : Chain k' := chain_add k0 hk0 e (toU64 (hf key) &&& (PyDict_MINSIZE - 1)) 0
      (by simp [probeFuel, k0, newKeysObject]) hpos
      (by
        have : k0.getIndex (toU64 (hf key) &&& (PyDict_MINSIZE - 1)) = DKIX_EMPTY := by
          simp only [Keys.getIndex, k0, newKeysObject, List.getD]
          have hlt := k0.pos_lt (hf key) 0
          rw [← hpos] at hlt
          have hs : k0.size = 2 ^ PyDict_LOG_MINSIZE := rfl
          simp [hs ▸ hlt]
        rw [this]
        decide)
      (fun j' h => by omega) k' rfl rfl rfl
    have hent : ∀ t e', k'.entry t = some e' → t = 0 ∧ e' = e := by
      intro t e' h
      have h' := (entry_iff k' t e').mp h
      simp only [k'] at h'
      cases t with
      | zero =>
        have : e' = e := by simpa using h'.symm
        exact ⟨rfl, this⟩
      | succ t => simp at h'
    have hw : WF hf eqv P.isStr k' := {
      toChain := hc
      hashes := by
        intro t e' h
        obtain ⟨_, rfl⟩ := hent t e' h
        rfl
      uniq := by
        intro i1 e1 i2 e2 a b _
        rw [(hent i1 e1 a).1, (hent i2 e2 b).1]
      strs := by
        intro t e' hg h
        obtain ⟨_, rfl⟩ := hent t e' h
        have hk : k'.kind = k0.kind := rfl
        cases hs : P.isStr key with
        | true => rfl
        | false =>
          have : k'.kind = .general := by
            rw [hk]
            simp [k0, newKeysObject, hs]
          exact absurd this hg
      notSplit := by
        have hk : k'.kind = k0.kind := rfl
        rw [hk]
        simp only [k0, newKeysObject]
        cases P.isStr key <;> simp
      load := by
        have h1 : k'.filled ≤ k0.filled + 1 := by
          have := filled_set k0 (toU64 (hf key) &&& (PyDict_MINSIZE - 1)) 0 (by
            rw [hk0.len, hpos]; exact k0.pos_lt _ _)
          exact this
        have h2 : k0.filled = 0 := by
          simp [Keys.filled, k0, newKeysObject, List.countP_replicate, DKIX_EMPTY]
        have h3 : k'.usable = (usableFraction k'.size : Int) - 1 := rfl
        rw [h3]
        omega
      nent := by
        have h3 : k'.usable = (usableFraction k'.size : Int) - 1 := rfl
        have h4 : k'.nentries = 1 := rfl
        rw [h3, h4]
        omega
      usableNN := by
        have h3 : k'.usable = 4 := by
          show (usableFraction (2 ^ 3) : Int) - 1 = 4
          decide
        rw [h3]
        decide }
    refine ⟨{ mp with used := mp.used + 1, nextId := mp.nextId + 1, body := .combined k' }, rfl,
      ⟨⟨k', rfl, hw, ?_⟩⟩, ?_⟩
    · simp [hused0, liveEntries, k']
    · have hany : k.items.any (fun p => eqv p.1 key) = false := by simp [hitems]
      simp only [dictAssoc, assocSet, hany, Bool.false_eq_true, if_false, hitems, List.nil_append]
      simp [Keys.items, liveEntries, k', e]
  · rw [if_neg hE]
    exact insertDict_spec H mp k hb w hu key v

end

end PyLean.DictSet
