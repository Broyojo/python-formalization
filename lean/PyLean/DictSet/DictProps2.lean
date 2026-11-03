import PyLean.DictSet.DictProps

/-!
Deletion, `popitem`, and iteration order on a well-formed combined table.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

theorem length_set_none : ∀ (es : List (Option (Ent K V))) (ix : Nat) (e : Ent K V),
    es[ix]? = some (some e) →
    ((es.set ix none).filterMap id).length + 1 = (es.filterMap id).length := by
  intro es
  induction es with
  | nil => intro ix e h; simp at h
  | cons a t ih =>
    intro ix e he
    cases ix with
    | zero =>
      have ha : a = some e := by simpa using he
      subst ha
      simp
    | succ ix =>
      have := ih ix e (by simpa using he)
      cases a <;> simpa [List.set_cons_succ] using this

/-- The first live slot of a list, as `_PyDict_Next` finds it. -/
theorem scanFrom_spec : ∀ (l : List (Option (Ent K V))) (i : Nat),
    (scanFrom l i = none ∧ l.filterMap id = []) ∨
    (∃ m e, scanFrom l i = some (i + m, e) ∧ l.filterMap id = e :: (l.drop (m + 1)).filterMap id) := by
  intro l
  induction l with
  | nil => intro i; exact Or.inl ⟨rfl, rfl⟩
  | cons a t ih =>
    intro i
    cases a with
    | none =>
      rcases ih (i + 1) with ⟨h1, h2⟩ | ⟨m, e, h1, h2⟩
      · exact Or.inl ⟨by simpa [scanFrom] using h1, by simpa using h2⟩
      · refine Or.inr ⟨m + 1, e, ?_, by simpa using h2⟩
        have : i + (m + 1) = i + 1 + m := by omega
        rw [this]
        simpa [scanFrom] using h1
    | some e =>
      exact Or.inr ⟨0, e, by simp [scanFrom], by simp⟩

/-- `_PyDict_Next` walks the live entries in order. -/
theorem dictNextAll_spec (mp : PyDict K V) (k : Keys K V) (hb : mp.body = .combined k) :
    ∀ (fuel i : Nat), k.nentries < i + fuel →
      dictNextAll mp fuel (i : Int) =
        ((k.entries.drop i).filterMap id).map fun e => (e.key, e.value, e.hash) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i h
    have : k.entries.drop i = [] := List.drop_eq_nil_of_le (by simp only [Keys.nentries] at h; omega)
    simp [dictNextAll, this]
  | succ fuel ih =>
    intro i h
    by_cases hge : i ≥ k.nentries
    · have : k.entries.drop i = [] := List.drop_eq_nil_of_le (by simpa [Keys.nentries] using hge)
      have hn : dictNext mp (i : Int) = none := by
        simp only [dictNext, hb]
        rw [if_pos (Or.inr (by omega))]
      simp [dictNextAll, hn, this]
    · have hn0 : ¬ ((i : Int) < 0 ∨ (i : Int) ≥ k.nentries) := by omega
      rcases scanFrom_spec (k.entries.drop i) i with ⟨h1, h2⟩ | ⟨m, e, h1, h2⟩
      · have hn : dictNext mp (i : Int) = none := by
          simp only [dictNext, hb]
          rw [if_neg hn0]
          simp [h1]
        simp [dictNextAll, hn, h2]
      · have hn : dictNext mp (i : Int) =
            some (((i + m + 1 : Nat) : Int), e.key, e.value, e.hash) := by
          simp only [dictNext, hb]
          rw [if_neg hn0]
          simp [h1]
        have hd : (k.entries.drop i).drop (m + 1) = k.entries.drop (i + m + 1) := by
          rw [List.drop_drop]
          congr 1 <;> omega
        simp only [dictNextAll, hn]
        rw [ih (i + m + 1) (by omega), h2, hd]
        simp

/-- Iteration order is the list's order: this is `dict.keys()`, `dict.values()`, `dict.items()`,
and every other full walk of the table. -/
theorem dictItems_spec (mp : PyDict K V) (k : Keys K V) (hb : mp.body = .combined k) :
    dictItems mp = (liveEntries k).map fun e => (e.key, e.value, e.hash) := by
  have hn : mp.body.nentries = k.nentries := by simp [Body.nentries, hb]
  simp only [dictItems, hn]
  have := dictNextAll_spec mp k hb (k.nentries + mp.used + 1) 0 (by omega)
  simpa [liveEntries] using this

theorem dictItemsList_spec (mp : PyDict K V) (k : Keys K V) (hb : mp.body = .combined k) :
    dictItemsList mp = k.items := by
  simp [dictItemsList, dictItems_spec mp k hb, Keys.items, Function.comp_def]

section
variable {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}

/-- `delitem_common` on a live entry. -/
theorem delitemCommon_spec (H : Honest P hf eqv) (mp : PyDict K V) (k : Keys K V)
    (hb : mp.body = .combined k) (w : WF hf eqv P.isStr k) (hused : mp.used = (liveEntries k).length)
    (key : K) (ix : Nat) (e : Ent K V) (he : k.entry ix = some e) (heq : eqv e.key key = true) :
    ∃ d', delitemCommon e.hash ix mp = (.ok (), d') ∧ DictInv hf eqv P.isStr d' ∧
      dictAssoc d' = assocDel eqv k.items key := by
  obtain ⟨s, hs, h1, h2⟩ := lookdictIndex_spec k w.toChain ix e he
  have he' := (entry_iff k ix e).mp he
  have hslt : s < k.indices.length := by rw [w.len]; exact hs
  let k' : Keys K V := { (k.setIndex s DKIX_DUMMY) with
    entries := k.entries.set ix none
    version := 0 }
  have hent : ∀ t, k'.entry t = if t = ix then none else k.entry t := by
    intro t
    simp only [Keys.entry, k', List.getElem?_set]
    by_cases h : t = ix
    · subst h
      have hlt : t < k.entries.length := (List.getElem?_eq_some_iff.mp he').1
      simp [hlt]
    · have h' : ix ≠ t := fun x => h x.symm
      simp [h, h']
  have hold : ∀ t e', k'.entry t = some e' → k.entry t = some e' := by
    intro t e' h
    rw [hent] at h
    by_cases ht : t = ix
    · simp [ht] at h
    · simpa [ht] using h
  have hc : Chain k' := chain_remove k w.toChain ix s hs h1 k' rfl rfl hent
  have hw : WF hf eqv P.isStr k' := {
    toChain := hc
    hashes := fun t e' h => w.hashes t e' (hold t e' h)
    uniq := fun i1 e1 i2 e2 a b c => w.uniq i1 e1 i2 e2 (hold i1 e1 a) (hold i2 e2 b) c
    strs := fun t e' hg h => w.strs t e' hg (hold t e' h)
    notSplit := w.notSplit
    load := by
      have hf1 := filled_set_filled k s DKIX_DUMMY hslt (by rw [h1]; simp [DKIX_EMPTY])
      have h2' : k'.filled = (k.setIndex s DKIX_DUMMY).filled := rfl
      have h3 : k'.usable = k.usable := rfl
      have h4 : k'.size = k.size := rfl
      have h5 := w.load
      rw [h3, h4]
      omega
    nent := by
      have h2' : k'.nentries = k.nentries := by simp [k', Keys.nentries]
      have h3 : k'.usable = k.usable := rfl
      have h4 : k'.size = k.size := rfl
      rw [h2', h3, h4]
      exact w.nent
    usableNN := w.usableNN
    small := w.small }
  have huq : ∀ (j : Nat) (e' : Ent K V), k.entries[j]? = some (some e') →
      eqv e'.key key = true → j = ix := fun j e' a b => by
    have hmatch : eqv e'.key e.key = true := H.trans _ key _ b (by rw [H.symm]; exact heq)
    exact w.uniq j e' ix e ((entry_iff k j e').mpr a) he hmatch
  have hlive : liveEntries k' = (liveEntries k).filter fun x => !eqv x.key key :=
    filterMap_set_none eqv key k.entries ix e he' heq huq
  have hlen := length_set_none k.entries ix e he'
  refine ⟨{ mp with used := mp.used - 1, body := .combined k' }, ?_, ⟨⟨k', rfl, hw, ?_⟩⟩, ?_⟩
  · simp only [delitemCommon, hb, h2]
    rw [if_neg (by omega)]
    simp only [Int.toNat_natCast]
    rfl
  · have : (liveEntries k').length + 1 = (liveEntries k).length := hlen
    show mp.used - 1 = (liveEntries k').length
    omega
  · simp only [dictAssoc, assocDel, Keys.items, hlive, List.filter_map, Function.comp_def]

/-- `del d[key]`. -/
theorem dictDelItem_spec (H : Honest P hf eqv) (mp : PyDict K V)
    (hd : DictInv hf eqv P.isStr mp) (key : K) :
    ((dictAssoc mp).any (fun p => eqv p.1 key) = false ∧
      dictDelItem P key mp = (.error (keyErr P key), mp)) ∨
    ((dictAssoc mp).any (fun p => eqv p.1 key) = true ∧
      ∃ d', dictDelItem P key mp = (.ok (), d') ∧ DictInv hf eqv P.isStr d' ∧
        dictAssoc d' = assocDel eqv (dictAssoc mp) key) := by
  obtain ⟨k, hb, w, hu⟩ := hd.wf
  have ha : dictAssoc mp = k.items := by simp [dictAssoc, hb]
  rw [ha]
  simp only [dictDelItem, H.hash_ok, H.hash_quiet, dictDelItemKnownHash]
  rcases dichotomy (eqv := eqv) k key with ⟨ix, e, h1, h2⟩ | hno
  · right
    refine ⟨(any_items k key).mpr ⟨ix, e, h1, h2⟩, ?_⟩
    rw [lookup_found H mp k hb w key ix e h1 h2]
    have hne : ((ix : Int) == DKIX_EMPTY) = false := by simp [DKIX_EMPTY]
    have hhash : e.hash = hf key := (w.hashes ix e h1).trans (H.hash_cons _ _ h2)
    simp only [hne, Bool.false_eq_true, if_false, Int.toNat_natCast, ← hhash]
    exact delitemCommon_spec H mp k hb w hu key ix e h1 h2
  · left
    refine ⟨not_any_items k key hno, ?_⟩
    rw [lookup_missing H mp k hb w key hno]

theorem lastLive_full (k : Keys K V) (hne : (liveEntries k).length ≠ 0) :
    ∃ i e, lastLive k.entries k.nentries = some (i, e) ∧ k.entry i = some e ∧
      (k.entries.take i).filterMap id ++ [e] = liveEntries k ∧
      ∀ t, i < t → k.entry t = none := by
  have hlen : k.nentries ≤ k.entries.length := by simp [Keys.nentries]
  have htop : k.entries.take k.nentries = k.entries := by simp [Keys.nentries]
  rcases lastLive_above k.entries k.nentries hlen with ⟨_, h2⟩ | ⟨i, e, _, h2, h3, h4, h5⟩
  · rw [htop] at h2
    simp [liveEntries, h2] at hne
  · refine ⟨i, e, h2, (entry_iff k i e).mpr h3, ?_, ?_⟩
    · rw [htop] at h4
      exact h4.symm
    · intro t ht
      cases hq : k.entry t with
      | none => rfl
      | some e' =>
        have h' := (entry_iff k t e').mp hq
        have hlt : t < k.nentries := (List.getElem?_eq_some_iff.mp h').1
        exact absurd h' (h5 t ht hlt e')

/-- `dict.popitem()`: LIFO, as documented. -/
theorem dictPopitem_spec (H : Honest P hf eqv) (mp : PyDict K V)
    (hd : DictInv hf eqv P.isStr mp) :
    (dictAssoc mp = [] ∧
      dictPopitem mp = (.error (.keyError "'popitem(): dictionary is empty'"), mp)) ∨
    ∃ p d', dictPopitem mp = (.ok p, d') ∧ DictInv hf eqv P.isStr d' ∧
      dictAssoc mp = dictAssoc d' ++ [p] := by
  obtain ⟨k, hb, w, hu⟩ := hd.wf
  have ha : dictAssoc mp = k.items := by simp [dictAssoc, hb]
  by_cases h0 : mp.used = 0
  · left
    have : liveEntries k = [] := List.length_eq_zero_iff.mp (by omega)
    refine ⟨by simp [ha, Keys.items, this], ?_⟩
    simp [dictPopitem, h0]
  · right
    obtain ⟨i, e, h1, h2, h3, h4⟩ := lastLive_full k (by omega)
    obtain ⟨s, hs, h5, h6⟩ := lookdictIndex_spec k w.toChain i e h2
    have hslt : s < k.indices.length := by rw [w.len]; exact hs
    let k' : Keys K V := { (k.setIndex s DKIX_DUMMY) with
      entries := k.entries.take i
      version := 0 }
    have hent : ∀ t, k'.entry t = if t = i then none else k.entry t := by
      intro t
      simp only [Keys.entry, k', List.getElem?_take]
      by_cases hlt : t < i
      · have : t ≠ i := by omega
        simp [hlt, this]
      · by_cases ht : t = i
        · simp [ht]
        · have := h4 t (by omega)
          simp only [Keys.entry] at this
          simp [hlt, ht, this]
    have hold : ∀ t e', k'.entry t = some e' → k.entry t = some e' := by
      intro t e' h
      rw [hent] at h
      by_cases ht : t = i
      · simp [ht] at h
      · simpa [ht] using h
    have hc : Chain k' := chain_remove k w.toChain i s hs h5 k' rfl rfl hent
    have hw : WF hf eqv P.isStr k' := {
      toChain := hc
      hashes := fun t e' h => w.hashes t e' (hold t e' h)
      uniq := fun i1 e1 i2 e2 a b c => w.uniq i1 e1 i2 e2 (hold i1 e1 a) (hold i2 e2 b) c
      strs := fun t e' hg h => w.strs t e' hg (hold t e' h)
      notSplit := w.notSplit
      load := by
        have hf1 := filled_set_filled k s DKIX_DUMMY hslt (by rw [h5]; simp [DKIX_EMPTY])
        have h2' : k'.filled = (k.setIndex s DKIX_DUMMY).filled := rfl
        have h3' : k'.usable = k.usable := rfl
        have h4' : k'.size = k.size := rfl
        have h5' := w.load
        rw [h3', h4']
        omega
      nent := by
        have hle : k'.nentries ≤ k.nentries := by
          simp only [k', Keys.nentries, List.length_take]
          omega
        have h3' : k'.usable = k.usable := rfl
        have h4' : k'.size = k.size := rfl
        have h5' := w.nent
        rw [h3', h4']
        omega
      usableNN := w.usableNN
      small := w.small }
    have hlive : liveEntries k' = (k.entries.take i).filterMap id := rfl
    refine ⟨(e.key, e.value), { mp with used := mp.used - 1, body := .combined k' }, ?_,
      ⟨⟨k', rfl, hw, ?_⟩⟩, ?_⟩
    · have hne0 : (mp.used == 0) = false := by simpa using h0
      simp only [dictPopitem, hne0, Bool.false_eq_true, if_false, hb, popLast, h1, h6]
      rw [if_neg (by omega)]
      simp only [Int.toNat_natCast]
      rfl
    · show mp.used - 1 = (liveEntries k').length
      have : (liveEntries k').length + 1 = (liveEntries k).length := by
        have h3' := congrArg List.length h3
        simp only [List.length_append, List.length_cons, List.length_nil] at h3'
        rw [hlive]
        omega
      omega
    · have hs : k.items = ((k.entries.take i).filterMap id).map (fun e => (e.key, e.value)) ++
          [(e.key, e.value)] := by
        simp only [Keys.items]
        rw [← h3]
        simp
      simp only [dictAssoc, hb]
      rw [hs]
      rfl

/-- Every read operation, from one lookup. -/
theorem dictGet_spec (H : Honest P hf eqv) (mp : PyDict K V)
    (hd : DictInv hf eqv P.isStr mp) (key : K) (dflt : V) :
    dictGet P key dflt mp = (.ok ((assocGet eqv (dictAssoc mp) key).getD dflt), mp) := by
  obtain ⟨ix, h1, h2, h3⟩ := lookup_assoc H mp hd key
  have hhash : hashKey P key mp = (.ok (hf key), mp) := by
    simp [hashKey, H.hash_ok, H.hash_quiet]
  simp only [dictGet, M.bind_run, hhash, h1]
  cases hq : assocGet eqv (dictAssoc mp) key with
  | none => simp
  | some v =>
    have := h3 v hq
    have hne : (ix == DKIX_EMPTY) = false := by
      simp [DKIX_EMPTY]
      omega
    simp [hne]

end

end PyLean.DictSet
