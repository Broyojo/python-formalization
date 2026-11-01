import PyLean.DictSet.Refine

/-!
Mutation on the table, and the association list it stands for. `Keys.items` is the abstraction
function: live entries in `dk_entries` order. The theorems say that a table in a well-formed
state behaves as this list does, with insertion appending at the end and overwriting in place,
which is the insertion-order guarantee of the language.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

/-- The `(key, value)` pairs of a keys object, in entry order. -/
def Keys.items (k : Keys K V) : List (K × V) := (liveEntries k).map fun e => (e.key, e.value)

/-- `d[key] = v` on the list. -/
def assocSet (eqv : K → K → Bool) (l : List (K × V)) (key : K) (v : V) : List (K × V) :=
  if l.any (fun p => eqv p.1 key) then
    l.map fun p => if eqv p.1 key then (p.1, v) else p
  else l ++ [(key, v)]

/-- `del d[key]` on the list. -/
def assocDel (eqv : K → K → Bool) (l : List (K × V)) (key : K) : List (K × V) :=
  l.filter fun p => !eqv p.1 key

/-- `d[key]` on the list. -/
def assocGet (eqv : K → K → Bool) (l : List (K × V)) (key : K) : Option V :=
  (l.find? fun p => eqv p.1 key).map (·.2)

theorem entry_iff (k : Keys K V) (ix : Nat) (e : Ent K V) :
    k.entry ix = some e ↔ k.entries[ix]? = some (some e) := by
  simp only [Keys.entry]
  cases h : k.entries[ix]? with
  | none => simp
  | some x => simp

theorem mem_filterMap_id (es : List (Option (Ent K V))) (e : Ent K V) :
    e ∈ es.filterMap id ↔ ∃ ix : Nat, es[ix]? = some (some e) := by
  simp only [List.mem_filterMap, id]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨i, hi, hv⟩ := List.getElem_of_mem ha
    exact ⟨i, by simp [hi, hv]⟩
  · rintro ⟨ix, h⟩
    exact ⟨some e, List.mem_of_getElem? h, rfl⟩

theorem mem_live (k : Keys K V) (e : Ent K V) :
    e ∈ liveEntries k ↔ ∃ ix, k.entry ix = some e := by
  simp only [liveEntries, mem_filterMap_id, entry_iff]

theorem liveEntries_length_le (k : Keys K V) : (liveEntries k).length ≤ k.nentries := by
  simp only [liveEntries, Keys.nentries]
  exact List.length_filterMap_le _ _

section Lists
variable (eqv : K → K → Bool) (key : K)

private theorem no_match (t : List (Option (Ent K V)))
    (hu : ∀ (j : Nat) (e' : Ent K V), t[j]? = some (some e') → eqv e'.key key = true → False) :
    ∀ x ∈ t.filterMap id, eqv x.key key = false := by
  intro x hx
  obtain ⟨j, hj⟩ := (mem_filterMap_id t x).mp hx
  cases hq : eqv x.key key with
  | false => rfl
  | true => exact (hu j x hj hq).elim

theorem filterMap_set_value (v : V) :
    ∀ (es : List (Option (Ent K V))) (ix : Nat) (e : Ent K V),
      es[ix]? = some (some e) → eqv e.key key = true →
      (∀ (j : Nat) (e' : Ent K V), es[j]? = some (some e') → eqv e'.key key = true → j = ix) →
      ((es.set ix (some { e with value := v })).filterMap id).map (fun e => (e.key, e.value)) =
        ((es.filterMap id).map fun e => (e.key, e.value)).map
          fun p => if eqv p.1 key then (p.1, v) else p := by
  intro es
  induction es with
  | nil => intro ix e h; simp at h
  | cons a t ih =>
    intro ix e he heq hu
    cases ix with
    | zero =>
      have ha : a = some e := by simpa using he
      subst ha
      have hrest := no_match eqv key t fun j e' h1 h2 => by
        have := hu (j + 1) e' (by simpa using h1) h2
        omega
      simp only [List.set_cons_zero, List.filterMap_cons, id, List.map_cons, heq, if_true,
        List.cons.injEq, true_and, List.map_map]
      apply List.map_congr_left
      intro x hx
      simp [hrest x hx]
    | succ ix =>
      have he' : t[ix]? = some (some e) := by simpa using he
      have hu' : ∀ (j : Nat) (e' : Ent K V), t[j]? = some (some e') → eqv e'.key key = true → j = ix := by
        intro j e' h1 h2
        have := hu (j + 1) e' (by simpa using h1) h2
        omega
      have ih' := ih ix e he' heq hu'
      cases a with
      | none => simpa [List.set_cons_succ] using ih'
      | some e0 =>
        have hne : eqv e0.key key = false := by
          cases hq : eqv e0.key key with
          | false => rfl
          | true =>
            have := hu 0 e0 (by simp) hq
            omega
        simp only [List.set_cons_succ, List.filterMap_cons, id, List.map_cons, hne, if_false,
          Bool.false_eq_true]
        rw [ih']

theorem filterMap_set_none :
    ∀ (es : List (Option (Ent K V))) (ix : Nat) (e : Ent K V),
      es[ix]? = some (some e) → eqv e.key key = true →
      (∀ (j : Nat) (e' : Ent K V), es[j]? = some (some e') → eqv e'.key key = true → j = ix) →
      (es.set ix none).filterMap id = (es.filterMap id).filter fun x => !eqv x.key key := by
  intro es
  induction es with
  | nil => intro ix e h; simp at h
  | cons a t ih =>
    intro ix e he heq hu
    cases ix with
    | zero =>
      have ha : a = some e := by simpa using he
      subst ha
      have hrest := no_match eqv key t fun j e' h1 h2 => by
        have := hu (j + 1) e' (by simpa using h1) h2
        omega
      simp only [List.set_cons_zero, List.filterMap_cons, id, List.filter_cons, heq,
        Bool.not_true, Bool.false_eq_true, if_false]
      symm
      apply List.filter_eq_self.mpr
      intro x hx
      simp [hrest x hx]
    | succ ix =>
      have he' : t[ix]? = some (some e) := by simpa using he
      have hu' : ∀ (j : Nat) (e' : Ent K V), t[j]? = some (some e') → eqv e'.key key = true → j = ix := by
        intro j e' h1 h2
        have := hu (j + 1) e' (by simpa using h1) h2
        omega
      have ih' := ih ix e he' heq hu'
      cases a with
      | none => simpa [List.set_cons_succ] using ih'
      | some e0 =>
        have hne : eqv e0.key key = false := by
          cases hq : eqv e0.key key with
          | false => rfl
          | true =>
            have := hu 0 e0 (by simp) hq
            omega
        simp only [List.set_cons_succ, List.filterMap_cons, id, List.filter_cons, hne,
          Bool.not_false, if_true]
        rw [ih']

theorem pairwise_of_uniq :
    ∀ (es : List (Option (Ent K V))),
      (∀ (i1 : Nat) (e1 : Ent K V) (i2 : Nat) (e2 : Ent K V), es[i1]? = some (some e1) →
        es[i2]? = some (some e2) → eqv e1.key e2.key = true → i1 = i2) →
      (es.filterMap id).Pairwise fun a b => eqv a.key b.key = false := by
  intro es
  induction es with
  | nil => intro _; simp
  | cons a t ih =>
    intro hu
    have hu' : ∀ (i1 : Nat) (e1 : Ent K V) (i2 : Nat) (e2 : Ent K V), t[i1]? = some (some e1) →
        t[i2]? = some (some e2) → eqv e1.key e2.key = true → i1 = i2 := by
      intro i1 e1 i2 e2 h1 h2 h3
      have := hu (i1 + 1) e1 (i2 + 1) e2 (by simpa using h1) (by simpa using h2) h3
      omega
    cases a with
    | none => simpa using ih hu'
    | some e0 =>
      simp only [List.filterMap_cons, id]
      refine List.pairwise_cons.mpr ⟨?_, ih hu'⟩
      intro b hb
      obtain ⟨j, hj⟩ := (mem_filterMap_id t b).mp hb
      cases hq : eqv e0.key b.key with
      | false => rfl
      | true =>
        have := hu 0 e0 (j + 1) b (by simp) (by simpa using hj) hq
        omega

theorem uniq_of_pairwise (hsym : ∀ a b, eqv a b = eqv b a) (l : List (Ent K V))
    (hp : l.Pairwise fun a b => eqv a.key b.key = false)
    (i1 i2 : Nat) (e1 e2 : Ent K V) (h1 : l[i1]? = some e1) (h2 : l[i2]? = some e2)
    (h3 : eqv e1.key e2.key = true) : i1 = i2 := by
  obtain ⟨hl1, rfl⟩ := List.getElem?_eq_some_iff.mp h1
  obtain ⟨hl2, rfl⟩ := List.getElem?_eq_some_iff.mp h2
  have hp' := List.pairwise_iff_getElem.mp hp
  apply Classical.byContradiction
  intro hne
  by_cases hlt : i1 < i2
  · have := hp' i1 i2 hl1 hl2 hlt
    rw [this] at h3
    exact absurd h3 (by simp)
  · have hlt' : i2 < i1 := by omega
    have := hp' i2 i1 hl2 hl1 hlt'
    rw [hsym] at this
    rw [this] at h3
    exact absurd h3 (by simp)

/-- The scan of `dict_popitem_impl`. -/
theorem lastLive_spec (es : List (Option (Ent K V))) (n : Nat) (hn : n ≤ es.length) :
    (lastLive es n = none ∧ (es.take n).filterMap id = []) ∨
    (∃ i e, i < n ∧ lastLive es n = some (i, e) ∧ es[i]? = some (some e) ∧
      (es.take n).filterMap id = (es.take i).filterMap id ++ [e]) := by
  induction n with
  | zero => exact Or.inl ⟨rfl, by simp⟩
  | succ n ih =>
    have hlt : n < es.length := by omega
    have hget : es[n]? = some es[n] := List.getElem?_eq_getElem hlt
    have htake : es.take (n + 1) = es.take n ++ [es[n]] := by
      rw [List.take_succ, hget]
      rfl
    have hl : lastLive es (n + 1) = match es[n]? with
        | some (some e) => some (n, e)
        | _ => lastLive es n := rfl
    cases hv : es[n] with
    | some e =>
      have h' : es[n]? = some (some e) := by rw [hget, hv]
      refine Or.inr ⟨n, e, by omega, ?_, h', ?_⟩
      · rw [hl, h']
      · rw [htake, hv]; simp
    | none =>
      have h' : es[n]? = some none := by rw [hget, hv]
      rcases ih (by omega) with ⟨h1, h2⟩ | ⟨i, e, h1, h2, h3, h4⟩
      · refine Or.inl ⟨?_, ?_⟩
        · rw [hl, h']; exact h1
        · rw [htake, hv]; simp [h2]
      · refine Or.inr ⟨i, e, by omega, ?_, h3, ?_⟩
        · rw [hl, h']; exact h2
        · rw [htake, hv]; simp [h4]

/-- `lastLive_spec`, and nothing live above the entry it finds. -/
theorem lastLive_above (es : List (Option (Ent K V))) (n : Nat) (hn : n ≤ es.length) :
    (lastLive es n = none ∧ (es.take n).filterMap id = []) ∨
    (∃ i e, i < n ∧ lastLive es n = some (i, e) ∧ es[i]? = some (some e) ∧
      (es.take n).filterMap id = (es.take i).filterMap id ++ [e] ∧
      ∀ t, i < t → t < n → ∀ e', es[t]? ≠ some (some e')) := by
  induction n with
  | zero => exact Or.inl ⟨rfl, by simp⟩
  | succ n ih =>
    have hlt : n < es.length := by omega
    have hget : es[n]? = some es[n] := List.getElem?_eq_getElem hlt
    have htake : es.take (n + 1) = es.take n ++ [es[n]] := by
      rw [List.take_succ, hget]
      rfl
    have hl : lastLive es (n + 1) = match es[n]? with
        | some (some e) => some (n, e)
        | _ => lastLive es n := rfl
    cases hv : es[n] with
    | some e =>
      have h' : es[n]? = some (some e) := by rw [hget, hv]
      refine Or.inr ⟨n, e, by omega, ?_, h', ?_, fun t a b => by omega⟩
      · rw [hl, h']
      · rw [htake, hv]; simp
    | none =>
      have h' : es[n]? = some none := by rw [hget, hv]
      rcases ih (by omega) with ⟨h1, h2⟩ | ⟨i, e, h1, h2, h3, h4, h5⟩
      · refine Or.inl ⟨?_, ?_⟩
        · rw [hl, h']; exact h1
        · rw [htake, hv]; simp [h2]
      · refine Or.inr ⟨i, e, by omega, ?_, h3, ?_, ?_⟩
        · rw [hl, h']; exact h2
        · rw [htake, hv]; simp [h4]
        · intro t a b e'
          by_cases ht : t = n
          · subst ht
            rw [h']
            simp
          · exact h5 t a (by omega) e'

end Lists

theorem chain_new (id log2 : Nat) (unicode : Bool) :
    Chain (newKeysObject id log2 unicode : Keys K V) := by
  have hidx : ∀ i, (newKeysObject id log2 unicode : Keys K V).getIndex i = DKIX_EMPTY := by
    intro i
    simp only [Keys.getIndex, newKeysObject, List.getD]
    by_cases h : i < 2 ^ log2 <;> simp [h]
  refine ⟨by simp [newKeysObject, Keys.size], fun i _ => Or.inl (hidx i), ?_, ?_⟩
  · intro i j ix _ _ h1 _
    rw [hidx] at h1
    simp [DKIX_EMPTY] at h1
  · intro ix e h
    simp [Keys.entry, newKeysObject] at h

theorem chain_empty : Chain (emptyKeys : Keys K V) := by
  have hidx : ∀ i, (emptyKeys : Keys K V).getIndex i = DKIX_EMPTY := by
    intro i
    cases i with
    | zero => simp [Keys.getIndex, emptyKeys, List.getD]
    | succ i => simp [Keys.getIndex, emptyKeys, List.getD]
  refine ⟨by simp [emptyKeys, Keys.size], fun i _ => Or.inl (hidx i), ?_, ?_⟩
  · intro i j ix _ _ h1 _
    rw [hidx] at h1
    simp [DKIX_EMPTY] at h1
  · intro ix e h
    simp [Keys.entry, emptyKeys] at h

/-- `build_indices_*`: adding `es` to a chained table, each at the first empty slot. -/
theorem build_spec : ∀ (es : List (Ent K V)) (k : Keys K V), Chain k →
    k.filled + es.length ≤ k.size →
    ∃ idx, buildIndices k.mask (probeFuel k.log2Size) k.indices k.nentries (es.map (·.hash)) = .ok idx ∧
      Chain { k with indices := idx, entries := k.entries ++ es.map some } ∧
      ({ k with indices := idx } : Keys K V).filled ≤ k.filled + es.length := by
  intro es
  induction es with
  | nil =>
    intro k hc _
    refine ⟨k.indices, rfl, by simpa using hc, by simp⟩
  | cons e rest ih =>
    intro k hc hroom
    simp only [List.length_cons] at hroom
    obtain ⟨j0, hj0, hemp⟩ := exists_stop k hc (exists_empty k hc (by omega)) e.hash
    have hw := probeUntil_walk (fun v => v == DKIX_EMPTY) k.indices k.mask (toU64 e.hash)
      (probeFuel k.log2Size) 0
      ⟨j0, by omega, by omega, by
        simpa [Keys.getIndex, Keys.pos] using hemp⟩
    obtain ⟨j, _, hj, hstop, hpre, hres⟩ := hw
    have hsj : (probeState k.mask (toU64 e.hash) j).1 = k.pos e.hash j := rfl
    rw [hsj] at hstop hres
    simp only [Nat.zero_add] at hj
    have hat : k.getIndex (k.pos e.hash j) = DKIX_EMPTY := by
      simpa [Keys.getIndex] using hstop
    let k1 : Keys K V := { k with
      indices := k.indices.set (k.pos e.hash j) k.nentries
      entries := k.entries ++ [some e] }
    have hc1 : Chain k1 := chain_add k hc e (k.pos e.hash j) j hj rfl
      (by rw [hat]; simp [DKIX_EMPTY])
      (fun j' h => by
        have := hpre j' (by omega) h
        simpa [Keys.getIndex, Keys.pos] using this)
      k1 rfl rfl rfl
    have hf1 : k1.filled ≤ k.filled + 1 := by
      have := filled_set k (k.pos e.hash j) k.nentries (by rw [hc.len]; exact k.pos_lt _ _)
      simpa [Keys.setIndex, Keys.filled, k1] using this
    obtain ⟨idx, h1, h2, h3⟩ := ih k1 hc1 (by
      have : k1.size = k.size := rfl
      omega)
    refine ⟨idx, ?_, ?_, ?_⟩
    · have hn : k1.nentries = k.nentries + 1 := by simp [k1, Keys.nentries]
      simp only [List.map_cons, buildIndices]
      have hr : probeUntil (fun v => v == DKIX_EMPTY) k.indices k.mask (probeFuel k.log2Size)
          (toU64 e.hash &&& k.mask) (toU64 e.hash) = .ok (k.pos e.hash j) := hres
      simp only [hr]
      have hmask : k1.mask = k.mask := rfl
      have hlog : k1.log2Size = k.log2Size := rfl
      rw [hn, hmask, hlog] at h1
      exact h1
    · have : ({ k1 with indices := idx, entries := k1.entries ++ rest.map some } : Keys K V)
          = { k with indices := idx, entries := k.entries ++ (e :: rest).map some } := by
        simp [k1]
      rw [← this]
      exact h2
    · have : ({ k1 with indices := idx } : Keys K V).filled = ({ k with indices := idx } : Keys K V).filled := rfl
      simp only [List.length_cons]
      omega

section Ops
variable {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}

/-- `dictresize` of a combined table keeps the live entries in order and rebuilds the index table
from them; every dummy disappears. This is why a resize cannot reorder a dict. -/
theorem dictResize_spec (H : Honest P hf eqv) (mp : PyDict K V) (k : Keys K V)
    (hb : mp.body = .combined k) (w : WF hf eqv P.isStr k)
    (hused : mp.used = (liveEntries k).length) (log2New : Nat) (hlt : log2New < 64)
    (hroom : mp.used ≤ usableFraction (2 ^ log2New)) (unicode : Bool) :
    ∃ k' : Keys K V, dictResize log2New unicode mp =
        (.ok (), { mp with nextId := mp.nextId + 1, body := .combined k' }) ∧
      WF hf eqv P.isStr k' ∧ liveEntries k' = liveEntries k ∧ k'.log2Size = log2New ∧
      k'.usable = (usableFraction (2 ^ log2New) : Int) - mp.used ∧
      (k'.kind = .general ∨ k.kind ≠ .general ∧ k'.kind = .unicode) ∧
      (unicode = false → k'.kind = .general) := by
  let u' := if (Body.combined k : Body K V).isUnicode then unicode else false
  let k0 : Keys K V := newKeysObject mp.nextId log2New u'
  have hk0 : Chain k0 := chain_new _ _ _
  have hf0 : k0.filled = 0 := by
    simp [Keys.filled, k0, newKeysObject, List.countP_replicate, DKIX_EMPTY]
  have hsz0 : k0.size = 2 ^ log2New := rfl
  have hroom' : (liveEntries k).length ≤ k0.size := by
    have := usableFraction_lt (2 ^ log2New) (Nat.pow_pos (by omega))
    rw [hsz0]
    omega
  obtain ⟨idx, h1, h2, h3⟩ := build_spec (liveEntries k) k0 hk0 (by omega)
  have htake : (liveEntries k).take mp.used = liveEntries k := by rw [hused]; simp
  let k' : Keys K V := { k0 with
    indices := idx
    entries := (liveEntries k).map some
    usable := k0.usable - mp.used }
  have hentries : (k'.entries) = (liveEntries k).map some := rfl
  have hent : ∀ ix e, k'.entry ix = some e → (liveEntries k)[ix]? = some e := by
    intro ix e h
    have := (entry_iff k' ix e).mp h
    rw [hentries] at this
    simpa using this
  have hlive : liveEntries k' = liveEntries k := by
    simp [liveEntries, k']
  have hpair := pairwise_of_uniq eqv k.entries
    (fun i1 e1 i2 e2 h1 h2 h3 =>
      w.uniq i1 e1 i2 e2 ((entry_iff k i1 e1).mpr h1) ((entry_iff k i2 e2).mpr h2) h3)
  have hmem : ∀ ix e, k'.entry ix = some e → e ∈ liveEntries k := by
    intro ix e h
    exact List.mem_of_getElem? (hent ix e h)
  have hchain : Chain k' := by
    have hc := h2
    simp only [k0, newKeysObject, List.nil_append] at hc
    exact ⟨hc.len, hc.range, hc.inj, hc.reach⟩
  have hkind : k'.kind = if u' then .unicode else .general := rfl
  have hunicode : u' = true → k.kind ≠ .general := by
    intro h
    simp only [u'] at h
    split at h
    · rename_i hu
      simpa [Body.isUnicode, Body.kind] using hu
    · exact absurd h (by simp)
  have hU : (k'.size : Nat) = 2 ^ log2New := rfl
  have hus : k'.usable = (usableFraction (2 ^ log2New) : Int) - mp.used := rfl
  refine ⟨k', ?_, ?_, hlive, rfl, hus, ?_, ?_⟩
  · simp only [dictResize]
    rw [if_neg (by omega)]
    simp only [hb, htake]
    have h1' : buildIndices (newKeysObject mp.nextId log2New u' : Keys K V).mask (probeFuel log2New)
        (newKeysObject mp.nextId log2New u' : Keys K V).indices 0
        ((liveEntries k).map (·.hash)) = .ok idx := h1
    simp only [u'] at h1'
    rw [h1']
  · refine { toChain := hchain, hashes := ?_, uniq := ?_, strs := ?_, notSplit := ?_, load := ?_,
             nent := ?_, usableNN := ?_ }
    · intro ix e h
      obtain ⟨t, ht⟩ := (mem_live k e).mp (hmem ix e h)
      exact w.hashes t e ht
    · intro i1 e1 i2 e2 a b c
      exact uniq_of_pairwise eqv H.symm _ hpair i1 i2 e1 e2 (hent i1 e1 a) (hent i2 e2 b) c
    · intro ix e hg h
      obtain ⟨t, ht⟩ := (mem_live k e).mp (hmem ix e h)
      have hu : u' = true := by
        rw [hkind] at hg
        cases hq : u' with
        | true => rfl
        | false => simp [hq] at hg
      exact w.strs t e (hunicode hu) ht
    · rw [hkind]
      cases u' <;> simp
    · have : k'.filled ≤ (liveEntries k).length := by
        have h3' : ({ k0 with indices := idx } : Keys K V).filled ≤ 0 + (liveEntries k).length := by
          rw [hf0] at h3
          exact h3
        simpa [Keys.filled, k'] using h3'
      rw [hus]
      have hsz : k'.size = 2 ^ log2New := rfl
      rw [hsz]
      omega
    · have : k'.nentries = (liveEntries k).length := by simp [Keys.nentries, k']
      rw [hus, this]
      have hsz : k'.size = 2 ^ log2New := rfl
      rw [hsz]
      omega
    · rw [hus]
      omega
  · rw [hkind]
    cases hq : u' with
    | false => exact Or.inl (by simp)
    | true => exact Or.inr ⟨hunicode hq, by simp⟩
  · intro hun
    rw [hkind]
    have : u' = false := by
      simp only [u', hun]
      split <;> rfl
    simp [this]

theorem bitLength_gt (n : Nat) : n < 2 ^ bitLength n := by
  unfold bitLength
  split
  · omega
  · exact Nat.lt_log2_self

/-- The table `calculate_log2_keysize` picks has room for three times `used`, at least 8 slots. -/
theorem calculateLog2_room (m : Nat) : max m 8 ≤ 2 ^ calculateLog2Keysize m := by
  have e : calculateLog2Keysize m = bitLength (max m 8 - 1) := rfl
  have h := bitLength_gt (max m 8 - 1)
  rw [e]
  omega

theorem growth_room (used : Nat) :
    used < usableFraction (2 ^ calculateLog2Keysize (growthRate used)) := by
  have h := calculateLog2_room (growthRate used)
  simp only [usableFraction, Nat.shiftLeft_eq, Nat.pow_one]
  generalize 2 ^ calculateLog2Keysize (growthRate used) = S at *
  simp only [growthRate] at h
  omega

/-- `insertion_resize`: either `MemoryError` with nothing changed, or a table with room. -/
theorem insertionResize_spec (H : Honest P hf eqv) (mp : PyDict K V) (k : Keys K V)
    (hb : mp.body = .combined k) (w : WF hf eqv P.isStr k)
    (hused : mp.used = (liveEntries k).length) (unicode : Bool) :
    insertionResize unicode mp = (.error memoryError, mp) ∨
    ∃ k' : Keys K V, insertionResize unicode mp =
        (.ok (), { mp with nextId := mp.nextId + 1, body := .combined k' }) ∧
      WF hf eqv P.isStr k' ∧ liveEntries k' = liveEntries k ∧ 0 < k'.usable ∧
      (k'.kind = .general ∨ k.kind ≠ .general ∧ k'.kind = .unicode) ∧
      (unicode = false → k'.kind = .general) := by
  simp only [insertionResize]
  by_cases hlt : calculateLog2Keysize (growthRate mp.used) < 64
  · right
    have hr := growth_room mp.used
    obtain ⟨k', h1, h2, h3, _, h5, h6, h7⟩ := dictResize_spec H mp k hb w hused _ hlt (by omega) unicode
    refine ⟨k', h1, h2, h3, ?_, h6, h7⟩
    rw [h5]
    omega
  · left
    simp only [dictResize]
    rw [if_pos (by omega)]

/-- `appendEntry` on a table with room, for a key that is not in it. -/
theorem appendEntry_spec (H : Honest P hf eqv) (k : Keys K V) (w : WF hf eqv P.isStr k)
    (hus : 0 < k.usable) (key : K) (v : V)
    (hno : ∀ ix e, k.entry ix = some e → eqv e.key key = false)
    (hstr : k.kind ≠ .general → P.isStr key = true) :
    ∃ k' : Keys K V, appendEntry k key (hf key) v = .ok k' ∧ WF hf eqv P.isStr k' ∧
      liveEntries k' = liveEntries k ++ [⟨key, hf key, v⟩] ∧ k'.log2Size = k.log2Size ∧
      k'.kind = k.kind := by
  let e : Ent K V := ⟨key, hf key, v⟩
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
  let k' : Keys K V := { (k.setIndex (k.pos (hf key) j) k.nentries) with
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
  refine ⟨k', ?_, ?_, ?_, rfl, rfl⟩
  · simp only [appendEntry, findEmptySlot]
    have hr : probeUntil (fun ix => !isUnusableSlot ix) k.indices k.mask (probeFuel k.log2Size)
        (toU64 (hf key) &&& k.mask) (toU64 (hf key)) = .ok (k.pos (hf key) j) := hres
    simp only [hr]
    rfl
  · refine { toChain := hc', hashes := ?_, uniq := ?_, strs := ?_, notSplit := w.notSplit, load := ?_,
             nent := ?_, usableNN := ?_ }
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
    · have h2 : k'.nentries = k.nentries + 1 := by simp [k', Keys.nentries]
      have h3 : k'.usable = k.usable - 1 := rfl
      have h4 : k'.size = k.size := rfl
      have h5 := w.nent
      rw [h2, h3, h4]
      omega
    · have h3 : k'.usable = k.usable - 1 := rfl
      rw [h3]
      omega
  · simp [liveEntries, k', e]

end Ops

end PyLean.DictSet
