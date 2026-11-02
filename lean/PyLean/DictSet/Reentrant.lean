import PyLean.DictSet.Split

/-!
What survives an `__eq__` that mutates the dict.

Nothing about the answers can survive: such a comparison can make a lookup miss a key that is there,
and a lying one can put two equal keys in a table. What survives is what memory safety rests on.

`_Py_dict_lookup` re-checks `dk == mp->ma_keys && ep->me_key == startkey` after every comparison
(`dictobject.c:1062`, `:1198`). The first theorem here is what that check buys: an index the lookup
reports is one the table has when the lookup returns, for every key protocol, with no hypothesis.
The second is that the table's structure, `Chain` and its counts, survives `insertdict` and delete
when every comparison may run any mutation that keeps it, which is what the operations themselves do.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

section Valid

/-- The probe loop reports an index only if `check` accepted it, in the state the loop ends in. -/
theorem doLookup_valid {σ : Type} (getIx : σ → Nat → Int) (check : Nat → M σ Int)
    (W : σ → Nat → Prop) (hc : ∀ ix s c s', check ix s = (.ok c, s') → 0 < c → W s' ix) :
    ∀ (fuel mask i perturb : Nat) (s s' : σ) (r : Int),
      doLookup getIx check fuel mask i perturb s = (.ok r, s') → 0 ≤ r → W s' r.toNat := by
  intro fuel
  induction fuel with
  | zero =>
    intro mask i perturb s s' r h
    simp [doLookup, M.throw] at h
  | succ fuel ih =>
    intro mask i perturb s s' r h hr
    simp only [doLookup] at h
    split at h
    · split at h
      · simp at h
      · rename_i cmp s1 heq
        split at h
        · simp only [Prod.mk.injEq, Except.ok.injEq] at h
          omega
        · split at h
          · rename_i hne1 hne2
            simp only [Prod.mk.injEq, Except.ok.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hpos : 0 < cmp := by
              have : cmp ≠ 0 := by simpa using hne2
              omega
            exact hc _ _ _ _ heq hpos
          · exact ih _ _ _ _ _ _ h hr
    · split at h
      · simp only [Prod.mk.injEq, Except.ok.injEq] at h
        rw [← h.1] at hr
        exact absurd hr (by decide)
      · exact ih _ _ _ _ _ _ h hr

variable (P : Proto K (PyDict K V))

/-- `stillThere` is the check at `:1142` and `:1198`: it holds only of an entry the table has. -/
theorem stillThere_entry (mp : PyDict K V) (dk ix : Nat) (k : K) (h : stillThere mp dk ix k = true) :
    (mp.body.entryKH ix).isSome = true := by
  simp only [stillThere, Bool.and_eq_true] at h
  cases he : mp.body.entryKH ix with
  | none =>
    rw [he] at h
    simp at h
  | some x => rfl

theorem compareGeneric_valid (ix : Nat) (key : K) (hash c : Int) (mp s' : PyDict K V)
    (h : compareGeneric P ix key hash mp = (.ok c, s')) (hc : 0 < c) :
    (s'.body.entryKH ix).isSome = true := by
  simp only [compareGeneric] at h
  split at h
  · simp at h
  · rename_i epKey epHash he
    split at h
    · simp only [Prod.mk.injEq] at h
      rw [← h.2, he]
      rfl
    · split at h
      · split at h
        · simp at h
        · split at h
          · rename_i hs
            simp only [Prod.mk.injEq] at h
            rw [← h.2]
            exact stillThere_entry _ _ _ _ hs
          · simp only [Prod.mk.injEq, Except.ok.injEq] at h
            rw [← h.1] at hc
            exact absurd hc (by decide)
      · simp only [Prod.mk.injEq, Except.ok.injEq] at h
        rw [← h.1] at hc
        exact absurd hc (by decide)

theorem compareUnicodeGeneric_valid (ix : Nat) (key : K) (hash c : Int) (mp s' : PyDict K V)
    (h : compareUnicodeGeneric P ix key hash mp = (.ok c, s')) (hc : 0 < c) :
    (s'.body.entryKH ix).isSome = true := by
  simp only [compareUnicodeGeneric] at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp at h
      · split at h
        · rename_i hs
          simp only [Prod.mk.injEq] at h
          rw [← h.2]
          exact stillThere_entry _ _ _ _ hs
        · simp only [Prod.mk.injEq, Except.ok.injEq] at h
          rw [← h.1] at hc
          exact absurd hc (by decide)
    · simp only [Prod.mk.injEq, Except.ok.injEq] at h
      rw [← h.1] at hc
      exact absurd hc (by decide)

theorem checkUnicode_valid (key : K) (hash : Int) (ix : Nat) (c : Int) (s s' : PyDict K V)
    (h : checkUnicode P key hash ix s = (.ok c, s')) (hc : 0 < c) :
    (s'.body.entryKH ix).isSome = true := by
  simp only [checkUnicode, Prod.mk.injEq, Except.ok.injEq] at h
  obtain ⟨h1, rfl⟩ := h
  cases he : s.body.entryKH ix with
  | none =>
    simp [he, compareUnicodeUnicode] at h1
    omega
  | some x => rfl

/-- All three dispatch branches of the scan. -/
theorem scan_valid (key : K) (hash r : Int) (mp s : PyDict K V)
    (h : (if mp.body.kind != .general then
        if P.isStr key then
          doLookup bodyIx (checkUnicode P key hash) (probeFuel mp.body.log2Size) mp.body.mask
            (toU64 hash &&& mp.body.mask) (toU64 hash) mp
        else unicodekeysLookupGeneric P mp.body.mask (probeFuel mp.body.log2Size) key hash mp
      else dictkeysGenericLookup P mp.body.mask (probeFuel mp.body.log2Size) key hash mp) = (.ok r, s))
    (hr : 0 ≤ r) : (s.body.entryKH r.toNat).isSome = true := by
  split at h
  · split at h
    · exact doLookup_valid _ _ (fun s i => (s.body.entryKH i).isSome = true)
        (fun ix s c s' a b => checkUnicode_valid P key hash ix c s s' a b) _ _ _ _ _ _ _ h hr
    · simp only [unicodekeysLookupGeneric] at h
      exact doLookup_valid _ _ (fun s i => (s.body.entryKH i).isSome = true)
        (fun ix s c s' a b => compareUnicodeGeneric_valid P ix key hash c s s' a b) _ _ _ _ _ _ _ h hr
  · simp only [dictkeysGenericLookup] at h
    exact doLookup_valid _ _ (fun s i => (s.body.entryKH i).isSome = true)
      (fun ix s c s' a b => compareGeneric_valid P ix key hash c s s' a b) _ _ _ _ _ _ _ h hr

/-- `_Py_dict_lookup` never reports an index the table does not have, for every key protocol. -/
theorem dictLookupAux_valid (key : K) (hash : Int) :
    ∀ (n : Nat) (mp s : PyDict K V) (ix : Int) (v : Option V),
      dictLookupAux P key hash n mp = (.ok (ix, v), s) → 0 ≤ ix →
      (s.body.entryKH ix.toNat).isSome = true := by
  intro n
  induction n with
  | zero =>
    intro mp s ix v h
    simp [dictLookupAux, M.throw] at h
  | succ n ih =>
    intro mp s ix v h hix
    simp only [dictLookupAux] at h
    split at h
    · simp at h
    · rename_i r mp' heq
      split at h
      · exact ih _ _ _ _ h hix
      · simp only [Prod.mk.injEq, Except.ok.injEq] at h
        obtain ⟨⟨rfl, _⟩, rfl⟩ := h
        exact scan_valid P key hash r mp mp' heq hix

end Valid

/-- What the re-check after a comparison buys: for every key protocol, including an `__eq__` that
lies, raises, or changes the dict in any way, an index `_Py_dict_lookup` reports is one the table has
when it returns. -/
def LookupIndexValid : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (key : K) (hash : Int)
    (mp s : PyDict K V) (ix : Int) (v : Option V),
    dictLookup P key hash mp = (.ok (ix, v), s) → 0 ≤ ix → (s.body.entryKH ix.toNat).isSome = true
theorem lookupIndexValid_proven : LookupIndexValid := fun _ _ _ P key hash mp s ix v h hix =>
  dictLookupAux_valid P key hash restartFuel mp s ix v h hix

section Struct

/-- A keys object's structure: the chains and the counts, with nothing about keys, which a lying
`__eq__` can break. -/
structure KeysOK (k : Keys K V) : Prop extends Chain k where
  load : (k.filled : Int) + k.usable ≤ usableFraction k.size
  nent : (k.nentries : Int) + k.usable ≤ usableFraction k.size
  usableNN : 0 ≤ k.usable

/-- A combined dict with that structure. -/
def DictStruct (d : PyDict K V) : Prop :=
  ∃ k, d.body = .combined k ∧ KeysOK k ∧ d.used = (liveEntries k).length

theorem KeysOK.filled_lt {k : Keys K V} (w : KeysOK k) : k.filled < k.size := by
  have h1 := w.load
  have h2 := w.usableNN
  have h3 := usableFraction_lt k.size k.size_pos
  omega

theorem DictStruct.peer {d : PyDict K V} (h : DictStruct d) (p : Option (PeerDict K V)) :
    DictStruct { d with peer := p } :=
  let ⟨k, hb, w, hu⟩ := h
  ⟨k, hb, w, hu⟩

/-- `dictresize` of a combined table keeps the structure, whatever the keys are. -/
theorem dictResize_struct (mp : PyDict K V) (k : Keys K V) (hb : mp.body = .combined k)
    (hused : mp.used = (liveEntries k).length) (c : Chain k) (log2New : Nat)
    (hlt : log2New < 64) (hroom : mp.used ≤ usableFraction (2 ^ log2New)) (unicode : Bool) :
    ∃ k' : Keys K V, dictResize log2New unicode mp =
        (.ok (), { mp with nextId := mp.nextId + 1, body := .combined k' }) ∧
      KeysOK k' ∧ liveEntries k' = liveEntries k ∧
      k'.usable = (usableFraction (2 ^ log2New) : Int) - mp.used := by
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
  have hlive : liveEntries k' = liveEntries k := by
    simp [liveEntries, k']
  have hchain : Chain k' := by
    have hc := h2
    simp only [k0, newKeysObject, List.nil_append] at hc
    exact ⟨hc.len, hc.range, hc.inj, hc.reach⟩
  have hus : k'.usable = (usableFraction (2 ^ log2New) : Int) - mp.used := rfl
  refine ⟨k', ?_, ?_, hlive, hus⟩
  · simp only [dictResize]
    rw [if_neg (by omega)]
    simp only [hb, htake]
    have h1' : buildIndices (newKeysObject mp.nextId log2New u' : Keys K V).mask (probeFuel log2New)
        (newKeysObject mp.nextId log2New u' : Keys K V).indices 0
        ((liveEntries k).map (·.hash)) = .ok idx := h1
    simp only [u'] at h1'
    rw [h1']
  · refine { toChain := hchain, load := ?_, nent := ?_, usableNN := ?_ }
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

/-- `insertion_resize` keeps the structure, and on success there is room. -/
theorem insertionResize_struct (mp : PyDict K V) (hd : DictStruct mp) (unicode : Bool) :
    insertionResize unicode mp = (.error memoryError, mp) ∨
    ∃ s, insertionResize unicode mp = (.ok (), s) ∧ DictStruct s ∧ 0 < s.body.usable := by
  obtain ⟨k, hb, w, hu⟩ := hd
  simp only [insertionResize]
  by_cases hlt : calculateLog2Keysize (growthRate mp.used) < 64
  · right
    have hr := growth_room mp.used
    obtain ⟨k', h1, h2, h3, h4⟩ := dictResize_struct mp k hb hu w.toChain _ hlt (by omega) unicode
    refine ⟨_, h1, ⟨k', rfl, h2, ?_⟩, ?_⟩
    · rw [h3]
      exact hu
    · simp only [Body.usable]
      rw [h4]
      omega
  · left
    simp only [dictResize]
    rw [if_pos (by omega)]

/-- A resize that may or may not run keeps the structure. -/
theorem room_step (c : Bool) (u : Bool) (mp : PyDict K V) (hd : DictStruct mp) :
    (∃ e s, (if c = true then insertionResize u mp else ((.ok (), mp) : Py Unit × PyDict K V)) =
      (.error e, s) ∧ DictStruct s) ∨
    ∃ s, (if c = true then insertionResize u mp else ((.ok (), mp) : Py Unit × PyDict K V)) =
      (.ok (), s) ∧ DictStruct s ∧ (c = true → 0 < s.body.usable) := by
  cases c with
  | false =>
    right
    exact ⟨mp, by simp, hd, by simp⟩
  | true =>
    rcases insertionResize_struct mp hd u with h | ⟨s, h1, h2, h3⟩
    · left
      exact ⟨memoryError, mp, by simp [h], hd⟩
    · right
      exact ⟨s, by simp [h1], h2, fun _ => h3⟩

/-- `appendEntry` on a table with room keeps the structure, for any key and any hash. -/
theorem appendEntry_struct (k : Keys K V) (w : KeysOK k) (hus : 0 < k.usable) (key : K) (hash : Int)
    (v : V) :
    ∃ k' : Keys K V, appendEntry k key hash v = .ok k' ∧ KeysOK k' ∧
      liveEntries k' = liveEntries k ++ [⟨key, hash, v⟩] := by
  let e : Ent K V := ⟨key, hash, v⟩
  obtain ⟨j0, hj0, hemp⟩ := exists_stop k w.toChain (exists_empty k w.toChain w.filled_lt) hash
  have hw := probeUntil_walk (fun ix => !isUnusableSlot ix) k.indices k.mask (toU64 hash)
    (probeFuel k.log2Size) 0
    ⟨j0, by omega, by omega, by
      have : k.indices.getD (probeState k.mask (toU64 hash) j0).1 DKIX_EMPTY = DKIX_EMPTY := hemp
      rw [this]
      decide⟩
  obtain ⟨j, _, hj, hstop, hpre, hres⟩ := hw
  simp only [Nat.zero_add] at hj
  have hat : k.getIndex (k.pos hash j) < 0 := by
    have : (!isUnusableSlot (k.getIndex (k.pos hash j))) = true := hstop
    simpa [isUnusableSlot] using this
  have hslt : k.pos hash j < k.indices.length := by rw [w.len]; exact k.pos_lt _ _
  let k' : Keys K V := { (k.setIndex (k.pos hash j) k.nentries) with
    entries := k.entries ++ [some e]
    usable := k.usable - 1
    version := 0 }
  have hc' : Chain k' := chain_add k w.toChain e (k.pos hash j) j hj rfl hat
    (fun j' h => by
      have hb := hpre j' (by omega) h
      intro he
      apply hb
      have : k.indices.getD (probeState k.mask (toU64 hash) j').1 DKIX_EMPTY = DKIX_EMPTY := he
      rw [this]
      decide) k' rfl rfl rfl
  refine ⟨k', ?_, ?_, ?_⟩
  · simp only [appendEntry, findEmptySlot]
    have hr : probeUntil (fun ix => !isUnusableSlot ix) k.indices k.mask (probeFuel k.log2Size)
        (toU64 hash &&& k.mask) (toU64 hash) = .ok (k.pos hash j) := hres
    simp only [hr]
    rfl
  · refine { toChain := hc', load := ?_, nent := ?_, usableNN := ?_ }
    · have h1 := filled_set k (k.pos hash j) k.nentries hslt
      have h2 : k'.filled = (k.setIndex (k.pos hash j) k.nentries).filled := rfl
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
  · simp [liveEntries, k', e, List.filterMap_append]

/-- `insert_combined_dict`, for any key and hash: the table keeps its structure, and it is one
item ahead of `ma_used`, which `insertdict` then bumps. -/
theorem insertCombined_struct (KO : KeyOps K) (hash : Int) (key : K) (value : V) (mp : PyDict K V)
    (hd : DictStruct mp) :
    match insertCombinedDict KO hash key value mp with
    | (.ok _, s) => DictStruct { s with used := s.used + 1 }
    | (.error _, s) => DictStruct s := by
  simp only [insertCombinedDict]
  rcases room_step (mp.body.isUnicode && !KO.isStr key) false mp hd with ⟨e, s, h1, h2⟩ | ⟨mp1, h1, h2, _⟩
  · simp only [insertionResize] at h1
    rw [show (if (mp.body.isUnicode && !KO.isStr key) = true then insertionResize false mp else
        ((.ok (), mp) : Py Unit × PyDict K V)) = (.error e, s) from h1]
    exact h2
  · rw [show (if (mp.body.isUnicode && !KO.isStr key) = true then insertionResize false mp else
        ((.ok (), mp) : Py Unit × PyDict K V)) = (.ok (), mp1) from h1]
    simp only []
    rcases room_step (decide (mp1.body.usable ≤ 0)) true mp1 h2 with ⟨e, s, g1, g2⟩ | ⟨mp2, g1, g2, g3⟩
    · have : (if mp1.body.usable ≤ 0 then insertionResize true mp1 else
          ((.ok (), mp1) : Py Unit × PyDict K V)) = (.error e, s) := by
        simpa using g1
      rw [this]
      exact g2
    · have e2 : (if mp1.body.usable ≤ 0 then insertionResize true mp1 else
          ((.ok (), mp1) : Py Unit × PyDict K V)) = (.ok (), mp2) := by
        simpa using g1
      rw [e2]
      simp only []
      obtain ⟨k, hb, w, hu⟩ := g2
      have hpos : 0 < k.usable := by
        by_cases hz : mp1.body.usable ≤ 0
        · have := g3 (by simpa using hz)
          simpa [Body.usable, hb] using this
        · have hsame : mp2 = mp1 := by
            have : (if mp1.body.usable ≤ 0 then insertionResize true mp1 else
                ((.ok (), mp1) : Py Unit × PyDict K V)) = (.ok (), mp1) := by simp [hz]
            rw [this] at e2
            simpa using e2.symm
          have hb' : mp1.body = .combined k := by rw [← hsame]; exact hb
          simp only [Body.usable, hb'] at hz
          omega
      obtain ⟨k', a, b, c⟩ := appendEntry_struct k w hpos key hash value
      rw [hb]
      simp only [a]
      exact ⟨k', rfl, b, by simp [c, hu]⟩

omit [DecidableEq K] in
theorem length_set_some : ∀ (es : List (Option (Ent K V))) (ix : Nat) (e e' : Ent K V),
    es[ix]? = some (some e) →
    ((es.set ix (some e')).filterMap id).length = (es.filterMap id).length := by
  intro es
  induction es with
  | nil => intro ix e e' h; simp at h
  | cons a t ih =>
    intro ix e e' h
    cases ix with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp
    | succ ix =>
      simp only [List.getElem?_cons_succ] at h
      simp only [List.set_cons_succ, List.filterMap_cons]
      cases a with
      | none => simpa using ih ix e e' h
      | some b => simpa using ih ix e e' h

/-- Overwriting a value keeps the structure. -/
theorem storeValue_struct (value : V) (ix : Nat) (mp : PyDict K V) (hd : DictStruct mp) :
    DictStruct (storeValue value ix mp).2 := by
  obtain ⟨k, hb, w, hu⟩ := hd
  simp only [storeValue, hb]
  split
  · rename_i e he
    let k' : Keys K V := { k with entries := k.entries.set ix (some { e with value := value }) }
    have hent : ∀ t, ((k'.entry t).map (·.hash)) = (k.entry t).map (·.hash) := by
      intro t
      have hlt : ix < k.entries.length := (List.getElem?_eq_some_iff.mp he).1
      by_cases h : t = ix
      · subst h
        have h1 : (k.entries.set t (some { e with value := value }))[t]? =
            some (some { e with value := value }) := by simp [hlt]
        simp [Keys.entry, k', h1, he]
      · have h1 : (k.entries.set ix (some { e with value := value }))[t]? = k.entries[t]? :=
          List.getElem?_set_ne (fun x => h x.symm)
        simp [Keys.entry, k', h1]
    have hc := chain_setvalue k w.toChain k' rfl rfl hent
    have hn : k'.nentries = k.nentries := by simp [k', Keys.nentries]
    refine ⟨k', rfl, { toChain := hc, load := w.load, nent := ?_, usableNN := w.usableNN }, ?_⟩
    · rw [hn]
      exact w.nent
    · show mp.used = _
      rw [hu]
      exact (length_set_some k.entries ix e _ he).symm
  · exact ⟨k, hb, w, hu⟩

/-- The tail of `insertdict`, for any index and value the lookup gave. -/
theorem insertAfterLookup_struct (P : Proto K (PyDict K V)) (key : K) (hash : Int) (value : V)
    (ix : Int) (old : Option V) (mp : PyDict K V) (hd : DictStruct mp) :
    DictStruct (insertAfterLookup P key hash value ix old mp).2 := by
  simp only [insertAfterLookup]
  split
  · have h := insertCombined_struct P.toKeyOps hash key value mp hd
    split
    · rename_i a s heq
      rw [heq] at h
      exact h
    · rename_i e s heq
      rw [heq] at h
      exact h
  · exact storeValue_struct _ _ _ hd

section Keep
variable (P : Proto K (PyDict K V))

theorem doLookup_inv {σ : Type} (I : σ → Prop) (getIx : σ → Nat → Int) (check : Nat → M σ Int)
    (hc : ∀ ix s, I s → I (check ix s).2) :
    ∀ (fuel mask i perturb : Nat) (s : σ), I s → I (doLookup getIx check fuel mask i perturb s).2 := by
  intro fuel
  induction fuel with
  | zero => intro mask i perturb s hs; exact hs
  | succ fuel ih =>
    intro mask i perturb s hs
    simp only [doLookup]
    split
    · split
      · rename_i e s' heq
        have := hc (getIx s i).toNat s hs
        rw [heq] at this
        exact this
      · rename_i cmp s' heq
        have hs' : I s' := by
          have := hc (getIx s i).toNat s hs
          rw [heq] at this
          exact this
        split
        · exact hs'
        · split
          · exact hs'
          · exact ih _ _ _ _ hs'
    · split
      · exact hs
      · exact ih _ _ _ _ hs

variable (I : PyDict K V → Prop) (hp : ∀ a b s, I s → I (P.eq a b s).2)
include hp

theorem compareGeneric_inv (ix : Nat) (key : K) (hash : Int) (mp : PyDict K V) (hs : I mp) :
    I (compareGeneric P ix key hash mp).2 := by
  simp only [compareGeneric]
  rcases h : mp.body.entryKH ix with _ | ⟨epKey, epHash⟩
  · simp only [h]
    exact hs
  · simp only [h]
    split
    · exact hs
    · split
      · have h1 := hp epKey key mp hs
        split
        · rename_i e mp' heq
          rw [heq] at h1
          exact h1
        · rename_i b mp' heq
          rw [heq] at h1
          split <;> exact h1
      · exact hs

theorem compareUnicodeGeneric_inv (ix : Nat) (key : K) (hash : Int) (mp : PyDict K V) (hs : I mp) :
    I (compareUnicodeGeneric P ix key hash mp).2 := by
  simp only [compareUnicodeGeneric]
  rcases h : mp.body.entryKH ix with _ | ⟨epKey, epHash⟩
  · simp only [h]
    exact hs
  · simp only [h]
    split
    · have h1 := hp epKey key mp hs
      split
      · rename_i e mp' heq
        rw [heq] at h1
        exact h1
      · rename_i b mp' heq
        rw [heq] at h1
        split <;> exact h1
    · exact hs

theorem scan_inv (key : K) (hash : Int) (mp : PyDict K V) (hs : I mp) :
    I (if mp.body.kind != .general then
        if P.isStr key then
          doLookup bodyIx (checkUnicode P key hash) (probeFuel mp.body.log2Size) mp.body.mask
            (toU64 hash &&& mp.body.mask) (toU64 hash) mp
        else unicodekeysLookupGeneric P mp.body.mask (probeFuel mp.body.log2Size) key hash mp
      else dictkeysGenericLookup P mp.body.mask (probeFuel mp.body.log2Size) key hash mp).2 := by
  split
  · split
    · exact doLookup_inv I _ _ (fun ix s h => h) _ _ _ _ mp hs
    · simp only [unicodekeysLookupGeneric]
      exact doLookup_inv I _ _ (fun ix s h => compareUnicodeGeneric_inv P I hp ix key hash s h)
        _ _ _ _ mp hs
  · simp only [dictkeysGenericLookup]
    exact doLookup_inv I _ _ (fun ix s h => compareGeneric_inv P I hp ix key hash s h) _ _ _ _ mp hs

theorem dictLookupAux_inv (key : K) (hash : Int) :
    ∀ (n : Nat) (mp : PyDict K V), I mp → I (dictLookupAux P key hash n mp).2 := by
  intro n
  induction n with
  | zero => intro mp hs; exact hs
  | succ n ih =>
    intro mp hs
    simp only [dictLookupAux]
    have h1 := scan_inv P I hp key hash mp hs
    split
    · rename_i e mp' heq
      rw [heq] at h1
      exact h1
    · rename_i ix mp' heq
      rw [heq] at h1
      split
      · exact ih _ h1
      · exact h1

theorem dictLookup_inv (key : K) (hash : Int) (mp : PyDict K V) (hs : I mp) :
    I (dictLookup P key hash mp).2 :=
  dictLookupAux_inv P I hp key hash restartFuel mp hs

end Keep

/-- `*value_addr` is NULL on a negative index (:1365-1387). -/
theorem dictLookupAux_some (P : Proto K (PyDict K V)) (key : K) (hash : Int) :
    ∀ (n : Nat) (mp s : PyDict K V) (ix : Int) (v : V),
      dictLookupAux P key hash n mp = (.ok (ix, some v), s) → 0 ≤ ix := by
  intro n
  induction n with
  | zero =>
    intro mp s ix v h
    simp [dictLookupAux, M.throw] at h
  | succ n ih =>
    intro mp s ix v h
    simp only [dictLookupAux] at h
    split at h
    · simp at h
    · split at h
      · exact ih _ _ _ _ h
      · simp only [Prod.mk.injEq, Except.ok.injEq] at h
        obtain ⟨⟨rfl, h1⟩, _⟩ := h
        split at h1
        · omega
        · simp at h1

/-- `lookdict_index` reports only a slot that holds the index. -/
theorem lookdictLoop_found (indices : List Int) (mask index : Nat) :
    ∀ (fuel i p : Nat) (r : Int), lookdictIndexLoop indices mask index fuel i p = .ok r → 0 ≤ r →
      ∃ n : Nat, r = (n : Int) ∧ indices.getD n DKIX_EMPTY = (index : Int) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i p r h
    simp [lookdictIndexLoop] at h
  | succ fuel ih =>
    intro i p r h hr
    simp only [lookdictIndexLoop] at h
    split at h
    · rename_i he
      have h2 : ((i : Int)) = r := by simpa using h
      exact ⟨i, h2.symm, by simpa using he⟩
    · split at h
      · have h2 : DKIX_EMPTY = r := by simpa using h
        rw [← h2] at hr
        exact absurd hr (by decide)
      · exact ih _ _ _ h hr

/-- `delitem_common` keeps the structure, on any entry the table has. -/
theorem delitemCommon_struct (hash : Int) (ix : Nat) (mp : PyDict K V) (hd : DictStruct mp)
    (hent : (mp.body.entryKH ix).isSome = true) : DictStruct (delitemCommon hash ix mp).2 := by
  obtain ⟨k, hb, w, hu⟩ := hd
  have hex : ∃ e, k.entry ix = some e := by
    simp only [hb, Body.entryKH, Option.isSome_map] at hent
    exact Option.isSome_iff_exists.mp hent
  obtain ⟨e, he⟩ := hex
  have he' := (entry_iff k ix e).mp he
  simp only [delitemCommon, hb]
  split
  · exact ⟨k, hb, w, hu⟩
  · rename_i hashpos hl
    split
    · exact ⟨k, hb, w, hu⟩
    · rename_i hpos
      obtain ⟨n, hn, hg⟩ := lookdictLoop_found k.indices k.mask ix _ _ _ _ hl (by omega)
      have hin : n < k.indices.length := by
        by_cases hlt : n < k.indices.length
        · exact hlt
        · have : k.indices.getD n DKIX_EMPTY = DKIX_EMPTY := by
            simp [List.getD, List.getElem?_eq_none (show k.indices.length ≤ n by omega)]
          rw [this] at hg
          simp [DKIX_EMPTY] at hg
      have hgi : k.getIndex n = (ix : Int) := hg
      have hns : n < k.size := by rw [← w.len]; exact hin
      subst hn
      simp only [Int.toNat_natCast]
      let k' : Keys K V := { (k.setIndex n DKIX_DUMMY) with
        entries := k.entries.set ix none
        version := 0 }
      have hentry : ∀ t, k'.entry t = if t = ix then none else k.entry t := by
        intro t
        simp only [Keys.entry, k', List.getElem?_set]
        by_cases h : t = ix
        · subst h
          have hlt : t < k.entries.length := (List.getElem?_eq_some_iff.mp he').1
          simp [hlt]
        · have h' : ix ≠ t := fun x => h x.symm
          simp [h, h']
      have hc : Chain k' := chain_remove k w.toChain ix n hns hgi k' rfl rfl hentry
      have hlen := length_set_none k.entries ix e he'
      refine ⟨k', rfl, { toChain := hc, load := ?_, nent := ?_, usableNN := w.usableNN }, ?_⟩
      · have hf1 := filled_set_filled k n DKIX_DUMMY hin (by rw [hgi]; simp [DKIX_EMPTY])
        have h2' : k'.filled = (k.setIndex n DKIX_DUMMY).filled := rfl
        have h3 : k'.usable = k.usable := rfl
        have h4 : k'.size = k.size := rfl
        have h5 := w.load
        rw [h3, h4]
        omega
      · have h2' : k'.nentries = k.nentries := by simp [k', Keys.nentries]
        have h3 : k'.usable = k.usable := rfl
        have h4 : k'.size = k.size := rfl
        rw [h2', h3, h4]
        exact w.nent
      · have : (liveEntries k').length + 1 = (liveEntries k).length := hlen
        show mp.used - 1 = (liveEntries k').length
        omega

end Struct

/-- The structure of a combined table survives an `__eq__` that mutates: if every comparison keeps
it, whatever it answers and whether or not it raises, then so do `_Py_dict_lookup`, `insertdict`
and `_PyDict_DelItem_KnownHash`, on all their outcomes. -/
def StructSurvives : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)),
    (∀ a b s, DictStruct s → DictStruct (P.eq a b s).2) →
    ∀ (key : K) (hash : Int) (value : V) (d : PyDict K V), DictStruct d →
      DictStruct (dictLookup P key hash d).2 ∧
      DictStruct (insertDict P key hash value d).2 ∧
      DictStruct (dictDelItemKnownHash P key hash d).2

theorem structSurvives_proven : StructSurvives := by
  intro K V _ P hp key hash value d hd
  have hl := dictLookup_inv P DictStruct hp key hash d hd
  obtain ⟨k, hb, w, hu⟩ := id hd
  refine ⟨hl, ?_, ?_⟩
  · simp only [insertDict, hb]
    rcases hk : dictLookup P key hash d with ⟨a, s⟩
    rw [hk] at hl
    cases a with
    | error e => exact hl
    | ok r =>
      obtain ⟨ix, old⟩ := r
      exact insertAfterLookup_struct P key hash value ix old s hl
  · simp only [dictDelItemKnownHash]
    rcases hk : dictLookup P key hash d with ⟨a, s⟩
    rw [hk] at hl
    cases a with
    | error e => exact hl
    | ok r =>
      obtain ⟨ix, old⟩ := r
      cases old with
      | none => exact hl
      | some v =>
        simp only []
        split
        · exact hl
        · have hpos := dictLookupAux_some P key hash restartFuel d s ix v hk
          exact delitemCommon_struct hash ix.toNat s hl
            (dictLookupAux_valid P key hash restartFuel d s ix (some v) hk hpos)

/-- The hypothesis of `StructSurvives` is met by an `__eq__` that really mutates: one that clears the
dict it is probing, answering what it likes. -/
def StructHypMet : Prop :=
  ∀ (K V : Type) [DecidableEq K] (KO : KeyOps K) (answer : K → K → Bool),
    let P : Proto K (PyDict K V) := { KO with eq := fun a b s => (.ok (answer a b), dictClear s) }
    ∀ a b s, DictStruct s → DictStruct (P.eq a b s).2
theorem structHypMet_proven : StructHypMet := by
  intro K V _ KO answer P a b s hd
  obtain ⟨k, hb, w, hu⟩ := hd
  show DictStruct (dictClear s)
  simp only [dictClear, hb]
  split
  · exact ⟨k, hb, w, hu⟩
  · have hw : KeysOK (emptyKeys : Keys K V) :=
      have h := wf_empty (fun _ => (0 : Int)) (fun _ _ => false) (fun _ => false) (K := K) (V := V)
      { toChain := h.toChain, load := h.load, nent := h.nent, usableNN := h.usableNN }
    exact ⟨emptyKeys, rfl, hw, by simp [liveEntries, emptyKeys]⟩

end PyLean.DictSet
