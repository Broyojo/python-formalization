import PyLean.DictSet.Table
import PyLean.DictSet.Probe

/-!
The index-table invariant of a compact dict, and the loops over the probe sequence.

`Chain k` says: `dk_indices` has `dk_size` slots; a slot is empty, dummy or names a live entry;
no two slots name the same entry; and every live entry sits on the probe sequence of its hash
with no empty slot before it. The last clause is what makes lookup correct, and it is why a
deleted slot must stay `DKIX_DUMMY` rather than go back to `DKIX_EMPTY`.

The invariant mentions nothing about keys, so it also holds of the shared keys of a split table.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type}

namespace Keys

/-- The `j`-th slot on the probe sequence of `h`. -/
def pos (k : Keys K V) (h : Int) (j : Nat) : Nat := (probeState k.mask (toU64 h) j).1

/-- How many slots are not `DKIX_EMPTY`: what bounds the load, since dummies count. -/
def filled (k : Keys K V) : Nat := k.indices.countP (· != DKIX_EMPTY)

end Keys

structure Chain (k : Keys K V) : Prop where
  len : k.indices.length = k.size
  range : ∀ i, i < k.size → k.getIndex i = DKIX_EMPTY ∨ k.getIndex i = DKIX_DUMMY ∨
    ∃ (ix : Nat) (e : Ent K V), k.getIndex i = (ix : Int) ∧ k.entry ix = some e
  inj : ∀ (i j ix : Nat), i < k.size → j < k.size →
    k.getIndex i = (ix : Int) → k.getIndex j = (ix : Int) → i = j
  reach : ∀ (ix : Nat) (e : Ent K V), k.entry ix = some e →
    ∃ j, j < probeFuel k.log2Size ∧ k.getIndex (k.pos e.hash j) = (ix : Int) ∧
      ∀ j', j' < j → k.getIndex (k.pos e.hash j') ≠ DKIX_EMPTY

theorem Keys.pos_lt (k : Keys K V) (h : Int) (j : Nat) : k.pos h j < k.size :=
  probe_lt k.log2Size (toU64 h) j

theorem Keys.pos_zero (k : Keys K V) (h : Int) : k.pos h 0 = toU64 h &&& k.mask := rfl

/-- Some slot is empty as soon as fewer slots are filled than exist. -/
theorem exists_empty (k : Keys K V) (hc : Chain k) (h : k.filled < k.size) :
    ∃ i, i < k.size ∧ k.getIndex i = DKIX_EMPTY := by
  apply Classical.byContradiction
  intro hn
  have hall : ∀ v ∈ k.indices, (v != DKIX_EMPTY) = true := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    have hi' : i < k.size := hc.len ▸ hi
    simp only [bne_iff_ne, ne_eq]
    intro he
    exact hn ⟨i, hi', by simp [Keys.getIndex, List.getD, hi, he]⟩
  have := List.countP_eq_length.mpr hall
  simp only [Keys.filled] at h
  rw [this, hc.len] at h
  exact absurd h (Nat.lt_irrefl _)

/-- An empty slot is met on every probe sequence. -/
theorem exists_stop (k : Keys K V) (hc : Chain k) (hfree : ∃ i, i < k.size ∧ k.getIndex i = DKIX_EMPTY)
    (h : Int) : ∃ j, j < probeFuel k.log2Size ∧ k.getIndex (k.pos h j) = DKIX_EMPTY := by
  obtain ⟨i, hi, he⟩ := hfree
  obtain ⟨j, hj, hp⟩ := probe_reaches_all k.log2Size (toU64 h) i (toU64_lt h) hi
  refine ⟨j, ?_, ?_⟩
  · simp only [probeFuel]; omega
  · have : k.pos h j = i := hp
    rw [this, he]

section Walk
variable {σ : Type}

/-- The search loop over the probe sequence. `Hit j` is where it stops: an empty slot, or an entry
that `c` accepts. It finds the first hit, and if `check` is pure it does nothing else. -/
theorem doLookup_walk (getIx : σ → Nat → Int) (check : Nat → M σ Int) (s : σ) (mask u : Nat)
    (c : Nat → Bool)
    (idx : Nat → Int) (hidx : ∀ j, idx j = getIx s (probeState mask u j).1)
    (hck : ∀ j, idx j ≥ 0 → check (idx j).toNat s = (.ok (if c (idx j).toNat then 1 else 0), s)) :
    ∀ fuel t, (∃ j, t ≤ j ∧ j < t + fuel ∧ (idx j = DKIX_EMPTY ∨ (idx j ≥ 0 ∧ c (idx j).toNat))) →
      ∃ j, t ≤ j ∧ j < t + fuel ∧ (idx j = DKIX_EMPTY ∨ (idx j ≥ 0 ∧ c (idx j).toNat)) ∧
        (∀ j', t ≤ j' → j' < j → ¬(idx j' = DKIX_EMPTY ∨ (idx j' ≥ 0 ∧ c (idx j').toNat))) ∧
        doLookup getIx check fuel mask (probeState mask u t).1 (probeState mask u t).2 s
          = (.ok (idx j), s) := by
  intro fuel
  induction fuel with
  | zero =>
    intro t ⟨j, h1, h2, _⟩
    omega
  | succ fuel ih =>
    intro t hex
    have hnext : ∀ (hnh : ¬(idx t = DKIX_EMPTY ∨ (idx t ≥ 0 ∧ c (idx t).toNat))),
        ∃ j, t + 1 ≤ j ∧ j < t + 1 + fuel ∧
          (idx j = DKIX_EMPTY ∨ (idx j ≥ 0 ∧ c (idx j).toNat)) := by
      intro hnh
      obtain ⟨j, h1, h2, h3⟩ := hex
      refine ⟨j, ?_, by omega, h3⟩
      have : j ≠ t := fun e => hnh (e ▸ h3)
      omega
    have step : probeStep mask (probeState mask u t).1 (probeState mask u t).2
        = probeState mask u (t + 1) := rfl
    by_cases hpos : idx t ≥ 0
    · have hck' := hck t hpos
      by_cases hc : c (idx t).toNat
      · refine ⟨t, by omega, by omega, Or.inr ⟨hpos, hc⟩, fun j' h1 h2 => by omega, ?_⟩
        simp only [doLookup]
        rw [← hidx t]
        simp [hpos, hck', hc]
      · have hnh : ¬(idx t = DKIX_EMPTY ∨ (idx t ≥ 0 ∧ c (idx t).toNat)) := by
          intro h
          rcases h with h | h
          · simp [DKIX_EMPTY] at h; omega
          · exact hc h.2
        obtain ⟨j, h1, h2, h3, h4, h5⟩ := ih (t + 1) (hnext hnh)
        refine ⟨j, by omega, by omega, h3, ?_, ?_⟩
        · intro j' a b
          by_cases e : j' = t
          · subst e; exact hnh
          · exact h4 j' (by omega) b
        · simp only [doLookup]
          rw [← hidx t]
          simp only [hpos, ge_iff_le, if_true, hck', hc, step]
          simpa using h5
    · by_cases he : idx t = DKIX_EMPTY
      · refine ⟨t, by omega, by omega, Or.inl he, fun j' h1 h2 => by omega, ?_⟩
        simp only [doLookup]
        rw [← hidx t]
        simp [he, DKIX_EMPTY]
      · have hnh : ¬(idx t = DKIX_EMPTY ∨ (idx t ≥ 0 ∧ c (idx t).toNat)) := by
          intro h
          rcases h with h | h
          · exact he h
          · exact hpos h.1
        obtain ⟨j, h1, h2, h3, h4, h5⟩ := ih (t + 1) (hnext hnh)
        refine ⟨j, by omega, by omega, h3, ?_, ?_⟩
        · intro j' a b
          by_cases e : j' = t
          · subst e; exact hnh
          · exact h4 j' (by omega) b
        · simp only [doLookup]
          rw [← hidx t]
          have he' : (idx t == DKIX_EMPTY) = false := by simpa using he
          simp only [hpos, if_false, he', Bool.false_eq_true, step]
          exact h5

/-- `probeUntil` stops at the first slot satisfying `stop`, if there is one in reach. -/
theorem probeUntil_walk (stop : Int → Bool) (indices : List Int) (mask u : Nat) :
    ∀ fuel t, (∃ j, t ≤ j ∧ j < t + fuel ∧ stop (indices.getD (probeState mask u j).1 DKIX_EMPTY)) →
      ∃ j, t ≤ j ∧ j < t + fuel ∧ stop (indices.getD (probeState mask u j).1 DKIX_EMPTY) ∧
        (∀ j', t ≤ j' → j' < j → ¬ stop (indices.getD (probeState mask u j').1 DKIX_EMPTY)) ∧
        probeUntil stop indices mask fuel (probeState mask u t).1 (probeState mask u t).2
          = .ok (probeState mask u j).1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro t ⟨j, h1, h2, _⟩
    omega
  | succ fuel ih =>
    intro t hex
    have step : probeStep mask (probeState mask u t).1 (probeState mask u t).2
        = probeState mask u (t + 1) := rfl
    by_cases hs : stop (indices.getD (probeState mask u t).1 DKIX_EMPTY)
    · refine ⟨t, by omega, by omega, hs, fun j' h1 h2 => by omega, ?_⟩
      simp only [probeUntil]
      rw [if_pos hs]
    · have hex' : ∃ j, t + 1 ≤ j ∧ j < t + 1 + fuel ∧
          stop (indices.getD (probeState mask u j).1 DKIX_EMPTY) := by
        obtain ⟨j, h1, h2, h3⟩ := hex
        refine ⟨j, ?_, by omega, h3⟩
        have : j ≠ t := fun e => hs (e ▸ h3)
        omega
      obtain ⟨j, h1, h2, h3, h4, h5⟩ := ih (t + 1) hex'
      refine ⟨j, by omega, by omega, h3, ?_, ?_⟩
      · intro j' a b
        by_cases e : j' = t
        · subst e; exact hs
        · exact h4 j' (by omega) b
      · simp only [probeUntil, hs, if_false, Bool.false_eq_true, step]
        exact h5

/-- `lookdict_index` finds the slot of a live entry. -/
theorem lookdictLoop_walk (indices : List Int) (mask u index : Nat) :
    ∀ fuel t j, t ≤ j → j < t + fuel →
      indices.getD (probeState mask u j).1 DKIX_EMPTY = (index : Int) →
      (∀ j', t ≤ j' → j' < j → indices.getD (probeState mask u j').1 DKIX_EMPTY ≠ DKIX_EMPTY) →
      ∃ j0, t ≤ j0 ∧ j0 ≤ j ∧ indices.getD (probeState mask u j0).1 DKIX_EMPTY = (index : Int) ∧
        lookdictIndexLoop indices mask index fuel (probeState mask u t).1 (probeState mask u t).2
          = .ok ((probeState mask u j0).1 : Int) := by
  intro fuel
  induction fuel with
  | zero => intro t j h1 h2; omega
  | succ fuel ih =>
    intro t j h1 h2 h3 h4
    have step : probeStep mask (probeState mask u t).1 (probeState mask u t).2
        = probeState mask u (t + 1) := rfl
    by_cases he : indices.getD (probeState mask u t).1 DKIX_EMPTY = (index : Int)
    · refine ⟨t, by omega, h1, he, ?_⟩
      simp only [lookdictIndexLoop]
      rw [if_pos (beq_iff_eq.mpr he)]
    · have hjt : t < j := by
        by_cases e : t = j
        · subst e; exact absurd h3 he
        · omega
      obtain ⟨j0, a, b, c, d⟩ := ih (t + 1) j (by omega) (by omega) h3
        (fun j' x y => h4 j' (by omega) y)
      refine ⟨j0, by omega, b, c, ?_⟩
      have hne := h4 t (by omega) hjt
      have he1 : (indices.getD (probeState mask u t).1 DKIX_EMPTY == (index : Int)) = false := by
        simpa using he
      have he2 : (indices.getD (probeState mask u t).1 DKIX_EMPTY == DKIX_EMPTY) = false := by
        simpa using hne
      simp only [lookdictIndexLoop, he1, he2, if_false, Bool.false_eq_true, step]
      exact d

end Walk

/-- `lookdict_index` on a chained table. -/
theorem lookdictIndex_spec (k : Keys K V) (hc : Chain k) (ix : Nat) (e : Ent K V)
    (he : k.entry ix = some e) :
    ∃ s, s < k.size ∧ k.getIndex s = (ix : Int) ∧ lookdictIndex k e.hash ix = .ok (s : Int) := by
  obtain ⟨j, hj, h1, h2⟩ := hc.reach ix e he
  obtain ⟨j0, _, _, h3, h4⟩ := lookdictLoop_walk k.indices k.mask (toU64 e.hash) ix
    (probeFuel k.log2Size) 0 j (by omega) (by omega) h1 (fun j' _ h => h2 j' h)
  exact ⟨k.pos e.hash j0, k.pos_lt _ _, h3, h4⟩

theorem getIndex_setIndex (k : Keys K V) (s i : Nat) (x : Int) (hs : s < k.indices.length) :
    (k.setIndex s x).getIndex i = if i = s then x else k.getIndex i := by
  simp only [Keys.setIndex, Keys.getIndex]
  by_cases h : i = s
  · subst h
    simp [List.getD, hs]
  · have h' : s ≠ i := fun e => h e.symm
    simp [h, List.getD, List.getElem?_set, h']

theorem filled_set (k : Keys K V) (s : Nat) (x : Int) (hs : s < k.indices.length) :
    (k.setIndex s x).filled ≤ k.filled + 1 := by
  simp only [Keys.filled, Keys.setIndex]
  have hlen : (k.indices.set s x).length = k.indices.length := by simp
  generalize k.indices = l at *
  induction l generalizing s with
  | nil => simp at hs
  | cons a t ih =>
    cases s with
    | zero =>
      simp only [List.set_cons_zero, List.countP_cons]
      split <;> split <;> omega
    | succ s =>
      simp only [List.set_cons_succ, List.countP_cons]
      have := ih s (by simpa using hs) (by simp)
      split <;> omega

/-- Replacing a slot by a dummy does not fill anything new, if it was filled already. -/
theorem filled_set_filled (k : Keys K V) (s : Nat) (x : Int) (hs : s < k.indices.length)
    (hne : k.getIndex s ≠ DKIX_EMPTY) : (k.setIndex s x).filled ≤ k.filled := by
  simp only [Keys.filled, Keys.setIndex]
  simp only [Keys.getIndex] at hne
  generalize k.indices = l at *
  induction l generalizing s with
  | nil => simp at hs
  | cons a t ih =>
    cases s with
    | zero =>
      simp only [List.set_cons_zero, List.countP_cons]
      have : (a != DKIX_EMPTY) = true := by simpa [List.getD] using hne
      simp only [this, if_true]
      split <;> omega
    | succ s =>
      simp only [List.set_cons_succ, List.countP_cons]
      have := ih s (by simpa using hs) (by simpa [List.getD] using hne)
      split <;> omega

/-- What adding an entry does to the table, abstracted from `appendEntry` and `buildIndices`:
write `nentries` into the first slot `stop` accepts on the probe sequence. -/
theorem chain_add (k : Keys K V) (hc : Chain k) (e : Ent K V) (s j : Nat) (hj : j < probeFuel k.log2Size)
    (hs : s = k.pos e.hash j) (hneg : k.getIndex s < 0)
    (hpre : ∀ j', j' < j → k.getIndex (k.pos e.hash j') ≠ DKIX_EMPTY)
    (k' : Keys K V) (hsize : k'.log2Size = k.log2Size)
    (hind : k'.indices = k.indices.set s k.nentries)
    (hent : k'.entries = k.entries ++ [some e]) : Chain k' := by
  have hmask : k'.mask = k.mask := by simp [Keys.mask, Keys.size, hsize]
  have hsz : k'.size = k.size := by simp [Keys.size, hsize]
  have hslt : s < k.indices.length := by rw [hc.len, hs]; exact k.pos_lt _ _
  have hidx : ∀ i, k'.getIndex i = if i = s then (k.nentries : Int) else k.getIndex i := by
    intro i
    have := getIndex_setIndex k s i k.nentries hslt
    simpa [Keys.setIndex, Keys.getIndex, hind] using this
  have hpos : ∀ h j, k'.pos h j = k.pos h j := by
    intro h j; simp [Keys.pos, hmask]
  have hlive : ∀ ix e', k.entry ix = some e' → ix < k.nentries := by
    intro ix e' h
    simp only [Keys.entry, Option.join_eq_some_iff] at h
    simp only [Keys.nentries]
    exact (List.getElem?_eq_some_iff.mp h).1
  have hentry : ∀ ix, k'.entry ix =
      if ix < k.nentries then k.entry ix else if ix = k.nentries then some e else none := by
    intro ix
    simp only [Keys.entry, hent, Keys.nentries]
    by_cases h : ix < k.entries.length
    · simp [h, List.getElem?_append_left]
    · by_cases h2 : ix = k.entries.length
      · subst h2; simp
      · have : ix - k.entries.length ≠ 0 := by omega
        have h3 : k.entries.length ≤ ix := by omega
        simp [h, h2, List.getElem?_append_right h3, List.getElem?_cons, this]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hind, hc.len, hsz]
  · intro i hi
    rw [hsz] at hi
    rw [hidx]
    by_cases his : i = s
    · simp only [his, if_true]
      exact Or.inr (Or.inr ⟨k.nentries, e, rfl, by simp [hentry]⟩)
    · simp only [his, if_false]
      rcases hc.range i hi with h | h | ⟨ix, e', h1, h2⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · refine Or.inr (Or.inr ⟨ix, e', h1, ?_⟩)
        rw [hentry]
        simp [hlive ix e' h2, h2]
  · intro i j' ix hi hj' h1 h2
    rw [hsz] at hi hj'
    rw [hidx] at h1 h2
    have hnone : ∀ t, t < k.size → t ≠ s → k.getIndex t ≠ (k.nentries : Int) := by
      intro t ht hts h
      rcases hc.range t ht with h' | h' | ⟨ix', e', h3, h4⟩
      · rw [h] at h'; simp [DKIX_EMPTY] at h'
      · rw [h] at h'; simp [DKIX_DUMMY] at h'
      · have := hlive ix' e' h4
        rw [h] at h3
        omega
    by_cases a : i = s <;> by_cases b : j' = s
    · omega
    · simp only [a, b, if_true, if_false] at h1 h2
      exact absurd (h2.trans h1.symm) (hnone j' hj' b)
    · simp only [a, b, if_true, if_false] at h1 h2
      exact absurd (h1.trans h2.symm) (hnone i hi a)
    · simp only [a, b, if_false] at h1 h2
      exact hc.inj i j' ix hi hj' h1 h2
  · intro ix e' he'
    rw [hentry] at he'
    by_cases hlt : ix < k.nentries
    · simp only [hlt, if_true] at he'
      obtain ⟨j0, h0, h1, h2⟩ := hc.reach ix e' he'
      refine ⟨j0, by simpa [hsize] using h0, ?_, ?_⟩
      · rw [hpos, hidx]
        have : k.pos e'.hash j0 ≠ s := by
          intro h
          rw [h] at h1
          rw [h1] at hneg
          omega
        simp [this, h1]
      · intro j1 h
        rw [hpos, hidx]
        by_cases e1 : k.pos e'.hash j1 = s
        · simp only [e1, if_true, DKIX_EMPTY]; omega
        · simp only [e1, if_false]; exact h2 j1 h
    · by_cases he2 : ix = k.nentries
      · have he3 : e = e' := by
          rw [if_neg hlt, if_pos he2] at he'
          exact Option.some.inj he'
        subst he3
        refine ⟨j, by simpa [hsize] using hj, ?_, ?_⟩
        · rw [hpos, ← hs, hidx]
          simp [he2]
        · intro j1 h
          rw [hpos, hidx]
          by_cases e1 : k.pos e.hash j1 = s
          · simp only [e1, if_true, DKIX_EMPTY]; omega
          · simp only [e1, if_false]; exact hpre j1 h
      · rw [if_neg hlt, if_neg he2] at he'
        exact absurd he' (by simp)

/-- Dropping a live entry: slot to `DKIX_DUMMY`, entry to NULL or truncated away. -/
theorem chain_remove (k : Keys K V) (hc : Chain k) (ix s : Nat) (hs : s < k.size)
    (his : k.getIndex s = (ix : Int)) (k' : Keys K V) (hsize : k'.log2Size = k.log2Size)
    (hind : k'.indices = k.indices.set s DKIX_DUMMY)
    (hent : ∀ t, k'.entry t = if t = ix then none else k.entry t) : Chain k' := by
  have hmask : k'.mask = k.mask := by simp [Keys.mask, Keys.size, hsize]
  have hsz : k'.size = k.size := by simp [Keys.size, hsize]
  have hslt : s < k.indices.length := by rw [hc.len]; exact hs
  have hidx : ∀ i, k'.getIndex i = if i = s then DKIX_DUMMY else k.getIndex i := by
    intro i
    have := getIndex_setIndex k s i DKIX_DUMMY hslt
    simpa [Keys.setIndex, Keys.getIndex, hind] using this
  have hpos : ∀ h j, k'.pos h j = k.pos h j := by
    intro h j; simp [Keys.pos, hmask]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hind, hc.len, hsz]
  · intro i hi
    rw [hsz] at hi
    rw [hidx]
    by_cases his' : i = s
    · simp [his']
    · simp only [his', if_false]
      rcases hc.range i hi with h | h | ⟨ix', e', h1, h2⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · refine Or.inr (Or.inr ⟨ix', e', h1, ?_⟩)
        rw [hent]
        have : ix' ≠ ix := by
          intro e
          subst e
          exact his' (hc.inj i s ix' hi hs h1 his)
        simp [this, h2]
  · intro i j ix' hi hj h1 h2
    rw [hsz] at hi hj
    rw [hidx] at h1 h2
    by_cases a : i = s
    · simp only [a, if_true, DKIX_DUMMY] at h1; omega
    · by_cases b : j = s
      · simp only [b, if_true, DKIX_DUMMY] at h2; omega
      · simp only [a, b, if_false] at h1 h2
        exact hc.inj i j ix' hi hj h1 h2
  · intro t e' he'
    rw [hent] at he'
    by_cases htix : t = ix
    · simp [htix] at he'
    · simp only [htix, if_false] at he'
      obtain ⟨j0, h0, h1, h2⟩ := hc.reach t e' he'
      refine ⟨j0, by simpa [hsize] using h0, ?_, ?_⟩
      · rw [hpos, hidx]
        have : k.pos e'.hash j0 ≠ s := by
          intro h
          rw [h, his] at h1
          exact htix (by omega)
        simp [this, h1]
      · intro j1 h
        rw [hpos, hidx]
        by_cases e1 : k.pos e'.hash j1 = s
        · simp [e1, DKIX_DUMMY, DKIX_EMPTY]
        · simp only [e1, if_false]; exact h2 j1 h

/-- Overwriting a value touches no index. -/
theorem chain_setvalue (k : Keys K V) (hc : Chain k) (k' : Keys K V)
    (hsize : k'.log2Size = k.log2Size) (hind : k'.indices = k.indices)
    (hent : ∀ t, ((k'.entry t).map (·.hash)) = (k.entry t).map (·.hash)) : Chain k' := by
  have hmask : k'.mask = k.mask := by simp [Keys.mask, Keys.size, hsize]
  have hsz : k'.size = k.size := by simp [Keys.size, hsize]
  have hidx : ∀ i, k'.getIndex i = k.getIndex i := by intro i; simp [Keys.getIndex, hind]
  have hpos : ∀ h j, k'.pos h j = k.pos h j := by intro h j; simp [Keys.pos, hmask]
  have hsome : ∀ t e, k.entry t = some e → ∃ e', k'.entry t = some e' ∧ e'.hash = e.hash := by
    intro t e h
    have := hent t
    rw [h] at this
    cases h' : k'.entry t with
    | none => simp [h'] at this
    | some e' => exact ⟨e', rfl, by simpa [h'] using this⟩
  refine ⟨by simp [hind, hc.len, hsz], ?_, ?_, ?_⟩
  · intro i hi
    rw [hsz] at hi
    rw [hidx]
    rcases hc.range i hi with h | h | ⟨ix, e, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨e', h3, _⟩ := hsome ix e h2
      exact Or.inr (Or.inr ⟨ix, e', h1, h3⟩)
  · intro i j ix hi hj h1 h2
    rw [hsz] at hi hj
    rw [hidx] at h1 h2
    exact hc.inj i j ix hi hj h1 h2
  · intro t e he
    have h0 := hent t
    rw [he] at h0
    cases h' : k.entry t with
    | none => simp [h'] at h0
    | some e0 =>
      have hh : e.hash = e0.hash := by simpa [h'] using h0
      obtain ⟨j, a, b, c⟩ := hc.reach t e0 h'
      refine ⟨j, by simpa [hsize] using a, ?_, ?_⟩
      · rw [hpos, hidx, hh]; exact b
      · intro j1 h
        rw [hpos, hidx, hh]
        exact c j1 h

end PyLean.DictSet
