import PyLean.TextLibs.DifflibSound

/-!
`get_matching_blocks` and `get_opcodes`: the sort and the collapsing step turn the blocks of the queue
into a chain, and the opcodes walk that chain. These hold for all sequences and all `isjunk`.
-/

namespace PyLean.TextLibs.Difflib

open PyLean

/-- Blocks before one another, in both sequences. -/
def BfT (u v : T) : Prop := Bf (toBox u) (toBox v)

theorem bfT_trans {x y z : T} (h1 : BfT x y) (h2 : BfT y z) : BfT x z := by
  obtain ⟨a1, a2⟩ := h1
  obtain ⟨b1, b2⟩ := h2
  simp only [toBox] at a1 a2 b1 b2
  exact ⟨by simp only [toBox]; omega, by simp only [toBox]; omega⟩

theorem tLe_fst {x y : T} (h : tLe x y = true) : x.1 ≤ y.1 := by
  simp only [tLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  omega

theorem tLe_not {x y : T} (h : tLe x y = false) : y.1 ≤ x.1 := by
  simp only [tLe, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne] at h
  omega

theorem mem_insertT (x z : T) (l : List T) : z ∈ insertT x l ↔ z = x ∨ z ∈ l := by
  induction l with
  | nil => simp [insertT]
  | cons y r ih =>
    simp only [insertT]
    split
    · simp
    · simp only [List.mem_cons, ih]
      constructor
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)

theorem mem_sortT (z : T) (l : List T) : z ∈ sortT l ↔ z ∈ l := by
  induction l with
  | nil => simp [sortT]
  | cons x r ih => simp [sortT, mem_insertT, ih]

theorem insert_chain (x : T) (hx : 1 ≤ x.2.2) : ∀ l : List T, (∀ y ∈ l, 1 ≤ y.2.2) →
    (∀ y ∈ l, Rel (toBox x) (toBox y)) → l.Pairwise BfT → (insertT x l).Pairwise BfT := by
  intro l
  induction l with
  | nil => intro _ _ _; simp [insertT]
  | cons y r ih =>
    intro h1 h2 h3
    obtain ⟨h4, h5⟩ := List.pairwise_cons.mp h3
    simp only [insertT]
    have hy := h1 y (by simp)
    have rel := h2 y (by simp)
    cases hle : tLe x y with
    | true =>
      simp only [if_true]
      have hf := tLe_fst hle
      have hb : BfT x y := by
        rcases rel with r1 | r1
        · exact r1
        · have := r1.1
          simp only [toBox] at this
          omega
      refine List.pairwise_cons.mpr ⟨?_, h3⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hb
      · exact bfT_trans hb (h4 z hz)
    | false =>
      simp only [Bool.false_eq_true, if_false]
      have hf := tLe_not hle
      have hb : BfT y x := by
        rcases rel with r1 | r1
        · have := r1.1
          simp only [toBox] at this
          omega
        · exact r1
      refine List.pairwise_cons.mpr ⟨?_, ih (fun z hz => h1 z (by simp [hz]))
        (fun z hz => h2 z (by simp [hz])) h5⟩
      intro z hz
      rcases (mem_insertT x z r).mp hz with rfl | hz
      · exact hb
      · exact h4 z hz

theorem sort_chain : ∀ l : List T, (∀ y ∈ l, 1 ≤ y.2.2) → l.Pairwise (fun u v => Rel (toBox u) (toBox v)) →
    (sortT l).Pairwise BfT := by
  intro l
  induction l with
  | nil => intro _ _; simp [sortT]
  | cons x r ih =>
    intro h1 h2
    obtain ⟨h3, h4⟩ := List.pairwise_cons.mp h2
    exact insert_chain x (h1 x (by simp)) _ (fun y hy => h1 y (by simp [(mem_sortT y r).mp hy]))
      (fun y hy => h3 y ((mem_sortT y r).mp hy)) (ih (fun y hy => h1 y (by simp [hy])) h4)

/-- `l` is a chain of real matches starting at or after `(i, j)`. -/
def ChainFrom (a b : List Nat) : Nat → Nat → List T → Prop
  | i, j, [] => i ≤ a.length ∧ j ≤ b.length
  | i, j, (x, y, k) :: r => 1 ≤ k ∧ i ≤ x ∧ j ≤ y ∧ Eqs a b x y k ∧ ChainFrom a b (x + k) (y + k) r

theorem collapse_chain (a b : List Nat) : ∀ (l : List T) (i j k p q : Nat), l.Pairwise BfT →
    (∀ t ∈ l, 1 ≤ t.2.2 ∧ Eqs a b t.1 t.2.1 t.2.2) → Eqs a b i j k →
    (∀ t ∈ l, i + k ≤ t.1 ∧ j + k ≤ t.2.1) → p ≤ i → q ≤ j →
    ChainFrom a b p q (collapse (i, j, k) l) := by
  intro l
  induction l with
  | nil =>
    intro i j k p q _ _ he _ h1 h2
    simp only [collapse]
    split
    · rename_i hk
      have hk : k ≠ 0 := by simpa using hk
      exact ⟨by omega, h1, h2, he, he.1, he.2.1⟩
    · exact ⟨by have := he.1; omega, by have := he.2.1; omega⟩
  | cons t r ih =>
    intro i j k p q hp hok he hle h1 h2
    obtain ⟨i2, j2, k2⟩ := t
    obtain ⟨hp1, hp2⟩ := List.pairwise_cons.mp hp
    have hthis := hok (i2, j2, k2) (by simp)
    have hrest : ∀ u ∈ r, 1 ≤ u.2.2 ∧ Eqs a b u.1 u.2.1 u.2.2 := fun u hu => hok u (by simp [hu])
    have hafter : ∀ u ∈ r, i2 + k2 ≤ u.1 ∧ j2 + k2 ≤ u.2.1 := by
      intro u hu
      have := hp1 u hu
      obtain ⟨c1, c2⟩ := this
      simp only [toBox] at c1 c2
      exact ⟨c1, c2⟩
    have hl0 := hle (i2, j2, k2) (by simp)
    simp only at hl0 hthis
    simp only [collapse]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨c1, c2⟩ := hc
      subst c1 c2
      refine ih i j (k + k2) p q hp2 hrest (eqs_join he hthis.2) ?_ h1 h2
      intro u hu
      have := hafter u hu
      omega
    · split
      · rename_i _ hk
        have hk : k ≠ 0 := by simpa using hk
        exact ⟨by omega, h1, h2, he, ih i2 j2 k2 _ _ hp2 hrest hthis.2 hafter (by omega) (by omega)⟩
      · exact ih i2 j2 k2 _ _ hp2 hrest hthis.2 hafter (by omega) (by omega)

/-- Adjacent blocks do not touch. -/
def NA : List T → Prop
  | x :: y :: r => (x.1 + x.2.2 ≠ y.1 ∨ x.2.1 + x.2.2 ≠ y.2.1) ∧ NA (y :: r)
  | _ => True

theorem collapse_head : ∀ (l : List T) (i j k : Nat), k ≠ 0 → (∀ t ∈ l, 1 ≤ t.2.2) →
    ∃ k' r, collapse (i, j, k) l = (i, j, k') :: r := by
  intro l
  induction l with
  | nil =>
    intro i j k hk _
    have : (k != 0) = true := by simpa using hk
    exact ⟨k, [], by simp [collapse, this]⟩
  | cons t r ih =>
    intro i j k hk ht
    obtain ⟨i2, j2, k2⟩ := t
    have hr : ∀ u ∈ r, 1 ≤ u.2.2 := fun u hu => ht u (by simp [hu])
    simp only [collapse]
    split
    · exact ih i j (k + k2) (by omega) hr
    · have : (k != 0) = true := by simpa using hk
      simp only [this, if_true]
      exact ⟨k, _, rfl⟩

theorem collapse_na : ∀ (l : List T) (i j k : Nat), (∀ t ∈ l, 1 ≤ t.2.2) → NA (collapse (i, j, k) l) := by
  intro l
  induction l with
  | nil =>
    intro i j k _
    simp only [collapse]
    split <;> simp [NA]
  | cons t r ih =>
    intro i j k ht
    obtain ⟨i2, j2, k2⟩ := t
    have hr : ∀ u ∈ r, 1 ≤ u.2.2 := fun u hu => ht u (by simp [hu])
    have h2 : 1 ≤ k2 := ht (i2, j2, k2) (by simp)
    simp only [collapse]
    split
    · exact ih _ _ _ hr
    · rename_i hc
      split
      · obtain ⟨k', r', he⟩ := collapse_head r i2 j2 k2 (by omega) hr
        have := ih i2 j2 k2 hr
        rw [he] at this ⊢
        refine ⟨?_, this⟩
        simp only [Bool.and_eq_true, beq_iff_eq, not_and] at hc
        by_cases h1 : i + k = i2
        · exact .inr (hc h1)
        · exact .inl h1
      · exact ih _ _ _ hr

/-- The tag says what the two slices are. -/
def TagOk (a b : List Nat) : Tag → Nat → Nat → Nat → Nat → Prop
  | .equal, i1, i2, j1, j2 => i1 < i2 ∧ i2 - i1 = j2 - j1 ∧ Eqs a b i1 j1 (i2 - i1)
  | .replace, i1, i2, j1, j2 => i1 < i2 ∧ j1 < j2
  | .delete, i1, i2, j1, j2 => i1 < i2 ∧ j1 = j2
  | .insert, i1, i2, j1, j2 => i1 = i2 ∧ j1 < j2

/-- The opcodes go from `(i, j)` to the ends of both sequences, with no gap. -/
def Cover (a b : List Nat) : Nat → Nat → List Op → Prop
  | i, j, [] => i = a.length ∧ j = b.length
  | i, j, (t, i1, i2, j1, j2) :: r =>
    i1 = i ∧ j1 = j ∧ i2 ≤ a.length ∧ j2 ≤ b.length ∧ TagOk a b t i1 i2 j1 j2 ∧ Cover a b i2 j2 r

/-- The opcodes before one block, and the block. -/
theorem op_step (a b : List Nat) (i j ai bj k : Nat) (hi : i ≤ ai) (hj : j ≤ bj) (hai : ai ≤ a.length)
    (hbj : bj ≤ b.length) (r : List T) (hc1 : k ≠ 0 → Eqs a b ai bj k)
    (hc2 : Cover a b (ai + k) (bj + k) (opLoop r (ai + k) (bj + k))) :
    Cover a b i j (opLoop ((ai, bj, k) :: r) i j) := by
  have tail : Cover a b ai bj ((if k != 0 then [(Tag.equal, ai, ai + k, bj, bj + k)] else []) ++
      opLoop r (ai + k) (bj + k)) := by
    by_cases hk : k = 0
    · subst hk
      simpa using hc2
    · have he := hc1 hk
      have : (k != 0) = true := by simpa using hk
      simp only [this, if_true, List.cons_append, List.nil_append]
      refine ⟨rfl, rfl, he.1, he.2.1, ?_, hc2⟩
      refine ⟨by omega, by omega, ?_⟩
      have e : ai + k - ai = k := by omega
      rw [e]
      exact he
  generalize hX : (if k != 0 then [(Tag.equal, ai, ai + k, bj, bj + k)] else []) ++
      opLoop r (ai + k) (bj + k) = X at tail
  by_cases h1 : i < ai
  · by_cases h2 : j < bj
    · have e : opLoop ((ai, bj, k) :: r) i j = (Tag.replace, i, ai, j, bj) :: X := by
        rw [← hX]
        simp [opLoop, h1, h2]
      rw [e]
      exact ⟨rfl, rfl, hai, hbj, ⟨h1, h2⟩, tail⟩
    · have hjb : j = bj := by omega
      subst hjb
      have e : opLoop ((ai, j, k) :: r) i j = (Tag.delete, i, ai, j, j) :: X := by
        rw [← hX]
        simp [opLoop, h1]
      rw [e]
      exact ⟨rfl, rfl, hai, hbj, ⟨h1, rfl⟩, tail⟩
  · have hia : i = ai := by omega
    subst hia
    by_cases h2 : j < bj
    · have e : opLoop ((i, bj, k) :: r) i j = (Tag.insert, i, i, j, bj) :: X := by
        rw [← hX]
        simp [opLoop, h2]
      rw [e]
      exact ⟨rfl, rfl, hai, hbj, ⟨rfl, h2⟩, tail⟩
    · have hjb : j = bj := by omega
      subst hjb
      have e : opLoop ((i, j, k) :: r) i j = X := by
        rw [← hX]
        simp [opLoop]
      rw [e]
      exact tail

theorem op_ok (a b : List Nat) : ∀ (l : List T) (i j : Nat), ChainFrom a b i j l →
    Cover a b i j (opLoop (l ++ [(a.length, b.length, 0)]) i j) := by
  intro l
  induction l with
  | nil =>
    intro i j h
    simp only [List.nil_append]
    exact op_step a b i j a.length b.length 0 h.1 h.2 (Nat.le_refl _) (Nat.le_refl _) []
      (fun h0 => absurd rfl h0) ⟨by omega, by omega⟩
  | cons t r ih =>
    intro i j h
    obtain ⟨x, y, k⟩ := t
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only [List.cons_append]
    exact op_step a b i j x y k h2 h3 (by have := h4.1; omega) (by have := h4.2.1; omega) _
      (fun _ => h4) (ih _ _ h5)

/-- What `getBlocks` gives on a matcher with no cached blocks. -/
theorem getBlocks_ok (s : SM) (hs : Ready s) (hc : s.blocks = none) :
    ∃ l, getBlocks s = .ok ({ s with blocks := some (l ++ [(s.a.length, s.b.length, 0)]) },
        l ++ [(s.a.length, s.b.length, 0)]) ∧ ChainFrom s.a s.b 0 0 l ∧ NA l := by
  have h0 : LoopInv s [(0, s.a.length, 0, s.b.length)] [] :=
    ⟨by
      intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨by simp, Nat.le_refl _, by simp, Nat.le_refl _⟩,
     by simp, by simp, by simp, by simp⟩
  obtain ⟨found, hf, hi⟩ := block_loop s hs (2 * s.a.length + 2) _ [] (by simp [blockMeasure]) h0
  have hk : ∀ y ∈ found, 1 ≤ y.2.2 := fun y hy => (hi.blocks y hy).1
  have hsorted := sort_chain found hk hi.pf
  have hmem : ∀ t ∈ sortT found, 1 ≤ t.2.2 ∧ Eqs s.a s.b t.1 t.2.1 t.2.2 :=
    fun t ht => hi.blocks t ((mem_sortT t found).mp ht)
  refine ⟨collapse (0, 0, 0) (sortT found), ?_, ?_, ?_⟩
  · simp [getBlocks, hc, hf]
  · refine collapse_chain _ _ _ 0 0 0 0 0 hsorted hmem (eqs_zero _ _ _ _ (by simp) (by simp)) (by simp) (by simp) (by simp)
  · exact collapse_na _ _ _ _ (fun t ht => (hmem t ht).1)

/-- `get_opcodes` on a new matcher: for all sequences and any `isjunk`, the opcodes go from the start to
the ends of both sequences with no gap, an `equal` is a real match, and each tag means what it says.
Anything that fails `Cover` is wrong, while a single `replace` of the whole would pass, so the blocks law
below says that the blocks are a chain. -/
def OpcodesLaw : Prop :=
  ∀ (isjunk : Option (Nat → Py Bool)) (a b : List Nat) (auto : Bool) (s : SM), make isjunk a b auto = .ok s →
    ∃ s' ops, getOpcodes s = .ok (s', ops) ∧ Cover a b 0 0 ops

/-- `get_matching_blocks` on a new matcher: a chain of real matches, in order in both sequences, that do
not touch, and the sentinel `(len(a), len(b), 0)`, the only block of size 0. -/
def BlocksLaw : Prop :=
  ∀ (isjunk : Option (Nat → Py Bool)) (a b : List Nat) (auto : Bool) (s : SM), make isjunk a b auto = .ok s →
    ∃ s' l, getBlocks s = .ok (s', l ++ [(a.length, b.length, 0)]) ∧ ChainFrom a b 0 0 l ∧ NA l

theorem make_fresh (isjunk : Option (Nat → Py Bool)) (a b : List Nat) (auto : Bool) (s : SM)
    (h : make isjunk a b auto = .ok s) : s.blocks = none ∧ s.opcodes = none := by
  obtain ⟨_, _, _, h4, h5, _⟩ := chainB_spec _ _ (make_ok _ _ _ _ _ h)
  exact ⟨h4, h5⟩

theorem getOpcodes_of (s s1 : SM) (bs : List T) (ho : s.opcodes = none) (h : getBlocks s = .ok (s1, bs)) :
    getOpcodes s = .ok ({ s1 with opcodes := some (opLoop bs 0 0) }, opLoop bs 0 0) := by
  simp only [getOpcodes, ho, h]

theorem ratioPair_of (s s1 : SM) (bs : List T) (h : getBlocks s = .ok (s1, bs)) :
    ratioPair s = .ok (s1, sumBlocks bs, s1.a.length + s1.b.length) := by
  simp only [ratioPair, h]

theorem blocksLaw_proven : BlocksLaw := by
  intro isjunk a b auto s h
  obtain ⟨hr, rfl, rfl⟩ := make_ready _ _ _ _ _ h
  obtain ⟨l, h1, h2, h3⟩ := getBlocks_ok s hr (make_fresh _ _ _ _ _ h).1
  exact ⟨_, l, h1, h2, h3⟩

theorem opcodesLaw_proven : OpcodesLaw := by
  intro isjunk a b auto s h
  obtain ⟨hr, rfl, rfl⟩ := make_ready _ _ _ _ _ h
  obtain ⟨hb, ho⟩ := make_fresh _ _ _ _ _ h
  obtain ⟨l, h1, h2, _⟩ := getBlocks_ok s hr hb
  exact ⟨_, _, getOpcodes_of s _ _ ho h1, op_ok _ _ l 0 0 h2⟩

theorem sum_chain (a b : List Nat) : ∀ (l : List T) (i j : Nat), ChainFrom a b i j l →
    i + sumBlocks l ≤ a.length ∧ j + sumBlocks l ≤ b.length := by
  intro l
  induction l with
  | nil => intro i j h; exact ⟨by simpa [sumBlocks] using h.1, by simpa [sumBlocks] using h.2⟩
  | cons t r ih =>
    intro i j h
    obtain ⟨x, y, k⟩ := t
    obtain ⟨_, h2, h3, _, h5⟩ := h
    have := ih _ _ h5
    simp only [sumBlocks]
    omega

theorem sumBlocks_append (l m : List T) : sumBlocks (l ++ m) = sumBlocks l + sumBlocks m := by
  induction l with
  | nil => simp [sumBlocks]
  | cons t r ih =>
    obtain ⟨x, y, k⟩ := t
    simp [sumBlocks, ih]
    omega

/-- `ratio() <= real_quick_ratio()`, exactly: the matches number at most the shorter length, on a new
matcher. With `length` nonzero, this is also why `ratio()` is at most 1. -/
def RatioBound : Prop :=
  ∀ (isjunk : Option (Nat → Py Bool)) (a b : List Nat) (auto : Bool) (s : SM), make isjunk a b auto = .ok s →
    ∃ s' m l, ratioPair s = .ok (s', m, l) ∧ l = a.length + b.length ∧ m ≤ (realQuickPair s).1

theorem ratioBound_proven : RatioBound := by
  intro isjunk a b auto s h
  obtain ⟨hr, rfl, rfl⟩ := make_ready _ _ _ _ _ h
  obtain ⟨l, h1, h2, _⟩ := getBlocks_ok s hr (make_fresh _ _ _ _ _ h).1
  have := sum_chain _ _ l 0 0 h2
  refine ⟨_, _, _, ratioPair_of s _ _ h1, rfl, ?_⟩
  rw [sumBlocks_append]
  simp only [sumBlocks, realQuickPair]
  omega

/-- Python's `s.get_opcodes()`, then `list(s.get_grouped_opcodes(n))`, then `s.get_opcodes()`. -/
def beforeAfter (a b : List Nat) (auto : Bool) (n : Nat) : Py (List Op × List Op) :=
  match make none a b auto with
  | .error e => .error e
  | .ok s =>
    match getOpcodes s with
    | .error e => .error e
    | .ok (s1, ops) =>
      match getGrouped s1 n with
      | .error e => .error e
      | .ok (s2, _) =>
        match getOpcodes s2 with
        | .error e => .error e
        | .ok (_, ops2) => .ok (ops, ops2)

/-- `get_grouped_opcodes` does not change what `get_opcodes` returns. False: it writes into the cache. -/
def GroupedKeepsOpcodes : Prop :=
  ∀ (a b : List Nat) (auto : Bool) (n : Nat) (ops ops2 : List Op), beforeAfter a b auto n = .ok (ops, ops2) → ops = ops2

theorem groupedKeepsOpcodes_refuted : ¬GroupedKeepsOpcodes := by
  intro h
  have := h [1, 2, 3, 4, 9] [1, 2, 3, 4, 8] false 1 _ _ rfl
  revert this
  decide

end PyLean.TextLibs.Difflib
