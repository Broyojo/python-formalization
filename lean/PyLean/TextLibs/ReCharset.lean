import PyLean.TextLibs.ReSearchProps

/-!
`_optimize_charset`, `Lib/re/_compiler.py:248-395`, preserves the set: what `SRE(charset)` answers on
the compiled result is what the unoptimized set says. This file reads a compiled charset back as a
list, and shows the steps of the loop; `ReCharset2.lean` has the compression.
-/

namespace PyLean.TextLibs.Re

open PyLean

set_option linter.unusedSimpArgs false

/-- Does a `BIGCHARSET`'s data hold `ch`? -/
def bigHit (d : List Nat) (ch : Nat) : Bool :=
  if ch < 0x10000 then
    let hi := ch / 256
    let block := (d.getD (1 + hi / 4) 0 / 256 ^ (hi % 4)) % 256
    (d.getD (1 + 64 + (block * 256 + ch % 256) / 32) 0 / 2 ^ (ch % 32)) % 2 == 1
  else false

/-- One compiled item. -/
def siHit (flags : Nat) : CItem → Nat → Bool
  | .lit a, c => c == a
  | .rng a b, c => decide (a ≤ c) && decide (c ≤ b)
  | .rngUni a b, c =>
    (decide (a ≤ c) && decide (c ≤ b)) ||
      (decide (a ≤ upperUnicode c) && decide (upperUnicode c ≤ b))
  | .cat k, c => sreCategory (catCode flags k) c
  | .neg, _ => false
  | .charset d, c => decide (c < 256) && (d.getD (c / 32) 0 / 2 ^ (c % 32)) % 2 == 1
  | .big d, c => bigHit d c

/-- A compiled set, read as a list: `NEGATE` flips what a hit answers. -/
def hitList (flags : Nat) : Bool → List CItem → Nat → Bool
  | ok, [], _ => !ok
  | ok, .neg :: r, c => hitList flags (!ok) r c
  | ok, it :: r, c => if siHit flags it c then ok else hitList flags ok r c

/-- The words of one item, as `compileCharset` lays them out. -/
def itemWords (flags : Nat) : CItem → List Nat
  | .neg => [OP_NEGATE]
  | .lit c => [OP_LITERAL, c]
  | .rng a b => [OP_RANGE, a, b]
  | .rngUni a b => [OP_RANGE_UNI_IGNORE, a, b]
  | .charset d => OP_CHARSET :: d
  | .big d => OP_BIGCHARSET :: d
  | .cat c => [OP_CATEGORY, catCode flags c]

/-- `compileCharset` writes the items' words, then `FAILURE`. -/
theorem compileCharset_eq (cs : List CItem) (flags : Nat) :
    compileCharset cs flags = cs.flatMap (itemWords flags) ++ [OP_FAILURE] := by
  unfold compileCharset
  congr 1

/-- The code has the words `l` at `set`. -/
def Slice (e : Env) (set : Nat) (l : List Nat) : Prop :=
  ∀ i, i < l.length → e.c (set + i) = l.getD i 0

theorem slice_left {e : Env} {set : Nat} {a b : List Nat} (h : Slice e set (a ++ b)) : Slice e set a := by
  intro i hi
  have := h i (by simp; omega)
  rwa [getD_app_left _ _ _ hi] at this

theorem slice_right {e : Env} {set : Nat} {a b : List Nat} (h : Slice e set (a ++ b)) :
    Slice e (set + a.length) b := by
  intro i hi
  have := h (a.length + i) (by simp; omega)
  rwa [getD_app_right, ← Nat.add_assoc] at this

/-- What an item must satisfy for the engine to step over it: the sizes the compiler gives it. -/
def ItemWf : CItem → Prop
  | .charset d => d.length = 8
  | .big d =>
    65 ≤ d.length ∧ d.length = 65 + d.headD 0 * 8 ∧
      ∀ ch, ch < 0x10000 →
        1 + 64 + ((d.getD (1 + ch / 256 / 4) 0 / 256 ^ (ch / 256 % 4)) % 256 * 256 + ch % 256) / 32 <
          d.length
  | _ => True

theorem charset_step (e : Env) (ch fuel set : Nat) (ok : Bool) :
    sreCharset e ch (fuel + 1) set ok =
      let word (i : Nat) := e.c i
      let op := e.c set
      let set := set + 1
      if op == OP_FAILURE then !ok
      else if op == OP_LITERAL then
        if ch == word set then ok else sreCharset e ch fuel (set + 1) ok
      else if op == OP_CATEGORY then
        if sreCategory (word set) ch then ok else sreCharset e ch fuel (set + 1) ok
      else if op == OP_CHARSET then
        if ch < 256 && (word (set + ch / 32) / 2 ^ (ch % 32)) % 2 == 1 then ok
        else sreCharset e ch fuel (set + 8) ok
      else if op == OP_RANGE then
        if word set ≤ ch ∧ ch ≤ word (set + 1) then ok else sreCharset e ch fuel (set + 2) ok
      else if op == OP_RANGE_UNI_IGNORE then
        let uch := upperUnicode ch
        if (word set ≤ ch ∧ ch ≤ word (set + 1)) ∨ (word set ≤ uch ∧ uch ≤ word (set + 1)) then ok
        else sreCharset e ch fuel (set + 2) ok
      else if op == OP_NEGATE then sreCharset e ch fuel set (!ok)
      else if op == OP_BIGCHARSET then
        let count := word set
        let set := set + 1
        let hit :=
          if ch < 0x10000 then
            let hi := ch / 256
            let block := (word (set + hi / 4) / 256 ^ (hi % 4)) % 256
            let set2 := set + 64
            (word (set2 + (block * 256 + ch % 256) / 32) / 2 ^ (ch % 32)) % 2 == 1
          else false
        if hit then ok else sreCharset e ch fuel (set + 64 + count * 8) ok
      else false := by
  rw [sreCharset]

/-- `SRE(charset)` on compiled words is `hitList`. -/
theorem charset_list (e : Env) (flags ch : Nat) : ∀ (cs : List CItem) (fuel set : Nat) (ok : Bool),
    (∀ it ∈ cs, ItemWf it) → cs.length + 1 ≤ fuel →
    Slice e set (cs.flatMap (itemWords flags) ++ [OP_FAILURE]) →
    sreCharset e ch fuel set ok = hitList flags ok cs ch := by
  intro cs
  induction cs with
  | nil =>
    intro fuel set ok _ hf hs
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have h0 := hs 0 (by simp)
    simp only [List.flatMap_nil, List.nil_append, List.getD_cons_zero, Nat.add_zero] at h0
    rw [charset_step]
    simp [h0, hitList, OP_FAILURE]
  | cons it r ih =>
    intro fuel set ok hw hf hs
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hf' : r.length + 1 ≤ f := by simp at hf; omega
    have hr : ∀ x ∈ r, ItemWf x := fun x hx => hw x (by simp [hx])
    have hs' : Slice e set (itemWords flags it ++ (r.flatMap (itemWords flags) ++ [OP_FAILURE])) := by
      simpa [List.flatMap_cons, List.append_assoc] using hs
    have hrest := slice_right hs'
    have hhead := slice_left hs'
    rw [charset_step]
    cases it with
    | neg =>
      have h0 := hhead 0 (by simp [itemWords])
      simp only [itemWords, List.getD_cons_zero, Nat.add_zero] at h0
      simp only [h0, OP_NEGATE, OP_FAILURE, OP_LITERAL, OP_CATEGORY, OP_CHARSET, OP_RANGE,
        OP_RANGE_UNI_IGNORE]
      simpa [hitList] using ih f (set + 1) (!ok) hr hf' hrest
    | lit a =>
      have h0 := hhead 0 (by simp [itemWords])
      have h1 := hhead 1 (by simp [itemWords])
      simp only [itemWords, List.getD_cons_zero, Nat.add_zero, List.getD_cons_succ] at h0 h1
      simp only [h0, h1, OP_LITERAL, OP_FAILURE]
      simp only [hitList, siHit]
      by_cases hc : (ch == a) = true
      · simp [hc]
      · simp only [hc]
        simpa using ih f (set + 1 + 1) ok hr hf' hrest
    | rng a b =>
      have h0 := hhead 0 (by simp [itemWords])
      have h1 := hhead 1 (by simp [itemWords])
      have h2 := hhead 2 (by simp [itemWords])
      simp only [itemWords, List.getD_cons_zero, Nat.add_zero, List.getD_cons_succ] at h0 h1 h2
      simp only [h0, OP_RANGE, OP_FAILURE, OP_LITERAL, OP_CATEGORY, OP_CHARSET]
      simp only [hitList, siHit, h1, show set + 1 + 1 = set + 2 from rfl, h2]
      by_cases hc : a ≤ ch ∧ ch ≤ b
      · simp [hc]
      · have hc' : (decide (a ≤ ch) && decide (ch ≤ b)) = false := by
          simpa using fun h => not_and.1 hc h
        simp only [hc', hc]
        simpa using ih f (set + 2 + 1) ok hr hf' hrest
    | rngUni a b =>
      have h0 := hhead 0 (by simp [itemWords])
      have h1 := hhead 1 (by simp [itemWords])
      have h2 := hhead 2 (by simp [itemWords])
      simp only [itemWords, List.getD_cons_zero, Nat.add_zero, List.getD_cons_succ] at h0 h1 h2
      simp only [h0, OP_RANGE, OP_FAILURE, OP_LITERAL, OP_CATEGORY, OP_CHARSET, OP_RANGE_UNI_IGNORE]
      simp only [hitList, siHit, h1, show set + 1 + 1 = set + 2 from rfl, h2]
      by_cases hc : (a ≤ ch ∧ ch ≤ b) ∨ (a ≤ upperUnicode ch ∧ upperUnicode ch ≤ b)
      · have hc' : ((decide (a ≤ ch) && decide (ch ≤ b)) ||
            (decide (a ≤ upperUnicode ch) && decide (upperUnicode ch ≤ b))) = true := by
          simpa using hc
        rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
          if_neg (by decide), if_pos (by decide), if_pos hc]
        exact (if_pos hc').symm
      · have hc' : ((decide (a ≤ ch) && decide (ch ≤ b)) ||
            (decide (a ≤ upperUnicode ch) && decide (upperUnicode ch ≤ b))) = false := by
          simpa using hc
        simp only [hc, hc', if_false]
        simpa using ih f (set + 2 + 1) ok hr hf' hrest
    | cat k =>
      have h0 := hhead 0 (by simp [itemWords])
      have h1 := hhead 1 (by simp [itemWords])
      simp only [itemWords, List.getD_cons_zero, Nat.add_zero, List.getD_cons_succ] at h0 h1
      simp only [h0, h1, OP_FAILURE, OP_LITERAL, OP_CATEGORY]
      simp only [hitList, siHit]
      by_cases hc : sreCategory (catCode flags k) ch = true
      · simp [hc]
      · simp only [hc]
        simpa using ih f (set + 1 + 1) ok hr hf' hrest
    | charset d =>
      have hd : d.length = 8 := hw (.charset d) (by simp)
      have h0 := hhead 0 (by simp [itemWords])
      simp only [itemWords, List.getD_cons_zero, Nat.add_zero] at h0
      simp only [h0, OP_FAILURE, OP_LITERAL, OP_CATEGORY, OP_CHARSET]
      simp only [hitList, siHit]
      have hbit : (decide (ch < 256) && (e.c (set + 1 + ch / 32) / 2 ^ (ch % 32)) % 2 == 1) =
          (decide (ch < 256) && (d.getD (ch / 32) 0 / 2 ^ (ch % 32)) % 2 == 1) := by
        by_cases h256 : ch < 256
        · have h3 := hhead (1 + ch / 32) (by simp [itemWords, hd]; omega)
          simp only [itemWords, Nat.add_comm 1, List.getD_cons_succ] at h3
          rw [show set + 1 + ch / 32 = set + (ch / 32 + 1) by omega, h3]
        · simp [h256]
      rw [hbit]
      by_cases hc : (decide (ch < 256) && (d.getD (ch / 32) 0 / 2 ^ (ch % 32)) % 2 == 1) = true
      · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide), if_pos hc]
        exact (if_pos hc).symm
      · simp only [hc, Bool.false_eq_true, if_false]
        have := ih f (set + (itemWords flags (.charset d)).length) ok hr hf' hrest
        simp only [itemWords, List.length_cons, hd] at this
        rw [show set + 1 + 8 = set + (8 + 1) by omega]
        exact this
    | big d =>
      obtain ⟨hl, hc8, hidx⟩ : ItemWf (.big d) := hw (.big d) (by simp)
      have h0 := hhead 0 (by simp [itemWords])
      simp only [itemWords, List.getD_cons_zero, Nat.add_zero] at h0
      have hat : ∀ i, i < d.length → e.c (set + 1 + i) = d.getD i 0 := by
        intro i hi
        have h3 := hhead (i + 1) (by simp [itemWords]; omega)
        simp only [itemWords, List.getD_cons_succ] at h3
        rw [show set + 1 + i = set + (i + 1) by omega, h3]
      have hcount : e.c (set + 1) = d.headD 0 := by
        have := hat 0 (by omega)
        cases d with
        | nil => simp at hl
        | cons x t => simpa using this
      simp only [h0, OP_FAILURE, OP_LITERAL, OP_CATEGORY, OP_CHARSET, OP_RANGE, OP_RANGE_UNI_IGNORE,
        OP_NEGATE, OP_BIGCHARSET]
      simp only [hitList, siHit]
      have hbig : (if ch < 0x10000 then
            (e.c (set + 1 + 1 + 64 + ((e.c (set + 1 + 1 + ch / 256 / 4) / 256 ^ (ch / 256 % 4)) % 256 * 256 +
              ch % 256) / 32) / 2 ^ (ch % 32)) % 2 == 1
          else false) = bigHit d ch := by
        unfold bigHit
        by_cases hb : ch < 0x10000
        · simp only [hb, if_true]
          have h4 := hat (1 + ch / 256 / 4) (by omega)
          rw [show set + 1 + 1 + ch / 256 / 4 = set + 1 + (1 + ch / 256 / 4) by omega, h4]
          have h5 := hidx ch hb
          have h6 := hat _ h5
          rw [show set + 1 + 1 + 64 + ((d.getD (1 + ch / 256 / 4) 0 / 256 ^ (ch / 256 % 4)) % 256 * 256 +
              ch % 256) / 32 = set + 1 + (1 + 64 + ((d.getD (1 + ch / 256 / 4) 0 / 256 ^ (ch / 256 % 4)) % 256 * 256 +
              ch % 256) / 32) by omega, h6]
        · simp [hb]
      simp only [hbig, hcount]
      by_cases hc : bigHit d ch = true
      · simp [hc]
      · simp only [hc]
        have := ih f (set + (itemWords flags (.big d)).length) ok hr hf' hrest
        simp only [itemWords, List.length_cons] at this
        rw [show set + 1 + 1 + 64 + d.headD 0 * 8 = set + (d.length + 1) by omega]
        simpa using this

end PyLean.TextLibs.Re
