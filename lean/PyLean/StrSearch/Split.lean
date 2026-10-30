import PyLean.StrSearch.Basic

/-!
The split loops of split.h against the greedy specification `splitN`, and
the replace loops of unicodeobject.c / transmogrify.h against `intercalate`.
-/

set_option linter.deprecated false

namespace PyLean.StrSearch

open PyLean

/-- Prepend `c` to the first piece. -/
def consHead (c : Nat) : List Seq → List Seq
  | [] => [[c]]
  | a :: l => (c :: a) :: l

theorem intercalate_consHead (sep : Seq) (c : Nat) {L : List Seq} (h : L ≠ []) :
    sep.intercalate (consHead c L) = c :: sep.intercalate L := by
  match L, h with
  | [a], _ => simp [consHead]
  | a :: b :: l, _ => simp [consHead, List.intercalate_cons_cons]

theorem intercalate_cons_ne {sep a : Seq} {L : List Seq} (h : L ≠ []) :
    sep.intercalate (a :: L) = a ++ sep ++ sep.intercalate L := by
  match L, h with
  | b :: l, _ => simp [List.intercalate_cons_cons]

theorem findL_cons_nomatch {p : Seq} {c : Nat} {cs : Seq} (h : ¬ p.isPrefixOf (c :: cs) = true) :
    findL p (c :: cs) = (findL p cs).map (· + 1) := by
  simp [findL, h]

theorem splitN_cons_nomatch {p : Seq} {c : Nat} {cs : Seq} (hp : p ≠ [])
    (h : ¬ p.isPrefixOf (c :: cs) = true) (k : Nat) :
    splitN p k (c :: cs) = consHead c (splitN p k cs) := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [splitN, findL_cons_nomatch h]
    cases hf : findL p cs with
    | none => rfl
    | some i =>
      simp only [Option.map_some, consHead]
      rw [show i + 1 + p.length = (i + p.length) + 1 by omega]
      rfl

theorem splitN_cons_match {p : Seq} {c : Nat} {cs : Seq} (h : p.isPrefixOf (c :: cs) = true) (k : Nat) :
    splitN p (k + 1) (c :: cs) = [] :: splitN p k ((c :: cs).drop p.length) := by
  simp [splitN, findL, h]

/-! ## The split loops -/

theorem splitLoop_eq {sep : Seq} (hp : sep ≠ []) :
    ∀ (mc : Int) (s : Seq), splitLoop sep mc s = splitN sep mc.toNat s := by
  intro mc s
  induction s using (measure List.length).wf.induction generalizing mc with
  | _ s ih =>
    rw [splitLoop]
    by_cases hm : mc > 0
    · simp only [hm, hp, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
      obtain ⟨k, hk⟩ : ∃ k, mc.toNat = k + 1 := ⟨mc.toNat - 1, by omega⟩
      rw [hk, splitN]
      split
      · next pos hf =>
        try simp only [hf]
        congr 1
        rw [ih _ (length_drop_match hp hf).2, show (mc - 1).toNat = k by omega]
      · next hf => simp [hf]
    · simp only [hm, false_and, ↓reduceIte]
      rw [show mc.toNat = 0 by omega]; rfl

/-- `split_char` (split.h:100-140), the fast path for a one-character
separator, agrees with the general loop of `STRINGLIB(split)`. -/
theorem splitChar_eq (c : Nat) : ∀ (mc : Int) (s : Seq), splitChar c mc s = splitLoop [c] mc s := by
  intro mc s
  induction s using (measure List.length).wf.induction generalizing mc with
  | _ s ih =>
    rw [splitChar, splitLoop]
    by_cases hs : s = []
    · subst hs
      by_cases hm : mc > 0 <;> simp [hm, findL, List.isPrefixOf]
    · by_cases hm : mc > 0
      · rw [if_pos ⟨hs, hm⟩, if_pos ⟨hm, by simp⟩]
        split
        · next k hf =>
          try simp only [hf]
          congr 1
          rw [ih _ (show (s.drop (k + 1)).length < s.length by
            have := findL_le hf; simp at this ⊢; omega)]
          rfl
        · next hf => simp [hf]
      · rw [if_neg (by omega), if_neg (by omega)]

theorem rsplitCharLoop_eq (c : Nat) :
    ∀ (mc : Int) (s : Seq), rsplitCharLoop c mc s = rsplitLoop [c] mc s := by
  intro mc s
  induction s using (measure List.length).wf.induction generalizing mc with
  | _ s ih =>
    rw [rsplitCharLoop, rsplitLoop]
    by_cases hs : s = []
    · subst hs
      by_cases hm : mc > 0 <;> simp [hm, rfindL, List.isPrefixOf]
    · by_cases hm : mc > 0
      · rw [if_pos ⟨hs, hm⟩, if_pos ⟨hm, by simp⟩]
        split
        · next k hf =>
          try simp only [hf]
          congr 1
          rw [ih _ (show (s.take k).length < s.length by
            have := rfindL_le hf; simp at this ⊢; omega)]
        · next hf => simp [hf]
      · rw [if_neg (by omega), if_neg (by omega)]

/-- `rsplitLoop` stops by itself after at most `len / len(sep)` splits. -/
theorem rsplitLoop_sat {sep : Seq} (hp : sep ≠ []) :
    ∀ (s : Seq) (mc mc' : Int), (s.length / sep.length + 1 : Nat) ≤ mc → (s.length / sep.length + 1 : Nat) ≤ mc' →
      rsplitLoop sep mc s = rsplitLoop sep mc' s := by
  have hpl : sep.length ≥ 1 := List.length_pos_iff.mpr hp
  intro s
  induction s using (measure List.length).wf.induction with
  | _ s ih =>
    intro mc mc' hk hk'
    rw [rsplitLoop, rsplitLoop]
    have h1 : mc > 0 := by generalize s.length / sep.length = q at hk; omega
    have h2 : mc' > 0 := by generalize s.length / sep.length = q at hk'; omega
    rw [if_pos ⟨h1, hp⟩, if_pos ⟨h2, hp⟩]
    split
    · next pos hf =>
      try simp only [hf]
      congr 1
      have hl := rfindL_le hf
      have hlen : (s.take pos).length = pos := by simp; omega
      have hd : (s.take pos).length / sep.length + 1 ≤ s.length / sep.length := by
        rw [hlen]
        have : (pos + sep.length) / sep.length ≤ s.length / sep.length := Nat.div_le_div_right hl
        rw [Nat.add_div_right _ (by omega)] at this
        omega
      apply ih _ (show (s.take pos).length < s.length by rw [hlen]; omega)
      · generalize s.length / sep.length = q at *; generalize (s.take pos).length / sep.length = q' at *; omega
      · generalize s.length / sep.length = q at *; generalize (s.take pos).length / sep.length = q' at *; omega
    · next hf => simp [hf]

/-! ## The replace loops -/

theorem replaceChars_le (u1 u2 : Nat) : ∀ (mc : Int) (s : Seq), mc ≤ 0 → replaceChars u1 u2 mc s = s := by
  intro mc s
  induction s generalizing mc with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro h
    simp only [replaceChars, show ¬ mc > 0 by omega, and_false, ↓reduceIte, ih mc h]

/-- `replace_1char_inplace` is the split-join replacement for one character. -/
theorem replaceChars_eq (u1 u2 : Nat) :
    ∀ (mc : Int) (s : Seq), replaceChars u1 u2 mc s = [u2].intercalate (splitN [u1] mc.toNat s) := by
  intro mc s
  induction s generalizing mc with
  | nil =>
    cases h : mc.toNat <;> simp [replaceChars, splitN, findL, List.isPrefixOf]
  | cons c cs ih =>
    by_cases hm : mc > 0
    · by_cases hc : c = u1
      · subst hc
        obtain ⟨k, hk⟩ : ∃ k, mc.toNat = k + 1 := ⟨mc.toNat - 1, by omega⟩
        rw [hk, splitN_cons_match (by simp [List.isPrefixOf])]
        simp only [replaceChars, hm, and_self, ↓reduceIte, List.length_singleton, List.drop_succ_cons,
          List.drop_zero]
        rw [ih, intercalate_cons_ne (splitN_ne_nil _ _ _), show (mc - 1).toNat = k by omega]
        rfl
      · have hnp : ¬ [u1].isPrefixOf (c :: cs) = true := by
          simp [List.isPrefixOf]; exact fun h => hc h.symm
        rw [splitN_cons_nomatch (by simp) hnp, intercalate_consHead _ _ (splitN_ne_nil _ _ _)]
        simp only [replaceChars, hc, false_and, ↓reduceIte, ih]
    · rw [replaceChars_le u1 u2 mc _ (by omega), show mc.toNat = 0 by omega]
      simp [splitN]

/-- The counted copy loop is the split-join replacement. -/
theorem replaceLoop_eq {old : Seq} (new : Seq) (hp : old ≠ []) :
    ∀ (n : Nat) (s : Seq), replaceLoop old new n s = new.intercalate (splitN old n s) := by
  intro n
  induction n with
  | zero => intro s; simp [replaceLoop, splitN]
  | succ n ih =>
    intro s
    simp only [replaceLoop, splitN]
    split
    · simp
    · simp only [ih, intercalate_cons_ne (splitN_ne_nil _ _ _), List.append_assoc]

/-- The in-place loop for equal lengths is the split-join replacement. -/
theorem replaceInplace_eq {old : Seq} (new : Seq) (hp : old ≠ []) :
    ∀ (mc : Int) (s : Seq), replaceInplace old new mc s = new.intercalate (splitN old mc.toNat s) := by
  intro mc s
  induction s using (measure List.length).wf.induction generalizing mc with
  | _ s ih =>
    rw [replaceInplace]
    by_cases hm : mc > 0
    · simp only [hm, hp, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
      obtain ⟨k, hk⟩ : ∃ k, mc.toNat = k + 1 := ⟨mc.toNat - 1, by omega⟩
      rw [hk, splitN]
      split
      · next j hf =>
        try simp only [hf]
        rw [ih _ (length_drop_match hp hf).2, intercalate_cons_ne (splitN_ne_nil _ _ _),
          show (mc - 1).toNat = k by omega, List.append_assoc]
      · next hf => simp [hf]
    · simp only [hm, false_and, ↓reduceIte]
      rw [show mc.toNat = 0 by omega]; simp [splitN]

/-! ## Counting -/

theorem countN_succ_some {p s : Seq} {i : Nat} (h : findL p s = some i) (k : Nat) :
    countN p (k + 1) s = 1 + countN p k (s.drop (i + p.length)) := by
  simp only [countN, splitN, h, List.length_cons]
  have := splitN_ne_nil p k (s.drop (i + p.length))
  cases h' : splitN p k (s.drop (i + p.length)) with
  | nil => exact absurd h' this
  | cons _ _ => simp; omega

theorem countN_succ_none {p s : Seq} (h : findL p s = none) (k : Nat) : countN p (k + 1) s = 0 := by
  simp [countN, splitN, h]

/-- `splitN` with at least as many rounds as there are matches is the full split. -/
theorem splitN_ge_count {p : Seq} (hp : p ≠ []) :
    ∀ (k : Nat) (s : Seq), countAll p s ≤ k → splitN p k s = splitAll p s := by
  intro k
  induction k with
  | zero =>
    intro s h
    cases hf : findL p s with
    | none => rw [splitAll_none hf]; rfl
    | some i => rw [countAll_some hp hf] at h; omega
  | succ k ih =>
    intro s h
    cases hf : findL p s with
    | none => rw [splitAll_none hf]; simp [splitN, hf]
    | some i =>
      rw [splitAll_some hp hf, countAll_some hp hf] at *
      simp only [splitN, hf]
      rw [ih _ (by omega)]

theorem countN_eq_min {p : Seq} (hp : p ≠ []) :
    ∀ (k : Nat) (s : Seq), countN p k s = min (countAll p s) k := by
  intro k
  induction k with
  | zero => intro s; simp [countN, splitN]
  | succ k ih =>
    intro s
    cases hf : findL p s with
    | none => rw [countN_succ_none hf, countAll_none hf]; simp
    | some i => rw [countN_succ_some hf, countAll_some hp hf, ih]; omega

theorem splitN_count {p : Seq} (hp : p ≠ []) (k : Nat) (s : Seq) :
    splitN p (countN p k s) s = splitN p k s := by
  rw [countN_eq_min hp]
  rcases Nat.le_total (countAll p s) k with h | h
  · rw [Nat.min_eq_left h, splitN_ge_count hp _ _ (Nat.le_refl _), splitN_ge_count hp _ _ h]
  · rw [Nat.min_eq_right h]

/-- Length of the split-join replacement. -/
theorem length_intercalate_splitN {p : Seq} (new : Seq) (hp : p ≠ []) :
    ∀ (k : Nat) (s : Seq), ((new.intercalate (splitN p k s)).length : Int) =
      s.length + countN p k s * ((new.length : Int) - p.length) := by
  intro k
  induction k with
  | zero => intro s; simp [splitN, countN]
  | succ k ih =>
    intro s
    cases hf : findL p s with
    | none => rw [countN_succ_none hf]; simp [splitN, hf]
    | some i =>
      rw [countN_succ_some hf]
      simp only [splitN, hf]
      rw [intercalate_cons_ne (splitN_ne_nil _ _ _)]
      have hl := findL_le hf
      have hL := ih (s.drop (i + p.length))
      simp only [List.length_drop] at hL
      simp only [List.length_append, List.length_take]
      have hm : ((1 + countN p k (s.drop (i + p.length)) : Nat) : Int) * ((new.length : Int) - p.length) =
          ((new.length : Int) - p.length) + (countN p k (s.drop (i + p.length)) : Int) *
            ((new.length : Int) - p.length) := by
        rw [Int.natCast_add, Int.add_mul, Int.natCast_one, Int.one_mul]
      rw [hm]
      generalize (countN p k (s.drop (i + p.length)) : Int) * ((new.length : Int) - p.length) = cx at *
      omega

/-- The split-join replacement reconstructs the string when `new = old`. -/
theorem intercalate_splitN {p : Seq} (hp : p ≠ []) :
    ∀ (k : Nat) (s : Seq), p.intercalate (splitN p k s) = s := by
  intro k
  induction k with
  | zero => intro s; simp [splitN]
  | succ k ih =>
    intro s
    cases hf : findL p s with
    | none => simp [splitN, hf]
    | some i =>
      simp only [splitN, hf]
      rw [intercalate_cons_ne (splitN_ne_nil _ _ _), ih]
      have ho := (findL_eq_some.mp hf).1
      have e := ho.2
      have hd : s.drop (i + p.length) = (s.drop i).drop p.length := by rw [List.drop_drop]
      rw [hd]
      calc s.take i ++ p ++ (s.drop i).drop p.length
          = s.take i ++ ((s.drop i).take p.length ++ (s.drop i).drop p.length) := by
            rw [e, List.append_assoc]
        _ = s := by rw [List.take_append_drop, List.take_append_drop]

end PyLean.StrSearch
