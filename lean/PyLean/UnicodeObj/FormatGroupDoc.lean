import PyLean.UnicodeObj.FormatFloat

/-!
Where `_PyUnicode_InsertThousandsGrouping` puts separators and zeros, unicode_formatter.c:135-243,
with `GroupGenerator_init` (:22-27), `GroupGenerator_next` (:32-51) and
`InsertThousandsGrouping_fill` (:57-108), against the documented layout (Doc/library/string.rst,
"grouping": "Inserts a comma every 3 digits", "underscores are inserted every 4 digits"; the
width is "the minimum total field width, including any prefixes, separators, and other
formatting characters", and `'0'` before the width pads with zeros).

The specification is written without the loop: `groupFR` places a separator between groups of
`g` digits counted from the right (the decimal point), `groupFL` between groups counted from the
left (for the fraction, also from the decimal point). Zero padding adds the fewest leading zeros
that make the grouped text reach the width.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- Digits given least significant first, laid out most significant first with `sep` between
groups of `g`. -/
def groupRev (g : Nat) (sep : Str) (R : Str) : Str :=
  if R.length ≤ g ∨ g = 0 then R.reverse
  else groupRev g sep (R.drop g) ++ sep ++ (R.take g).reverse
termination_by R.length
decreasing_by simp_wf; omega

/-- The digits `D` (most significant first) with `sep` between groups of `g` counted from the
right: `groupFR_short` and `groupFR_split` are its two equations. -/
def groupFR (g : Nat) (sep : Str) (D : Str) : Str := groupRev g sep D.reverse

/-- The digits `D` with `sep` between groups of `g` counted from the left. -/
def groupFL (g : Nat) (sep : Str) (D : Str) : Str :=
  if D.length ≤ g ∨ g = 0 then D else D.take g ++ sep ++ groupFL g sep (D.drop g)
termination_by D.length
decreasing_by simp_wf; omega

theorem groupRev_short {g : Nat} {sep R : Str} (h : R.length ≤ g) : groupRev g sep R = R.reverse := by
  rw [groupRev, if_pos (Or.inl h)]

theorem groupRev_split {g : Nat} {sep R : Str} (hg : 0 < g) (h : g < R.length) :
    groupRev g sep R = groupRev g sep (R.drop g) ++ sep ++ (R.take g).reverse := by
  rw [groupRev, if_neg (by omega)]

/-- A group of `g` or fewer digits stands alone. -/
theorem groupFR_short {g : Nat} {sep D : Str} (h : D.length ≤ g) : groupFR g sep D = D := by
  simp [groupFR, groupRev_short (show D.reverse.length ≤ g by simpa using h)]

/-- Longer: the last `g` digits, after a separator, after the grouping of the rest. -/
theorem groupFR_split {g : Nat} {sep D : Str} (hg : 0 < g) (h : g < D.length) :
    groupFR g sep D = groupFR g sep (D.take (D.length - g)) ++ sep ++ D.drop (D.length - g) := by
  unfold groupFR
  rw [groupRev_split hg (by simpa using h)]
  rw [List.reverse_take, List.drop_reverse]
  simp

theorem groupFR_zero (sep D : Str) : groupFR 0 sep D = D := by
  unfold groupFR; rw [groupRev, if_pos (Or.inr rfl)]; simp

theorem groupFL_short {g : Nat} {sep D : Str} (h : D.length ≤ g) : groupFL g sep D = D := by
  rw [groupFL, if_pos (Or.inl h)]

theorem groupFL_split {g : Nat} {sep D : Str} (hg : 0 < g) (h : g < D.length) :
    groupFL g sep D = D.take g ++ sep ++ groupFL g sep (D.drop g) := by
  rw [groupFL, if_neg (by omega)]

/-! ## The backward loop: the integer digits -/

theorem rev_zeros_take {R : Str} {C Z k g : Nat} (hC : C = min R.length g) (hZ : Z = g - C)
    (hcase : C = g ∨ C = R.length) :
    (R ++ List.replicate (Z + k) 48).take g = R.take C ++ List.replicate Z 48 := by
  rcases hcase with h | h
  · have hz : Z = 0 := by omega
    subst hz
    rw [List.take_append_of_le_length (by omega)]
    simp [h]
  · rw [List.take_append, List.take_of_length_le (by omega), h, List.take_replicate]
    simp only [List.take_length]
    congr 2
    omega

theorem rev_zeros_drop {R : Str} {C Z k g : Nat} (hC : C = min R.length g) (hZ : Z = g - C)
    (hcase : C = g ∨ C = R.length) :
    (R ++ List.replicate (Z + k) 48).drop g = R.drop C ++ List.replicate k 48 := by
  rcases hcase with h | h
  · have hz : Z = 0 := by omega
    subst hz
    rw [List.drop_append_of_le_length (by omega)]
    simp [h]
  · rw [List.drop_append, List.drop_of_length_le (by omega), List.drop_replicate]
    rw [h, List.drop_length, List.nil_append]
    congr 1
    omega

/-- The loop of `_PyUnicode_InsertThousandsGrouping` walking backwards with grouping `[g]`: from
any state it ends with the remaining digits `R` (least significant first), padded with the fewest
zeros that reach `mw`, grouped by `g` from the right, in front of what it had written. -/
theorem backLoop (g : Nat) (sep : Str) (hg0 : 0 < g) (hg1 : g < 127) :
    ∀ (fuel i prev : Nat) (useSep : Bool) (R : Str) (mw : Int) (count : Nat) (out : Str) (it : Nat),
      ((i = 0 ∧ prev = 0) ∨ (i = 1 ∧ prev = g)) → R.length + mw.toNat + 1 < fuel →
      ∃ k n it', groupLoop [g] sep fuel i prev useSep R.length mw R count out it =
          .ok (n, groupRev g sep (R ++ List.replicate k 48) ++ (if useSep then sep else []) ++ out, it') ∧
        R ++ List.replicate k 48 ≠ [] ∧ mw ≤ (groupRev g sep (R ++ List.replicate k 48)).length ∧
        (k = 0 ∨ R ++ List.replicate (k - 1) 48 = [] ∨
          ((groupRev g sep (R ++ List.replicate (k - 1) 48)).length : Int) < mw) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro i prev useSep R mw count out it hi hfuel
    have hN := groupNext_single g (by omega) (by omega) i prev hi
    obtain ⟨L, hL⟩ : ∃ L : Nat, (L : Int) = min (g : Int) (max (max (R.length : Int) mw) 1) :=
      ⟨(min (g : Int) (max (max (R.length : Int) mw) 1)).toNat, by omega⟩
    have hL1 : 1 ≤ L := by omega
    have hLg : L ≤ g := by omega
    obtain ⟨C, hC⟩ : ∃ C, C = min R.length L := ⟨_, rfl⟩
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = L - C := ⟨_, rfl⟩
    have e1 : max 0 ((L : Int) - R.length) = (Z : Int) := by omega
    have e2 : max 0 (min (R.length : Int) (L : Int)) = (C : Int) := by omega
    simp only [groupLoop, hN, gt_iff_lt, show (0 : Nat) < g from hg0, if_true, ← hL, e1, e2,
      groupPiece, Int.toNat_natCast]
    have hgroup : (R.take C ++ List.replicate Z 48).reverse =
        List.replicate Z 48 ++ (R.take C).reverse := by simp
    by_cases hb : ((R.length : Int) - C ≤ 0 ∧ mw - L ≤ 0)
    · rw [if_pos hb]
      have hCn : C = R.length := by omega
      have hlen : (R ++ List.replicate Z 48).length = L := by simp; omega
      have hshort : groupRev g sep (R ++ List.replicate Z 48) = List.replicate Z 48 ++ R.reverse := by
        rw [groupRev_short (by omega)]; simp
      refine ⟨Z, (count + (if useSep = true then sep.length else 0)) + Z + C, it + 1, ?_, ?_, ?_, ?_⟩
      · (rw [hshort, hCn, List.take_length]) <;> simp [List.append_assoc]
      · intro e; rw [e] at hlen; simp at hlen; omega
      · rw [groupRev_short (by omega), List.length_reverse, hlen]; omega
      · by_cases hz : Z = 0
        · exact Or.inl hz
        · right
          by_cases hL1' : L = 1
          · left
            have hR0 : R.length = 0 := by omega
            have hR : R = [] := List.eq_nil_of_length_eq_zero hR0
            subst hR
            rw [show Z - 1 = 0 by omega]
            rfl
          · right
            have hl2 : (R ++ List.replicate (Z - 1) 48).length = L - 1 := by
              simp only [List.length_append, List.length_replicate]; omega
            rw [groupRev_short (by omega), List.length_reverse, hl2]
            omega
    · rw [if_neg hb]
      have hLg' : L = g := by omega
      have hcase : C = g ∨ C = R.length := by omega
      have hfuel' : (R.drop C).length + (mw - L - sep.length).toNat + 1 < fuel := by
        simp only [List.length_drop]; omega
      have hrem : (R.length : Int) - C = ((R.drop C).length : Int) := by simp; omega
      rw [hrem]
      obtain ⟨k', n, it', hrun, hne, hmw, hmin⟩ := ih 1 g true (R.drop C) (mw - L - sep.length) _
        (List.replicate Z 48 ++ (R.take C).reverse ++ (if useSep = true then sep else []) ++ out)
        (it + 1) (Or.inr ⟨rfl, rfl⟩) hfuel'
      have hC' : C = min R.length g := by omega
      have hZ' : Z = g - C := by omega
      have htake := rev_zeros_take (k := k') hC' hZ' hcase
      have hdrop := rev_zeros_drop (k := k') hC' hZ' hcase
      have hlong : g < (R ++ List.replicate (Z + k') 48).length := by
        have : 0 < (R.drop C ++ List.replicate k' 48).length := by
          cases h : R.drop C ++ List.replicate k' 48 with
          | nil => exact absurd h hne
          | cons _ _ => simp
        simp only [List.length_append, List.length_replicate, List.length_drop] at this ⊢
        omega
      have hsplit : groupRev g sep (R ++ List.replicate (Z + k') 48) =
          groupRev g sep (R.drop C ++ List.replicate k' 48) ++ sep ++
            (List.replicate Z 48 ++ (R.take C).reverse) := by
        rw [groupRev_split hg0 hlong, hdrop, htake, hgroup]
      refine ⟨Z + k', n, it', ?_, ?_, ?_, ?_⟩
      · rw [hrun, hsplit]
        simp [List.append_assoc]
      · intro e; rw [e] at hlong; simp at hlong
      · rw [hsplit]; simp only [List.length_append, List.length_replicate, List.length_reverse,
          List.length_take]; omega
      · by_cases hk : Z + k' = 0
        · exact Or.inl hk
        right
        have hlenC : (R.drop C).length = R.length - C := List.length_drop ..
        by_cases hE : R.drop C ++ List.replicate (k' - 1) 48 = []
        · -- the zeros ran out on a full group of `g`: one digit fewer stays under `mw`
          have hk0 : k' ≠ 0 := by
            intro h; subst h; exact hne (by simpa using hE)
          have h1 := List.append_eq_nil_iff.1 hE
          have hRC : C = R.length := by
            have := congrArg List.length h1.1; rw [hlenC] at this; simp at this; omega
          have h2 := h1.2
          simp only [List.replicate_eq_nil_iff] at h2
          right
          have hl : (R ++ List.replicate (Z + k' - 1) 48).length = g := by
            simp only [List.length_append, List.length_replicate]; omega
          rw [groupRev_short (by omega), List.length_reverse, hl]
          omega
        · right
          rcases hmin with h0 | h0 | h0
          · subst h0
            exfalso
            have hZ0 : Z ≠ 0 := by omega
            apply hE
            have : R.drop C = [] := by
              rw [List.drop_eq_nil_iff]; omega
            simp [this]
          · exact absurd h0 hE
          · have hk0 : k' ≠ 0 := by
              intro h; subst h
              have hZ0 : Z ≠ 0 := by omega
              apply hE
              have : R.drop C = [] := by
                rw [List.drop_eq_nil_iff]; omega
              simp [this]
            have hlong2 : g < (R ++ List.replicate (Z + (k' - 1)) 48).length := by
              have : 0 < (R.drop C ++ List.replicate (k' - 1) 48).length := by
                cases h : R.drop C ++ List.replicate (k' - 1) 48 with
                | nil => exact absurd h hE
                | cons _ _ => simp
              simp only [List.length_append, List.length_replicate, List.length_drop] at this ⊢
              omega
            have htake2 := rev_zeros_take (k := k' - 1) hC' hZ' hcase
            have hdrop2 := rev_zeros_drop (k := k' - 1) hC' hZ' hcase
            rw [show Z + k' - 1 = Z + (k' - 1) by omega, groupRev_split hg0 hlong2, hdrop2, htake2,
              hgroup]
            simp only [List.length_append, List.length_replicate, List.length_reverse, List.length_take]
            push_cast
            omega

/-- `_PyUnicode_InsertThousandsGrouping` against the docs, for the backward (integer part) call
with a grouping of one repeated size `g` (CHAR_MAX = 127 would mean "no grouping") and any
separator: the text is the digits padded with leading zeros and grouped by `g` from the right,
with exactly as many zeros as it takes to reach `min_width` (none if it is reached already), and
the count it returns is the text's length. -/
def GroupingPlacement : Prop :=
  ∀ (g : Nat) (sep ds : Str) (w : Int), 0 < g → g < 127 → ds ≠ [] →
    ∃ k n it, insertThousandsGrouping ds w [g] sep =
        .ok (n, groupFR g sep (List.replicate k 48 ++ ds), it) ∧
      n = (groupFR g sep (List.replicate k 48 ++ ds)).length ∧
      w ≤ (groupFR g sep (List.replicate k 48 ++ ds)).length ∧
      (k = 0 ∨ ((groupFR g sep (List.replicate (k - 1) 48 ++ ds)).length : Int) < w)

theorem groupingPlacement_proven : GroupingPlacement := by
  intro g sep ds w hg0 hg1 hne
  obtain ⟨k, n, it, hrun, hne', hmw, hmin⟩ := backLoop g sep hg0 hg1
    (ds.length + (max 0 w).toNat + 2) 0 0 false ds.reverse (max 0 w) 0 [] 0 (Or.inl ⟨rfl, rfl⟩)
    (by simp only [List.length_reverse]; omega)
  have hrev : ∀ j, ds.reverse ++ List.replicate j 48 = (List.replicate j 48 ++ ds).reverse := by
    intro j; simp
  have hrun' : insertThousandsGrouping ds w [g] sep =
      .ok (n, groupFR g sep (List.replicate k 48 ++ ds), it) := by
    unfold insertThousandsGrouping groupFR
    have : ((ds.reverse.length : Nat) : Int) = (ds.length : Int) := by simp
    rw [this] at hrun
    (rw [hrun, hrev]) <;> simp
  refine ⟨k, n, it, hrun', ?_, ?_, ?_⟩
  · have := insert_len hrun'
    exact this.symm
  · unfold groupFR; rw [← hrev]; omega
  · rcases hmin with h | h | h
    · exact Or.inl h
    · exfalso; apply hne; simpa using (List.append_eq_nil_iff.1 h).1
    · right; unfold groupFR; rw [← hrev]; omega

/-! ## The forward loop: the fraction -/

theorem fwdLoop (g : Nat) (sep : Str) (hg0 : 0 < g) (hg1 : g < 127) :
    ∀ (fuel i prev : Nat) (useSep : Bool) (D : Str) (mw : Int) (count : Nat) (out : Str),
      ((i = 0 ∧ prev = 0) ∨ (i = 1 ∧ prev = g)) → mw ≤ D.length → D ≠ [] → D.length < fuel →
      ∃ n, groupLoopFwd [g] sep fuel i prev useSep D.length mw D count out =
        .ok (n, out ++ (if useSep then sep else []) ++ groupFL g sep D) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro i prev useSep D mw count out hi hmw hne hfuel
    have hL0 : 0 < D.length := List.length_pos_iff.2 hne
    have hN := groupNext_single g (by omega) (by omega) i prev hi
    obtain ⟨L, hL⟩ : ∃ L, L = min g D.length := ⟨_, rfl⟩
    have e1 : min (g : Int) (max (max (D.length : Int) mw) 1) = L := by omega
    have e2 : max 0 ((L : Int) - D.length) = 0 := by omega
    have e3 : max 0 (min (D.length : Int) (L : Int)) = L := by omega
    simp only [groupLoopFwd, hN, gt_iff_lt, show (0 : Nat) < g from hg0, if_true, e1, e2, e3,
      groupPieceFwd, Int.toNat_zero, Int.toNat_natCast, List.replicate_zero, List.append_nil]
    by_cases hb : D.length ≤ g
    · have hc : ((D.length : Int) - L ≤ 0 ∧ mw - L ≤ 0) := by omega
      rw [if_pos hc, groupFL_short hb, show L = D.length by omega, List.take_length]
      exact ⟨_, rfl⟩
    · have hc : ¬ ((D.length : Int) - L ≤ 0 ∧ mw - L ≤ 0) := by omega
      rw [if_neg hc]
      have hLg : L = g := by omega
      have hcast : (D.length : Int) - L = ((D.drop L).length : Int) := by
        simp only [List.length_drop]; omega
      rw [hcast]
      obtain ⟨n, hn⟩ := ih 1 g true (D.drop L) (mw - L - sep.length) _
        (out ++ (if useSep = true then sep else []) ++ D.take L) (Or.inr ⟨rfl, rfl⟩)
        (by simp only [List.length_drop]; omega)
        (by intro h; have := congrArg List.length h; simp only [List.length_drop, List.length_nil] at this; omega)
        (by simp only [List.length_drop]; omega)
      refine ⟨n, ?_⟩
      rw [hn, groupFL_split hg0 (Nat.lt_of_not_le hb), hLg]
      simp [List.append_assoc]

/-- The forward call `calc_number_widths` and `fill_number` make for the fraction
(unicode_formatter.c:822-826, 985-988, `min_width` = the fraction's length): the fraction grouped by
`g` from the decimal point, and nothing else. -/
def GroupingFraction : Prop :=
  ∀ (g : Nat) (sep frac : Str), 0 < g → g < 127 → frac ≠ [] →
    ∃ n, insertGroupingFwd frac frac.length [g] sep = .ok (n, groupFL g sep frac)

theorem groupingFraction_proven : GroupingFraction := by
  intro g sep frac hg0 hg1 hne
  obtain ⟨n, h⟩ := fwdLoop g sep hg0 hg1 (frac.length + (max 0 (frac.length : Int)).toNat + 2) 0 0
    false frac (max 0 (frac.length : Int)) 0 [] (Or.inl ⟨rfl, rfl⟩) (by omega) hne (by omega)
  exact ⟨n, by simpa [insertGroupingFwd] using h⟩

/-! ## Zero padding, as the docs describe it -/

theorem groupRev_length (g : Nat) (sep : Str) :
    ∀ (n : Nat) (R : Str), R.length = n →
      (groupRev g sep R).length = R.length + (R.length - 1) / g * sep.length := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro R hR
    by_cases hs : R.length ≤ g ∨ g = 0
    · rw [groupRev, if_pos hs]
      rcases hs with hs | hs
      · have : (R.length - 1) / g = 0 := by
          rcases Nat.eq_zero_or_pos g with h | h
          · simp [h]
          · exact Nat.div_eq_of_lt (by omega)
        simp [this]
      · subst hs; simp
    · rw [groupRev, if_neg hs]
      have hg : 0 < g := by omega
      have hl : (R.drop g).length = R.length - g := List.length_drop ..
      have := ih (R.length - g) (by omega) (R.drop g) hl
      simp only [List.length_append, List.length_reverse, List.length_take, this, hl]
      have hd : (R.length - 1) / g = (R.length - g - 1) / g + 1 := by
        rw [show R.length - 1 = (R.length - g - 1) + g by omega, Nat.add_div_right _ hg]
      rw [hd, Nat.add_mul, Nat.one_mul]
      have : min g R.length = g := by omega
      rw [this]
      omega

theorem groupFR_length (g : Nat) (sep D : Str) :
    (groupFR g sep D).length = D.length + (D.length - 1) / g * sep.length := by
  unfold groupFR
  rw [groupRev_length g sep _ D.reverse rfl]
  simp

/-- The first `k ≥ start` (within `fuel` steps) where `p` holds. -/
def firstFromK (p : Nat → Bool) : Nat → Nat → Nat
  | 0, k => k
  | fuel + 1, k => if p k then k else firstFromK p fuel (k + 1)

theorem firstFrom_spec (p : Nat → Bool) :
    ∀ (fuel k : Nat), p (k + fuel) = true →
      p (firstFromK p fuel k) = true ∧ k ≤ firstFromK p fuel k ∧
        ∀ j, k ≤ j → j < firstFromK p fuel k → p j = false := by
  intro fuel
  induction fuel with
  | zero =>
    intro k h
    simp only [firstFromK]
    exact ⟨by simpa using h, Nat.le_refl _, fun j h1 h2 => by omega⟩
  | succ fuel ih =>
    intro k h
    simp only [firstFromK]
    by_cases hk : p k = true
    · rw [if_pos hk]
      exact ⟨hk, Nat.le_refl _, fun j h1 h2 => by omega⟩
    · rw [if_neg hk]
      obtain ⟨a, b, c⟩ := ih (k + 1) (by rw [show k + 1 + fuel = k + (fuel + 1) by omega]; exact h)
      refine ⟨a, by omega, fun j h1 h2 => ?_⟩
      by_cases hj : j = k
      · subst hj; simpa using hk
      · exact c j (by omega) h2

/-- How many leading zeros the docs' zero padding adds: the fewest that make the digits `ds`,
grouped by `g` with `sep`, at least `w` long. -/
def zerosFor (g : Nat) (sep ds : Str) (w : Int) : Nat :=
  firstFromK (fun k => decide (w ≤ ((groupFR g sep (List.replicate k 48 ++ ds)).length : Int))) w.toNat 0

/-- The digits `ds` zero padded to `w` and grouped. -/
def zeroGrouped (g : Nat) (sep ds : Str) (w : Int) : Str :=
  groupFR g sep (List.replicate (zerosFor g sep ds w) 48 ++ ds)

theorem len_mono (g : Nat) (sep ds : Str) {j k : Nat} (h : j ≤ k) :
    (groupFR g sep (List.replicate j 48 ++ ds)).length ≤
      (groupFR g sep (List.replicate k 48 ++ ds)).length := by
  rw [groupFR_length, groupFR_length]
  simp only [List.length_append, List.length_replicate]
  have : (j + ds.length - 1) / g ≤ (k + ds.length - 1) / g := Nat.div_le_div_right (by omega)
  have := Nat.mul_le_mul_right sep.length this
  omega

theorem len_ge (g : Nat) (sep ds : Str) (k : Nat) :
    k ≤ (groupFR g sep (List.replicate k 48 ++ ds)).length := by
  rw [groupFR_length]; simp; omega

/-- The zero padding is pinned by two facts: it reaches `w`, and one zero fewer would not. -/
theorem zerosFor_unique (g : Nat) (sep ds : Str) (w : Int) (k : Nat)
    (h1 : w ≤ (groupFR g sep (List.replicate k 48 ++ ds)).length)
    (h2 : k = 0 ∨ ((groupFR g sep (List.replicate (k - 1) 48 ++ ds)).length : Int) < w) :
    zerosFor g sep ds w = k := by
  have hp : (fun k => decide (w ≤ ((groupFR g sep (List.replicate k 48 ++ ds)).length : Int)))
      (0 + w.toNat) = true := by
    have := len_ge g sep ds w.toNat
    simp only [Nat.zero_add, decide_eq_true_eq]; omega
  obtain ⟨a, -, c⟩ := firstFrom_spec (fun k => decide (w ≤ ((groupFR g sep (List.replicate k 48 ++ ds)).length : Int))) w.toNat 0 hp
  unfold zerosFor
  generalize hm : firstFromK _ w.toNat 0 = m at a c
  simp only [decide_eq_true_eq] at a
  rcases Nat.lt_trichotomy k m with hlt | heq | hgt
  · have := c k (by omega) hlt
    simp only [decide_eq_false_iff_not] at this
    omega
  · exact heq.symm
  · rcases h2 with h2 | h2
    · omega
    · have := len_mono g sep ds (show m ≤ k - 1 by omega)
      omega

theorem zerosFor_reach (g : Nat) (sep ds : Str) (w : Int) :
    w ≤ (zeroGrouped g sep ds w).length := by
  have hp : (fun k => decide (w ≤ ((groupFR g sep (List.replicate k 48 ++ ds)).length : Int)))
      (0 + w.toNat) = true := by
    have := len_ge g sep ds w.toNat
    simp only [Nat.zero_add, decide_eq_true_eq]; omega
  obtain ⟨a, -, -⟩ := firstFrom_spec (fun k => decide (w ≤ ((groupFR g sep (List.replicate k 48 ++ ds)).length : Int))) w.toNat 0 hp
  simpa [zeroGrouped, zerosFor] using a

theorem zerosFor_nonpos (g : Nat) (sep ds : Str) (w : Int) (hw : w ≤ 0) : zerosFor g sep ds w = 0 :=
  zerosFor_unique g sep ds w 0 (by omega) (Or.inl rfl)

/-- `_PyUnicode_InsertThousandsGrouping` for the integer part, in the documented terms: with a
grouping `[g]` (`0 < g < 127`) the digits padded and grouped by `g` with `sep`, with no grouping
(`[CHAR_MAX]` or the C locale's empty string) the digits padded, for every `min_width`. -/
theorem insert_doc (ds : Str) (hne : ds ≠ []) (mw : Int) (gr : List Nat) (g : Nat) (sep : Str)
    (h : (0 < g ∧ g < 127 ∧ gr = [g]) ∨ (g = 0 ∧ (gr = [127] ∨ gr = []))) :
    ∃ it, insertThousandsGrouping ds mw gr sep =
      .ok ((zeroGrouped g sep ds mw).length, zeroGrouped g sep ds mw, it) := by
  rcases h with ⟨h0, h1, rfl⟩ | ⟨rfl, hgr⟩
  · obtain ⟨k, n, it, hrun, hn, hw, hmin⟩ := groupingPlacement_proven g sep ds mw h0 h1 hne
    have hk := zerosFor_unique g sep ds mw k hw hmin
    refine ⟨it, ?_⟩
    rw [hrun, hn]
    unfold zeroGrouped
    rw [hk]
  · obtain ⟨it, h⟩ := noGroupMin ds hne mw gr hgr sep
    have hk : zerosFor 0 sep ds mw = (mw - ds.length).toNat := by
      apply zerosFor_unique
      · rw [groupFR_length]
        simp only [List.length_append, List.length_replicate, Nat.div_zero, Nat.zero_mul, Nat.add_zero]
        omega
      · by_cases h0 : (mw - ds.length).toNat = 0
        · exact Or.inl h0
        · right
          rw [groupFR_length]
          simp only [List.length_append, List.length_replicate, Nat.div_zero, Nat.zero_mul, Nat.add_zero]
          omega
    refine ⟨it, ?_⟩
    rw [h]
    unfold zeroGrouped
    rw [hk, groupFR_zero]
    simp only [List.length_append, List.length_replicate]
    congr 2
    omega

theorem groupRev_map (φ : Nat → Nat) (g : Nat) (sep : Str) :
    ∀ (n : Nat) (R : Str), R.length = n → (groupRev g sep R).map φ = groupRev g (sep.map φ) (R.map φ) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro R hR
    by_cases hs : R.length ≤ g ∨ g = 0
    · have e1 : groupRev g sep R = R.reverse := by rw [groupRev, if_pos hs]
      have e2 : groupRev g (sep.map φ) (R.map φ) = (R.map φ).reverse := by
        rw [groupRev, if_pos (by simpa using hs)]
      rw [e1, e2, List.map_reverse]
    · have e1 : groupRev g sep R = groupRev g sep (R.drop g) ++ sep ++ (R.take g).reverse := by
        rw [groupRev, if_neg hs]
      have e2 : groupRev g (sep.map φ) (R.map φ) =
          groupRev g (sep.map φ) ((R.map φ).drop g) ++ sep.map φ ++ ((R.map φ).take g).reverse := by
        rw [groupRev, if_neg (by simpa using hs)]
      have := ih (R.length - g) (by omega) (R.drop g) (by simp)
      rw [e1, e2, List.map_append, List.map_append, this, List.map_reverse, List.map_take, List.map_drop]

/-- Mapping the characters commutes with the zero-padded grouping, when it fixes `'0'`. -/
theorem zeroGrouped_map (φ : Nat → Nat) (h0 : φ 48 = 48) (g : Nat) (sep ds : Str) (w : Int) :
    (zeroGrouped g sep ds w).map φ = zeroGrouped g (sep.map φ) (ds.map φ) w := by
  have hk : zerosFor g (sep.map φ) (ds.map φ) w = zerosFor g sep ds w := by
    unfold zerosFor
    congr 1
    funext k
    simp only [groupFR_length, List.length_append, List.length_replicate, List.length_map]
  unfold zeroGrouped groupFR
  rw [hk, groupRev_map φ g sep _ _ rfl]
  simp [List.map_reverse, List.map_replicate, h0]

/-! ## A number laid out as the docs describe it -/

/-- The padding of a number to the width: the fill on the right (`<`), the left (`>`), both
sides (`^`, the odd one on the right), or between the sign and prefix and the digits (`=`). -/
def padLayout (f : FormatSpec) (sg pfx body tail : Str) : Str :=
  let p := (f.width - (sg.length + pfx.length + body.length + tail.length)).toNat
  if f.align = 60 then sg ++ pfx ++ body ++ tail ++ List.replicate p f.fillChar
  else if f.align = 94 then
    List.replicate (p / 2) f.fillChar ++ sg ++ pfx ++ body ++ tail ++ List.replicate (p - p / 2) f.fillChar
  else if f.align = 61 then sg ++ pfx ++ List.replicate p f.fillChar ++ body ++ tail
  else List.replicate p f.fillChar ++ sg ++ pfx ++ body ++ tail

/-- The sign the docs ask for: `-` for a negative number, else `+` for the `+` option, a space for
the space option, nothing otherwise. -/
def signStr (opt : Nat) (neg : Bool) : Str :=
  if neg then [45] else if opt = 43 then [43] else if opt = 32 then [32] else []

/-- A number as the docs lay it out: the sign, a prefix, the integer digits `ds` grouped by `g`
with `sep`, and `tail` (decimal point, grouped fraction, exponent or `%`). With the `0` fill and `=`
alignment the padding is leading zeros among the digits, grouped with them; otherwise it is the fill
on the right (`<`), the left (`>`), both sides (`^`, the odd one on the right) or between the sign
and prefix and the digits (`=`). -/
def docNumber (sg pfx ds : Str) (g : Nat) (sep tail : Str) (f : FormatSpec) : Str :=
  if f.fillChar = 48 ∧ f.align = 61 ∧ ds ≠ [] then
    sg ++ pfx ++ zeroGrouped g sep ds (f.width - sg.length - pfx.length - tail.length) ++ tail
  else padLayout f sg pfx (groupFR g sep ds) tail

/-- `padFields` (the switch on the alignment in `calc_number_widths`) and the order
`fill_number` writes the fields in give `padLayout`. -/
theorem padLayout_eq (f : FormatSpec) (sg pfx body tail : Str) (N : Int)
    (hN : N = f.width - ((sg.length : Int) + pfx.length + body.length + tail.length))
    (hal : f.align = 60 ∨ f.align = 62 ∨ f.align = 61 ∨ f.align = 94) :
    List.replicate (padFields N f.align).1 f.fillChar ++ sg ++ pfx ++
      List.replicate (padFields N f.align).2.1 f.fillChar ++ body ++ tail ++
      List.replicate (padFields N f.align).2.2 f.fillChar = padLayout f sg pfx body tail := by
  unfold padLayout
  rw [← hN]
  unfold padFields
  by_cases hp : N > 0
  · rw [if_pos hp]
    rcases hal with h | h | h | h <;> simp [h]
  · rw [if_neg hp]
    have : N.toNat = 0 := by omega
    rcases hal with h | h | h | h <;> simp [h, this]

end PyLean.UnicodeObj
