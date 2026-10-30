import PyLean.StrSearch.Basic

/-!
Padding (`center`, `ljust`, `rjust`, `zfill`) and `expandtabs`: `str`
(unicodeobject.c, with overflow checks in `pad`) against `bytes`
(transmogrify.h, without), and against their docstrings.
-/

set_option linter.deprecated false

namespace PyLean.StrSearch

open PyLean

theorem argSsize_ok {w : Int} (h1 : ssizeMin ≤ w) (h2 : w ≤ ssizeMax) : argSsize w = .ok w := by
  simp [argSsize]; omega

theorem argSsize_err {w : Int} (h : ¬ (ssizeMin ≤ w ∧ w ≤ ssizeMax)) :
    argSsize w = .error (.overflowError "Python int too large to convert to C ssize_t") := by
  simp [argSsize]; omega

theorem and_one_le (a b : Nat) : (a &&& b &&& 1) ≤ 1 := Nat.and_le_right

theorem and_one_even {m w : Nat} (h : m % 2 = 0) : (m &&& w &&& 1) = 0 := by
  rw [Nat.and_one_is_mod]
  have := Nat.testBit_and m w 0
  simp only [Nat.testBit_zero] at this
  have hm : decide (m % 2 = 1) = false := by simp; omega
  rw [hm, Bool.false_and] at this
  have := Nat.mod_two_eq_zero_or_one (m &&& w)
  simp at *
  omega

theorem centerLeft_bounds {marg width : Int} (h : 1 ≤ marg) :
    0 ≤ centerLeft marg width ∧ centerLeft marg width ≤ marg ∧
    marg - centerLeft marg width ≤ centerLeft marg width + 1 ∧
    centerLeft marg width ≤ marg - centerLeft marg width + 1 := by
  unfold centerLeft
  have h1 := and_one_le marg.toNat width.toNat
  have h2 : marg.toNat % 2 = 0 → (marg.toNat &&& width.toNat &&& 1) = 0 := and_one_even
  generalize (marg.toNat &&& width.toNat &&& 1 : Nat) = c at *
  omega

/-- `pad` of `str` never takes its overflow branch when the result fits:
it then equals the `bytes` `pad`. -/
theorem strPad_ok {s : Seq} {l r : Int} {fill : Nat} (hl : 0 ≤ l) (hr : 0 ≤ r)
    (h : l + s.length + r ≤ ssizeMax) : strPad s l r fill = .ok (bytesPad s l r fill) := by
  unfold strPad bytesPad
  simp only [show ¬ l < 0 by omega, show ¬ r < 0 by omega, ↓reduceIte]
  split
  · rfl
  · rw [if_neg (by omega)]

/-- `str` and `bytes` padding agree for every width and fill character:
`center`, `ljust`, `rjust` and `zfill`. In particular the overflow check of
the `str` `pad` (unicodeobject.c:10510-10514) can never fire, so a width that
is a valid `Py_ssize_t` never raises `OverflowError` ("padded string is too
long"). Precondition: `len(s) ≤ sys.maxsize` (type invariant). -/
def PadStrBytes : Prop :=
  ∀ (s : Seq) (width : Int) (fill : Nat), (s.length : Int) ≤ ssizeMax →
    strCenter s width fill = bytesCenter s width fill ∧
    strLjust s width fill = bytesLjust s width fill ∧
    strRjust s width fill = bytesRjust s width fill ∧
    strZfill s width = bytesZfill s width

theorem padStrBytes_proven : PadStrBytes := by
  intro s width fill hs
  by_cases hw : ssizeMin ≤ width ∧ width ≤ ssizeMax
  · simp only [strCenter, bytesCenter, strLjust, bytesLjust, strRjust, bytesRjust, strZfill,
      bytesZfill, argSsize_ok hw.1 hw.2, bind, Except.bind, pure, Except.pure]
    by_cases hle : (s.length : Int) ≥ width
    · simp [hle]
    · simp only [hle, ↓reduceIte]
      have hb := centerLeft_bounds (marg := width - s.length) (width := width) (by omega)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [strPad_ok hb.1 (by omega) (by omega)]
      · rw [strPad_ok (by omega) (by omega) (by omega)]
      · rw [strPad_ok (by omega) (by omega) (by omega)]
      · rw [strPad_ok (by omega) (by omega) (by omega)]
  · simp [strCenter, bytesCenter, strLjust, bytesLjust, strRjust, bytesRjust, strZfill,
      bytesZfill, argSsize_err hw, bind, Except.bind]

/-- `center` docstring, "Return a centered string of length width ... The
original string is returned if width is less than or equal to len(s)": for
a valid `Py_ssize_t` width the result is `s` when `width <= len(s)`, and
otherwise `s` with `l` fill characters before and `r` after, `l + len(s) + r
== width` and `|l - r| <= 1`. -/
def CenterBalanced : Prop :=
  ∀ (s : Seq) (width : Int) (fill : Nat), (s.length : Int) ≤ ssizeMax →
    ssizeMin ≤ width → width ≤ ssizeMax →
    (width ≤ s.length → strCenter s width fill = .ok s) ∧
    ((s.length : Int) < width → ∃ l r : Nat,
      strCenter s width fill = .ok (List.replicate l fill ++ s ++ List.replicate r fill) ∧
      (l : Int) + s.length + r = width ∧ l ≤ r + 1 ∧ r ≤ l + 1)

theorem centerBalanced_proven : CenterBalanced := by
  intro s width fill hs h1 h2
  simp only [strCenter, argSsize_ok h1 h2, bind, Except.bind, pure, Except.pure]
  constructor
  · intro h; simp [show (s.length : Int) ≥ width by omega]
  · intro h
    simp only [show ¬ (s.length : Int) ≥ width by omega, ↓reduceIte]
    have hb := centerLeft_bounds (marg := width - s.length) (width := width) (by omega)
    rw [strPad_ok hb.1 (by omega) (by omega)]
    refine ⟨(centerLeft (width - s.length) width).toNat,
      (width - s.length - centerLeft (width - s.length) width).toNat, ?_, by omega, by omega, by omega⟩
    simp only [bytesPad, show ¬ centerLeft (width - s.length) width < 0 by omega,
      show ¬ width - s.length - centerLeft (width - s.length) width < 0 by omega, ↓reduceIte]
    split
    · next hz => omega
    · rfl

theorem zfillSign_eq (s : Seq) (f : Nat) (hf : 1 ≤ f) :
    zfillSign (List.replicate f 48 ++ s) f =
      match s with
      | c :: rest => if c = 43 ∨ c = 45 then c :: List.replicate f 48 ++ rest
                     else List.replicate f 48 ++ s
      | [] => List.replicate f 48 := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  unfold zfillSign
  cases s with
  | nil => simp
  | cons c rest =>
    have hget : (List.replicate (g + 1) 48 ++ c :: rest).getD (g + 1) 0 = c := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
    simp only [hget]
    split
    · rw [List.replicate_succ, List.cons_append, List.set_cons_zero, List.set_cons_succ,
        List.set_append_right _ _ (by simp), List.length_replicate, Nat.sub_self, List.set_cons_zero]
      have : ∀ g : Nat, List.replicate g 48 ++ 48 :: rest = 48 :: (List.replicate g 48 ++ rest) := by
        intro g
        induction g with
        | zero => rfl
        | succ g ih => simp [List.replicate_succ, ih]
      rw [this]; rfl
    · rfl

/-- `zfill` docstring and stdtypes.rst:2892-2898: "left filled with ASCII '0'
digits to make a string of length width. A leading sign prefix ('+'/'-') is
handled by inserting the padding after the sign character rather than before.
The original string is returned if width is less than or equal to len(s)."
For every `str` and valid `Py_ssize_t` width. -/
def ZfillSpec : Prop :=
  ∀ (s : Seq) (width : Int), (s.length : Int) ≤ ssizeMax → ssizeMin ≤ width → width ≤ ssizeMax →
    strZfill s width =
      .ok (if width ≤ s.length then s
           else match s with
             | c :: rest => if c = 43 ∨ c = 45 then c :: List.replicate (width - s.length).toNat 48 ++ rest
                            else List.replicate (width - s.length).toNat 48 ++ s
             | [] => List.replicate width.toNat 48)

theorem zfillSpec_proven : ZfillSpec := by
  intro s width hs h1 h2
  simp only [strZfill, argSsize_ok h1 h2, bind, Except.bind, pure, Except.pure]
  by_cases hle : width ≤ s.length
  · simp [show (s.length : Int) ≥ width by omega, hle]
  · simp only [show ¬ (s.length : Int) ≥ width by omega, hle, ↓reduceIte]
    rw [strPad_ok (by omega) (by omega) (by omega)]
    have hb : bytesPad s (width - s.length) 0 48 = List.replicate (width - s.length).toNat 48 ++ s := by
      simp only [bytesPad]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp
    simp only [hb]
    rw [zfillSign_eq s _ (by omega)]
    cases s with
    | nil => simp
    | cons c rest => rfl

/-! ## expandtabs -/

theorem incr_bounds {t col : Int} (ht : 0 < t) : 1 ≤ t - col % t ∧ t - col % t ≤ t := by
  have h1 := Int.emod_nonneg col (by omega : t ≠ 0)
  have h2 := Int.emod_lt_of_pos col ht
  omega

/-- First pass of `str.expandtabs`: it overflows exactly when the output would
be longer than `PY_SSIZE_T_MAX`. -/
theorem strExpandSize_eq (t : Int) :
    ∀ (s : Seq) (j col : Int) (found : Bool), 0 ≤ j → j ≤ ssizeMax →
      strExpandSize t s j col found =
        if j + (expandFill t s col).length > ssizeMax then none
        else some (j + (expandFill t s col).length, found || s.any (· == 9)) := by
  intro s
  induction s with
  | nil => intro j col found _ _; simp [strExpandSize, expandFill]; omega
  | cons ch rest ih =>
    intro j col found hj hjM
    by_cases h9 : ch = 9
    · subst h9
      by_cases ht : 0 < t
      · have hb := incr_bounds (col := col) ht
        simp only [strExpandSize, expandFill, ↓reduceIte, ht, List.length_append, List.length_replicate,
          List.any_cons, beq_self_eq_true, Bool.true_or, Bool.or_true]
        by_cases hov : j > ssizeMax - (t - col % t)
        · rw [if_pos hov, if_pos (by omega)]
        · rw [if_neg hov, ih _ _ _ (by omega) (by omega)]
          simp only [Bool.true_or]
          split <;> split <;> first | rfl | omega | (congr 2; omega)
      · simp only [strExpandSize, expandFill, ↓reduceIte, ht, List.any_cons, beq_self_eq_true,
          Bool.true_or, Bool.or_true]
        rw [ih _ _ _ hj hjM]
        simp
    · have hne : (ch == 9) = false := by simpa using h9
      simp only [strExpandSize, expandFill, h9, ↓reduceIte, List.length_cons, List.any_cons, hne,
        Bool.false_or]
      generalize (if ch = 10 ∨ ch = 13 then (0 : Int) else col + 1) = col'
      by_cases hov : j > ssizeMax - 1
      · rw [if_pos hov, if_pos (by omega)]
      · rw [if_neg hov, ih _ _ _ (by omega) (by omega)]
        split <;> split <;> first | rfl | omega | (congr 2; omega)

/-- First pass of `bytes.expandtabs`: the same condition, although it only
checks the current column inside a line and the line total at line ends. -/
theorem bytesExpandSize_eq (t : Int) :
    ∀ (s : Seq) (i col : Int), 0 ≤ i → 0 ≤ col → col ≤ ssizeMax →
      bytesExpandSize t s i col =
        if i + col + (expandFill t s col).length > ssizeMax then none
        else some (i + col + (expandFill t s col).length) := by
  intro s
  induction s with
  | nil => intro i col _ _ _; simp [bytesExpandSize, expandFill]; split <;> split <;> first | rfl | omega
  | cons ch rest ih =>
    intro i col hi hc hcM
    by_cases h9 : ch = 9
    · subst h9
      by_cases ht : 0 < t
      · have hb := incr_bounds (col := col) ht
        simp only [bytesExpandSize, expandFill, ↓reduceIte, ht, List.length_append, List.length_replicate]
        by_cases hov : col > ssizeMax - (t - col % t)
        · rw [if_pos hov, if_pos (by omega)]
        · rw [if_neg hov, ih _ _ hi (by omega) (by omega)]
          split <;> split <;> first | rfl | omega | (congr 1; omega)
      · simp only [bytesExpandSize, expandFill, ↓reduceIte, ht]
        exact ih _ _ hi hc hcM
    · simp only [bytesExpandSize, expandFill, h9, ↓reduceIte, List.length_cons]
      by_cases hov : col > ssizeMax - 1
      · rw [if_pos hov, if_pos (by omega)]
      · rw [if_neg hov]
        by_cases hnl : ch = 10 ∨ ch = 13
        · rw [if_pos hnl, if_pos hnl]
          by_cases hov2 : i > ssizeMax - (col + 1)
          · rw [if_pos hov2, if_pos (by omega)]
          · rw [if_neg hov2, ih _ _ (by omega) (by omega) (by omega)]
            split <;> split <;> first | rfl | omega | (congr 1; omega)
        · rw [if_neg hnl, if_neg hnl, ih _ _ hi (by omega) (by omega)]
          split <;> split <;> first | rfl | omega | (congr 1; omega)

theorem expandFill_notab (t : Int) : ∀ (s : Seq) (col : Int), s.any (· == 9) = false →
    expandFill t s col = s := by
  intro s
  induction s with
  | nil => intro _ _; rfl
  | cons ch rest ih =>
    intro col h
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    have h9 : ch ≠ 9 := by simpa using h.1
    simp only [expandFill, h9, ↓reduceIte]
    rw [ih _ h.2]

/-- `str.expandtabs` (unicodeobject.c:11882-11948) and `bytes.expandtabs`
(transmogrify.h:36-98) compute their sizes with different overflow checks
(`str` bounds the running total; `bytes` bounds the column and adds whole
lines). Both return the same expansion when it has at most `PY_SSIZE_T_MAX`
characters and both raise `OverflowError` otherwise; there is no silent
wraparound. For every string and every C `int` tabsize. -/
def ExpandtabsStrBytes : Prop :=
  ∀ (s : Seq) (tabsize : Int), -(2 ^ 31) ≤ tabsize → tabsize ≤ 2 ^ 31 - 1 →
    ((expandFill tabsize s 0).length ≤ ssizeMax →
      strExpandtabs s tabsize = .ok (expandFill tabsize s 0) ∧
      bytesExpandtabs s tabsize = .ok (expandFill tabsize s 0)) ∧
    ((expandFill tabsize s 0).length > ssizeMax →
      strExpandtabs s tabsize = .error (.overflowError "new string is too long") ∧
      bytesExpandtabs s tabsize = .error (.overflowError "result too long"))

theorem expandtabsStrBytes_proven : ExpandtabsStrBytes := by
  intro s t h1 h2
  have harg : argCInt t = .ok t := by simp [argCInt]; omega
  have hM : (0 : Int) ≤ ssizeMax := by unfold ssizeMax; omega
  have hs := strExpandSize_eq t s 0 0 false (by omega) hM
  have hb := bytesExpandSize_eq t s 0 0 (by omega) (by omega) hM
  simp only [Int.zero_add, Int.add_zero, Bool.false_or] at hs hb
  simp only [strExpandtabs, bytesExpandtabs, harg, bind, Except.bind, pure, Except.pure, hs, hb]
  constructor
  · intro hle
    rw [if_neg (by omega), if_neg (by omega)]
    cases hany : s.any (· == 9)
    · simp [expandFill_notab t s 0 hany]
    · simp
  · intro hgt
    rw [if_pos (by omega), if_pos (by omega)]
    exact ⟨rfl, rfl⟩

end PyLean.StrSearch
