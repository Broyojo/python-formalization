import PyLean.CoreLibs.CalStat.CalProps

/-! Properties of the `calendar` formatters, the locale machinery and `main`. -/

namespace PyLean.CoreLibs.CalStat

open PyLean PyLean.Datetime

/-! ## String lemmas -/

theorem center_length (s : Str) (w : Int) (hw : 0 ≤ w) :
    (center s w).length = max s.length w.toNat := by
  unfold center
  split
  · omega
  · rename_i h
    simp only [spaces, List.length_append, List.length_replicate]
    have : 0 ≤ (if (w - (s.length : Int)) % 2 = 1 ∧ w % 2 = 1 then (1 : Int) else 0) ∧
        (if (w - (s.length : Int)) % 2 = 1 ∧ w % 2 = 1 then (1 : Int) else 0) ≤ 1 := by
      split <;> omega
    by_cases hm : (w - (s.length : Int)) % 2 = 1 ∧ w % 2 = 1
    · rw [if_pos hm]; omega
    · rw [if_neg hm]; omega

theorem join_length (sep : Str) (parts : List Str) (n : Nat) (h : ∀ p ∈ parts, p.length = n) :
    (join sep parts).length = parts.length * n + (parts.length - 1) * sep.length := by
  unfold join
  induction parts with
  | nil => simp
  | cons a as ih =>
    cases as with
    | nil =>
      have := h a (by simp)
      simp [this]
    | cons b bs =>
      have ih' := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
      rw [List.intercalate_cons_cons]
      simp only [List.length_append, ih', h a (by simp), List.length_cons, Nat.add_sub_cancel,
        Nat.add_mul, Nat.one_mul]
      omega

theorem pyIndex_ok {α : Type} (xs : List α) (i : Int) (h0 : 0 ≤ i) (h1 : i < xs.length) :
    ∃ x ∈ xs, pyIndex xs i = .ok x := by
  have hlt : i.toNat < xs.length := by omega
  refine ⟨xs[i.toNat], List.getElem_mem hlt, ?_⟩
  unfold pyIndex
  simp only
  rw [if_neg (by omega), if_neg (by omega)]
  rw [List.getElem?_eq_getElem hlt]

/-- `lst[i]` for an out-of-range index, on either side. -/
theorem pyIndex_err {α : Type} (xs : List α) (i : Int)
    (h : i ≥ xs.length ∨ i < -(xs.length : Int)) :
    pyIndex xs i = .error (.indexError "list index out of range") := by
  unfold pyIndex
  simp only
  by_cases hn : i < 0
  · rw [if_pos hn, if_pos (by omega)]
  · rw [if_neg hn, if_pos (by omega)]

theorem mapM_exists {α β : Type} (f : α → Py β) (l : List α) (P : β → Prop)
    (h : ∀ x ∈ l, ∃ y, f x = .ok y ∧ P y) :
    ∃ r, l.mapM f = .ok r ∧ r.length = l.length ∧ ∀ y ∈ r, P y := by
  induction l with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | cons a as ih =>
    obtain ⟨y, hy, hP⟩ := h a (by simp)
    obtain ⟨r, hr, hl, hall⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨y :: r, ?_, by simp [hl], ?_⟩
    · simp only [List.mapM_cons, hy, hr]; rfl
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hP
      · exact hall z hz

theorem iterweekdays_range (c : Calendar) : ∀ i ∈ c.iterweekdays, 0 ≤ i ∧ i ≤ 6 := by
  intro i hi
  unfold Calendar.iterweekdays at hi
  simp only [List.mem_map] at hi
  obtain ⟨_, _, rfl⟩ := hi
  omega

theorem iterweekdays_length (c : Calendar) : c.iterweekdays.length = 7 := by
  rcases iterweekdays_fw c with h | h | h | h | h | h | h <;> rw [h.2] <;> rfl

/-- The weekday tables of a locale: seven names, as `strftime` gives. -/
def Names.WellFormed (N : Names) : Prop :=
  N.dayName.length = 7 ∧ N.dayAbbr.length = 7 ∧ N.monthName.length = 12

theorem cNames_wf : cNames.WellFormed := by
  unfold Names.WellFormed; decide

/-! ## Widths -/

theorem fmt2i_length (d : Int) (h0 : 0 < d) (h1 : d < 100) : (fmt2i d).length = 2 := by
  have : ∀ n : Fin 100, 0 < n.val → (Nat.toDigits 10 n.val).length + (2 - (Nat.toDigits 10 n.val).length) = 2 := by
    decide
  obtain ⟨n, rfl⟩ : ∃ n : Nat, d = n := ⟨d.toNat, by omega⟩
  have hn := this ⟨n, by omega⟩ (by simpa using h0)
  unfold fmt2i
  simp only [spaces, List.length_append, List.length_replicate]
  have hneg : ¬((n : Int) < 0) := by omega
  simp only [hneg, if_false, Int.natAbs_natCast, List.nil_append]
  simp only [Int.natAbs_natCast, if_false] at hn ⊢
  simp only [List.length_nil, Nat.zero_add] at *
  omega

theorem tFormatday_length (d wd w : Int) (hw : 2 ≤ w) (h0 : 0 ≤ d) (h1 : d < 100) :
    (tFormatday d wd w).length = w.toNat := by
  unfold tFormatday
  simp only
  rw [center_length _ _ (by omega)]
  split
  · simp
  · rw [fmt2i_length d (by omega) h1]; omega

/-- Text columns line up: a week of day numbers below 100 formatted with width `w >= 2` is
exactly `n*w + n-1` wide, the width `formatmonth` and `formatyear` rely on. `prweek` prints it. -/
def TextWeekWidth : Prop :=
  ∀ (week : List (Int × Int)) (w : Int), 2 ≤ w → (∀ p ∈ week, 0 ≤ p.1 ∧ p.1 < 100) →
    (tFormatweek week w).length = week.length * w.toNat + (week.length - 1) ∧
    tPrweek week w = tFormatweek week w

theorem textWeekWidth_proven : TextWeekWidth := by
  intro week w hw hd
  refine ⟨?_, rfl⟩
  unfold tFormatweek
  rw [join_length [' '] _ w.toNat]
  · simp
  · intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact tFormatday_length _ _ _ hw (hd q hq).1 (hd q hq).2

theorem tFormatweekday_ok (N : Names) (hN : N.WellFormed) (i w : Int) (h0 : 0 ≤ i) (h1 : i ≤ 6)
    (hw : 0 ≤ w) : ∃ s, tFormatweekday N i w = .ok s ∧ s.length = w.toNat ∧
      ∃ t, (t ∈ N.dayName ∨ t ∈ N.dayAbbr) ∧ s = center (sliceTo t w) w := by
  have hlen : (if w ≥ 9 then N.dayName else N.dayAbbr).length = 7 := by
    split
    · exact hN.1
    · exact hN.2.1
  obtain ⟨x, hx, hi⟩ := pyIndex_ok (if w ≥ 9 then N.dayName else N.dayAbbr) i h0 (by omega)
  refine ⟨center (sliceTo x w) w, ?_, ?_, x, ?_, rfl⟩
  · unfold tFormatweekday localizedGet
    simp only [bind, Except.bind, hi, pure, Except.pure]
  · rw [center_length _ _ hw]
    have : (sliceTo x w).length ≤ w.toNat := by
      unfold sliceTo
      simp only [List.length_take]
      rw [if_neg (by omega)]
      omega
    omega
  · by_cases h9 : w ≥ 9
    · rw [if_pos h9] at hx; exact Or.inl hx
    · rw [if_neg h9] at hx; exact Or.inr hx

/-- The week header has the same width as a week row: `7*w + 6`, for every first weekday
and every locale table of seven names; in particular `iterweekdays` never raises `IndexError`
through `day_name[...]`. -/
def TextHeaderWidth : Prop :=
  ∀ (N : Names) (c : Calendar) (w : Int), N.WellFormed → 0 ≤ w →
    ∃ s, tFormatweekheader N c w = .ok s ∧ s.length = 7 * w.toNat + 6

theorem tFormatweekheader_ok (N : Names) (hN : N.WellFormed) (c : Calendar) (w : Int) (hw : 0 ≤ w) :
    ∃ s, tFormatweekheader N c w = .ok s ∧ s.length = 7 * w.toNat + 6 ∧
      ∃ parts : List Str, s = join [' '] parts ∧
        ∀ p ∈ parts, ∃ t, (t ∈ N.dayName ∨ t ∈ N.dayAbbr) ∧ p = center (sliceTo t w) w := by
  obtain ⟨r, hr, hl, hall⟩ := mapM_exists (fun i => tFormatweekday N i w) c.iterweekdays
    (fun s => s.length = w.toNat ∧ ∃ t, (t ∈ N.dayName ∨ t ∈ N.dayAbbr) ∧ s = center (sliceTo t w) w)
    (fun i hi => by
      obtain ⟨h0, h1⟩ := iterweekdays_range c i hi
      obtain ⟨s, hs, h2, h3⟩ := tFormatweekday_ok N hN i w h0 h1 hw
      exact ⟨s, hs, h2, h3⟩)
  refine ⟨join [' '] r, ?_, ?_, r, rfl, fun p hp => (hall p hp).2⟩
  · unfold tFormatweekheader
    simp only [bind, Except.bind, hr, pure, Except.pure]
  · rw [join_length [' '] r w.toNat (fun p hp => (hall p hp).1), hl, iterweekdays_length]
    simp

theorem textHeaderWidth_proven : TextHeaderWidth := by
  intro N c w hN hw
  obtain ⟨s, h1, h2, -⟩ := tFormatweekheader_ok N hN c w hw
  exact ⟨s, h1, h2⟩

/-- `formatstring` centres each column in `colwidth` and joins them with `spacing` blanks, so
`n` columns no wider than `colwidth` give `n*colwidth + (n-1)*spacing` characters;
`format` prints that and a newline. -/
def FormatstringWidth : Prop :=
  ∀ (cols : List Str) (colwidth spacing : Int), 0 ≤ colwidth → 0 ≤ spacing →
    (∀ s ∈ cols, (s.length : Int) ≤ colwidth) →
    (formatstring cols colwidth spacing).length =
      cols.length * colwidth.toNat + (cols.length - 1) * spacing.toNat ∧
    formatPrint cols colwidth spacing = formatstring cols colwidth spacing ++ ['\n']

theorem strTimes_space_length (n : Int) : (strTimes [' '] n).length = n.toNat := by
  unfold strTimes
  generalize n.toNat = k
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.flatten_cons, List.length_append, ih]; simp; omega

theorem formatstringWidth_proven : FormatstringWidth := by
  intro cols cw sp hc hs hall
  refine ⟨?_, rfl⟩
  unfold formatstring
  rw [join_length _ _ cw.toNat, strTimes_space_length]
  · simp
  · intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨s, hs', rfl⟩ := hp
    rw [center_length _ _ hc]
    have := hall s hs'
    omega

/-! ## Line structure -/

def NoNL (s : Str) : Prop := '\n' ∉ s

theorem noNL_append {a b : Str} (ha : NoNL a) (hb : NoNL b) : NoNL (a ++ b) := by
  unfold NoNL at *
  simp [ha, hb]

theorem noNL_spaces (n : Nat) : NoNL (spaces n) := by
  unfold NoNL spaces
  simp [List.mem_replicate]

theorem noNL_center {s : Str} (h : NoNL s) (w : Int) : NoNL (center s w) := by
  unfold center
  split
  · exact h
  · exact noNL_append (noNL_append (noNL_spaces _) h) (noNL_spaces _)

theorem noNL_rstrip {s : Str} (h : NoNL s) : NoNL (rstrip s) := by
  unfold NoNL rstrip at *
  intro hm
  rw [List.mem_reverse] at hm
  exact h (List.mem_reverse.mp ((List.dropWhile_sublist isSpaceChar).subset hm))

theorem noNL_join {sep : Str} (hs : NoNL sep) (parts : List Str) (h : ∀ p ∈ parts, NoNL p) :
    NoNL (join sep parts) := by
  unfold join
  induction parts with
  | nil => unfold NoNL; simp
  | cons a as ih =>
    have ih' := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    cases as with
    | nil => simpa using h a (by simp)
    | cons b bs =>
      rw [List.intercalate_cons_cons]
      exact noNL_append (noNL_append (h a (by simp)) hs) ih'

theorem noNL_digits (n : Nat) : NoNL (Nat.toDigits 10 n) := by
  unfold NoNL
  intro hm
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hm
  revert this
  decide

theorem noNL_fmt2i (d : Int) : NoNL (fmt2i d) := by
  unfold fmt2i
  refine noNL_append (noNL_spaces _) (noNL_append ?_ (noNL_digits _))
  split
  · unfold NoNL; decide
  · unfold NoNL; simp

theorem noNL_tFormatday (d wd w : Int) : NoNL (tFormatday d wd w) := by
  unfold tFormatday
  apply noNL_center
  split
  · unfold NoNL; simp
  · exact noNL_fmt2i d

theorem noNL_tFormatweek (week : List (Int × Int)) (w : Int) : NoNL (tFormatweek week w) := by
  unfold tFormatweek
  apply noNL_join
  · unfold NoNL; decide
  · intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, _, rfl⟩ := hp
    exact noNL_tFormatday _ _ _

theorem count_nl (l : Int) : (nl l).count '\n' = l.toNat := by
  unfold nl strTimes
  generalize l.toNat = k
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, List.flatten_cons, List.count_append, ih]

theorem count_noNL {s : Str} (h : NoNL s) : s.count '\n' = 0 := List.count_eq_zero.mpr h

theorem count_flatten_lines (lines : List Str) (l : Int) (h : ∀ s ∈ lines, NoNL s) :
    ((lines.map (· ++ nl l)).flatten).count '\n' = lines.length * l.toNat := by
  induction lines with
  | nil => simp
  | cons a as ih =>
    have ih' := ih (fun s hs => h s (List.mem_cons_of_mem _ hs))
    simp only [List.map_cons, List.flatten_cons, List.count_append, ih', count_nl,
      count_noNL (h a (by simp)), List.length_cons]
    rw [Nat.add_mul]
    omega

/-- A year (or any int) below the `int`/`str` conversion limit. -/
def ReprOk (y : Int) : Prop := Fractions.numDigits y.natAbs ≤ Fractions.maxStrDigits

theorem reprInt_ok (y : Int) (h : ReprOk y) : ∃ s, reprInt y = .ok s ∧ NoNL s := by
  unfold ReprOk at h
  refine ⟨(if y < 0 then ['-'] else []) ++ Nat.toDigits 10 y.natAbs, ?_, ?_⟩
  · unfold reprInt Fractions.strInt
    rw [if_neg (by omega)]
  · refine noNL_append ?_ (noNL_digits _)
    split
    · unfold NoNL; decide
    · unfold NoNL; simp

theorem cNames_noNL : (∀ t ∈ cNames.dayName, NoNL t) ∧ (∀ t ∈ cNames.dayAbbr, NoNL t) ∧
    (∀ t ∈ cNames.monthName, NoNL t) := by
  unfold NoNL; decide

theorem noNL_sliceTo {s : Str} (h : NoNL s) (w : Int) : NoNL (sliceTo s w) := by
  unfold NoNL sliceTo at *
  intro hm
  exact h (List.mem_of_mem_take hm)

theorem tFormatmonthname_ok (y m w : Int) (hm : 1 ≤ m ∧ m ≤ 12) (hy : ReprOk y) (withyear : Bool) :
    ∃ s, tFormatmonthname cNames y m w withyear = .ok s ∧ NoNL s := by
  obtain ⟨yr, hyr, hn⟩ := reprInt_ok y hy
  have hlen : ((localizedMonthList cNames.monthName).length : Int) = 13 := by decide
  obtain ⟨x, hx, hi⟩ := pyIndex_ok (localizedMonthList cNames.monthName) m (by omega) (by omega)
  have hxn : NoNL x := by
    simp only [localizedMonthList, List.mem_cons] at hx
    rcases hx with rfl | hx
    · unfold NoNL; simp
    · exact cNames_noNL.2.2 x hx
  unfold tFormatmonthname localizedGet
  rw [validateMonth_ok m hm]
  simp only [bind, Except.bind, hi]
  cases withyear with
  | true =>
    simp only [if_true, hyr, pure, Except.pure]
    exact ⟨_, rfl, noNL_center (noNL_append (noNL_append hxn (by unfold NoNL; decide)) hn) _⟩
  | false =>
    simp only [Bool.false_eq_true, if_false, pure, Except.pure]
    exact ⟨_, rfl, noNL_center hxn _⟩

theorem tFormatweekheader_noNL (c : Calendar) (w : Int) (hw : 0 ≤ w) :
    ∃ s, tFormatweekheader cNames c w = .ok s ∧ NoNL s := by
  obtain ⟨s, h1, -, parts, rfl, hp⟩ := tFormatweekheader_ok cNames cNames_wf c w hw
  refine ⟨_, h1, noNL_join (by unfold NoNL; decide) _ ?_⟩
  intro p hmem
  obtain ⟨t, ht, rfl⟩ := hp p hmem
  apply noNL_center
  apply noNL_sliceTo
  rcases ht with ht | ht
  · exact cNames_noNL.1 t ht
  · exact cNames_noNL.2.1 t ht

/-- `formatmonth` is a title line, a header line and one line per week, each followed by `l`
newlines (`l` clamped to at least 1), so the output has `(weeks + 2) * l` newlines
and the printed `prmonth` is the same text. -/
def FormatmonthLines : Prop :=
  ∀ (c : Calendar) (y m w l : Int), (1 ≤ m ∧ m ≤ 12) → ReprOk y →
    ∃ s wks, tFormatmonth cNames c y m w l = .ok s ∧ c.monthdays2calendar y m = .ok wks ∧
      4 ≤ wks.length ∧ wks.length ≤ 6 ∧
      s.count '\n' = (wks.length + 2) * (max 1 l).toNat ∧
      tPrmonth cNames c y m w l = .ok s

theorem formatmonthLines_proven : FormatmonthLines := by
  intro c y m w l hm hy
  obtain ⟨t, ht, htn⟩ := tFormatmonthname_ok y m (7 * (max 2 w + 1) - 1) hm hy true
  obtain ⟨h, hh, hhn⟩ := tFormatweekheader_noNL c (max 2 w) (by omega)
  obtain ⟨ll, hl1, hl2, hl3, hl4, hl5⟩ := monthdays2calendar_ok c y m hm
  obtain ⟨a, b, -, -⟩ := chunk7 ll hl3 hl4 hl5
  have hres : tFormatmonth cNames c y m w l =
      .ok (rstrip t ++ nl (max 1 l) ++ rstrip h ++ nl (max 1 l) ++
        ((chunks 7 ll).map (fun week => rstrip (tFormatweek week (max 2 w)) ++ nl (max 1 l))).flatten) := by
    unfold tFormatmonth
    simp only [bind, Except.bind, ht, hh, hl2, pure, Except.pure, List.append_assoc]
  refine ⟨_, chunks 7 ll, hres, hl2, a, b, ?_, hres⟩
  have hc := count_flatten_lines ((chunks 7 ll).map (fun week => rstrip (tFormatweek week (max 2 w))))
    (max 1 l) (fun s hs => by
      simp only [List.mem_map] at hs
      obtain ⟨wk', _, rfl⟩ := hs
      exact noNL_rstrip (noNL_tFormatweek _ _))
  simp only [List.map_map, List.length_map] at hc
  simp only [List.count_append, count_nl, count_noNL (noNL_rstrip htn), count_noNL (noNL_rstrip hhn)]
  have e : (fun s => s ++ nl (max 1 l)) ∘ (fun week => rstrip (tFormatweek week (max 2 w))) =
      (fun week => rstrip (tFormatweek week (max 2 w)) ++ nl (max 1 l)) := rfl
  rw [e] at hc
  rw [hc, Nat.add_mul]
  omega

/-! ## `_CLIDemoCalendar` -/

/-- The empty colour set of `NO_COLOR` (`_colorize.get_colors` with colour off). -/
def noColors : Ansi := ⟨[], [], []⟩

theorem dFormatweek_none (A : Ansi) (week : List (Int × Int)) (w : Int) :
    dFormatweek A week w none = tFormatweek week w := by
  simp [dFormatweek, tFormatweek]

theorem dFormatweek_noColors (week : List (Int × Int)) (w : Int) (hd : Option Int) :
    dFormatweek noColors week w hd = tFormatweek week w := by
  simp only [dFormatweek, tFormatweek, noColors]
  congr 1
  apply List.map_congr_left
  intro p _
  by_cases h : some p.1 = hd <;> simp [h]

/-- The demo subclass is `TextCalendar` plus colour and nothing else: without a highlighted
day in view, or with colours off, `formatweek`, `formatmonth` and `formatyear` of
`_CLIDemoCalendar` return exactly what `TextCalendar` returns. -/
def DemoIsText : Prop :=
  (∀ (A : Ansi) (N : Names) (c : Calendar) (y m w l cc mm : Int),
    dFormatmonth A N c none y m w l = tFormatmonth N c y m w l ∧
    dFormatyear A N c none y w l cc mm = tFormatyear N c y w l cc mm) ∧
  (∀ (A : Ansi) (N : Names) (c : Calendar) (y m w l : Int) (d : Date), (d.1 ≠ y ∨ d.2.1 ≠ m) →
    dFormatmonth A N c (some d) y m w l = tFormatmonth N c y m w l) ∧
  (∀ (N : Names) (c : Calendar) (hl : Highlight) (y m w l cc mm : Int),
    dFormatmonth noColors N c hl y m w l = tFormatmonth N c y m w l ∧
    dFormatyear noColors N c hl y w l cc mm = tFormatyear N c y w l cc mm)

theorem dFormatmonth_of (A : Ansi) (N : Names) (c : Calendar) (hl : Highlight) (y m w l : Int)
    (h : ∀ wk ww, dFormatweek A wk ww (monthHighlight hl y m) = tFormatweek wk ww) :
    dFormatmonth A N c hl y m w l = tFormatmonth N c y m w l := by
  unfold dFormatmonth tFormatmonth
  simp only [h]

theorem demoIsText_proven : DemoIsText := by
  refine ⟨?_, ?_, ?_⟩
  · intro A N c y m w l cc mm
    refine ⟨dFormatmonth_of A N c none y m w l (fun wk ww => dFormatweek_none A wk ww), ?_⟩
    unfold dFormatyear tFormatyear
    simp only [dYearDay, dFormatweek_none]
  · rintro A N c y m w l ⟨a, b, d⟩ h
    apply dFormatmonth_of
    intro wk ww
    have : ¬(a = y ∧ b = m) := by
      simp only at h
      omega
    simp only [monthHighlight, this, if_false]
    exact dFormatweek_none A wk ww
  · intro N c hl y m w l cc mm
    refine ⟨dFormatmonth_of noColors N c hl y m w l (fun wk ww => dFormatweek_noColors wk ww _), ?_⟩
    unfold dFormatyear tFormatyear
    simp only [dFormatweek_noColors]

/-- In the year view exactly the column of the highlighted month is highlighted: for a
row of distinct months, `formatweek` receives the day only in the column holding that month. -/
def DemoYearColumn : Prop :=
  ∀ (y mo d : Int) (months : List Int) (k : Nat), months.Nodup →
    (dYearDay (some (y, mo, d)) y months k = some d ↔ months[k]? = some mo)

theorem demoYearColumn_proven : DemoYearColumn := by
  intro y mo d months k hn
  simp only [dYearDay, true_and]
  constructor
  · intro h
    split at h
    · rename_i hm
      split at h
      · rename_i he
        subst he
        have hlt := List.idxOf_lt_length_iff.mpr hm
        rw [List.getElem?_eq_getElem hlt]
        simp [List.getElem_idxOf]
      · cases h
    · cases h
  · intro h
    have hm : mo ∈ months := List.mem_of_getElem? h
    rw [if_pos hm]
    have : months.idxOf mo = k := by
      obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp h
      subst he
      exact (List.Nodup.idxOf_getElem hn k hlt)
    rw [if_pos this]

/-! ## Month rows of the year formatters -/

/-- `HTMLCalendar.formatyear`: for every width at least 1, the rows of month numbers cover
January to December exactly once, each row having at most `width` months. -/
def HtmlYearMonths : Prop :=
  ∀ width : Int, 1 ≤ width →
    (htmlMonthRows width).flatten = months12 ∧
    ∀ r ∈ htmlMonthRows width, (r.length : Int) ≤ width

theorem htmlYearMonths_proven : HtmlYearMonths := by
  intro width hw
  by_cases hbig : 12 ≤ width
  · have : htmlMonthRows width = [months12] := by
      unfold htmlMonthRows rangeStep
      have e : (13 - 1 - 1 : Int) / width = 0 := by
        apply Int.ediv_eq_zero_of_lt <;> omega
      have e2 : ((13 - 1 - 1) / width + 1 : Int).toNat = 1 := by
        rw [e]; rfl
      simp only [show (1 : Int) < 13 by decide, if_true, e2]
      have e3 : min (1 + width) 13 = 13 := by omega
      simp [e3]
      rfl
    rw [this]
    refine ⟨by simp, ?_⟩
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    have : (months12.length : Int) = 12 := rfl
    omega
  · rcases (by omega : width = 1 ∨ width = 2 ∨ width = 3 ∨ width = 4 ∨ width = 5 ∨ width = 6 ∨
      width = 7 ∨ width = 8 ∨ width = 9 ∨ width = 10 ∨ width = 11) with
      h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- `TextCalendar.formatyear`: the numbers of the month row `i` computed at calendar.py:422 are
the months actually laid out in row `i` by `yeardays2calendar`, for all `m >= 1`.
A formatted name can never disagree with the column below it. -/
def TextYearMonths : Prop :=
  ∀ m : Int, 1 ≤ m → ∀ (i : Nat) (r : List Int), (chunks m.toNat months12)[i]? = some r →
    textMonthRow m i = r

theorem textYearMonths_proven : TextYearMonths := by
  intro m hm i r hi
  by_cases hbig : 12 ≤ m
  · have hch : chunks m.toNat months12 = [months12] := by
      have hk : 12 ≤ m.toNat := by omega
      unfold chunks
      show chunksGo m.toNat 12 months12 = [months12]
      unfold months12
      simp only [chunksGo]
      rw [List.take_of_length_le (by simpa using hk), List.drop_of_length_le (by simpa using hk)]
      cases (11 : Nat) <;> rfl
    rw [hch] at hi
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      unfold textMonthRow
      have e : min (m * (((0 : Nat) : Int) + 1) + 1) 13 = 13 := by simp; omega
      rw [e]
      simp
      rfl
    | succ i => simp at hi
  · have hc : ((chunks m.toNat months12).zipIdx.all
        (fun p => textMonthRow m (p.2 : Int) == p.1)) = true := by
      rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨
        m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11) with
        h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
    have := List.all_eq_true.mp hc (r, i) (List.mem_zipIdx_iff_getElem?.mpr (by simpa using hi))
    simpa using this

/-- A zero month count reaches the `range()` step of `yeardays2calendar` and raises its
`ValueError`; a negative one yields only the title. (`HTMLCalendar.formatyear` clamps its width
to at least 1 instead: for `width <= 0` it is the same as `width = 1`.) -/
def FormatyearMonthCount : Prop :=
  (∀ (c : Calendar) (y w l cc : Int), ReprOk y →
    tFormatyear cNames c y w l cc 0 = .error (.valueError "range() arg 3 must not be zero")) ∧
  (∀ (N : Names) (c : Calendar) (y width : Int), width ≤ 0 →
    hFormatyear N c y width = hFormatyear N c y 1)

theorem yeardays2_ok (c : Calendar) (y : Int) :
    ∃ ms, months12.mapM (c.monthdays2calendar y) = .ok ms := by
  obtain ⟨r, hr, -, -⟩ := mapM_exists (c.monthdays2calendar y) months12 (fun _ => True)
    (fun m hm => by
      obtain ⟨l, _, h2, _⟩ := monthdays2calendar_ok c y m (mem_months12 hm)
      exact ⟨_, h2, trivial⟩)
  exact ⟨r, hr⟩

theorem formatyearMonthCount_proven : FormatyearMonthCount := by
  refine ⟨?_, ?_⟩
  · intro c y w l cc hy
    obtain ⟨yr, hyr, -⟩ := reprInt_ok y hy
    obtain ⟨h, hh, -⟩ := tFormatweekheader_noNL c (max 2 w) (by omega)
    obtain ⟨ms, hms⟩ := yeardays2_ok c y
    unfold tFormatyear tFormatyearWith Calendar.yeardays2calendar
    simp only [bind, Except.bind, hyr, hh, hms]
    rfl
  · intro N c y width hw
    unfold hFormatyear
    have : max width 1 = max 1 1 := by omega
    rw [this]

/-! ## HTML -/

theorem hFormatday_noNL (d wd : Int) (hw : 0 ≤ wd ∧ wd ≤ 6) (hd : ReprOk d) :
    ∃ s, hFormatday d wd = .ok s ∧ NoNL s := by
  obtain ⟨cls, hc, hi⟩ := pyIndex_ok cssclasses wd hw.1 (by have : (cssclasses.length : Int) = 7 := by decide
                                                            omega)
  obtain ⟨r, hr, hn⟩ := reprInt_ok d hd
  have hall : ∀ t ∈ cssclasses, NoNL t := by unfold NoNL; decide
  have hcn : NoNL cls := hall cls hc
  unfold hFormatday
  by_cases h0 : d = 0
  · simp only [h0, if_true]
    exact ⟨_, rfl, by unfold NoNL lit; decide⟩
  · simp only [h0, if_false, bind, Except.bind, hi, hr, pure, Except.pure]
    refine ⟨_, rfl, ?_⟩
    have l1 : NoNL (lit "<td class=\"") := by unfold NoNL lit; decide
    have l2 : NoNL (lit "\">") := by unfold NoNL lit; decide
    have l3 : NoNL (lit "</td>") := by unfold NoNL lit; decide
    exact noNL_append (noNL_append (noNL_append (noNL_append l1 hcn) l2) hn) l3

end PyLean.CoreLibs.CalStat
