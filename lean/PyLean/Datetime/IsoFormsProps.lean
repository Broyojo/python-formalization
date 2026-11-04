import PyLean.Datetime.IsoRoundtrip

/-!
`_parse_isoformat_date` and `_find_isoformat_datetime_separator` on every form they accept
and every refusal they make, over symbolic ASCII digits.
-/

namespace PyLean.Datetime

open PyLean

theorem dc_ascii (k : Nat) (hk : k < 10) : (dc k).toNat < 128 := by
  rw [(dc_facts k hk).2.1]; omega

theorem dc_ne_W (k : Nat) (hk : k < 10) : dc k ≠ 'W' := (dc_facts k hk).2.2.2.2.2.2.2.2.1
theorem dc_ne_dash (k : Nat) (hk : k < 10) : dc k ≠ '-' := (dc_facts k hk).2.2.2.2.2.2.2.1
theorem dc_digit (k : Nat) (hk : k < 10) : isAsciiDigit (dc k) = true := (dc_facts k hk).1

/-- The four-digit year and the two-digit fields read by `_read_isoformat_component`. -/
theorem read4 (a b c e : Nat) (ha : a < 10) (hb : b < 10) (hc : c < 10) (he : e < 10) :
    readIsoComponent [dc a, dc b, dc c, dc e] 4 = .ok ((a * 1000 + b * 100 + c * 10 + e : Nat) : Int) := by
  have := readIsoComponent_dc [a, b, c, e] (by simp) (by simp; omega)
  simp only [List.map_cons, List.map_nil, digitsNat, List.foldl_cons, List.foldl_nil, List.length_cons,
    List.length_nil] at this
  rw [this]; congr 2; omega

theorem read2 (f g : Nat) (hf : f < 10) (hg : g < 10) :
    readIsoComponent [dc f, dc g] 2 = .ok ((f * 10 + g : Nat) : Int) := by
  have := readIsoComponent_dc [f, g] (by simp) (by simp; omega)
  simp only [List.map_cons, List.map_nil, digitsNat, List.foldl_cons, List.foldl_nil, List.length_cons,
    List.length_nil] at this
  rw [this]; congr 2; omega

theorem read1 (i : Nat) (hi : i < 10) : readIsoComponent [dc i] 1 = .ok ((i : Nat) : Int) := by
  have := readIsoComponent_dc [i] (by simp) (by simp; omega)
  simp only [List.map_cons, List.map_nil, digitsNat, List.foldl_cons, List.foldl_nil, List.length_cons,
    List.length_nil] at this
  rw [this]; congr 2; omega

/-- `_parse_isoformat_date(s)` on each of the six ISO 8601 date forms of the docs, for all
digits (`Y = 1000a + 100b + 10c + e`, `M`/`W = 10f + g`, `D = 10i + j` or `i`): `YYYYMMDD`
gives the fields, the four week forms `YYYY-Www-D`, `YYYYWwwD`, `YYYY-Www`, `YYYYWww` give
`_isoweek_to_gregorian(Y, W, D or 1)`; a dash in one place and not the other raises
`Inconsistent use of dash separator` (month and week forms); any other length than 7, 8 or
10, and a non-ASCII string, raise `Invalid isoformat string`. (`YYYY-MM-DD` is
`parseIsoDatePy_ext`.) -/
def ParseIsoDateForms : Prop :=
  ∀ a b c e f g i j : Nat, a < 10 → b < 10 → c < 10 → e < 10 → f < 10 → g < 10 → i < 10 → j < 10 →
    let Y : Int := ((a * 1000 + b * 100 + c * 10 + e : Nat) : Int)
    let W : Int := ((f * 10 + g : Nat) : Int)
    parseIsoDatePy [dc a, dc b, dc c, dc e, dc f, dc g, dc i, dc j] = .ok (Y, W, ((i * 10 + j : Nat) : Int)) ∧
    parseIsoDatePy [dc a, dc b, dc c, dc e, '-', 'W', dc f, dc g, '-', dc i] = isoweekToGregorianPy Y W i ∧
    parseIsoDatePy [dc a, dc b, dc c, dc e, 'W', dc f, dc g, dc i] = isoweekToGregorianPy Y W i ∧
    parseIsoDatePy [dc a, dc b, dc c, dc e, '-', 'W', dc f, dc g] = isoweekToGregorianPy Y W 1 ∧
    parseIsoDatePy [dc a, dc b, dc c, dc e, 'W', dc f, dc g] = isoweekToGregorianPy Y W 1 ∧
    parseIsoDatePy [dc a, dc b, dc c, dc e, '-', dc f, dc g, dc i, dc j, dc j] =
      .error (.valueError "Inconsistent use of dash separator") ∧
    parseIsoDatePy [dc a, dc b, dc c, dc e, dc f, dc g, '-', dc i, dc j, dc j] =
      .error (.valueError "Inconsistent use of dash separator") ∧
    parseIsoDatePy [dc a, dc b, dc c, dc e, '-', 'W', dc f, dc g, dc i, dc j] =
      .error (.valueError "Inconsistent use of dash separator") ∧
    parseIsoDatePy [dc a, dc b, dc c, dc e, 'W', dc f, dc g, '-', dc i, dc j] =
      .error (.valueError "Inconsistent use of dash separator")

theorem parseIsoDateForms_proven : ParseIsoDateForms := by
  intro a b c e f g i j ha hb hc he hf hg hi hj
  have r4 := read4 a b c e ha hb hc he
  have r2 := read2 f g hf hg
  have r2' := read2 i j hi hj
  have r1 := read1 i hi
  have ra := dc_ascii a ha; have rb := dc_ascii b hb; have rc := dc_ascii c hc; have re := dc_ascii e he
  have rf := dc_ascii f hf; have rg := dc_ascii g hg; have ri := dc_ascii i hi; have rj := dc_ascii j hj
  have w1 := dc_ne_W f hf
  have d1 := dc_ne_dash e he
  have d2 := dc_ne_dash i hi
  have d3 := dc_ne_dash g hg
  have d4 := dc_ne_dash f hf
  have w2 := dc_ne_W i hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    unfold parseIsoDatePy
    simp [isAsciiStr, slice, charAt, ra, rb, rc, re, rf, rg, ri, rj, r4, r2, r2', r1, w1, w2, d1, d2, d3, d4,
      Ne.symm w1, Ne.symm d4, bind, Except.bind, pure, Except.pure]
    try rfl

/-- The two refusals before any field is read: a length other than 7, 8, 10, then a
non-ASCII string, both `Invalid isoformat string`. -/
def ParseIsoDateRefusals : Prop :=
  ∀ s : List Char,
    (¬ (s.length = 7 ∨ s.length = 8 ∨ s.length = 10) →
      parseIsoDatePy s = .error (.valueError "Invalid isoformat string")) ∧
    (isAsciiStr s = false → parseIsoDatePy s = .error (.valueError "Invalid isoformat string"))

theorem parseIsoDateRefusals_proven : ParseIsoDateRefusals := by
  intro s
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold parseIsoDatePy
    simp only [h, if_true]
    rfl
  · unfold parseIsoDatePy
    by_cases hl : s.length = 7 ∨ s.length = 8 ∨ s.length = 10
    · simp only [hl, not_true_eq_false, if_false, h, Bool.not_false, if_true]
      rfl
    · simp only [hl, not_false_eq_true, if_true]
      rfl

/-! ### `_is_ascii_digit` and `_find_isoformat_datetime_separator` -/

/-- `_is_ascii_digit(c)`, _pydatetime.py:298-299, is `c in "0123456789"`; on the
one-character strings its callers pass (`dtstr[idx]`) it holds exactly for the ten ASCII
digits U+0030..U+0039, so a Unicode digit such as `'٣'` or `'１'` is not one. -/
def IsAsciiDigit : Prop :=
  ∀ c : Char, isAsciiDigit c = true ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57

theorem isAsciiDigit_proven : IsAsciiDigit := by
  intro c
  unfold isAsciiDigit
  simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le]
  exact Iff.rfl

theorem isAsciiDigit_false (x : Char) (hx : x.toNat < 48 ∨ 57 < x.toNat) : isAsciiDigit x = false := by
  cases h : isAsciiDigit x
  · rfl
  · have := (isAsciiDigit_proven x).1 h; omega

theorem takeWhile_digits (ds t : List Char) (x : Char)
    (hd : ∀ d ∈ ds, isAsciiDigit d = true) (hx : isAsciiDigit x = false) :
    (ds ++ x :: t).takeWhile isAsciiDigit = ds := by
  induction ds with
  | nil => simp [hx]
  | cons d ds ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hd
    simp [hd.1, ih hd.2]

theorem takeWhile_digits_end (ds : List Char) (hd : ∀ d ∈ ds, isAsciiDigit d = true) :
    ds.takeWhile isAsciiDigit = ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hd
    simp [hd.1, ih hd.2]

/-- `_find_isoformat_datetime_separator` on a date part in each form followed by any
separator `x` and time text `t`: it returns the length of the date part, so the string is
split at the separator. For `YYYY-Www-D` a digit right after the separator would make the
date `YYYY-Www`, so `x` is a non-digit there (the documented ambiguity rule, :315-323); a
non-digit is any character outside U+0030..U+0039, stated without `_is_ascii_digit`. A
nine-character `YYYY-Www-` is `Invalid ISO string`. -/
def FindSepForms : Prop :=
  ∀ (a b c e f g i : Nat) (x : Char) (t : List Char), a < 10 → b < 10 → c < 10 → e < 10 → f < 10 →
    g < 10 → i < 10 →
    findSepPy ([dc a, dc b, dc c, dc e, '-', dc f, dc g, '-', dc i, dc i] ++ x :: t) = .ok 10 ∧
    findSepPy ([dc a, dc b, dc c, dc e, dc f, dc g, dc i, dc i] ++ x :: t) = .ok 8 ∧
    ((x.toNat < 48 ∨ 57 < x.toNat) →
      findSepPy ([dc a, dc b, dc c, dc e, '-', 'W', dc f, dc g, '-', dc i] ++ x :: t) = .ok 10) ∧
    findSepPy ([dc a, dc b, dc c, dc e, '-', 'W', dc f, dc g, '-'] ++ dc i :: dc i :: t) = .ok 8 ∧
    ((x.toNat < 48 ∨ 57 < x.toNat) → x ≠ '-' →
      findSepPy ([dc a, dc b, dc c, dc e, '-', 'W', dc f, dc g] ++ x :: t) = .ok 8) ∧
    findSepPy [dc a, dc b, dc c, dc e, '-', 'W', dc f, dc g, '-'] = .error (.valueError "Invalid ISO string")

theorem findSepForms_proven : FindSepForms := by
  intro a b c e f g i x t ha hb hc he hf hg hi
  have w1 := dc_ne_W f hf
  have w2 := dc_ne_W e he
  have d1 := dc_ne_dash e he
  have d2 := dc_ne_dash f hf
  have g1 := dc_digit f hf
  have g2 := dc_digit g hg
  have g3 := dc_digit i hi
  refine ⟨?_, ?_, fun hx => ?_, ?_, fun hx hd => ?_, ?_⟩ <;>
  · try have hx' := isAsciiDigit_false x hx
    unfold findSepPy
    simp [charAt, w1, w2, d1, d2, g1, g2, g3, Ne.symm w1, Ne.symm d2, List.takeWhile_cons, *]

/-- The basic week form `YYYYWww` of `_find_isoformat_datetime_separator` (:336-353): the
digit run from index 7 is counted (`idx` is 7 plus its length `n`), up to the first
non-digit `x` or the end of the string. `n = 0` is `YYYYWww` followed by a separator
(7); `n = 1` is `YYYYWwwD` (8) at the end or before a non-digit; from `n = 2` on the
separator itself is a digit and the date is `YYYYWww` (7) when `idx` is even, i.e. `n` odd,
and `YYYYWwwD` (8) when `idx` is odd. Stated for every digit run `ds` (digits as code points
U+0030..U+0039), so every branch of the loop and of `idx % 2` is pinned. -/
def FindSepWeekDigits : Prop :=
  ∀ (a b c e f g : Nat) (ds t : List Char) (x : Char), a < 10 → b < 10 → c < 10 → e < 10 →
    f < 10 → g < 10 → (∀ d ∈ ds, 48 ≤ d.toNat ∧ d.toNat ≤ 57) →
    let r : Nat := if ds.length = 0 then 7 else if ds.length = 1 then 8
      else if ds.length % 2 = 1 then 7 else 8
    ((x.toNat < 48 ∨ 57 < x.toNat) →
      findSepPy ([dc a, dc b, dc c, dc e, 'W', dc f, dc g] ++ ds ++ x :: t) = .ok r) ∧
    (ds ≠ [] → findSepPy ([dc a, dc b, dc c, dc e, 'W', dc f, dc g] ++ ds) = .ok r)

theorem findSepWeekDigits_proven : FindSepWeekDigits := by
  intro a b c e f g ds t x ha hb hc he hf hg hd r
  have hd' : ∀ d ∈ ds, isAsciiDigit d = true := fun d h => (isAsciiDigit_proven d).2 (hd d h)
  have w2 := dc_ne_W e he
  have d1 := dc_ne_dash e he
  have fin : (if 7 + ds.length < 9 then (Except.ok (7 + ds.length) : Py Nat)
      else if (7 + ds.length) % 2 = 0 then Except.ok 7 else Except.ok 8) = .ok r := by
    simp only [r]
    by_cases h0 : ds.length = 0
    · simp [h0]
    by_cases h1 : ds.length = 1
    · simp [h1]
    by_cases h2 : ds.length % 2 = 1
    · rw [if_neg (by omega), if_pos (by omega), if_neg h0, if_neg h1, if_pos h2]
    · rw [if_neg (by omega), if_neg (by omega), if_neg h0, if_neg h1, if_neg h2]
  refine ⟨fun hx => ?_, fun hne => ?_⟩
  · have tw := takeWhile_digits ds t x hd' (isAsciiDigit_false x hx)
    have hl7 : ([dc a, dc b, dc c, dc e, 'W', dc f, dc g] ++ ds ++ x :: t).length ≠ 7 := by
      simp
    unfold findSepPy
    rw [if_neg hl7]
    simp [charAt, w2, d1, tw]
    exact fin
  · have tw := takeWhile_digits_end ds hd'
    have hl : ds.length ≠ 0 := by simpa using hne
    have hl7 : ([dc a, dc b, dc c, dc e, 'W', dc f, dc g] ++ ds).length ≠ 7 := by
      simp; omega
    unfold findSepPy
    rw [if_neg hl7]
    simp [charAt, w2, d1, tw]
    exact fin

/-! ### `date.fromisoformat` -/

/-- `date.fromisoformat(s)` for every `str`: a non-ASCII string is refused first (`Argument
must be an ASCII str`); then a length other than 7, 8, 10 is a `ValueError`; a string the
date parser accepts gives the checked date, and one it refuses, or an invalid date, a
`ValueError`. With `ParseIsoDateForms` this fixes the result on every accepted form. -/
def DateFromisoformat : Prop :=
  ∀ s : List Char,
    (isAsciiStr s = false → dateFromIsoPy s = .error (.valueError "Argument must be an ASCII str")) ∧
    (isAsciiStr s = true → ¬ (s.length = 7 ∨ s.length = 8 ∨ s.length = 10) →
      (dateFromIsoPy s).raises "ValueError") ∧
    (∀ y m d, isAsciiStr s = true → parseIsoDatePy s = .ok (y, m, d) →
      (ValidDate y m d → dateFromIsoPy s = .ok (y, m, d)) ∧
      (¬ ValidDate y m d → (dateFromIsoPy s).raises "ValueError")) ∧
    (∀ e, isAsciiStr s = true → parseIsoDatePy s = .error e → (dateFromIsoPy s).raises "ValueError")

theorem checkDate_err' (y m d : Int) (h : ¬ ValidDate y m d) : ∃ e, checkDate y m d = .error e := by
  unfold ValidDate at h
  unfold checkDate
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · dsimp only
      split
      · exact ⟨_, rfl⟩
      · exfalso; apply h; unfold MINYEAR MAXYEAR at *; omega

theorem dateFromisoformat_proven : DateFromisoformat := by
  intro s
  have refl := parseIsoDateRefusals_proven s
  refine ⟨fun h => ?_, fun h hl => ?_, fun y m d h hp => ?_, fun e h hp => ?_⟩
  · unfold dateFromIsoPy; simp [h]
  · unfold dateFromIsoPy
    rw [if_neg (by simp [h]), if_pos hl]
    exact ⟨_, rfl, rfl⟩
  · have hl : s.length = 7 ∨ s.length = 8 ∨ s.length = 10 := by
      apply Classical.byContradiction; intro hl; rw [refl.1 hl] at hp; cases hp
    unfold dateFromIsoPy
    rw [if_neg (by simp [h]), if_neg (by simp [hl])]
    simp only [hp, bind, Except.bind]
    refine ⟨fun hv => by rw [checkDate_ok y m d hv], fun hv => ?_⟩
    obtain ⟨e, he⟩ := checkDate_err' y m d hv
    rw [he]; exact ⟨_, rfl, rfl⟩
  · unfold dateFromIsoPy
    rw [if_neg (by simp [h])]
    by_cases hl : s.length = 7 ∨ s.length = 8 ∨ s.length = 10
    · rw [if_neg (by simp [hl])]
      simp only [hp, bind, Except.bind]
      exact ⟨_, rfl, rfl⟩
    · rw [if_pos hl]
      exact ⟨_, rfl, rfl⟩

/-- `date.fromisoformat(x)` on every argument: a non-`str` (bytes included) is
`TypeError('Argument must be a str')` in Python and a `TypeError` in C's clinic converter; a
`str` with a lone surrogate is `ValueError('Argument must be an ASCII str')` in Python and a
`ValueError` in C; a `str` is `dateFromIsoPy` (pinned by `DateFromisoformat`) and C's impl. -/
def DateFromisoformatArg : Prop :=
  ∀ s : List Char,
    dateFromIsoArgPy .other = .error (.typeError "Argument must be a str") ∧
    (dateFromIsoArgC .other).raises "TypeError" ∧
    dateFromIsoArgPy .surrogateStr = .error (.valueError "Argument must be an ASCII str") ∧
    (dateFromIsoArgC .surrogateStr).raises "ValueError" ∧
    dateFromIsoArgPy (.str s) = dateFromIsoPy s ∧ dateFromIsoArgC (.str s) = dateFromIsoC s

theorem dateFromisoformatArg_proven : DateFromisoformatArg :=
  fun _ => ⟨rfl, ⟨_, rfl, rfl⟩, rfl, ⟨_, rfl, rfl⟩, rfl, rfl⟩

/-! ### `_parse_hh_mm_ss_ff` -/

/-- `_parse_hh_mm_ss_ff(t)` on the time forms of the docs, for all digits: `HH`, `HH:MM`,
`HHMMSS`, `HH:MM:SS.ffffff`, `HH:MM:SS,fff` (scaled by 1000), and a seventh fraction digit
truncated; and its three refusals: a separator other than `:` after `HH:MM`, a fraction
separator other than `.` or `,`, and a non-digit fraction. -/
def ParseHHMMSSFFForms : Prop :=
  ∀ h1 h2 m1 m2 s1 s2 u1 u2 u3 u4 u5 u6 u7 : Nat, ∀ x : Char,
    h1 < 10 → h2 < 10 → m1 < 10 → m2 < 10 → s1 < 10 → s2 < 10 → u1 < 10 → u2 < 10 → u3 < 10 →
    u4 < 10 → u5 < 10 → u6 < 10 → u7 < 10 →
    let H : Int := ((h1 * 10 + h2 : Nat) : Int)
    let M : Int := ((m1 * 10 + m2 : Nat) : Int)
    let S : Int := ((s1 * 10 + s2 : Nat) : Int)
    let U : Int := ((digitsNat [u1, u2, u3, u4, u5, u6] : Nat) : Int)
    parseHHMMSSFFPy [dc h1, dc h2] = .ok (H, 0, 0, 0) ∧
    parseHHMMSSFFPy [dc h1, dc h2, ':', dc m1, dc m2] = .ok (H, M, 0, 0) ∧
    parseHHMMSSFFPy [dc h1, dc h2, dc m1, dc m2, dc s1, dc s2] = .ok (H, M, S, 0) ∧
    parseHHMMSSFFPy [dc h1, dc h2, ':', dc m1, dc m2, ':', dc s1, dc s2, '.',
      dc u1, dc u2, dc u3, dc u4, dc u5, dc u6] = .ok (H, M, S, U) ∧
    parseHHMMSSFFPy [dc h1, dc h2, ':', dc m1, dc m2, ':', dc s1, dc s2, ',', dc u1, dc u2, dc u3] =
      .ok (H, M, S, ((digitsNat [u1, u2, u3] : Nat) : Int) * 1000) ∧
    parseHHMMSSFFPy [dc h1, dc h2, ':', dc m1, dc m2, ':', dc s1, dc s2, '.',
      dc u1, dc u2, dc u3, dc u4, dc u5, dc u6, dc u7] = .ok (H, M, S, U) ∧
    (x ≠ ':' → parseHHMMSSFFPy [dc h1, dc h2, ':', dc m1, dc m2, x, dc s1, dc s2] =
      .error (.valueError s!"Invalid time separator: {String.ofList [x]}")) ∧
    (x ≠ '.' → x ≠ ',' → parseHHMMSSFFPy [dc h1, dc h2, dc m1, dc m2, dc s1, dc s2, x, dc u1] =
      .error (.valueError "Invalid microsecond separator")) ∧
    (isAsciiDigit x = false → parseHHMMSSFFPy [dc h1, dc h2, dc m1, dc m2, dc s1, dc s2, '.', x] =
      .error (.valueError "Non-digit values in fraction"))

theorem parseHHMMSSFFForms_proven : ParseHHMMSSFFForms := by
  intro h1 h2 m1 m2 s1 s2 u1 u2 u3 u4 u5 u6 u7 x hh1 hh2 hm1 hm2 hs1 hs2 hu1 hu2 hu3 hu4 hu5 hu6 hu7
  have rh := read2 h1 h2 hh1 hh2
  have rm := read2 m1 m2 hm1 hm2
  have rs := read2 s1 s2 hs1 hs2
  have p6 : pyInt [dc u1, dc u2, dc u3, dc u4, dc u5, dc u6] = .ok (digitsNat [u1, u2, u3, u4, u5, u6]) :=
    pyInt_dc [u1, u2, u3, u4, u5, u6] (by simp) (by simp; omega)
  have p3 : pyInt [dc u1, dc u2, dc u3] = .ok (digitsNat [u1, u2, u3]) :=
    pyInt_dc [u1, u2, u3] (by simp) (by simp; omega)
  have i6 : isDigitStr [dc u1, dc u2, dc u3, dc u4, dc u5, dc u6] = true :=
    isDigitStr_dc [u1, u2, u3, u4, u5, u6] (by simp) (by simp; omega)
  have i7 : isDigitStr [dc u1, dc u2, dc u3, dc u4, dc u5, dc u6, dc u7] = true :=
    isDigitStr_dc [u1, u2, u3, u4, u5, u6, u7] (by simp) (by simp; omega)
  have i3 : isDigitStr [dc u1, dc u2, dc u3] = true := isDigitStr_dc [u1, u2, u3] (by simp) (by simp; omega)
  have cm1 : dc m1 ≠ ':' := by have := (dc_facts m1 hm1).2.1; intro h; rw [h] at this; simp at this; omega
  have cs1 : dc s1 ≠ ':' := by have := (dc_facts s1 hs1).2.1; intro h; rw [h] at this; simp at this; omega
  have cu1 : dc u1 ≠ '.' := by have := (dc_facts u1 hu1).2.1; intro h; rw [h] at this; simp at this; omega
  have g1 := dc_digit u1 hu1; have g2 := dc_digit u2 hu2; have g3 := dc_digit u3 hu3
  have g4 := dc_digit u4 hu4; have g5 := dc_digit u5 hu5; have g6 := dc_digit u6 hu6
  have g7 := dc_digit u7 hu7
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun hx => ?_, fun hx1 hx2 => ?_, fun hx => ?_⟩
  all_goals
    unfold parseHHMMSSFFPy timeCompPy fractionPy
    simp [slice, charAt, rh, rm, rs, p6, p3, i6, i7, i3, cm1, cs1, fractionCorrection, isDigitStr,
      bind, Except.bind, pure, Except.pure, *]
    try rfl

theorem fractionCorrection_pow (k : Nat) (h1 : 1 ≤ k) (h2 : k < 6) :
    fractionCorrection (k - 1) = 10 ^ (6 - k) := by
  obtain rfl | rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  all_goals rfl

theorem fractionPy_digits (pre : List Char) (sepc : Char) (ns : List Nat)
    (hsep : sepc = '.' ∨ sepc = ',') (hne : ns ≠ []) (hd : ∀ k ∈ ns, k < 10) :
    fractionPy (pre ++ sepc :: ns.map dc) pre.length =
      .ok ((digitsNat (ns.take 6) * 10 ^ (6 - min ns.length 6) : Nat) : Int) := by
  unfold fractionPy
  have hlt : pre.length < (pre ++ sepc :: ns.map dc).length := by simp
  have hc : charAt (pre ++ sepc :: ns.map dc) pre.length = sepc := by simp [charAt]
  have hdrop : (pre ++ sepc :: ns.map dc).drop (pre.length + 1) = ns.map dc := by simp
  have hsep' : ¬ (sepc ≠ '.' ∧ sepc ≠ ',') := by rcases hsep with h | h <;> simp [h]
  have hdig := isDigitStr_dc ns hne hd
  rw [if_pos hlt, hc, hdrop]
  simp only [hsep', hdig, ↓reduceIte, List.length_map, Bool.not_true, Bool.false_eq_true]
  by_cases hl : ns.length < 6
  · have hm : min ns.length 6 = ns.length := by omega
    have ht : ns.take 6 = ns := List.take_of_length_le (by omega)
    have hp : pyInt ((ns.map dc).take ns.length) = .ok (digitsNat ns) := by
      rw [List.take_of_length_le (by simp)]; exact pyInt_dc ns hne hd
    have h1 : 1 ≤ ns.length := by cases ns with | nil => exact absurd rfl hne | cons _ _ => simp
    simp only [hm, hp, ht, if_pos hl, fractionCorrection_pow _ h1 hl]
    simp [bind, Except.bind, pure, Except.pure]
  · have hm : min ns.length 6 = 6 := by omega
    have hp : pyInt ((ns.map dc).take 6) = .ok (digitsNat (ns.take 6)) := by
      rw [← List.map_take]
      exact pyInt_dc _ (by intro h; rw [List.take_eq_nil_iff] at h; rcases h with h | h; omega; exact hne h)
        (fun k hk => hd k (List.mem_of_mem_take hk))
    simp only [hm, hp]
    simp [bind, Except.bind, pure, Except.pure]

/-- `_parse_hh_mm_ss_ff(t)` on `HH:MM:SS` or `HHMMSS`, a `.` or `,`, and any nonempty run of
ASCII digits: the fraction is its first six digits scaled to microseconds, i.e. a run of
`k < 6` digits is multiplied by `10 ** (6 - k)` (one digit is tenths of a second, so
`.5` is 500000 and `.12345` is 123450) and digits after the sixth are dropped. This fixes
every entry of `_FRACTION_CORRECTION` (:406, used at :448-449) against `10 ** (6 - k)`. -/
def ParseHHMMSSFFFraction : Prop :=
  ∀ h1 h2 m1 m2 s1 s2 : Nat, ∀ (sepc : Char) (ns : List Nat),
    h1 < 10 → h2 < 10 → m1 < 10 → m2 < 10 → s1 < 10 → s2 < 10 → (sepc = '.' ∨ sepc = ',') →
    ns ≠ [] → (∀ k ∈ ns, k < 10) →
    let H : Int := ((h1 * 10 + h2 : Nat) : Int)
    let M : Int := ((m1 * 10 + m2 : Nat) : Int)
    let S : Int := ((s1 * 10 + s2 : Nat) : Int)
    let U : Int := ((digitsNat (ns.take 6) * 10 ^ (6 - min ns.length 6) : Nat) : Int)
    parseHHMMSSFFPy ([dc h1, dc h2, ':', dc m1, dc m2, ':', dc s1, dc s2] ++ sepc :: ns.map dc) =
      .ok (H, M, S, U) ∧
    parseHHMMSSFFPy ([dc h1, dc h2, dc m1, dc m2, dc s1, dc s2] ++ sepc :: ns.map dc) = .ok (H, M, S, U)

theorem parseHHMMSSFFFraction_proven : ParseHHMMSSFFFraction := by
  intro h1 h2 m1 m2 s1 s2 sepc ns hh1 hh2 hm1 hm2 hs1 hs2 hsep hne hd
  have rh := read2 h1 h2 hh1 hh2
  have rm := read2 m1 m2 hm1 hm2
  have rs := read2 s1 s2 hs1 hs2
  have cm1 : dc m1 ≠ ':' := by have := (dc_facts m1 hm1).2.1; intro h; rw [h] at this; simp at this; omega
  have cs1 : dc s1 ≠ ':' := by have := (dc_facts s1 hs1).2.1; intro h; rw [h] at this; simp at this; omega
  have fr1 := fractionPy_digits [dc h1, dc h2, ':', dc m1, dc m2, ':', dc s1, dc s2] sepc ns hsep hne hd
  have fr2 := fractionPy_digits [dc h1, dc h2, dc m1, dc m2, dc s1, dc s2] sepc ns hsep hne hd
  simp only [List.length_cons, List.length_nil, List.cons_append, List.nil_append] at fr1 fr2
  refine ⟨?_, ?_⟩
  all_goals
    unfold parseHHMMSSFFPy timeCompPy
    simp [slice, charAt, rh, rm, rs, cm1, cs1, fr1, fr2, bind, Except.bind, pure, Except.pure]

end PyLean.Datetime
