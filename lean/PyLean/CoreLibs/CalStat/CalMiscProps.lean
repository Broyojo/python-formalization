import PyLean.CoreLibs.CalStat.CalFmtProps

/-! Properties of the `calendar` mirror, continued: year layout, HTML, codecs, locale
switching, `main`, and the module-level odds and ends. -/

namespace PyLean.CoreLibs.CalStat

open PyLean PyLean.Datetime

/-! ## `formatyear` line structure -/

theorem noNL_strTimes_space (n : Int) : NoNL (strTimes [' '] n) := by
  unfold NoNL strTimes
  simp only [List.mem_flatten, List.mem_replicate]
  rintro ⟨l, ⟨-, rfl⟩, h⟩
  simp at h

theorem noNL_formatstring (cols : List Str) (cw sp : Int) (h : ∀ s ∈ cols, NoNL s) :
    NoNL (formatstring cols cw sp) := by
  unfold formatstring
  apply noNL_join (noNL_strTimes_space sp)
  intro p hp
  simp only [List.mem_map] at hp
  obtain ⟨s, hs, rfl⟩ := hp
  exact noNL_center (h s hs) _

theorem yearWeekLines_count (row : List (List (List (Int × Int)))) (cw c l : Int)
    (fw : Nat → List (Int × Int) → Str) (hfw : ∀ k wk, NoNL (fw k wk)) :
    (yearWeekLines row cw c l fw).count '\n' = (row.map List.length).foldr max 0 * l.toNat := by
  unfold yearWeekLines
  simp only
  generalize hh : (row.map List.length).foldr max 0 = height
  have := count_flatten_lines ((List.range height).map (fun j =>
    rstrip (formatstring (row.zipIdx.map (fun p => match p.1[j]? with
      | none => []
      | some wk => fw p.2 wk)) cw c))) l (fun s hs => by
        simp only [List.mem_map] at hs
        obtain ⟨j, _, rfl⟩ := hs
        apply noNL_rstrip
        apply noNL_formatstring
        intro t ht
        simp only [List.mem_map] at ht
        obtain ⟨p, _, rfl⟩ := ht
        split
        · unfold NoNL; simp
        · exact hfw _ _)
  simp only [List.map_map, List.length_map, List.length_range] at this
  exact this

theorem mapM_count {α : Type} (f : α → Py Str) (l : List α) (g : α → Nat) (ch : Char)
    (h : ∀ x ∈ l, ∃ y, f x = .ok y ∧ y.count ch = g x) :
    ∃ r, l.mapM f = .ok r ∧ r.flatten.count ch = (l.map g).sum := by
  induction l with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons a as ih =>
    obtain ⟨y, hy, hc⟩ := h a (by simp)
    obtain ⟨r, hr, hc2⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨y :: r, ?_, ?_⟩
    · simp only [List.mapM_cons, hy, hr]; rfl
    · simp only [List.flatten_cons, List.count_append, hc, hc2, List.map_cons, List.sum_cons]

theorem textMonthRow_range (m i k : Int) (hm : 1 ≤ m) (hi : 0 ≤ i) (hk : k ∈ textMonthRow m i) :
    1 ≤ k ∧ k ≤ 12 := by
  unfold textMonthRow rangeI at hk
  simp only [List.mem_map, List.mem_range] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have : 0 ≤ m * i := Int.mul_nonneg (by omega) hi
  omega

theorem yearRowHead_ok (y : Int) (months : List Int) (h : Str) (cw C L : Int) (hy : ReprOk y)
    (hm : ∀ k ∈ months, 1 ≤ k ∧ k ≤ 12) (hh : NoNL h) :
    ∃ s, yearRowHead cNames y months h cw C L = .ok s ∧ s.count '\n' = 3 * L.toNat := by
  obtain ⟨names, hn, -, hall⟩ := mapM_exists
    (fun k => tFormatmonthname cNames y k cw false) months NoNL
    (fun k hk => tFormatmonthname_ok y k cw (hm k hk) hy false)
  have n1 : NoNL (rstrip (formatstring names cw C)) :=
    noNL_rstrip (noNL_formatstring _ _ _ hall)
  have n2 : NoNL (rstrip (formatstring (months.map (fun _ => h)) cw C)) := by
    apply noNL_rstrip
    apply noNL_formatstring
    intro s hs
    simp only [List.mem_map] at hs
    obtain ⟨_, _, rfl⟩ := hs
    exact hh
  have hres : yearRowHead cNames y months h cw C L = .ok (nl L ++ rstrip (formatstring names cw C) ++
      nl L ++ rstrip (formatstring (months.map (fun _ => h)) cw C) ++ nl L) := by
    simp only [yearRowHead, bind, Except.bind, hn, pure, Except.pure]
  refine ⟨_, hres, ?_⟩
  simp only [List.count_append, count_nl, count_noNL n1, count_noNL n2]
  omega

/-- `formatyear` for `m >= 1`: a title block, then for each row of months a blank block, a
names line, a header line and as many week lines as the longest month in the row; every block is
followed by `l` newlines. `pryear` prints the same text. -/
def FormatyearLines : Prop :=
  ∀ (c : Calendar) (y w l cc m : Int), 1 ≤ m → ReprOk y →
    ∃ s rows, tFormatyear cNames c y w l cc m = .ok s ∧ c.yeardays2calendar y m = .ok rows ∧
      s.count '\n' = (max 1 l).toNat *
        (1 + (rows.map (fun r => 3 + (r.map List.length).foldr max 0)).sum) ∧
      tPryear cNames c y w l cc m = .ok s

theorem sum_mul_map {α : Type} (l : List α) (f : α → Nat) (k : Nat) :
    (l.map (fun x => f x * k)).sum = (l.map f).sum * k := by
  induction l with
  | nil => simp
  | cons a as ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

theorem map_zipIdx_fst {α β : Type} (F : α → β) (l : List α) :
    l.zipIdx.map (fun p => F p.1) = l.map F := by
  have := congrArg (List.map F) (List.zipIdx_map_fst 0 l)
  rw [List.map_map] at this
  exact this

theorem formatyearLines_proven : FormatyearLines := by
  intro c y w l cc m hm hy
  obtain ⟨yr, hyr, hyn⟩ := reprInt_ok y hy
  obtain ⟨h, hh, hhn⟩ := tFormatweekheader_noNL c (max 2 w) (by omega)
  obtain ⟨ms, hms⟩ := yeardays2_ok c y
  have hrows : c.yeardays2calendar y m = .ok (chunks m.toNat ms) := by
    unfold Calendar.yeardays2calendar
    simp only [bind, Except.bind, hms]
    unfold pyChunks
    rw [if_neg (by omega), if_neg (by omega)]
  generalize chunks m.toNat ms = rows at hrows
  have hbody := mapM_count
    (yearRow cNames y m h ((max 2 w + 1) * 7 - 1) (max 2 cc) (max 1 l) (fun _ _ wk => tFormatweek wk (max 2 w)))
    rows.zipIdx
    (fun p => (fun (r : List (List (List (Int × Int)))) => 3 + (r.map List.length).foldr max 0) p.1 * (max 1 l).toNat)
    '\n'
    (fun p _ => by
      obtain ⟨s, hs, hc⟩ := yearRowHead_ok y (textMonthRow m (p.2 : Int)) h
        ((max 2 w + 1) * 7 - 1) (max 2 cc) (max 1 l) hy
        (fun k hk => textMonthRow_range m _ k hm (by omega) hk) hhn
      have hc2 := yearWeekLines_count p.1 ((max 2 w + 1) * 7 - 1) (max 2 cc) (max 1 l)
        (fun _ wk => tFormatweek wk (max 2 w)) (fun _ wk => noNL_tFormatweek wk _)
      have hres : yearRow cNames y m h ((max 2 w + 1) * 7 - 1) (max 2 cc) (max 1 l)
          (fun _ _ wk => tFormatweek wk (max 2 w)) p =
          .ok (s ++ yearWeekLines p.1 ((max 2 w + 1) * 7 - 1) (max 2 cc) (max 1 l)
            (fun _ wk => tFormatweek wk (max 2 w))) := by
        simp only [yearRow, bind, Except.bind, hs, pure, Except.pure]
      refine ⟨_, hres, ?_⟩
      simp only [List.count_append, hc, hc2]
      rw [Nat.add_mul])
  obtain ⟨r, hr, hcount⟩ := hbody
  have hres : tFormatyear cNames c y w l cc m =
      .ok (rstrip (center yr (((max 2 w + 1) * 7 - 1) * m + max 2 cc * (m - 1))) ++ nl (max 1 l) ++
        r.flatten) := by
    unfold tFormatyear tFormatyearWith
    simp only [bind, Except.bind, hyr, hh, hrows, pure, Except.pure]
    rw [show (rows.zipIdx.mapM (yearRow cNames y m h ((max 2 w + 1) * 7 - 1) (max 2 cc) (max 1 l)
      fun _ _ wk => tFormatweek wk (max 2 w))) = .ok r from hr]
  refine ⟨_, rows, hres, hrows, ?_, hres⟩
  simp only [List.count_append, count_nl, count_noNL (noNL_rstrip (noNL_center hyn _)), hcount]
  rw [sum_mul_map]
  rw [map_zipIdx_fst (fun (r : List (List (List (Int × Int)))) =>
    3 + (r.map List.length).foldr max 0) rows, Nat.mul_add, Nat.mul_one,
    Nat.mul_comm (List.sum _) _]
  omega

/-! ## HTML month -/

theorem reprOk_small (d : Int) (h0 : 0 ≤ d) (h1 : d < 100) : ReprOk d := by
  have : ∀ n : Fin 100, (Nat.toDigits 10 n.val).length ≤ 4300 := by decide
  unfold ReprOk Fractions.numDigits Fractions.maxStrDigits
  exact this ⟨d.natAbs, by omega⟩

theorem hFormatweekheader_ok (c : Calendar) :
    ∃ s, hFormatweekheader cNames c = .ok s ∧ NoNL s := by
  obtain ⟨r, hr, -, hall⟩ := mapM_exists (hFormatweekday cNames) c.iterweekdays NoNL
    (fun i hi => by
      obtain ⟨h0, h1⟩ := iterweekdays_range c i hi
      have hl1 : (cssclasses.length : Int) = 7 := by decide
      have hl2 : (cNames.dayAbbr.length : Int) = 7 := by decide
      obtain ⟨cls, hc, hi1⟩ := pyIndex_ok cssclasses i h0 (by omega)
      obtain ⟨ab, ha, hi2⟩ := pyIndex_ok cNames.dayAbbr i h0 (by omega)
      have hallc : ∀ t ∈ cssclasses, NoNL t := by unfold NoNL; decide
      have l1 : NoNL (lit "<th class=\"") := by unfold NoNL lit; decide
      have l2 : NoNL (lit "\">") := by unfold NoNL lit; decide
      have l3 : NoNL (lit "</th>") := by unfold NoNL lit; decide
      refine ⟨_, ?_, noNL_append (noNL_append (noNL_append (noNL_append l1 (hallc cls hc)) l2)
        (cNames_noNL.2.1 ab ha)) l3⟩
      simp only [hFormatweekday, localizedGet, bind, Except.bind, hi1, hi2, pure, Except.pure])
  have l1 : NoNL (lit "<tr>") := by unfold NoNL lit; decide
  have l2 : NoNL (lit "</tr>") := by unfold NoNL lit; decide
  have hf : NoNL r.flatten := by
    unfold NoNL
    simp only [List.mem_flatten, not_exists, not_and]
    exact fun l hl => hall l hl
  refine ⟨_, ?_, noNL_append (noNL_append l1 hf) l2⟩
  simp only [hFormatweekheader, bind, Except.bind, hr, pure, Except.pure]

theorem hFormatmonthname_ok (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) (hy : ReprOk y) (withyear : Bool) :
    ∃ s, hFormatmonthname cNames y m withyear = .ok s ∧ NoNL s := by
  obtain ⟨yr, hyr, hn⟩ := reprInt_ok y hy
  have hlen : ((localizedMonthList cNames.monthName).length : Int) = 13 := by decide
  obtain ⟨x, hx, hi⟩ := pyIndex_ok (localizedMonthList cNames.monthName) m (by omega) (by omega)
  have hxn : NoNL x := by
    simp only [localizedMonthList, List.mem_cons] at hx
    rcases hx with rfl | hx
    · unfold NoNL; simp
    · exact cNames_noNL.2.2 x hx
  have l1 : NoNL (lit "<tr><th colspan=\"7\" class=\"month\">") := by unfold NoNL lit; decide
  have l2 : NoNL (lit "</th></tr>") := by unfold NoNL lit; decide
  unfold hFormatmonthname localizedGet
  rw [validateMonth_ok m hm]
  simp only [bind, Except.bind, hi]
  cases withyear with
  | true =>
    simp only [if_true, hyr, pure, Except.pure]
    exact ⟨_, rfl, noNL_append (noNL_append l1 (noNL_append (noNL_append hxn (by unfold NoNL; decide)) hn)) l2⟩
  | false =>
    simp only [Bool.false_eq_true, if_false, pure, Except.pure]
    exact ⟨_, rfl, noNL_append (noNL_append l1 hxn) l2⟩

theorem hFormatweek_ok (week : List (Int × Int))
    (h : ∀ p ∈ week, 0 ≤ p.1 ∧ p.1 < 100 ∧ 0 ≤ p.2 ∧ p.2 ≤ 6) :
    ∃ s, hFormatweek week = .ok s ∧ NoNL s := by
  obtain ⟨r, hr, -, hall⟩ := mapM_exists (fun p : Int × Int => hFormatday p.1 p.2) week NoNL
    (fun p hp => hFormatday_noNL p.1 p.2 ⟨(h p hp).2.2.1, (h p hp).2.2.2⟩
      (reprOk_small _ (h p hp).1 (h p hp).2.1))
  have l1 : NoNL (lit "<tr>") := by unfold NoNL lit; decide
  have l2 : NoNL (lit "</tr>") := by unfold NoNL lit; decide
  have hf : NoNL r.flatten := by
    unfold NoNL
    simp only [List.mem_flatten, not_exists, not_and]
    exact fun l hl => hall l hl
  refine ⟨_, ?_, noNL_append (noNL_append l1 hf) l2⟩
  simp only [hFormatweek, bind, Except.bind, hr, pure, Except.pure]

theorem count_flatten_nl1 (lines : List Str) (h : ∀ s ∈ lines, NoNL s) :
    ((lines.map (· ++ ['\n'])).flatten).count '\n' = lines.length := by
  induction lines with
  | nil => simp
  | cons a as ih =>
    have ih' := ih (fun s hs => h s (List.mem_cons_of_mem _ hs))
    simp only [List.map_cons, List.flatten_cons, List.count_append, ih', count_noNL (h a (by simp)),
      List.length_cons]
    simp
    omega

/-- `HTMLCalendar.formatmonth` puts the table tag, the name row, the header row, one row per
week and the closing tag on lines of their own. It succeeds for every first weekday and year. -/
def HtmlMonthLines : Prop :=
  ∀ (c : Calendar) (y m : Int) (withyear : Bool), (1 ≤ m ∧ m ≤ 12) → ReprOk y →
    ∃ s wks, hFormatmonth cNames c y m withyear = .ok s ∧ c.monthdays2calendar y m = .ok wks ∧
      s.count '\n' = wks.length + 4

theorem htmlMonthLines_proven : HtmlMonthLines := by
  intro c y m withyear hm hy
  obtain ⟨name, h1, n1⟩ := hFormatmonthname_ok y m hm hy withyear
  obtain ⟨head, h2, n2⟩ := hFormatweekheader_ok c
  obtain ⟨ll, hl1, hl2, -, -, -⟩ := monthdays2calendar_ok c y m hm
  have hwk : ∀ week ∈ chunks 7 ll, ∃ s, hFormatweek week = .ok s ∧ NoNL s := by
    intro week hw
    apply hFormatweek_ok
    intro p hp
    have hmem : p ∈ ll := by
      have hfl := chunks_flatten 7 (by decide) ll
      rw [← hfl]
      exact List.mem_flatten.mpr ⟨week, hw, hp⟩
    obtain ⟨l', hl', hall⟩ := itermonthdays2Weekday_proven c y m hm
    rw [hl1] at hl'
    cases hl'
    obtain ⟨d, wd⟩ := p
    obtain ⟨h0, h6, hne⟩ := hall d wd hmem
    simp only
    by_cases hd : d = 0
    · subst hd; omega
    · obtain ⟨-, hdr, -⟩ := weekday_eq (hne hd)
      have := daysInMonth_bounds y m hm
      omega
  obtain ⟨rows, hr, hrl, hall⟩ := mapM_exists hFormatweek (chunks 7 ll) NoNL hwk
  have nt : NoNL (htmlTable "month") := by unfold NoNL htmlTable lit; decide
  have ne : NoNL (lit "</table>") := by unfold NoNL lit; decide
  have hres : hFormatmonth cNames c y m withyear = .ok (htmlTable "month" ++ ['\n'] ++ name ++ ['\n'] ++
      head ++ ['\n'] ++ (rows.map (· ++ ['\n'])).flatten ++ lit "</table>" ++ ['\n']) := by
    simp only [hFormatmonth, bind, Except.bind, h1, h2, hl2, hr, pure, Except.pure]
  refine ⟨_, chunks 7 ll, hres, hl2, ?_⟩
  simp only [List.count_append, count_noNL nt, count_noNL n1, count_noNL n2, count_noNL ne,
    count_flatten_nl1 rows hall, hrl]
  simp
  omega

/-! ## `str.encode(..., "xmlcharrefreplace")` -/

theorem digit_lt {c : Char} (h : c.isDigit = true) : c.toNat < 128 := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  have h2 := h.2
  simp only [Char.toNat]
  have : c.val.toNat ≤ 57 := by
    have := UInt32.le_iff_toNat_le.mp h2
    simpa using this
  omega

theorem encodeChar_ascii (c : Char) : ∀ b ∈ encodeChar .ascii c, b < 128 := by
  intro b hb
  unfold encodeChar at hb
  by_cases hlt : c.toNat < Codec.ascii.limit
  · rw [if_pos hlt] at hb
    simp only [List.mem_singleton] at hb
    have : Codec.ascii.limit = 128 := rfl
    omega
  · rw [if_neg hlt] at hb
    simp only [List.mem_map, List.mem_append, lit] at hb
    obtain ⟨ch, hch, rfl⟩ := hb
    rcases hch with (hch | hch) | hch
    · revert ch; decide
    · exact digit_lt (Nat.isDigit_of_mem_toDigits (by decide) (by decide) hch)
    · revert ch; decide

/-- `xmlcharrefreplace` under `ascii` yields only ASCII, whatever the input, and leaves ASCII
text unchanged; so `formatyearpage(encoding='ascii')` is a pure ASCII page for every `css`. -/
def XmlcharrefAscii : Prop :=
  (∀ s : Str, ∀ b ∈ encodeXml .ascii s, b < 128) ∧
  (∀ s : Str, (∀ c ∈ s, c.toNat < 128) → encodeXml .ascii s = s.map Char.toNat) ∧
  (∀ (N : Names) (c : Calendar) (y w : Int) (css : Option Str) (b : List Nat),
    hFormatyearpage N c y w css (some (lit "ascii")) = .ok b → ∀ x ∈ b, x < 128)

theorem codecOf_ascii : codecOf (lit "ascii") = .ok .ascii := by
  unfold codecOf lit
  simp

theorem xmlcharrefAscii_proven : XmlcharrefAscii := by
  have h1 : ∀ s : Str, ∀ b ∈ encodeXml .ascii s, b < 128 := by
    intro s b hb
    unfold encodeXml at hb
    simp only [List.mem_flatMap] at hb
    obtain ⟨c, _, hb⟩ := hb
    exact encodeChar_ascii c b hb
  refine ⟨h1, ?_, ?_⟩
  · intro s hs
    unfold encodeXml
    induction s with
    | nil => rfl
    | cons a as ih =>
      simp only [List.flatMap_cons, List.map_cons]
      rw [ih (fun c hc => hs c (List.mem_cons_of_mem _ hc))]
      have := hs a (by simp)
      simp [encodeChar, Codec.limit, this]
  · intro N c y w css b h
    unfold hFormatyearpage at h
    simp only [Option.getD_some, bind, Except.bind, codecOf_ascii, pure, Except.pure] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        exact h1 _

/-! ## `different_locale` -/

/-- `with different_locale(loc)`: if the locale can be set the body runs under it and the previous
`LC_TIME` is back afterwards, also when the body raised; if it cannot, the body does not run and
nothing changes. The saved locale must be a settable one, which it is since it came from
`setlocale(LC_TIME, None)`. -/
def DifferentLocaleRestores : Prop :=
  ∀ (α : Type) (e : LocaleEnv) (loc : String) (body : LocaleEnv → Py α),
    e.current ≠ "" → e.supported e.current = true →
    let t := if loc = "" then e.userDefault else loc
    (e.supported t = true →
      (withDifferentLocale e loc body).1 = body { e with current := t } ∧
      (withDifferentLocale e loc body).2.current = e.current) ∧
    (e.supported t = false →
      (withDifferentLocale e loc body).1 = .error (.named "Error" "unsupported locale setting") ∧
      (withDifferentLocale e loc body).2.current = e.current)

theorem differentLocaleRestores_proven : DifferentLocaleRestores := by
  intro α e loc body h1 h2 t
  constructor
  · intro hs
    have hset : setlocale e loc = .ok { e with current := t } := by
      unfold setlocale
      simp only [hs, t, if_true]
    have hback : setlocale { e with current := t } e.current = .ok { e with current := e.current } := by
      unfold setlocale
      simp only [h1, if_false, h2, if_true]
    unfold withDifferentLocale
    simp only [hset, hback]
    simp
  · intro hs
    have hset : setlocale e loc = .error (.named "Error" "unsupported locale setting") := by
      unfold setlocale
      simp only [t] at hs
      simp only [hs, Bool.false_eq_true, if_false]
    unfold withDifferentLocale
    simp only [hset]
    simp

/-- `_get_default_locale`: the current `LC_TIME` unless it is `C`, in which case the
user's preferred locale. `LocaleTextCalendar`/`LocaleHTMLCalendar` keep an explicit
locale as given. -/
def GetDefaultLocaleSpec : Prop :=
  ∀ (e : LocaleEnv),
    (e.current ≠ "C" → getDefaultLocale e = .ok e.current) ∧
    (e.current = "C" → e.supported "C" = true → e.supported e.userDefault = true →
      getDefaultLocale e = .ok e.userDefault) ∧
    (∀ l : String, initLocale e (some l) = .ok l) ∧
    initLocale e none = getDefaultLocale e

theorem getDefaultLocaleSpec_proven : GetDefaultLocaleSpec := by
  intro e
  refine ⟨?_, ?_, fun _ => rfl, rfl⟩
  · intro h
    unfold getDefaultLocale
    rw [if_neg h]
  · intro h1 h2 h3
    have hr := (differentLocaleRestores_proven String e "" (fun e' => .ok e'.current)
      (by rw [h1]; decide) (by rw [h1]; exact h2))
    simp only [if_true] at hr
    unfold getDefaultLocale
    rw [if_pos h1]
    exact (hr.1 h3).1

/-- The locale subclasses are the base classes run under the locale: when it can be set, each
overridden method returns the base method with that locale's name tables, and
leaves `LC_TIME` unchanged. -/
def LocaleCalendarMethods : Prop :=
  ∀ (e : LocaleEnv) (loc : String) (y m d w : Int) (wy : Bool),
    e.current ≠ "" → e.supported e.current = true → loc ≠ "" → e.supported loc = true →
    (ltFormatweekday e loc d w).1 = tFormatweekday (e.names loc) d w ∧
    (ltFormatweekday e loc d w).2.current = e.current ∧
    (ltFormatmonthname e loc y m w wy).1 = tFormatmonthname (e.names loc) y m w wy ∧
    (ltFormatmonthname e loc y m w wy).2.current = e.current ∧
    (lhFormatweekday e loc d).1 = hFormatweekday (e.names loc) d ∧
    (lhFormatweekday e loc d).2.current = e.current ∧
    (lhFormatmonthname e loc y m wy).1 = hFormatmonthname (e.names loc) y m wy ∧
    (lhFormatmonthname e loc y m wy).2.current = e.current

theorem localeCalendarMethods_proven : LocaleCalendarMethods := by
  intro e loc y m d w wy h1 h2 h3 h4
  have R := fun (α : Type) (body : LocaleEnv → Py α) => differentLocaleRestores_proven α e loc body h1 h2
  simp only [if_neg h3] at R
  have a := (R _ (fun e' => tFormatweekday (e'.names e'.current) d w)).1 h4
  have b := (R _ (fun e' => tFormatmonthname (e'.names e'.current) y m w wy)).1 h4
  have c := (R _ (fun e' => hFormatweekday (e'.names e'.current) d)).1 h4
  have f := (R _ (fun e' => hFormatmonthname (e'.names e'.current) y m wy)).1 h4
  exact ⟨a.1, a.2, b.1, b.2, c.1, c.2, f.1, f.2⟩

/-! ## `main` -/

/-- The checks of `main`, in source order: `--locale` without `--encoding` and a month with
`--type html` are `parser.error` exits, a bad month in text mode is `IllegalMonthError`. -/
def MainChecks : Prop :=
  ∀ (A : Ansi) (N : Names) (today : Date) (o : Options),
    (strTruthy o.locale = true → strTruthy o.encoding = false →
      mainRun A N today o = .error (.named "SystemExit" "2")) ∧
    (strTruthy o.locale = false → o.type = lit "html" → (∃ mo, o.month = some mo ∧ mo ≠ 0) →
      mainRun A N today o = .error (.named "SystemExit" "2")) ∧
    (strTruthy o.locale = false → o.type ≠ lit "html" → ∀ mo, o.month = some mo →
      ¬(1 ≤ mo ∧ mo ≤ 12) → mainRun A N today o = .error (illegalMonth mo))

theorem mainChecks_proven : MainChecks := by
  intro A N today o
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2
    simp [mainRun, h1, h2, parserError, bind, Except.bind, throw, throwThe, MonadExcept.throw]
    rfl
  · rintro h1 h2 ⟨mo, h3, h4⟩
    simp [mainRun, h1, h2, h3, h4, parserError, bind, Except.bind, throw, throwThe, MonadExcept.throw]
    rfl
  · intro h1 h2 mo h3 h4
    simp [mainRun, h1, h2, h3, validateMonth_err mo h4, bind, Except.bind]

/-- `python -m calendar YEAR MONTH` prints what `_CLIDemoCalendar.formatmonth` returns with the
first weekday from `-f`; for a month other than today's, that is `TextCalendar.formatmonth`. -/
def MainMonthOutput : Prop :=
  ∀ (A : Ansi) (N : Names) (today : Date) (o : Options) (y mo : Int),
    o.locale = none → o.encoding = none → o.type ≠ lit "html" → o.year = some y → o.month = some mo →
    (1 ≤ mo ∧ mo ≤ 12) →
    (mainRun A N today o = (MainOut.text <$> dFormatmonth A N ⟨o.firstWeekday⟩ (some today) y mo o.width o.lines)) ∧
    ((today.1 ≠ y ∨ today.2.1 ≠ mo) →
      mainRun A N today o = (MainOut.text <$> tFormatmonth N ⟨o.firstWeekday⟩ y mo o.width o.lines))

theorem mainMonthOutput_proven : MainMonthOutput := by
  intro A N today o y mo h1 h2 h3 h4 h5 h6
  have key : mainRun A N today o =
      (MainOut.text <$> dFormatmonth A N ⟨o.firstWeekday⟩ (some today) y mo o.width o.lines) := by
    simp only [mainRun, h1, h2, h3, h4, h5, strTruthy, Bool.false_and, Bool.false_eq_true, if_false,
      Calendar.setfirstweekday, validateMonth_ok mo h6, bind, Except.bind, pure, Except.pure]
    cases dFormatmonth A N ⟨o.firstWeekday⟩ (some today) y mo o.width o.lines <;> rfl
  refine ⟨key, fun h => ?_⟩
  rw [key, demoIsText_proven.2.1 A N _ y mo _ _ today h]

/-! ## Month names -/

/-- `formatmonthname` of both formatters validates first: a month outside 1..12, including
the 0 that indexes the empty entry of `month_name`, is `IllegalMonthError`, never an empty
title. A valid month gives the name, centred in `width` in the text formatter. -/
def FormatmonthnameSpec : Prop :=
  ∀ (N : Names) (y m w : Int) (wy : Bool),
    (¬(1 ≤ m ∧ m ≤ 12) → tFormatmonthname N y m w wy = .error (illegalMonth m) ∧
      hFormatmonthname N y m wy = .error (illegalMonth m)) ∧
    ((1 ≤ m ∧ m ≤ 12) → N.WellFormed → ∃ t ∈ N.monthName,
      tFormatmonthname N y m w false = .ok (center t w))

theorem formatmonthnameSpec_proven : FormatmonthnameSpec := by
  intro N y m w wy
  constructor
  · intro h
    constructor
    · unfold tFormatmonthname
      rw [validateMonth_err m h]
      rfl
    · unfold hFormatmonthname
      rw [validateMonth_err m h]
      rfl
  · intro hm hN
    have hl : ((localizedMonthList N.monthName).length : Int) = 13 := by
      have := hN.2.2
      simp [localizedMonthList, this]
    obtain ⟨k, hk⟩ : ∃ k, m.toNat = k + 1 := ⟨m.toNat - 1, by omega⟩
    have hlt : k < N.monthName.length := by have := hN.2.2; omega
    refine ⟨N.monthName[k], List.getElem_mem hlt, ?_⟩
    have hi : pyIndex (localizedMonthList N.monthName) m = .ok N.monthName[k] := by
      unfold pyIndex
      simp only
      rw [if_neg (by omega), if_neg (by omega), hk]
      simp only [localizedMonthList, List.getElem?_cons_succ]
      simp [hlt]
    unfold tFormatmonthname localizedGet
    rw [validateMonth_ok m hm]
    simp only [bind, Except.bind, hi, Bool.false_eq_true, if_false, pure, Except.pure]

/-! ## Module odds and ends -/

/-- Module `setfirstweekday`: 0..6 are accepted and stored, anything else raises
`IllegalWeekdayError` with the source's message. -/
def SetfirstweekdaySpec : Prop :=
  ∀ (c : Calendar) (fw : Int),
    ((0 ≤ fw ∧ fw ≤ 6) → ∃ c', setfirstweekdayModule c fw = .ok c' ∧ c'.firstweekday = fw) ∧
    (¬(0 ≤ fw ∧ fw ≤ 6) → setfirstweekdayModule c fw = .error
      (.named "IllegalWeekdayError" s!"bad weekday number {fw}; must be 0 (Monday) to 6 (Sunday)"))

theorem setfirstweekdaySpec_proven : SetfirstweekdaySpec := by
  intro c fw
  constructor
  · intro h
    refine ⟨⟨fw⟩, ?_, ?_⟩
    · unfold setfirstweekdayModule
      rw [if_neg (by omega)]
      rfl
    · show fw % 7 = fw
      omega
  · intro h
    unfold setfirstweekdayModule
    rw [if_pos h]
    rfl

/-- The deprecated `calendar.January`/`February` are the values of `JANUARY`/`FEBRUARY`; any other
missing attribute raises `AttributeError`. -/
def ModuleGetattrSpec : Prop :=
  (∃ w, moduleGetattr "January" = .ok (months12[0]!, w)) ∧
  (∃ w, moduleGetattr "February" = .ok (months12[1]!, w)) ∧
  ∀ name : String, name ≠ "January" → name ≠ "February" →
    moduleGetattr name = .error (.named "AttributeError" s!"module 'calendar' has no attribute '{name}'")

theorem moduleGetattrSpec_proven : ModuleGetattrSpec := by
  refine ⟨⟨s!"The 'January' attribute is deprecated, use '{"January".toUpper}' instead", ?_⟩,
    ⟨s!"The 'February' attribute is deprecated, use '{"February".toUpper}' instead", ?_⟩, ?_⟩
  · unfold moduleGetattr; rw [if_pos (Or.inl rfl), if_pos rfl]; rfl
  · unfold moduleGetattr
    rw [if_pos (Or.inr rfl), if_neg (by decide)]
    rfl
  · intro name h1 h2
    unfold moduleGetattr
    rw [if_neg (by simp [h1, h2])]

/-- `_localized_month` and `_localized_day` behave as read-only lists: lengths 13 and 7, the
empty string at month 0, negative indices count from the end, an index out of range is
`IndexError`, and `[:]` gives the whole table. January 1, 2001 is a Monday (calendar.py:117),
so `date(2001, 1, i+1)` names weekday `i`. -/
def LocalizedTables : Prop :=
  (localizedMonthList cNames.monthName).length = localizedMonthLen ∧
  (localizedMonthList cNames.monthAbbr).length = localizedMonthLen ∧
  cNames.dayName.length = localizedDayLen ∧ cNames.dayAbbr.length = localizedDayLen ∧
  localizedGet (localizedMonthList cNames.monthName) 0 = .ok [] ∧
  (∀ (tbl : List Str) (i : Int), 0 ≤ i → i < tbl.length →
    localizedGet tbl (i - tbl.length) = localizedGet tbl i) ∧
  (∀ (tbl : List Str) (i : Int), (i ≥ tbl.length ∨ i < -(tbl.length : Int)) →
    localizedGet tbl i = .error (.indexError "list index out of range")) ∧
  localizedSlice cNames.dayName none none 1 = .ok cNames.dayName ∧
  localizedSlice (localizedMonthList cNames.monthName) none none 1 =
    .ok (localizedMonthList cNames.monthName) ∧
  (∀ i : Int, 0 ≤ i → i ≤ 6 → weekday 2001 1 (i + 1) = .ok i)

theorem localizedTables_proven : LocalizedTables := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_, by decide, by decide, ?_⟩
  · intro tbl i h0 h1
    unfold localizedGet pyIndex
    simp only
    rw [if_pos (by omega : i - tbl.length < 0), if_neg (by omega : ¬ i < 0)]
    rw [show i - (tbl.length : Int) + tbl.length = i by omega]
  · intro tbl i h
    exact pyIndex_err tbl i h
  · intro i h0 h1
    have hb : daysInMonth 2001 1 = 31 := by decide
    rw [weekday_ok 2001 1 (i + 1) (by decide) (by omega)]
    have : wk 2001 1 (i + 1) = i := by
      have hw : ymd2ord 2001 1 1 = 730486 := by decide
      have := ymd2ord_day 2001 1 (i + 1)
      unfold wk
      omega
    rw [this]

end PyLean.CoreLibs.CalStat
