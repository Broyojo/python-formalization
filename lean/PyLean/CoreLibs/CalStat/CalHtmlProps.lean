import PyLean.CoreLibs.CalStat.CalMiscProps

/-!
The exact text of the calendar formatters, for any locale table with the right lengths: which name is picked, which class
a cell gets, and what surrounds each part. The width and line-count theorems in CalFmtProps.lean and CalMiscProps.lean hold for
any text of that shape, and these do not.
-/

namespace PyLean.CoreLibs.CalStat

open PyLean PyLean.Datetime

theorem pyIndex_nat {α : Type} (l : List α) (k : Nat) (h : k < l.length) : pyIndex l (k : Int) = .ok l[k] := by
  unfold pyIndex
  simp only
  rw [if_neg (by omega), if_neg (by omega)]
  simp [h]

theorem pyIndex_month (N : Names) (hN : N.WellFormed) (m : Int) (hm : 1 ≤ m ∧ m ≤ 12) :
    pyIndex (localizedMonthList N.standaloneName) m = .ok (N.standaloneName.getD (m - 1).toNat []) := by
  have hl : N.standaloneName.length = 12 := hN.2.2.2
  obtain ⟨k, rfl⟩ : ∃ k : Nat, m = ((k + 1 : Nat) : Int) := ⟨(m - 1).toNat, by omega⟩
  have h1 := pyIndex_nat (localizedMonthList N.standaloneName) (k + 1) (by simp [localizedMonthList]; omega)
  have hk : k < N.standaloneName.length := by omega
  have e : ((((k + 1 : Nat) : Int) - 1).toNat) = k := by omega
  rw [h1, e]
  simp [localizedMonthList, List.getD_eq_getElem?_getD, hk]

/-- `TextCalendar.formatweekday`: the full name when `width` holds the longest one, and the abbreviation otherwise, cut to
`width` and centred, for any table of seven names; a day past the end of the table is an `IndexError`. -/
def TextWeekdayExact : Prop :=
  ∀ (N : Names) (k : Nat) (w : Int) (hk : k < 7) (hN : N.WellFormed),
    (w ≥ (N.dayName.map (fun s => (s.length : Int))).foldr max 0 →
      tFormatweekday N k w = .ok (center (sliceTo (N.dayName[k]'(by rw [hN.1]; exact hk)) w) w)) ∧
    (w < (N.dayName.map (fun s => (s.length : Int))).foldr max 0 →
      tFormatweekday N k w = .ok (center (sliceTo (N.dayAbbr[k]'(by rw [hN.2.1]; exact hk)) w) w))

theorem textWeekdayExact_proven : TextWeekdayExact := by
  intro N k w hk hN
  constructor
  · intro h
    have hi := pyIndex_nat N.dayName k (by rw [hN.1]; exact hk)
    simp only [tFormatweekday, localizedGet, h, ite_true, bind, Except.bind, hi, pure, Except.pure]
  · intro h
    have hi := pyIndex_nat N.dayAbbr k (by rw [hN.2.1]; exact hk)
    have h' : ¬w ≥ (N.dayName.map (fun s => (s.length : Int))).foldr max 0 := by omega
    simp only [tFormatweekday, localizedGet, h', ite_false, bind, Except.bind, hi, pure, Except.pure]

/-- Both `formatmonthname`: the standalone name of that month, with `' '` and the year when `withyear`. The text one
centres it and the HTML one puts it in the month heading. -/
def MonthNameExact : Prop :=
  ∀ (N : Names) (y m w : Int) (r : Str), N.WellFormed → (1 ≤ m ∧ m ≤ 12) → reprInt y = .ok r →
    let name := N.standaloneName.getD (m - 1).toNat []
    tFormatmonthname N y m w true = .ok (center (name ++ [' '] ++ r) w) ∧
    tFormatmonthname N y m w false = .ok (center name w) ∧
    hFormatmonthname N y m true = .ok (lit "<tr><th colspan=\"7\" class=\"month\">" ++ (name ++ [' '] ++ r) ++ lit "</th></tr>") ∧
    hFormatmonthname N y m false = .ok (lit "<tr><th colspan=\"7\" class=\"month\">" ++ name ++ lit "</th></tr>")

theorem monthNameExact_proven : MonthNameExact := by
  intro N y m w r hN hm hr
  have hi := pyIndex_month N hN m hm
  simp only [tFormatmonthname, hFormatmonthname, localizedGet, validateMonth_ok m hm, hi, hr, bind, Except.bind, pure,
    Except.pure, Bool.false_eq_true, ite_false, ite_true, and_self]

/-- The cells of `HTMLCalendar`: a day outside the month is the `noday` cell whatever its weekday, a day is a cell with the
class of its weekday and its number, and a weekday past the table is an `IndexError`. A week is its cells in order, and
the header is the abbreviations in the order of `iterweekdays`. -/
def HtmlCellsExact : Prop :=
  ∀ (N : Names) (c : Calendar) (d wd : Int) (k : Nat) (r : Str) (hk : k < 7) (hN : N.WellFormed)
    (week : List (Int × Int)) (cells : List Str) (heads : List Str),
    hFormatday 0 wd = .ok (lit "<td class=\"noday\">&nbsp;</td>") ∧
    (d ≠ 0 → reprInt d = .ok r →
      hFormatday d k = .ok (lit "<td class=\"" ++ cssclasses.getD k [] ++ lit "\">" ++ r ++ lit "</td>")) ∧
    (d ≠ 0 → 7 ≤ wd → wd < 2 ^ 63 → hFormatday d wd = .error (.indexError "list index out of range")) ∧
    hFormatweekday N k =
      .ok (lit "<th class=\"" ++ cssclasses.getD k [] ++ lit "\">" ++ N.dayAbbr[k]'(by rw [hN.2.1]; exact hk) ++ lit "</th>") ∧
    (week.mapM (fun p => hFormatday p.1 p.2) = .ok cells → hFormatweek week = .ok (lit "<tr>" ++ cells.flatten ++ lit "</tr>")) ∧
    (c.iterweekdays.mapM (hFormatweekday N) = .ok heads →
      hFormatweekheader N c = .ok (lit "<tr>" ++ heads.flatten ++ lit "</tr>"))

theorem css_index (k : Nat) (hk : k < 7) : pyIndex cssclasses (k : Int) = .ok (cssclasses.getD k []) := by
  have hl : cssclasses.length = 7 := by decide
  rw [pyIndex_nat cssclasses k (by omega)]
  simp [List.getD_eq_getElem?_getD, hl, hk]

theorem htmlCellsExact_proven : HtmlCellsExact := by
  intro N c d wd k r hk hN week cells heads
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0 hr
    simp [hFormatday, h0, css_index k hk, hr, bind, Except.bind, pure, Except.pure]
  · intro h0 h7 hb
    have hl : (cssclasses.length : Int) = 7 := by decide
    have e : pyIndex cssclasses wd = .error (.indexError "list index out of range") := by
      unfold pyIndex
      simp only
      have h1 : ¬wd < 0 := by omega
      rw [if_neg h1, if_pos (by omega), if_neg (by omega)]
    simp [hFormatday, h0, e, bind, Except.bind]
  · have hi := pyIndex_nat N.dayAbbr k (by rw [hN.2.1]; exact hk)
    simp only [hFormatweekday, localizedGet, css_index k hk, hi, bind, Except.bind, pure, Except.pure]
  · intro h
    simp only [hFormatweek, h, bind, Except.bind, pure, Except.pure]
  · intro h
    simp only [hFormatweekheader, h, bind, Except.bind, pure, Except.pure]

/-- `HTMLCalendar.formatmonth`: the table, its name row, its header row and the rows of `monthdays2calendar`, each on a line
of its own, and the first failure in that order. -/
def HtmlMonthExact : Prop :=
  ∀ (N : Names) (c : Calendar) (y m : Int) (wy : Bool) (name head : Str) (weeks : List (List (Int × Int)))
    (rows : List Str) (e : PyExc),
    (hFormatmonthname N y m wy = .ok name → hFormatweekheader N c = .ok head → c.monthdays2calendar y m = .ok weeks →
      weeks.mapM hFormatweek = .ok rows →
      hFormatmonth N c y m wy = .ok (lit "<table class=\"month\">" ++ ['\n'] ++ name ++ ['\n'] ++ head ++ ['\n'] ++
        (rows.map (· ++ ['\n'])).flatten ++ lit "</table>" ++ ['\n'])) ∧
    (hFormatmonthname N y m wy = .error e → hFormatmonth N c y m wy = .error e) ∧
    (hFormatmonthname N y m wy = .ok name → hFormatweekheader N c = .error e → hFormatmonth N c y m wy = .error e)

theorem htmlMonthExact_proven : HtmlMonthExact := by
  intro N c y m wy name head weeks rows e
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2 h3 h4
    simp only [hFormatmonth, h1, h2, h3, h4, bind, Except.bind, pure, Except.pure, htmlTable]
    rfl
  · intro h
    simp [hFormatmonth, h, bind, Except.bind]
  · intro h1 h2
    simp [hFormatmonth, h1, h2, bind, Except.bind]

/-- `HTMLCalendar.formatyear`: a `width` below one counts as one, the heading spans that many columns, and each row of
`htmlMonthRows` is a row of cells that hold the month tables, without the year. -/
def HtmlYearExact : Prop :=
  ∀ (N : Names) (c : Calendar) (y width : Int) (w ys : Str) (rows : List Str),
    reprInt (max width 1) = .ok w → reprInt y = .ok ys →
    (htmlMonthRows (max width 1)).mapM (fun months => do
      let cells ← months.mapM (fun m => do
        let t ← hFormatmonth N c y m false
        return lit "<td>" ++ t ++ lit "</td>")
      return lit "<tr>" ++ cells.flatten ++ lit "</tr>") = .ok rows →
    hFormatyear N c y width =
      .ok (lit "<table class=\"year\">" ++ ['\n'] ++ lit "<tr><th colspan=\"" ++ w ++ lit "\" class=\"year\">" ++ ys ++
        lit "</th></tr>" ++ rows.flatten ++ lit "</table>")

theorem htmlYearExact_proven : HtmlYearExact := by
  intro N c y width w ys rows h1 h2 h3
  simp only [hFormatyear, h1, h2, bind, Except.bind, pure, Except.pure, htmlTable]
  simp only [bind, Except.bind, pure, Except.pure] at h3
  rw [h3]
  rfl

/-- `HTMLCalendar._format_html_page`: the content sits in the body of the page, the stylesheet line is there exactly when
`css` is given, `None` means UTF-8, an unknown encoding is a `LookupError`, and both pages are this page around their own
content, where the month page uses a month with its year. -/
def HtmlPageExact : Prop :=
  ∀ (N : Names) (c : Calendar) (y m width : Int) (content ys e cs : Str) (css : Option Str) (enc : Option Str)
    (k : Codec) (x : PyExc),
    reprInt y = .ok ys →
    htmlPageText ys e none content =
      htmlPageHead ys e ++ lit "</head>\n" ++ lit "<body>\n" ++ content ++ lit "</body>\n" ++ lit "</html>\n" ∧
    htmlPageText ys e (some cs) content =
      htmlPageHead ys e ++ lit "<link rel=\"stylesheet\" href=\"" ++ cs ++ lit "\">\n" ++ lit "</head>\n" ++ lit "<body>\n" ++
        content ++ lit "</body>\n" ++ lit "</html>\n" ∧
    (codecOf e = .ok k → hFormatPage y content css (some e) = .ok (encodeXml k (htmlPageText ys e css content))) ∧
    (codecOf e = .error x → hFormatPage y content css (some e) = .error x) ∧
    hFormatPage y content css none = hFormatPage y content css (some (lit "utf-8")) ∧
    (hFormatyear N c y width = .ok content →
      hFormatyearpage N c y width css enc = hFormatPage y content css enc) ∧
    (hFormatmonth N c y m true = .ok content →
      hFormatmonthpage N c y m css enc = hFormatPage y content css enc) ∧
    (hFormatyear N c y width = .error x → hFormatyearpage N c y width css enc = .error x) ∧
    (hFormatmonth N c y m true = .error x → hFormatmonthpage N c y m css enc = .error x)

theorem htmlPageExact_proven : HtmlPageExact := by
  intro N c y m width content ys e cs css enc k x hy
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · simp [htmlPageText, List.append_assoc]
  · simp [htmlPageText, List.append_assoc]
  · intro h
    simp only [hFormatPage, hy, h, bind, Except.bind, pure, Except.pure, Option.getD_some]
  · intro h
    simp only [hFormatPage, hy, h, bind, Except.bind, pure, Except.pure, Option.getD_some]
  · intro h
    simp only [hFormatyearpage, h, bind, Except.bind]
  · intro h
    simp only [hFormatmonthpage, h, bind, Except.bind]
  · intro h
    simp only [hFormatyearpage, h, bind, Except.bind]
  · intro h
    simp only [hFormatmonthpage, h, bind, Except.bind]

/-- A week of `_CLIDemoCalendar`: the cells of `TextCalendar`, joined by one space, with the highlighted day wrapped and no
other, and `TextCalendar.formatday` is the number right-aligned to two columns and centred. -/
def DemoWeekExact : Prop :=
  ∀ (A : Ansi) (week : List (Int × Int)) (w d wd : Int) (hd : Option Int),
    dFormatweek A week w hd = join [' '] (week.map (fun p =>
      if some p.1 = hd then A.highlight ++ tFormatday p.1 p.2 w ++ A.reset else tFormatday p.1 p.2 w)) ∧
    tFormatday 0 wd w = center [] w ∧
    (d ≠ 0 → tFormatday d wd w = center (fmt2i d) w) ∧
    tFormatweek week w = join [' '] (week.map (fun p => tFormatday p.1 p.2 w))

theorem demoWeekExact_proven : DemoWeekExact := by
  intro A week w d wd hd
  refine ⟨rfl, rfl, ?_, rfl⟩
  intro h
  simp [tFormatday, h]

end PyLean.CoreLibs.CalStat
