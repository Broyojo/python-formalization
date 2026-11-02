import PyLean.CoreLibs.CalStat.Cal

/-!
Mirror of `Lib/calendar.py` (CPython 3.15.2), second part: `TextCalendar`,
`HTMLCalendar`, `different_locale`, the locale subclasses, `_CLIDemoCalendar` and `main`.

Locale dependence is a parameter: the text methods take the `Names` table of the
current `LC_TIME` locale; `LocaleEnv` models `setlocale`. `print(x, end='')` is modelled
by the string `x` itself.
-/

namespace PyLean.CoreLibs.CalStat

open PyLean PyLean.Datetime

/-! ## class TextCalendar, calendar.py:349-466 -/

/-- `TextCalendar.formatday`, calendar.py:361-369. -/
def tFormatday (day _weekday width : Int) : Str :=
  let s := if day = 0 then [] else fmt2i day
  center s width

/-- `TextCalendar.formatweek`, calendar.py:371-375. -/
def tFormatweek (theweek : List (Int × Int)) (width : Int) : Str :=
  join [' '] (theweek.map (fun p => tFormatday p.1 p.2 width))

/-- `TextCalendar.prweek`, calendar.py:355-359. -/
def tPrweek (theweek : List (Int × Int)) (width : Int) : Str := tFormatweek theweek width

/-- `TextCalendar.formatweekday`, calendar.py:377-385. -/
def tFormatweekday (N : Names) (day width : Int) : Py Str := do
  let names := if width ≥ (N.dayName.map (fun s => (s.length : Int))).foldr max 0 then N.dayName else N.dayAbbr
  let s ← localizedGet names day
  return center (sliceTo s width) width

/-- `TextCalendar.formatweekheader`, calendar.py:387-391. -/
def tFormatweekheader (N : Names) (c : Calendar) (width : Int) : Py Str := do
  let parts ← c.iterweekdays.mapM (fun i => tFormatweekday N i width)
  return join [' '] parts

/-- `TextCalendar.formatmonthname`, calendar.py:393-402. -/
def tFormatmonthname (N : Names) (theyear themonth width : Int) (withyear : Bool) : Py Str := do
  validateMonth themonth
  let s ← localizedGet (localizedMonthList N.standaloneName) themonth
  let s ← if withyear then do
      let y ← reprInt theyear
      pure (s ++ [' '] ++ y)
    else pure s
  return center s width

/-- `TextCalendar.formatmonth`, calendar.py:410-424. -/
def tFormatmonth (N : Names) (c : Calendar) (theyear themonth w l : Int) : Py Str := do
  let w := max 2 w
  let l := max 1 l
  let s ← tFormatmonthname N theyear themonth (7 * (w + 1) - 1) true
  let s := rstrip s
  let s := s ++ nl l
  let s := s ++ rstrip (← tFormatweekheader N c w)
  let s := s ++ nl l
  let weeks ← c.monthdays2calendar theyear themonth
  return s ++ (weeks.map (fun week => rstrip (tFormatweek week w) ++ nl l)).flatten

/-- `TextCalendar.prmonth`, calendar.py:404-408. -/
def tPrmonth (N : Names) (c : Calendar) (theyear themonth w l : Int) : Py Str :=
  tFormatmonth N c theyear themonth w l

/-- The body of the height loop of `formatyear`, calendar.py:451-461; `fw` formats
a week of month column `k`. -/
def yearWeekLines (row : List (List (List (Int × Int)))) (colwidth c l : Int)
    (fw : Nat → List (Int × Int) → Str) : Str :=
  let height := (row.map List.length).foldr max 0
  ((List.range height).map (fun j =>
    let weeks := row.zipIdx.map (fun p => match p.1[j]? with
      | none => []
      | some wk => fw p.2 wk)
    rstrip (formatstring weeks colwidth c) ++ nl l)).flatten

/-- The header lines of one month row of `formatyear`, calendar.py:441-449. -/
def yearRowHead (months : List Int) (header : Str) (colwidth c l : Int) (name : Int → Py Str) : Py Str := do
  let names ← months.mapM name
  return nl l ++ rstrip (formatstring names colwidth c) ++ nl l ++
    rstrip (formatstring (months.map (fun _ => header)) colwidth c) ++ nl l

/-- `months = range(m*i+1, min(m*(i+1)+1, 13))`, calendar.py:441. -/
def textMonthRow (m i : Int) : List Int := rangeI (m * i + 1) (min (m * (i + 1) + 1) 13)

/-- One iteration of the row loop of `formatyear`, calendar.py:439-461; `p` is
`(row, i)` from `enumerate`. -/
def yearRow (m : Int) (header : Str) (colwidth c l : Int)
    (fw : List Int → Nat → List (Int × Int) → Str) (name : Int → Py Str)
    (p : List (List (List (Int × Int))) × Nat) : Py Str := do
  let months := textMonthRow m (p.2 : Int)
  let head ← yearRowHead months header colwidth c l name
  return head ++ yearWeekLines p.1 colwidth c l (fw months)

/-- `TextCalendar.formatyear`, calendar.py:426-462, with the week formatter as a
parameter `fw w months k week`, the month name as `name colwidth k`, and `wrap` for what colour adds to the year line
and to the week header, so that `_CLIDemoCalendar.formatyear`, Lib/calendar.py:768-820, can share it. -/
def tFormatyearWith (N : Names) (cal : Calendar) (theyear w l c m : Int)
    (fw : Int → List Int → Nat → List (Int × Int) → Str) (name : Int → Int → Py Str)
    (wrapYear wrapHead : Str → Str) : Py Str := do
  let w := max 2 w
  let l := max 1 l
  let c := max 2 c
  let colwidth := (w + 1) * 7 - 1
  let yr ← reprInt theyear
  let v := wrapYear (rstrip (center yr (colwidth * m + c * (m - 1)))) ++ nl l
  let header := wrapHead (← tFormatweekheader N cal w)
  let rows ← cal.yeardays2calendar theyear m
  let body ← rows.zipIdx.mapM (yearRow m header colwidth c l (fw w) (name colwidth))
  return v ++ body.flatten

def tFormatyear (N : Names) (cal : Calendar) (theyear w l c m : Int) : Py Str :=
  tFormatyearWith N cal theyear w l c m (fun w _ _ wk => tFormatweek wk w)
    (fun cw k => tFormatmonthname N theyear k cw false) id id

/-- `TextCalendar.pryear`, calendar.py:464-466. -/
def tPryear (N : Names) (cal : Calendar) (theyear w l c m : Int) : Py Str :=
  tFormatyear N cal theyear w l c m

/-! ## class HTMLCalendar, calendar.py:488-617 -/

/-- `HTMLCalendar.cssclasses`, calendar.py:475. -/
def cssclasses : List Str := ["mon", "tue", "wed", "thu", "fri", "sat", "sun"].map String.toList

/-- `HTMLCalendar.formatday`, calendar.py:495-503. -/
def hFormatday (day weekday : Int) : Py Str := do
  if day = 0 then return lit "<td class=\"noday\">&nbsp;</td>"
  else
    let cls ← pyIndex cssclasses weekday
    let d ← reprInt day
    return lit "<td class=\"" ++ cls ++ lit "\">" ++ d ++ lit "</td>"

/-- `HTMLCalendar.formatweek`, calendar.py:505-510. -/
def hFormatweek (theweek : List (Int × Int)) : Py Str := do
  let parts ← theweek.mapM (fun p => hFormatday p.1 p.2)
  return lit "<tr>" ++ parts.flatten ++ lit "</tr>"

/-- `HTMLCalendar.formatweekday`, calendar.py:512-516. -/
def hFormatweekday (N : Names) (day : Int) : Py Str := do
  let cls ← pyIndex cssclasses day
  let abbr ← localizedGet N.dayAbbr day
  return lit "<th class=\"" ++ cls ++ lit "\">" ++ abbr ++ lit "</th>"

/-- `HTMLCalendar.formatweekheader`, calendar.py:518-523. -/
def hFormatweekheader (N : Names) (c : Calendar) : Py Str := do
  let parts ← c.iterweekdays.mapM (hFormatweekday N)
  return lit "<tr>" ++ parts.flatten ++ lit "</tr>"

/-- `HTMLCalendar.formatmonthname`, calendar.py:525-534. -/
def hFormatmonthname (N : Names) (theyear themonth : Int) (withyear : Bool) : Py Str := do
  validateMonth themonth
  let name ← localizedGet (localizedMonthList N.standaloneName) themonth
  let s ← if withyear then do
      let y ← reprInt theyear
      pure (name ++ [' '] ++ y)
    else pure name
  return lit "<tr><th colspan=\"7\" class=\"month\">" ++ s ++ lit "</th></tr>"

def htmlTable (cls : String) : Str :=
  lit s!"<table class=\"{cls}\">"

/-- `HTMLCalendar.formatmonth`, calendar.py:536-553. -/
def hFormatmonth (N : Names) (c : Calendar) (theyear themonth : Int) (withyear : Bool) :
    Py Str := do
  let name ← hFormatmonthname N theyear themonth withyear
  let head ← hFormatweekheader N c
  let weeks ← c.monthdays2calendar theyear themonth
  let rows ← weeks.mapM hFormatweek
  return htmlTable "month" ++ ['\n'] ++ name ++ ['\n'] ++ head ++ ['\n'] ++
    (rows.map (· ++ ['\n'])).flatten ++ lit "</table>" ++ ['\n']

/-- `list(range(a, b, step))` for `step > 0`. -/
def rangeStep (a b step : Int) : List Int :=
  let n := if a < b then ((b - a - 1) / step + 1).toNat else 0
  (List.range n).map (fun (i : Nat) => a + (i : Int) * step)

/-- The rows of month numbers of `HTMLCalendar.formatyear`, calendar.py:565-567. -/
def htmlMonthRows (width : Int) : List (List Int) :=
  (rangeStep 1 13 width).map (fun i => rangeI i (min (i + width) 13))

/-- `HTMLCalendar.formatyear`, calendar.py:555-575. -/
def hFormatyear (N : Names) (c : Calendar) (theyear width : Int) : Py Str := do
  let width := max width 1
  let w ← reprInt width
  let y ← reprInt theyear
  let head := htmlTable "year" ++ ['\n'] ++ lit "<tr><th colspan=\"" ++ w ++
    lit "\" class=\"year\">" ++ y ++ lit "</th></tr>"
  let rows ← (htmlMonthRows width).mapM (fun months => do
    let cells ← months.mapM (fun m => do
      let t ← hFormatmonth N c theyear m false
      return lit "<td>" ++ t ++ lit "</td>")
    return lit "<tr>" ++ cells.flatten ++ lit "</tr>")
  return head ++ rows.flatten ++ lit "</table>"

/-! ### `str.encode(encoding, "xmlcharrefreplace")` -/

/-- The codecs the model knows; any other name is a `LookupError`. Normalization of
codec names is not modelled, so the difftest only passes the canonical spellings. -/
inductive Codec | utf8 | ascii | latin1
  deriving DecidableEq

def codecOf (encoding : Str) : Py Codec :=
  match String.ofList encoding with
  | "utf-8" => .ok .utf8
  | "ascii" => .ok .ascii
  | "latin-1" => .ok .latin1
  | e => .error (.named "LookupError" s!"unknown encoding: {e}")

def Codec.limit : Codec → Nat
  | .utf8 => 0x110000
  | .ascii => 128
  | .latin1 => 256

def utf8Bytes (c : Char) : List Nat := (String.singleton c).toUTF8.toList.map UInt8.toNat

/-- The bytes of one code point in a codec, or `xmlcharrefreplace`'s `&#N;`. -/
def encodeChar (k : Codec) (c : Char) : List Nat :=
  if c.toNat < k.limit then
    match k with
    | .utf8 => utf8Bytes c
    | _ => [c.toNat]
  else (lit "&#" ++ Nat.toDigits 10 c.toNat ++ [';']).map Char.toNat

def encodeXml (k : Codec) (s : Str) : List Nat := s.flatMap (encodeChar k)

/-- `HTMLCalendar._format_html_page`, calendar.py:577-604. `encoding = None` becomes `'utf-8'`, and `content` was
computed by the caller, so its exception comes first. -/
def hFormatPage (theyear : Int) (content : Str) (css : Option Str) (encoding : Option Str) : Py (List Nat) := do
  let encoding := encoding.getD (lit "utf-8")
  let y ← reprInt theyear
  let page := lit "<!DOCTYPE html>\n" ++ lit "<html lang=\"en\">\n" ++ lit "<head>\n" ++
    lit "<meta charset=\"" ++ encoding ++ lit "\">\n" ++
    lit "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n" ++
    lit "<title>Calendar for " ++ y ++ lit "</title>\n" ++ lit "<style>\n" ++
    lit ":root { color-scheme: light dark; }\n" ++ lit "table.year { border: solid; }\n" ++
    lit "table.year > tbody > tr > td { border: solid; vertical-align: top; }\n" ++ lit "</style>\n" ++
    (match css with
     | some css => lit "<link rel=\"stylesheet\" href=\"" ++ css ++ lit "\">\n"
     | none => []) ++
    lit "</head>\n" ++ lit "<body>\n" ++ content ++ lit "</body>\n" ++ lit "</html>\n"
  let k ← codecOf encoding
  return encodeXml k page

/-- `HTMLCalendar.formatyearpage`, calendar.py:606-611. -/
def hFormatyearpage (N : Names) (c : Calendar) (theyear width : Int) (css : Option Str)
    (encoding : Option Str) : Py (List Nat) := do
  hFormatPage theyear (← hFormatyear N c theyear width) css encoding

/-- `HTMLCalendar.formatmonthpage`, calendar.py:613-618. -/
def hFormatmonthpage (N : Names) (c : Calendar) (theyear themonth : Int) (css : Option Str)
    (encoding : Option Str) : Py (List Nat) := do
  hFormatPage theyear (← hFormatmonth N c theyear themonth true) css encoding

/-! ## `different_locale` and the locale calendars, calendar.py:620-681 -/

/-- The process `LC_TIME` state and what the C library offers. -/
structure LocaleEnv where
  /-- `setlocale(LC_TIME, None)`. -/
  current : String
  /-- What `setlocale(LC_TIME, "")` selects from the environment. -/
  userDefault : String
  supported : String → Bool
  names : String → Names

/-- `locale.setlocale(LC_TIME, name)`, Modules/_localemodule.c `_locale_setlocale_impl`. -/
def setlocale (e : LocaleEnv) (name : String) : Py LocaleEnv :=
  let t := if name = "" then e.userDefault else name
  if e.supported t then .ok { e with current := t }
  else .error (.named "Error" "unsupported locale setting")

/-- `with different_locale(locale): body`, calendar.py:620-630:
`__enter__` saves the locale and switches, `__exit__` restores it whatever the
body did. An exception from `__enter__` skips both the body and `__exit__`. -/
def withDifferentLocale {α : Type} (e : LocaleEnv) (locale : String) (body : LocaleEnv → Py α) :
    Py α × LocaleEnv :=
  let old := e.current
  match setlocale e locale with
  | .error x => (.error x, e)
  | .ok e' =>
    let r := body e'
    match setlocale e' old with
    | .error x => (.error x, e')
    | .ok e'' => (r, e'')

/-- `_get_default_locale`, calendar.py:633-640. -/
def getDefaultLocale (e : LocaleEnv) : Py String :=
  if e.current = "C" then
    (withDifferentLocale e "" (fun e' => .ok e'.current)).1
  else .ok e.current

/-- `LocaleTextCalendar.__init__`/`LocaleHTMLCalendar.__init__`, the `locale` attribute,
calendar.py:649-653 and :669-673. -/
def initLocale (e : LocaleEnv) (locale : Option String) : Py String :=
  match locale with
  | some l => .ok l
  | none => getDefaultLocale e

/-- `LocaleTextCalendar.formatweekday`, calendar.py:655-657. -/
def ltFormatweekday (e : LocaleEnv) (locale : String) (day width : Int) : Py Str × LocaleEnv :=
  withDifferentLocale e locale (fun e' => tFormatweekday (e'.names e'.current) day width)

/-- `LocaleTextCalendar.formatmonthname`, calendar.py:659-661. -/
def ltFormatmonthname (e : LocaleEnv) (locale : String) (theyear themonth width : Int)
    (withyear : Bool) : Py Str × LocaleEnv :=
  withDifferentLocale e locale
    (fun e' => tFormatmonthname (e'.names e'.current) theyear themonth width withyear)

/-- `LocaleHTMLCalendar.formatweekday`, calendar.py:675-677. -/
def lhFormatweekday (e : LocaleEnv) (locale : String) (day : Int) : Py Str × LocaleEnv :=
  withDifferentLocale e locale (fun e' => hFormatweekday (e'.names e'.current) day)

/-- `LocaleHTMLCalendar.formatmonthname`, calendar.py:679-681. -/
def lhFormatmonthname (e : LocaleEnv) (locale : String) (theyear themonth : Int)
    (withyear : Bool) : Py Str × LocaleEnv :=
  withDifferentLocale e locale
    (fun e' => hFormatmonthname (e'.names e'.current) theyear themonth withyear)

/-! ## `_CLIDemoCalendar`, calendar.py:684-826 -/

/-- `_get_theme().calendar`, Lib/calendar.py:689-692 and Lib/_colorize.py:202-206; all empty when colour is off. -/
structure Ansi where
  header : Str
  highlight : Str
  weekday : Str
  reset : Str

/-- `_CLIDemoCalendar.__init__` keeps `highlight_day`, a `date` or `None`
(:685-687); `_CLIDemoLocaleCalendar.__init__` does the same (:824-826). -/
abbrev Highlight := Option Date

/-- `_CLIDemoCalendar.formatday`, calendar.py:694-705. `day == highlight_day` is a plain comparison, so a blank cell,
`day = 0`, is coloured when `highlight_day` is `0`. -/
def dFormatday (A : Ansi) (day weekday width : Int) (highlightDay : Option Int) : Str :=
  let s := tFormatday day weekday width
  if some day = highlightDay then A.highlight ++ s ++ A.reset else s

/-- `_CLIDemoCalendar.formatweek`, calendar.py:707-714. -/
def dFormatweek (A : Ansi) (theweek : List (Int × Int)) (width : Int)
    (highlightDay : Option Int) : Str :=
  join [' '] (theweek.map (fun p => dFormatday A p.1 p.2 width highlightDay))

/-- `_CLIDemoCalendar.formatweekheader`, calendar.py:716-722. -/
def dFormatweekheader (A : Ansi) (N : Names) (c : Calendar) (width : Int) : Py Str := do
  let header ← tFormatweekheader N c width
  return A.weekday ++ header ++ A.reset

/-- `name.strip()` and what is around it. -/
def stripParts (s : Str) : Str × Str × Str :=
  let lead := s.takeWhile isSpaceChar
  let rest := s.dropWhile isSpaceChar
  let core := rstrip rest
  (lead, core, rest.drop core.length)

/-- `_CLIDemoCalendar.formatmonthname`, calendar.py:724-742. `name.replace(name_only, colored_name, 1)` finds the
stripped name just after the leading spaces; an empty one matches at the very start. -/
def dFormatmonthname (A : Ansi) (N : Names) (hl : Highlight) (theyear themonth width : Int) (withyear : Bool) :
    Py Str := do
  let name ← tFormatmonthname N theyear themonth width withyear
  let here := match hl with
    | some (y, m, _) => decide (y = theyear) && decide (m = themonth)
    | none => false
  if here then
    let (lead, core, trail) := stripParts name
    if core.isEmpty then return A.highlight ++ A.reset ++ name
    return lead ++ A.highlight ++ core ++ A.reset ++ trail
  else return A.header ++ name ++ A.reset

/-- The `highlight_day` choice at calendar.py:748-755. -/
def monthHighlight (hl : Highlight) (theyear themonth : Int) : Option Int :=
  match hl with
  | some (y, m, d) => if y = theyear ∧ m = themonth then some d else none
  | none => none

/-- `_CLIDemoCalendar.formatmonth`, calendar.py:744-766. -/
def dFormatmonth (A : Ansi) (N : Names) (c : Calendar) (hl : Highlight) (theyear themonth w l : Int) :
    Py Str := do
  let highlightDay := monthHighlight hl theyear themonth
  let w := max 2 w
  let l := max 1 l
  let s ← dFormatmonthname A N hl theyear themonth (7 * (w + 1) - 1) true
  let s := rstrip s
  let s := s ++ nl l
  let s := s ++ rstrip (← dFormatweekheader A N c w)
  let s := s ++ nl l
  let weeks ← c.monthdays2calendar theyear themonth
  return s ++ (weeks.map (fun week => rstrip (dFormatweek A week w highlightDay) ++ nl l)).flatten

/-- `month_pos` and the day passed to `formatweek` for column `k`, calendar.py:795-817. -/
def dYearDay (hl : Highlight) (theyear : Int) (months : List Int) (k : Nat) : Option Int :=
  match hl with
  | some (y, mo, d) =>
    if y = theyear ∧ mo ∈ months then
      if months.idxOf mo = k then some d else none
    else none
  | none => none

/-- `_CLIDemoCalendar.formatyear`, calendar.py:768-820. -/
def dFormatyear (A : Ansi) (N : Names) (cal : Calendar) (hl : Highlight) (theyear w l c m : Int) :
    Py Str :=
  tFormatyearWith N cal theyear w l c m
    (fun w months k wk => dFormatweek A wk w (dYearDay hl theyear months k))
    (fun cw k => dFormatmonthname A N hl theyear k cw false)
    (fun year => A.header ++ year ++ A.reset) (fun header => A.weekday ++ header ++ A.reset)

/-! ## `main`, calendar.py:879-993 -/

/-- What `parser.parse_args(args)` leaves in `options`, calendar.py:943 (`argparse` itself
is another module). -/
structure Options where
  width : Int := 2
  lines : Int := 1
  spacing : Int := 6
  months : Int := 3
  css : Str := lit "calendar.css"
  locale : Option Str := none
  encoding : Option Str := none
  type : Str := lit "text"
  firstWeekday : Int := 0
  year : Option Int := none
  month : Option Int := none

/-- `parser.error(...)`: `SystemExit` with status 2. -/
def parserError : PyExc := .named "SystemExit" "2"

/-- Python truthiness of an optional string. -/
def strTruthy : Option Str → Bool
  | some s => !s.isEmpty
  | none => false

/-- What `main` writes: text to `sys.stdout`, or bytes to `sys.stdout.buffer`. -/
inductive MainOut where
  | text (s : Str)
  | bytes (b : List Nat)
  deriving DecidableEq, Repr

/-- `result.encode(encoding)` (strict). -/
def encodeStrict (encoding : Str) (s : Str) : Py (List Nat) := do
  let k ← codecOf encoding
  if s.all (fun c => c.toNat < k.limit) then return encodeXml k s
  else .error (.named "UnicodeEncodeError" "~unencodable")

/-- `main` after argument parsing, calendar.py:945-993. `N` is the table of the
locale selected by `--locale` (the C table without one), `today` is `date.today()`. -/
def mainRun (A : Ansi) (N : Names) (today : Date) (o : Options) : Py MainOut := do
  if strTruthy o.locale && !strTruthy o.encoding then throw parserError
  if o.type = lit "html" then
    let cal := (Calendar.mk 0).setfirstweekday o.firstWeekday
    let encoding := o.encoding.getD (lit "utf-8")
    match o.year with
    | none => return .bytes (← hFormatyearpage N cal today.1 3 (some o.css) (some encoding))
    | some y =>
      match o.month with
      | some mo =>
        if mo != 0 then return .bytes (← hFormatmonthpage N cal y mo (some o.css) (some encoding))
        else return .bytes (← hFormatyearpage N cal y 3 (some o.css) (some encoding))
      | none => return .bytes (← hFormatyearpage N cal y 3 (some o.css) (some encoding))
  else
    let cal := (Calendar.mk 0).setfirstweekday o.firstWeekday
    let hl : Highlight := some today
    match o.month with
    | some mo => validateMonth mo
    | none => pure ()
    let result ← match o.year, o.month with
      | none, some _ =>
        -- `formatyear(today.year, w=..., l=...)`: c and m keep their defaults
        dFormatyear A N cal hl today.1 o.width o.lines 6 3
      | none, none => dFormatyear A N cal hl today.1 o.width o.lines o.spacing o.months
      | some y, none => dFormatyear A N cal hl y o.width o.lines o.spacing o.months
      | some y, some mo => dFormatmonth A N cal hl y mo o.width o.lines
    if strTruthy o.encoding then return .bytes (← encodeStrict (o.encoding.getD []) result)
    return .text result

end PyLean.CoreLibs.CalStat
