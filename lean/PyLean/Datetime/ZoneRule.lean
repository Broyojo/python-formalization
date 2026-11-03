import PyLean.Datetime.ZoneTzif
import PyLean.Datetime.Calendar

/-!
# POSIX TZ rules of `zoneinfo` (CPython 3.15.2), both twins

* the transition-date rules: Python `_DayOffset`/`_CalendarOffset`
  (Lib/zoneinfo/_zoneinfo.py:514-624), C `DayRule`/`CalendarRule`
  (Modules/_zoneinfo.c:1310-1482);
* the lookups after the last transition: Python `_TZStr` (:425-511), C `find_tzrule_ttinfo`
  and `find_tzrule_ttinfo_fromutc` (:1484-1598);
* the TZ string parsers: Python `_parse_tz_str` and its helpers (:627-779), regular
  expressions over text; C `parse_tz_str` and its helpers (:1600-1989), a pointer walk over a
  NUL-terminated `char *`.

C integer storage (`uint8_t`, `int8_t`, `int16_t`, `int`) is modelled with explicit wraps.
CPython is built with `-fwrapv`, so signed overflow wraps.

The year these functions get is `dt.year` of a `datetime` (C: `PyDateTime_GET_YEAR`), so it
lies in 1..9999; the C arithmetic in `ymd_to_ord` cannot overflow there.
-/

namespace PyLean.Datetime.Zone

open PyLean PyLean.Datetime

/-! ### C integer conversions -/

/-- Conversion to a signed `bits`-bit C integer (two's complement). -/
def wrapS (bits : Nat) (x : Int) : Int :=
  let m : Int := 2 ^ bits
  let r := x % m
  if r ≥ 2 ^ (bits - 1) then r - m else r

/-- Conversion to an unsigned `bits`-bit C integer. -/
def wrapU (bits : Nat) (x : Int) : Int := x % (2 ^ bits : Int)

def wrap64 (x : Int) : Int := wrapS 64 x
def wrap32 (x : Int) : Int := wrapS 32 x

/-! ### Values -/

/-- A `_ttinfo`: Python Lib/zoneinfo/_zoneinfo.py:400-413, C Modules/_zoneinfo.c:29-34. The two
offsets are the timedeltas' values in seconds (C keeps `utcoff_seconds` too, equal to `utcoff`
since both come from the same `long`); `tzname` is the abbreviation's UTF-8 bytes. -/
structure TTI where
  utcoff : Int
  dstoff : Int
  tzname : Bytes
  deriving Repr, DecidableEq, Inhabited

/-- C `ttinfo_eq`, Modules/_zoneinfo.c:933-953, over its three `PyObject_RichCompareBool`
results (`-1` error, `0`, `1`), in the order it makes them: `utcoff`, then `dstoff`, then
`tzname`, each made only when the one before gave `1` (`rv < 1` jumps to `end`). -/
def ttinfoEqWithC (cu cd cn : Unit → Int) : Int :=
  let rv := cu ()
  if rv < 1 then rv
  else
    let rv := cd ()
    if rv < 1 then rv
    else cn ()

/-- `_ttinfo.__eq__`, Lib/zoneinfo/_zoneinfo.py:408-413: `self.utcoff == other.utcoff and
self.dstoff == other.dstoff and self.tzname == other.tzname`, left to right, stopping at the
first false operand. Each operand is the truth of that comparison in a monad `m` (for `Py`,
the comparison or its `bool()` may raise). -/
def ttinfoEqWithPy {m : Type → Type} [Monad m] (pu pd pn : m Bool) : m Bool := do
  if !(← pu) then return false
  if !(← pd) then return false
  pn

/-- `ttinfo_eq` on two `_ttinfo`s: the fields are two `timedelta`s and a `str`, whose
comparisons cannot fail. -/
def ttiEqC (a b : TTI) : Int :=
  ttinfoEqWithC (fun _ => if a.utcoff = b.utcoff then 1 else 0)
    (fun _ => if a.dstoff = b.dstoff then 1 else 0)
    (fun _ => if a.tzname = b.tzname then 1 else 0)

/-- `_ttinfo.__eq__` on two `_ttinfo`s (comparisons that cannot fail: the identity monad). -/
def ttiEqPy (a b : TTI) : Bool :=
  ttinfoEqWithPy (m := Id) (pure (decide (a.utcoff = b.utcoff))) (pure (decide (a.dstoff = b.dstoff)))
    (pure (decide (a.tzname = b.tzname)))

/-- A transition-date rule, with the fields as stored. -/
inductive TRule where
  /-- `Mm.w.d/time`: Python `_CalendarOffset` (:547-581), C `CalendarRule` (:68-76). -/
  | cal (m w d h mi s : Int)
  /-- `Jn/time` (julian) or `n/time`: Python `_DayOffset` (:520-532), C `DayRule` (:78-85). -/
  | day (julian : Bool) (d h mi s : Int)
  deriving Repr, DecidableEq, Inhabited

def EPOCHORDINAL : Int := 719163

/-! ### Python rule dates -/

/-- `_post_epoch_days_before_year`, _zoneinfo.py:514-517. -/
def postEpochDaysBeforeYear (year : Int) : Int :=
  let y := year - 1
  y * 365 + y / 4 - y / 100 + y / 400 - EPOCHORDINAL

/-- `calendar.weekday(year, month, day)`, Lib/calendar.py:175-179: years outside 1..9999 are
moved by whole 400-year cycles, then `date.weekday()` (`(toordinal() + 6) % 7`). -/
def calWeekday (year month day : Int) : Int :=
  let year := if 1 ≤ year ∧ year ≤ 9999 then year else 2000 + year % 400
  (ymd2ord year month day + 6) % 7

/-- `calendar.monthrange(year, month)`, Lib/calendar.py:186-192, for a month in 1..12 (the
`_CalendarOffset` constructor checked it, so `_validate_month` passes). `mdays` (:90). -/
def monthrange (year month : Int) : Int × Int :=
  (calWeekday year month 1, daysInMonthTable month + (if month = 2 ∧ isLeap year then 1 else 0))

/-- `_CalendarOffset._ymd2ord`, _zoneinfo.py:583-590 (`_DAYS_BEFORE_MONTH`, :550-564). -/
def calYmd2ordPy (year month day : Int) : Int :=
  postEpochDaysBeforeYear year + daysBeforeMonthTable month +
    (if month > 2 ∧ isLeap year then 1 else 0) + day

/-- The day of the month in `_CalendarOffset.year_to_epoch`, _zoneinfo.py:609-619. -/
def calMonthDayPy (firstDay dim d w : Int) : Int :=
  let monthDay := (d - (firstDay + 1)) % 7 + 1
  let monthDay := monthDay + (w - 1) * 7
  if monthDay > dim then monthDay - 7 else monthDay

/-- `_CalendarOffset.year_to_epoch`, _zoneinfo.py:593-624. -/
def calYearToEpochPy (m w d hour minute second year : Int) : Int :=
  let (firstDay, dim) := monthrange year m
  let monthDay := calMonthDayPy firstDay dim d w
  let ordinal := calYmd2ordPy year m monthDay
  ordinal * 86400 + (hour * 3600 + minute * 60 + second)

/-- `_DayOffset.year_to_epoch`, _zoneinfo.py:534-544. -/
def dayYearToEpochPy (julian : Bool) (d hour minute second year : Int) : Int :=
  let daysBeforeYear := postEpochDaysBeforeYear year
  let d := if julian ∧ d ≥ 60 ∧ isLeap year then d + 1 else d
  let epoch := (daysBeforeYear + d) * 86400
  epoch + (hour * 3600 + minute * 60 + second)

def TRule.yearToEpochPy : TRule → Int → Int
  | .cal m w d h mi s, year => calYearToEpochPy m w d h mi s year
  | .day j d h mi s, year => dayYearToEpochPy j d h mi s year

/-! ### C rule dates -/

/-- C `is_leap_year`, :2257-2262 (on the `unsigned int` of the year). -/
def isLeapC (year : Int) : Bool :=
  let a := wrapU 32 year
  a % 4 == 0 && (a % 100 != 0 || a % 400 == 0)

/-- C `ymd_to_ord`, :2265-2276 (`int` arithmetic, truncating division; no overflow for the
years 1..9999 it gets). -/
def ymdToOrdZ (y m d : Int) : Int :=
  let y := y - 1
  let daysBeforeYear := y * 365 + y.tdiv 4 - y.tdiv 100 + y.tdiv 400
  let yearday := daysBeforeMonthTable m + (if m > 2 ∧ isLeapC (y + 1) then 1 else 0)
  daysBeforeYear + yearday + d

/-- The day of the month in C `calendarrule_year_to_timestamp`, :1335-1350, with its
`int8_t month_day`. -/
def calMonthDayC (firstDay dim day week : Int) : Int :=
  let monthDay := wrapS 8 ((wrapS 8 day - (firstDay + 1)).tmod 7)
  let monthDay := if monthDay < 0 then wrapS 8 (monthDay + 7) else monthDay
  let monthDay := wrapS 8 (monthDay + 1)
  let monthDay := wrapS 8 (monthDay + (wrapS 8 week - 1) * 7)
  if monthDay > dim then wrapS 8 (monthDay - 7) else monthDay

/-- C `calendarrule_year_to_timestamp`, :1311-1355, with its `int8_t first_day` and
`uint8_t days_in_month`. -/
def calYearToTsC (month week day hour minute second : Int) (year : Int) : Int :=
  let firstDay := wrapS 8 ((ymdToOrdZ year month 1 + 6).tmod 7)
  let dim0 := wrapU 8 (daysInMonthTable month)
  let dim := if month = 2 ∧ isLeapC year then wrapU 8 (dim0 + 1) else dim0
  let monthDay := calMonthDayC firstDay dim day week
  let ordinal := ymdToOrdZ year month monthDay - EPOCHORDINAL
  wrap64 (ordinal * 86400 + hour * 3600 + minute * 60 + second)

/-- C `dayrule_year_to_timestamp`, :1411-1445 (`uint16_t day`). -/
def dayYearToTsC (julian : Bool) (day hour minute second : Int) (year : Int) : Int :=
  let daysBeforeYear := ymdToOrdZ year 1 1 - EPOCHORDINAL - 1
  let day := if julian ∧ day ≥ 60 ∧ isLeapC year then wrapU 16 (day + 1) else day
  wrap64 ((daysBeforeYear + day) * 86400 + hour * 3600 + minute * 60 + second)

def TRule.yearToTsC : TRule → Int → Int
  | .cal m w d h mi s, year => calYearToTsC m w d h mi s year
  | .day j d h mi s, year => dayYearToTsC j d h mi s year

/-! ### The rule after the last transition -/

/-- Python `_TZStr` (:425-458): built only with a start and an end rule. -/
structure TZStr where
  std : TTI
  dst : TTI
  dstDiff : Int
  start : TRule
  «end» : TRule
  deriving Repr, DecidableEq, Inhabited

/-- `_TZStr.__init__`, :436-458: `dst_diff`, the STD ttinfo with no DST, the DST one with
`dst_diff` (`_load_timedelta` of offsets this small cannot fail). -/
def mkTZStr (stdAbbr : Bytes) (stdOff : Int) (dstAbbr : Bytes) (dstOff : Int)
    (start «end» : TRule) : TZStr :=
  let dstDiff := dstOff - stdOff
  ⟨⟨stdOff, 0, stdAbbr⟩, ⟨dstOff, dstDiff, dstAbbr⟩, dstDiff, start, «end»⟩

/-- `_TZStr.transitions`, :460-463. -/
def TZStr.transitions (r : TZStr) (year : Int) : Int × Int :=
  (r.start.yearToEpochPy year, r.end.yearToEpochPy year)

/-- `_TZStr._get_trans_info`, :465-487. `fold == (self.dst_diff >= 0)` compares an int with a
bool, so only a fold of 1 (resp. 0) equals `True` (resp. `False`). -/
def TZStr.getTransInfo (r : TZStr) (ts year fold : Int) : TTI :=
  let (start, «end») := r.transitions year
  let (start, «end») :=
    if fold = (if r.dstDiff ≥ 0 then 1 else 0) then (start, «end» - r.dstDiff)
    else (start + r.dstDiff, «end»)
  let isdst := if start < «end» then decide (start ≤ ts ∧ ts < «end»)
    else !decide («end» ≤ ts ∧ ts < start)
  if isdst then r.dst else r.std

/-- `_TZStr._get_trans_info_fromutc`, :489-511. `start -= self.std.utcoff.total_seconds()`
makes floats of values below `2**40`, so they and the comparisons stay exact as ints. -/
def TZStr.getTransInfoFromutc (r : TZStr) (ts year : Int) : TTI × Bool :=
  let (start, «end») := r.transitions year
  let start := start - r.std.utcoff
  let «end» := «end» - r.dst.utcoff
  let isdst := if start < «end» then decide (start ≤ ts ∧ ts < «end»)
    else !decide («end» ≤ ts ∧ ts < start)
  let (ambigStart, ambigEnd) :=
    if r.dstDiff > 0 then («end», «end» + r.dstDiff) else (start, start - r.dstDiff)
  let fold := decide (ambigStart ≤ ts ∧ ts < ambigEnd)
  (if isdst then r.dst else r.std, fold)

/-- C `_tzrule`, :36-43. `start`/`end` are `NULL` (`none`) for an STD-only rule. -/
structure CRule where
  std : TTI
  dst : TTI
  dstDiff : Int
  start : Option TRule
  «end» : Option TRule
  stdOnly : Bool
  deriving Repr, DecidableEq, Inhabited

/-- C `tzrule_transitions`, :1485-1492 (asserts both rules are set; only called when
`std_only` is false, and then both are). -/
def CRule.transitions (r : CRule) (year : Int) : Int × Int :=
  ((r.start.getD default).yearToTsC year, (r.end.getD default).yearToTsC year)

/-- C `find_tzrule_ttinfo`, :1502-1542. -/
def CRule.find (r : CRule) (ts : Int) (fold : Nat) (year : Int) : TTI :=
  if r.stdOnly then r.std
  else
    let (start, «end») := r.transitions year
    let (start, «end») :=
      if fold = (if r.dstDiff ≥ 0 then 1 else 0) then (start, wrap64 («end» - r.dstDiff))
      else (wrap64 (start + r.dstDiff), «end»)
    let isdst := if start < «end» then decide (ts ≥ start ∧ ts < «end»)
      else decide (ts < «end» ∨ ts ≥ start)
    if isdst then r.dst else r.std

/-- C `find_tzrule_ttinfo_fromutc`, :1555-1598. -/
def CRule.findFromutc (r : CRule) (ts : Int) (year : Int) : TTI × Bool :=
  if r.stdOnly then (r.std, false)
  else
    let (start, «end») := r.transitions year
    let start := wrap64 (start - r.std.utcoff)
    let «end» := wrap64 («end» - r.dst.utcoff)
    let isdst := if start < «end» then decide (ts ≥ start ∧ ts < «end»)
      else decide (ts < «end» ∨ ts ≥ start)
    let (ambigStart, ambigEnd) :=
      if r.dstDiff > 0 then («end», wrap64 («end» + r.dstDiff))
      else (start, wrap64 (start - r.dstDiff))
    let fold := decide (ts ≥ ambigStart ∧ ts < ambigEnd)
    (if isdst then r.dst else r.std, fold)

/-! ### Character classes (ASCII; `re.ASCII` in Python, `Py_ISALPHA`/`Py_ISDIGIT` in C) -/

def isDigitB (c : UInt8) : Bool := inR c 48 57
def isAlphaB (c : UInt8) : Bool := inR c 65 90 || inR c 97 122
/-- `[a-zA-Z0-9+-]`, the quoted-abbreviation class. -/
def isQuotedB (c : UInt8) : Bool := isAlphaB c || isDigitB c || c == 43 || c == 45

/-- The decimal value of ASCII digits. -/
def digitsVal (ds : Bytes) : Int := ds.foldl (fun acc c => acc * 10 + ((c.toNat - 48 : Nat) : Int)) 0

/-! ### The C parser -/

/-- `*p`: the C string ends at its NUL, which `PyBytes_AsString` provides; the model's
remaining list has no NUL, so its end reads as `'\0'`. -/
def peek (p : Bytes) : UInt8 := p.headD 0

/-- C `parse_digits(p, min, max, &value)`, :1725-1738: at most `max` digits, failing with
fewer than `min`. Returns the value and the rest. -/
def parseDigitsC (min max : Nat) (p : Bytes) : Option (Int × Bytes) :=
  go max 0 0 p
where
  /-- `k` iterations of `for (i = 0; i < max; i++, (*p)++)` left; `i` is the index. -/
  go : Nat → Nat → Int → Bytes → Option (Int × Bytes)
    | 0, _, v, p => some (v, p)
    | k + 1, i, v, p =>
      if isDigitB (peek p) then go k (i + 1) (v * 10 + ((peek p).toNat - 48 : Nat)) p.tail
      else if i < min then none else some (v, p)

/-- The quoted loop of C `parse_abbr`, :1752-1768: characters of the class up to `'>'`; any
other character, the terminating NUL included, fails. Returns the run and what follows `'>'`. -/
def quotedRunC : Bytes → Option (Bytes × Bytes)
  | [] => none
  | c :: r =>
    if c = 62 then some ([], r)
    else if isQuotedB c then (quotedRunC r).map fun (a, b) => (c :: a, b)
    else none

/-- C `parse_abbr`, :1741-1798. -/
def parseAbbrC (p : Bytes) : Option (Bytes × Bytes) :=
  if peek p = 60 then
    match quotedRunC p.tail with
    | none => none
    | some (run, rest) => if run = [] then none else some (run, rest)
  else
    let run := p.takeWhile isAlphaB
    if run = [] then none else some (run, p.drop run.length)

/-- C `parse_transition_time`, :1940-1989. The caller's `minute`/`second` (`mi0`, `s0`) stay
when their `:dd` part is absent; the hour is always written. -/
def parseTransTimeC (mi0 s0 : Int) (p : Bytes) : Option ((Int × Int × Int) × Bytes) := do
  let (sign, p) : Int × Bytes :=
    if peek p = 45 then (-1, p.tail) else if peek p = 43 then (1, p.tail) else (1, p)
  let (h, p) ← parseDigitsC 1 3 p
  let h := h * sign
  if peek p = 58 then
    let (mi, p) ← parseDigitsC 2 2 p.tail
    let mi := mi * sign
    if peek p = 58 then
      let (s, p) ← parseDigitsC 2 2 p.tail
      pure ((h, mi, s * sign), p)
    else pure ((h, mi, s0), p)
  else pure ((h, mi0, s0), p)

/-- C `parse_tz_delta`, :1801-1836: hours beyond ±24 fail; the sign is inverted. -/
def parseTzDeltaC (p : Bytes) : Option (Int × Bytes) := do
  let ((h, m, s), p) ← parseTransTimeC 0 0 p
  if h > 24 ∨ h < -24 then none
  else some (-((h * 3600) + (m * 60) + s), p)

/-- C `calendarrule_new`, :1358-1403: the checks in order, then the stores into `uint8_t`,
`int16_t` and `int8_t` fields. -/
def calendarruleNew (month week day hour minute second : Int) : Option TRule :=
  if month < 1 ∨ month > 12 then none
  else if week < 1 ∨ week > 5 then none
  else if day < 0 ∨ day > 6 then none
  else if hour < -167 ∨ hour > 167 then none
  else some (.cal (wrapU 8 month) (wrapU 8 week) (wrapU 8 day) (wrapS 16 hour)
    (wrapS 8 minute) (wrapS 8 second))

/-- C `dayrule_new`, :1448-1482. -/
def dayruleNew (julian : Bool) (day hour minute second : Int) : Option TRule :=
  if day < (if julian then 1 else 0) ∨ day > 365 then none
  else if hour < -167 ∨ hour > 167 then none
  else some (.day julian (wrapU 16 (wrapS 16 day)) (wrapS 16 hour) (wrapS 8 minute) (wrapS 8 second))

/-- What the date part of a rule reads: `Mm.w.d`, or a day with or without `J`. -/
inductive RuleDate where
  | cal (m w d : Int)
  | day (julian : Bool) (d : Int)
  deriving Repr, DecidableEq

/-- The date part of C `parse_transition_rule`, :1863-1881 and :1903-1913. -/
def parseRuleDateC (p : Bytes) : Option (RuleDate × Bytes) :=
  if peek p = 77 then do
    let (month, p) ← parseDigitsC 1 2 p.tail
    if peek p ≠ 46 then none
    let (week, p) ← parseDigitsC 1 1 p.tail
    if peek p ≠ 46 then none
    let (day, p) ← parseDigitsC 1 1 p.tail
    pure (.cal month week day, p)
  else do
    let (julian, p) := if peek p = 74 then (true, p.tail) else (false, p)
    let (day, p) ← parseDigitsC 1 3 p
    pure (.day julian day, p)

/-- C `parse_transition_rule`, :1839-1937 (allocation failure is not modelled): the date, an
optional `/time` (02:00:00 by default, :1853-1855), then `calendarrule_new` or `dayrule_new`. -/
def parseTransRuleC (p : Bytes) : Option (TRule × Bytes) := do
  let (dt, p) ← parseRuleDateC p
  let ((h, mi, s), p) ← if peek p = 47 then parseTransTimeC 0 0 p.tail else some ((2, 0, 0), p)
  let r ← match dt with
    | .cal month week day => calendarruleNew month week day h mi s
    | .day julian day => dayruleNew julian day h mi s
  pure (r, p)

/-- C `build_tzrule`, :1999-2030 (`dst_abbr == NULL` gives an STD-only rule; `load_timedelta`
of offsets this small cannot fail). -/
def buildTzruleC (stdAbbr : Bytes) (dstAbbr : Option Bytes) (stdOff dstOff : Int)
    (start «end» : Option TRule) : CRule :=
  match dstAbbr with
  | some da =>
    let dstDiff := wrap32 (dstOff - stdOff)
    ⟨⟨stdOff, 0, stdAbbr⟩, ⟨dstOff, dstDiff, da⟩, dstDiff, start, «end», false⟩
  | none => ⟨⟨stdOff, 0, stdAbbr⟩, default, 0, start, «end», true⟩

/-- `ValueError` from C `parse_tz_str`; the message embeds `%R` of the bytes. -/
def tzErrC (what : String) : PyExc := .valueError s!"~{what}"

/-- C `parse_tz_str`, :1615-1723. `PyBytes_AsString` gives a `char *` that ends at the first
NUL, so the parser never sees what follows one. -/
def parseTzStrC (tz : Bytes) : Py CRule :=
  let p := tz.takeWhile (· ≠ 0)
  match parseAbbrC p with
  | none => .error (tzErrC "Invalid STD format in")
  | some (stdAbbr, p) =>
  match parseTzDeltaC p with
  | none => .error (tzErrC "Invalid STD offset in")
  | some (stdOff, p) =>
  if peek p = 0 then .ok (buildTzruleC stdAbbr none stdOff (2 ^ 20) none none)
  else
  match parseAbbrC p with
  | none => .error (tzErrC "Invalid DST format in")
  | some (dstAbbr, p) =>
  match (if peek p = 44 then some (stdOff + 3600, p) else parseTzDeltaC p) with
  | none => .error (tzErrC "Invalid DST offset in")
  | some (dstOff, p) =>
  if peek p ≠ 44 then .error (tzErrC "Missing transition rules in TZ string:")
  else
  match parseTransRuleC p.tail with
  | none => .error (tzErrC "Malformed transition rule in TZ string:")
  | some (start, p) =>
  if peek p ≠ 44 then .error (tzErrC "Missing transition rules in TZ string:")
  else
  match parseTransRuleC p.tail with
  | none => .error (tzErrC "Malformed transition rule in TZ string:")
  | some («end», p) =>
  if peek p ≠ 0 then .error (tzErrC "Extraneous characters at end of TZ string:")
  else .ok (buildTzruleC stdAbbr (some dstAbbr) stdOff dstOff (some start) (some «end»))

/-! ### The Python parser

The patterns are `re.ASCII`, and every character they accept is ASCII, so they are matched
over the UTF-8 bytes of the (valid UTF-8) string: a multi-byte character is one code point
that no class accepts, and its bytes are all `>= 0x80`, which no class accepts either; the
separators `,` and `/` never occur inside one.

Each `fullmatch` is deterministic. A shorter choice for a greedy part always leaves a letter,
digit or `:` next, and in every pattern such a character can only be taken by the part that
was shortened, so the greedy choice is the only one that can reach the end. -/

/-- `s.split(sep, 1)`: the part before the first `sep` and, if there is one, the rest. -/
def splitFirst (sep : UInt8) (s : Bytes) : Bytes × Option Bytes :=
  match s.findIdx? (· == sep) with
  | some i => (s.take i, some (s.drop (i + 1)))
  | none => (s, none)

/-- `[a-zA-Z]+|<[a-zA-Z0-9+-]+>` at the start (the group text, brackets included). -/
def reAbbr (s : Bytes) : Option (Bytes × Bytes) :=
  if isAlphaB (peek s) then
    let run := s.takeWhile isAlphaB
    some (run, s.drop run.length)
  else if peek s = 60 then
    let run := s.tail.takeWhile isQuotedB
    if run ≠ [] ∧ peek (s.tail.drop run.length) = 62 then
      some ([60] ++ run ++ [62], s.tail.drop (run.length + 1))
    else none
  else none

/-- `:\d{2}` at the start. -/
def reColon2 (s : Bytes) : Option (Bytes × Bytes) :=
  match s with
  | c :: a :: b :: r => if c = 58 ∧ isDigitB a ∧ isDigitB b then some ([a, b], r) else none
  | _ => none

/-- `[+-]?\d{1,3}(?::\d{2}(?::\d{2})?)?` at the start: the sign, hour digits, and the minute
and second digit pairs. -/
def reOff (s : Bytes) : Option ((Option UInt8 × Bytes × Option Bytes × Option Bytes) × Bytes) :=
  let (sg, s1) : Option UInt8 × Bytes :=
    if peek s = 43 ∨ peek s = 45 then (some (peek s), s.tail) else (none, s)
  let ds := (s1.takeWhile isDigitB).take 3
  if ds = [] then none
  else
    let s2 := s1.drop ds.length
    match reColon2 s2 with
    | none => some ((sg, ds, none, none), s2)
    | some (mm, s3) =>
      match reColon2 s3 with
      | none => some ((sg, ds, some mm, none), s3)
      | some (ss, s4) => some ((sg, ds, some mm, some ss), s4)

/-- The text a `reOff` match spans. -/
def offText (o : Option UInt8 × Bytes × Option Bytes × Option Bytes) : Bytes :=
  o.1.toList ++ o.2.1 ++ (o.2.2.1.map ([58] ++ ·)).getD [] ++ (o.2.2.2.map ([58] ++ ·)).getD []

/-- `parser_re.fullmatch(offset_str)` (_zoneinfo.py:641-655): the groups `std`, `stdoff`,
`dst`, `dstoff`, or `none` for no match. -/
def reTz (s : Bytes) : Option (Bytes × Option Bytes × Option Bytes × Option Bytes) := do
  let (std, r) ← reAbbr s
  if r = [] then return (std, none, none, none)
  let (so, r) ← reOff r
  if r = [] then return (std, some (offText so), none, none)
  let (dst, r) ← reAbbr r
  if r = [] then return (std, some (offText so), some dst, none)
  let (dso, r) ← reOff r
  if r = [] then return (std, some (offText so), some dst, some (offText dso))
  none

/-- The pattern `(?P<sign>[+-])?(?P<h>\d{1,3})(:(?P<m>\d{2})(:(?P<s>\d{2}))?)?` of
`_parse_transition_time` (:735-739) and `_parse_tz_delta` (:757-761), as a `fullmatch`:
whether the sign is `-`, and `int(v or 0)` of each group. -/
def reTime (s : Bytes) : Option (Bool × Int × Int × Int) :=
  match reOff s with
  | some ((sg, h, m, sec), []) =>
    some (sg = some 45, digitsVal h, (m.map digitsVal).getD 0, (sec.map digitsVal).getD 0)
  | _ => none

/-- `_parse_transition_time`, :734-753. -/
def parseTransitionTimePy (t : Bytes) : Py (Int × Int × Int) :=
  match reTime t with
  | none => .error (.valueError "~Invalid time:")
  | some (neg, h, m, s) =>
    if h > 167 then .error (.valueError "~Hour must be in [0, 167]:")
    else if neg then .ok (-h, -m, -s) else .ok (h, m, s)

/-- `_parse_tz_delta`, :756-779 (the `assert` holds: the caller's pattern matched first). -/
def parseTzDeltaPy (t : Bytes) : Py Int :=
  match reTime t with
  | none => .error (.assertionError "~")
  | some (neg, h, m, s) =>
    let total := h * 3600 + m * 60 + s
    if h > 24 then .error (.valueError "~Offset hours must be in [0, 24]:")
    else if !neg then .ok (-total) else .ok total

/-- `_CalendarOffset.__init__`, :566-581 (hour 2, minute 0, second 0 by default). -/
def calendarOffsetNew (m w d : Int) : Py TRule :=
  if ¬(1 ≤ m ∧ m ≤ 12) then .error (.valueError "m must be in [1, 12]")
  else if ¬(1 ≤ w ∧ w ≤ 5) then .error (.valueError "w must be in [1, 5]")
  else if ¬(0 ≤ d ∧ d ≤ 6) then .error (.valueError "d must be in [0, 6]")
  else .ok (.cal m w d 2 0 0)

/-- `_DayOffset.__init__`, :523-532. -/
def dayOffsetNew (d : Int) (julian : Bool) : Py TRule :=
  let minDay : Int := if julian then 1 else 0
  if ¬(minDay ≤ d ∧ d ≤ 365) then .error (.valueError s!"d must be in [{minDay}, 365], not: {d}")
  else .ok (.day julian d 2 0 0)

/-- `offset.hour, offset.minute, offset.second = ...`. -/
def TRule.setTime : TRule → Int × Int × Int → TRule
  | .cal m w d _ _ _, (h, mi, s) => .cal m w d h mi s
  | .day j d _ _ _, (h, mi, s) => .day j d h mi s

/-- `re.fullmatch(r"M(\d{1,2})\.(\d)\.(\d)", date)`, :711. -/
def reMonthRule (s : Bytes) : Option (Int × Int × Int) :=
  match s with
  | 77 :: r =>
    let ms := (r.takeWhile isDigitB).take 2
    if ms = [] then none
    else
      match r.drop ms.length with
      | 46 :: w :: 46 :: d :: [] => if isDigitB w ∧ isDigitB d then
          some (digitsVal ms, digitsVal [w], digitsVal [d]) else none
      | _ => none
  | _ => none

/-- The date part of `_parse_dst_start_end`, :708-726. -/
def parseDatePy (date : Bytes) : Py TRule :=
  if date.take 1 = [77] then
    match reMonthRule date with
    | none => .error (.valueError "~Invalid dst start/end date:")
    | some (m, w, d) => calendarOffsetNew m w d
  else
    let (julian, date) := if date.take 1 = [74] then (true, date.drop 1) else (false, date)
    if ¬(1 ≤ date.length ∧ date.length ≤ 3 ∧ date.all isDigitB) then
      .error (.valueError "~Invalid dst start/end date:")
    else dayOffsetNew (digitsVal date) julian

/-- `_parse_dst_start_end`, :706-731. -/
def parseDstStartEndPy (x : Bytes) : Py TRule := do
  let (date, time) := splitFirst 47 x
  let off ← parseDatePy date
  match time with
  | none => pure off
  | some t => do
    let hms ← parseTransitionTimePy t
    pure (off.setTime hms)

/-- What Python keeps after the last transition: a `_ttinfo` or a `_TZStr`. -/
inductive After where
  | tti (t : TTI)
  | tzstr (r : TZStr)
  deriving Repr, DecidableEq, Inhabited

/-- `str.strip("<>")`. -/
def stripAngle (s : Bytes) : Bytes :=
  ((s.dropWhile (fun c => c = 60 ∨ c = 62)).reverse.dropWhile (fun c => c = 60 ∨ c = 62)).reverse

/-- `ValueError` from `_parse_tz_str`; the messages embed the string. -/
def tzErrPy (what : String) : PyExc := .valueError s!"~{what}"

/-- `try: offset = _parse_tz_delta(t) except ValueError as e: raise ValueError(...) from e`
(_zoneinfo.py:670-673, :680-683): a `ValueError` becomes the caller's own; anything else
propagates. -/
def pyOffStep (t : Bytes) (msg : String) : Py Int :=
  match parseTzDeltaPy t with
  | .ok v => pure v
  | .error (.valueError _) => throw (tzErrPy msg)
  | .error e => throw e

/-- `_parse_tz_str(tz_str)`, :627-703, on the decoded string's UTF-8 bytes. Every `ValueError`
of a helper is re-raised as the caller's own `ValueError`. -/
def parseTzStrPy (tz : Bytes) : Py After := do
  let (offsetStr, startEndStr) := splitFirst 44 tz
  match reTz offsetStr with
  | none => throw (tzErrPy "is not a valid TZ string")
  | some (stdG, stdoffG, dstG, dstoffG) =>
  let stdAbbr := stripAngle stdG
  let dstAbbr := dstG.map stripAngle
  let stdOffset ← match stdoffG with
    | some t => pyOffStep t "Invalid STD offset in"
    | none => throw (tzErrPy "Invalid STD offset in")
  match dstAbbr with
  | some da => do
    let dstOffset ← match dstoffG with
      | some t => pyOffStep t "Invalid DST offset in"
      | none => pure (stdOffset + 3600)
    match startEndStr with
    | none => throw (tzErrPy "Missing transition rules:")
    | some se =>
      -- `start, end = (_parse_dst_start_end(x) for x in start_end_strs)`
      match splitFirst 44 se with
      | (a, none) =>
        match parseDstStartEndPy a with
        | .error _ => throw (tzErrPy "Invalid TZ string:")
        | .ok _ => throw (tzErrPy "Invalid TZ string:")  -- not enough values to unpack
      | (a, some b) =>
        match parseDstStartEndPy a, parseDstStartEndPy b with
        | .ok s, .ok e => pure (.tzstr (mkTZStr stdAbbr stdOffset da dstOffset s e))
        | _, _ => throw (tzErrPy "Invalid TZ string:")
  | none =>
    if startEndStr.isSome then throw (tzErrPy "Transition rule present without DST:")
    else pure (.tti ⟨stdOffset, 0, stdAbbr⟩)

end PyLean.Datetime.Zone
