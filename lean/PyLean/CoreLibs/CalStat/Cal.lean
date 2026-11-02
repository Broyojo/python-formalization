import PyLean.CoreLibs.CalStat.Text

/-!
Mirror of `Lib/calendar.py` (CPython 3.14.7), first part: the module functions and
the iterator methods of `Calendar`.

Generators are modelled by the list `list(gen)` produces, so a generator that
raises part-way is `.error`, which is what `list()` observes.
`datetime.date(y, m, d)` is `mkDate`: the `"iii"` argument conversion followed by
`Datetime.checkDate`. A `date` value is its `(year, month, day)` triple.
`Day(...)` and `Month` members are their int values (`IntEnum`).
-/

namespace PyLean.CoreLibs.CalStat

open PyLean PyLean.Datetime

/-! ## Exceptions (calendar.py:28-44) -/

/-- `IllegalMonthError(month)` with its `__str__`, calendar.py:33-37. -/
def illegalMonth (month : Int) : PyExc :=
  .named "IllegalMonthError" s!"bad month number {month}; must be 1-12"

/-- `IllegalWeekdayError(weekday)` with its `__str__`, calendar.py:40-44. -/
def illegalWeekday (wd : Int) : PyExc :=
  .named "IllegalWeekdayError" s!"bad weekday number {wd}; must be 0 (Monday) to 6 (Sunday)"

/-- `calendar.__getattr__(name)`, calendar.py:47-57. The `DeprecationWarning` is
returned next to the value, so it stays observable. -/
def moduleGetattr (name : String) : Py (Int × String) :=
  if name = "January" ∨ name = "February" then
    let w := s!"The '{name}' attribute is deprecated, use '{name.toUpper}' instead"
    if name = "January" then .ok (1, w) else .ok (2, w)
  else .error (.named "AttributeError" s!"module 'calendar' has no attribute '{name}'")

/-! ## `_localized_month`, `_localized_day` (calendar.py:97-132) -/

/-- What `strftime` gives for `%A`, `%a`, `%B`, `%b` in one locale. -/
structure Names where
  dayName : List Str
  dayAbbr : List Str
  monthName : List Str
  monthAbbr : List Str
  /-- `standalone_month_name`, Lib/calendar.py:143-159: `%OB` where the platform has it, or `month_name`. -/
  standaloneName : List Str
  deriving Inhabited

/-- The C locale. -/
def cNames : Names where
  dayName := ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"].map String.toList
  dayAbbr := ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"].map String.toList
  monthName := ["January", "February", "March", "April", "May", "June", "July", "August",
    "September", "October", "November", "December"].map String.toList
  monthAbbr := ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov",
    "Dec"].map String.toList
  standaloneName := ["January", "February", "March", "April", "May", "June", "July", "August",
    "September", "October", "November", "December"].map String.toList

/-- `_localized_month._months` applied to the format: the entry at index 0 is the
`lambda x: ""` inserted at calendar.py:100. -/
def localizedMonthList (months : List Str) : List Str := [] :: months

/-- `_localized_month.__getitem__`/`_localized_day.__getitem__`, int index,
calendar.py:105-110 and :124-129: the index goes to the underlying list. -/
def localizedGet (tbl : List Str) (i : Int) : Py Str := pyIndex tbl i

/-- The slice branch of the same methods. -/
def localizedSlice (tbl : List Str) (start stop : Option Int) (step : Int) : Py (List Str) :=
  pySlice tbl start stop step

/-- `_localized_month.__len__` (:112-113) and `_localized_day.__len__` (:131-132). -/
def localizedMonthLen : Nat := 13
def localizedDayLen : Nat := 7

/-! ## Module functions -/

/-- `isleap`, calendar.py:162-164. -/
def isleap (year : Int) : Bool :=
  year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)

/-- `leapdays`, calendar.py:167-172. -/
def leapdays (y1 y2 : Int) : Int :=
  let y1 := y1 - 1
  let y2 := y2 - 1
  (y2 / 4 - y1 / 4) - (y2 / 100 - y1 / 100) + (y2 / 400 - y1 / 400)

/-- The Argument Clinic conversion of `date_new`, Modules/clinic/_datetimemodule.c.h:173-181: `PyLong_AsInt`. -/
def cIntArg (x : Int) : Py Int :=
  if x > 2 ^ 31 - 1 ∨ x < -(2 ^ 31) then .error (.overflowError "Python int too large to convert to C int")
  else .ok x

/-- A `date` value. -/
abbrev Date := Int × Int × Int

/-- `datetime.date(y, m, d)`, Modules/_datetimemodule.c `date_new` (format `"iii"`)
then `check_date_args`. -/
def mkDate (y m d : Int) : Py Date := do
  let y ← cIntArg y
  let m ← cIntArg m
  let d ← cIntArg d
  checkDate y m d

/-- The year substitution of `weekday`, calendar.py:177-178. -/
def yearMap (year : Int) : Int :=
  if MINYEAR ≤ year ∧ year ≤ MAXYEAR then year else 2000 + year % 400

/-- `weekday`, calendar.py:175-179, with `date.weekday()` =
`(toordinal + 6) % 7` (_pydatetime.py `date.weekday`). -/
def weekday (year month day : Int) : Py Int := do
  let (y, m, d) ← mkDate (yearMap year) month day
  return (ymd2ord y m d + 6) % 7

/-- `_validate_month`, calendar.py:182-184. -/
def validateMonth (month : Int) : Py Unit :=
  if ¬(1 ≤ month ∧ month ≤ 12) then .error (illegalMonth month) else .ok ()

/-- `mdays`, calendar.py:90. -/
def mdaysList : List Int := [0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]

/-- `month == FEBRUARY and isleap(year)` as an int summand. -/
def febExtra (year month : Int) : Int := if month = 2 ∧ isleap year = true then 1 else 0

/-- `monthrange`, calendar.py:186-192. -/
def monthrange (year month : Int) : Py (Int × Int) := do
  validateMonth month
  let day1 ← weekday year month 1
  let ndays := (← pyIndex mdaysList month) + febExtra year month
  return (day1, ndays)

/-- `_monthlen`, calendar.py:195-196 (unvalidated: `mdays[month]` is a list index). -/
def monthlen (year month : Int) : Py Int := do
  return (← pyIndex mdaysList month) + febExtra year month

/-- `_prevmonth`, calendar.py:199-203. -/
def prevmonth (year month : Int) : Int × Int :=
  if month = 1 then (year - 1, 12) else (year, month - 1)

/-- `_nextmonth`, calendar.py:206-210. -/
def nextmonth (year month : Int) : Int × Int :=
  if month = 12 then (year + 1, 1) else (year, month + 1)

/-! ## class Calendar, calendar.py:213-346 -/

/-- A `Calendar`: the raw `_firstweekday` attribute (`__init__`, :219-220, and
`setfirstweekday`, :225-226, store it unchanged). -/
structure Calendar where
  raw : Int
  deriving Repr, DecidableEq, Inhabited

/-- `Calendar.getfirstweekday`, calendar.py:222-223. -/
def Calendar.firstweekday (c : Calendar) : Int := c.raw % 7

/-- `Calendar.setfirstweekday`, calendar.py:225-226. -/
def Calendar.setfirstweekday (_c : Calendar) (fw : Int) : Calendar := ⟨fw⟩

/-- `Calendar.iterweekdays`, calendar.py:230-236. -/
def Calendar.iterweekdays (c : Calendar) : List Int :=
  (rangeI c.firstweekday (c.firstweekday + 7)).map (· % 7)

/-- `Calendar.itermonthdays`, calendar.py:247-257. -/
def Calendar.itermonthdays (c : Calendar) (year month : Int) : Py (List Int) := do
  let (day1, ndays) ← monthrange year month
  let daysBefore := (day1 - c.firstweekday) % 7
  let daysAfter := (c.firstweekday - day1 - ndays) % 7
  return List.replicate daysBefore.toNat 0 ++ rangeI 1 (ndays + 1) ++
    List.replicate daysAfter.toNat 0

/-- `enumerate(xs, start)`. -/
def enumFrom {α : Type} (start : Int) (xs : List α) : List (Int × α) :=
  xs.zipIdx.map (fun p => (start + (p.2 : Int), p.1))

/-- `Calendar.itermonthdays2`, calendar.py:259-265. -/
def Calendar.itermonthdays2 (c : Calendar) (year month : Int) : Py (List (Int × Int)) := do
  let days ← c.itermonthdays year month
  return (enumFrom c.firstweekday days).map (fun p => (p.2, p.1 % 7))

/-- `Calendar.itermonthdays3`, calendar.py:267-283. -/
def Calendar.itermonthdays3 (c : Calendar) (year month : Int) : Py (List Date) := do
  let (day1, ndays) ← monthrange year month
  let daysBefore := (day1 - c.firstweekday) % 7
  let daysAfter := (c.firstweekday - day1 - ndays) % 7
  let (y, m) := prevmonth year month
  let endd := (← monthlen y m) + 1
  let part1 := (rangeI (endd - daysBefore) endd).map (fun d => ((y, m, d) : Date))
  let part2 := (rangeI 1 (ndays + 1)).map (fun d => ((year, month, d) : Date))
  let (y', m') := nextmonth year month
  let part3 := (rangeI 1 (daysAfter + 1)).map (fun d => ((y', m', d) : Date))
  return part1 ++ part2 ++ part3

/-- `Calendar.itermonthdays4`, calendar.py:285-291. -/
def Calendar.itermonthdays4 (c : Calendar) (year month : Int) :
    Py (List (Int × Int × Int × Int)) := do
  let days ← c.itermonthdays3 year month
  return (enumFrom 0 days).map
    (fun p => (p.2.1, p.2.2.1, p.2.2.2, (c.firstweekday + p.1) % 7))

/-- `[datetime.date(*t) for t in ts]`, stopping at the first exception. -/
def mkDates (ts : List Date) : Py (List Date) :=
  ts.mapM (fun t => mkDate t.1 t.2.1 t.2.2)

/-- `Calendar.itermonthdates`, calendar.py:238-245. -/
def Calendar.itermonthdates (c : Calendar) (year month : Int) : Py (List Date) := do
  mkDates (← c.itermonthdays3 year month)

/-- `Calendar.monthdatescalendar`, calendar.py:293-299. -/
def Calendar.monthdatescalendar (c : Calendar) (year month : Int) : Py (List (List Date)) := do
  return chunks 7 (← c.itermonthdates year month)

/-- `Calendar.monthdays2calendar`, calendar.py:301-309. -/
def Calendar.monthdays2calendar (c : Calendar) (year month : Int) :
    Py (List (List (Int × Int))) := do
  return chunks 7 (← c.itermonthdays2 year month)

/-- `Calendar.monthdayscalendar`, calendar.py:311-317. -/
def Calendar.monthdayscalendar (c : Calendar) (year month : Int) : Py (List (List Int)) := do
  return chunks 7 (← c.itermonthdays year month)

/-- The `Month` enum in definition order, calendar.py:62-74. -/
def months12 : List Int := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- `Calendar.yeardatescalendar`, calendar.py:319-327. -/
def Calendar.yeardatescalendar (c : Calendar) (year width : Int) :
    Py (List (List (List (List Date)))) := do
  let months ← months12.mapM (c.monthdatescalendar year)
  pyChunks width months

/-- `Calendar.yeardays2calendar`, calendar.py:329-337. -/
def Calendar.yeardays2calendar (c : Calendar) (year width : Int) :
    Py (List (List (List (List (Int × Int))))) := do
  let months ← months12.mapM (c.monthdays2calendar year)
  pyChunks width months

/-- `Calendar.yeardayscalendar`, calendar.py:339-346. -/
def Calendar.yeardayscalendar (c : Calendar) (year width : Int) :
    Py (List (List (List (List Int)))) := do
  let months ← months12.mapM (c.monthdayscalendar year)
  pyChunks width months

/-! ## Module level state and helpers -/

/-- Module-level `setfirstweekday`, calendar.py:834-837, on the module's calendar `c`. -/
def setfirstweekdayModule (c : Calendar) (fw : Int) : Py Calendar :=
  if ¬(0 ≤ fw ∧ fw ≤ 6) then .error (illegalWeekday fw)
  else .ok (c.setfirstweekday fw)

/-- `formatstring`, calendar.py:859-862. -/
def formatstring (cols : List Str) (colwidth spacing : Int) : Str :=
  join (strTimes [' '] spacing) (cols.map (center · colwidth))

/-- `format`, calendar.py:854-856, as its printed output. -/
def formatPrint (cols : List Str) (colwidth spacing : Int) : Str :=
  formatstring cols colwidth spacing ++ ['\n']

/-- `_EPOCH_ORD`, calendar.py:866. -/
def epochOrd : Int := ymd2ord 1970 1 1

/-- `timegm`, calendar.py:869-876; the tuple is passed unpacked (`tuple[:6]`). -/
def timegm (year month day hour minute second : Int) : Py Int := do
  let (y, m, d) ← mkDate year month 1
  let days := ymd2ord y m d - epochOrd + day - 1
  let hours := days * 24 + hour
  let minutes := hours * 60 + minute
  return minutes * 60 + second

end PyLean.CoreLibs.CalStat
