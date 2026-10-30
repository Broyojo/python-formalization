import PyLean.Datetime.Delta

/-!
The proleptic Gregorian calendar core of `date`: ordinals, ISO calendar,
`date ± timedelta` and the field checks, after `Lib/_pydatetime.py` and
`Modules/_datetimemodule.c` (CPython 3.14.7).

The C helpers use truncating `/` and `%` on `int` (`Int.tdiv`, `Int.tmod`);
Python uses floor division. Where the source asserts that its inputs are
in range (e.g. `assert(ordinal >= 1)`), the C model still uses the C operators,
so their agreement with Python is a theorem rather than a modelling choice.
-/

namespace PyLean.Datetime

open PyLean

def MINYEAR : Int := 1
def MAXYEAR : Int := 9999
/-- `date.max.toordinal()`, `_MAXORDINAL` (_pydatetime.py:20), C `MAXORDINAL`. -/
def MAXORDINAL : Int := 3652059

/-- `_is_leap`, _pydatetime.py:47-49; C `is_leap` (:422-432) casts to
`unsigned int` first, which agrees for the non-negative years it is given. -/
def isLeap (y : Int) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

/-- `_DAYS_IN_MONTH`, _pydatetime.py:38 (index 0 is a placeholder). -/
def daysInMonthTable (m : Int) : Int :=
  [-1, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31].getD m.toNat (-1)

/-- `_DAYS_BEFORE_MONTH`, _pydatetime.py:40-44. -/
def daysBeforeMonthTable (m : Int) : Int :=
  [-1, 0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334].getD m.toNat (-1)

/-- `_days_in_month`, _pydatetime.py:56-61; C `days_in_month`, :435-444.
Both assert `1 <= month <= 12`; every caller establishes it. -/
def daysInMonth (y m : Int) : Int :=
  if m = 2 ∧ isLeap y then 29 else daysInMonthTable m

/-- `_days_before_month`, _pydatetime.py:63-66; C `days_before_month`, :447-458. -/
def daysBeforeMonth (y m : Int) : Int :=
  daysBeforeMonthTable m + (if m > 2 ∧ isLeap y then 1 else 0)

/-- `_days_before_year`, _pydatetime.py:51-54. -/
def daysBeforeYear (year : Int) : Int :=
  let y := year - 1
  y * 365 + y / 4 - y / 100 + y / 400

/-- `_ymd2ord`, _pydatetime.py:68-75 (asserts a valid date; callers ensure it). -/
def ymd2ord (y m d : Int) : Int := daysBeforeYear y + daysBeforeMonth y m + d

def DI400Y : Int := 146097
def DI100Y : Int := 36524
def DI4Y : Int := 1461

/-- The month search at the end of `_ord2ymd`, _pydatetime.py:140-153: month
and day from the 0-based day of the year `n`. -/
def monthDayPy (leapyear : Bool) (n : Int) : Int × Int :=
  -- `(n + 50) >> 5` is floor division by 32
  let month := (n + 50) / 32
  let preceding := daysBeforeMonthTable month + (if month > 2 ∧ leapyear then 1 else 0)
  let (month, preceding) :=
    if preceding > n then
      let month := month - 1
      (month, preceding - (daysInMonthTable month + (if month = 2 ∧ leapyear then 1 else 0)))
    else (month, preceding)
  (month, n - preceding + 1)

/-- `_ord2ymd`, _pydatetime.py:93-153. The two `assert`s are invariants of the
arithmetic and are not modelled. -/
def ord2ymd (n : Int) : Int × Int × Int :=
  let n := n - 1
  let n400 := n / DI400Y
  let n := n % DI400Y
  let year := n400 * 400 + 1
  let n100 := n / DI100Y
  let n := n % DI100Y
  let n4 := n / DI4Y
  let n := n % DI4Y
  let n1 := n / 365
  let n := n % 365
  let year := year + n100 * 100 + n4 * 4 + n1
  if n1 = 4 ∨ n100 = 4 then (year - 1, 12, 31)
  else
    let leapyear := decide (n1 = 3 ∧ (n4 ≠ 24 ∨ n100 = 3))
    let (month, day) := monthDayPy leapyear n
    (year, month, day)

/-! ### C calendar helpers -/

/-- C `days_before_year`, :463-473 (truncating division; asserts `year >= 1`). -/
def daysBeforeYearC (year : Int) : Int :=
  let y := year - 1
  y * 365 + y.tdiv 4 - y.tdiv 100 + y.tdiv 400

/-- C `ymd_to_ord`, :567-571. -/
def ymdToOrdC (y m d : Int) : Int := daysBeforeYearC y + daysBeforeMonth y m + d

/-- The month search at the end of C `ord_to_ymd`, :552-563; the estimate
correction uses `days_in_month(year, month)`. -/
def monthDayC (year : Int) (leapyear : Bool) (n : Int) : Int × Int :=
  -- `(n + 50) >> 5`: arithmetic shift, i.e. floor division by 32
  let month := (n + 50) / 32
  let preceding := daysBeforeMonthTable month + (if month > 2 ∧ leapyear then 1 else 0)
  let (month, preceding) :=
    if preceding > n then
      let month := month - 1
      (month, preceding - daysInMonth year month)
    else (month, preceding)
  (month, n - preceding + 1)

/-- C `ord_to_ymd`, :483-564 (asserts `ordinal >= 1`; callers check it). -/
def ordToYmdC (ordinal : Int) : Int × Int × Int :=
  let ordinal := ordinal - 1
  let n400 := ordinal.tdiv DI400Y
  let n := ordinal.tmod DI400Y
  let year := n400 * 400 + 1
  let n100 := n.tdiv DI100Y
  let n := n.tmod DI100Y
  let n4 := n.tdiv DI4Y
  let n := n.tmod DI4Y
  let n1 := n.tdiv 365
  let n := n.tmod 365
  let year := year + n100 * 100 + n4 * 4 + n1
  if n1 = 4 ∨ n100 = 4 then (year - 1, 12, 31)
  else
    let leapyear := decide (n1 = 3 ∧ (n4 ≠ 24 ∨ n100 = 3))
    let (month, day) := monthDayC year leapyear n
    (year, month, day)

/-! ### Field checks -/

/-- `_check_date_fields`, _pydatetime.py:559-570; C `check_date_args`, :655-677
(same order and messages). -/
def checkDate (y m d : Int) : Py (Int × Int × Int) :=
  if ¬(MINYEAR ≤ y ∧ y ≤ MAXYEAR) then .error (.valueError s!"year must be in 1..9999, not {y}")
  else if ¬(1 ≤ m ∧ m ≤ 12) then .error (.valueError s!"month must be in 1..12, not {m}")
  else
    let dim := daysInMonth y m
    if ¬(1 ≤ d ∧ d ≤ dim) then
      .error (.valueError s!"day {d} must be in range 1..{dim} for month {m} in year {y}")
    else .ok (y, m, d)

/-- A valid `date` value. -/
def ValidDate (y m d : Int) : Prop :=
  MINYEAR ≤ y ∧ y ≤ MAXYEAR ∧ 1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ daysInMonth y m

instance (y m d : Int) : Decidable (ValidDate y m d) := by unfold ValidDate; infer_instance

/-- `_check_time_fields`, _pydatetime.py:572-588 with `fold=0`; C
`check_time_args`, :682-708. -/
def checkTime (h mi s us : Int) : Py (Int × Int × Int × Int) :=
  if ¬(0 ≤ h ∧ h ≤ 23) then .error (.valueError s!"hour must be in 0..23, not {h}")
  else if ¬(0 ≤ mi ∧ mi ≤ 59) then .error (.valueError s!"minute must be in 0..59, not {mi}")
  else if ¬(0 ≤ s ∧ s ≤ 59) then .error (.valueError s!"second must be in 0..59, not {s}")
  else if ¬(0 ≤ us ∧ us ≤ 999999) then
    .error (.valueError s!"microsecond must be in 0..999999, not {us}")
  else .ok (h, mi, s, us)

/-! ### Ordinals and arithmetic -/

/-- `PyArg_ParseTuple` format `i`: a C `int`. -/
def fitsCInt (x : Int) : Prop := -2 ^ 31 ≤ x ∧ x ≤ 2 ^ 31 - 1

instance (x : Int) : Decidable (fitsCInt x) := by unfold fitsCInt; infer_instance


/-- `date.fromordinal(n)`, _pydatetime.py:1031-1038. -/
def fromordinalPy (n : Int) : Py (Int × Int × Int) :=
  let (y, m, d) := ord2ymd n
  checkDate y m d

/-- `date.fromordinal(n)` in C, `date_fromordinal`, :3362-3382 (`"i"` conversion,
then the `ordinal >= 1` check). -/
def fromordinalC (n : Int) : Py (Int × Int × Int) :=
  if ¬fitsCInt n then .error (.overflowError "~Python int too large to convert to C int")
  else if n < 1 then .error (.valueError "ordinal must be >= 1")
  else let (y, m, d) := ordToYmdC n; checkDate y m d

/-- `date.toordinal()`, _pydatetime.py:1151-1157. -/
def toordinal (y m d : Int) : Int := ymd2ord y m d

/-- `date + timedelta`, _pydatetime.py:1213-1220. -/
def dateAddPy (y m d : Int) (t : Delta) : Py (Int × Int × Int) :=
  let o := toordinal y m d + t.days
  if 0 < o ∧ o ≤ MAXORDINAL then fromordinalPy o
  else .error (.overflowError "result out of range")

/-- `normalize_y_m_d`, _datetimemodule.c:767-828. -/
def normalizeYMDC (y m d : Int) : Py (Int × Int × Int) :=
  let dim := daysInMonth y m
  let r : Option (Int × Int × Int) :=
    if d < 1 ∨ d > dim then
      if d = 0 then
        let m := m - 1
        if m > 0 then some (y, m, daysInMonth y m) else some (y - 1, 12, 31)
      else if d = dim + 1 then
        let m := m + 1
        if m > 12 then some (y + 1, 1, 1) else some (y, m, 1)
      else
        let ordinal := ymdToOrdC y m 1 + d - 1
        if ordinal < 1 ∨ ordinal > MAXORDINAL then none
        else some (ordToYmdC ordinal)
    else some (y, m, d)
  match r with
  | some (y, m, d) =>
    if MINYEAR ≤ y ∧ y ≤ MAXYEAR then .ok (y, m, d)
    else .error (.overflowError "date value out of range")
  | none => .error (.overflowError "date value out of range")

/-- `add_date_timedelta`, _datetimemodule.c:3496-3510 (`negate = 0`), then
`new_date_subclass_ex` (whose `check_date_args` cannot fail after
normalization). -/
def dateAddC (y m d : Int) (t : Delta) : Py (Int × Int × Int) := do
  let (y, m, d) ← normalizeYMDC y m (d + t.days)
  checkDate y m d

/-! ### ISO calendar -/

/-- `_isoweek1monday`, _pydatetime.py:2391-2399; C `iso_week1_monday`,
:583-595 (same arithmetic; C uses `%` on a positive left operand). -/
def isoWeek1Monday (year : Int) : Int :=
  let firstday := ymd2ord year 1 1
  let firstweekday := (firstday + 6) % 7
  let week1monday := firstday - firstweekday
  if firstweekday > 3 then week1monday + 7 else week1monday

/-- `date.isocalendar()`, _pydatetime.py:1245-1271; C `date_isocalendar`,
:3797-3830 (its `divmod` helper rounds towards minus infinity, like Python). -/
def isocalendar (y m d : Int) : Int × Int × Int :=
  let week1monday := isoWeek1Monday y
  let today := ymd2ord y m d
  let week := (today - week1monday) / 7
  let day := (today - week1monday) % 7
  if week < 0 then
    let year := y - 1
    let week1monday := isoWeek1Monday year
    (year, (today - week1monday) / 7 + 1, (today - week1monday) % 7 + 1)
  else if week ≥ 52 ∧ today ≥ isoWeek1Monday (y + 1) then (y + 1, 1, day + 1)
  else (y, week + 1, day + 1)

/-- `_isoweek_to_gregorian`, _pydatetime.py:503-535. -/
def isoweekToGregorianPy (year week day : Int) : Py (Int × Int × Int) :=
  if ¬(MINYEAR ≤ year ∧ year ≤ MAXYEAR) then
    .error (.valueError s!"year must be in 1..9999, not {year}")
  else
    let outOfRange :=
      if ¬(0 < week ∧ week < 53) then
        if week = 53 then
          let firstWeekday := ymd2ord year 1 1 % 7
          ¬(firstWeekday = 4 ∨ (firstWeekday = 3 ∧ isLeap year))
        else True
      else False
    if outOfRange then .error (.valueError s!"Invalid week: {week}")
    else if ¬(0 < day ∧ day < 8) then
      .error (.valueError s!"Invalid weekday: {day} (range is [1, 7])")
    else
      let dayOffset := (week - 1) * 7 + (day - 1)
      .ok (ord2ymd (isoWeek1Monday year + dayOffset))

/-- `date.fromisocalendar(year, week, day)`, _pydatetime.py:1058-1063. -/
def fromisocalendarPy (year week day : Int) : Py (Int × Int × Int) := do
  let (y, m, d) ← isoweekToGregorianPy year week day
  checkDate y m d

/-- C `weekday`, :574-578. -/
def weekdayC (y m d : Int) : Int := (ymdToOrdC y m d + 6).tmod 7

/-- C `iso_to_ymd`, :597-631; returns the C status code or the date. -/
def isoToYmdC (isoYear isoWeek isoDay : Int) : Except Int (Int × Int × Int) :=
  if isoYear < MINYEAR ∨ isoYear > MAXYEAR then .error (-4)
  else
    let outOfRange :=
      if isoWeek ≤ 0 ∨ isoWeek ≥ 53 then
        if isoWeek = 53 then
          let firstWeekday := weekdayC isoYear 1 1
          ¬(firstWeekday = 3 ∨ (firstWeekday = 2 ∧ isLeap isoYear))
        else True
      else False
    if outOfRange then .error (-2)
    else if isoDay ≤ 0 ∨ isoDay ≥ 8 then .error (-3)
    else
      let day1 := isoWeek1Monday isoYear
      let dayOffset := (isoWeek - 1) * 7 + isoDay - 1
      .ok (ordToYmdC (day1 + dayOffset))

/-- `date.fromisocalendar`, C `date_fromisocalendar`, :3425-3465. The
`OverflowError` of the `"iii"` conversion is turned into `ValueError`. -/
def fromisocalendarC (year week day : Int) : Py (Int × Int × Int) :=
  if ¬(fitsCInt year ∧ fitsCInt week ∧ fitsCInt day) then
    .error (.valueError "ISO calendar component out of range")
  else
    match isoToYmdC year week day with
    | .error (-4) => .error (.valueError s!"year must be in 1..9999, not {year}")
    | .error (-2) => .error (.valueError s!"Invalid week: {week}")
    | .error _ => .error (.valueError s!"Invalid weekday: {day} (range is [1, 7])")
    | .ok (y, m, d) => checkDate y m d

end PyLean.Datetime
