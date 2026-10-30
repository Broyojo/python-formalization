import PyLean.Registry
import PyLean.Datetime.Diff
import PyLean.Datetime.DeltaProps
import PyLean.Datetime.CalendarProps
import PyLean.Datetime.IsoCalProps
import PyLean.Datetime.IsoRefute
import PyLean.Datetime.IsoRoundtrip

/-!
`Lib/_pydatetime.py` and `Modules/_datetimemodule.c`, CPython 3.14.7.

The model covers the exact (integer) core of both twins: ordinals, the ISO
calendar, `date + timedelta`, `timedelta` construction and arithmetic with int
and timedelta operands, `timezone` offset checks, `isoformat()`, and the
three ISO 8601 parsers (`fromisoformat`). Floats, the OS clock and local time
are out of scope.
-/

namespace PyLean.Datetime

open PyLean.Registry

def entries : List Entry := [
  { id := "datetime-ordinal-roundtrip", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromordinal", "date.toordinal", "_ord2ymd", "_ymd2ord", "C ord_to_ymd", "C ymd_to_ord"]
    statement := "For every date d, date.fromordinal(d.toordinal()) == d, in both the C and the Python implementation."
    source := "date.toordinal docs (inverse of fromordinal); invariant", status := .proven
    prop := ``FromordinalToordinal, thm := some ``fromordinalToordinal_proven },
  { id := "datetime-toordinal-roundtrip", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromordinal", "date.toordinal", "_ord2ymd", "C ord_to_ymd"]
    statement := "For every 1 <= n <= date.max.toordinal(), date.fromordinal(n) returns the same valid date in both twins, and its toordinal() is n."
    source := "date.fromordinal docs; invariant", status := .proven
    prop := ``ToordinalFromordinal, thm := some ``toordinalFromordinal_proven },
  { id := "datetime-date-add-timedelta", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.__add__", "C add_date_timedelta", "C normalize_y_m_d"]
    statement := "For every date d and timedelta t: if d.toordinal() + t.days is in 1..MAXORDINAL, C and Python both return the same valid date with that ordinal; otherwise both raise OverflowError."
    source := "date + timedelta docs (\"date2 is moved forward ... timedelta.days days\"); C/Python twins", status := .proven
    prop := ``DateAddTimedelta, thm := some ``dateAddTimedelta_proven },
  { id := "datetime-isocalendar-roundtrip", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.isocalendar", "date.fromisocalendar", "_isoweek_to_gregorian", "C iso_to_ymd"]
    statement := "For every date d, date.fromisocalendar(*d.isocalendar()) == d, in both twins."
    source := "date.fromisocalendar docstring (\"inverse of the date.isocalendar() function\")", status := .proven
    prop := ``FromisocalendarIsocalendar, thm := some ``fromisocalendarIsocalendar_proven },
  { id := "datetime-fromisocalendar-exact", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromisocalendar", "_isoweek_to_gregorian", "date.isocalendar"]
    statement := "date.fromisocalendar(Y, W, D) succeeds only for valid ISO triples (week 53 only in years with 53 ISO weeks) and the result's isocalendar() is (Y, W, D)."
    source := "date.fromisocalendar docstring; ISO 8601 week rules", status := .proven
    prop := ``FromisocalendarExact, thm := some ``fromisocalendarExact_proven },
  { id := "datetime-fromisocalendar-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromisocalendar", "C date_fromisocalendar"]
    statement := "For all ints Y, W, D, C and Python date.fromisocalendar(Y, W, D) return the same date or both raise ValueError."
    source := "C/Python twins", status := .proven
    prop := ``FromisocalendarTwins, thm := some ``fromisocalendarTwins_proven },
  { id := "datetime-timedelta-ctor-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__new__", "C delta_new", "C microseconds_to_delta_ex"]
    statement := "For all int arguments days, seconds, microseconds, milliseconds, minutes, hours, weeks, C and Python timedelta(...) return the same value or raise the same exception class (OverflowError)."
    source := "C/Python twins", status := .proven
    prop := ``TimedeltaCtorTwins, thm := some ``timedeltaCtorTwins_proven },
  { id := "datetime-timedelta-ctor-exact", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__new__"]
    statement := "timedelta(...) with int arguments returns the normalized value (0 <= seconds < 86400, 0 <= microseconds < 10**6, |days| <= 999999999) equal to the sum of the arguments exactly when that sum is within [timedelta.min, timedelta.max], and raises OverflowError otherwise."
    source := "timedelta docs (normalization, \"If the normalized value of days lies outside the indicated range, OverflowError is raised\")", status := .proven
    prop := ``TimedeltaCtorExact, thm := some ``timedeltaCtorExact_proven },
  { id := "datetime-timedelta-ops-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__add__", "__sub__", "__neg__", "__abs__", "__mul__", "__floordiv__", "__truediv__", "__mod__", "__divmod__"]
    statement := "For all valid timedeltas a, b and every int k, a+b, a-b, -a, abs(a), a*k, a//k, a/k, a//b, a%b and divmod(a, b) agree between C and Python in value and exception class."
    source := "C/Python twins", status := .proven
    prop := ``TimedeltaOpsTwins, thm := some ``timedeltaOpsTwins_proven },
  { id := "datetime-timedelta-divmod", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__divmod__", "__floordiv__", "__mod__"]
    statement := "For valid timedeltas a, b with b != 0, divmod(a, b) == (a // b, a % b) with q*b + r == a and r zero or of b's sign with |r| < |b|; for b == 0 it raises ZeroDivisionError."
    source := "timedelta docs (q, r = divmod(t1, t2)); invariant", status := .proven
    prop := ``TimedeltaDivmod, thm := some ``timedeltaDivmod_proven },
  { id := "datetime-timezone-range", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timezone.__new__", "C new_timezone"]
    statement := "timezone(offset) accepts exactly the offsets strictly between -24h and 24h (returning that offset) and otherwise raises ValueError, identically in both twins."
    source := "timezone docs (\"strictly between -timedelta(hours=24) and timedelta(hours=24)\")", status := .proven
    prop := ``TimezoneRange, thm := some ``timezoneRange_proven },
  { id := "datetime-date-isoformat-roundtrip", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.isoformat", "date.fromisoformat", "datetime.fromisoformat", "_parse_isoformat_date", "C parse_isoformat_date"]
    statement := "For every date d, date.fromisoformat(d.isoformat()) == d and datetime.fromisoformat(d.isoformat()) == datetime(d.year, d.month, d.day), in both twins."
    source := "date.fromisoformat docs (\"the output of date.isoformat()\" is accepted)", status := .proven
    prop := ``DateIsoformatRoundtrip, thm := some ``dateIsoformatRoundtrip_proven },
  { id := "datetime-date-fromiso-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromisoformat", "_parse_isoformat_date", "C date_fromisoformat"]
    statement := "For every string s, C and Python date.fromisoformat(s) return the same date or both raise the same exception class."
    source := "C/Python twins", status := .refuted
    prop := ``DateFromisoTwins, thm := some ``dateFromisoTwins_refuted
    bug := some "datetime-pydatetime-fromisoformat-int-leniency"
    notes := "Python's int() on fixed-width slices accepts signs, white space and non-ASCII digits ('2020-+1-01'). Fixed on main (_read_isoformat_component). The C-only acceptance of '20040509\\u0660' (UTF-8 byte length) also breaks this property." },
  { id := "datetime-time-fromiso-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.fromisoformat", "_parse_hh_mm_ss_ff", "C parse_hh_mm_ss_ff"]
    statement := "For every string s, C and Python time.fromisoformat(s) return the same time or both raise the same exception class."
    source := "C/Python twins", status := .refuted
    prop := ``TimeFromisoTwins, thm := some ``timeFromisoTwins_refuted
    bug := some "datetime-c-fromisoformat-fraction-without-decimal-mark"
    notes := "C reads digits after HHMMSS as a fraction with no '.' or ','. Other witnesses on 3.14.7: stray text before an offset ('12:30x+05:00', gh-158501, fixed on main), Python int() leniency (' 1:00')." },
  { id := "datetime-datetime-fromiso-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.fromisoformat", "C parse_isoformat_time"]
    statement := "For every string s, C and Python datetime.fromisoformat(s) return the same datetime or both raise the same exception class."
    source := "C/Python twins", status := .refuted
    prop := ``DatetimeFromisoTwins, thm := some ``datetimeFromisoTwins_refuted
    bug := some "datetime-c-fromisoformat-nul-after-z"
    notes := "Witness '2020-01-01T12:00Z\\x00junk' (still on main). On 3.14.7 an embedded NUL also ends the time in other positions ('...T12\\x00')." },
  { id := "datetime-datetime-fromiso-bare-separator", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.fromisoformat"]
    statement := "For every date d and character c, datetime.fromisoformat(d.isoformat() + c) raises ValueError in both twins (a separator needs a time after it)."
    source := "datetime.fromisoformat docs (any valid ISO 8601 format); C behaviour", status := .refuted
    prop := ``DatetimeFromisoBareSeparator, thm := some ``datetimeFromisoBareSeparator_refuted
    bug := some "datetime-pydatetime-fromisoformat-trailing-separator" },
  { id := "datetime-datetime-fromiso-midnight-valid-date", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.fromisoformat", "C datetime_fromisoformat"]
    statement := "For every string D, if datetime.fromisoformat(D + 'T24:00') returns a value then datetime.fromisoformat(D) does too, in both twins."
    source := "datetime.fromisoformat docs (24:00 is midnight at the end of the day)", status := .refuted
    prop := ``DatetimeFromisoMidnightNeedsValidDate, thm := some ``datetimeFromisoMidnightNeedsValidDate_refuted
    bug := some "datetime-fromisoformat-midnight-day-zero" },
  { id := "datetime-date-fromiso-ten-chars", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromisoformat", "_parse_isoformat_date", "C parse_isoformat_date"]
    statement := "If date.fromisoformat(s) succeeds for a 10-character s then s[4] == '-' (only YYYY-MM-DD and YYYY-Www-D have 10 characters), in both twins."
    source := "date.fromisoformat docs (any valid ISO 8601 format)", status := .refuted
    prop := ``DateFromisoTenChars, thm := some ``dateFromisoTenChars_refuted
    bug := some "datetime-date-fromisoformat-ignores-trailing-chars" }
]

end PyLean.Datetime
