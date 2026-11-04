import PyLean.Registry
import PyLean.Datetime.Diff
import PyLean.Datetime.DeltaProps
import PyLean.Datetime.CalendarProps
import PyLean.Datetime.IsoCalProps
import PyLean.Datetime.IsoRefute
import PyLean.Datetime.IsoRoundtrip
import PyLean.Datetime.ObjProps
import PyLean.Datetime.DateProps
import PyLean.Datetime.TzProps
import PyLean.Datetime.TimeProps
import PyLean.Datetime.DtProps
import PyLean.Datetime.CmpProps
import PyLean.Datetime.Refute2
import PyLean.Datetime.MiscProps
import PyLean.Datetime.OpenProps
import PyLean.Datetime.ChangedProps
import PyLean.Datetime.ZoneRuleProps
import PyLean.Datetime.ZoneLoadProps
import PyLean.Datetime.ZoneProps
import PyLean.Datetime.ZoneCacheErrProps
import PyLean.Datetime.ZoneCacheIdProps
import PyLean.Datetime.ZoneCacheEqProps
import PyLean.Datetime.ZoneCacheSubProps
import PyLean.Datetime.TwinsProps
import PyLean.Datetime.FmtTwinsProps
import PyLean.Datetime.FloatProps
import PyLean.Datetime.IsoFormsProps
import PyLean.Datetime.IndexProps
import PyLean.Datetime.IsoTimeProps
import PyLean.Datetime.WrapScanProps
import PyLean.Datetime.DeltaStrProps

import PyLean.Datetime.EdgeProps
import PyLean.Datetime.Twins2Props
/-!
`Lib/_pydatetime.py`, `Modules/_datetimemodule.c` and `Lib/_strptime.py`, CPython 3.15.2.

Both twins of every class are modelled over ints: `timedelta`, `date`, `time`, `datetime`,
`timezone`, `tzinfo` through an abstract method table (`TzEnv`), comparison, hash, pickle,
`strftime` up to the call of `time.strftime`, `strptime` from `found.groupdict()` on, and
`fromisoformat`. Float paths, the OS clock and the local time zone are not modelled yet.
-/

namespace PyLean.Datetime

open PyLean.Registry

def entries : List Entry := [
  { id := "datetime-ordinal-roundtrip", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromordinal", "date.toordinal", "_ymd2ord", "_ord2ymd", "_is_leap", "_days_before_year", "_days_in_month", "_days_before_month", "_check_date_fields", "C datetime_date_fromordinal_impl", "C date_toordinal", "C ord_to_ymd", "C ymd_to_ord", "C is_leap", "C days_in_month", "C days_before_month", "C days_before_year", "C check_date_args"]
    statement := "For every date d, date.fromordinal(d.toordinal()) == d, in both the C and the Python implementation."
    source := "date.toordinal docs (inverse of fromordinal); invariant", status := .proven
    prop := ``FromordinalToordinal, thm := some ``fromordinalToordinal_proven },
  { id := "datetime-toordinal-roundtrip", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromordinal", "date.toordinal", "_ord2ymd", "_ymd2ord", "C ord_to_ymd", "C ymd_to_ord"]
    statement := "For every 1 <= n <= date.max.toordinal(), date.fromordinal(n) returns the same valid date in both twins, and its toordinal() is n."
    source := "date.fromordinal docs; invariant", status := .proven
    prop := ``ToordinalFromordinal, thm := some ``toordinalFromordinal_proven },
  { id := "datetime-date-add-timedelta", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.__add__", "_ymd2ord", "_ord2ymd", "_check_date_fields", "C add_date_timedelta", "C date_add", "C normalize_y_m_d", "C normalize_date", "C ord_to_ymd", "C ymd_to_ord"]
    statement := "For every date d and timedelta t: if d.toordinal() + t.days is in 1..MAXORDINAL, C and Python both return the same valid date with that ordinal; otherwise both raise OverflowError."
    source := "date + timedelta docs (\"date2 is moved forward ... timedelta.days days\"); C/Python twins", status := .proven
    prop := ``DateAddTimedelta, thm := some ``dateAddTimedelta_proven },
  { id := "datetime-isocalendar-roundtrip", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.isocalendar", "date.fromisocalendar", "_isoweek_to_gregorian", "_isoweek1monday", "C date_isocalendar", "C datetime_date_fromisocalendar_impl", "C iso_week1_monday", "C weekday"]
    statement := "For every date d, date.fromisocalendar(*d.isocalendar()) == d, in both twins."
    source := "date.fromisocalendar docstring (\"inverse of the date.isocalendar() function\")", status := .proven
    prop := ``FromisocalendarIsocalendar, thm := some ``fromisocalendarIsocalendar_proven },
  { id := "datetime-fromisocalendar-exact", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromisocalendar", "date.isocalendar", "_isoweek_to_gregorian", "_isoweek1monday"]
    statement := "date.fromisocalendar(Y, W, D) succeeds only for valid ISO triples (week 53 only in years with 53 ISO weeks) and the result's isocalendar() is (Y, W, D)."
    source := "date.fromisocalendar docstring; ISO 8601 week rules", status := .proven
    prop := ``FromisocalendarExact, thm := some ``fromisocalendarExact_proven },
  { id := "datetime-fromisocalendar-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromisocalendar", "_isoweek_to_gregorian"]
    statement := "For all ints Y, W, D, C and Python date.fromisocalendar(Y, W, D) return the same date or both raise ValueError."
    source := "C/Python twins", status := .refuted
    prop := ``FromisocalendarTwins, thm := some ``fromisocalendarTwins_refuted
    bug := some "datetime-fromisocalendar-overflow-class"
    notes := "fromisocalendar(2**31, 1, 1): OverflowError from the clinic conversion in C, ValueError in Python. New in 3.15: the 3.14 C code converted it to ValueError." },
  { id := "datetime-fromisocalendar-twins-cint", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromisocalendar", "_isoweek_to_gregorian", "C datetime_date_fromisocalendar_impl"]
    statement := "For all C ints Y, W, D, C and Python date.fromisocalendar(Y, W, D) return the same date or both raise ValueError."
    source := "C/Python twins", status := .proven
    prop := ``FromisocalendarTwinsCInt, thm := some ``fromisocalendarTwinsCInt_proven },
  { id := "datetime-timedelta-ctor-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__new__", "C delta_new_impl", "C accum", "C microseconds_to_delta_ex", "C new_delta_ex", "C check_delta_day_range", "C checked_divmod", "C normalize_pair", "C normalize_d_s_us", "C divmod"]
    statement := "For all int arguments days, seconds, microseconds, milliseconds, minutes, hours, weeks, C and Python timedelta(...) return the same value or raise the same exception class (OverflowError)."
    source := "C/Python twins", status := .proven
    prop := ``TimedeltaCtorTwins, thm := some ``timedeltaCtorTwins_proven
    notes := "Float arguments wait for the binary64 model." },
  { id := "datetime-timedelta-ctor-exact", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__new__", "timedelta.days", "timedelta.seconds", "timedelta.microseconds"]
    statement := "timedelta(...) with int arguments returns the normalized value (0 <= seconds < 86400, 0 <= microseconds < 10**6, |days| <= 999999999) equal to the sum of the arguments exactly when that sum is within [timedelta.min, timedelta.max], and raises OverflowError otherwise."
    source := "timedelta docs (normalization, \"If the normalized value of days lies outside the indicated range, OverflowError is raised\")", status := .proven
    prop := ``TimedeltaCtorExact, thm := some ``timedeltaCtorExact_proven },
  { id := "datetime-timedelta-ops-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__add__", "timedelta.__sub__", "timedelta.__neg__", "timedelta.__abs__", "timedelta.__mul__", "timedelta.__floordiv__", "timedelta.__truediv__", "timedelta.__mod__", "timedelta.__divmod__", "timedelta._to_microseconds", "_divide_and_round", "C delta_add", "C delta_subtract", "C delta_negative", "C delta_abs", "C delta_multiply", "C delta_divide", "C delta_truedivide", "C delta_remainder", "C delta_divmod", "C multiply_int_timedelta", "C divide_timedelta_int", "C divide_timedelta_timedelta", "C truedivide_timedelta_int", "C divide_nearest", "C delta_to_microseconds"]
    statement := "For all valid timedeltas a, b and every int k, a+b, a-b, -a, abs(a), a*k, a//k, a/k, a//b, a%b and divmod(a, b) agree between C and Python in value and exception class."
    source := "C/Python twins", status := .proven
    prop := ``TimedeltaOpsTwins, thm := some ``timedeltaOpsTwins_proven
    notes := "Float multipliers and timedelta/timedelta (a float) wait for the binary64 model." },
  { id := "datetime-divide-and-round", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_divide_and_round", "C divide_nearest"]
    statement := "For all ints a, b: _divide_and_round(a, b) equals C divide_nearest(a, b) (_PyLong_DivmodNear); for b != 0 it is a / b rounded to the nearest int with ties to even, for b == 0 it raises ZeroDivisionError."
    source := "_divide_and_round docstring; C/Python twins", status := .proven
    prop := ``DivideAndRound, thm := some ``divideAndRound_proven },
  { id := "datetime-timedelta-divmod", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__divmod__", "timedelta.__floordiv__", "timedelta.__mod__", "timedelta._to_microseconds"]
    statement := "For valid timedeltas a, b with b != 0, divmod(a, b) == (a // b, a % b) with q*b + r == a and r zero or of b's sign with |r| < |b|; for b == 0 it raises ZeroDivisionError."
    source := "timedelta docs (q, r = divmod(t1, t2)); invariant", status := .proven
    prop := ``TimedeltaDivmod, thm := some ``timedeltaDivmod_proven },
  { id := "datetime-timedelta-compare", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__eq__", "timedelta.__le__", "timedelta.__lt__", "timedelta.__ge__", "timedelta.__gt__", "timedelta._cmp", "timedelta._getstate", "_cmp", "C delta_cmp", "C delta_richcompare", "C diff_to_bool"]
    statement := "For valid timedeltas a, b and every operator op, a op b in Python and in C is the comparison of a._to_microseconds() and b._to_microseconds() by op."
    source := "C/Python twins; timedelta docs (comparison)", status := .proven
    prop := ``TimedeltaCompare, thm := some ``timedeltaCompare_proven },
  { id := "datetime-timedelta-bool-hash", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__bool__", "timedelta.__hash__", "C delta_bool", "C delta_hash", "C delta_getstate"]
    statement := "bool(t) is t != timedelta(0); hash(t) is the hash of the state tuple (days, seconds, microseconds) in both twins, so two valid timedeltas have the same hash key exactly when they are equal."
    source := "timedelta docs; __hash__ contract", status := .proven
    prop := ``TimedeltaBoolHash, thm := some ``timedeltaBoolHash_proven },
  { id := "datetime-timedelta-reduce", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__reduce__", "timedelta._getstate", "C delta_reduce", "C delta_getstate"]
    statement := "timedelta(*t.__reduce__()[1]) == t in both twins."
    source := "pickle contract", status := .proven
    prop := ``TimedeltaReduce, thm := some ``timedeltaReduce_proven },
  { id := "datetime-timedelta-pos", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__pos__", "C delta_positive"]
    statement := "For every valid timedelta t, Python's +t is t itself; C's +t is a new timedelta equal to t, except that a zero t is the zero_delta singleton and +t is t."
    source := "C/Python twins (identity is observable: +t is t)", status := .proven
    prop := ``TimedeltaPos, thm := some ``timedeltaPos_proven },
  { id := "datetime-timedelta-rsub", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__rsub__", "C delta_subtract"]
    statement := "For valid timedeltas a, b: if -a is a timedelta, a.__rsub__(b) agrees between the twins; otherwise Python raises OverflowError."
    source := "C/Python twins", status := .proven
    prop := ``TimedeltaRsub, thm := some ``timedeltaRsub_proven
    notes := "The excluded case is on record as datetime-timedelta-rsub-twins." },
  { id := "datetime-timedelta-rsub-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__rsub__"]
    statement := "For all valid timedeltas a, b, a.__rsub__(b) agrees between C and Python."
    source := "C/Python twins", status := .refuted
    prop := ``TimedeltaRsubTwins, thm := some ``timedeltaRsubTwins_refuted
    bug := some "datetime-pydatetime-rsub-negate-overflow"
    notes := "timedelta.max.__rsub__(timedelta.max): Python computes -self + other and -self overflows; C returns timedelta(0)." },
  { id := "datetime-timezone-range", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timezone.__new__", "C new_timezone"]
    statement := "timezone(offset) accepts exactly the offsets strictly between -24h and 24h (returning that offset) and otherwise raises ValueError, identically in both twins."
    source := "timezone docs (\"strictly between -timedelta(hours=24) and timedelta(hours=24)\")", status := .proven
    prop := ``TimezoneRange, thm := some ``timezoneRange_proven },
  { id := "datetime-timezone-name", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timezone.__str__", "timezone.tzname", "timezone._name_from_offset", "C timezone_str", "C timezone_tzname"]
    statement := "str(tz) and tz.tzname(dt) are the same text in both twins for every timezone."
    source := "C/Python twins", status := .proven
    prop := ``TimezoneName, thm := some ``timezoneName_proven },
  { id := "datetime-tzinfo-base", pyFile := "Lib/_pydatetime.py"
    pyFns := ["tzinfo.tzname", "tzinfo.utcoffset", "tzinfo.dst", "C tzinfo_nogo", "C tzinfo_tzname", "C tzinfo_utcoffset", "C tzinfo_dst"]
    statement := "The abstract tzinfo methods raise NotImplementedError in both twins."
    source := "tzinfo docs", status := .proven
    prop := ``TzinfoBase, thm := some ``tzinfoBase_proven },
  { id := "datetime-timezone-methods", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timezone.utcoffset", "timezone.dst", "timezone.__eq__", "timezone.__hash__", "timezone.__getinitargs__", "C timezone_utcoffset", "C timezone_dst", "C timezone_richcompare", "C timezone_hash", "C timezone_getinitargs"]
    statement := "For every timezone: utcoffset is its offset, dst is None, == compares offsets only and agrees between the twins, ordering is NotImplemented, equal timezones hash alike, __getinitargs__ is (offset, name)."
    source := "timezone docs; C/Python twins", status := .proven
    prop := ``TimezoneMethods, thm := some ``timezoneMethods_proven },
  { id := "datetime-timezone-new", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timezone.__new__", "timezone._create", "C timezone_new_impl", "C create_timezone", "C new_timezone"]
    statement := "timezone(offset[, name]) agrees between the twins for every valid timedelta and name; a zero offset without a name is timezone.utc."
    source := "C/Python twins; timezone docs", status := .proven
    prop := ``TimezoneNew, thm := some ``timezoneNew_proven },
  { id := "datetime-time-offsets", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.utcoffset", "time.dst", "_check_utc_offset", "C call_tzinfo_method", "C call_utcoffset", "C call_dst", "C get_tzinfo_member", "C time_utcoffset", "C time_dst"]
    statement := "time.utcoffset() and time.dst() agree between the twins for every tzinfo, and an offset returned is strictly inside 24 hours."
    source := "tzinfo docs; C/Python twins", status := .proven
    prop := ``TimeOffsets, thm := some ``timeOffsets_proven },
  { id := "datetime-datetime-offsets", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.utcoffset", "datetime.dst", "_check_utc_offset", "C call_tzinfo_method", "C call_utcoffset", "C call_dst", "C get_tzinfo_member", "C datetime_utcoffset", "C datetime_dst"]
    statement := "datetime.utcoffset() and datetime.dst() agree between the twins for every tzinfo, and an offset returned is strictly inside 24 hours."
    source := "tzinfo docs; C/Python twins", status := .proven
    prop := ``DatetimeOffsets, thm := some ``datetimeOffsets_proven },
  { id := "datetime-tzname-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.tzname", "datetime.tzname", "_check_tzname", "C time_tzname", "C datetime_tzname", "C call_tzname"]
    statement := "tzname() agrees between the twins in value or exception class for every tzinfo."
    source := "C/Python twins", status := .proven
    prop := ``TznameTwins, thm := some ``tznameTwins_proven },
  { id := "datetime-time-repr", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.__repr__", "_get_class_module", "C time_repr", "C append_keyword_tzinfo", "C append_keyword_fold"]
    statement := "repr(time) is the same text in both twins."
    source := "C/Python twins", status := .proven
    prop := ``TimeRepr, thm := some ``timeRepr_proven },
  { id := "datetime-datetime-repr", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.__repr__", "_get_class_module", "C datetime_repr", "C append_keyword_tzinfo", "C append_keyword_fold"]
    statement := "repr(datetime) is the same text in both twins unless both fold and tzinfo are set."
    source := "C/Python twins", status := .proven
    prop := ``DatetimeRepr, thm := some ``datetimeRepr_proven
    notes := "With fold=1 and a tzinfo the keywords come in a different order: C prints fold first, Python tzinfo first. Cosmetic, not filed." },
  { id := "datetime-time-isoformat-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.isoformat", "time._tzstr", "_format_time", "_format_offset", "C datetime_time_isoformat_impl", "C time_str", "C format_utcoffset"]
    statement := "time.isoformat(timespec) and str(time) agree between the twins for every timespec and tzinfo."
    source := "C/Python twins", status := .proven
    prop := ``TimeIsoformatTwins, thm := some ``timeIsoformatTwins_proven },
  { id := "datetime-datetime-isoformat-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.isoformat", "datetime.__str__", "_format_time", "_format_offset", "C datetime_datetime_isoformat_impl", "C datetime_str", "C format_utcoffset"]
    statement := "datetime.isoformat(sep, timespec) agrees between the twins for every separator, timespec and tzinfo; str(datetime) is its sep=\" \" case."
    source := "C/Python twins", status := .proven
    prop := ``DatetimeIsoformatTwins, thm := some ``datetimeIsoformatTwins_proven },
  { id := "datetime-replace-combine", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.replace", "datetime.replace", "datetime.combine", "datetime.date", "datetime.time", "datetime.timetz", "C datetime_time_replace_impl", "C datetime_datetime_replace_impl", "C datetime_datetime_combine_impl", "C datetime_getdate", "C datetime_gettime", "C datetime_gettimetz"]
    statement := "t.replace() == t, d.replace() == d, datetime.combine(d.date(), d.timetz()) == d, datetime.combine(d.date(), d.time(), d.tzinfo) == d, and d.time() is naive."
    source := "datetime docs", status := .proven
    prop := ``ReplaceCombine, thm := some ``replaceCombine_proven },
  { id := "datetime-time-pickle", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time._getstate", "time.__setstate", "time.__reduce_ex__", "time.__reduce__", "C time_getstate", "C time_from_pickle", "C datetime_time___reduce_ex___impl", "C datetime_time___reduce___impl"]
    statement := "time(*t.__reduce_ex__(p)[1]) == t in both twins, with fold kept above protocol 3 and dropped otherwise."
    source := "pickle contract; PEP 495", status := .proven
    prop := ``TimePickle, thm := some ``timePickle_proven },
  { id := "datetime-datetime-pickle", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime._getstate", "datetime.__setstate", "datetime.__reduce_ex__", "datetime.__reduce__", "C datetime_getstate", "C datetime_from_pickle", "C datetime_datetime___reduce_ex___impl", "C datetime_datetime___reduce___impl"]
    statement := "datetime(*d.__reduce_ex__(p)[1]) == d in both twins, with fold kept above protocol 3 and dropped otherwise."
    source := "pickle contract; PEP 495", status := .proven
    prop := ``DatetimePickle, thm := some ``datetimePickle_proven },
  { id := "datetime-time-ctor", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.__new__", "_check_time_fields", "_check_tzinfo_arg", "C time_new", "C datetime_time_impl", "C new_time_ex2", "C check_time_args", "C check_tzinfo_subclass"]
    statement := "time(h, m, s, us, tz, fold=f) with C-int fields agrees between the twins."
    source := "C/Python twins", status := .proven
    prop := ``TimeCtorInt, thm := some ``timeCtorInt_proven
    notes := "Fields outside int: OverflowError versus ValueError is the rejected class of gh-158778. fold is on record as datetime-time-ctor-fold-twins." },
  { id := "datetime-time-ctor-fold-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.__new__", "_check_time_fields", "C time_new"]
    statement := "time(h, m, s, us, tz, fold=f) with C-int h, m, s, us and any int fold agrees between the twins."
    source := "C/Python twins", status := .refuted
    prop := ``TimeCtorFoldTwins, thm := some ``timeCtorFoldTwins_refuted
    bug := some "datetime-ctor-fold-overflow-class"
    notes := "fold=2**31: OverflowError from the clinic conversion in C, ValueError in Python. Only the exception class differs." },
  { id := "datetime-datetime-ctor", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.__new__", "_check_date_fields", "_check_time_fields", "_check_tzinfo_arg", "C datetime_new", "C datetime_datetime_impl", "C new_datetime_ex2", "C check_date_args", "C check_time_args", "C check_tzinfo_subclass"]
    statement := "datetime(y, m, d, h, mi, s, us, tz, fold=f) with C-int fields agrees between the twins."
    source := "C/Python twins", status := .proven
    prop := ``DatetimeCtorInt, thm := some ``datetimeCtorInt_proven
    notes := "Fields outside int: gh-158778. fold is on record as datetime-datetime-ctor-fold-twins." },
  { id := "datetime-datetime-ctor-fold-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.__new__", "_check_date_fields", "_check_time_fields", "C datetime_new"]
    statement := "datetime(y, m, d, h, mi, s, us, tz, fold=f) with C-int fields and any int fold agrees between the twins."
    source := "C/Python twins", status := .refuted
    prop := ``DatetimeCtorFoldTwins, thm := some ``datetimeCtorFoldTwins_refuted
    bug := some "datetime-ctor-fold-overflow-class"
    notes := "fold=2**31: OverflowError from the clinic conversion in C, ValueError in Python. Only the exception class differs." },
  { id := "datetime-time-compare-base", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.__eq__", "time.__le__", "time.__lt__", "time.__ge__", "time.__gt__", "time._cmp", "_cmp", "C time_richcompare", "C diff_to_bool"]
    statement := "time comparison with the same tzinfo object agrees between the twins, field by field."
    source := "C/Python twins", status := .proven
    prop := ``TimeCompareBase, thm := some ``timeCompareBase_proven },
  { id := "datetime-time-compare-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.__eq__", "time._cmp", "C time_richcompare"]
    statement := "For all valid times and tzinfos, C and Python time comparison agree."
    source := "C/Python twins", status := .refuted
    prop := ``TimeCompareTwins, thm := some ``timeCompareTwins_refuted
    bug := some "datetime-time-subminute-offset"
    notes := "Python floors offsets to minutes; C drops microseconds. Fixed on main (gh-99772)." },
  { id := "datetime-time-hash-total", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.__hash__"]
    statement := "hash(time) returns a value for every time with a valid offset."
    source := "no internal error leaking", status := .refuted
    prop := ``TimeHashTotal, thm := some ``timeHashTotal_refuted
    bug := some "datetime-time-subminute-offset"
    notes := "_pydatetime raises AssertionError('whole minute'). Fixed on main." },
  { id := "datetime-time-eq-hash", pyFile := "Lib/_pydatetime.py"
    pyFns := ["C time_hash", "C time_richcompare"]
    statement := "Equal time objects have equal hashes in C."
    source := "__hash__ contract", status := .refuted
    prop := ``TimeEqHash, thm := some ``timeEqHash_refuted
    bug := some "datetime-time-subminute-offset"
    notes := "Offsets of 1 and 2 microseconds. Fixed on main." },
  { id := "datetime-date-compare", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.__eq__", "date.__le__", "date.__lt__", "date.__ge__", "date.__gt__", "date._cmp", "_cmp", "C date_richcompare", "C diff_to_bool"]
    statement := "For valid dates a, b and every operator op, a op b in Python and in C is the comparison of a.toordinal() and b.toordinal() by op; comparing with a datetime is NotImplemented in both."
    source := "date docs; C/Python twins", status := .proven
    prop := ``DateCompare, thm := some ``dateCompare_proven },
  { id := "datetime-date-hash", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.__hash__", "date._getstate", "C date_hash", "C generic_hash", "C date_getstate"]
    statement := "In each twin two valid dates have the same hash key exactly when they are equal; Python hashes the 1-tuple _getstate(), C the state bytes."
    source := "__hash__ contract", status := .proven
    prop := ``DateHash, thm := some ``dateHash_proven },
  { id := "datetime-date-weekday", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.weekday", "date.isoweekday", "C date_weekday", "C date_isoweekday", "C weekday"]
    statement := "weekday() and isoweekday() agree between the twins, isoweekday() is weekday() + 1 and is the third field of isocalendar()."
    source := "date docs", status := .proven
    prop := ``DateWeekday, thm := some ``dateWeekday_proven },
  { id := "datetime-date-subtract", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.__sub__", "C date_subtract", "C add_date_timedelta"]
    statement := "date - date is the ordinal difference in both twins; date - timedelta agrees between the twins in value and exception class."
    source := "date docs; C/Python twins", status := .proven
    prop := ``DateSubtract, thm := some ``dateSubtract_proven },
  { id := "datetime-date-replace", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.replace", "date.__new__", "C datetime_date_replace", "C datetime_date_replace_impl", "C new_date_subclass_ex", "C new_date_ex", "C check_date_args"]
    statement := "d.replace() == d in both twins and d.replace(None, None, None) == d in Python; with no explicit None and C-int ints, replace agrees between the twins for every int or other argument."
    source := "date docs; C/Python twins", status := .proven
    prop := ``DateReplace, thm := some ``dateReplace_proven
    notes := "An explicit None is on record as datetime-date-replace-twins; ints beyond C int are gh-158778's class." },
  { id := "datetime-date-replace-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.replace"]
    statement := "date.replace agrees between the twins for every combination of omitted, None, int and other arguments."
    source := "C/Python twins", status := .refuted
    prop := ``DateReplaceTwins, thm := some ``dateReplaceTwins_refuted
    bug := some "datetime-pydatetime-none-as-omitted"
    notes := "date(2020, 1, 1).replace(year=None): Python keeps the year, C raises TypeError." },
  { id := "datetime-date-timetuple", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.timetuple", "_build_struct_time", "C date_timetuple", "C build_struct_time"]
    statement := "date.timetuple() agrees between the twins and is (y, m, d, 0, 0, 0, weekday, yday, -1)."
    source := "date.timetuple docs", status := .proven
    prop := ``DateTimetuple, thm := some ``dateTimetuple_proven },
  { id := "datetime-ctime", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.ctime", "datetime.ctime", "C date_ctime", "C datetime_ctime", "C format_ctime"]
    statement := "ctime() is the same text in both twins for every valid date and any time fields."
    source := "C/Python twins", status := .proven
    prop := ``DateCtime, thm := some ``dateCtime_proven },
  { id := "datetime-date-repr", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.__repr__", "_get_class_module", "C date_repr"]
    statement := "repr(date) agrees between the twins for the base class and for every subclass whose __qualname__ is its __name__ and whose module is not named datetime."
    source := "C/Python twins", status := .proven
    prop := ``DateRepr, thm := some ``dateRepr_proven
    notes := "Other classes are on record as datetime-date-repr-twins." },
  { id := "datetime-date-repr-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.__repr__", "_get_class_module", "C date_repr"]
    statement := "repr(date) is the same text in both twins for every class."
    source := "C/Python twins", status := .refuted
    prop := ``DateReprTwins, thm := some ``dateReprTwins_refuted
    bug := some "datetime-repr-qualname-vs-tp-name"
    notes := "A nested subclass: Python prints __qualname__ (Outer.D), C tp_name (D)." },
  { id := "datetime-date-pickle", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date._getstate", "date.__setstate", "date.__reduce__", "C date_getstate", "C date_from_pickle", "C date_reduce"]
    statement := "date(*d.__reduce__()[1]) == d in both twins."
    source := "pickle contract", status := .proven
    prop := ``DatePickle, thm := some ``datePickle_proven },
  { id := "datetime-date-ctor", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.__new__", "_check_date_fields", "C date_new", "C datetime_date_impl", "C new_date_ex", "C check_date_args"]
    statement := "date(y, m, d) with C-int fields agrees between the twins."
    source := "C/Python twins", status := .proven
    prop := ``DateCtorInt, thm := some ``dateCtorInt_proven
    notes := "Fields outside int: gh-158778." },
  { id := "datetime-date-ctor-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.__new__", "C date_new"]
    statement := "date(*args) agrees between the twins for every positional argument list whose ints fit a C int."
    source := "C/Python twins", status := .refuted
    prop := ``DateNewTwins, thm := some ``dateNewTwins_refuted
    bug := some "datetime-date-pickle-test-month-none"
    notes := "date(b'\\x07\\xd0\\x01\\x01', None): Python unpickles (its test is month is None), C raises TypeError (its test is one positional argument)." },
  { id := "datetime-date-isoformat-text", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.isoformat", "C date_isoformat"]
    statement := "For every valid date, date.isoformat() is the ten characters YYYY-MM-DD (four year digits, '-', two month digits, '-', two day digits), and C date_isoformat gives the same text."
    source := "date.isoformat docstring (\"This is 'YYYY-MM-DD'.\"); C/Python twins", status := .proven
    prop := ``DateIsoformatText, thm := some ``dateIsoformatText_proven },
  { id := "datetime-format-time-text", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_format_time", "C datetime_time_isoformat_impl"]
    statement := "For valid hh, mm, ss, us and every timespec, _format_time is HH, HH:MM, HH:MM:SS, HH:MM:SS.sss (us // 1000) or HH:MM:SS.ffffff, auto choosing microseconds exactly when us != 0, and the C time formatter gives the same text."
    source := "time.isoformat docs (timespec); C/Python twins", status := .proven
    prop := ``FormatTimeText, thm := some ``formatTimeText_proven },
  { id := "datetime-format-offset-text", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_format_offset", "C format_utcoffset"]
    statement := "For every separator and every utcoffset() result (None, or a valid offset strictly inside +-24h), _format_offset is '' for None and otherwise +-HH sep MM, then sep SS when seconds or microseconds are nonzero, then .ffffff when microseconds are nonzero; C format_utcoffset gives the same text."
    source := "utcoffset/isoformat docs; C/Python twins", status := .proven
    prop := ``FormatOffsetText, thm := some ``formatOffsetText_proven },
  { id := "datetime-timespec-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_format_time", "C datetime_time_isoformat_impl"]
    statement := "isoformat(timespec=x) refuses the same arguments with the same exception class in both twins."
    source := "C/Python twins; time.isoformat docs (ValueError for an invalid timespec)", status := .refuted
    prop := ``TimespecTwins, thm := some ``timespecTwins_refuted
    bug := some "datetime-timespec-non-str-class"
    notes := "time(1).isoformat(timespec=1): ValueError in Python, TypeError in C." },
  { id := "datetime-timespec-str-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_format_time", "C datetime_time_isoformat_impl", "C datetime_time_isoformat", "C datetime_datetime_isoformat"]
    statement := "For every str timespec the twins give the same spec or the same ValueError, message included."
    source := "C/Python twins", status := .refuted
    prop := ``TimespecStrTwins, thm := some ``timespecStrTwins_refuted
    bug := some "datetime-timespec-non-str-class"
    notes := "time(1).isoformat(timespec='auto\\0'): Python 'Unknown timespec value', C's clinic str converter 'embedded null character' (clinic/_datetimemodule.c.h:965-968)." },
  { id := "datetime-timespec-str", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_format_time", "C datetime_time_isoformat_impl", "C datetime_time_isoformat", "C datetime_datetime_isoformat"]
    statement := "For every str timespec without NUL or lone surrogate the twins give the same result, the spec its documented name selects or ValueError('Unknown timespec value'); with a NUL Python raises 'Unknown timespec value' and C 'embedded null character' (both ValueError); with a lone surrogate Python raises ValueError and C UnicodeEncodeError; an unhashable non-str is a TypeError in both."
    source := "C/Python twins; time.isoformat docs (timespec values)", status := .proven
    prop := ``TimespecStr, thm := some ``timespecStr_proven },
  { id := "datetime-timedelta-float-ops", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__mul__", "timedelta.__truediv__", "_divide_and_round", "C multiply_truedivide_timedelta_float", "C get_float_as_integer_ratio", "C divide_nearest"]
    statement := "For every valid timedelta t and float x, t * x and t / x agree between the twins; for finite x = n/d (as_integer_ratio), t * x is t_us * n / d and t / x is t_us * d / n microseconds rounded half to even (OverflowError out of range, ZeroDivisionError for x == 0); infinities raise OverflowError and NaN ValueError."
    source := "timedelta docs (t1 * f, t1 / f: rounded using round-half-to-even); C/Python twins", status := .proven
    prop := ``TimedeltaFloatOps, thm := some ``timedeltaFloatOps_proven },
  { id := "datetime-timedelta-float-ratio-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__mul__", "timedelta.__truediv__", "C multiply_truedivide_timedelta_float", "C get_float_as_integer_ratio"]
    statement := "For every valid timedelta t and every float operand, a float subclass with its own as_integer_ratio included, t * x and t / x agree between the twins."
    source := "C/Python twins", status := .refuted
    prop := ``TimedeltaFloatRatioTwins, thm := some ``timedeltaFloatRatioTwins_refuted
    bug := some "datetime-timedelta-float-ratio-not-tuple"
    notes := "A float subclass whose as_integer_ratio returns [3, 2]: Python unpacks it, C's get_float_as_integer_ratio raises TypeError for a non-tuple." },
  { id := "datetime-timedelta-float-ratio", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__mul__", "timedelta.__truediv__", "_divide_and_round", "C multiply_truedivide_timedelta_float", "C get_float_as_integer_ratio", "C divide_nearest"]
    statement := "For every valid timedelta t: a plain float operand is the float.as_integer_ratio model; for a float subclass whose as_integer_ratio returns a 2-tuple (n, d) of ints the twins agree and t * x is t_us * n / d (t / x is d * t_us / n) rounded half to even; a 2-list gives the same in Python and TypeError in C; a tuple of another length is ValueError in both, a list of another length ValueError in Python and TypeError in C; a non-iterable is TypeError in both; an exception of the method propagates in both."
    source := "C/Python twins; timedelta docs (round-half-to-even)", status := .proven
    prop := ``TimedeltaFloatRatio, thm := some ``timedeltaFloatRatio_proven },
  { id := "datetime-timedelta-truediv-delta", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__truediv__", "C truedivide_timedelta_timedelta"]
    statement := "For valid timedeltas a, b with b != 0, a / b is the correctly rounded double of a_us / b_us in both twins."
    source := "timedelta docs (t2 / t3 returns a float)", status := .open
    prop := ``TimedeltaTruedivDelta
    notes := "Both twins reach long_true_divide, mirrored in LongObj.trueDivide; its correct rounding is the open longobj-true-divide-rounds." },
  { id := "datetime-date-format", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.__format__", "C datetime_date___format__", "C datetime_date___format___impl"]
    statement := "For every fmt and every result of the str and strftime methods, format(d, fmt) agrees between the twins: TypeError for a non-str, str(d) for '', d.strftime(fmt) otherwise."
    source := "date.__format__ docs; C/Python twins", status := .proven
    prop := ``DateFormat, thm := some ``dateFormat_proven },
  { id := "datetime-date-strptime", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.strptime", "C datetime_date_strptime_impl"]
    statement := "For every parse, date.strptime(s, fmt) is date(*(time.strptime(s, fmt)[0:3])) through the date constructor, exceptions included; for a parse with a valid date, no offset and second 60 or 61 it returns the date while datetime.strptime raises ValueError; and '2024 1 2 60' with %Y %m %d %S is such a parse."
    source := "date.strptime docs; _strptime_datetime_date", status := .proven
    prop := ``DateStrptime, thm := some ``dateStrptime_proven },
  { id := "datetime-parse-isodate-forms", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_parse_isoformat_date", "_read_isoformat_component", "_isoweek_to_gregorian"]
    statement := "For all ASCII digits, _parse_isoformat_date parses YYYYMMDD to its fields, YYYY-Www-D, YYYYWwwD, YYYY-Www and YYYYWww to _isoweek_to_gregorian(Y, W, D or 1), and raises 'Inconsistent use of dash separator' when only one of the two separators is a dash (month and week forms)."
    source := "date.fromisoformat docs (ISO 8601 formats); _parse_isoformat_date", status := .proven
    prop := ``ParseIsoDateForms, thm := some ``parseIsoDateForms_proven },
  { id := "datetime-parse-isodate-refusals", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_parse_isoformat_date"]
    statement := "For every string, _parse_isoformat_date raises 'Invalid isoformat string' when its length is not 7, 8 or 10, and when it is not ASCII."
    source := "_parse_isoformat_date", status := .proven
    prop := ``ParseIsoDateRefusals, thm := some ``parseIsoDateRefusals_proven },
  { id := "datetime-is-ascii-digit", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_is_ascii_digit"]
    statement := "For every character c, _is_ascii_digit(c) holds exactly when c is U+0030..U+0039, so no Unicode digit counts."
    source := "the function's name and body (c in '0123456789')", status := .proven
    prop := ``IsAsciiDigit, thm := some ``isAsciiDigit_proven },
  { id := "datetime-find-sep-forms", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_find_isoformat_datetime_separator", "_is_ascii_digit"]
    statement := "For all digits, any separator x and any time text t, _find_isoformat_datetime_separator returns the length of the date part for YYYY-MM-DD, YYYYMMDD, YYYY-Www-D (x outside U+0030..U+0039), YYYY-Www followed by -DD and YYYY-Www (x not a digit or '-'), and raises 'Invalid ISO string' for the nine characters YYYY-Www-."
    source := "datetime.fromisoformat docs; the ambiguity rule at _pydatetime.py:315-323", status := .proven
    prop := ``FindSepForms, thm := some ``findSepForms_proven },
  { id := "datetime-find-sep-week-digits", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_find_isoformat_datetime_separator", "_is_ascii_digit"]
    statement := "For every YYYYWww followed by a run of n ASCII digits and then a non-digit or the end, _find_isoformat_datetime_separator returns 7 for n = 0, 8 for n = 1, and for n >= 2 returns 7 when n is odd and 8 when n is even (idx = 7 + n, :336-353)."
    source := "datetime.fromisoformat docs (YYYYWww, YYYYWwwD); _pydatetime.py:336-353", status := .proven
    prop := ``FindSepWeekDigits, thm := some ``findSepWeekDigits_proven },
  { id := "datetime-date-fromisoformat", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromisoformat", "_parse_isoformat_date"]
    statement := "For every string, date.fromisoformat refuses non-ASCII text ('Argument must be an ASCII str') and lengths other than 7, 8, 10 (ValueError), returns the checked date of an accepted parse, and raises ValueError for a refused parse or an invalid date."
    source := "date.fromisoformat docs", status := .proven
    prop := ``DateFromisoformat, thm := some ``dateFromisoformat_proven },
  { id := "datetime-date-fromisoformat-arg", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromisoformat", "C datetime_date_fromisoformat", "C datetime_date_fromisoformat_impl"]
    statement := "For every argument, date.fromisoformat raises TypeError('Argument must be a str') for a non-str (C: TypeError from the clinic converter), ValueError('Argument must be an ASCII str') for a str with a lone surrogate (C: ValueError), and is the str parser otherwise."
    source := "date.fromisoformat docs; C/Python twins", status := .proven
    prop := ``DateFromisoformatArg, thm := some ``dateFromisoformatArg_proven },
  { id := "datetime-parse-hhmmssff-forms", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_parse_hh_mm_ss_ff", "_read_isoformat_component"]
    statement := "For all ASCII digits, _parse_hh_mm_ss_ff parses HH, HH:MM, HHMMSS, HH:MM:SS.ffffff, HH:MM:SS,fff (times 1000) and truncates a seventh fraction digit; it raises 'Invalid time separator' for a non-colon after HH:MM, 'Invalid microsecond separator' for a separator other than . or ,, and 'Non-digit values in fraction'."
    source := "time.fromisoformat docs; _parse_hh_mm_ss_ff", status := .proven
    prop := ``ParseHHMMSSFFForms, thm := some ``parseHHMMSSFFForms_proven },
  { id := "datetime-parse-isotime-forms", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_parse_isoformat_time"]
    statement := "For every ASCII time part t (no -, + or Z, at least 2 characters) and offset text tz: t alone is naive; t + 'Z' is UTC; t + sign + tz is Malformed for len(tz) in (0, 1, 3), UTC for an all-zero offset, sign * ((a*3600 + b*60 + d)*10**6 + u) microseconds for a valid one, and an error_from_tz ValueError with no tzinfo for an out-of-range one; t + 'Z' + nonempty tz is Malformed; hour 24 becomes 0 with became_next_day only for 24:00[:00[.0]], otherwise error_from_components; parse errors of t propagate."
    source := "time.fromisoformat docs; _pydatetime.py:453-519", status := .proven
    prop := ``ParseIsoTimeForms, thm := some ``parseIsoTimeForms_proven },
  { id := "datetime-parse-hhmmssff-fraction", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_parse_hh_mm_ss_ff", "_read_isoformat_component"]
    statement := "For all ASCII digits, HH:MM:SS or HHMMSS followed by '.' or ',' and a nonempty run of k ASCII digits parses to the first min(k, 6) digits times 10**(6 - min(k, 6)) microseconds, which pins every _FRACTION_CORRECTION entry."
    source := "time.fromisoformat docs (fractional seconds); _pydatetime.py:432-449", status := .proven
    prop := ``ParseHHMMSSFFFraction, thm := some ``parseHHMMSSFFFraction_proven },
  { id := "datetime-date-ctor-args", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.__new__", "_check_date_fields", "C date_new", "C datetime_date", "C datetime_date_impl", "C new_date_ex", "C check_date_args", "C date_from_pickle"]
    statement := "date(*args) agrees between the twins for every positional argument list whose second argument is not None, whose ints (given or returned by __index__) fit a C int, and in which no __index__ raises: pickle state, int and __index__ fields, non-int fields, missing or extra arguments."
    source := "C/Python twins", status := .proven
    prop := ``DateNewArgs, thm := some ``dateNewArgs_proven
    notes := "A None second argument is on record as datetime-date-ctor-twins; ints beyond C int are gh-158778's class; a raising __index__ with a missing field is datetime-date-new-index-missing." },
  { id := "datetime-date-sub-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.__sub__", "C date_subtract"]
    statement := "date - x agrees between the twins for every valid right operand: timedelta, date, datetime or another object."
    source := "C/Python twins; date docs (date - date, date - timedelta only)", status := .refuted
    prop := ``DateSubTwins, thm := some ``dateSubTwins_refuted
    bug := some "datetime-pydatetime-date-sub-datetime"
    notes := "date(2020, 1, 2) - datetime(2020, 1, 1): timedelta(days=1) in Python, TypeError in C." },
  { id := "datetime-date-sub-operand", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.__sub__", "C date_subtract", "C add_date_timedelta"]
    statement := "For every valid date and every right operand other than a datetime, date - x agrees between the twins, and another object is NotImplemented in both."
    source := "C/Python twins", status := .proven
    prop := ``DateSubOperand, thm := some ``dateSubOperand_proven },
  { id := "datetime-fromordinal-range", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromordinal", "_ord2ymd", "C datetime_date_fromordinal_impl", "C ord_to_ymd"]
    statement := "date.fromordinal(n) raises ValueError in Python for every int n outside 1..date.max.toordinal(); C raises ValueError for such C ints and OverflowError beyond int; for C ints the twins agree."
    source := "date.fromordinal docs (ValueError unless 1 <= ordinal <= date.max.toordinal())", status := .proven
    prop := ``FromordinalRange, thm := some ``fromordinalRange_proven },
  { id := "datetime-date-fromtimestamp", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromtimestamp", "C date_fromtimestamp"]
    statement := "For every clock and argument, date.fromtimestamp(None) raises TypeError in both twins without consulting the clock, and otherwise both return the checked localtime date of the same time_t."
    source := "date.fromtimestamp docs; C/Python twins", status := .proven
    prop := ``DateFromtimestamp, thm := some ``dateFromtimestamp_proven
    notes := "The clock (time(NULL), localtime(3) and the float-to-time_t path) is an abstract parameter: platform." },
  { id := "datetime-days-in-month", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_days_in_month", "C days_in_month", "C is_leap"]
    statement := "For 1 <= m <= 12, _days_in_month(y, m) is 31, 28 or 29 (Gregorian leap rule), 31, 30, 31, 30, 31, 31, 30, 31, 30, 31; it agrees with C days_in_month for 0 <= y < 2**31, is the step of _days_before_month, and the months sum to 365 or 366."
    source := "Gregorian calendar; C/Python twins", status := .proven
    prop := ``DaysInMonth, thm := some ``daysInMonth_proven },
  { id := "datetime-check-date-fields", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_check_date_fields", "C check_date_args"]
    statement := "For all ints y, m, d, _check_date_fields and C check_date_args give the same result and message; it succeeds exactly for valid dates, returning the fields, and raises ValueError otherwise."
    source := "date docs (ValueError out of range); C/Python twins", status := .proven
    prop := ``CheckDateFields, thm := some ``checkDateFields_proven },
  { id := "datetime-check-date-fields-index", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_check_date_fields", "C check_date_args", "C datetime_date", "C PyLong_AsInt"]
    statement := "For all arguments, _check_date_fields equals C's clinic date() conversions plus check_date_args whenever every argument fits a C int; __index__ results are the fields, an exception of __index__ propagates unchanged in argument order, and a non-int __index__ result or a float is a TypeError."
    source := "operator.index docs; C/Python twins", status := .proven
    prop := ``CheckDateFieldsIndex, thm := some ``checkDateFieldsIndex_proven },
  { id := "datetime-date-new-index-missing", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.__new__", "_check_date_fields", "C date_new", "C datetime_date"]
    statement := "date(a, b) where a.__index__ raises e and b is not None raises e in Python (day=None is reached after a's conversion) and TypeError for the missing day in C."
    source := "C/Python twins (the case DateNewArgs excludes)", status := .proven
    prop := ``DateNewIndexMissing, thm := some ``dateNewIndexMissing_proven },
  { id := "datetime-check-time-fields-index", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_check_time_fields", "C check_time_args", "C datetime_time", "C PyLong_AsInt"]
    statement := "For all arguments, _check_time_fields on ints is the int-level check with fold returned as given; __index__ results are the fields; an exception of __index__ propagates unchanged in argument order; a non-int __index__ result is a TypeError; and time(h, m, s, us, fold=f) with fields that are ints or __index__ objects within a C int and an int fold within a C int is the same in both twins."
    source := "operator.index docs; C/Python twins", status := .proven
    prop := ``CheckTimeFieldsIndex, thm := some ``checkTimeFieldsIndex_proven },
  { id := "datetime-time-fold-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_check_time_fields", "time.__new__", "C datetime_time", "C PyLong_AsInt"]
    statement := "time(fold=x) agrees between the twins for every fold that fits a C int."
    source := "C/Python twins; time docs (fold in [0, 1])", status := .refuted
    prop := ``TimeFoldTwins, thm := some ``timeFoldTwins_refuted
    bug := some "datetime-pydatetime-fold-ordinal-no-index"
    notes := "time(fold=1.0): Python's fold not in (0, 1) accepts 1.0 (no _index); C's int converter raises TypeError." },
  { id := "datetime-datetime-fold-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_check_time_fields", "datetime.__new__", "C datetime_datetime", "C PyLong_AsInt"]
    statement := "datetime(2020, 1, 1, fold=x) agrees between the twins for every fold that fits a C int."
    source := "C/Python twins; datetime docs (fold in [0, 1])", status := .refuted
    prop := ``DatetimeFoldTwins, thm := some ``datetimeFoldTwins_refuted
    bug := some "datetime-pydatetime-fold-ordinal-no-index"
    notes := "datetime(2020, 1, 1, fold=1.0): accepted by Python, TypeError in C." },
  { id := "datetime-time-fold-arg", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_check_time_fields", "time.__new__", "C datetime_time"]
    statement := "time(fold=x) for every float x succeeds in Python exactly when x == 0 or x == 1 (so -0.0 too) and is a TypeError in C; for an object whose __index__ returns n it is a ValueError in Python and C's time(fold=n)."
    source := "C/Python twins; time docs (fold)", status := .proven
    prop := ``TimeFoldArg, thm := some ``timeFoldArg_proven },
  { id := "datetime-fromordinal-index-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromordinal", "_ord2ymd", "C datetime_date_fromordinal", "C datetime_date_fromordinal_impl"]
    statement := "date.fromordinal(x) agrees between the twins for every argument that fits a C int."
    source := "C/Python twins", status := .refuted
    prop := ``FromordinalIndexTwins, thm := some ``fromordinalIndexTwins_refuted
    bug := some "datetime-pydatetime-fold-ordinal-no-index"
    notes := "date.fromordinal(obj) with obj.__index__() == 5: date(1, 1, 5) in C, TypeError from n -= 1 in Python." },
  { id := "datetime-fromordinal-arg", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromordinal", "_ord2ymd", "C datetime_date_fromordinal", "C datetime_date_fromordinal_impl"]
    statement := "date.fromordinal(x) for every argument: an int is the int-level model in each twin; an object whose __index__ returns n is fromordinal(n) in C and a TypeError in Python; an exception of __index__ propagates in C; every argument without __index__ (None, str, bytes, float, any other object) is a TypeError in both."
    source := "C/Python twins", status := .proven
    prop := ``FromordinalArg, thm := some ``fromordinalArg_proven },
  { id := "datetime-check-time-fields", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_check_time_fields", "C check_time_args"]
    statement := "For all ints h, m, s, us, fold, _check_time_fields and C check_time_args give the same result and message; it succeeds exactly when every field is in range and fold is 0 or 1, and raises ValueError otherwise."
    source := "time docs; C/Python twins", status := .proven
    prop := ``CheckTimeFields, thm := some ``checkTimeFields_proven },
  { id := "datetime-check-tzinfo-arg", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_check_tzinfo_arg", "C check_tzinfo_subclass"]
    statement := "For every argument, _check_tzinfo_arg and C check_tzinfo_subclass accept None and tzinfo instances and raise TypeError for anything else."
    source := "time/datetime docs; C/Python twins", status := .proven
    prop := ``TzinfoArg, thm := some ``tzinfoArg_proven },
  { id := "datetime-build-struct-time", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_build_struct_time", "C build_struct_time"]
    statement := "For every valid date and any ints hh, mm, ss, dstflag, _build_struct_time is (y, m, d, hh, mm, ss, weekday, yday, dstflag) with weekday in 0..6 and yday in 1..366, the tuple C build_struct_time passes to struct_time."
    source := "time.struct_time docs; C/Python twins", status := .proven
    prop := ``BuildStructTime, thm := some ``buildStructTime_proven },
  { id := "datetime-isocalendardate", pyFile := "Lib/_pydatetime.py"
    pyFns := ["IsoCalendarDate.__new__", "IsoCalendarDate.year", "IsoCalendarDate.week", "IsoCalendarDate.weekday", "IsoCalendarDate.__repr__", "C iso_calendar_date_repr", "C iso_calendar_date_year", "C iso_calendar_date_week", "C iso_calendar_date_weekday"]
    statement := "The named fields of IsoCalendarDate are its tuple items, and repr in C is repr in Python with the module prefix."
    source := "IsoCalendarDate docs", status := .proven
    prop := ``IsoCalendarDateFields, thm := some ``isoCalendarDateFields_proven
    notes := "The repr prefix differs by design: _pydatetime names the class without the module." },
  { id := "datetime-datetime-sub-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.__sub__", "C datetime_subtract", "C delta_cmp", "C delta_subtract"]
    statement := "datetime - datetime agrees between the twins in value or exception class for every tzinfo."
    source := "C/Python twins", status := .proven
    prop := ``DatetimeSubTwins, thm := some ``datetimeSubTwins_proven },
  { id := "datetime-datetime-add", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.__add__", "C datetime_add", "C add_datetime_timedelta", "C normalize_datetime"]
    statement := "For every valid datetime d and timedelta t: if the sum is in range both twins return the same datetime at d + t, same tzinfo, fold=0; otherwise both raise OverflowError."
    source := "datetime docs; C/Python twins", status := .proven
    prop := ``DatetimeAddTimedelta, thm := some ``datetimeAddTimedelta_proven },
  { id := "datetime-datetime-sub-delta", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.__sub__", "C datetime_subtract", "C add_datetime_timedelta", "C normalize_datetime"]
    statement := "For every valid datetime d and timedelta t: if the difference is in range both twins return the same datetime; otherwise both raise OverflowError."
    source := "datetime docs; C/Python twins", status := .proven
    prop := ``DatetimeSubTimedelta, thm := some ``datetimeSubTimedelta_proven },
  { id := "datetime-timezone-fromutc", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timezone.fromutc", "C timezone_fromutc"]
    statement := "timezone.fromutc(dt) agrees between the twins for every valid dt, including the dt.tzinfo-is-not-self error."
    source := "C/Python twins", status := .proven
    prop := ``TimezoneFromutc, thm := some ``timezoneFromutc_proven },
  { id := "datetime-datetime-hash", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.__hash__", "C datetime_hash"]
    statement := "hash(datetime) uses the same key in both twins for every tzinfo: the UTC value when aware, the packed fields when naive."
    source := "C/Python twins", status := .proven
    prop := ``DatetimeHashTwins, thm := some ``datetimeHashTwins_proven },
  { id := "datetime-datetime-timetuple", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.timetuple", "C datetime_timetuple"]
    statement := "datetime.timetuple() agrees between the twins for every tzinfo."
    source := "C/Python twins", status := .proven
    prop := ``DatetimeTimetuple, thm := some ``datetimeTimetuple_proven },
  { id := "datetime-datetime-utctimetuple", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.utctimetuple", "C datetime_utctimetuple"]
    statement := "datetime.utctimetuple() agrees between the twins for every tzinfo, in value or exception class."
    source := "C/Python twins", status := .proven
    prop := ``DatetimeUtctimetuple, thm := some ``datetimeUtctimetuple_proven },
  { id := "datetime-datetime-compare", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.__eq__", "datetime.__le__", "datetime.__lt__", "datetime.__ge__", "datetime.__gt__", "datetime._cmp", "_cmp", "C datetime_richcompare", "C diff_to_bool", "C flip_fold", "C get_flip_fold_offset", "C pep495_eq_exception"]
    statement := "datetime comparison agrees between the twins for every tzinfo whose utcoffset does not raise on the operands with fold flipped, including the PEP 495 exception to ==."
    source := "C/Python twins; PEP 495", status := .proven
    prop := ``DatetimeCompareTwins, thm := some ``datetimeCompareTwins_proven
    notes := "Python asks for the flipped offsets up front, C only when the operands are otherwise equal, so a method that raises only there is an exception in one twin." },
  { id := "datetime-wrap-scan-directives", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_wrap_strftime"]
    statement := "Step by step, for every object, tzinfo environment and remaining format, _wrap_strftime copies a non-% character, replaces %f by the six-digit microsecond, %z and %:z by _format_offset(utcoffset()) without and with ':' (empty for a date; exceptions propagate), %Z by tzname() with % doubled (empty for None or a date), keeps %:x, %% and every other directive, keeps a trailing % and drops a trailing %:, and for a year below 1000 with the normalization needed writes %Y, %G, %C, %F itself."
    source := "strftime docs (%f, %z, %:z, %Z); _pydatetime.py:227-292", status := .proven
    prop := ``WrapScanDirectives, thm := some ``wrapScanDirectives_proven },
  { id := "datetime-strftime-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_wrap_strftime", "C wrap_strftime"]
    statement := "For every format, both twins hand the same format to time.strftime."
    source := "C/Python twins", status := .refuted
    prop := ``StrftimeTwins, thm := some ``strftimeTwins_refuted
    bug := some "datetime-strftime-bare-colon"
    notes := "A bare %: at the end of the format is dropped by Python and kept by C; '%:%Z' also differs. Still on main." },
  { id := "datetime-astimezone-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.astimezone", "C datetime_datetime_astimezone_impl"]
    statement := "astimezone agrees between the twins for every tzinfo and valid datetime."
    source := "C/Python twins", status := .refuted
    prop := ``AstimezoneTwins, thm := some ``astimezoneTwins_refuted
    bug := some "datetime-pydatetime-astimezone-unchecked-offset"
    notes := "_pydatetime does not check mytz.utcoffset(self), and calls it before the 'tz is mytz' shortcut." },
  { id := "datetime-time-pickle-ctor-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.__new__", "C time_new"]
    statement := "The pickle form time(state, tzinfo) takes the same second argument in both twins."
    source := "C/Python twins", status := .refuted
    prop := ``TimePickleCtorTwins, thm := some ``timePickleCtorTwins_refuted
    bug := some "datetime-time-pickle-falsy-tzinfo"
    notes := "Python's `minute or None` accepts any falsy object as tzinfo." },
  { id := "datetime-mktime-fixed", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime._mktime", "C local_to_seconds"]
    statement := "In a zone with a fixed offset, local seconds t are POSIX seconds t - offset, for either fold."
    source := "datetime.timestamp docs; invariant", status := .proven
    prop := ``MktimeFixedOffset, thm := some ``mktimeFixedOffset_proven },
  { id := "datetime-utc-to-seconds", pyFile := "Lib/_pydatetime.py"
    pyFns := ["C utc_to_seconds", "C ymd_to_ord"]
    statement := "utc_to_seconds is the ordinal times 86400 plus the time of day for a valid date, and raises ValueError for a year out of range."
    source := "invariant", status := .proven
    prop := ``UtcToSeconds, thm := some ``utcToSeconds_proven },
  { id := "datetime-packed-accessors", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.year", "date.month", "date.day", "time.hour", "time.minute", "time.second", "time.microsecond", "datetime.hour", "datetime.minute", "datetime.second", "datetime.microsecond", "C date_year", "C date_month", "C date_day", "C time_hour", "C time_minute", "C py_time_second", "C time_microsecond", "C datetime_hour", "C datetime_minute", "C datetime_second", "C datetime_microsecond", "C set_date_fields"]
    statement := "For every valid object, each C accessor reads back from the packed bytes the field the Python class keeps as an attribute."
    source := "C/Python twins", status := .proven
    prop := ``PackedAccessors, thm := some ``packedAccessors_proven },
  { id := "datetime-subclass-construction", pyFile := "Lib/_pydatetime.py"
    pyFns := ["C new_date_subclass_ex", "C new_datetime_ex", "C new_datetime_subclass_fold_ex", "C call_subclass_fold", "C new_time_ex", "C new_time_subclass_fold_ex"]
    statement := "The base classes take the fast path, which checks the fields; a subclass constructor whose fold keyword defaults to 0 sees the object's fold."
    source := "invariant", status := .proven
    prop := ``SubclassConstruction, thm := some ``subclassConstruction_proven },
  { id := "datetime-format-via-strftime", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.__format__", "time.__format__", "C datetime_date___format___impl", "C datetime_time___format___impl"]
    statement := "format(x, '') is str(x) and format(x, f) is x.strftime(f) for nonempty f, for date and time, in both twins."
    source := "date.__format__ docs", status := .proven
    prop := ``FormatViaStrftime, thm := some ``formatViaStrftime_proven },
  { id := "datetime-sanitize-isoformat", pyFile := "Lib/_pydatetime.py"
    pyFns := ["C _sanitize_isoformat_str"]
    statement := "Short strings fail, a string with no surrogate at positions 7, 8 or 10 comes back unchanged, and a surrogate at 7 becomes T."
    source := "code comment (:5763-5766)", status := .proven
    prop := ``SanitizeIsoformat, thm := some ``sanitizeIsoformat_proven },
  { id := "strptime-julian-weekday", pyFile := "Lib/_strptime.py"
    pyFns := ["_calc_julian_from_U_or_W"]
    statement := "The day of the year computed from a week number falls on the requested weekday, for weeks counted from Monday or Sunday, including week 0."
    source := "time.strptime %U/%W docs; invariant", status := .proven
    prop := ``CalcJulianWeekday, thm := some ``calcJulianWeekday_proven },
  { id := "strptime-seqtore-sorted", pyFile := "Lib/_strptime.py"
    pyFns := ["TimeRE.__seqToRE"]
    statement := "__seqToRE keeps every alternative and sorts them longest first, so a name that is a prefix of another cannot shadow it."
    source := "code comment; invariant", status := .proven
    prop := ``SeqToRESorted, thm := some ``seqToRESorted_proven },
  { id := "strptime-compile-errors", pyFile := "Lib/_strptime.py"
    pyFns := ["TimeRE.pattern", "TimeRE.compile", "TimeRE.__init__"]
    statement := "Once the locale formats are translated, a bad format produces only ValueError, never the internal KeyError."
    source := "no internal error leaking", status := .proven
    prop := ``StrptimeCompileErrors, thm := some ``strptimeCompileErrors_proven },
  { id := "strptime-methods", pyFile := "Lib/_strptime.py"
    pyFns := ["_strptime", "_strptime_datetime_date", "_strptime_datetime_time", "_strptime_datetime_datetime", "_parse_tz", "C datetime_date_strptime_impl", "C datetime_time_strptime_impl", "C datetime_datetime_strptime_impl"]
    statement := "When datetime.strptime succeeds, date.strptime gives its date and time.strptime its time and tzinfo, for the same match."
    source := "method vs equivalent method", status := .proven
    prop := ``StrptimeMethods, thm := some ``strptimeMethods_proven },
  { id := "datetime-strptime-wrappers", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.strptime", "time.strptime", "datetime.strptime"]
    statement := "When datetime.strptime succeeds, date.strptime gives its date and time.strptime its time and tzinfo, for the same match."
    source := "method vs equivalent method", status := .proven
    prop := ``StrptimeMethods, thm := some ``strptimeMethods_proven },
  { id := "datetime-date-isoformat-roundtrip", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.isoformat", "date.fromisoformat", "datetime.fromisoformat", "_parse_isoformat_date", "_read_isoformat_component", "_find_isoformat_datetime_separator", "_is_ascii_digit", "C date_isoformat", "C date_str", "C datetime_date_fromisoformat_impl", "C datetime_datetime_fromisoformat_impl", "C tzinfo_from_isoformat_results", "C parse_isoformat_date", "C parse_digits", "C is_digit", "C _find_isoformat_datetime_separator"]
    statement := "For every date d, date.fromisoformat(d.isoformat()) == d and datetime.fromisoformat(d.isoformat()) == datetime(d.year, d.month, d.day), in both twins."
    source := "date.fromisoformat docs (\"the output of date.isoformat()\" is accepted)", status := .proven
    prop := ``DateIsoformatRoundtrip, thm := some ``dateIsoformatRoundtrip_proven },
  { id := "datetime-date-fromiso-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromisoformat", "C datetime_date_fromisoformat_impl", "C parse_isoformat_date", "C parse_digits"]
    statement := "For every string s, C and Python date.fromisoformat(s) return the same date or both raise the same exception class."
    source := "C/Python twins", status := .refuted
    prop := ``DateFromisoTwins, thm := some ``dateFromisoTwins_refuted
    bug := some "datetime-date-fromisoformat-ignores-trailing-chars"
    notes := "Witness '20040509\\u0660': C measures UTF-8 bytes and ignores what follows the day, Python refuses non-ASCII text. The 3.14.7 witness '2020-+1-01' is gone: _read_isoformat_component (gh-152205) demands digits." },
  { id := "datetime-time-fromiso-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.fromisoformat", "_parse_hh_mm_ss_ff", "_parse_isoformat_time", "C datetime_time_fromisoformat_impl", "C parse_hh_mm_ss_ff", "C parse_isoformat_time"]
    statement := "For every string s, C and Python time.fromisoformat(s) return the same time or both raise the same exception class."
    source := "C/Python twins", status := .refuted
    prop := ``TimeFromisoTwins, thm := some ``timeFromisoTwins_refuted
    bug := some "datetime-c-fromisoformat-fraction-without-decimal-mark"
    notes := "C reads digits after HHMMSS as a fraction with no '.' or ','. Another witness on 3.15.2: stray text before an offset ('12:30x+05:00', gh-158501, fixed on main)." },
  { id := "datetime-datetime-fromiso-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.fromisoformat", "_parse_isoformat_time", "C datetime_datetime_fromisoformat_impl", "C parse_isoformat_time"]
    statement := "For every string s, C and Python datetime.fromisoformat(s) return the same datetime or both raise the same exception class."
    source := "C/Python twins", status := .refuted
    prop := ``DatetimeFromisoTwins, thm := some ``datetimeFromisoTwins_refuted
    bug := some "datetime-c-fromisoformat-nul-after-z"
    notes := "Witness '2020-01-01T12:00Z\\x00junk' (still on main). On 3.15.2 an embedded NUL also ends the time in other positions ('...T12\\x00')." },
  { id := "datetime-datetime-fromiso-bare-separator", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.fromisoformat", "_find_isoformat_datetime_separator"]
    statement := "For every date d and character c, datetime.fromisoformat(d.isoformat() + c) raises ValueError in both twins (a separator needs a time after it)."
    source := "datetime.fromisoformat docs (any valid ISO 8601 format); C behaviour", status := .refuted
    prop := ``DatetimeFromisoBareSeparator, thm := some ``datetimeFromisoBareSeparator_refuted
    bug := some "datetime-pydatetime-fromisoformat-trailing-separator" },
  { id := "datetime-datetime-fromiso-midnight-valid-date", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.fromisoformat", "C datetime_datetime_fromisoformat_impl"]
    statement := "For every string D, if datetime.fromisoformat(D + 'T24:00') returns a value then datetime.fromisoformat(D) does too, in both twins."
    source := "datetime.fromisoformat docs (24:00 is midnight at the end of the day)", status := .refuted
    prop := ``DatetimeFromisoMidnightNeedsValidDate, thm := some ``datetimeFromisoMidnightNeedsValidDate_refuted
    bug := some "datetime-fromisoformat-midnight-day-zero" },
  { id := "datetime-date-fromiso-ten-chars", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromisoformat", "_parse_isoformat_date", "C parse_isoformat_date"]
    statement := "If date.fromisoformat(s) succeeds for a 10-character s then s[4] == '-' (only YYYY-MM-DD and YYYY-Www-D have 10 characters), in both twins."
    source := "date.fromisoformat docs (any valid ISO 8601 format)", status := .refuted
    prop := ``DateFromisoTenChars, thm := some ``dateFromisoTenChars_refuted
    bug := some "datetime-date-fromisoformat-ignores-trailing-chars" },
  { id := "datetime-read-isoformat-component", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_read_isoformat_component"]
    statement := "_read_isoformat_component(s, n) returns the value of n ASCII digits and, for an ASCII s, raises ValueError for any other length, the empty string and any non-digit."
    source := "code comment (:359-360); the C parser it matches", status := .proven
    prop := ``ReadIsoComponentExact, thm := some ``readIsoComponentExact_proven
    notes := "ASCII is the function's precondition: str.isdigit takes non-ASCII digits, so ('١٢', 2) returns 12. Both callers check isascii() first." },
  { id := "datetime-fromiso-offset-range", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.fromisoformat", "_parse_isoformat_time", "_parse_hh_mm_ss_ff", "_check_time_fields", "C datetime_time_fromisoformat_impl", "C parse_isoformat_time", "C parse_hh_mm_ss_ff", "C check_time_args", "C tzinfo_from_isoformat_results"]
    statement := "For every two-digit HH and MM, time.fromisoformat('12:00±HH:MM') in both twins raises the ValueError naming the hour above 23 or the minute above 59, and otherwise has an offset of exactly that many microseconds."
    source := "C/Python twins; datetime.fromisoformat docs", status := .proven
    prop := ``FromisoOffsetRange, thm := some ``fromisoOffsetRange_proven
    notes := "New in 3.15: 3.14.7 took '+05:60' as +06:00. An offset that fails to parse differs in the message only: C checks the fields it read first, so '+99x' names the hour where Python says Invalid isoformat string." },
  { id := "strptime-abbreviations", pyFile := "Lib/_strptime.py"
    pyFns := ["TimeRE.__init__"]
    statement := "In every locale whose formats translate, %D and %F are the regexes of %m/%d/%y and %Y-%m-%d."
    source := "strftime docs (%D, %F are those formats)", status := .proven
    prop := ``TimeREAbbreviations, thm := some ``timeREAbbreviations_proven },
  { id := "strptime-end-check", pyFile := "Lib/_strptime.py"
    pyFns := ["_strptime"]
    statement := "After the match, with found.end() within the string: a full match goes on, and otherwise _strptime raises ValueError, never an IndexError from rest[0], blaming a missing colon exactly when %:z matched and the rest does not start with one."
    source := "no internal error leaking", status := .proven
    prop := ``StrptimeEndCheckExact, thm := some ``strptimeEndCheckExact_proven },
  { id := "strptime-z-colon", pyFile := "Lib/_strptime.py"
    pyFns := ["_strptime"]
    statement := "%z and %:z read the same text the same way, and a group that did not take part leaves the state unchanged."
    source := "method vs equivalent method", status := .proven
    prop := ``StrptimeZColon, thm := some ``strptimeZColon_proven },
  { id := "strptime-day-needs-year", pyFile := "Lib/_strptime.py"
    pyFns := ["TimeRE.pattern", "TimeRE.__init__", "TimeRE.compile"]
    statement := "TimeRE.pattern raises 'may not be used without a year directive' only for a format whose translation captures no year."
    source := "strptime docs (\"%d without a year now raises ValueError\"); the error message", status := .refuted
    prop := ``StrptimeDayNeedsYear, thm := some ``strptimeDayNeedsYear_refuted
    bug := some "datetime-strptime-oy-day-without-year"
    notes := "Witness '%d/%m/%Oy' with LC_alt_digits None: %Oy fills group y but does not set year_in_format. Needs a locale with alt digits or no ALT_DIGITS; in the C locale %Oy is empty and the error is right." },
  { id := "datetime-time-isoformat-roundtrip", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.isoformat", "time.fromisoformat", "_parse_isoformat_time", "_parse_hh_mm_ss_ff", "_format_time", "_format_offset", "C datetime_time_fromisoformat_impl", "C parse_isoformat_time", "C parse_hh_mm_ss_ff"]
    statement := "time.fromisoformat(t.isoformat()) == t for every time, naive or with any offset in range, in both twins."
    source := "time.fromisoformat docs", status := .open
    prop := ``TimeIsoformatRoundtrip
    notes := "Needs the digit lemmas of IsoRoundtrip carried through _parse_hh_mm_ss_ff and the sign and fraction branches of the offset, for both parsers. No counterexample in 40000 random round trips." },
  { id := "datetime-datetime-isoformat-roundtrip", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.isoformat", "datetime.fromisoformat", "_find_isoformat_datetime_separator", "C datetime_datetime_isoformat_impl", "C datetime_datetime_fromisoformat_impl"]
    statement := "datetime.fromisoformat(d.isoformat()) == d for every datetime, in both twins."
    source := "datetime.fromisoformat docs", status := .open
    prop := ``DatetimeIsoformatRoundtrip
    notes := "Needs datetime-time-isoformat-roundtrip and the separator search on a well-formed string." },
  { id := "datetime-datetime-eq-hash", pyFile := "Lib/_pydatetime.py"
    pyFns := ["C datetime_hash", "C datetime_richcompare"]
    statement := "Equal datetime objects have equal hashes, for every tzinfo."
    source := "__hash__ contract", status := .open
    prop := ``DatetimeEqHash
    notes := "Needs a case split on the PEP 495 path: equal offsets with fold flipped, then the UTC keys of datetimes equal across zones." },
  { id := "datetime-strftime-twins-narrow", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_wrap_strftime", "C wrap_strftime", "C make_freplacement", "C make_somezreplacement", "C make_Zreplacement", "C format_utcoffset"]
    statement := "Without a bare %:, and with the century normalization not in play, both twins hand the same format to time.strftime."
    source := "C/Python twins", status := .open
    prop := ``StrftimeTwinsNoBareColon
    notes := "Needs an induction relating the list scan of _wrap_strftime to the index loop of wrap_strftime." },
  { id := "datetime-time-compare-whole-minutes", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time._cmp", "C time_richcompare"]
    statement := "With whole-minute offsets, time comparison agrees between the twins."
    source := "C/Python twins", status := .open
    prop := ``TimeCompareWholeMinutes
    notes := "The arithmetic of the two offset branches; cmpTuple against the C difference." },
  { id := "datetime-astimezone-to-timezone", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.astimezone", "timezone.fromutc", "C datetime_datetime_astimezone_impl", "C timezone_fromutc"]
    statement := "astimezone to a timezone agrees between the twins when utcoffset(self) is a timedelta in range."
    source := "C/Python twins", status := .open
    prop := ``AstimezoneToTimezone
    notes := "Should follow from DatetimeSubTimedelta and TimezoneFromutc." },
  { id := "datetime-tzinfo-fromutc", pyFile := "Lib/_pydatetime.py"
    pyFns := ["tzinfo.fromutc", "C tzinfo_fromutc"]
    statement := "tzinfo.fromutc agrees between the twins for a subclass whose dst() is constant."
    source := "tzinfo.fromutc docs; C/Python twins", status := .open
    prop := ``TzinfoFromutcFixedDst
    notes := "Both add dst in two steps; the intermediate overflow cases need care." },
  { id := "datetime-timedelta-str-repr", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__str__", "timedelta.__repr__", "C delta_str", "C delta_repr"]
    statement := "For every timedelta, str(t) ('[D day[s], ]H:MM:SS[.ffffff]') and repr(t) of the base class are the same text in both twins."
    source := "C/Python twins", status := .proven
    prop := ``TimedeltaStrRepr, thm := some ``timedeltaStrRepr_proven },
  { id := "datetime-timedelta-repr-cls", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__repr__", "_get_class_module", "C delta_repr"]
    statement := "repr(t) agrees between the twins for timedelta and for every subclass whose __qualname__ is its __name__ and whose module is not named datetime, and for the base class it is datetime.timedelta(...) with the nonzero fields."
    source := "C/Python twins (gh-107773)", status := .proven
    prop := ``TimedeltaReprCls, thm := some ``timedeltaReprCls_proven },
  { id := "datetime-timedelta-repr-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__repr__", "_get_class_module", "C delta_repr"]
    statement := "repr(t) agrees between the twins for every timedelta subclass."
    source := "C/Python twins (gh-107773)", status := .refuted
    prop := ``TimedeltaReprTwins, thm := some ``timedeltaReprTwins_refuted
    bug := some "datetime-repr-qualname-vs-tp-name"
    notes := "class Outer: class TSub(timedelta): repr(Outer.TSub(1)) is Outer.TSub(days=1) in Python, TSub(days=1) in C." },
  { id := "datetime-zoneinfo-rule-date-twins", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C calendarrule_year_to_timestamp", "C dayrule_year_to_timestamp", "C ymd_to_ord", "C is_leap_year", "_CalendarOffset.year_to_epoch", "_CalendarOffset._ymd2ord", "_DayOffset.year_to_epoch", "_post_epoch_days_before_year"]
    statement := "For every rule either TZ parser can build (Mm.w.d, Jn or n with a time of at most 167 hours) and every datetime year, C and Python compute the same local transition timestamp."
    source := "C/Python twins", status := .proven
    prop := ``Zone.RuleDateTwins, thm := some ``Zone.ruleDateTwins_proven
    notes := "C int8_t/uint8_t/uint16_t locals and int64 sums are shown not to wrap for these fields." },
  { id := "datetime-zoneinfo-calendar-rule-meaning", pyFile := "Lib/zoneinfo/_zoneinfo.py"
    pyFns := ["_CalendarOffset.year_to_epoch", "_CalendarOffset._ymd2ord", "_post_epoch_days_before_year"]
    statement := "Mm.w.d/time is time on the d-th weekday (0 = Sunday) of week w of month m, week 5 meaning the last such weekday, in every datetime year."
    source := "POSIX TZ (IEEE Std 1003.1 8.3); RFC 9636 3.3.1", status := .proven
    prop := ``Zone.CalendarRuleMeaning, thm := some ``Zone.calendarRuleMeaning_proven
    notes := "C gives the same timestamp by datetime-zoneinfo-rule-date-twins." },
  { id := "datetime-zoneinfo-julian-rule-meaning", pyFile := "Lib/zoneinfo/_zoneinfo.py"
    pyFns := ["_DayOffset.year_to_epoch", "_post_epoch_days_before_year"]
    statement := "Jn/time is the n-th day of a year without February 29 (March 1 is J60 in every year)."
    source := "POSIX TZ (IEEE Std 1003.1 8.3)", status := .proven
    prop := ``Zone.JulianRuleMeaning, thm := some ``Zone.julianRuleMeaning_proven
    notes := "The 3.15 change from d >= 59 to d >= 60 is what makes this hold." },
  { id := "datetime-zoneinfo-zero-based-rule", pyFile := "Lib/zoneinfo/_zoneinfo.py"
    pyFns := ["_DayOffset.year_to_epoch", "C dayrule_year_to_timestamp"]
    statement := "The zero-based rule n/time is n days after January 1, in both twins."
    source := "POSIX TZ (IEEE Std 1003.1 8.3: zero-based Julian day)", status := .refuted
    prop := ``Zone.ZeroBasedRuleMeaning, thm := some ``Zone.zeroBasedRuleMeaning_refuted
    bug := some "datetime-zoneinfo-zero-based-day"
    notes := "Both start from December 31; duplicate of gh-159712." },
  { id := "datetime-zoneinfo-dstoff-twins", pyFile := "Lib/zoneinfo/_zoneinfo.py"
    pyFns := ["ZoneInfo._utcoff_to_dstoff", "C utcoff_to_dstoff"]
    statement := "For every tuple _common.load_data can return, C and Python give every type the same dst() offset."
    source := "C/Python twins", status := .refuted
    prop := ``Zone.DstoffTwins, thm := some ``Zone.dstoffTwins_refuted
    bug := some "datetime-zoneinfo-isdst-sum"
    notes := "An isdst byte 0xff makes sum(isdsts) undercount the DST types." },
  { id := "datetime-zoneinfo-dstoff-twins-flags", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C load_timedelta", "C utcoff_to_dstoff", "ZoneInfo._utcoff_to_dstoff"]
    statement := "With isdst flags 0 or 1, C and Python give every type the same dst() offset."
    source := "C/Python twins; no silent wraparound", status := .refuted
    prop := ``Zone.DstoffTwinsFlags, thm := some ``Zone.dstoffTwinsFlags_refuted
    bug := some "datetime-zoneinfo-dstoff-int-narrowing"
    notes := "load_timedelta passes a long to the int parameter of Delta_FromDelta." },
  { id := "datetime-zoneinfo-dstoff-twins-narrow", pyFile := "Lib/zoneinfo/_zoneinfo.py"
    pyFns := ["ZoneInfo._utcoff_to_dstoff", "C utcoff_to_dstoff", "C load_timedelta"]
    statement := "With isdst flags 0 or 1 and type offsets below 2**30, C and Python give every type the same dst() offset."
    source := "C/Python twins (narrows datetime-zoneinfo-dstoff-twins-flags)", status := .proven
    prop := ``Zone.DstoffTwinsNarrow, thm := some ``Zone.dstoffTwinsNarrow_proven
    notes := "Python breaks when its DST count is reached and C runs on; the proof shows the remaining C steps change nothing and the 3600 fallbacks agree." },
  { id := "datetime-zoneinfo-ts-to-local-twins", pyFile := "Lib/zoneinfo/_zoneinfo.py"
    pyFns := ["ZoneInfo._ts_to_local", "C ts_to_local"]
    statement := "C and Python compute the same wall-clock transition times for both folds."
    source := "C/Python twins; no silent wraparound", status := .refuted
    prop := ``Zone.TsToLocalTwins, thm := some ``Zone.tsToLocalTwins_refuted
    bug := some "datetime-zoneinfo-transition-int64-wrap" },
  { id := "datetime-zoneinfo-ts-to-local-narrow", pyFile := "Lib/zoneinfo/_zoneinfo.py"
    pyFns := ["ZoneInfo._ts_to_local", "C ts_to_local"]
    statement := "When no transition time plus type offset leaves int64_t, C and Python compute the same wall-clock transition times."
    source := "C/Python twins (narrows datetime-zoneinfo-ts-to-local-twins)", status := .proven
    prop := ``Zone.TsToLocalTwinsNarrow, thm := some ``Zone.tsToLocalTwinsNarrow_proven },
  { id := "datetime-zoneinfo-load-data-valueerror", pyFile := "Lib/zoneinfo/_common.py"
    pyFns := ["load_data", "_TZifHeader.from_file"]
    statement := "_common.load_data, which both twins call, raises only ValueError (or UnicodeDecodeError) on data that is not a valid TZif file."
    source := "ZoneInfo.from_file docs (ValueError for an invalid TZif file)", status := .refuted
    prop := ``Zone.LoadDataValueError, thm := some ``Zone.loadDataValueError_refuted
    bug := some "datetime-zoneinfo-load-data-not-valueerror"
    notes := "A short header raises struct.error; a footer without its leading newline raises AssertionError." },
  { id := "datetime-zoneinfo-load-data-shape", pyFile := "Lib/zoneinfo/_common.py"
    pyFns := ["load_data", "_TZifHeader.from_file", "_TZifHeader.__init__"]
    statement := "On success _common.load_data returns lists of matching lengths whose transition indices name types and whose values fit their struct formats."
    source := "invariant (C load_data relies on it)", status := .proven
    prop := ``Zone.LoadDataShape, thm := some ``Zone.loadDataShape_proven
    notes := "Through the staged readTrans/readTypesStage/readFooter mirror of _common.py:32-132: unpack counts, the max(trans_idx) check and the per-type abbreviation reads." },
  { id := "datetime-zoneinfo-load-data-no-assertion", pyFile := "Lib/zoneinfo/_common.py"
    pyFns := ["load_data", "_TZifHeader.from_file"]
    statement := "_common.load_data reports a malformed file with an exception, never with a failed assert (which python -O removes)."
    source := "invariant (no internal error leaking); ZoneInfo.from_file docs", status := .refuted
    prop := ``Zone.LoadDataNoAssertion, thm := some ``Zone.loadDataNoAssertion_refuted
    bug := some "datetime-zoneinfo-load-data-not-valueerror"
    notes := "A complete version 2 file whose footer lacks its leading newline fails the assert at _common.py:123." },
  { id := "datetime-zoneinfo-tzstr-twins", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C parse_tz_str", "C parse_abbr", "C parse_tz_delta", "C parse_transition_time", "C parse_digits", "C build_tzrule", "_parse_tz_str"]
    statement := "C and Python accept the same TZ footers with the same rule and refuse the same ones with ValueError."
    source := "C/Python twins", status := .refuted
    prop := ``Zone.TzStrTwins, thm := some ``Zone.tzStrTwins_refuted
    bug := some "datetime-zoneinfo-footer-nul"
    notes := "C stops at an embedded NUL (PyBytes_AsString)." },
  { id := "datetime-zoneinfo-tzstr-twins-nonul", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C parse_tz_str", "C parse_abbr", "C parse_tz_delta", "C parse_transition_rule", "C parse_transition_time", "C parse_digits", "C calendarrule_new", "C dayrule_new", "C build_tzrule", "_parse_tz_str", "_parse_dst_start_end", "_parse_transition_time", "_parse_tz_delta", "_CalendarOffset.__init__", "_DayOffset.__init__", "_TZStr.__init__"]
    statement := "For footers without a NUL byte, C and Python accept the same TZ strings with the same rule and refuse the same ones."
    source := "C/Python twins (narrows datetime-zoneinfo-tzstr-twins)", status := .proven
    prop := ``Zone.TzStrTwinsNoNul, thm := some ``Zone.tzStrTwinsNoNul_proven
    notes := "Component-wise: each C pointer walk (parse_abbr, parse_tz_delta, parse_transition_rule, parse_transition_time) is shown equal to the matching regex group; ASCII decomposition and comma/slash tail locality carry it across components. 3.15 already fixed three regex/C differences (gh-152212, gh-152246, gh-152248)." },
  { id := "datetime-zoneinfo-load-twins", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C load_data", "ZoneInfo._load_file", "C build_ttinfo", "C ttinfo_eq", "_ttinfo.__eq__", "_ttinfo.__init__"]
    statement := "From the same well-formed tuple with isdst flags 0 or 1, type offsets below 2**30, no int64_t overflow in transition plus offset and a footer without NUL (the refuted cases), and some non-DST type or a first transition to type 0 (outside textlibs-zoneinfo-before-first-transition), _load_file and C load_data build corresponding zones or both raise."
    source := "C/Python twins (narrows the dstoff, ts_to_local, tzstr and before-first-transition refutations)", status := .proven
    prop := ``Zone.LoadTwins, thm := some ``Zone.loadTwins_proven
    notes := "Composes datetime-zoneinfo-dstoff-twins-narrow, -ts-to-local-narrow and -tzstr-twins-nonul with the per-transition ttinfo list, ttinfo_before and the fixed-offset flag. The before-first-transition hypothesis is exactly the complement of the textlibs refutation." },
  { id := "datetime-zoneinfo-ttinfo-eq", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C ttinfo_eq", "_ttinfo.__eq__"]
    statement := "On two _ttinfo objects, C ttinfo_eq gives 1 and _ttinfo.__eq__ True exactly when utcoff, dstoff and tzname are all equal (else 0 and False); over arbitrary field comparisons both compare utcoff, then dstoff, then tzname, stopping at the same field, so an error, False or True comes out of the same comparison."
    source := "C/Python twins", status := .proven
    prop := ``Zone.TtinfoEq, thm := some ``Zone.ttinfoEq_proven
    notes := "Each twin has its own mirror (ttinfoEqWithC over RichCompareBool results with the rv < 1 exits, ttinfoEqWithPy as the and-chain); C load_data's fixed_offset and _load_file's _fixed_offset use them, so datetime-zoneinfo-load-twins rests on both specs." },
  { id := "datetime-zoneinfo-lookup-twins", pyFile := "Lib/zoneinfo/_zoneinfo.py"
    pyFns := ["ZoneInfo._find_trans", "ZoneInfo._get_local_timestamp", "_TZStr._get_trans_info", "_TZStr.transitions", "C get_local_timestamp", "C find_ttinfo", "C _bisect", "C find_tzrule_ttinfo", "C tzrule_transitions"]
    statement := "For corresponding zones, C find_ttinfo and Python _find_trans pick the same ttinfo for None and for every plain datetime (type(dt) is datetime, both folds), through the bisect over local transitions and the rule after the last one."
    source := "C/Python twins", status := .proven
    prop := ``Zone.LookupTwins, thm := some ``Zone.lookupTwins_proven
    notes := "Plain datetime objects only: subclasses are datetime-zoneinfo-lookup-twins-instances (refuted), a non-datetime argument is datetime-zoneinfo-find-ttinfo-defined. The zones correspond by hypothesis, which datetime-zoneinfo-load-twins establishes." },
  { id := "datetime-zoneinfo-lookup-twins-instances", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C get_local_timestamp", "C find_ttinfo", "ZoneInfo._get_local_timestamp", "ZoneInfo._find_trans"]
    statement := "For corresponding zones, C find_ttinfo and Python _find_trans pick the same ttinfo for every datetime instance, subclasses included."
    source := "C/Python twins; no silent wraparound", status := .refuted
    prop := ``Zone.LookupTwinsInstances, thm := some ``Zone.lookupTwinsInstances_refuted
    bug := some "datetime-zoneinfo-subclass-lookup"
    notes := "For a subclass C calls toordinal() and narrows it with PyLong_AsLong into int ord (Modules/_zoneinfo.c:2301-2307); toordinal() + 2**32 gives +00:00 in C and +07:00 in Python." },
  { id := "datetime-zoneinfo-lookup-methods", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C zoneinfo_ZoneInfo_utcoffset_impl", "C zoneinfo_ZoneInfo_dst_impl", "C zoneinfo_ZoneInfo_tzname_impl", "ZoneInfo.utcoffset", "ZoneInfo.dst", "ZoneInfo.tzname"]
    statement := "For corresponding zones, utcoffset(), dst() and tzname() return the same values in both twins for None and every plain datetime (type(dt) is datetime)."
    source := "C/Python twins", status := .proven
    prop := ``Zone.LookupMethodsTwins, thm := some ``Zone.lookupMethodsTwins_proven },
  { id := "datetime-zoneinfo-find-ttinfo-defined", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C find_ttinfo", "C get_local_timestamp"]
    statement := "C find_ttinfo never reads memory it does not own: every argument whose toordinal(), hour, minute and second it can read gets a defined result."
    source := "invariant (no crash)", status := .refuted
    prop := ``Zone.FindTtinfoDefined, thm := some ``Zone.findTtinfoDefined_refuted
    bug := some "datetime-zoneinfo-non-datetime-crash"
    notes := "Duplicate of gh-125318 and gh-111306; segfaults on 3.15.2 and main." },
  { id := "datetime-zoneinfo-fromutc-twins", pyFile := "Lib/zoneinfo/_zoneinfo.py"
    pyFns := ["ZoneInfo.fromutc", "C zoneinfo_fromutc", "C find_tzrule_ttinfo_fromutc", "_TZStr._get_trans_info_fromutc"]
    statement := "For corresponding zones and every datetime, C and Python fromutc add the same offset and set the same fold."
    source := "C/Python twins; tzinfo.fromutc contract", status := .refuted
    prop := ``Zone.FromutcTwins, thm := some ``Zone.fromutcTwins_refuted
    bug := some "datetime-zoneinfo-fromutc-fold-last-transition"
    notes := "Python misses the fold of the last explicit transition; duplicate of gh-159707." },
  { id := "datetime-zoneinfo-fromutc-twins-notrans", pyFile := "Lib/zoneinfo/_zoneinfo.py"
    pyFns := ["ZoneInfo.fromutc", "C zoneinfo_fromutc", "C find_tzrule_ttinfo_fromutc", "_TZStr._get_trans_info_fromutc"]
    statement := "For corresponding zones without explicit transitions, C and Python fromutc add the same offset and set the same fold."
    source := "C/Python twins (narrows datetime-zoneinfo-fromutc-twins)", status := .proven
    prop := ``Zone.FromutcTwinsNoTrans, thm := some ``Zone.fromutcTwinsNoTrans_proven },
  { id := "datetime-zoneinfo-fromutc-twins-static", pyFile := "Lib/zoneinfo/_zoneinfo.py"
    pyFns := ["ZoneInfo.fromutc", "C zoneinfo_fromutc"]
    statement := "For corresponding zones whose rule after the last transition is a fixed offset, C and Python fromutc add the same offset and set the same fold for every plain datetime."
    source := "C/Python twins; tzinfo.fromutc contract (result consistent with utcoffset)", status := .refuted
    prop := ``Zone.FromutcTwinsStatic, thm := some ``Zone.fromutcTwinsStatic_refuted
    bug := some "datetime-zoneinfo-fromutc-static-footer"
    notes := "With two or more transitions, Python takes self._ttinfos[idx - 2 : idx] (_zoneinfo.py:144-145) after the last transition and adds that transition's offset instead of the footer's; C adds the footer's." },
  { id := "datetime-zoneinfo-fromutc-twins-sorted", pyFile := "Lib/zoneinfo/_zoneinfo.py"
    pyFns := ["ZoneInfo.fromutc", "C zoneinfo_fromutc", "C _bisect", "ZoneInfo._get_local_timestamp", "C get_local_timestamp"]
    statement := "For corresponding zones with ascending transitions (RFC 9636 3.2), TZif-sized offsets and transition times within 2**62, C and Python fromutc add the same offset and set the same fold for every plain datetime not after the last transition, or after it when the rule there is the last transition's own ttinfo."
    source := "C/Python twins (narrows datetime-zoneinfo-fromutc-twins and -fromutc-twins-static)", status := .proven
    prop := ``Zone.FromutcTwinsSorted, thm := some ``Zone.fromutcTwinsSorted_proven
    notes := "Three exclusions, each refuted: after the last transition with a TZ rule (datetime-zoneinfo-fromutc-twins, fold of the last transition) or with a different fixed footer offset (datetime-zoneinfo-fromutc-twins-static), and transition times beyond 2**62, where C's int64_t difference at :712 can wrap (datetime-zoneinfo-fromutc-twins-wide)." },
  { id := "datetime-zoneinfo-fromutc-twins-wide", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C zoneinfo_fromutc", "C _bisect", "ZoneInfo.fromutc"]
    statement := "datetime-zoneinfo-fromutc-twins-sorted with transition times anywhere in the int64_t range a TZif v2+ file can hold, instead of within 2**62."
    source := "C/Python twins; no silent wraparound", status := .refuted
    prop := ``Zone.FromutcTwinsSortedWide, thm := some ``Zone.fromutcTwinsSortedWide_refuted
    bug := some "datetime-zoneinfo-transition-int64-wrap"
    notes := "Transitions [-2**63, 2**60] (all +00:00), 2000-01-01 00:00 UTC: timestamp - trans_list_utc[idx - 1] (Modules/_zoneinfo.c:712) wraps negative, so C sets fold=1; Python gives fold=0." },
  { id := "datetime-zoneinfo-fromutc-twins-instances", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C zoneinfo_fromutc", "C get_local_timestamp", "ZoneInfo.fromutc", "ZoneInfo._get_local_timestamp"]
    statement := "For corresponding zones, C and Python fromutc agree for every datetime instance whose tzinfo is the zone, subclasses included."
    source := "C/Python twins; no silent wraparound", status := .refuted
    prop := ``Zone.FromutcTwinsInstances, thm := some ``Zone.fromutcTwinsInstances_refuted
    bug := some "datetime-zoneinfo-subclass-lookup"
    notes := "The same narrowed toordinal(): fromutc of 2021-01-01 adds +00:00 in C and +07:00 in Python." },
  { id := "datetime-zoneinfo-cache-twins", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C zoneinfo_ZoneInfo_impl", "C zone_from_strong_cache", "C find_in_strong_cache", "C move_strong_cache_node_to_front", "C remove_from_strong_cache", "C update_strong_cache", "C strong_cache_node_new", "C strong_cache_free", "C strong_cache_node_free", "C eject_from_strong_cache", "C clear_strong_cache", "C zoneinfo_ZoneInfo_clear_cache_impl", "ZoneInfo.__new__", "ZoneInfo.clear_cache"]
    statement := "For every run of ZoneInfo(key), clear_cache and instance-collection steps on the base class ZoneInfo, with keys whose equality cannot raise or re-enter and that have no finalizers, both twins keep the same keys in the same recency order in the strong cache, never more than 8, and fail the same calls (a call fails only when loading the key fails)."
    source := "C/Python twins; _strong_cache_size", status := .proven
    prop := ``Zone.CacheTwins, thm := some ``Zone.cacheTwins_proven
    notes := "The abstract model; datetime-zoneinfo-cache-twins-fallible carries it to the mirrors with fallible keys. Scope limits, each refuted outside: subclasses (datetime-zoneinfo-cache-twins-subclass), a key __eq__ that re-enters (datetime-zoneinfo-strong-lookup-defined) or raises (datetime-zoneinfo-cache-err-twins), key finalizers during clear_cache (datetime-zoneinfo-clear-cache-defined)." },
  { id := "datetime-zoneinfo-cache-twins-fallible", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C zoneinfo_ZoneInfo_impl", "C zone_from_strong_cache", "C find_in_strong_cache", "C update_strong_cache", "C eject_from_strong_cache", "C clear_strong_cache", "C zoneinfo_ZoneInfo_clear_cache_impl", "C get_weak_cache", "ZoneInfo.__new__", "ZoneInfo.clear_cache"]
    statement := "On the base class, for keys whose == is identity and whose hash() does not raise, every run of ZoneInfo(key), clear_cache(), clear_cache(only_keys=...) with an iterator that may raise after any prefix, and instance collections gives the same outcome in both twins (the same instance, the same exception) and the same strong-cache entries in recency order, never more than 8."
    source := "C/Python twins; _strong_cache_size", status := .proven
    prop := ``Zone.CacheTwinsFallible, thm := some ``Zone.cacheTwinsFallible_proven
    notes := "The mirrors (ZoneCacheErr.lean) make the real lookups: C compares the key with every node through PyObject_RichCompareBool, the weak cache and Python's OrderedDict hash then compare equal-hash stored keys; get/setdefault/pop and the rv < 0 returns are fallible. With identity keys each step equals the abstract step of ZoneCache.lean, so the proof reuses CacheTwins. Value-equal distinct key objects (two equal str objects) are not covered by this statement." },
  { id := "datetime-zoneinfo-cache-twins-equiv", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C zoneinfo_ZoneInfo_impl", "C zone_from_strong_cache", "C find_in_strong_cache", "C update_strong_cache", "C eject_from_strong_cache", "C clear_strong_cache", "C zoneinfo_ZoneInfo_clear_cache_impl", "ZoneInfo.__new__", "ZoneInfo.clear_cache"]
    statement := "On the base class, for keys whose == compares a value and never raises and whose hash() is a function of that value (separate str objects with equal text are equal keys), every run of ZoneInfo(key), clear_cache(), clear_cache(only_keys=...) with an iterator that may raise after any prefix, and instance collections gives the same outcome in both twins (the same instance, the same exception), and the strong caches hold the same key values with the same instances in recency order, never more than 8."
    source := "C/Python twins; _strong_cache_size", status := .proven
    prop := ``Zone.CacheTwinsEquiv, thm := some ``Zone.cacheTwinsEquiv_proven
    notes := "A strong-cache hit for an equal but distinct key is the main case: C keeps the first key object and moves the node to the front, Python's OrderedDict pop then __setitem__ stores the latest key object; the proof relates both to ZoneCache.lean over values, each value naming its current instance. A lookup that ignored a True __eq__ would leave two C nodes for one value and break the strong-cache conjunct. Raising (datetime-zoneinfo-cache-err-twins) and re-entering (datetime-zoneinfo-strong-lookup-defined) comparisons are refuted." },
  { id := "datetime-zoneinfo-sub-cache-twins", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C get_weak_cache", "C zoneinfo_init_subclass", "C new_weak_cache", "C zoneinfo_ZoneInfo_impl", "C zone_from_strong_cache", "C update_strong_cache", "C eject_from_strong_cache", "C zoneinfo_ZoneInfo_clear_cache_impl", "ZoneInfo.__init_subclass__", "ZoneInfo.__new__", "ZoneInfo.clear_cache"]
    statement := "After class Sub(ZoneInfo), while the instances stay referenced, every run of Sub(key), Sub.clear_cache() and Sub.clear_cache(only_keys=...) gives the same results and leaves the same weak cache in both twins, for keys whose __hash__ and __eq__ do not raise."
    source := "C/Python twins", status := .proven
    prop := ``Zone.SubCacheTwins, thm := some ``Zone.subCacheTwins_proven
    notes := "C get_weak_cache's subclass branch returns the _weak_cache attribute zoneinfo_init_subclass stored (:299-301); a version returning a fresh dictionary would lose the cached instance and fail. Collections are excluded: once unreferenced, C's subclass instance dies and Python's strong cache keeps it (datetime-zoneinfo-cache-twins-subclass, -cache-err-subclass)." },
  { id := "datetime-zoneinfo-weak-cache-type", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C zoneinfo_ZoneInfo_impl", "C get_weak_cache", "ZoneInfo.__new__"]
    statement := "For a fresh subclass, Sub(key) behaves the same in both twins on every run that does not delete Sub._weak_cache, replacing it included."
    source := "C/Python twins", status := .refuted
    prop := ``Zone.WeakCacheTypeTwins, thm := some ``Zone.weakCacheTypeTwins_refuted
    bug := some "datetime-zoneinfo-get-weak-cache-fallback"
    notes := "Sub._weak_cache = {'a': 1}; Sub('a'): C's PyObject_TypeCheck (:352-358) raises RuntimeError, Python returns 1." },
  { id := "datetime-zoneinfo-clear-keys-breaks", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C zoneinfo_ZoneInfo_clear_cache_impl", "C eject_from_strong_cache", "C strong_cache_node_free", "ZoneInfo.clear_cache"]
    statement := "In clear_cache(only_keys=[k, *rest]) on the base class, with any set of zones the caller has released, each failure on k stops the loop with that exception and the state at that point, whatever rest is: C's failed eject leaves both caches as they were; C's failed weak pop keeps the eject done, including the weak entry the freed node's zone lost if the caller had released it; Python's failed weak pop changes nothing, its failed strong pop keeps the weak pop done."
    source := "CPython source (loop exits at Modules/_zoneinfo.c:542-544, :552-553; exception propagation in _zoneinfo.py:97-99)", status := .proven
    prop := ``Zone.ClearKeysBreaks, thm := some ``Zone.clearKeysBreaks_proven
    notes := "Restated after the third review: the eject's strong_cache_node_free can drop a released zone's last reference, whose KeyedRef callback removes its weak entry before the pop (freeCb); the pop then runs on that weak cache, and can succeed where it used to be said to fail. A loop that went on to the next key after either failure would depend on rest." },
  { id := "datetime-zoneinfo-clear-keys-stop", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C zoneinfo_ZoneInfo_clear_cache_impl", "C eject_from_strong_cache", "C find_in_strong_cache", "C strong_cache_node_free", "ZoneInfo.clear_cache"]
    statement := "On the base class, while the weak cache holds a zone the caller still references, clear_cache(only_keys=[k, *rest]) with a k whose __hash__ raises (and whose __eq__ does not) raises that exception in both twins and processes no later key: Python changes nothing; C has at most ejected the strong node equal to k and, if the caller had released that node's zone, dropped its weak entry, whatever rest and the iterator are."
    source := "C/Python twins", status := .proven
    prop := ``Zone.ClearKeysStop, thm := some ``Zone.clearKeysStop_proven
    notes := "Restated after the third review measured the earlier hypothesis (a weak entry under a key not equal to k) false: with a non-transitive __eq__ that entry can be the freed zone's own. A referenced zone survives every callback, so the weak cache stays non-empty and dict.pop hashes. Without one, C carries on: datetime-zoneinfo-cache-twins-released. Measured on 3.15.2: with u = ZoneInfo('UTC') held and 'k' released, only_keys=[NoHash('k'), 'UTC'] raises TypeError in both and ZoneInfo('UTC') is u afterwards." },
  { id := "datetime-zoneinfo-cache-twins-released", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C zoneinfo_ZoneInfo_clear_cache_impl", "C eject_from_strong_cache", "C strong_cache_node_free", "ZoneInfo.clear_cache"]
    statement := "On the base class, the twins give the same outcomes on every run in which the caller may let go of zones the strong cache still holds."
    source := "C/Python twins", status := .refuted
    prop := ``Zone.CacheTwinsReleased, thm := some ``Zone.cacheTwinsReleased_refuted
    bug := some "datetime-zoneinfo-cache-eq-raises"
    notes := "z = ZoneInfo('k'); del z; clear_cache(only_keys=[NoHash('k'), 'UTC']): C's eject frees the node, the zone is collected and its KeyedRef callback empties the weak cache, dict.pop returns without hashing, and C clears the later keys and returns None; Python raises TypeError. Measured on 3.15.2." },
  { id := "datetime-zoneinfo-cache-err-twins", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C zoneinfo_ZoneInfo_impl", "C zone_from_strong_cache", "C find_in_strong_cache", "C eject_from_strong_cache", "C zoneinfo_ZoneInfo_clear_cache_impl", "ZoneInfo.__new__", "ZoneInfo.clear_cache"]
    statement := "On the base class, ZoneInfo(key) and clear_cache give the same outcomes in both twins for every run, whatever the keys' __hash__ and __eq__ do."
    source := "C/Python twins", status := .refuted
    prop := ``Zone.CacheErrTwins, thm := some ``Zone.cacheErrTwins_refuted
    bug := some "datetime-zoneinfo-cache-eq-raises"
    notes := "ZoneInfo(0), clear_cache(only_keys=[1]), ZoneInfo(1) with a key 1 whose __eq__ raises: C compares it with node 0 (rv < 0 at :2442-2444, returned at :320-321 and as eject's -1 at :2475-2477) and raises twice; Python's dicts never compare keys of different hash." },
  { id := "datetime-zoneinfo-cache-err-subclass", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C eject_from_strong_cache", "C zoneinfo_ZoneInfo_clear_cache_impl", "C get_weak_cache", "C zone_from_strong_cache", "C update_strong_cache", "C zoneinfo_ZoneInfo_impl", "ZoneInfo.clear_cache", "ZoneInfo.__new__"]
    statement := "For a fresh subclass, Sub(key), clear_cache and instance collections give the same outcomes in both twins for every run, whatever the keys' __hash__ and __eq__ do."
    source := "C/Python twins", status := .refuted
    prop := ``Zone.CacheErrTwinsSub, thm := some ``Zone.cacheErrTwinsSub_refuted
    bug := some "datetime-zoneinfo-subclass-strong-cache"
    notes := "Sub(0), its instance collected, then Sub.clear_cache(only_keys=[1]) with a same-hash key whose __eq__ raises: Python's subclass strong cache kept key 0 in the weak cache, so pop compares and raises; C's subclass branch of eject_from_strong_cache (:2463-2465) returns 0 and the weak entry is gone." },
  { id := "datetime-zoneinfo-weak-cache-attr", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C get_weak_cache", "C zoneinfo_ZoneInfo_impl", "ZoneInfo.__new__"]
    statement := "For a fresh subclass, Sub(key) behaves the same in both twins on every run, del Sub._weak_cache included."
    source := "C/Python twins", status := .refuted
    prop := ``Zone.WeakCacheAttrTwins, thm := some ``Zone.weakCacheAttrTwins_refuted
    bug := some "datetime-zoneinfo-get-weak-cache-fallback"
    notes := "After del Sub._weak_cache, C's PyObject_GetAttrString(type, \"_weak_cache\") (:299-301) raises AttributeError; Python's cls._weak_cache finds ZoneInfo._weak_cache." },
  { id := "datetime-zoneinfo-init-subclass-twins", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C zoneinfo_init_subclass", "ZoneInfo.__init_subclass__"]
    statement := "With sys.modules['weakref'] the module _zoneinfo.py imported, class S(ZoneInfo, **kw) succeeds or fails alike in both twins."
    source := "C/Python twins; data model (__init_subclass__ receives the class keywords)", status := .refuted
    prop := ``Zone.InitSubclassTwins, thm := some ``Zone.initSubclassTwins_refuted
    bug := some "datetime-zoneinfo-init-subclass"
    notes := "class S(ZoneInfo, foo=1): C ignores the keyword (METH_VARARGS | METH_KEYWORDS, :2654-2656), Python's __init_subclass__(cls) raises TypeError." },
  { id := "datetime-zoneinfo-init-subclass-weakref", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C new_weak_cache", "C zoneinfo_init_subclass", "ZoneInfo.__init_subclass__"]
    statement := "Without class keywords, the twins create a subclass alike whatever sys.modules['weakref'] is at that point."
    source := "C/Python twins", status := .refuted
    prop := ``Zone.InitSubclassWeakref, thm := some ``Zone.initSubclassWeakref_refuted
    bug := some "datetime-zoneinfo-init-subclass"
    notes := "new_weak_cache imports weakref at call time (PyImport_ImportModuleAttrString, :2595-2596); Python uses the weakref it bound at import. A replaced module without WeakValueDictionary makes C raise AttributeError." },
  { id := "datetime-zoneinfo-init-subclass-same-module", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C new_weak_cache", "C zoneinfo_init_subclass", "ZoneInfo.__init_subclass__"]
    statement := "Without class keywords and with sys.modules['weakref'] the module _zoneinfo.py imported, both twins read WeakValueDictionary from it and call it: the same outcome when the attribute is missing, when the call raises, and on success (a fresh subclass state)."
    source := "C/Python twins (narrows datetime-zoneinfo-init-subclass-twins and -weakref)", status := .proven
    prop := ``Zone.InitSubclassSameModule, thm := some ``Zone.initSubclassSameModule_proven },
  { id := "datetime-zoneinfo-cache-twins-subclass", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C zoneinfo_init_subclass", "C new_weak_cache", "C get_weak_cache", "C zone_from_strong_cache", "C update_strong_cache", "C zoneinfo_ZoneInfo_impl", "ZoneInfo.__init_subclass__", "ZoneInfo.__new__"]
    statement := "For a subclass of ZoneInfo, after __init_subclass__ runs (through new_weak_cache), every run of Sub(key) calls leaves the same keys in the strong cache in both twins."
    source := "C/Python twins", status := .refuted
    prop := ``Zone.CacheTwinsSubclass, thm := some ``Zone.cacheTwinsSubclass_refuted
    bug := some "datetime-zoneinfo-subclass-strong-cache"
    notes := "Python gives each subclass its own strong cache (_zoneinfo.py:36-38); C has none for subclasses (Modules/_zoneinfo.c:2520-2522, :2547-2549), so in C Sub(key) is Sub(key) only while a reference is held." },
  { id := "datetime-zoneinfo-clear-cache-defined", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C clear_strong_cache", "C strong_cache_free", "C strong_cache_node_free", "C zoneinfo_ZoneInfo_clear_cache_impl"]
    statement := "ZoneInfo.clear_cache() never reads or frees C memory twice, whatever the cached keys' finalizers do."
    source := "invariant (no crash)", status := .refuted
    prop := ``Zone.ClearCacheDefined, thm := some ``Zone.clearCacheDefined_refuted
    bug := some "datetime-zoneinfo-clear-cache-reentrant-free"
    notes := "strong_cache_free runs key destructors before state->ZONEINFO_STRONG_CACHE is reset (:2588-2589); a finalizer that constructs a ZoneInfo walks freed nodes." },
  { id := "datetime-zoneinfo-strong-lookup-defined", pyFile := "Modules/_zoneinfo.c"
    pyFns := ["C find_in_strong_cache", "C zone_from_strong_cache"]
    statement := "Looking a key up in the C strong cache never reads freed memory, whatever the keys' __eq__ does."
    source := "invariant (no crash)", status := .refuted
    prop := ``Zone.StrongLookupDefined, thm := some ``Zone.strongLookupDefined_refuted
    bug := some "datetime-zoneinfo-strong-cache-eq-reentry"
    notes := "Duplicate of gh-142782: an __eq__ that calls ZoneInfo.clear_cache() frees the node find_in_strong_cache reads next." },
  { id := "datetime-wrap-scan-end", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_wrap_strftime"]
    statement := "For every object, tzinfo environment and format, _wrap_strftime's scan appends nothing once the format is used up, the format's length is enough fuel (any larger fuel gives the same result), and _wrap_strftime is that scan from the start of the format with the time tuple's year, month and day."
    source := "_pydatetime.py:225-294 (while i < n; \"\".join); invariant (no early stop)", status := .proven
    prop := ``WrapScanEnd, thm := some ``wrapScanEnd_proven },
  { id := "datetime-find-sep-len7", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_find_isoformat_datetime_separator"]
    statement := "_find_isoformat_datetime_separator returns 7 for every string of length 7, whatever its characters."
    source := "_pydatetime.py:303-304", status := .proven
    prop := ``FindSepLen7, thm := some ``findSepLen7_proven },
  { id := "datetime-parse-isotime-edges", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_parse_isoformat_time"]
    statement := "_parse_isoformat_time raises 'Isoformat time too short' for fewer than two characters and 'Invalid isoformat string' for any non-ASCII string before parsing; hour 24 next to a Z or an offset sets the same flags as without one (24:00 is midnight with became_next_day, other hour-24 times set error_from_components) and keeps the offset."
    source := "_pydatetime.py:455-459, :471-478", status := .proven
    prop := ``ParseIsoTimeEdges, thm := some ``parseIsoTimeEdges_proven },
  { id := "datetime-tzinfo-reduce-body", pyFile := "Lib/_pydatetime.py"
    pyFns := ["tzinfo.__reduce__", "C tzinfo_reduce"]
    statement := "For every lookup of __getinitargs__ and every state: a lookup error propagates; a missing attribute gives () and the state; Python tests the object's truth (an error propagates), gives () for a false object without calling it and calls a true one, C calls whatever it found; an error of the call propagates before the state is asked for."
    source := "_pydatetime.py:1370-1376; _datetimemodule.c:4256-4282; pickle contract", status := .proven
    prop := ``TzinfoReduceBody, thm := some ``tzinfoReduceBody_proven },
  { id := "datetime-tzinfo-reduce-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["tzinfo.__reduce__", "C tzinfo_reduce"]
    statement := "tzinfo.__reduce__ agrees between the twins for every __getinitargs__ attribute."
    source := "C/Python twins", status := .refuted
    prop := ``TzinfoReduceTwins, thm := some ``tzinfoReduceTwins_refuted
    bug := some "datetime-pydatetime-tzinfo-reduce-truthiness"
    notes := "__getinitargs__ = None: Python's `if getinitargs:` is false and gives (); C calls None and raises TypeError." },
  { id := "datetime-tzinfo-reduce-twins-truthy", pyFile := "Lib/_pydatetime.py"
    pyFns := ["tzinfo.__reduce__", "C tzinfo_reduce"]
    statement := "tzinfo.__reduce__ returns the same value or exception in both twins whenever __getinitargs__ is missing or true (every function and bound method is true)."
    source := "C/Python twins (narrows datetime-tzinfo-reduce-twins)", status := .proven
    prop := ``TzinfoReduceTwinsTruthy, thm := some ``tzinfoReduceTwinsTruthy_proven },
  { id := "datetime-isoformat-sep-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.isoformat", "C datetime_datetime_isoformat_impl"]
    statement := "datetime.isoformat(sep, timespec) agrees between the twins for every sep object."
    source := "C/Python twins", status := .refuted
    prop := ``IsoformatSepTwins, thm := some ``isoformatSepTwins_refuted
    bug := some "datetime-pydatetime-isoformat-int-sep"
    notes := "isoformat(sep=65): Python's '%c' gives 'A', C's clinic converter raises TypeError." },
  { id := "datetime-isoformat-sep-arg", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.isoformat", "C datetime_datetime_isoformat_impl"]
    statement := "For a one-character str sep both twins give the same text; any other str is a TypeError in both; every non-str sep is a TypeError in C, while Python takes an int n in 0..0x10FFFF as chr(n) and raises OverflowError outside it."
    source := "C/Python twins; datetime.isoformat docs (one-character separator)", status := .proven
    prop := ``IsoformatSepArg, thm := some ``isoformatSepArg_proven },
  { id := "datetime-datetime-compare-all", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.__eq__", "datetime._cmp", "C datetime_richcompare", "C pep495_eq_exception"]
    statement := "datetime comparison agrees between the twins for every valid tzinfo environment and valid operands, with no assumption on the flipped-fold offsets."
    source := "C/Python twins; PEP 495", status := .refuted
    prop := ``DatetimeCompareTwinsAll, thm := some ``datetimeCompareTwinsAll_refuted
    bug := some "datetime-pydatetime-pep495-eager-flip"
    notes := "Python asks for the flipped-fold offset of both operands up front for ==; C only for otherwise-equal operands. A utcoffset that raises for fold=1 makes == raise in Python and return False in C. datetime-datetime-compare is the narrowed statement." },
  { id := "datetime-time-replace-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.replace", "C datetime_time_replace_impl"]
    statement := "time.replace agrees between the twins for every combination of omitted, None, int and other arguments, on every valid time."
    source := "C/Python twins", status := .refuted
    prop := ``TimeReplaceTwins, thm := some ``timeReplaceTwins_refuted
    bug := some "datetime-pydatetime-none-as-omitted"
    notes := "time(1, 2, 3).replace(hour=None): Python keeps the hour, C raises TypeError." },
  { id := "datetime-time-replace-int", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.replace", "C datetime_time_replace_impl", "C new_time_subclass_fold_ex"]
    statement := "time.replace with each field and fold omitted or an int within C int, and any tzinfo argument, gives in both twins exactly the time with the new fields (omitted ones from self), checked in the constructor's order with its messages."
    source := "time.replace docs; C/Python twins (narrows datetime-time-replace-twins)", status := .proven
    prop := ``TimeReplaceInt, thm := some ``timeReplaceInt_proven },
  { id := "datetime-datetime-replace-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.replace", "C datetime_datetime_replace_impl"]
    statement := "datetime.replace agrees between the twins for every combination of omitted, None, int and other arguments, on every valid datetime."
    source := "C/Python twins", status := .refuted
    prop := ``DatetimeReplaceTwins, thm := some ``datetimeReplaceTwins_refuted
    bug := some "datetime-pydatetime-none-as-omitted"
    notes := "datetime(2020, 2, 3).replace(year=None): Python keeps the year, C raises TypeError." },
  { id := "datetime-datetime-replace-int", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.replace", "C datetime_datetime_replace_impl", "C new_datetime_subclass_fold_ex"]
    statement := "datetime.replace with each field and fold omitted or an int within C int, and any tzinfo argument, gives in both twins exactly the datetime with the new fields (omitted ones from self), checked in the constructor's order with its messages."
    source := "datetime.replace docs; C/Python twins (narrows datetime-datetime-replace-twins)", status := .proven
    prop := ``DatetimeReplaceInt, thm := some ``datetimeReplaceInt_proven },
  { id := "datetime-mktime-local-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime._mktime", "C local_to_seconds", "C local", "C utc_to_seconds"]
    statement := "For every valid naive datetime and every C-library localtime whose fields a datetime accepts, Python's _mktime and C's local_to_seconds(...) - epoch give the same seconds or the same exception."
    source := "C/Python twins (narrows datetime-mktime-local-twins-all)", status := .proven
    prop := ``MktimeLocalTwins, thm := some ``mktimeLocalTwins_proven },
  { id := "datetime-mktime-local-twins-all", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime._mktime", "C local_to_seconds", "C local", "C utc_to_seconds"]
    statement := "Python's _mktime and C's local_to_seconds agree for every valid naive datetime and every C-library localtime, a leap-second zone included."
    source := "C/Python twins", status := .refuted
    prop := ``MktimeLocalTwinsAll, thm := some ``mktimeLocalTwinsAll_refuted
    bug := some "datetime-pydatetime-mktime-leap-second"
    notes := "A localtime reporting second 60: Python's local() builds datetime(..., 60) and raises ValueError; C's utc_to_seconds takes the second as it is." },
  { id := "datetime-local-timezone-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime._local_timezone", "datetime._mktime", "C local_timezone_from_local", "C local_to_seconds"]
    statement := "datetime._local_timezone and C local_timezone_from_local pick the same timestamp for every valid datetime and every localtime with fields a datetime accepts: in a gap or fold the other fold's seconds exactly when (ts2 > ts) == fold."
    source := "C/Python twins (narrows datetime-local-timezone-twins-all)", status := .proven
    prop := ``LocalTimezoneTwins, thm := some ``localTimezoneTwins_proven },
  { id := "datetime-local-timezone-twins-all", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime._local_timezone", "C local_timezone_from_local"]
    statement := "datetime._local_timezone and C local_timezone_from_local pick the same timestamp for every valid datetime and every localtime."
    source := "C/Python twins", status := .refuted
    prop := ``LocalTimezoneTwinsAll, thm := some ``localTimezoneTwinsAll_refuted
    bug := some "datetime-pydatetime-mktime-leap-second"
    notes := "datetime(1972, 7, 1).astimezone() in a leap-second zone: Python raises ValueError, C returns." }
]

end PyLean.Datetime
