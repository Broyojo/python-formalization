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

/-!
`Lib/_pydatetime.py`, `Modules/_datetimemodule.c` and `Lib/_strptime.py`, CPython 3.14.7.

Both twins of every class are modelled over ints: `timedelta`, `date`, `time`, `datetime`,
`timezone`, `tzinfo` through an abstract method table (`TzEnv`), comparison, hash, pickle,
`strftime` up to the call of `time.strftime`, `strptime` from `found.groupdict()` on, and
`fromisoformat`. Float paths, the OS clock and the local time zone are not modelled yet.
-/

namespace PyLean.Datetime

open PyLean.Registry

def entries : List Entry := [
  { id := "datetime-ordinal-roundtrip", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromordinal", "date.toordinal", "_ymd2ord", "_ord2ymd", "_is_leap", "_days_before_year", "_days_in_month", "_days_before_month", "_check_date_fields", "C date_fromordinal", "C date_toordinal", "C ord_to_ymd", "C ymd_to_ord", "C is_leap", "C days_in_month", "C days_before_month", "C days_before_year", "C check_date_args"]
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
    pyFns := ["date.isocalendar", "date.fromisocalendar", "_isoweek_to_gregorian", "_isoweek1monday", "C date_isocalendar", "C date_fromisocalendar", "C iso_week1_monday", "C weekday"]
    statement := "For every date d, date.fromisocalendar(*d.isocalendar()) == d, in both twins."
    source := "date.fromisocalendar docstring (\"inverse of the date.isocalendar() function\")", status := .proven
    prop := ``FromisocalendarIsocalendar, thm := some ``fromisocalendarIsocalendar_proven },
  { id := "datetime-fromisocalendar-exact", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromisocalendar", "date.isocalendar", "_isoweek_to_gregorian", "_isoweek1monday"]
    statement := "date.fromisocalendar(Y, W, D) succeeds only for valid ISO triples (week 53 only in years with 53 ISO weeks) and the result's isocalendar() is (Y, W, D)."
    source := "date.fromisocalendar docstring; ISO 8601 week rules", status := .proven
    prop := ``FromisocalendarExact, thm := some ``fromisocalendarExact_proven },
  { id := "datetime-fromisocalendar-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromisocalendar", "_isoweek_to_gregorian", "C date_fromisocalendar"]
    statement := "For all ints Y, W, D, C and Python date.fromisocalendar(Y, W, D) return the same date or both raise ValueError."
    source := "C/Python twins", status := .proven
    prop := ``FromisocalendarTwins, thm := some ``fromisocalendarTwins_proven },
  { id := "datetime-timedelta-ctor-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__new__", "C delta_new", "C accum", "C microseconds_to_delta_ex", "C new_delta_ex", "C check_delta_day_range", "C checked_divmod", "C normalize_pair", "C normalize_d_s_us", "C divmod"]
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
  { id := "datetime-timedelta-divmod", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__divmod__", "timedelta.__floordiv__", "timedelta.__mod__", "timedelta._to_microseconds"]
    statement := "For valid timedeltas a, b with b != 0, divmod(a, b) == (a // b, a % b) with q*b + r == a and r zero or of b's sign with |r| < |b|; for b == 0 it raises ZeroDivisionError."
    source := "timedelta docs (q, r = divmod(t1, t2)); invariant", status := .proven
    prop := ``TimedeltaDivmod, thm := some ``timedeltaDivmod_proven },
  { id := "datetime-timedelta-compare", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__eq__", "timedelta.__le__", "timedelta.__lt__", "timedelta.__ge__", "timedelta.__gt__", "timedelta._cmp", "timedelta._getstate", "_cmp", "C delta_cmp", "C delta_richcompare", "C diff_to_bool"]
    statement := "For valid timedeltas, every comparison operator agrees between C and Python and orders the durations."
    source := "C/Python twins; timedelta docs (comparison)", status := .proven
    prop := ``TimedeltaCompare, thm := some ``timedeltaCompare_proven },
  { id := "datetime-timedelta-bool-hash", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__bool__", "timedelta.__hash__", "C delta_bool", "C delta_hash"]
    statement := "bool(t) is t != timedelta(0), and equal timedeltas have the same hash key."
    source := "timedelta docs; __hash__ contract", status := .proven
    prop := ``TimedeltaBoolHash, thm := some ``timedeltaBoolHash_proven },
  { id := "datetime-timedelta-reduce", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__reduce__", "timedelta._getstate", "C delta_reduce", "C delta_getstate"]
    statement := "timedelta(*t.__reduce__()[1]) == t in both twins."
    source := "pickle contract", status := .proven
    prop := ``TimedeltaReduce, thm := some ``timedeltaReduce_proven },
  { id := "datetime-timedelta-pos-rsub", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__pos__", "timedelta.__rsub__", "C delta_positive"]
    statement := "+t == t, and b - a through __rsub__ agrees between the twins whenever -a is a timedelta."
    source := "C/Python twins", status := .proven
    prop := ``TimedeltaPosRsub, thm := some ``timedeltaPosRsub_proven
    notes := "-a out of range: timedelta.max.__rsub__ raises in Python where C does not; no reflected call reaches it from the operators." },
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
    pyFns := ["timezone.__new__", "timezone._create", "C timezone_new", "C create_timezone", "C new_timezone"]
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
    pyFns := ["time.isoformat", "time._tzstr", "_format_time", "_format_offset", "C time_isoformat", "C time_str", "C format_utcoffset"]
    statement := "time.isoformat(timespec) and str(time) agree between the twins for every timespec and tzinfo."
    source := "C/Python twins", status := .proven
    prop := ``TimeIsoformatTwins, thm := some ``timeIsoformatTwins_proven },
  { id := "datetime-datetime-isoformat-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.isoformat", "datetime.__str__", "_format_time", "_format_offset", "C datetime_isoformat", "C datetime_str", "C format_utcoffset"]
    statement := "datetime.isoformat(sep, timespec) agrees between the twins for every separator, timespec and tzinfo; str(datetime) is its sep=\" \" case."
    source := "C/Python twins", status := .proven
    prop := ``DatetimeIsoformatTwins, thm := some ``datetimeIsoformatTwins_proven },
  { id := "datetime-replace-combine", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.replace", "datetime.replace", "datetime.combine", "datetime.date", "datetime.time", "datetime.timetz", "C datetime_time_replace_impl", "C datetime_datetime_replace_impl", "C datetime_combine", "C datetime_getdate", "C datetime_gettime", "C datetime_gettimetz"]
    statement := "t.replace() == t, d.replace() == d, datetime.combine(d.date(), d.timetz()) == d, datetime.combine(d.date(), d.time(), d.tzinfo) == d, and d.time() is naive."
    source := "datetime docs", status := .proven
    prop := ``ReplaceCombine, thm := some ``replaceCombine_proven },
  { id := "datetime-time-pickle", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time._getstate", "time.__setstate", "time.__reduce_ex__", "time.__reduce__", "C time_getstate", "C time_from_pickle", "C time_reduce_ex", "C time_reduce"]
    statement := "time(*t.__reduce_ex__(p)[1]) == t in both twins, with fold kept above protocol 3 and dropped otherwise."
    source := "pickle contract; PEP 495", status := .proven
    prop := ``TimePickle, thm := some ``timePickle_proven },
  { id := "datetime-datetime-pickle", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime._getstate", "datetime.__setstate", "datetime.__reduce_ex__", "datetime.__reduce__", "C datetime_getstate", "C datetime_from_pickle", "C datetime_reduce_ex", "C datetime_reduce"]
    statement := "datetime(*d.__reduce_ex__(p)[1]) == d in both twins, with fold kept above protocol 3 and dropped otherwise."
    source := "pickle contract; PEP 495", status := .proven
    prop := ``DatetimePickle, thm := some ``datetimePickle_proven },
  { id := "datetime-time-ctor", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.__new__", "_check_time_fields", "_check_tzinfo_arg", "C time_new", "C new_time_ex2", "C check_time_args", "C check_tzinfo_subclass"]
    statement := "time(h, m, s, us, tz, fold=f) with C-int fields agrees between the twins."
    source := "C/Python twins", status := .proven
    prop := ``TimeCtorInt, thm := some ``timeCtorInt_proven
    notes := "Fields outside int: OverflowError versus ValueError is the rejected class of gh-158778." },
  { id := "datetime-datetime-ctor", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.__new__", "_check_date_fields", "_check_time_fields", "_check_tzinfo_arg", "C datetime_new", "C new_datetime_ex2", "C check_date_args", "C check_time_args", "C check_tzinfo_subclass"]
    statement := "datetime(y, m, d, h, mi, s, us, tz, fold=f) with C-int fields agrees between the twins."
    source := "C/Python twins", status := .proven
    prop := ``DatetimeCtorInt, thm := some ``datetimeCtorInt_proven
    notes := "Fields outside int: gh-158778." },
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
    statement := "date comparison agrees between the twins and == is field equality; comparing with a datetime is NotImplemented in both."
    source := "date docs; C/Python twins", status := .proven
    prop := ``DateCompare, thm := some ``dateCompare_proven },
  { id := "datetime-date-hash", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.__hash__", "date._getstate", "C date_hash", "C generic_hash", "C date_getstate"]
    statement := "Equal dates have equal hash keys in both twins."
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
    pyFns := ["date.replace", "C datetime_date_replace_impl"]
    statement := "d.replace() == d, and replace with C-int fields agrees between the twins."
    source := "date docs; C/Python twins", status := .proven
    prop := ``DateReplace, thm := some ``dateReplace_proven },
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
    statement := "repr(date) is the same text in both twins."
    source := "C/Python twins", status := .proven
    prop := ``DateRepr, thm := some ``dateRepr_proven },
  { id := "datetime-date-pickle", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date._getstate", "date.__setstate", "date.__reduce__", "C date_getstate", "C date_from_pickle", "C date_reduce"]
    statement := "date(*d.__reduce__()[1]) == d in both twins."
    source := "pickle contract", status := .proven
    prop := ``DatePickle, thm := some ``datePickle_proven },
  { id := "datetime-date-ctor", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.__new__", "_check_date_fields", "C date_new", "C new_date_ex", "C check_date_args"]
    statement := "date(y, m, d) with C-int fields agrees between the twins."
    source := "C/Python twins", status := .proven
    prop := ``DateCtorInt, thm := some ``dateCtorInt_proven
    notes := "Fields outside int: gh-158778." },
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
  { id := "datetime-strftime-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_wrap_strftime", "C wrap_strftime"]
    statement := "For every format, both twins hand the same format to time.strftime."
    source := "C/Python twins", status := .refuted
    prop := ``StrftimeTwins, thm := some ``strftimeTwins_refuted
    bug := some "datetime-strftime-bare-colon"
    notes := "A bare %: at the end of the format is dropped by Python and kept by C; '%:%Z' also differs. Still on main." },
  { id := "datetime-astimezone-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.astimezone", "C datetime_astimezone"]
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
  { id := "datetime-mktime-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime._mktime", "C local_to_seconds"]
    statement := "datetime._mktime and local_to_seconds compute the same seconds for every local-time function and either fold."
    source := "C/Python twins", status := .proven
    prop := ``MktimeTwins, thm := some ``mktimeTwins_proven },
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
    pyFns := ["date.__format__", "time.__format__", "C date_format"]
    statement := "format(x, '') is str(x) and format(x, f) is x.strftime(f) for nonempty f, for date and time, in both twins."
    source := "date.__format__ docs", status := .proven
    prop := ``FormatViaStrftime, thm := some ``formatViaStrftime_proven },
  { id := "datetime-tzinfo-reduce", pyFile := "Lib/_pydatetime.py"
    pyFns := ["tzinfo.__reduce__", "C tzinfo_reduce"]
    statement := "tzinfo.__reduce__ gives no constructor arguments without __getinitargs__, its result with one, then the state; an exception from either propagates."
    source := "pickle contract", status := .proven
    prop := ``TzinfoReduce, thm := some ``tzinfoReduce_proven },
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
    pyFns := ["_strptime", "_strptime_datetime_date", "_strptime_datetime_time", "_strptime_datetime_datetime", "_parse_tz", "C date_strptime", "C time_strptime", "C datetime_strptime"]
    statement := "When datetime.strptime succeeds, date.strptime gives its date and time.strptime its time and tzinfo, for the same match."
    source := "method vs equivalent method", status := .proven
    prop := ``StrptimeMethods, thm := some ``strptimeMethods_proven },
  { id := "datetime-strptime-wrappers", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.strptime", "time.strptime", "datetime.strptime"]
    statement := "When datetime.strptime succeeds, date.strptime gives its date and time.strptime its time and tzinfo, for the same match."
    source := "method vs equivalent method", status := .proven
    prop := ``StrptimeMethods, thm := some ``strptimeMethods_proven },
  { id := "datetime-date-isoformat-roundtrip", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.isoformat", "date.fromisoformat", "datetime.fromisoformat", "_parse_isoformat_date", "_find_isoformat_datetime_separator", "_is_ascii_digit", "C date_isoformat", "C date_str", "C date_fromisoformat", "C datetime_fromisoformat", "C tzinfo_from_isoformat_results", "C parse_isoformat_date", "C parse_digits", "C is_digit", "C _find_isoformat_datetime_separator"]
    statement := "For every date d, date.fromisoformat(d.isoformat()) == d and datetime.fromisoformat(d.isoformat()) == datetime(d.year, d.month, d.day), in both twins."
    source := "date.fromisoformat docs (\"the output of date.isoformat()\" is accepted)", status := .proven
    prop := ``DateIsoformatRoundtrip, thm := some ``dateIsoformatRoundtrip_proven },
  { id := "datetime-date-fromiso-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromisoformat", "_parse_isoformat_date", "C date_fromisoformat", "C parse_isoformat_date", "C parse_digits"]
    statement := "For every string s, C and Python date.fromisoformat(s) return the same date or both raise the same exception class."
    source := "C/Python twins", status := .refuted
    prop := ``DateFromisoTwins, thm := some ``dateFromisoTwins_refuted
    bug := some "datetime-pydatetime-fromisoformat-int-leniency"
    notes := "Python's int() on fixed-width slices accepts signs, white space and non-ASCII digits ('2020-+1-01'). Fixed on main (_read_isoformat_component). The C-only acceptance of '20040509\\u0660' (UTF-8 byte length) also breaks this property." },
  { id := "datetime-time-fromiso-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.fromisoformat", "_parse_hh_mm_ss_ff", "_parse_isoformat_time", "C time_fromisoformat", "C parse_hh_mm_ss_ff", "C parse_isoformat_time"]
    statement := "For every string s, C and Python time.fromisoformat(s) return the same time or both raise the same exception class."
    source := "C/Python twins", status := .refuted
    prop := ``TimeFromisoTwins, thm := some ``timeFromisoTwins_refuted
    bug := some "datetime-c-fromisoformat-fraction-without-decimal-mark"
    notes := "C reads digits after HHMMSS as a fraction with no '.' or ','. Other witnesses on 3.14.7: stray text before an offset ('12:30x+05:00', gh-158501, fixed on main), Python int() leniency (' 1:00')." },
  { id := "datetime-datetime-fromiso-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.fromisoformat", "_parse_isoformat_time", "C datetime_fromisoformat", "C parse_isoformat_time"]
    statement := "For every string s, C and Python datetime.fromisoformat(s) return the same datetime or both raise the same exception class."
    source := "C/Python twins", status := .refuted
    prop := ``DatetimeFromisoTwins, thm := some ``datetimeFromisoTwins_refuted
    bug := some "datetime-c-fromisoformat-nul-after-z"
    notes := "Witness '2020-01-01T12:00Z\\x00junk' (still on main). On 3.14.7 an embedded NUL also ends the time in other positions ('...T12\\x00')." },
  { id := "datetime-datetime-fromiso-bare-separator", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.fromisoformat", "_find_isoformat_datetime_separator"]
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
    bug := some "datetime-date-fromisoformat-ignores-trailing-chars" },
  { id := "datetime-time-isoformat-roundtrip", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.isoformat", "time.fromisoformat", "_parse_isoformat_time", "_parse_hh_mm_ss_ff", "_format_time", "_format_offset", "C time_fromisoformat", "C parse_isoformat_time", "C parse_hh_mm_ss_ff"]
    statement := "time.fromisoformat(t.isoformat()) == t for every time, naive or with any offset in range, in both twins."
    source := "time.fromisoformat docs", status := .open
    prop := ``TimeIsoformatRoundtrip
    notes := "Needs the digit lemmas of IsoRoundtrip carried through _parse_hh_mm_ss_ff and the sign and fraction branches of the offset, for both parsers. No counterexample in 40000 random round trips." },
  { id := "datetime-datetime-isoformat-roundtrip", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.isoformat", "datetime.fromisoformat", "_find_isoformat_datetime_separator", "C datetime_isoformat", "C datetime_fromisoformat"]
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
    pyFns := ["datetime.astimezone", "timezone.fromutc", "C datetime_astimezone", "C timezone_fromutc"]
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
    statement := "str(t) and repr(t) are the same text in both twins."
    source := "C/Python twins", status := .open
    prop := ``TimedeltaStrRepr
    notes := "String equalities between list concatenation and interpolation; the difftest shows no difference." }
]

end PyLean.Datetime
