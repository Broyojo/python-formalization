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
import PyLean.Datetime.ArgCheckProps
import PyLean.Datetime.PickleProps
import PyLean.Datetime.CmpProps2
import PyLean.Datetime.ReprProps
import PyLean.Datetime.Misc2Props
import PyLean.Datetime.FromisoBodyProps
import PyLean.Datetime.AstzProps
import PyLean.Datetime.Hollow0506Props
import PyLean.Datetime.LocalZoneProps
import PyLean.Datetime.TdFloat
import PyLean.Datetime.DeltaObjProps
import PyLean.Datetime.CalendarCProps
import PyLean.Datetime.IsoDateCProps
import PyLean.Datetime.SubclassCtor
import PyLean.Datetime.IsoformatCProps
import PyLean.Datetime.FromtimestampProps
import PyLean.Datetime.StrptimeImpl
import PyLean.Datetime.Misc3Props
import PyLean.Datetime.SubObjProps
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
  { id := "datetime-date-replace-cls", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_date_replace_impl", "C new_date_subclass_ex", "date.replace"]
    statement := "date.replace in both twins, for every receiver class (date, datetime, a subclass), valid date and omitted or C-int int fields: C builds through Py_TYPE(self) as Python's type(self)(year, month, day) does, a subclass is called with exactly the kept or given fields positionally, and a field outside C int is OverflowError in C before any construction."
    source := "C/Python twins; mirror of :3956-3961", status := .proven
    prop := ``DateReplaceCls, thm := some ``dateReplaceCls_proven },
  { id := "datetime-time-replace-cls", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_time_replace_impl", "C new_time_subclass_fold_ex"]
    statement := "C time.replace for every receiver type: for time it is tmReplaceC; for a subclass with C-int fields the class is called with the fields and tzinfo positionally and fold as a keyword only when nonzero; a field outside C int is OverflowError before any call."
    source := "mirror of :5171-5178", status := .proven
    prop := ``TimeReplaceCls, thm := some ``timeReplaceCls_proven },
  { id := "datetime-datetime-replace-cls", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_datetime_replace_impl", "C new_datetime_subclass_fold_ex"]
    statement := "C datetime.replace for every receiver type: for datetime it is dtReplaceC; for a subclass with C-int fields the class is called with the eight fields positionally and fold as a keyword only when nonzero; a field outside C int is OverflowError before any call."
    source := "mirror of :6753-6762", status := .proven
    prop := ``DatetimeReplaceCls, thm := some ``datetimeReplaceCls_proven },
  { id := "datetime-combine-cls", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_datetime_combine_impl", "C new_datetime_subclass_fold_ex"]
    statement := "C datetime.combine for every class: the date then time TypeErrors first; for datetime it is dtCombineArgC; a subclass is called with the date and time fields and the tzinfo (the time's when omitted) positionally, fold as a keyword only when the time's fold is set."
    source := "mirror of :5891-5911", status := .proven
    prop := ``CombineCls, thm := some ``combineCls_proven },
  { id := "datetime-time-strptime-cls", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_time_strptime_impl", "time.strptime", "_strptime_datetime_time"]
    statement := "time.strptime in both twins for every class: C passes its class to _strptime_datetime_time as Python does; time gives strptimeDatetimeTime's result; a subclass is called with hour, minute, second, fraction and, only with an offset, the timezone; parse and offset errors come before any call."
    source := "C/Python twins; mirror of :4793-4810 and _strptime.py:829-839", status := .proven
    prop := ``TimeStrptimeCls, thm := some ``timeStrptimeCls_proven },
  { id := "datetime-datetime-strptime-cls", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_datetime_strptime_impl", "datetime.strptime", "_strptime_datetime_datetime"]
    statement := "datetime.strptime in both twins for every class: C passes its class to _strptime_datetime_datetime as Python does; datetime gives strptimeDatetime's result; a subclass is called with the seven parsed fields and, only with an offset, the timezone; parse and offset errors come before any call."
    source := "C/Python twins; mirror of :5862-5878 and _strptime.py:841-851", status := .proven
    prop := ``DatetimeStrptimeCls, thm := some ``datetimeStrptimeCls_proven },
  { id := "datetime-time-fromisoformat-cls", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_time_fromisoformat_impl", "C tzinfo_from_isoformat_results"]
    statement := "C time.fromisoformat for every class: for time it is timeFromIsoC; the parse's error is the result for every class before any call; on success time checks the values and a subclass is called with hour, minute, second, microsecond and tzinfo positionally, unchecked."
    source := "mirror of :5191-5258", status := .proven
    prop := ``TimeFromIsoCls, thm := some ``timeFromIsoCls_proven },
  { id := "datetime-datetime-fromisoformat-cls", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_datetime_fromisoformat_impl", "C _sanitize_isoformat_str", "C new_datetime_subclass_ex"]
    statement := "C datetime.fromisoformat for every class, on the code points of any str: a surrogate-free string is datetimeFromIsoC for datetime; a surrogate at the separator position the sanitizer picks behaves as T; a surrogate left after sanitizing is ValueError; the parse's error is the result for every class; on success a subclass is called with the eight values positionally, no fold keyword."
    source := "mirror of :6079-6194", status := .proven
    prop := ``DatetimeFromIsoCls, thm := some ``datetimeFromIsoCls_proven },
  { id := "datetime-sanitize-isoformat-full", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C _sanitize_isoformat_str"]
    statement := "_sanitize_isoformat_str on every path: NULL below 7 code points; the first of positions 7, 8, 10 holding a surrogate (index len read as NUL, stopping past it) becomes T and nothing else changes; with none there the string is unchanged."
    source := "mirror of :5914-5966; code comment (:5922-5926)", status := .proven
    prop := ``SanitizeIsoformatFull, thm := some ``sanitizeIsoformatFull_proven },
  { id := "datetime-find-sep-twins", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C _find_isoformat_datetime_separator", "_find_isoformat_datetime_separator"]
    statement := "C _find_isoformat_datetime_separator (on UTF-8 bytes) and Python's (on code points) give the same separator index on every ASCII string of at least 7 characters, on every branch, and C's -1 exactly where Python raises ValueError('Invalid ISO string')."
    source := "C/Python twins", status := .proven
    prop := ``FindSepTwins, thm := some ``findSepTwins_proven },
  { id := "datetime-date-reduce-cls", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C date_reduce", "date.__reduce__"]
    statement := "date.__reduce__ in both twins is (type(self), (bytes,)) with the receiver's own type for every class, and date(*state) gives every valid date back in both twins."
    source := "C/Python twins; pickle contract", status := .proven
    prop := ``DateReduceCls, thm := some ``dateReduceCls_proven },
  { id := "datetime-time-reduce-ex-cls", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_time___reduce_ex___impl", "C datetime_time___reduce___impl", "time.__reduce_ex__", "time.__reduce__"]
    statement := "time.__reduce_ex__(p) in C for every receiver type: the clinic int converter first (OverflowError outside C int, a failure for objects without __index__), then (type(self), state); for every p in C int it is Python's (self.__class__, self._getstate(p)), and __reduce__ is the protocol-2 state in both twins."
    source := "C/Python twins; mirror of :5297-5311 and clinic .h:1234-1247", status := .proven
    prop := ``TimeReduceExCls, thm := some ``timeReduceExCls_proven },
  { id := "datetime-datetime-reduce-ex-cls", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_datetime___reduce_ex___impl", "C datetime_datetime___reduce___impl", "datetime.__reduce_ex__", "datetime.__reduce__"]
    statement := "datetime.__reduce_ex__(p) in C for every receiver type: the clinic int converter first, then (type(self), state); for every p in C int it is Python's, and __reduce__ is the protocol-2 state in both twins."
    source := "C/Python twins; mirror of :7229-7245 and clinic .h:2063-2076", status := .proven
    prop := ``DatetimeReduceExCls, thm := some ``datetimeReduceExCls_proven },
  { id := "datetime-time-reduce-ex-all-int", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_time___reduce_ex___impl", "time.__reduce_ex__"]
    statement := "time.__reduce_ex__(p) agrees between C and Python for every valid time and every int p."
    source := "C/Python twins", status := .refuted
    prop := ``TimeReduceExTwinsAllInt, thm := some ``timeReduceExTwinsAllInt_refuted
    bug := some "datetime-reduce-ex-protocol-int-converter"
    notes := "p = 2**31: C OverflowError from the clinic int converter, Python returns the state." },
  { id := "datetime-datetime-reduce-ex-all-int", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_datetime___reduce_ex___impl", "datetime.__reduce_ex__"]
    statement := "datetime.__reduce_ex__(p) agrees between C and Python for every valid datetime and every int p."
    source := "C/Python twins", status := .refuted
    prop := ``DatetimeReduceExTwinsAllInt, thm := some ``datetimeReduceExTwinsAllInt_refuted
    bug := some "datetime-reduce-ex-protocol-int-converter"
    notes := "p = 2**31: C OverflowError, Python returns the state." },
  { id := "datetime-tzinfo-reduce-cls", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C tzinfo_reduce", "tzinfo.__reduce__"]
    statement := "tzinfo.__reduce__ in both twins for every receiver type: (type(self), args, state) with tzinfoReduceC's / tzinfoReducePy's args and state, so the triples agree where those do, and the first element is always the receiver's type."
    source := "C/Python twins; mirror of :4257-4283", status := .proven
    prop := ``TzinfoReduceCls, thm := some ``tzinfoReduceCls_proven },
  { id := "datetime-isocalendar-date-obj", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C iso_calendar_date_year", "C iso_calendar_date_week", "C iso_calendar_date_weekday", "C iso_calendar_date_reduce", "C iso_calendar_date_new_impl", "C date_isocalendar"]
    statement := "IsoCalendarDate in C: for C-int fields the object is the 3-tuple Python builds, year/week/weekday read items 0/1/2 (never PyTuple_GetItem's NULL) as Python's self[0..2] do, __reduce__ is the same plain tuple, a field outside C int is OverflowError; isocalendar()'s attributes are the ISO triple fromisocalendar inverts."
    source := "C/Python twins; mirror of :3743-3876", status := .proven
    prop := ``IsoCalendarDateObj, thm := some ``isoCalendarDateObj_proven },
  { id := "datetime-date-toordinal-c", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C date_toordinal", "C ymd_to_ord"]
    statement := "C date.toordinal() (ymd_to_ord of the fields) equals Python's toordinal on every valid date, lies in 1..date.max.toordinal(), and C date.fromordinal of it gives the date back."
    source := "C/Python twins; toordinal docs", status := .proven
    prop := ``DateToordinalC, thm := some ``dateToordinalC_proven },
  { id := "datetime-timezone-richcompare", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C timezone_richcompare", "timezone.__eq__"]
    statement := "timezone comparison in both twins for every operator and right operand: == and != against a timezone compare offsets only and != negates ==; <, <=, >, >= and any operator against a non-timezone are NotImplemented."
    source := "C/Python twins", status := .proven
    prop := ``TimezoneRichcompare, thm := some ``timezoneRichcompare_proven },
  { id := "datetime-init-types-twins", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C _PyDateTime_InitTypes", "C create_timezone_from_delta", "C look_up_timezone", "C create_timezone"]
    statement := "The class attributes timedelta/date/time/datetime min, max, resolution and timezone utc/min/max are the same values in C (built by new_delta, new_date, new_time, new_datetime, create_timezone_from_delta) and Python; timezone.min/max are -/+23:59; create_timezone_from_delta reaches look_up_timezone's utc branch exactly for a zero offset."
    source := "C/Python twins; datetime docs (class attributes)", status := .proven
    prop := ``InitTypesTwins, thm := some ``initTypesTwins_proven },
  { id := "datetime-datetime-str-call", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_str", "datetime.__str__"]
    statement := "str(dt) calls the object's own isoformat in both twins, C with ' ' positional and Python with sep=' '; for the built-in isoformat both are dt.isoformat(' ')."
    source := "C/Python twins; datetime.__str__ docs", status := .proven
    prop := ``DatetimeStrCall, thm := some ``datetimeStrCall_proven },
  { id := "datetime-datetime-str-twins", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_str", "datetime.__str__"]
    statement := "str(dt) agrees between the twins for every isoformat a subclass defines."
    source := "C/Python twins", status := .refuted
    prop := ``DatetimeStrTwins, thm := some ``datetimeStrTwins_refuted
    bug := some "datetime-pydatetime-str-isoformat-alias"
    notes := "An override isoformat(self, *a, **k) sees (' ',) in C and sep=' ' in Python." },
  { id := "datetime-now-checks", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_datetime_now_impl"]
    statement := "datetime.now(tz) in C: a tz that is neither None nor a tzinfo is TypeError whatever the clock does; None is the local reading; a tzinfo gets the UTC reading passed to its fromutc, whose result or exception is returned, a clock error first."
    source := "mirror of :5721-5743 (the clock is a parameter)", status := .proven
    prop := ``DatetimeNowChecks, thm := some ``datetimeNowChecks_proven },
  { id := "datetime-add-timedelta-obj", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C add_datetime_timedelta", "C new_datetime_subclass_ex", "C new_datetime_subclass_fold_ex", "C call_subclass_fold"]
    statement := "C datetime +/- timedelta (add_datetime_timedelta) for every receiver type: a normalization error comes before any constructor call; for datetime itself the result is the base model (pinned against Python elsewhere); for a subclass the class is called once with the eight normalized fields and the receiver's tzinfo positionally, no fold keyword, and its result (any object) is returned."
    source := "mirror of :6241-6266 and :1288-1314", status := .proven
    prop := ``AddDatetimeTimedeltaObj, thm := some ``addDatetimeTimedeltaObj_proven },
  { id := "datetime-utctimetuple-obj", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_utctimetuple", "C add_datetime_timedelta"]
    statement := "C utctimetuple for every receiver type: for datetime it is the base model; for a subclass with an aware receiver and any timedelta offset, zero included, the subclass is called on the normalized self - offset fields and the struct_time is the returned datetime's fields; a naive receiver or a None offset never calls it."
    source := "mirror of :7154-7191", status := .proven
    prop := ``UtctimetupleObj, thm := some ``utctimetupleObj_proven },
  { id := "datetime-utctimetuple-obj-defined", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_utctimetuple", "C add_datetime_timedelta"]
    statement := "C utctimetuple never reads the datetime fields of an object that is not a datetime."
    source := "invariant (no memory-unsafe reads)", status := .refuted
    prop := ``UtctimetupleObjDefined, thm := some ``utctimetupleObjDefined_refuted
    bug := some "datetime-subclass-arith-result-type-confusion"
    notes := "A subclass __new__ returning bytearray(200) gives struct_time (0, 0, 0, 0, 0, 0, -2, 0, 0) on 3.15.2 and main; same root cause as gh-145166." },
  { id := "datetime-astimezone-obj", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_datetime_astimezone_impl", "C add_datetime_timedelta"]
    statement := "C astimezone for every receiver type: for datetime with the built-in fromutc it is the base model dtAstimezoneFullC; for a subclass, an aware receiver, a target that is not its own tzinfo and a timedelta offset, the subclass is called once on the normalized self - offset fields with the receiver's tzinfo, and the returned datetime, given tzinfo tz (rebuilt aware in its own type if it was naive), is passed to tz.fromutc, whose result is returned."
    source := "mirror of :6914-7004", status := .proven
    prop := ``AstimezoneObj, thm := some ``astimezoneObj_proven },
  { id := "datetime-astimezone-obj-defined", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_datetime_astimezone_impl", "C add_datetime_timedelta"]
    statement := "C astimezone never reads or writes the tzinfo slot of an object that is not a datetime."
    source := "invariant (no crash)", status := .refuted
    prop := ``AstimezoneObjDefined, thm := some ``astimezoneObjDefined_refuted
    bug := some "datetime-subclass-arith-result-type-confusion"
    notes := "Segfault on 3.15.2 and main when the subclass __new__ returns 1 or three zero bytes; open PR #145181 (gh-145166) would add the check in add_datetime_timedelta." },
  { id := "datetime-pep495-obj-same-kind", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C pep495_eq_exception", "C delta_cmp"]
    statement := "When each side's offset and flip offset are both None or both timedeltas, C pep495_eq_exception (pointer test, then delta_cmp) equals Python's value test in _cmp(allow_mixed=True), errors of either flip-offset call included, and the second flip offset is consulted only when the first test does not fire."
    source := "C/Python twins; mirror of :6560-6586", status := .proven
    prop := ``Pep495ObjSameKind, thm := some ``pep495ObjSameKind_proven },
  { id := "datetime-pep495-obj-defined", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C pep495_eq_exception", "C delta_cmp"]
    statement := "pep495_eq_exception never reads a non-timedelta as a timedelta: for all None/timedelta offsets and flip offsets its result is defined."
    source := "invariant (no out-of-object reads)", status := .refuted
    prop := ``Pep495ObjDefined, thm := some ``pep495ObjDefined_refuted
    bug := some "datetime-pep495-delta-cmp-none"
    notes := "utcoffset None for fold 0 and timedelta(0) for fold 1: C == is True, Python False, on 3.15.2 and main." },
  { id := "datetime-ordinal-roundtrip", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromordinal", "date.toordinal", "_ymd2ord", "_ord2ymd", "_is_leap", "_days_before_year", "_days_in_month", "_days_before_month", "_check_date_fields", "C datetime_date_fromordinal_impl", "C date_toordinal", "C ord_to_ymd", "C ymd_to_ord", "C is_leap", "C days_in_month", "C check_date_args"]
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
    pyFns := ["timedelta.__new__", "C delta_new_impl", "C accum", "C microseconds_to_delta_ex", "C check_delta_day_range"]
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
    pyFns := ["timedelta.__add__", "timedelta.__sub__", "timedelta.__neg__", "timedelta.__abs__", "timedelta.__mul__", "timedelta.__floordiv__", "timedelta.__truediv__", "timedelta.__mod__", "timedelta.__divmod__", "timedelta._to_microseconds", "_divide_and_round", "C delta_add", "C delta_subtract", "C delta_negative", "C delta_abs", "C delta_divide", "C delta_remainder", "C delta_divmod", "C multiply_int_timedelta", "C divide_timedelta_int", "C divide_timedelta_timedelta", "C truedivide_timedelta_int", "C divide_nearest", "C delta_to_microseconds", "C normalize_d_s_us", "C normalize_pair", "C divmod"]
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
    pyFns := ["timedelta.__reduce__", "timedelta._getstate", "C delta_getstate"]
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
    pyFns := ["timezone.utcoffset", "timezone.dst", "timezone.__eq__", "timezone.__hash__", "C timezone_utcoffset", "C timezone_dst", "C timezone_richcompare", "C timezone_hash"]
    statement := "For every timezone: utcoffset is its offset, dst is None, == compares offsets only and agrees between the twins, ordering is NotImplemented, equal timezones hash alike."
    source := "timezone docs; C/Python twins", status := .proven
    prop := ``TimezoneMethods, thm := some ``timezoneMethods_proven },
  { id := "datetime-timezone-new", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timezone.__new__", "timezone._create", "C timezone_new_impl", "C create_timezone", "C new_timezone", "C look_up_timezone"]
    statement := "timezone(offset[, name]) agrees between the twins for every valid timedelta and name; a zero offset without a name is timezone.utc in both, a zero offset with a name and every nonzero in-range offset a new timezone."
    source := "C/Python twins; timezone docs", status := .proven
    prop := ``TimezoneNew, thm := some ``timezoneNew_proven },
  { id := "datetime-time-offsets", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.utcoffset", "time.dst", "_check_utc_offset", "C call_tzinfo_method", "C call_utcoffset", "C call_dst", "C time_utcoffset", "C time_dst"]
    statement := "time.utcoffset() and time.dst() agree between the twins for every tzinfo, and an offset returned is strictly inside 24 hours."
    source := "tzinfo docs; C/Python twins", status := .proven
    prop := ``TimeOffsets, thm := some ``timeOffsets_proven },
  { id := "datetime-datetime-offsets", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.utcoffset", "datetime.dst", "_check_utc_offset", "C call_tzinfo_method", "C call_utcoffset", "C call_dst", "C datetime_utcoffset", "C datetime_dst"]
    statement := "datetime.utcoffset() and datetime.dst() agree between the twins for every tzinfo, and an offset returned is strictly inside 24 hours."
    source := "tzinfo docs; C/Python twins", status := .proven
    prop := ``DatetimeOffsets, thm := some ``datetimeOffsets_proven },
  { id := "datetime-tzname-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.tzname", "datetime.tzname", "_check_tzname", "C time_tzname", "C datetime_tzname", "C call_tzname"]
    statement := "tzname() agrees between the twins in value or exception class for every tzinfo."
    source := "C/Python twins", status := .proven
    prop := ``TznameTwins, thm := some ``tznameTwins_proven },
  { id := "datetime-time-repr", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.__repr__", "_get_class_module", "C time_repr", "C append_keyword_tzinfo"]
    statement := "repr(time) of the base class is the same text in both twins."
    source := "C/Python twins", status := .proven
    prop := ``TimeRepr, thm := some ``timeRepr_proven },
  { id := "datetime-datetime-repr", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.__repr__", "_get_class_module", "C datetime_repr", "C append_keyword_tzinfo"]
    statement := "repr(datetime) of the base class is the same text in both twins unless both fold and tzinfo are set."
    source := "C/Python twins", status := .proven
    prop := ``DatetimeRepr, thm := some ``datetimeRepr_proven
    notes := "With fold=1 and a tzinfo the keywords come in a different order: C prints fold first, Python tzinfo first; refuted on record as datetime-repr-fold-tzinfo-twins." },
  { id := "datetime-time-isoformat-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.isoformat", "time._tzstr", "_format_time", "_format_offset", "C datetime_time_isoformat_impl", "C format_utcoffset"]
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
    pyFns := ["date.strptime"]
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
    pyFns := ["date.fromtimestamp", "C date_fromtimestamp", "C datetime_date_fromtimestamp_impl"]
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
    pyFns := ["_check_date_fields", "date.__new__", "C check_date_args", "C datetime_date", "C PyLong_AsInt"]
    statement := "For all arguments, _check_date_fields equals C's clinic date() conversions plus check_date_args whenever every argument fits a C int; __index__ results are the fields, an exception of __index__ propagates unchanged in argument order, and a non-int __index__ result or a float is a TypeError."
    source := "operator.index docs; C/Python twins", status := .proven
    prop := ``CheckDateFieldsIndex, thm := some ``checkDateFieldsIndex_proven },
  { id := "datetime-date-new-index-missing", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.__new__", "_check_date_fields", "C date_new", "C datetime_date"]
    statement := "date(a, b) where a.__index__ raises e and b is not None raises e in Python (day=None is reached after a's conversion) and TypeError for the missing day in C."
    source := "C/Python twins (the case DateNewArgs excludes)", status := .proven
    prop := ``DateNewIndexMissing, thm := some ``dateNewIndexMissing_proven },
  { id := "datetime-check-time-fields-index", pyFile := "Lib/_pydatetime.py"
    pyFns := ["_check_time_fields", "time.__new__", "C check_time_args", "C datetime_time", "C time_new", "C PyLong_AsInt"]
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
    statement := "date.fromordinal(x) for every argument: an int is the int-level model in each twin; an object whose __index__ returns n is fromordinal(n) in C and a TypeError in Python; an exception of __index__ propagates in C; every argument without __index__ (None, str, bytes, any other object) is a TypeError in both; a float is a TypeError in C and runs _ord2ymd on floats in Python (date.fromordinal(0.1) is AssertionError, date.fromordinal(1.5) a TypeError from >>)."
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
    pyFns := ["date.year", "date.month", "date.day", "time.hour", "time.minute", "time.second", "time.microsecond", "datetime.hour", "datetime.minute", "datetime.second", "datetime.microsecond", "C date_year", "C time_hour", "C time_minute", "C py_time_second", "C time_microsecond", "C datetime_hour", "C datetime_minute", "C datetime_second", "C datetime_microsecond", "C set_date_fields"]
    statement := "For every valid object, each C accessor reads back from the packed bytes the field the Python class keeps as an attribute."
    source := "C/Python twins", status := .proven
    prop := ``PackedAccessors, thm := some ``packedAccessors_proven },
  { id := "datetime-format-via-strftime", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.__format__", "time.__format__", "C datetime_date___format___impl", "C datetime_time___format___impl"]
    statement := "format(x, '') is str(x) and format(x, f) is x.strftime(f) for nonempty f, for date and time, in both twins."
    source := "date.__format__ docs", status := .proven
    prop := ``FormatViaStrftime, thm := some ``formatViaStrftime_proven },
  { id := "datetime-sanitize-isoformat", pyFile := "Lib/_pydatetime.py"
    pyFns := ["C _sanitize_isoformat_str"]
    statement := "Short strings fail, a string with no surrogate at positions 7, 8 or 10 comes back unchanged, and a surrogate at 7 becomes T."
    source := "code comment (:5922-5926)", status := .proven
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
    pyFns := ["_strptime", "_strptime_datetime_date", "_strptime_datetime_time", "_strptime_datetime_datetime", "_parse_tz", "C datetime_time_strptime_impl", "C datetime_datetime_strptime_impl"]
    statement := "When datetime.strptime succeeds, date.strptime gives its date and time.strptime its time and tzinfo, for the same match."
    source := "method vs equivalent method", status := .proven
    prop := ``StrptimeMethods, thm := some ``strptimeMethods_proven },
  { id := "datetime-strptime-wrappers", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.strptime", "time.strptime", "datetime.strptime"]
    statement := "When datetime.strptime succeeds, date.strptime gives its date and time.strptime its time and tzinfo, for the same match."
    source := "method vs equivalent method", status := .proven
    prop := ``StrptimeMethods, thm := some ``strptimeMethods_proven },
  { id := "datetime-date-isoformat-roundtrip", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.isoformat", "date.fromisoformat", "datetime.fromisoformat", "_parse_isoformat_date", "_read_isoformat_component", "_find_isoformat_datetime_separator", "_is_ascii_digit", "C date_isoformat", "C datetime_date_fromisoformat_impl", "C datetime_datetime_fromisoformat_impl", "C tzinfo_from_isoformat_results", "C parse_isoformat_date", "C _find_isoformat_datetime_separator"]
    statement := "For every date d, date.fromisoformat(d.isoformat()) == d and datetime.fromisoformat(d.isoformat()) == datetime(d.year, d.month, d.day), in both twins."
    source := "date.fromisoformat docs (\"the output of date.isoformat()\" is accepted)", status := .proven
    prop := ``DateIsoformatRoundtrip, thm := some ``dateIsoformatRoundtrip_proven },
  { id := "datetime-date-fromiso-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["date.fromisoformat", "C datetime_date_fromisoformat_impl", "C parse_isoformat_date"]
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
    pyFns := ["time._cmp", "time.__eq__", "time.__le__", "time.__lt__", "time.__ge__", "time.__gt__", "_cmp", "C time_richcompare", "C diff_to_bool"]
    statement := "With whole-minute offsets, time comparison agrees between the twins for every operator: the same tzinfo, equal offsets of different tzinfos, naive against aware (== False, != True, ordering TypeError in both), and different offsets compared in UTC."
    source := "C/Python twins (narrows datetime-time-compare-twins)", status := .proven
    prop := ``TimeCompareWholeMinutes, thm := some ``timeCompareWholeMinutes_proven },
  { id := "datetime-astimezone-to-timezone", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.astimezone", "timezone.fromutc", "C datetime_datetime_astimezone_impl", "C timezone_fromutc"]
    statement := "astimezone to a timezone agrees between the twins when utcoffset(self) is a timedelta in range."
    source := "C/Python twins", status := .proven
    prop := ``AstimezoneToTimezone, thm := some ``astimezoneToTimezone_proven },
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
    source := "_pydatetime.py:1370-1376; _datetimemodule.c:4257-4283; pickle contract", status := .proven
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
    notes := "datetime(1972, 7, 1).astimezone() in a leap-second zone: Python raises ValueError, C returns." },
  { id := "datetime-timezone-method-args", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timezone.utcoffset", "timezone.tzname", "timezone.dst", "timezone.fromutc", "C timezone_utcoffset", "C timezone_tzname", "C timezone_dst", "C timezone_fromutc", "C _timezone_check_argument"]
    statement := "For every valid timezone and every argument: one that is neither a datetime nor None is a TypeError in both twins for utcoffset, tzname and dst; otherwise utcoffset is the offset, dst None and tzname the name, the same in both; fromutc refuses None and other objects with TypeError in both and agrees on valid datetimes."
    source := "timezone docs; C/Python twins", status := .proven
    prop := ``TimezoneMethodArgs, thm := some ``timezoneMethodArgs_proven },
  { id := "datetime-timezone-new-arg", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timezone.__new__", "C timezone_new_impl"]
    statement := "timezone(offset, name) on every offset object: a non-timedelta offset is a TypeError in both twins whatever the name; a timedelta agrees between the twins."
    source := "timezone docs; C/Python twins", status := .proven
    prop := ``TimezoneNewArg, thm := some ``timezoneNewArg_proven },
  { id := "datetime-timezone-getinitargs", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timezone.__getinitargs__", "C timezone_getinitargs"]
    statement := "For every valid timezone, __getinitargs__ is the same in both twins, the one-tuple (offset,) exactly when there is no name, and timezone(*args) rebuilds a timezone with the same offset and name (timezone.utc itself for timezone.utc)."
    source := "pickle contract; C/Python twins", status := .proven
    prop := ``TimezoneGetinitargs, thm := some ``timezoneGetinitargs_proven },
  { id := "datetime-timezone-hash", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timezone.__hash__", "C timezone_hash"]
    statement := "hash(timezone) uses the same key in both twins, the key of its offset, and two timezones hash alike exactly when their offsets are equal."
    source := "C/Python twins; hash/eq contract", status := .proven
    prop := ``TimezoneHash, thm := some ``timezoneHash_proven },
  { id := "datetime-combine-args", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.combine", "C datetime_datetime_combine_impl"]
    statement := "datetime.combine on every argument: a non-date first argument, then a non-time second argument, is a TypeError in both twins; for a valid date and time and a tzinfo omitted or given (not True), both give exactly the datetime of their fields with the time's fold and the time's (or the given) tzinfo."
    source := "datetime.combine docs; C/Python twins", status := .proven
    prop := ``CombineArgs, thm := some ``combineArgs_proven },
  { id := "datetime-combine-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.combine", "C datetime_datetime_combine_impl"]
    statement := "datetime.combine agrees between the twins for every valid date and time and every tzinfo argument."
    source := "C/Python twins", status := .refuted
    prop := ``CombineTwins, thm := some ``combineTwins_refuted
    bug := some "datetime-pydatetime-none-as-omitted"
    notes := "tzinfo=True: Python's `if tzinfo is True` keeps the time's tzinfo, C passes True to check_tzinfo_subclass and raises TypeError." },
  { id := "datetime-astimezone-arg", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.astimezone", "C datetime_datetime_astimezone_impl"]
    statement := "datetime.astimezone(tz) with tz neither None nor a tzinfo is a TypeError in both twins for every datetime and tzinfo environment, before any tzinfo method or the local zone is consulted."
    source := "datetime.astimezone docs; C/Python twins", status := .proven
    prop := ``AstimezoneArg, thm := some ``astimezoneArg_proven },
  { id := "datetime-time-format", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.__format__", "C datetime_time___format___impl"]
    statement := "format(t, fmt) agrees between the twins for every fmt and every result of str and strftime: a non-str fmt is a TypeError in both, '' gives str(t) and a nonempty format t.strftime(fmt)."
    source := "time.__format__ docs; C/Python twins", status := .proven
    prop := ``TimeFormat, thm := some ``timeFormat_proven },
  { id := "datetime-fromiso-arg", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.fromisoformat", "datetime.fromisoformat", "C datetime_time_fromisoformat_impl", "C datetime_datetime_fromisoformat_impl"]
    statement := "time.fromisoformat and datetime.fromisoformat raise TypeError in both twins for a non-str argument; time.fromisoformat raises ValueError in both for a str with a lone surrogate."
    source := "fromisoformat docs; C/Python twins", status := .proven
    prop := ``FromisoArg, thm := some ``fromisoArg_proven },
  { id := "datetime-time-fromiso-body", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.fromisoformat"]
    statement := "time.fromisoformat(s), by what _parse_isoformat_time returns for s without a leading T: a parser ValueError becomes 'Invalid isoformat string', another exception propagates, error_from_tz is raised, error_from_components is the hour-24 ValueError, otherwise the parsed time checked by the constructor."
    source := "_pydatetime.py:1653-1670", status := .proven
    prop := ``TimeFromIsoBody, thm := some ``timeFromIsoBody_proven },
  { id := "datetime-time-reduce-roundtrip", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time._getstate", "time.__reduce_ex__", "time.__reduce__", "time.__setstate", "time.__new__", "C time_getstate", "C datetime_time___reduce_ex___impl", "C datetime_time___reduce___impl", "C time_from_pickle", "C time_new"]
    statement := "For every valid time and protocol p as the C impl receives it (after the clinic int converter, which rejects p outside C int: datetime-time-reduce-ex-all-int), both twins' __reduce_ex__(p) give the same state tuple (with the tzinfo when there is one), __reduce__ is __reduce_ex__(2), and time(*state) gives back the time with its tzinfo, its fold above protocol 3 and fold 0 otherwise, in both twins."
    source := "pickle contract; PEP 495; C/Python twins", status := .proven
    prop := ``TimeReduceRoundtrip, thm := some ``timeReduceRoundtrip_proven },
  { id := "datetime-datetime-reduce-roundtrip", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime._getstate", "datetime.__reduce_ex__", "datetime.__reduce__", "datetime.__setstate", "datetime.__new__", "C datetime_getstate", "C datetime_datetime___reduce_ex___impl", "C datetime_datetime___reduce___impl", "C datetime_from_pickle", "C datetime_new"]
    statement := "For every valid datetime and protocol p as the C impl receives it (after the clinic int converter: datetime-datetime-reduce-ex-all-int), both twins' __reduce_ex__(p) give the same state tuple, __reduce__ is __reduce_ex__(2), and datetime(*state) gives back the datetime with its tzinfo, its fold above protocol 3 and fold 0 otherwise, in both twins."
    source := "pickle contract; PEP 495; C/Python twins", status := .proven
    prop := ``DatetimeReduceRoundtrip, thm := some ``datetimeReduceRoundtrip_proven },
  { id := "datetime-time-new-pickle", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.__new__", "time.__setstate", "C time_new", "C time_from_pickle"]
    statement := "time(state, tzinfo) for every byte string: the header test selects the pickle branch, which decodes hour, fold, minute, second and microsecond unchecked and keeps a None or tzinfo argument in both twins; another non-falsy second argument is TypeError('bad tzinfo state arg') in both; a str state above U+00FF is the latin-1 ValueError in both; bytes failing the header are a TypeError in both."
    source := "pickle contract; C/Python twins", status := .proven
    prop := ``TimeNewPickle, thm := some ``timeNewPickle_proven },
  { id := "datetime-datetime-new-pickle", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.__new__", "datetime.__setstate", "C datetime_new", "C datetime_from_pickle"]
    statement := "datetime(state, tzinfo) for every byte string: the header test selects the pickle branch, which decodes every field and fold unchecked and keeps a None or tzinfo argument in both twins; any other second argument is TypeError('bad tzinfo state arg') in both; a str state above U+00FF is the latin-1 ValueError in both; bytes failing the header are a TypeError in both."
    source := "pickle contract; C/Python twins", status := .proven
    prop := ``DatetimeNewPickle, thm := some ``datetimeNewPickle_proven },
  { id := "datetime-time-repr-cls", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.__repr__", "_get_class_module", "C time_repr", "C append_keyword_tzinfo"]
    statement := "repr(time) is the same text in both twins for the base class and every subclass whose __qualname__ is its __name__ and whose module is not named datetime, for every field value, tzinfo and fold."
    source := "C/Python twins", status := .proven
    prop := ``TimeReprCls, thm := some ``timeReprCls_proven },
  { id := "datetime-time-repr-cls-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.__repr__", "_get_class_module", "C time_repr"]
    statement := "repr(time) is the same text in both twins for every class."
    source := "C/Python twins", status := .refuted
    prop := ``TimeReprClsTwins, thm := some ``timeReprClsTwins_refuted
    bug := some "datetime-repr-qualname-vs-tp-name"
    notes := "A nested subclass: Python prints __qualname__ (Outer.T(1, 2)), C tp_name (T(1, 2))." },
  { id := "datetime-datetime-repr-cls", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.__repr__", "_get_class_module", "C datetime_repr", "C append_keyword_tzinfo"]
    statement := "repr(datetime) is the same text in both twins for the base class and every plain subclass, for every valid datetime without both fold=1 and a tzinfo."
    source := "C/Python twins (narrows datetime-repr-fold-tzinfo-twins)", status := .proven
    prop := ``DatetimeReprCls, thm := some ``datetimeReprCls_proven },
  { id := "datetime-repr-fold-tzinfo-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.__repr__", "C datetime_repr"]
    statement := "repr(datetime) of the base class is the same text in both twins for every valid datetime, fold=1 with a tzinfo included."
    source := "C/Python twins", status := .refuted
    prop := ``DatetimeReprFoldTzTwins, thm := some ``datetimeReprFoldTzTwins_refuted
    bug := some "datetime-repr-fold-tzinfo-order"
    notes := "C appends fold before tzinfo, Python after." },
  { id := "datetime-tzinfo-base-dispatch", pyFile := "Lib/_pydatetime.py"
    pyFns := ["tzinfo.tzname", "tzinfo.utcoffset", "tzinfo.dst", "C tzinfo_nogo", "C tzinfo_tzname", "C tzinfo_utcoffset", "C tzinfo_dst"]
    statement := "For a tzinfo subclass that does not override utcoffset, dst or tzname, datetime.utcoffset()/dst()/tzname() and time.utcoffset()/dst()/tzname() run the base method and raise NotImplementedError in both twins, with each twin's message."
    source := "tzinfo docs (subclasses must override); C/Python twins", status := .proven
    prop := ``TzinfoBaseDispatch, thm := some ``tzinfoBaseDispatch_proven },
  { id := "datetime-isocalendardate-new", pyFile := "Lib/_pydatetime.py"
    pyFns := ["IsoCalendarDate.__new__"]
    statement := "IsoCalendarDate(year, week, weekday) with ints within C int holds the same three items in both twins, unchecked; Python stores any three objects as they are."
    source := "IsoCalendarDate (date.isocalendar docs); C/Python twins", status := .proven
    prop := ``IsoCalendarDateNew, thm := some ``isoCalendarDateNew_proven },
  { id := "datetime-isocalendardate-new-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["IsoCalendarDate.__new__"]
    statement := "IsoCalendarDate(year, week, weekday) agrees between the twins for every argument."
    source := "C/Python twins", status := .refuted
    prop := ``IsoCalendarDateNewTwins, thm := some ``isoCalendarDateNewTwins_refuted
    bug := some "datetime-pydatetime-fold-ordinal-no-index"
    notes := "IsoCalendarDate('a', 2, 3): Python stores the str, C's int converter raises TypeError." },
  { id := "datetime-strptime-time-datetime", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.strptime", "datetime.strptime", "C datetime_time_strptime_impl", "C datetime_datetime_strptime_impl"]
    statement := "time.strptime and datetime.strptime for every parse: a _strptime exception propagates; without an offset they are the naive time/datetime of the parsed fields through the constructor; with one they attach _parse_tz's timezone; and '%H:%M' on 12:30 is time(12, 30), '%Y %m %d %H %M' on 2024 1 2 12 30 is datetime(2024, 1, 2, 12, 30)."
    source := "time.strptime/datetime.strptime docs", status := .proven
    prop := ``StrptimeTimeDatetime, thm := some ``strptimeTimeDatetime_proven
    notes := "Scope: the class and _strptime's datetime module are one implementation (Lib/datetime.py's setup); a _pydatetime class with the C _strptime refuses a parsed offset, datetime-strptime-class-impl." },
  { id := "datetime-datetime-fromiso-body", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.fromisoformat", "_find_isoformat_datetime_separator", "_parse_isoformat_date", "_parse_isoformat_time"]
    statement := "datetime.fromisoformat(s) for every string, by its parsers' results: short strings and refused date parts are 'Invalid isoformat string'; no time part is midnight of the date; a time-part ValueError is 'Invalid isoformat string', error_from_tz is raised, hour 24 with other fields is the hour-24 ValueError, and 24:00 on a valid date other than 9999-12-31 is midnight of the next day (ordinal + 1, a valid date)."
    source := "datetime.fromisoformat docs (24:00 is the next day's midnight); _pydatetime.py:1969-2014", status := .proven
    prop := ``DatetimeFromIsoBody, thm := some ``datetimeFromIsoBody_proven },
  { id := "datetime-time-new-str-state", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.__new__", "time.__setstate", "C time_new", "C time_from_pickle"]
    statement := "time(state, tzinfo) with a str state that passes the header test and has every character at most U+00FF builds, in both twins, exactly the time of the same six bytes (hour, fold, minute, second, microsecond, the tzinfo argument kept), the same as for the bytes state."
    source := "pickle contract (Python 2 pickles loaded with encoding='latin1'); C/Python twins", status := .proven
    prop := ``TimeNewStrState, thm := some ``timeNewStrState_proven },
  { id := "datetime-datetime-new-str-state", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.__new__", "datetime.__setstate", "C datetime_new", "C datetime_from_pickle"]
    statement := "datetime(state, tzinfo) with a str state that passes the header test and has every character at most U+00FF builds, in both twins, exactly the datetime of the same ten bytes (every field and fold, the tzinfo argument kept), the same as for the bytes state."
    source := "pickle contract (Python 2 pickles loaded with encoding='latin1'); C/Python twins", status := .proven
    prop := ``DatetimeNewStrState, thm := some ``datetimeNewStrState_proven },
  { id := "datetime-strptime-offset-range", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.strptime", "datetime.strptime", "C datetime_time_strptime_impl", "C datetime_datetime_strptime_impl"]
    statement := "When the parse has a UTC offset that _parse_tz refuses, time.strptime and datetime.strptime raise its exception; '+9900' with '%z' passes the %z regex and both raise the timezone range ValueError, whatever the locale."
    source := "_strptime.py:375, :706-711, :822-851; timezone docs (offset strictly inside a day)", status := .proven
    prop := ``StrptimeOffsetRange, thm := some ``strptimeOffsetRange_proven },
  { id := "datetime-datetime-fromiso-rollover", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.fromisoformat"]
    statement := "datetime.fromisoformat with a 24:00 time part is the constructor on the rolled-over date for every parsed date; when the guard 1 <= month <= 12 and day <= days_in_month is false the date stays as parsed and the constructor's ValueError is the result; 9999-12-31T24:00 is 'year must be in 1..9999, not 10000'; and 2021-02-29T24:00, 2021-02-28T24:00, 9999-12-31T24:00 give what CPython gives."
    source := "_pydatetime.py:1998-2014; datetime.fromisoformat docs", status := .proven
    prop := ``DatetimeFromIsoRollover, thm := some ``datetimeFromIsoRollover_proven },
  { id := "datetime-time-repr-fallible", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.__repr__", "_get_class_module", "C time_repr", "C append_keyword_tzinfo"]
    statement := "repr(time) with a tzinfo whose __repr__ may raise or return a non-str: both twins agree on every outcome for the base class and plain subclasses; a raising __repr__ propagates its exception, a non-str result is TypeError, a str result r is inserted as tzinfo=r before fold, in both; with str results it is the infallible text of TimeReprCls."
    source := "C/Python twins; PyObject_Repr contract", status := .proven
    prop := ``TimeReprFallible, thm := some ``timeReprFallible_proven },
  { id := "datetime-datetime-repr-fallible", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.__repr__", "_get_class_module", "C datetime_repr", "C append_keyword_tzinfo"]
    statement := "repr(datetime) with a tzinfo whose __repr__ may raise or return a non-str: both twins agree for plain classes when fold is 0, there is no tzinfo, or the tzinfo repr fails; a raising __repr__ propagates, a non-str is TypeError, a str r is inserted in each twin's order; with str results it is DatetimeReprCls's text."
    source := "C/Python twins; PyObject_Repr contract", status := .proven
    prop := ``DatetimeReprFallible, thm := some ``datetimeReprFallible_proven },
  { id := "datetime-datetime-repr-cls-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.__repr__", "_get_class_module", "C datetime_repr"]
    statement := "repr(datetime) is the same text in both twins for every class."
    source := "C/Python twins", status := .refuted
    prop := ``DatetimeReprClsTwins, thm := some ``datetimeReprClsTwins_refuted
    bug := some "datetime-repr-qualname-vs-tp-name"
    notes := "A nested subclass: Python prints __qualname__ (Outer.DT(2020, 1, 1, 0, 0)), C tp_name (DT(2020, 1, 1, 0, 0))." },
  { id := "datetime-local-timezone-full", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime._local_timezone", "datetime._mktime", "C local_timezone_from_local", "C local_timezone", "C local_timezone_from_timestamp", "C local_to_seconds"]
    statement := "datetime._local_timezone against C, for every valid datetime and localtime with fields a datetime accepts: a naive datetime gets the same zone or exception class in both twins; an aware one with offset o uses the timestamp floor((self - o - epoch) / 1 s); an aware one whose utcoffset() is None raises TypeError('cannot mix naive and timezone-aware time'); the zone of a timestamp is timezone(timedelta(seconds=tm_gmtoff), tm_zone) when tm_gmtoff is inside a day, in both twins, and a localtime error propagates."
    source := "C/Python twins; _pydatetime.py:2121-2135", status := .proven
    prop := ``LocalTimezoneFull, thm := some ``localTimezoneFull_proven },
  { id := "datetime-astimezone-local", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.astimezone", "datetime._local_timezone", "C datetime_datetime_astimezone_impl", "C local_timezone_from_local", "C local_timezone"]
    statement := "datetime.astimezone with the local zone, the new zones fresh: to a timezone from a naive datetime or one whose utcoffset() is None, both twins agree; to the local zone (tz=None) from an aware datetime with an offset whose self - offset is in range, both agree; a non-tzinfo argument is TypeError in both."
    source := "datetime.astimezone docs; C/Python twins", status := .proven
    prop := ``AstimezoneLocal, thm := some ``astimezoneLocal_proven },
  { id := "datetime-astimezone-local-naive-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.astimezone", "datetime._local_timezone", "C datetime_datetime_astimezone_impl", "C local_timezone"]
    statement := "astimezone() (tz=None) on a naive datetime agrees between the twins for every localtime with fields a datetime accepts."
    source := "C/Python twins", status := .refuted
    prop := ``AstimezoneLocalNaiveTwins, thm := some ``astimezoneLocalNaiveTwins_refuted
    bug := some "datetime-pydatetime-astimezone-local-target"
    notes := "A wall time in a gap: Python takes the target zone from the naive wall time (keeps 00:30, old offset), C from the UTC result (01:30, new offset)." },
  { id := "datetime-astimezone-local-none-offset-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.astimezone", "datetime._local_timezone", "C datetime_datetime_astimezone_impl"]
    statement := "astimezone() (tz=None) on an aware datetime whose tzinfo's utcoffset() is None agrees between the twins."
    source := "C/Python twins", status := .refuted
    prop := ``AstimezoneLocalNoneOffsetTwins, thm := some ``astimezoneLocalNoneOffsetTwins_refuted
    bug := some "datetime-pydatetime-astimezone-local-target"
    notes := "Python's self._local_timezone() subtracts _EPOCH and raises TypeError; C goes to naive: and converts." },
  { id := "datetime-timedelta-float-ctor-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__new__", "C delta_new", "C delta_new_impl", "C accum"]
    statement := "timedelta(...) agrees between the twins for every combination of int and float arguments."
    source := "C/Python twins; timedelta docs (fractional microseconds of all arguments combined, then rounded)", status := .refuted
    prop := ``TimedeltaFloatCtorTwins, thm := some ``timedeltaFloatCtorTwins_refuted
    bug := some "datetime-pydatetime-timedelta-float-precision"
    notes := "timedelta(hours=10000000.1): C 416666 days 57959 s 999999 us (exact), Python 416666 days 57960 s (hours*3600 rounded as a double first). gh-160806, fixed on main. Not on record as a refutation: the type checks run in a different order (timedelta(days='x', microseconds=inf) is TypeError in Python, OverflowError in C)." },
  { id := "datetime-c-normalize-helpers", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C divmod", "C normalize_pair", "C normalize_d_s_us"]
    statement := "The C divmod helper is Python's divmod for every positive divisor; normalize_pair keeps hi*factor + lo with 0 <= lo < factor and leaves an in-range pair alone; normalize_d_s_us keeps the total microseconds with seconds and microseconds in range and leaves in-range fields alone."
    source := "C/Python twins (divmod); invariant (the asserts at :384, :734, :760-761)", status := .proven
    prop := ``CNormalizeHelpers, thm := some ``cNormalizeHelpers_proven },
  { id := "datetime-new-delta-ex", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C new_delta_ex", "C look_up_delta", "C normalize_d_s_us"]
    statement := "new_delta_ex(d, s, us, normalize, type) is the normalized value of (d*86400 + s)*10**6 + us microseconds as an object of class type, the zero value of timedelta itself being the zero_delta singleton, and OverflowError out of the day range; with normalize false, for in-range s and us."
    source := "invariant (new_delta_ex comment, :1377-1382); timedelta(0) is timedelta(0) in C", status := .proven
    prop := ``NewDeltaEx, thm := some ``newDeltaEx_proven },
  { id := "datetime-timedelta-ctor-obj", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C delta_new_impl", "C microseconds_to_delta_ex", "C new_delta_ex", "C look_up_delta"]
    statement := "timedelta(...) with int arguments in C, for every class: the value of the value model (equal to Python's) as an object of that class; timedelta(0) is the zero_delta singleton, a subclass's zero a new object."
    source := "C/Python twins (value); identity as CPython 3.15.2 behaves", status := .proven
    prop := ``TimedeltaCtorObj, thm := some ``timedeltaCtorObj_proven },
  { id := "datetime-us-to-delta-obj", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C microseconds_to_delta_ex", "C checked_divmod"]
    statement := "microseconds_to_delta_ex on any object: an int converts exactly; for another object, an exception from divmod propagates, a non-tuple and a tuple of size other than 2 are checked_divmod's TypeErrors, an out-of-range int remainder is 'divmod() returned a value out of range', a remainder without __index__ is TypeError, and a pair of ints (q, r) with 0 <= r < 10**6 converts like q*10**6 + r."
    source := "invariant (no crash, errors as in the source); messages checked on CPython 3.15.2", status := .proven
    prop := ``UsToDeltaExObj, thm := some ``usToDeltaExObj_proven },
  { id := "datetime-timedelta-mul-int-subclass", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["timedelta.__mul__", "C delta_multiply", "C multiply_int_timedelta", "C microseconds_to_delta_ex", "C checked_divmod"]
    statement := "timedelta * n agrees between the twins for every int operand, an int subclass with its own __mul__ included."
    source := "C/Python twins", status := .refuted
    prop := ``TimedeltaMulIntSubclassTwins, thm := some ``timedeltaMulIntSubclassTwins_refuted
    bug := some "datetime-timedelta-mul-int-subclass"
    notes := "class I(int): __mul__ = lambda s, o: 2.5; timedelta(1) * I(2): Python timedelta(days=2) (int.__mul__ on the fields), C TypeError (PyNumber_Multiply(intobj, us) runs I.__mul__)." },
  { id := "datetime-timedelta-mul-dispatch", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["timedelta.__mul__", "C delta_multiply", "C multiply_int_timedelta", "C multiply_truedivide_timedelta_float"]
    statement := "For operands without overridden arithmetic and a timedelta on either side, x * y agrees between the twins: NotImplemented for two timedeltas or another object, the same outcome for timedelta*int, int*timedelta, timedelta*float and float*timedelta; C's result is of class timedelta."
    source := "C/Python twins", status := .proven
    prop := ``TimedeltaMulDispatch, thm := some ``timedeltaMulDispatch_proven },
  { id := "datetime-timedelta-truediv-dispatch", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["timedelta.__truediv__", "C delta_truedivide", "C truedivide_timedelta_int", "C multiply_truedivide_timedelta_float"]
    statement := "For operands without overridden arithmetic and a timedelta on either side, x / y agrees between the twins: NotImplemented unless a timedelta is divided by a timedelta, int or float; the same outcome for each of those; C's timedelta / timedelta is long_true_divide of the microsecond counts and its timedelta results are of class timedelta."
    source := "C/Python twins", status := .proven
    prop := ``TimedeltaTruedivDispatch, thm := some ``timedeltaTruedivDispatch_proven },
  { id := "datetime-timedelta-reduce-cls", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["timedelta.__reduce__", "C delta_reduce", "C delta_getstate"]
    statement := "t.__reduce__() is (type(t), (days, seconds, microseconds)) in both twins for every class, and calling that class on those arguments gives back an object of the same class and value (the zero_delta singleton for a zero timedelta in C)."
    source := "pickle contract (__reduce__); C/Python twins", status := .proven
    prop := ``TimedeltaReduceCls, thm := some ``timedeltaReduceCls_proven },
  { id := "datetime-ymd-to-ord-twins", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C ymd_to_ord", "C days_before_year", "C days_before_month", "C is_leap", "_ymd2ord", "_days_before_year", "_days_before_month"]
    statement := "For every year in 1..9999 and month in 1..12, C days_before_year, days_before_month and ymd_to_ord equal Python's _days_before_year, _days_before_month and _ymd2ord; at year 0 (unvalidated pickle state) days_before_year is -365 in C and -366 in Python."
    source := "C/Python twins", status := .proven
    prop := ``YmdToOrdTwins, thm := some ``ymdToOrdTwins_proven },
  { id := "datetime-date-subclass-ctor", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C new_date_subclass_ex", "C new_date_ex", "C new_datetime_ex", "date.fromordinal"]
    statement := "new_date_subclass_ex(y, m, d, cls) is Python's cls(y, m, d) for every class and all C-int fields: date and datetime check the fields as their constructors do (ValueError, the same text; midnight for datetime), another class is called with (y, m, d) and no keyword."
    source := "C/Python twins", status := .proven
    prop := ``DateSubclassCtor, thm := some ``dateSubclassCtor_proven },
  { id := "datetime-new-datetime-ex-twins", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C new_datetime_ex", "C new_time_ex"]
    statement := "new_datetime_ex (DateTime_FromDateAndTime) is datetime(y, m, d, hh, mm, ss, us, tzinfo) and new_time_ex (Time_FromTime) is time(hh, mm, ss, us, tzinfo) for all C-int fields and a None or tzinfo tzinfo, with fold 0."
    source := "C/Python twins (C API constructors against the Python constructors)", status := .proven
    prop := ``NewDatetimeExTwins, thm := some ``newDatetimeExTwins_proven },
  { id := "datetime-subclass-fold-twins", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C call_subclass_fold", "C new_datetime_subclass_fold_ex", "C new_time_subclass_fold_ex", "datetime.replace", "time.replace"]
    statement := "For every class whose constructor treats an omitted fold like fold=0, new_datetime_subclass_fold_ex and new_time_subclass_fold_ex agree with replace's type(self)(..., fold=fold): the base classes run the same checks, a subclass gets the fields positionally in order and fold as a keyword, which C passes only when nonzero."
    source := "C/Python twins", status := .proven
    prop := ``SubclassFoldTwins, thm := some ``subclassFoldTwins_proven },
  { id := "datetime-replace-subclass-fold-any", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C call_subclass_fold", "C new_datetime_subclass_fold_ex", "datetime.replace"]
    statement := "datetime.replace on a subclass agrees between the twins for every subclass constructor."
    source := "C/Python twins", status := .refuted
    prop := ``DtReplaceSubclassAnyTwins, thm := some ``dtReplaceSubclassAnyTwins_refuted
    bug := some "datetime-pydatetime-replace-fold-keyword"
    notes := "A subclass whose __new__ takes no fold keyword: Python's replace always passes fold=0 and raises TypeError; C's call_subclass_fold leaves a zero fold out and succeeds." },
  { id := "datetime-parse-digits-c", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C parse_digits", "C is_digit"]
    statement := "parse_digits(p, var, n) fails exactly when one of the n bytes from p is not an ASCII digit (is_digit is the 0x30..0x39 test), and otherwise returns p + n and the value the C loop accumulates."
    source := "invariant (no read past the NUL terminator; the value of the digits)", status := .proven
    prop := ``ParseDigitsSpec, thm := some ``parseDigitsSpec_proven },
  { id := "datetime-parse-isoformat-date-c", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C parse_isoformat_date", "C parse_digits", "C is_digit"]
    statement := "parse_isoformat_date returns -1 unless the first four bytes are digits; YYYY-Www-D, YYYYWwwD, YYYY-Www and YYYYWww give iso_to_ymd's date or -3 + its code; a wrong separator is -2 in both branches, a missing day digit -4, a missing week digit -3; YYYY-MM-DD and YYYYMMDD give their fields."
    source := "code comment (return codes, :946-955); invariant", status := .proven
    prop := ``ParseIsoDateCSpec, thm := some ``parseIsoDateCSpec_proven },
  { id := "datetime-str-via-isoformat", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C date_str", "C time_str", "date.__str__", "time.__str__"]
    statement := "str() of a date or time whose class keeps isoformat is the same text in both twins (YYYY-MM-DD for a date); in C, a class that overrides isoformat gets its override's result or exception."
    source := "C/Python twins; date.__str__ docs (\"For a date d, str(d) is equivalent to d.isoformat()\")", status := .proven
    prop := ``StrViaIsoformat, thm := some ``strViaIsoformat_proven },
  { id := "datetime-str-isoformat-override-twins", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C date_str", "date.__str__"]
    statement := "str() of a date agrees between the twins for every class, a subclass overriding isoformat included."
    source := "C/Python twins", status := .refuted
    prop := ``StrIsoformatOverrideTwins, thm := some ``strIsoformatOverrideTwins_refuted
    bug := some "datetime-pydatetime-str-isoformat-alias"
    notes := "class D(date): def isoformat(self): return 'X'; str(D(2000, 1, 1)) is 'X' in C, '2000-01-01' in _pydatetime (__str__ = isoformat binds date.isoformat). time is the same; datetime.__str__ calls self.isoformat(sep=' ') in both." },
  { id := "datetime-append-fold-twins", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C append_keyword_fold"]
    statement := "C append_keyword_fold (', fold=%d)') and Python's s[:-1] + ', fold=1)' agree for folds 0 and 1: no change for 0, ', fold=1)' for 1."
    source := "C/Python twins", status := .proven
    prop := ``AppendFoldTwins, thm := some ``appendFoldTwins_proven },
  { id := "datetime-timestamp-conversion", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C date_fromtimestamp", "C datetime_date_fromtimestamp_impl", "date.fromtimestamp"]
    statement := "date.fromtimestamp(t) in both twins: an int outside the 64-bit time_t range is OverflowError (an int inside it goes to localtime as is), a NaN ValueError, an infinity OverflowError, a str TypeError."
    source := "_PyTime_ObjectToTime_t (Python/pytime.c:484-520); messages checked on CPython 3.15.2", status := .proven
    prop := ``TimestampConversion, thm := some ``timestampConversion_proven },
  { id := "datetime-timestamp-floor", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C date_fromtimestamp"]
    statement := "For a finite float t, date.fromtimestamp(t) uses floor(t) when it lies in [-2**63, 2**63) and raises OverflowError otherwise, in both twins."
    source := "date.fromtimestamp docs; _PyTime_ObjectToTime_t with _PyTime_ROUND_FLOOR", status := .open
    prop := ``TimestampConversion
    notes := "Needs F64.floor's value (ofIntS of floorInt) and the comparison of ofInt(+-2**63) with it through toRat; the model (objectToTimeT) has the branch." },
  { id := "datetime-date-strptime-cls", pyFile := "Modules/_datetimemodule.c"
    pyFns := ["C datetime_date_strptime_impl", "date.strptime", "_strptime_datetime_date"]
    statement := "date.strptime in both twins passes its class to _strptime_datetime_date: for date the checked parsed date, a subclass is called with the parsed year, month and day, and a parse error propagates."
    source := "C/Python twins", status := .proven
    prop := ``DateStrptimeCls, thm := some ``dateStrptimeCls_proven },
  { id := "datetime-strptime-class-impl", pyFile := "Lib/_pydatetime.py"
    pyFns := ["time.strptime", "datetime.strptime", "_strptime_datetime_time", "_strptime_datetime_datetime", "_check_tzinfo_arg"]
    statement := "time.strptime and datetime.strptime give the StrptimeTimeDatetime results when the class and _strptime's datetime module are one implementation; when they differ (a _pydatetime class with the C _strptime), a parsed %z offset is TypeError from the class's tzinfo check and a format without %z gives the same value."
    source := "Lib/datetime.py:7-10 and _strptime.py:22-24 (configuration); _check_tzinfo_arg", status := .proven
    prop := ``StrptimeClassImpl, thm := some ``strptimeClassImpl_proven },
  { id := "datetime-timedelta-type-loop", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__new__"]
    statement := "timedelta(...) in Python raises TypeError naming the first component, in signature order, that is neither an int nor a float, before any arithmetic."
    source := "timedelta docs (arguments may be integers or floats); Py:667-679", status := .proven
    prop := ``TimedeltaTypeLoop, thm := some ``timedeltaTypeLoop_proven },
  { id := "datetime-timedelta-num-py-int", pyFile := "Lib/_pydatetime.py"
    pyFns := ["timedelta.__new__"]
    statement := "With int arguments the float-capable model of timedelta.__new__ is the int-only model (so TimedeltaCtorTwins and TimedeltaCtorExact apply to it)."
    source := "invariant (the float branches are not taken)", status := .open
    prop := ``TimedeltaNumPyInt
    notes := "Needs binary64 lemmas: float(m) + 0.0 == float(m) for |m| < 10**6 and round() of an integral double." },
  { id := "datetime-astimezone-local-aware-edge-twins", pyFile := "Lib/_pydatetime.py"
    pyFns := ["datetime.astimezone", "datetime._local_timezone", "C datetime_datetime_astimezone_impl"]
    statement := "astimezone() (tz=None) on an aware datetime with an offset agrees between the twins, where self - offset leaves the datetime range included."
    source := "C/Python twins", status := .refuted
    prop := ``AstimezoneLocalAwareEdgeTwins, thm := some ``astimezoneLocalAwareEdgeTwins_refuted
    bug := some "datetime-pydatetime-astimezone-local-target"
    notes := "datetime(1, 1, 1, tzinfo=timezone(timedelta(hours=1))).astimezone() with TZ='XXX-24:30': Python builds the local timezone first and raises ValueError (offset 24:30), C subtracts first and raises OverflowError." }
]

end PyLean.Datetime
