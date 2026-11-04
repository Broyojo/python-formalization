import PyLean.Datetime.PickleProps
import PyLean.Datetime.StrptimeImpl
import PyLean.Datetime.Twins2Props
import PyLean.Datetime.SubObj

/-!
The class argument of the C methods that build their result through the receiver's type or a
classmethod's `type` (Modules/_datetimemodule.c, CPython 3.15.2): `date.replace`,
`time.replace`, `datetime.replace` (`Py_TYPE(self)`), `datetime.combine`, `time.strptime`,
`datetime.strptime`, `time.fromisoformat`, `datetime.fromisoformat` (`type`), and the
`(Py_TYPE(self), state)` of `__reduce__`/`__reduce_ex__` of `date`, `time`, `datetime` and
`tzinfo`.

Classes are modelled by identity: `DateClsC`/`ClsC α` from SubclassCtor.lean (the base class,
whose fast path the C code takes, or a subclass given by what calling it returns), and a plain
type identity `ty : Nat` where only the type object itself is returned (`__reduce__`).
-/

namespace PyLean.Datetime
open PyLean

/-! ### `replace` -/

/-- `datetime_date_replace` (clinic/_datetimemodule.c.h:587-658: an omitted argument keeps the
field, a given one goes through `PyLong_AsInt`) and `datetime_date_replace_impl`, :3956-3961:
`new_date_subclass_ex(year, month, day, Py_TYPE(self))`. -/
def dateReplaceClsC (cls : DateClsC) (y m d : Int) (ny nm nd : Option Arg) : Py DT := do
  let year ← replConv y ny
  let month ← replConv m nm
  let day ← replConv d nd
  newDateSubclassExC year month day cls

/-- `date.replace`, Py:1184-1192: `None` or omitted keeps a field, then `type(self)(year,
month, day)` with the objects as given. -/
def dateReplaceClsPy (cls : DateClsC) (y m d : Int) (ny nm nd : Option Arg) : Py DT :=
  let a := replKeep y ny
  let b := replKeep m nm
  let c := replKeep d nd
  match cls with
  | .date => (fun r => (⟨r.1, r.2.1, r.2.2, 0, 0, 0, 0, 0, none⟩ : DT)) <$> dateNewPy a b c
  | .datetime => datetimeNewPy a b c (.int 0) (.int 0) (.int 0) (.int 0) .none_ (.int 0)
  | .sub call => call [a, b, c] none

/-- `datetime_time_replace_impl`, :5171-5178, after the clinic `int` conversions (modelled as in
`tmReplaceC`: an out-of-range field is `OverflowError`): `new_time_subclass_fold_ex(...,
Py_TYPE(self))`, the given or kept `tzinfo` passed as is. -/
def tmReplaceClsC (cls : ClsC TM) (t : TM) (h mi s us fold : Option Int) (tz : Option (Option Tz)) : Py TM :=
  if ¬(fitsCInt (h.getD t.h) ∧ fitsCInt (mi.getD t.mi) ∧ fitsCInt (s.getD t.s) ∧
      fitsCInt (us.getD t.us) ∧ fitsCInt (fold.getD t.fold)) then
    .error (.overflowError "Python int too large to convert to C int")
  else newTimeSubclassFoldExC (h.getD t.h) (mi.getD t.mi) (s.getD t.s) (us.getD t.us)
    (tzArgOf (tz.getD t.tz)) (fold.getD t.fold) cls

/-- `datetime_datetime_replace_impl`, :6753-6762, after the clinic conversions:
`new_datetime_subclass_fold_ex(..., Py_TYPE(self))`. -/
def dtReplaceClsC (cls : ClsC DT) (dt : DT) (y m d h mi s us fold : Option Int) (tz : Option (Option Tz)) : Py DT :=
  if ¬(fitsCInt (y.getD dt.y) ∧ fitsCInt (m.getD dt.m) ∧ fitsCInt (d.getD dt.d) ∧
      fitsCInt (h.getD dt.h) ∧ fitsCInt (mi.getD dt.mi) ∧ fitsCInt (s.getD dt.s) ∧
      fitsCInt (us.getD dt.us) ∧ fitsCInt (fold.getD dt.fold)) then
    .error (.overflowError "Python int too large to convert to C int")
  else newDatetimeSubclassFoldExC (y.getD dt.y) (m.getD dt.m) (d.getD dt.d) (h.getD dt.h) (mi.getD dt.mi)
    (s.getD dt.s) (us.getD dt.us) (tzArgOf (tz.getD dt.tz)) (fold.getD dt.fold) cls

/-! ### `combine` -/

/-- `datetime_datetime_combine`, clinic/_datetimemodule.c.h:1637-1697 (the `subclass_of`
checks of `date` then `time`), and `datetime_datetime_combine_impl`, :5891-5911: an omitted
`tzinfo` is the time's (:5895-5900), then `new_datetime_subclass_fold_ex(..., TIME_GET_FOLD(time),
type)`. -/
def dtCombineClsC (cls : ClsC DT) (d : DateObj) (t : TimeObj) (tz : TzParam) : Py DT :=
  match d with
  | .other => .error (.typeError "~combine() argument 'date' must be datetime.date")
  | .date y m dd =>
    match t with
    | .other => .error (.typeError "~combine() argument 'time' must be datetime.time")
    | .time t => newDatetimeSubclassFoldExC y m dd t.h t.mi t.s t.us (tzParamC t.tz tz) t.fold cls

/-! ### `strptime` -/

/-- `_strptime._strptime_datetime_time(cls, string, format)`, _strptime.py:829-839, from the
regex match on: `_strptime`, then `_parse_tz` when there is an offset, then `cls(*args)` or
`cls(*args, tz)` with `args = (hour, minute, second, fraction)`. The base class's call is
`time(...)` on those ints (`newTM`, as `strptimeDatetimeTime`). -/
def strptimeTimeCls (cls : ClsC TM) (lt : LocaleTimeV) (found : StrpFound) : Py TM := do
  let r ← strptimeCore lt found
  let tz ← match r.gmtoff with
    | none => pure none
    | some g => some <$> parseTz r.tzname g r.gmtoffFraction
  let args : List Arg := [.int r.hour, .int r.minute, .int r.second, .int r.fraction] ++
    (match tz with | none => [] | some z => [.tz z])
  match cls with
  | .base => newTM ⟨r.hour, r.minute, r.second, r.fraction, 0, tz⟩
  | .sub call => call args none

/-- `_strptime._strptime_datetime_datetime(cls, string, format)`, _strptime.py:841-851: the
same with `args = (year, month, day, hour, minute, second, fraction)`. -/
def strptimeDatetimeCls (cls : ClsC DT) (lt : LocaleTimeV) (found : StrpFound) : Py DT := do
  let r ← strptimeCore lt found
  let tz ← match r.gmtoff with
    | none => pure none
    | some g => some <$> parseTz r.tzname g r.gmtoffFraction
  let args : List Arg := [.int r.year, .int r.month, .int r.day, .int r.hour, .int r.minute, .int r.second,
    .int r.fraction] ++ (match tz with | none => [] | some z => [.tz z])
  match cls with
  | .base => newDT ⟨r.year, r.month, r.day, r.hour, r.minute, r.second, r.fraction, 0, tz⟩
  | .sub call => call args none

/-- `datetime_time_strptime_impl(type, string, format)`, :4793-4810: import `_strptime` and call
`_strptime_datetime_time(type, string, format)` (:4804-4806). -/
def timeStrptimeImplC (cls : ClsC TM) (lt : LocaleTimeV) (found : StrpFound) : Py TM :=
  strptimeTimeCls cls lt found

/-- `time.strptime(cls, ...)`, Py:1477-1484: the same call. -/
def timeStrptimePy (cls : ClsC TM) (lt : LocaleTimeV) (found : StrpFound) : Py TM :=
  strptimeTimeCls cls lt found

/-- `datetime_datetime_strptime_impl(type, string, format)`, :5862-5878. -/
def datetimeStrptimeImplC (cls : ClsC DT) (lt : LocaleTimeV) (found : StrpFound) : Py DT :=
  strptimeDatetimeCls cls lt found

/-- `datetime.strptime(cls, ...)`, Py:2225-2232. -/
def datetimeStrptimePy (cls : ClsC DT) (lt : LocaleTimeV) (found : StrpFound) : Py DT :=
  strptimeDatetimeCls cls lt found

/-! ### `fromisoformat` -/

/-- A `timedelta` of `us` microseconds, normalized. -/
def isoDeltaOfUs (us : Int) : Delta := ⟨us / 86400000000, us / 1000000 % 86400, us % 1000000⟩

/-- The `tzinfo` object `tzinfo_from_isoformat_results` (:1672-1693) gives, as a call argument:
`None`, `timezone.utc` for a zero offset, or a new `timezone` of the offset. -/
def isoTzArg : Option Int → Arg
  | none => .none_
  | some 0 => .tz tzUTC
  | some us => .tz ⟨1, .timezone (isoDeltaOfUs us) none⟩

/-- The parse of `datetime_time_fromisoformat_impl`, :5191-5231 (`timeFromIsoC` up to
`tzinfo_from_isoformat_results`), with what follows it as a continuation `k`. -/
def timeFromIsoK {α : Type} (s : List Char) (k : Int × Int × Int × Int × Option Int → Py α) : Py α := do
  let b := utf8 s
  let (p, len) := if byteAt b 0 = 84 then (1, b.length - 1) else (0, b.length)
  let r := parseIsoTimeC b p len
  if r.rv < 0 then throw (timeResError r)
  let hour ← if r.h = 24 then
      if r.mi = 0 ∧ r.s = 0 ∧ r.us = 0 then pure 0
      else throw (.valueError "minute, second, and microsecond must be 0 when hour is 24")
    else pure r.h
  let tz ← tzinfoFromIsoResults r.rv r.tzoffset r.tzus
  k (hour, r.mi, r.s, r.us, tz)

/-- `new_time(...)` for `time` itself (:5238-5239), whose `check_time_args` is the `checkTime`. -/
def tmIsoBaseTail : Int × Int × Int × Int × Option Int → Py TimeV
  | (hour, mi, se, us, tz) => do
    let _ ← checkTime hour mi se us
    return ⟨hour, mi, se, us, tz⟩

/-- The arguments of `PyObject_CallFunction(type, "iiiiO", hour, minute, second, microsecond,
tzinfo)` (:5240-5242). -/
def tmIsoArgs : Int × Int × Int × Int × Option Int → List Arg
  | (hour, mi, se, us, tz) => [.int hour, .int mi, .int se, .int us, isoTzArg tz]

/-- `datetime_time_fromisoformat_impl`, :5191-5258, for the class `type`: the parse, then for
`time` itself `new_time(...)`, otherwise the class called with the five values (:5237-5243),
with no check of its own. -/
def timeFromIsoClsC (cls : ClsC TimeV) (s : List Char) : Py TimeV :=
  timeFromIsoK s fun p =>
    match cls with
    | .base => tmIsoBaseTail p
    | .sub call => call (tmIsoArgs p) none

/-- The date-and-time parse of `datetime_datetime_fromisoformat_impl`, :6079-6170, on a
sanitized, encodable string, with what follows it as a continuation `k`: `datetimeFromIsoC` is
this with `k` the base class's checks (`datetimeFromIsoK_base`). -/
def datetimeFromIsoK {α : Type} (s : List Char) (k : Int × Int × Int × Int × Int × Int × Int × Option Int → Py α) :
    Py α := do
  if s.length < 7 then throw (.valueError "~Invalid isoformat string")
  let b := utf8 s
  let len : Int := b.length
  let sepLoc := findSepC b
  let dlen : Nat := if sepLoc < 0 then 2 ^ 64 - 1 else sepLoc.toNat
  let date := parseIsoDateC b dlen
  let (ymd, r) ← match date with
    | .error _ => throw (.valueError "~Invalid isoformat string")
    | .ok ymd =>
      if len > sepLoc then
        let p := sepLoc.toNat + utf8SkipC (byteAt b sepLoc.toNat)
        pure (ymd, parseIsoTimeC b p (len - p).toNat)
      else pure (ymd, (⟨0, 0, 0, 0, 0, 0, 0, none⟩ : TimeRes))
  if r.rv < 0 then throw (timeResError r)
  let tz ← tzinfoFromIsoResults r.rv r.tzoffset r.tzus
  let (y, m, d) := ymd
  let (y, m, d, hour) ← if r.h = 24 ∧ 1 ≤ m ∧ m ≤ 12 then
      let dim := daysInMonth y m
      if d ≤ dim then
        if r.mi = 0 ∧ r.s = 0 ∧ r.us = 0 then
          let d := d + 1
          if d > dim then
            let m := m + 1
            if m > 12 then pure (y + 1, 1, 1, 0) else pure (y, m, 1, 0)
          else pure (y, m, d, 0)
        else throw (.valueError "minute, second, and microsecond must be 0 when hour is 24")
      else pure (y, m, d, r.h)
    else pure (y, m, d, r.h)
  k (y, m, d, hour, r.mi, r.s, r.us, tz)

/-- The base class's tail: `new_datetime_subclass_ex(..., DATETIME_TYPE)`, the fast path
`new_datetime`, whose `check_date_args` and `check_time_args` are these. -/
def dtIsoBaseTail : Int × Int × Int × Int × Int × Int × Int × Option Int → Py DateTimeV
  | (y, m, d, hour, mi, s, us, tz) => do
    let _ ← checkDate y m d
    let _ ← checkTime hour mi s us
    return ⟨y, m, d, ⟨hour, mi, s, us, tz⟩⟩

/-- The arguments of the subclass call, `"iiiiiiiO"` (:1300-1301). -/
def dtIsoArgs : Int × Int × Int × Int × Int × Int × Int × Option Int → List Arg
  | (y, m, d, hour, mi, se, us, tz) => [.int y, .int m, .int d, .int hour, .int mi, .int se, .int us, isoTzArg tz]

/-- `datetime_datetime_fromisoformat_impl`, :6079-6194, for the class `type`, on the code points
of the argument: `_sanitize_isoformat_str` (:6086-6089, `NULL` is `invalid_string_error`); then
`PyUnicode_AsUTF8AndSize` (:6092-6101), which fails with `UnicodeEncodeError` exactly when a
surrogate is left, turned into `invalid_string_error`; then the parse, and
`new_datetime_subclass_ex(..., type)` (:6173-6174): the fast path for `datetime`, otherwise
`cls(y, m, d, hh, mm, ss, us, tzinfo)` through `call_subclass_fold` with `fold = 0`. -/
def datetimeFromIsoClsC (cls : ClsC DateTimeV) (cps : List Nat) : Py DateTimeV :=
  match sanitizeIsoformatC cps with
  | none => .error (.valueError "~Invalid isoformat string")
  | some clean =>
    if clean.any isSurrogate then .error (.valueError "~Invalid isoformat string")
    else datetimeFromIsoK (clean.map Char.ofNat) fun p =>
      match cls with
      | .base => dtIsoBaseTail p
      | .sub call => callSubclassFoldC call 0 (dtIsoArgs p)

/-! ### `__reduce__`, `__reduce_ex__` -/

/-- `date_reduce`, :4013-4018: `Py_BuildValue("(ON)", Py_TYPE(self), date_getstate(self))`,
the state `(bytes,)`. -/
def dateReduceClsC (ty : Nat) (y m d : Int) : Nat × List Nat := (ty, dateGetstate y m d)

/-- `date.__reduce__`, Py:1308-1309: `(self.__class__, self._getstate())`; `_getstate`,
Py:1297-1300, is the four bytes. The class is the receiver's type (a `__class__` property
overriding it is out of scope). -/
def dateReduceClsPy (ty : Nat) (y m d : Int) : Nat × List Nat := (ty, dateData y m d)

/-- `datetime.time.__reduce_ex__` (clinic/_datetimemodule.c.h:1234-1247: `PyLong_AsInt`, the
`int` converter) and `datetime_time___reduce_ex___impl`, :5297-5300:
`(Py_TYPE(self), time_getstate(self, proto))`. -/
def tmReduceExClsC (ty : Nat) (t : TM) (proto : Arg) : Py (Nat × StateTuple) := do
  let p ← parseI proto
  return (ty, tmReduceExC t p)

/-- `datetime_time___reduce___impl`, :5308-5311: `(Py_TYPE(self), time_getstate(self, 2))`. -/
def tmReduceClsC (ty : Nat) (t : TM) : Nat × StateTuple := (ty, tmReduceC t)

/-- `time.__reduce_ex__(protocol)`, Py:1779-1780: `(self.__class__, self._getstate(protocol))`
for an int protocol (`_getstate` compares `protocol > 3` only when `fold` is set). -/
def tmReduceExClsPy (ty : Nat) (t : TM) (p : Int) : Nat × StateTuple := (ty, tmReduceExPy t p)

/-- `datetime.datetime.__reduce_ex__` (clinic/_datetimemodule.c.h:2063-2076) and
`datetime_datetime___reduce_ex___impl`, :7229-7233. -/
def dtReduceExClsC (ty : Nat) (dt : DT) (proto : Arg) : Py (Nat × StateTuple) := do
  let p ← parseI proto
  return (ty, dtReduceExC dt p)

/-- `datetime_datetime___reduce___impl`, :7241-7245. -/
def dtReduceClsC (ty : Nat) (dt : DT) : Nat × StateTuple := (ty, dtReduceC dt)

/-- `datetime.__reduce_ex__(protocol)`, Py:2432-2433. -/
def dtReduceExClsPy (ty : Nat) (dt : DT) (p : Int) : Nat × StateTuple := (ty, dtReduceExPy dt p)

/-- `tzinfo_reduce`, :4257-4283: the arguments and state of `tzinfoReduceC`, then
`Py_BuildValue("(ONN)", Py_TYPE(self), args, state)` (:4282). -/
def tzinfoReduceClsC {α σ : Type} (ty : Nat) (attr : Py (Option (InitArgsObj α))) (state : Py σ) :
    Py (Nat × ReduceArgs α × σ) :=
  (fun r => (ty, r.1, r.2)) <$> tzinfoReduceC attr state

/-- `tzinfo.__reduce__`, Py:1370-1376: `(self.__class__, args, self.__getstate__())`. -/
def tzinfoReduceClsPy {α σ : Type} (ty : Nat) (attr : Py (Option (InitArgsObj α))) (state : Py σ) :
    Py (Nat × ReduceArgs α × σ) :=
  (fun r => (ty, r.1, r.2)) <$> tzinfoReducePy attr state

end PyLean.Datetime
