import PyLean.Datetime.Twins2

/-!
The argument type checks (`isinstance` in `Lib/_pydatetime.py`, the clinic converters or
explicit checks in `Modules/_datetimemodule.c`) that the earlier models took for granted by
typing the argument: `timezone` methods and constructor, `datetime.combine`,
`datetime.astimezone`, `time.__format__`, `time.fromisoformat` and `datetime.fromisoformat`,
and `timezone.__getinitargs__` and `__hash__`. 3.15.2.
-/

namespace PyLean.Datetime

open PyLean

/-! ### `timezone` methods -/

/-- The argument of `timezone.utcoffset`, `tzname`, `dst` and `fromutc`: a `datetime` (or an
instance of a subclass), `None`, or any other object (a `date`, an int, ...). -/
inductive TzMethArg where
  | dt (d : DT)
  | none_
  | other
  deriving DecidableEq, Inhabited

/-- `isinstance(dt, datetime) or dt is None`. -/
def TzMethArg.ok : TzMethArg → Bool
  | .other => false
  | _ => true

/-- `timezone.utcoffset(dt)`, Py:2524-2528. -/
def timezoneUtcoffsetArgPy (offset : Delta) : TzMethArg → Py Delta
  | .other => .error (.typeError "utcoffset() argument must be a datetime instance or None")
  | _ => .ok offset

/-- `timezone_utcoffset`, :4488-4495: `_timezone_check_argument` (:4403-4410), then the offset. -/
def timezoneUtcoffsetArgC (offset : Delta) (a : TzMethArg) : Py Delta := do
  timezoneCheckArg a.ok "utcoffset"
  return offset

/-- `timezone.tzname(dt)`, Py:2530-2536: the name, or `_name_from_offset` when it is `None`. -/
def timezoneTznameArgPy (offset : Delta) (name : Option String) : TzMethArg → Py String
  | .other => .error (.typeError "tzname() argument must be a datetime instance or None")
  | _ => .ok (match name with
    | none => nameFromOffset offset
    | some n => n)

/-- `timezone_tzname`, :4479-4485: the check, then `timezone_str`. -/
def timezoneTznameArgC (oid : Nat) (offset : Delta) (name : Option String) (a : TzMethArg) : Py String := do
  timezoneCheckArg a.ok "tzname"
  return timezoneStrC oid offset name

/-- `timezone.dst(dt)`, Py:2538-2542. -/
def timezoneDstArgPy : TzMethArg → Py (Option Delta)
  | .other => .error (.typeError "dst() argument must be a datetime instance or None")
  | _ => .ok none

/-- `timezone_dst`, :4498-4504. -/
def timezoneDstArgC (a : TzMethArg) : Py (Option Delta) := do
  timezoneCheckArg a.ok "dst"
  return none

/-- `timezone.fromutc(dt)`, Py:2544-2551: `isinstance(dt, datetime)` (so `None` is refused,
whatever the message says), then `timezoneFromutcPy`. -/
def timezoneFromutcArgPy (tz : Tz) (offset : Delta) : TzMethArg → Py DT
  | .dt d => timezoneFromutcPy tz offset d
  | _ => .error (.typeError "fromutc() argument must be a datetime instance or None")

/-- `timezone_fromutc`, :4507-4523: `PyDateTime_Check`, then `timezoneFromutcC`. -/
def timezoneFromutcArgC (tz : Tz) (offset : Delta) : TzMethArg → Py DT
  | .dt d => timezoneFromutcC tz offset d
  | _ => .error (.typeError "fromutc: argument must be a datetime")

/-! ### `timezone(offset, name)` -/

/-- `timezone.__new__(cls, offset, name)`, Py:2462-2475: `offset` is a `timedelta` (`some`) or
another object (`none`), tested first (:2463-2464); then `timezoneNewPy`. -/
def timezoneNewArgPy (oid : Nat) (offset : Option Delta) (name : TzName) : Py Tz :=
  match offset with
  | none => .error (.typeError "offset must be a timedelta")
  | some o => timezoneNewPy oid o name

/-- `timezone_new`, clinic/_datetimemodule.c.h:670-730: the `offset` type check first (:712-715),
then `name` (:720-723) and `timezone_new_impl` (`timezoneNewC`). -/
def timezoneNewArgC (oid : Nat) (offset : Option Delta) (name : TzName) : Py Tz :=
  match offset with
  | none => .error (.typeError "~timezone() argument 'offset' must be datetime.timedelta")
  | some o => timezoneNewC oid o name

/-- The `offset` argument of `timezone(offset, name)` as an object. `other` is an ordinary object
that neither twin takes for a `timedelta`; `delta o` an exact `timedelta`; `sub o truth geMin
leMax` an instance of a `timedelta` subclass with the stored value `o`, where `truth` is the
outcome of its truth test (`not offset`, Py:2466), `geMin` the outcome of `cls._minoffset <=
offset` and `leMax` that of `offset <= cls._maxoffset` (Py:2471). Each is the truth value the `if`
ends up with, after any `NotImplemented` fallback and the conversion to `bool`, or the exception
raised on the way; it is not the raw return value of the method. A subclass can override
`__bool__`, `__ge__` (which Python tries first for `_minoffset <= offset`, the right operand being
of a subclass, Objects/object.c:1055) and `__le__`, or the helpers `_cmp` and `_getstate` the
inherited comparisons use, so the three are free.

Out of scope: an object whose `__class__` misreports its type or raises (`isinstance` at Py:2463
consults it, the clinic check does not); a subclass whose `__repr__` raises (both twins format
the offset into the range `ValueError`, Py:2474 and `_datetimemodule.c:1472-1474`); side effects
of these methods, such as changing the object's fields between the calls; and the identity of
the offset the new `timezone` holds, since `TzKind.timezone` keeps its value only. -/
inductive TzOffsetArg where
  | other
  | delta (o : Delta)
  | sub (o : Delta) (truth geMin leMax : Py Bool)

/-- The stored fields are those of a `timedelta`. -/
def TzOffsetArg.Valid : TzOffsetArg → Prop
  | .other => True
  | .delta o => o.Valid
  | .sub o _ _ _ => o.Valid

/-- `if not cls._minoffset <= offset <= cls._maxoffset: raise ValueError(...)` and
`cls._create(offset, name)`, Py:2471-2475, on a subclass instance: the chained comparison asks
the object, left comparison first, and stops at the first false or raising one. -/
def timezoneRangeSubPy (oid : Nat) (o : Delta) (geMin leMax : Py Bool) (name : Option String) :
    Py Tz :=
  let bad : Py Tz := .error (.valueError
    "~offset must be a timedelta strictly between -timedelta(hours=24) and timedelta(hours=24)")
  match geMin with
  | .error e => .error e
  | .ok false => bad
  | .ok true =>
    match leMax with
    | .error e => .error e
    | .ok false => bad
    | .ok true => .ok ⟨oid, .timezone o name⟩

/-- `timezone.__new__(cls, offset, name)`, Py:2462-2475, on any `offset` object. An exact
`timedelta` is `timezoneNewPy`. A subclass instance is asked for its truth (:2466) and for the
two comparisons (:2471), in that order. -/
def timezoneNewObjPy (oid : Nat) (offset : TzOffsetArg) (name : TzName) : Py Tz :=
  match offset with
  | .other => .error (.typeError "offset must be a timedelta")
  | .delta o => timezoneNewPy oid o name
  | .sub o truth geMin leMax =>
    match name with
    | .omitted =>
      match truth with
      | .error e => .error e
      | .ok false => .ok tzUTC
      | .ok true => timezoneRangeSubPy oid o geMin leMax none
    | .other => .error (.typeError "name must be a string")
    | .str s => timezoneRangeSubPy oid o geMin leMax (some s)

/-- `timezone_new`, clinic/_datetimemodule.c.h:670-730, and `new_timezone`, :1459-1479, on any
`offset` object. `PyDelta_Check` accepts a subclass instance, and `delta_bool` (:1465) and the
range test (:1468-1471) read its stored fields, so its truth and comparison methods are never
called. -/
def timezoneNewObjC (oid : Nat) (offset : TzOffsetArg) (name : TzName) : Py Tz :=
  match offset with
  | .other => .error (.typeError "~timezone() argument 'offset' must be datetime.timedelta")
  | .delta o => timezoneNewC oid o name
  | .sub o _ _ _ => timezoneNewC oid o name

/-- The constructor arguments `timezone.__getinitargs__()` returns. -/
inductive TzInitArgs where
  | one (offset : Delta)
  | two (offset : Delta) (name : String)
  deriving DecidableEq, Repr

/-- `timezone.__getinitargs__`, Py:2487-2491: `(self._offset,)` without a name. -/
def timezoneGetinitargsPy (offset : Delta) (name : Option String) : TzInitArgs :=
  match name with
  | none => .one offset
  | some n => .two offset n

/-- `timezone_getinitargs`, :4526-4532: `PyTuple_Pack(1, ...)` when `name == NULL`. -/
def timezoneGetinitargsC (offset : Delta) (name : Option String) : TzInitArgs :=
  if name.isNone then .one offset else .two offset (name.getD "")

/-- `timezone(*args)` for the arguments of `__getinitargs__`, as unpickling calls it. -/
def timezoneFromInitargsPy (oid : Nat) : TzInitArgs → Py Tz
  | .one o => timezoneNewPy oid o .omitted
  | .two o n => timezoneNewPy oid o (.str n)

/-- `timezone_hash`, :4392-4396: `delta_hash(self->offset)`. -/
def timezoneHashKeyC (offset : Delta) : HashKey := offset.hashKeyC

/-! ### `datetime.combine(date, time, tzinfo)` -/

/-- The `date` argument of `combine`: a `date` or `datetime` (any subclass; its fields), or
another object. -/
inductive DateObj where
  | date (y m d : Int)
  | other
  deriving DecidableEq, Inhabited

/-- The `time` argument of `combine`: a `time` (any subclass), or another object (a `datetime`
is not a `time`). -/
inductive TimeObj where
  | time (t : TM)
  | other
  deriving DecidableEq, Inhabited

/-- `datetime.combine(date, time, tzinfo=True)`, Py:1951-1961: the two `isinstance` checks in
order, `if tzinfo is True: tzinfo = time.tzinfo`, then
`cls(date.year, ..., time.microsecond, tzinfo, fold=time.fold)`, i.e. `datetime.__new__`. -/
def dtCombineArgPy (d : DateObj) (t : TimeObj) (tz : TzParam) : Py DT :=
  match d with
  | .other => .error (.typeError "date argument must be a date instance")
  | .date y m dd =>
    match t with
    | .other => .error (.typeError "time argument must be a time instance")
    | .time t =>
      datetimeNewPy (.int y) (.int m) (.int dd) (.int t.h) (.int t.mi) (.int t.s) (.int t.us)
        (tzParamPy t.tz tz) (.int t.fold)

/-- `datetime_datetime_combine`, clinic/_datetimemodule.c.h:1637-1697: `subclass_of` checks of
`date` (:1678-1681) then `time` (:1683-1686), then `datetime_datetime_combine_impl`,
:5891-5911: an omitted `tzinfo` (`NULL`) is the time's, and `new_datetime_subclass_fold_ex`
(for the base class `new_datetime_ex2`, `datetimeDatetimeImplC`). -/
def dtCombineArgC (d : DateObj) (t : TimeObj) (tz : TzParam) : Py DT :=
  match d with
  | .other => .error (.typeError "~combine() argument 'date' must be datetime.date")
  | .date y m dd =>
    match t with
    | .other => .error (.typeError "~combine() argument 'time' must be datetime.time")
    | .time t => datetimeDatetimeImplC y m dd t.h t.mi t.s t.us (tzParamC t.tz tz) t.fold

/-! ### `datetime.astimezone(tz)` -/

/-- The `tz` argument of `astimezone`: `None` (the default), a `tzinfo`, or another object. -/
inductive AstzArg where
  | none_
  | tz (t : Tz)
  | other
  deriving DecidableEq, Inhabited

/-- `datetime.astimezone(tz)`, Py:2137-2160: `tz is None` takes the local zone (reported as
`none`; the zone is `localTimezoneTsPy`), another non-`tzinfo` is `TypeError` before any
`tzinfo` method is called (:2138-2141), and a `tzinfo` goes on as in `dtAstimezonePy`. -/
def dtAstimezoneArgPy (env : TzEnv) (self : DT) : AstzArg → Py (Option DT)
  | .none_ => .ok none
  | .other => .error (.typeError "tz argument must be an instance of tzinfo")
  | .tz t => dtAstimezonePy env self t

/-- `datetime_datetime_astimezone_impl`, :6914-6922: `check_tzinfo_subclass(tzinfo)` first,
then as in `dtAstimezoneC`. -/
def dtAstimezoneArgC (env : TzEnv) (self : DT) : AstzArg → Py (Option DT)
  | .none_ => .ok none
  | .other => .error (.typeError "~tzinfo argument must be None or of a tzinfo subclass")
  | .tz t => dtAstimezoneC env self t

/-! ### `time.__format__` -/

/-- `time.__format__(fmt)`, Py:1686-1691: `isinstance(fmt, str)`, then `self.strftime(fmt)` for
a nonempty format and `str(self)` otherwise (the method results are parameters). -/
def timeFormatPy {α : Type} (fmt : FmtArg) (str : Py String) (strftime : List Char → Py α) :
    Py (Sum String α) :=
  match fmt with
  | .other => .error (.typeError "~must be str, not")
  | .str cs => if cs.length ≠ 0 then Sum.inr <$> strftime cs else Sum.inl <$> str

/-- `datetime_time___format__`, clinic/_datetimemodule.c.h:1057-1071 (`PyUnicode_Check`), then
`datetime_time___format___impl`, :5012-5020. -/
def timeFormatC {α : Type} (fmt : FmtArg) (str : Py String) (strftime : List Char → Py α) :
    Py (Sum String α) :=
  match fmt with
  | .other => .error (.typeError "~__format__() argument must be str")
  | .str cs => if cs.length = 0 then Sum.inl <$> str else Sum.inr <$> strftime cs

/-! ### `fromisoformat` on any argument -/

/-- `time.fromisoformat(arg)`, Py:1645-1670: `isinstance(time_string, str)` (:1647-1648), then
`timeFromIsoPy`; a string with a lone surrogate fails `isascii()` in `_parse_isoformat_time`
(or is too short), a `ValueError` re-raised as `Invalid isoformat string`. -/
def timeFromIsoArgPy : IsoArg → Py TimeV
  | .str s => timeFromIsoPy s
  | .surrogateStr => .error (.valueError "~Invalid isoformat string")
  | .other => .error (.typeError "fromisoformat: argument must be str")

/-- `time.fromisoformat(arg)` in C: the clinic `unicode` converter
(clinic/_datetimemodule.c.h:1206-1220), then the impl, :5191-5258, whose failed
`PyUnicode_AsUTF8AndSize` on a surrogate goes to `invalid_string_error` (:5198-5200). -/
def timeFromIsoArgC : IsoArg → Py TimeV
  | .str s => timeFromIsoC s
  | .surrogateStr => .error (.valueError "~Invalid isoformat string")
  | .other => .error (.typeError "~fromisoformat() argument must be str")

/-- The argument of `datetime.fromisoformat`: a `str` or another object. A `str` with a lone
surrogate is out of scope here (Lean's `Char` has none, and where the surrogate sits matters:
`_pydatetime` accepts `'20200516\ud800'`, the surrogate being the separator before an empty
time part, the bare-separator difference on record as
`datetime-pydatetime-fromisoformat-trailing-separator`). -/
inductive DtIsoArg where
  | str (s : List Char)
  | other
  deriving DecidableEq, Repr

/-- `datetime.fromisoformat(arg)`, Py:1964-2014: `isinstance(date_string, str)` (:1966-1967),
then `datetimeFromIsoPy`. -/
def datetimeFromIsoArgPy : DtIsoArg → Py DateTimeV
  | .str s => datetimeFromIsoPy s
  | .other => .error (.typeError "fromisoformat: argument must be str")

/-- `datetime.fromisoformat(arg)` in C: the clinic converter (clinic/_datetimemodule.c.h:1712-1726),
then the impl. -/
def datetimeFromIsoArgC : DtIsoArg → Py DateTimeV
  | .str s => datetimeFromIsoC s
  | .other => .error (.typeError "~fromisoformat() argument must be str")

end PyLean.Datetime
