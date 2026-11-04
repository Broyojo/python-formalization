import PyLean.Datetime.ClsRowsProps
import PyLean.Datetime.CalendarCProps

/-!
Rows of Modules/_datetimemodule.c (CPython 3.15.2) withdrawn by review b666ff1d that need no
class model: the `IsoCalendarDate` getters and `__reduce__`, `date_toordinal`,
`timezone_richcompare`, `look_up_timezone` with `create_timezone_from_delta`, the class
attributes `_PyDateTime_InitTypes` sets, `datetime_str`, and `datetime.now`'s checks around the
clock.
-/

namespace PyLean.Datetime
open PyLean

/-! ### `IsoCalendarDate` -/

/-- `iso_calendar_date_new_impl`, :3843-3876, after the clinic `int` converters (`year: int`,
`week: int`, `weekday: int`): a 3-tuple of the three ints (`PyLong_FromLong` of each). The type
is not subclassable (no `Py_TPFLAGS_BASETYPE`, :3825-3832), so every instance is one of these. -/
def isoCalTupC (y w d : Arg) : Py (List Int) := do
  let y ← parseI y
  let w ← parseI w
  let d ← parseI d
  return [y, w, d]

/-- `PyTuple_GetItem(self, i)` (Objects/tupleobject.c:104-115): the item, or
`IndexError("tuple index out of range")` (`NULL`). -/
def tupleGetItemC (t : List Int) (i : Nat) : Py Int :=
  match t[i]? with
  | some v => .ok v
  | none => .error (.indexError "tuple index out of range")

/-- `iso_calendar_date_year`, :3757-3764; `_week`, :3767-3774; `_weekday`, :3777-3784: the item
or the `NULL` of `PyTuple_GetItem`. -/
def isoCalYearC (t : List Int) : Py Int := tupleGetItemC t 0
def isoCalWeekC (t : List Int) : Py Int := tupleGetItemC t 1
def isoCalWeekdayC (t : List Int) : Py Int := tupleGetItemC t 2

/-- `iso_calendar_date_reduce`, :3743-3754: `(tuple, ((year, week, weekday),))` from
`PyTuple_GET_ITEM` of the three items. -/
def isoCalReduceC (t : List Int) : List Int := [t.getD 0 0, t.getD 1 0, t.getD 2 0]

/-- `_IsoCalendarDate.__new__(cls, year, week, weekday)`, Py:1381-1382: the tuple of the three
objects; `year`, `week`, `weekday` (Py:1384-1394) are `self[0]`, `self[1]`, `self[2]`, and
`__reduce__` (Py:1396-1399) is `(tuple, (tuple(self),))`. -/
def isoCalTupPy (y w d : Int) : List Int := [y, w, d]

/-- `date_isocalendar`, :3879-3911, ends in `iso_calendar_date_new_impl(ISOCALENDAR_DATE_TYPE,
year, week + 1, day + 1)` (:3904-3905) on the computed ints (`isocalendar`). -/
def dateIsocalendarObjC (y m d : Int) : Py (List Int) :=
  let r := isocalendar y m d
  isoCalTupC (.int r.1) (.int r.2.1) (.int r.2.2)

/-- `IsoCalendarDate` in both twins: for all C-int fields the C object is the 3-tuple Python
builds, `year`, `week`, `weekday` read items 0, 1, 2 (never the `NULL` branch) and agree with
Python's `self[0]`, `self[1]`, `self[2]`, and `__reduce__` reduces to the same plain tuple; a
field outside the C `int` range is `OverflowError` before any object exists; and for every
valid date, `isocalendar()`'s attributes are the ISO year, week and weekday that
`fromisocalendar` inverts. -/
def IsoCalendarDateObj : Prop :=
  (∀ y w d : Int, fitsCInt y → fitsCInt w → fitsCInt d →
    isoCalTupC (.int y) (.int w) (.int d) = .ok (isoCalTupPy y w d) ∧
    (isoCalTupC (.int y) (.int w) (.int d) >>= isoCalYearC) = .ok y ∧
    (isoCalTupC (.int y) (.int w) (.int d) >>= isoCalWeekC) = .ok w ∧
    (isoCalTupC (.int y) (.int w) (.int d) >>= isoCalWeekdayC) = .ok d ∧
    (isoCalReduceC <$> isoCalTupC (.int y) (.int w) (.int d)) = .ok (isoCalTupPy y w d)) ∧
  (∀ y w d : Int, ¬ fitsCInt y → (isoCalTupC (.int y) (.int w) (.int d)).raises "OverflowError") ∧
  (∀ y m d : Int, ValidDate y m d →
    ∃ t, dateIsocalendarObjC y m d = .ok t ∧
      fromisocalendarC (t.getD 0 0) (t.getD 1 0) (t.getD 2 0) = .ok (y, m, d) ∧
      isoCalYearC t = .ok (isocalendar y m d).1 ∧ isoCalWeekC t = .ok (isocalendar y m d).2.1 ∧
      isoCalWeekdayC t = .ok (isocalendar y m d).2.2)

/-! ### `date_toordinal` -/

/-- `date_toordinal`, :3987-3991: `ymd_to_ord(GET_YEAR(self), GET_MONTH(self), GET_DAY(self))`. -/
def dateToordinalC (y m d : Int) : Int := ymdToOrdCSrc y m d

/-- C `date.toordinal()` on every valid date: Python's `toordinal` (`_ymd2ord`), in
`1..date.max.toordinal()`, and C's `date.fromordinal` of it gives the date back. -/
def DateToordinalC : Prop :=
  ∀ y m d : Int, ValidDate y m d →
    dateToordinalC y m d = toordinal y m d ∧ 1 ≤ dateToordinalC y m d ∧ dateToordinalC y m d ≤ 3652059 ∧
    fromordinalC (dateToordinalC y m d) = .ok (y, m, d)

/-! ### `timezone_richcompare` -/

/-- `timezone_richcompare(self, other, op)`, :4379-4389, with `other` a `timezone`'s offset
(`some`) or another object (`none`): `NotImplemented` (`none`) for an operator other than `==`
and `!=` (:4381-4382), then for a non-`timezone` (:4383-4385), else `delta_richcompare` of the
offsets. -/
def timezoneRichObjC (op : CmpOp) (self : Delta) (other : Option Delta) : Option Bool :=
  if op ≠ .eq ∧ op ≠ .ne then none
  else match other with
    | none => none
    | some b => some (self.richC op b)

/-- Python: `timezone.__eq__`, Py:2493-2496 (`NotImplemented` for a non-`timezone`); `!=` is
`object.__ne__`, the inverse of `__eq__` unless that is `NotImplemented`; `timezone` defines no
ordering, so `<`, `<=`, `>`, `>=` are `object`'s `NotImplemented`. -/
def timezoneRichObjPy (op : CmpOp) (self : Delta) (other : Option Delta) : Option Bool :=
  match op with
  | .eq => other.map (fun b => self.richPy .eq b)
  | .ne => other.map (fun b => !(self.richPy .eq b))
  | _ => none

/-- `timezone` comparison in both twins, every operator and every right operand: `==` and `!=`
against a `timezone` compare the offsets only (names ignored), `!=` is the negation of `==`;
every ordering operator, and any operator against a non-`timezone`, is `NotImplemented`. -/
def TimezoneRichcompare : Prop :=
  ∀ (op : CmpOp) (a : Delta) (other : Option Delta), a.Valid → (∀ b, other = some b → b.Valid) →
    timezoneRichObjC op a other = timezoneRichObjPy op a other ∧
    (other = none → timezoneRichObjC op a other = none) ∧
    (op ≠ .eq → op ≠ .ne → timezoneRichObjC op a other = none) ∧
    (∀ b, other = some b → timezoneRichObjC .eq a other = some (decide (a.toUs = b.toUs)) ∧
      timezoneRichObjC .ne a other = some (!decide (a.toUs = b.toUs)))

/-! ### `look_up_timezone`, `create_timezone_from_delta`, class attributes -/

/-- `new_delta(days, seconds, us, normalize)` for the base type, `new_delta_ex`, :1383-1411:
`normalize_d_s_us` when asked, the day-range check, then the value (the `zero_delta` singleton
for zero, `look_up_delta`, :3173-3181, which is the same value). -/
def newDeltaC (d s us : Int) (normalize : Bool) : Py Delta := do
  let (d, s, us) := if normalize then normalizeDSUsC d s us else (d, s, us)
  checkDeltaDayRange d
  return ⟨d, s, us⟩

/-- `create_timezone_from_delta(days, sec, ms, normalize)`, :7413-7422: `new_delta`, then
`create_timezone(delta, NULL)` (:1431-1453), whose `look_up_timezone` (:4603-4609) returns
`timezone.utc` for the zero offset with no name. `oid` is the new object's identity. -/
def createTzFromDeltaC (oid : Nat) (d s us : Int) (normalize : Bool) : Py Tz := do
  let delta ← newDeltaC d s us normalize
  return createTimezoneC oid delta none

/-- The class attributes: `timedelta.min/max/resolution`, `date.min/max/resolution`,
`time.min/max/resolution`, `datetime.min/max/resolution`, `timezone.utc/min/max`. -/
structure ClassAttrs where
  tdMin : Delta
  tdMax : Delta
  tdRes : Delta
  dMin : Int × Int × Int
  dMax : Int × Int × Int
  dRes : Delta
  tMin : TM
  tMax : TM
  tRes : Delta
  dtMin : DT
  dtMax : DT
  dtRes : Delta
  tzUtc : Delta
  tzMin : Delta
  tzMax : Delta
  deriving DecidableEq, Repr

/-- The offset of a `timezone`. -/
def Tz.offsetOf (t : Tz) : Delta :=
  match t.kind with
  | .timezone o _ => o
  | .custom _ => ⟨0, 0, 0⟩

/-- `_PyDateTime_InitTypes`, :7532-7607 (after readying the static types, :7536-7542): each
attribute in the source order, through `new_delta` (:7562-7565), `new_date` (:7568-7571),
`new_time` (:7574-7577), `new_datetime` (:7580-7585) and, for `timezone`, the static
`utc_timezone` (:7589-7591) and `create_timezone_from_delta(-1, 60, 0, 1)` and
`(0, (23 * 60 + 59) * 60, 0, 0)` (:7597-7601). -/
def initTypesC : Py ClassAttrs := do
  let tdRes ← newDeltaC 0 0 1 false
  let tdMin ← newDeltaC (-MAX_DELTA_DAYS) 0 0 false
  let tdMax ← newDeltaC MAX_DELTA_DAYS (24 * 3600 - 1) (1000000 - 1) false
  let dMin ← checkDateC 1 1 1
  let dMax ← checkDateC MAXYEAR 12 31
  let dRes ← newDeltaC 1 0 0 false
  let tMin ← datetimeTimeImplC 0 0 0 0 .none_ 0
  let tMax ← datetimeTimeImplC 23 59 59 999999 .none_ 0
  let tRes ← newDeltaC 0 0 1 false
  let dtMin ← datetimeDatetimeImplC 1 1 1 0 0 0 0 .none_ 0
  let dtMax ← datetimeDatetimeImplC MAXYEAR 12 31 23 59 59 999999 .none_ 0
  let dtRes ← newDeltaC 0 0 1 false
  let tzMin ← createTzFromDeltaC 1 (-1) 60 0 true
  let tzMax ← createTzFromDeltaC 2 0 ((23 * 60 + 59) * 60) 0 false
  return ⟨tdMin, tdMax, tdRes, dMin, dMax, dRes, tMin, tMax, tRes, dtMin, dtMax, dtRes,
    tzUTC.offsetOf, tzMin.offsetOf, tzMax.offsetOf⟩

/-- The same attributes in `_pydatetime`: Py:965-968, 1313-1315, 1787-1789, 2439-2441,
2576 (`timezone._create(timedelta(0))`) and 2581-2582
(`timezone._create(-timedelta(hours=23, minutes=59))`, `timezone._create(timedelta(hours=23,
minutes=59))`, `_create` storing the offset unchecked, Py:2481-2485). -/
def classAttrsPy : Py ClassAttrs := do
  let tdMin ← deltaPy (-999999999) 0 0 0 0 0 0
  let tdMax ← deltaPy 999999999 59 999999 0 59 23 0
  let tdRes ← deltaPy 0 0 1 0 0 0 0
  let dMin ← dateNewPy (.int 1) (.int 1) (.int 1)
  let dMax ← dateNewPy (.int 9999) (.int 12) (.int 31)
  let dRes ← deltaPy 1 0 0 0 0 0 0
  let tMin ← timeNewPy (.int 0) (.int 0) (.int 0) (.int 0) .none_ (.int 0)
  let tMax ← timeNewPy (.int 23) (.int 59) (.int 59) (.int 999999) .none_ (.int 0)
  let tRes ← deltaPy 0 0 1 0 0 0 0
  let dtMin ← datetimeNewPy (.int 1) (.int 1) (.int 1) (.int 0) (.int 0) (.int 0) (.int 0) .none_ (.int 0)
  let dtMax ← datetimeNewPy (.int 9999) (.int 12) (.int 31) (.int 23) (.int 59) (.int 59) (.int 999999) .none_ (.int 0)
  let dtRes ← deltaPy 0 0 1 0 0 0 0
  let utc ← deltaPy 0 0 0 0 0 0 0
  let m ← deltaPy 0 0 0 0 59 23 0
  let tzMin ← m.negPy
  let tzMax ← deltaPy 0 0 0 0 59 23 0
  return ⟨tdMin, tdMax, tdRes, dMin, dMax, dRes, tMin, tMax, tRes, dtMin, dtMax, dtRes, utc, tzMin, tzMax⟩

/-- The class attributes agree between the twins (values; the `timezone` attributes by their
offsets), and `timezone.min`/`max` are -23:59/+23:59 as documented. `create_timezone_from_delta`
reaches `look_up_timezone`'s `utc` branch exactly for a zero offset (it returns the `utc`
singleton itself), and otherwise builds a new `timezone` of the normalized offset. -/
def InitTypesTwins : Prop :=
  initTypesC = classAttrsPy ∧
  (∃ a, initTypesC = .ok a ∧ a.tzMin.toUs = -(23 * 3600 + 59 * 60) * 1000000 ∧ a.tzMax.toUs = (23 * 3600 + 59 * 60) * 1000000) ∧
  (∀ (oid : Nat) (n : Bool), createTzFromDeltaC oid 0 0 0 n = .ok tzUTC) ∧
  (∀ (oid : Nat) (d s us : Int) (n : Bool) (r : Delta), newDeltaC d s us n = .ok r → r ≠ ⟨0, 0, 0⟩ →
    createTzFromDeltaC oid d s us n = .ok ⟨oid, .timezone r none⟩)

/-! ### `datetime_str` -/

/-- How a `datetime` object answers `isoformat` called with positional arguments `pos` and
keyword arguments `kw` (the method found on its class: the built-in one or an override). -/
abbrev IsoformatMeth := List Arg → List (String × Arg) → Py String

/-- `datetime_str`, :6416-6425: `PyObject_CallMethodOneArg(self, "isoformat", " ")`, the
separator passed positionally. -/
def datetimeStrC (meth : IsoformatMeth) : Py String := meth [.str [32]] []

/-- `datetime.__str__`, Py:2220-2222: `self.isoformat(sep=' ')`. -/
def datetimeStrPy (meth : IsoformatMeth) : Py String := meth [] [("sep", .str [32])]

/-- The built-in `datetime.isoformat(sep='T', timespec='auto')` as a method: `sep` taken
positionally or by keyword, then `dtIsoformatC` (for an `isoformat` that is the C one). -/
def builtinIsoformat (env : TzEnv) (dt : DT) : IsoformatMeth
  | [.str [c]], [] => dtIsoformatC env dt (Char.ofNat c) .auto
  | [], [("sep", .str [c])] => dtIsoformatC env dt (Char.ofNat c) .auto
  | _, _ => .error (.typeError "~isoformat() arguments")

/-- `str(dt)` calls the object's own `isoformat` in both twins; for the built-in method both
give `dt.isoformat(' ')` (`DatetimeIsoformatTwins` pins its text against Python). -/
def DatetimeStrCall : Prop :=
  (∀ (env : TzEnv) (dt : DT), datetimeStrC (builtinIsoformat env dt) = dtIsoformatC env dt ' ' .auto ∧
    datetimeStrPy (builtinIsoformat env dt) = dtIsoformatC env dt ' ' .auto) ∧
  (∀ meth : IsoformatMeth, datetimeStrC meth = meth [.str [32]] [] ∧ datetimeStrPy meth = meth [] [("sep", .str [32])])

/-- The broad twin: `str(dt)` agrees for every `isoformat` a subclass may define. -/
def DatetimeStrTwins : Prop := ∀ meth : IsoformatMeth, datetimeStrC meth = datetimeStrPy meth

/-! ### `datetime.now` -/

/-- `datetime_datetime_now_impl(type, tz)`, :5721-5743: `check_tzinfo_subclass(tz)` (:5729-5730)
before the clock is read; `datetime_best_possible` (:5732-5735, the clock, `localtime` for
`None` and `gmtime` otherwise, building through `type`) is the parameter `best`; for a `tzinfo`,
`tz.fromutc(self)` (:5736-5740), a method call (`fromutc`). -/
def datetimeNowC {α : Type} (best : Option Tz → Py α) (fromutc : Tz → α → Py α) (tz : Arg) : Py α := do
  let t ← checkTzinfoSubclassC tz
  let self ← best t
  match t with
  | none => pure self
  | some z => fromutc z self

/-- `datetime.now(tz)` in C on every argument: a `tz` that is neither `None` nor a `tzinfo` is
`TypeError` whatever the clock does (it is not read); `None` is the local reading; a `tzinfo`
gets the UTC reading passed to its `fromutc`, whose result (or exception) is returned, and an
error of the clock comes first. -/
def DatetimeNowChecks : Prop :=
  ∀ {α : Type} (best best' : Option Tz → Py α) (fromutc : Tz → α → Py α),
    (∀ a : Arg, (∀ z, a ≠ .tz z) → a ≠ .none_ →
      (datetimeNowC best fromutc a).raises "TypeError" ∧ datetimeNowC best fromutc a = datetimeNowC best' fromutc a) ∧
    datetimeNowC best fromutc .none_ = best none ∧
    (∀ z : Tz, datetimeNowC best fromutc (.tz z) = (best (some z) >>= fromutc z))

end PyLean.Datetime
