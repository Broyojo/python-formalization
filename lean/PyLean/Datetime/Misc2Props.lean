import PyLean.Datetime.ReprProps

/-!
Rows the review 50b4b958 left hollow that need a statement of their own: the abstract
`tzinfo` methods through subclass dispatch, `IsoCalendarDate.__new__`, and
`time.strptime`/`datetime.strptime` on every parse.
-/

namespace PyLean.Datetime
open PyLean

/-! ### The abstract `tzinfo` methods -/

/-- `env` with the methods of subclass `i` not overridden: what `tzinfo.tzname`,
`tzinfo.utcoffset` and `tzinfo.dst` do, given as `nogo` (Py:1325-1339 raise
`NotImplementedError("tzinfo subclass must override ...()")`; C `tzinfo_nogo`, :4143-4149,
`"a tzinfo subclass must implement ...()"`). -/
def TzEnv.inherit (env : TzEnv) (i : Nat) (nogo : String → PyExc) : TzEnv :=
  { env with
    utcoffset := fun j a => if j = i then .error (nogo "utcoffset") else env.utcoffset j a
    dst := fun j a => if j = i then .error (nogo "dst") else env.dst j a
    tzname := fun j a => if j = i then .error (nogo "tzname") else env.tzname j a }

/-- A `tzinfo` subclass that does not override `utcoffset`, `dst` or `tzname`: through
`datetime.utcoffset()`/`dst()`/`tzname()` and `time.utcoffset()`/`dst()`/`tzname()` the base
method runs and raises `NotImplementedError` in both twins, before any result check, with the
twin's own message (`tzinfo subclass must override utcoffset()` in Python, `a tzinfo subclass
must implement utcoffset()` in C). -/
def TzinfoBaseDispatch : Prop :=
  ∀ (env : TzEnv) (oid i : Nat) (dt : DT) (t : TM), dt.tz = some ⟨oid, .custom i⟩ → t.tz = some ⟨oid, .custom i⟩ →
    let ep := env.inherit i tzinfoBasePy
    let ec := env.inherit i tzinfoNogoC
    dt.utcoffsetPy ep = .error (.named "NotImplementedError" "tzinfo subclass must override utcoffset()") ∧
    dt.dstPy ep = .error (.named "NotImplementedError" "tzinfo subclass must override dst()") ∧
    dt.tznamePy ep = .error (.named "NotImplementedError" "tzinfo subclass must override tzname()") ∧
    t.utcoffsetPy ep = .error (.named "NotImplementedError" "tzinfo subclass must override utcoffset()") ∧
    t.dstPy ep = .error (.named "NotImplementedError" "tzinfo subclass must override dst()") ∧
    t.tznamePy ep = .error (.named "NotImplementedError" "tzinfo subclass must override tzname()") ∧
    dt.utcoffsetC ec = .error (.named "NotImplementedError" "a tzinfo subclass must implement utcoffset()") ∧
    dt.dstC ec = .error (.named "NotImplementedError" "a tzinfo subclass must implement dst()") ∧
    dt.tznameC ec = .error (.named "NotImplementedError" "a tzinfo subclass must implement tzname()") ∧
    t.utcoffsetC ec = .error (.named "NotImplementedError" "a tzinfo subclass must implement utcoffset()")

theorem tzinfoBaseDispatch_proven : TzinfoBaseDispatch := by
  intro env oid i dt t hd ht
  simp [TzEnv.inherit, DT.utcoffsetPy, DT.dstPy, DT.tznamePy, TM.utcoffsetPy, TM.dstPy, TM.tznamePy,
    DT.utcoffsetC, DT.dstC, DT.tznameC, TM.utcoffsetC, hd, ht, tzUtcoffsetRaw, tzDstRaw, tzTznameRawPy,
    tzTznameRawC, tzinfoBasePy, tzinfoNogoC, bind, Except.bind]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### `IsoCalendarDate.__new__` -/

/-- `IsoCalendarDate.__new__(cls, year, week, weekday, /)`, Py:1381-1382:
`super().__new__(cls, (year, week, weekday))`, the three objects as they are. -/
def isoCalNewPy (y w d : Arg) : Py (Arg × Arg × Arg) := .ok (y, w, d)

/-- `iso_calendar_date_new_impl`, :3843-3870, after the clinic `int` converters
(`PyLong_AsInt`): the three converted ints. -/
def isoCalNewC (y w d : Arg) : Py (Arg × Arg × Arg) := do
  let a ← parseI y
  let b ← parseI w
  let c ← parseI d
  return (.int a, .int b, .int c)

/-- `IsoCalendarDate(year, week, weekday)` for int arguments within C `int` (what
`date.isocalendar()` passes): the same three items in both twins, unchecked (no week or weekday
range); Python stores any three objects as they are. -/
def IsoCalendarDateNew : Prop :=
  ∀ (y w d : Int) (a b c : Arg), fitsCInt y → fitsCInt w → fitsCInt d →
    isoCalNewPy (.int y) (.int w) (.int d) = .ok (.int y, .int w, .int d) ∧
    isoCalNewC (.int y) (.int w) (.int d) = .ok (.int y, .int w, .int d) ∧
    isoCalNewPy a b c = .ok (a, b, c)

theorem isoCalendarDateNew_proven : IsoCalendarDateNew := by
  intro y w d a b c hy hw hd
  refine ⟨rfl, ?_, rfl⟩
  simp [isoCalNewC, parseI_int y hy, parseI_int w hw, parseI_int d hd, bind, Except.bind, pure, Except.pure]

/-- `IsoCalendarDate(year, week, weekday)` agrees between the twins for every argument. -/
def IsoCalendarDateNewTwins : Prop :=
  ∀ (a b c : Arg), SameOutcome (isoCalNewPy a b c) (isoCalNewC a b c)

/-- `IsoCalendarDate('a', 2, 3)`: Python stores the str, C's `int` converter raises
`TypeError`. -/
theorem isoCalendarDateNewTwins_refuted : ¬IsoCalendarDateNewTwins := by
  intro h
  have := h (.str [97]) (.int 2) (.int 3)
  exact this

/-! ### `time.strptime` and `datetime.strptime` -/

/-- `time.strptime(s, fmt)` and `datetime.strptime(s, fmt)` (`_strptime_datetime_time` and
`_strptime_datetime_datetime`, _strptime.py:829-851) for every parse `found`: an exception of
`_strptime` propagates in both; a parse with no UTC offset gives exactly the naive datetime of
the parsed fields (and the naive time of its time fields) when they are in range, and the
constructor's `ValueError` otherwise; a parse with an offset attaches the `timezone`
`_parse_tz` builds; and the methods are not vacuous: with a locale without alternative digits,
`'%H:%M'` on `12:30` is `time(12, 30)` and `'%Y %m %d %H %M'` on `2024 1 2 12 30` is
`datetime(2024, 1, 2, 12, 30)`. -/
def StrptimeTimeDatetime : Prop :=
  ∀ (lt : LocaleTimeV) (found : StrpFound),
    (∀ e, strptimeCore lt found = .error e →
      strptimeDatetimeTime lt found = .error e ∧ strptimeDatetime lt found = .error e) ∧
    (∀ r, strptimeCore lt found = .ok r → r.gmtoff = none →
      strptimeDatetimeTime lt found = newTM ⟨r.hour, r.minute, r.second, r.fraction, 0, none⟩ ∧
      strptimeDatetime lt found = newDT ⟨r.year, r.month, r.day, r.hour, r.minute, r.second, r.fraction, 0, none⟩) ∧
    (∀ r g tz, strptimeCore lt found = .ok r → r.gmtoff = some g → parseTz r.tzname g r.gmtoffFraction = .ok tz →
      strptimeDatetimeTime lt found = newTM ⟨r.hour, r.minute, r.second, r.fraction, 0, some tz⟩ ∧
      strptimeDatetime lt found = newDT ⟨r.year, r.month, r.day, r.hour, r.minute, r.second, r.fraction, 0, some tz⟩) ∧
    (lt.altDigits = none →
      strptimeDatetimeTime lt [("H", some "12"), ("M", some "30")] = .ok ⟨12, 30, 0, 0, 0, none⟩ ∧
      strptimeDatetime lt [("Y", some "2024"), ("m", some "1"), ("d", some "2"), ("H", some "12"), ("M", some "30")] =
        .ok ⟨2024, 1, 2, 12, 30, 0, 0, 0, none⟩)

theorem strptimeTimeDatetime_proven : StrptimeTimeDatetime := by
  intro lt found
  refine ⟨fun e h => ?_, fun r h hg => ?_, fun r g tz h hg hz => ?_, fun hlt => ?_⟩
  · simp [strptimeDatetimeTime, strptimeDatetime, h, bind, Except.bind]
  · simp [strptimeDatetimeTime, strptimeDatetime, h, hg, bind, Except.bind]
  · simp [strptimeDatetimeTime, strptimeDatetime, h, hg, hz, bind, Except.bind]
  · have hp : ∀ s, parseIntLt lt s = pyInt s.toList := by
      intro s; simp [parseIntLt, hlt]
    refine ⟨?_, ?_⟩
    · simp [strptimeDatetimeTime, strptimeCore, strpStep, foundGet, hp, bind, Except.bind, pure, Except.pure]
      decide
    · simp [strptimeDatetime, strptimeCore, strpStep, foundGet, hp, bind, Except.bind, pure, Except.pure]
      decide

end PyLean.Datetime
