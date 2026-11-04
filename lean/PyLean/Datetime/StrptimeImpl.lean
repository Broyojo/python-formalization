import PyLean.Datetime.SubclassCtor
import PyLean.Datetime.Misc2Props

/-!
The class argument of the `strptime` class methods (CPython 3.15.2): C
`datetime_date_strptime_impl` (Modules/_datetimemodule.c:3521-3536) and `date.strptime`
(Lib/_pydatetime.py:1085-1092) both call `_strptime._strptime_datetime_date(cls, string,
format)` (Lib/_strptime.py:815-820), which calls `cls(*tt[:3])`; and the `timezone` that
`_strptime_datetime_time`/`_datetime` (:829-851) pass to `cls` comes from the `datetime` module
`_strptime` imported (:22-24), which is `_datetime` whenever the C module exists
(Lib/datetime.py:7-10).
-/

namespace PyLean.Datetime

open PyLean

/-- `_strptime._strptime_datetime_date(cls, string, format)`, _strptime.py:815-820, from the
regex match on: `_strptime`, then `cls(*tt[:3])`. -/
def strptimeDateCls (cls : DateClsC) (lt : LocaleTimeV) (found : StrpFound) : Py DT := do
  let r ← strptimeCore lt found
  dateClsCallPy r.year r.month r.day cls

/-- `datetime_date_strptime_impl(type, string, format)`, :3521-3536: import `_strptime` and
call `_strptime_datetime_date(type, string, format)` with the class it was called on. -/
def datetimeDateStrptimeImplC (cls : DateClsC) (lt : LocaleTimeV) (found : StrpFound) : Py DT :=
  strptimeDateCls cls lt found

/-- `date.strptime(cls, date_string, format)`, Py:1085-1092: the same call. -/
def dateStrptimePy (cls : DateClsC) (lt : LocaleTimeV) (found : StrpFound) : Py DT :=
  strptimeDateCls cls lt found

/-- `date.strptime` in both twins, for every class: the C method passes its class on to
`_strptime_datetime_date` as Python's does, so for `date` the result is `strptimeDate`'s date
(the parsed fields checked by `date(y, m, d)`), and a subclass is called with the parsed
year, month and day; a parse error propagates unchanged. -/
def DateStrptimeCls : Prop :=
  ∀ (cls : DateClsC) (lt : LocaleTimeV) (found : StrpFound),
    datetimeDateStrptimeImplC cls lt found = dateStrptimePy cls lt found ∧
    datetimeDateStrptimeImplC .date lt found =
      (fun r => (⟨r.1, r.2.1, r.2.2, 0, 0, 0, 0, 0, none⟩ : DT)) <$> strptimeDate lt found ∧
    (∀ call r, strptimeCore lt found = .ok r →
      datetimeDateStrptimeImplC (.sub call) lt found = call [.int r.year, .int r.month, .int r.day] none) ∧
    (∀ e, strptimeCore lt found = .error e → datetimeDateStrptimeImplC cls lt found = .error e)

theorem dateStrptimeCls_proven : DateStrptimeCls := by
  intro cls lt found
  refine ⟨rfl, ?_, fun call r hr => ?_, fun e he => ?_⟩
  · unfold datetimeDateStrptimeImplC strptimeDateCls strptimeDate
    cases strptimeCore lt found with
    | error e => rfl
    | ok r =>
      simp only [bind, Except.bind, dateClsCallPy]
      have : dateNewPy (.int r.year) (.int r.month) (.int r.day) = checkDate r.year r.month r.day := by
        simp [dateNewPy, checkDateFieldsArgPy, stateOf, pyIndex, bind, Except.bind]
      rw [this]
  · simp [datetimeDateStrptimeImplC, strptimeDateCls, hr, bind, Except.bind, dateClsCallPy]
  · simp [datetimeDateStrptimeImplC, strptimeDateCls, he, bind, Except.bind]

/-! ### The `timezone` of `%z` and the class's implementation -/

/-- The implementation a class, or the `timezone` `_strptime` makes, belongs to. -/
inductive DtImpl where
  | c
  | py
  deriving DecidableEq, Repr

/-- `_strptime_datetime_time(cls, ...)` (_strptime.py:829-839) for a `cls` of implementation
`clsImpl`, with `_strptime`'s own `datetime` module of implementation `stImpl`: `cls(*args)`
without an offset; with one, `cls(*args, tz)` for a `timezone` of `stImpl`, which `cls`'s
tzinfo check (Python's `_check_tzinfo_arg`, Py:608-612, after the field checks, Py:1462-1464;
C's `check_tzinfo_subclass`, :1489-1498) accepts only when the implementations agree. -/
def strptimeTimeImpl (clsImpl stImpl : DtImpl) (lt : LocaleTimeV) (found : StrpFound) : Py TM := do
  let r ← strptimeCore lt found
  match r.gmtoff with
  | none => newTM ⟨r.hour, r.minute, r.second, r.fraction, 0, none⟩
  | some g =>
    let tz ← parseTz r.tzname g r.gmtoffFraction
    let t ← newTM ⟨r.hour, r.minute, r.second, r.fraction, 0, some tz⟩
    if clsImpl ≠ stImpl then
      throw (.typeError "~tzinfo argument must be None or of a tzinfo subclass, not 'timezone'")
    return t

/-- `_strptime_datetime_datetime(cls, ...)`, _strptime.py:841-851, as `strptimeTimeImpl`
(the tzinfo check after the date and time field checks, Py:1818-1821). -/
def strptimeDatetimeImpl (clsImpl stImpl : DtImpl) (lt : LocaleTimeV) (found : StrpFound) : Py DT := do
  let r ← strptimeCore lt found
  match r.gmtoff with
  | none => newDT ⟨r.year, r.month, r.day, r.hour, r.minute, r.second, r.fraction, 0, none⟩
  | some g =>
    let tz ← parseTz r.tzname g r.gmtoffFraction
    let v ← newDT ⟨r.year, r.month, r.day, r.hour, r.minute, r.second, r.fraction, 0, some tz⟩
    if clsImpl ≠ stImpl then
      throw (.typeError "~tzinfo argument must be None or of a tzinfo subclass, not 'timezone'")
    return v

/-- `time.strptime` and `datetime.strptime` (Py:1477-1484, :2225-2232; C
`datetime_time_strptime_impl`, `datetime_datetime_strptime_impl`) when the class and
`_strptime`'s `datetime` module are the same implementation (the configuration
`Lib/datetime.py` sets up, and the one `test_datetime`'s pure run uses, with `_strptime`
imported afresh): the results of `StrptimeTimeDatetime` (`strptimeDatetimeTime`,
`strptimeDatetime`). When they differ, as for `_pydatetime.time.strptime('+0100', '%z')` on a
build with `_datetime` (`_strptime` hands the C `timezone` to the `_pydatetime` class), a
parsed offset that would otherwise give a value is `TypeError` from the class's tzinfo check,
and a format without `%z` gives the same value; mixing the two implementations is not a
supported configuration (gh-137754 is the same mix through `zoneinfo`), so this is a stated
scope, not a defect. -/
def StrptimeClassImpl : Prop :=
  ∀ (lt : LocaleTimeV) (found : StrpFound) (a b : DtImpl),
    (a = b → strptimeTimeImpl a b lt found = strptimeDatetimeTime lt found ∧
      strptimeDatetimeImpl a b lt found = strptimeDatetime lt found) ∧
    (a ≠ b → ∀ r, strptimeCore lt found = .ok r →
      (r.gmtoff = none → strptimeTimeImpl a b lt found = strptimeDatetimeTime lt found ∧
        strptimeDatetimeImpl a b lt found = strptimeDatetime lt found) ∧
      (∀ g t, r.gmtoff = some g → strptimeDatetimeTime lt found = .ok t →
        (strptimeTimeImpl a b lt found).raises "TypeError") ∧
      (∀ g v, r.gmtoff = some g → strptimeDatetime lt found = .ok v →
        (strptimeDatetimeImpl a b lt found).raises "TypeError"))

theorem strptimeClassImpl_proven : StrptimeClassImpl := by
  intro lt found a b
  refine ⟨fun hab => ?_, fun hab r hr => ⟨fun hg => ?_, fun g t hg ht => ?_, fun g v hg hv => ?_⟩⟩
  · subst hab
    constructor
    · unfold strptimeTimeImpl strptimeDatetimeTime
      cases strptimeCore lt found with
      | error e => rfl
      | ok r =>
        simp only [bind, Except.bind]
        cases r.gmtoff with
        | none => rfl
        | some g =>
          simp only
          cases parseTz r.tzname g r.gmtoffFraction with
          | error e => rfl
          | ok tz =>
            simp only
            cases newTM ⟨r.hour, r.minute, r.second, r.fraction, 0, some tz⟩ <;> simp [pure, Except.pure]
    · unfold strptimeDatetimeImpl strptimeDatetime
      cases strptimeCore lt found with
      | error e => rfl
      | ok r =>
        simp only [bind, Except.bind]
        cases r.gmtoff with
        | none => rfl
        | some g =>
          simp only
          cases parseTz r.tzname g r.gmtoffFraction with
          | error e => rfl
          | ok tz =>
            simp only
            cases newDT ⟨r.year, r.month, r.day, r.hour, r.minute, r.second, r.fraction, 0, some tz⟩ <;>
              simp [pure, Except.pure]
  · simp [strptimeTimeImpl, strptimeDatetimeTime, strptimeDatetimeImpl, strptimeDatetime, hr, hg, bind,
      Except.bind]
  · unfold strptimeDatetimeTime at ht
    unfold strptimeTimeImpl
    simp only [hr, hg, bind, Except.bind] at ht ⊢
    cases hp : parseTz r.tzname g r.gmtoffFraction with
    | error e => rw [hp] at ht; cases ht
    | ok tz =>
      rw [hp] at ht
      simp only at ht ⊢
      rw [ht]
      simp only [hab, ne_eq, not_false_eq_true, ite_true]
      exact ⟨_, rfl, rfl⟩
  · unfold strptimeDatetime at hv
    unfold strptimeDatetimeImpl
    simp only [hr, hg, bind, Except.bind] at hv ⊢
    cases hp : parseTz r.tzname g r.gmtoffFraction with
    | error e => rw [hp] at hv; cases hv
    | ok tz =>
      rw [hp] at hv
      simp only at hv ⊢
      rw [hv]
      simp only [hab, ne_eq, not_false_eq_true, ite_true]
      exact ⟨_, rfl, rfl⟩

end PyLean.Datetime
