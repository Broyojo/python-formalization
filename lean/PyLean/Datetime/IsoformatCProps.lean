import PyLean.Datetime.FmtTwinsProps
import PyLean.Datetime.DtProps

/-!
`time.isoformat`, `datetime.isoformat` and `str()` of `date` and `time` in both twins: the
C side formats the offset with its own `format_utcoffset` (Modules/_datetimemodule.c:1731-1776),
and `date_str`/`time_str` call `self.isoformat()` through the object's class, where Python binds
`__str__ = isoformat` to the base class's function (Lib/_pydatetime.py:1150, :1642).
-/

namespace PyLean.Datetime

open PyLean

theorem tm_offset_valid (env : TzEnv) (henv : env.Valid) (a : TM) (h : OptTzOk a.tz) (o : Delta)
    (ho : a.utcoffsetPy env = .ok (some o)) : o.Valid := by
  unfold TM.utcoffsetPy at ho
  split at ho
  · cases ho
  · rename_i tz htz
    rw [htz] at h
    cases hr : tzUtcoffsetRaw env tz none with
    | error e => rw [hr] at ho; cases ho
    | ok v =>
      rw [hr] at ho
      cases v with
      | none => cases ho
      | other ty => cases ho
      | delta d =>
        simp only [bind, Except.bind, checkUtcOffset] at ho
        split at ho
        · cases ho
        · cases ho; exact raw_off_valid env henv tz h _ o hr

/-- `time.isoformat(timespec)` and `str(time)` agree between the twins for every timespec
and every valid tzinfo method table: Python's `_format_offset` and C's `format_utcoffset`
give the same text for every offset `utcoffset()` can return. -/
def TimeIsoformatTwins : Prop :=
  ∀ (env : TzEnv) (t : TM) (spec : TimeSpec), env.Valid → OptTzOk t.tz →
    tmIsoformatPy env t spec = tmIsoformatC env t spec

theorem timeIsoformatTwins_proven : TimeIsoformatTwins := by
  intro env t spec henv h
  unfold tmIsoformatPy tmIsoformatC tmTzstrPy
  have hv := tm_offset_valid env henv t h
  have hr := (timeOffsets_proven env t henv h).2.2
  rw [tm_utcoffset_twin env henv t h] at *
  cases hc : t.utcoffsetC env with
  | error e => rfl
  | ok off =>
    cases off with
    | none => rfl
    | some o =>
      have e := (formatOffsetText_proven [':'] (some o)
        (fun x hx => by cases hx; exact ⟨hv o hc, hr o hc⟩)).2
      simp only [bind, Except.bind, pure, Except.pure]
      rw [e]; rfl

/-- `datetime.isoformat(sep, timespec)` and `str(datetime)` agree between the twins for every
`sep` and `timespec`, as `TimeIsoformatTwins`. -/
def DatetimeIsoformatTwins : Prop :=
  ∀ (env : TzEnv) (dt : DT) (sep : Char) (spec : TimeSpec), env.Valid → OptTzOk dt.tz →
    dtIsoformatPy env dt sep spec = dtIsoformatC env dt sep spec

theorem datetimeIsoformatTwins_proven : DatetimeIsoformatTwins := by
  intro env dt sep spec henv h
  unfold dtIsoformatPy dtIsoformatC
  have hv := dt_offset_valid env henv dt h
  have hr := dt_offset_range env henv dt h
  rw [dt_utcoffset_twin env henv dt h] at *
  cases hc : dt.utcoffsetC env with
  | error e => rfl
  | ok off =>
    cases off with
    | none => rfl
    | some o =>
      have e := (formatOffsetText_proven [':'] (some o)
        (fun x hx => by cases hx; exact ⟨hv o hc, hr o hc⟩)).2
      simp only [bind, Except.bind, pure, Except.pure]
      rw [e]; rfl

/-! ### `str()` through `isoformat` -/

/-- What `self.isoformat()` finds on the object's class: the inherited method (`none`), or a
subclass's own `isoformat` and what calling it returns (any object's `str`, or an exception;
a non-`str` result would be refused by `str()` in both twins and is out of scope). -/
abbrev IsoOverride := Option (Py String)

/-- `date_str`, :3637-3640, and `time_str`, :4880-4883:
`PyObject_CallMethodNoArgs(self, "isoformat")`, a lookup on the object's class. `base` is the
inherited `isoformat()` with no arguments. -/
def strViaIsoformatC (base : Py String) : IsoOverride → Py String
  | none => base
  | some r => r

/-- `date.__str__ = isoformat` (Py:1150) and `time.__str__ = isoformat` (Py:1642): the class
attribute is the base class's function object, so `str()` runs it whatever the subclass
defines. -/
def strViaIsoformatPy (base : Py String) (_ov : IsoOverride) : Py String := base

/-- `str(d)` for a date and `str(t)` for a time in each twin. -/
def dateStrC (y m d : Int) (ov : IsoOverride) : Py String :=
  strViaIsoformatC (.ok (String.ofList (dateIsoformatC y m d))) ov
def dateStrPy (y m d : Int) (ov : IsoOverride) : Py String :=
  strViaIsoformatPy (.ok (String.ofList (dateIsoformat y m d))) ov
def timeStrC (env : TzEnv) (t : TM) (ov : IsoOverride) : Py String :=
  strViaIsoformatC (tmIsoformatC env t .auto) ov
def timeStrPy (env : TzEnv) (t : TM) (ov : IsoOverride) : Py String :=
  strViaIsoformatPy (tmIsoformatPy env t .auto) ov

/-- `str()` of a `date` or `time` whose class does not override `isoformat` is the same text
in both twins (for a valid date; a time with a valid tzinfo table), the date's being
`YYYY-MM-DD`; in C, a class that overrides `isoformat` gets its override's result or
exception. `StrIsoformatOverrideTwins` drops the assumption and is refuted. -/
def StrViaIsoformat : Prop :=
  (∀ y m d : Int, ValidDate y m d →
    dateStrC y m d none = dateStrPy y m d none ∧
    dateStrC y m d none = .ok (String.ofList (dateIsoformat y m d))) ∧
  (∀ (env : TzEnv) (t : TM), env.Valid → OptTzOk t.tz → timeStrC env t none = timeStrPy env t none) ∧
  (∀ (r : Py String) (y m d : Int) (env : TzEnv) (t : TM),
    dateStrC y m d (some r) = r ∧ timeStrC env t (some r) = r)

theorem strViaIsoformat_proven : StrViaIsoformat := by
  refine ⟨fun y m d hv => ?_, fun env t henv h => ?_, fun r y m d env t => ⟨rfl, rfl⟩⟩
  · have e := (dateIsoformatText_proven y m d hv).2
    refine ⟨?_, ?_⟩ <;> simp [dateStrC, dateStrPy, strViaIsoformatC, strViaIsoformatPy, e]
  · simp only [timeStrC, timeStrPy, strViaIsoformatC, strViaIsoformatPy]
    exact (timeIsoformatTwins_proven env t .auto henv h).symm

/-- `str()` of a `date` agrees between the twins for every class, a subclass that overrides
`isoformat` included. -/
def StrIsoformatOverrideTwins : Prop :=
  ∀ (y m d : Int) (ov : IsoOverride), ValidDate y m d → dateStrC y m d ov = dateStrPy y m d ov

/-- `class D(date): def isoformat(self): return "X"`; `str(D(2000, 1, 1))` is `'X'` in C
(`date_str` calls `self.isoformat()`) and `'2000-01-01'` in `_pydatetime`, whose
`__str__ = isoformat` is `date.isoformat` itself (CPython 3.15.2; `time` behaves the same). -/
theorem strIsoformatOverrideTwins_refuted : ¬ StrIsoformatOverrideTwins := by
  intro h
  have := h 2000 1 1 (some (.ok "X")) (by decide)
  simp [dateStrC, dateStrPy, strViaIsoformatC, strViaIsoformatPy] at this
  revert this
  decide

/-! ### `append_keyword_fold` -/

/-- Python's fold suffix of `time.__repr__` (Py:1620-1622) and `datetime.__repr__`
(Py:2215-2217): `if self._fold: s = s[:-1] + ", fold=1)"`, the literal `1`. -/
def appendFoldPy (s : String) (fold : Int) : String :=
  if fold ≠ 0 then (s.dropEnd 1).toString ++ ", fold=1)" else s

/-- C `append_keyword_fold(repr, fold)` (`appendFold`, :1653-1669) prints the fold with `%d`
where Python prints the literal `1`, so the two agree for every fold a `time` or `datetime`
can hold (`0` or `1`, the type invariant), leave a zero fold's text alone, and replace the
closing `)` by `, fold=1)` for fold 1. -/
def AppendFoldTwins : Prop :=
  ∀ (s : String) (fold : Int), (fold = 0 ∨ fold = 1) →
    appendFold s fold = appendFoldPy s fold ∧
    (fold = 0 → appendFold s fold = s) ∧
    (fold = 1 → appendFold s fold = (s.dropEnd 1).toString ++ ", fold=1)")

theorem appendFoldTwins_proven : AppendFoldTwins := by
  intro s fold h
  rcases h with rfl | rfl
  · exact ⟨by simp [appendFold, appendFoldPy], fun _ => by simp [appendFold], fun h => absurd h (by decide)⟩
  · have e : fmtD 1 = "1" := by decide
    have e2 : (toString ", fold=" ++ toString "1" ++ toString ")" : String) = ", fold=1)" := by decide
    refine ⟨?_, fun h => absurd h (by decide), fun _ => ?_⟩ <;>
      simp [appendFold, appendFoldPy, e, e2]

end PyLean.Datetime
