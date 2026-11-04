import PyLean.Datetime.CmpProps2

/-!
`repr` of `time` and `datetime` with the class (review 50b4b958), as `date` and `timedelta`
already are: Python prints `_get_class_module(self)` and `__qualname__`, C prints
`Py_TYPE(self)->tp_name`; and the keyword order of `datetime_repr` (fold before tzinfo).
-/

namespace PyLean.Datetime
open PyLean

/-- `__qualname__` of `time` or a subclass. -/
def ReprCls.tmQualname : ReprCls → String
  | .base => "time"
  | .sub _ q _ => q

/-- `tp_name` of `time` or a heap subclass. -/
def ReprCls.tmTpName : ReprCls → String
  | .base => "datetime.time"
  | .sub _ _ n => n

/-- `__qualname__` of `datetime` or a subclass. -/
def ReprCls.dtQualname : ReprCls → String
  | .base => "datetime"
  | .sub _ q _ => q

/-- `tp_name` of `datetime` or a heap subclass. -/
def ReprCls.dtTpName : ReprCls → String
  | .base => "datetime.datetime"
  | .sub _ _ n => n

/-- The positional part of `time.__repr__`, Py:1608-1616, after the class prefix `pre`. -/
def tmReprBodyPy (pre : String) (t : TM) : String :=
  let s := if t.us ≠ 0 then s!", {fmtD t.s}, {fmtD t.us}"
    else if t.s ≠ 0 then s!", {fmtD t.s}" else ""
  s!"{pre}({fmtD t.h}, {fmtD t.mi}{s})"

/-- The positional part of `time_repr`, :4864-4871, after `type_name`. -/
def tmReprBodyC (pre : String) (t : TM) : String :=
  if t.us ≠ 0 then s!"{pre}({fmtD t.h}, {fmtD t.mi}, {fmtD t.s}, {fmtD t.us})"
  else if t.s ≠ 0 then s!"{pre}({fmtD t.h}, {fmtD t.mi}, {fmtD t.s})"
  else s!"{pre}({fmtD t.h}, {fmtD t.mi})"

/-- `time.__repr__`, Py:1606-1623: `"%s%s(%d, %d%s)" % (_get_class_module(self),
self.__class__.__qualname__, ...)`, then `, tzinfo=%r`, then `, fold=1`. -/
def tmReprClsPy (env : TzEnv) (c : ReprCls) (t : TM) : String :=
  appendFold (appendTzinfo env (tmReprBodyPy (getClassModule c.module ++ c.tmQualname) t) t.tz) t.fold

/-- `time_repr`, :4852-4876: `Py_TYPE(self)->tp_name`, then tzinfo (:4872-4873), then fold
(:4874-4875). -/
def tmReprClsC (env : TzEnv) (c : ReprCls) (t : TM) : String :=
  appendFold (appendTzinfo env (tmReprBodyC c.tmTpName t) t.tz) t.fold

/-- The positional part of `datetime.__repr__`, Py:2203-2211: the seven fields with up to two
trailing zeros dropped, joined with `', '`. -/
def dtReprBodyPy (pre : String) (dt : DT) : String :=
  let L := [dt.y, dt.m, dt.d, dt.h, dt.mi, dt.s, dt.us]
  let L := if L.getLast? = some 0 then L.dropLast else L
  let L := if L.getLast? = some 0 then L.dropLast else L
  s!"{pre}({", ".intercalate (L.map fmtD)})"

/-- The positional part of `datetime_repr`, :6384-6405. -/
def dtReprBodyC (pre : String) (dt : DT) : String :=
  let f (xs : List Int) := s!"{pre}({", ".intercalate (xs.map fmtD)})"
  if dt.us ≠ 0 then f [dt.y, dt.m, dt.d, dt.h, dt.mi, dt.s, dt.us]
  else if dt.s ≠ 0 then f [dt.y, dt.m, dt.d, dt.h, dt.mi, dt.s]
  else f [dt.y, dt.m, dt.d, dt.h, dt.mi]

/-- `datetime.__repr__`, Py:2201-2218: the class prefix, then tzinfo, then fold. -/
def dtReprClsPy (env : TzEnv) (c : ReprCls) (dt : DT) : String :=
  appendFold (appendTzinfo env (dtReprBodyPy (getClassModule c.module ++ c.dtQualname) dt) dt.tz) dt.fold

/-- `datetime_repr`, :6378-6413: `tp_name`, then fold (:6408-6409), then tzinfo (:6410-6412). -/
def dtReprClsC (env : TzEnv) (c : ReprCls) (dt : DT) : String :=
  appendTzinfo env (appendFold (dtReprBodyC c.dtTpName dt) dt.fold) dt.tz

theorem tmReprBody_twin (pre : String) (t : TM) : tmReprBodyPy pre t = tmReprBodyC pre t := by
  unfold tmReprBodyPy tmReprBodyC
  by_cases h1 : t.us = 0
  · by_cases h2 : t.s = 0
    · simp [h1, h2, toString, String.append_assoc]
    · simp [h1, h2, toString, String.append_assoc]
  · simp [h1, toString, String.append_assoc]

theorem dtReprBody_twin (pre : String) (dt : DT) (_hd : dt.d ≠ 0) : dtReprBodyPy pre dt = dtReprBodyC pre dt := by
  unfold dtReprBodyPy dtReprBodyC
  by_cases h1 : dt.us = 0
  · by_cases h2 : dt.s = 0
    · simp [h1, h2]
    · simp [h1, h2]
  · simp [h1]

/-- The class prefix both twins print for `time`/`datetime` and their subclasses that are not
nested and not defined in a module named `datetime`. -/
def ReprCls.Plain (c : ReprCls) : Prop :=
  c = .base ∨ ∃ mod name, c = .sub mod name name ∧ mod ≠ "datetime"

/-- `repr(time)` is the same text in both twins for the base class and every subclass whose
`__qualname__` is its `__name__` and whose module is not named `datetime`, for every field
value, tzinfo and fold: the class prefix, the positional fields without trailing zero second
and microsecond, then `tzinfo=` and `fold=` in that order in both. -/
def TimeReprCls : Prop :=
  ∀ (env : TzEnv) (c : ReprCls) (t : TM), c.Plain → tmReprClsPy env c t = tmReprClsC env c t

theorem timeReprCls_proven : TimeReprCls := by
  intro env c t hc
  unfold tmReprClsPy tmReprClsC
  rw [tmReprBody_twin]
  rcases hc with rfl | ⟨mod, name, rfl, hm⟩
  · rfl
  · simp [getClassModule, hm, ReprCls.module, ReprCls.tmQualname, ReprCls.tmTpName]

/-- `repr(time)` agrees between the twins for every class. -/
def TimeReprClsTwins : Prop :=
  ∀ (env : TzEnv) (c : ReprCls) (t : TM), tmReprClsPy env c t = tmReprClsC env c t

/-- `class Outer: class T(time): pass`; `repr(Outer.T(1, 2))`: `Outer.T(1, 2)` in Python
(`__qualname__`), `T(1, 2)` in C (`tp_name`). -/
theorem timeReprClsTwins_refuted : ¬TimeReprClsTwins := by
  intro h
  have := h emptyEnv (.sub "__main__" "Outer.T" "T") ⟨1, 2, 0, 0, 0, none⟩
  revert this
  decide

/-- `repr(datetime)` is the same text in both twins for the base class and every plain
subclass, for every datetime without both a fold of 1 and a tzinfo. -/
def DatetimeReprCls : Prop :=
  ∀ (env : TzEnv) (c : ReprCls) (dt : DT), c.Plain → dt.Valid → (dt.fold = 0 ∨ dt.tz = none) →
    dtReprClsPy env c dt = dtReprClsC env c dt

theorem datetimeReprCls_proven : DatetimeReprCls := by
  intro env c dt hc hv hf
  have hd : dt.d ≠ 0 := by have := hv.1; unfold ValidDate at this; omega
  unfold dtReprClsPy dtReprClsC
  rw [dtReprBody_twin _ _ hd]
  have hp : getClassModule c.module ++ c.dtQualname = c.dtTpName := by
    rcases hc with rfl | ⟨mod, name, rfl, hm⟩
    · rfl
    · simp [getClassModule, hm, ReprCls.module, ReprCls.dtQualname, ReprCls.dtTpName]
  rw [hp]
  rcases hf with h0 | h0
  · simp [appendFold, h0]
  · simp [appendTzinfo, h0]

/-- `repr(datetime)` agrees between the twins for every valid datetime, a fold of 1 with a
tzinfo included. -/
def DatetimeReprFoldTzTwins : Prop :=
  ∀ (env : TzEnv) (dt : DT), dt.Valid → dtReprClsPy env .base dt = dtReprClsC env .base dt

/-- `repr(datetime(2020, 1, 1, fold=1, tzinfo=timezone.utc))`: Python appends the tzinfo then
the fold, `...tzinfo=datetime.timezone.utc, fold=1)`; C the fold then the tzinfo,
`...fold=1, tzinfo=datetime.timezone.utc)`. -/
theorem datetimeReprFoldTzTwins_refuted : ¬DatetimeReprFoldTzTwins := by
  intro h
  have := h emptyEnv ⟨2020, 1, 1, 0, 0, 0, 0, 1, some tzUTC⟩
    (by refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, Or.inr rfl, ?_⟩; simp [OptTzOk, Tz.Ok, tzUTC, Delta.Valid, MAX_DELTA_DAYS, Delta.toUs])
  revert this
  decide +kernel

end PyLean.Datetime
