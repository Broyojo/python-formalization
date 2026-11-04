import PyLean.Datetime.FmtTwinsProps
import PyLean.Datetime.Refute2

/-!
`get_tzinfo_member` (Modules/_datetimemodule.c:1505-1515) and the `%z`, `%:z` and `%Z`
replacements built on it (`make_somezreplacement`, :1799-1817; `make_Zreplacement`,
:1820-1860), against `_wrap_strftime`'s `object.utcoffset()` and `object.tzname()`
(Lib/_pydatetime.py:240-247, :252-259, :264-272), CPython 3.15.2.

C reads the `tzinfo` member of the struct and calls the tzinfo's methods directly; Python
calls the object's own `utcoffset` and `tzname` methods, which a subclass may override.
-/

namespace PyLean.Datetime

open PyLean

/-! ### `get_tzinfo_member` over every struct -/

/-- `make_somezreplacement` and `make_Zreplacement` on every struct `get_tzinfo_member` may
see, by its dispatch: an object that is neither a `datetime` nor a `time`, one whose
`hastzinfo` byte is 0, or one whose member is `Py_None` gives `""` for `%z`, `%:z` and `%Z`
without calling anything; a `datetime` or `time` with `hastzinfo` set and a `tzinfo` member
calls that tzinfo's `utcoffset(tzinfoarg)` (checked by `call_tzinfo_method`) and formats it
with `format_utcoffset`, and its `tzname(tzinfoarg)` (checked by `call_tzname`) with `%`
doubled. Its errors propagate. -/
def TzinfoMemberReplacements : Prop :=
  ∀ (env : TzEnv) (sep : List Char) (arg : Option DT) (o : TzMemberView),
    (((o.isDatetime || o.isTime) && o.hastzinfo) = false ∨ o.tzinfo = none →
      makeSomezreplacementViewC env sep o arg = .ok [] ∧ makeZreplacementViewC env o arg = .ok []) ∧
    (∀ tz : Tz, (o.isDatetime || o.isTime) = true → o.hastzinfo = true → o.tzinfo = some tz →
      makeSomezreplacementViewC env sep o arg =
        (do return formatUtcoffsetC sep (← callTzinfoCheckC "utcoffset" (← tzUtcoffsetRaw env tz arg))) ∧
      makeZreplacementViewC env o arg =
        (do
          match ← callTznameCheckC (← tzTznameRawC env tz arg) with
          | none => return []
          | some s => return escapePercent s.toList))

theorem member_none (o : TzMemberView)
    (h : ((o.isDatetime || o.isTime) && o.hastzinfo) = false ∨ o.tzinfo = none) :
    getTzinfoMemberC o = none ∨ getTzinfoMemberC o = some none := by
  obtain ⟨a, b, c, t⟩ := o
  unfold getTzinfoMemberC
  cases a <;> cases b <;> cases c <;> simp_all

theorem member_some (o : TzMemberView) (tz : Tz) (h1 : (o.isDatetime || o.isTime) = true)
    (h2 : o.hastzinfo = true) (h3 : o.tzinfo = some tz) : getTzinfoMemberC o = some (some tz) := by
  obtain ⟨a, b, c, t⟩ := o
  simp only at h1 h2 h3
  subst h2 h3
  unfold getTzinfoMemberC
  cases a <;> cases b <;> simp_all

theorem tzinfoMemberReplacements_proven : TzinfoMemberReplacements := by
  intro env sep arg o
  refine ⟨fun h => ?_, fun tz h1 h2 h3 => ?_⟩
  · rcases member_none o h with e | e <;> simp [makeSomezreplacementViewC, makeZreplacementViewC, e]
  · have e := member_some o tz h1 h2 h3
    refine ⟨?_, ?_⟩ <;> simp only [makeSomezreplacementViewC, makeZreplacementViewC, e] <;> rfl

/-! ### The `%z` and `%Z` twins for the inherited methods -/

/-- The tzinfo invariant of the object `strftime` runs on. -/
def StrfObj.TzOk : StrfObj → Prop
  | .date => True
  | .time t => OptTzOk t.tz
  | .dt d => OptTzOk d.tz

theorem fmt_twin_raw (sep : List Char) (r : Py OffRet) (hr : ∀ d, r = .ok (.delta d) → d.Valid) :
    (do return formatUtcoffsetC sep (← callTzinfoCheckC "utcoffset" (← r)) : Py (List Char)) =
      (do return formatOffsetSep sep ((← checkUtcOffset "utcoffset" (← r)).map Delta.toUs)) := by
  cases r with
  | error e => rfl
  | ok v =>
    have hv : ∀ d, v = .delta d → d.Valid := fun d h => hr d (by rw [h])
    simp only [bind, Except.bind]
    rw [← check_twin "utcoffset" v hv]
    cases hc : checkUtcOffset "utcoffset" v with
    | error e => rfl
    | ok w =>
      cases w with
      | none => rfl
      | some o =>
        have hrange := checked_range _ _ _ hc
        have ho : v = .delta o := by
          cases v with
          | none => simp [checkUtcOffset] at hc
          | other ty => simp [checkUtcOffset] at hc
          | delta d =>
            simp only [checkUtcOffset] at hc
            split at hc
            · cases hc
            · cases hc; rfl
        have hov := hv o ho
        have := (formatOffsetText_proven sep (some o) (fun t ht => by
          cases ht; exact ⟨hov, hrange⟩)).2
        simp only [pure, Except.pure, Option.map] at this ⊢
        rw [this]

theorem name_twin (env : TzEnv) (tz : Tz) (htz : tz.Ok) (arg : Option DT) :
    SameOutcome
      (do
        match ← callTznameCheckC (← tzTznameRawC env tz arg) with
        | none => return ([] : List Char)
        | some s => return escapePercent s.toList)
      (do
        match ← checkTzname (← tzTznameRawPy env tz arg) with
        | none => return []
        | some s => return escapePercent s.toList) := by
  unfold tzTznameRawC tzTznameRawPy
  cases hk : tz.kind with
  | timezone off name =>
    have e := timezoneName_proven tz off name hk htz
    simp [e, callTznameCheckC, checkTzname, bind, Except.bind, pure, Except.pure, SameOutcome]
  | custom i =>
    rcases hr : env.tzname i arg with e | r
    · simp [hr, bind, Except.bind, SameOutcome]
    · cases r <;> simp [hr, callTznameCheckC, checkTzname, bind, Except.bind, pure, Except.pure, SameOutcome,
        PyExc.className]

/-- `strftime`'s `%z`/`%:z` and `%Z` replacements agree between the twins for every object
of the three classes whose `utcoffset` and `tzname` are the inherited ones, every separator,
and every `tzinfo` (a `timezone` or a subclass of `tzinfo`): `%z` gives the same text or the
same exception, `%Z` the same text or an exception of the same class (the TypeError for a
non-string `tzname()` differs in one word). A `date` has neither method in Python and no
`tzinfo` member in C, so both give `""`. -/
def StrftimeZTwins : Prop :=
  ∀ (env : TzEnv) (sep : List Char) (obj : StrfObj), env.Valid → obj.TzOk →
    makeSomezreplacementC env sep obj = obj.zreplacePy env sep ∧
    SameOutcome (makeZreplacementC env obj) (obj.ZreplacePy env)

theorem strftimeZTwins_proven : StrftimeZTwins := by
  intro env sep obj henv hok
  cases obj with
  | date => exact ⟨rfl, rfl⟩
  | time t =>
    simp only [StrfObj.TzOk] at hok
    cases ht : t.tz with
    | none =>
      simp [makeSomezreplacementC, makeSomezreplacementViewC, makeZreplacementC, makeZreplacementViewC,
        StrfObj.cView, StrfObj.tzinfoArg, getTzinfoMemberC, ht, StrfObj.zreplacePy, StrfObj.ZreplacePy,
        TM.utcoffsetPy, TM.tznamePy, formatOffsetSep, bind, Except.bind, pure, Except.pure, SameOutcome]
    | some tz =>
      rw [ht] at hok
      have hm : getTzinfoMemberC (StrfObj.time t).cView = some (some tz) := by
        simp [getTzinfoMemberC, StrfObj.cView, ht]
      refine ⟨?_, ?_⟩
      · simp only [makeSomezreplacementC, makeSomezreplacementViewC, hm, StrfObj.tzinfoArg,
          StrfObj.zreplacePy, TM.utcoffsetPy, ht]
        rw [fmt_twin_raw sep _ (fun d hd => raw_off_valid env henv tz hok none d hd)]
        cases tzUtcoffsetRaw env tz none <;> rfl
      · have := name_twin env tz hok none
        simp only [makeZreplacementC, makeZreplacementViewC, hm, StrfObj.tzinfoArg, StrfObj.ZreplacePy,
          TM.tznamePy, ht]
        revert this
        cases tzTznameRawPy env tz none <;> cases tzTznameRawC env tz none <;> exact id
  | dt d =>
    simp only [StrfObj.TzOk] at hok
    cases ht : d.tz with
    | none =>
      simp [makeSomezreplacementC, makeSomezreplacementViewC, makeZreplacementC, makeZreplacementViewC,
        StrfObj.cView, StrfObj.tzinfoArg, getTzinfoMemberC, ht, StrfObj.zreplacePy, StrfObj.ZreplacePy,
        DT.utcoffsetPy, DT.tznamePy, formatOffsetSep, bind, Except.bind, pure, Except.pure, SameOutcome]
    | some tz =>
      rw [ht] at hok
      have hm : getTzinfoMemberC (StrfObj.dt d).cView = some (some tz) := by
        simp [getTzinfoMemberC, StrfObj.cView, ht]
      refine ⟨?_, ?_⟩
      · simp only [makeSomezreplacementC, makeSomezreplacementViewC, hm, StrfObj.tzinfoArg,
          StrfObj.zreplacePy, DT.utcoffsetPy, ht]
        rw [fmt_twin_raw sep _ (fun e he => raw_off_valid env henv tz hok (some d) e he)]
        cases tzUtcoffsetRaw env tz (some d) <;> rfl
      · have := name_twin env tz hok (some d)
        simp only [makeZreplacementC, makeZreplacementViewC, hm, StrfObj.tzinfoArg, StrfObj.ZreplacePy,
          DT.tznamePy, ht]
        revert this
        cases tzTznameRawPy env tz (some d) <;> cases tzTznameRawC env tz (some d) <;> exact id

/-! ### A subclass that overrides `utcoffset` or `tzname` -/

/-- The object `_wrap_strftime` runs on, with the `utcoffset()` and `tzname()` its class
defines: `none` keeps the inherited method (for a `date`: no attribute at all), `some r` is an
override and what calling it returns (an offset or `None`, or an exception). The struct is
what C reads. -/
structure StrfSubj where
  obj : StrfObj
  utcoffsetOv : Option (Py (Option Delta)) := none
  tznameOv : Option (Py (Option String)) := none

/-- `_wrap_strftime`'s `%z`/`%:z` replacement, Py:240-247 and :252-259:
`_format_offset(object.utcoffset(), sep)` when `hasattr(object, "utcoffset")`, else `""`. -/
def StrfSubj.zreplacePy (env : TzEnv) (sep : List Char) (o : StrfSubj) : Py (List Char) :=
  match o.utcoffsetOv with
  | some m => do return formatOffsetSep sep ((← m).map Delta.toUs)
  | none => o.obj.zreplacePy env sep

/-- `_wrap_strftime`'s `%Z` replacement, Py:264-272: `object.tzname()` when the attribute
exists, `""` for `None`, `%` doubled. -/
def StrfSubj.ZreplacePy (env : TzEnv) (o : StrfSubj) : Py (List Char) :=
  match o.tznameOv with
  | some m => do
    match ← m with
    | none => return []
    | some s => return escapePercent s.toList
  | none => o.obj.ZreplacePy env

/-- The broad twin: `%z` agrees between the twins for every object, a subclass that overrides
`utcoffset()` included. -/
def StrftimeZOverrideTwins : Prop :=
  ∀ (env : TzEnv) (sep : List Char) (o : StrfSubj), env.Valid → o.obj.TzOk →
    makeSomezreplacementC env sep o.obj = o.zreplacePy env sep

/-- `class D(datetime)` with `def utcoffset(self): return timedelta(hours=5)`:
`D(2000, 1, 1).strftime('%z')` is `'+0500'` in Python (the override is called) and `''` in C
(the struct has no tzinfo member, so the override is never consulted). -/
theorem strftimeZOverrideTwins_refuted : ¬ StrftimeZOverrideTwins := by
  intro h
  have h1 := h emptyEnv [] ⟨.dt ⟨2000, 1, 1, 0, 0, 0, 0, 0, none⟩, some (.ok (some ⟨0, 18000, 0⟩)), none⟩
    emptyEnv_valid (by simp [StrfObj.TzOk, OptTzOk])
  revert h1
  decide

/-- The values of that call in each twin. -/
theorem strftimeZOverride_example :
    makeSomezreplacementC emptyEnv [] (.dt ⟨2000, 1, 1, 0, 0, 0, 0, 0, none⟩) = .ok [] ∧
    StrfSubj.zreplacePy emptyEnv []
      ⟨.dt ⟨2000, 1, 1, 0, 0, 0, 0, 0, none⟩, some (.ok (some ⟨0, 18000, 0⟩)), none⟩ = .ok "+0500".toList := by
  decide

end PyLean.Datetime
