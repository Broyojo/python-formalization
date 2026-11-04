import PyLean.Datetime.ArgCheck
import PyLean.Datetime.Twins2Props
import PyLean.Datetime.DtProps
import PyLean.Datetime.FmtTwinsProps

/-!
Properties of the argument checks in `ArgCheck`: each check is mirrored in both twins and
stated on every argument, with the branch behind it pinned by the existing theorems.
-/

namespace PyLean.Datetime
open PyLean

/-! ### `timezone.utcoffset`, `tzname`, `dst`, `fromutc` -/

/-- The `timezone` methods on every argument, for every valid `timezone`: an argument that is
neither a `datetime` nor `None` is a `TypeError` in both twins (before anything else); otherwise
`utcoffset` is the offset, `dst` is `None` and `tzname` the name (or `UTC±HH:MM...` from the
offset), the same in both twins. `fromutc` refuses `None` and other objects with `TypeError` in
both, and on a valid `datetime` agrees between the twins (`TimezoneFromutc`). -/
def TimezoneMethodArgs : Prop :=
  ∀ (tz : Tz) (off : Delta) (name : Option String) (a : TzMethArg), tz.kind = .timezone off name → tz.Ok →
    SameOutcome (timezoneUtcoffsetArgPy off a) (timezoneUtcoffsetArgC off a) ∧
    SameOutcome (timezoneTznameArgPy off name a) (timezoneTznameArgC tz.oid off name a) ∧
    SameOutcome (timezoneDstArgPy a) (timezoneDstArgC a) ∧
    (a = .other → (timezoneUtcoffsetArgPy off a).raises "TypeError" ∧
      (timezoneTznameArgPy off name a).raises "TypeError" ∧ (timezoneDstArgPy a).raises "TypeError") ∧
    (a ≠ .other → timezoneUtcoffsetArgPy off a = .ok off ∧ timezoneDstArgPy a = .ok none ∧
      timezoneTznameArgPy off name a = .ok (timezoneStrPy off name)) ∧
    ((∀ d, a = .dt d → d.Valid) → SameOutcome (timezoneFromutcArgPy tz off a) (timezoneFromutcArgC tz off a)) ∧
    (a = .none_ ∨ a = .other → (timezoneFromutcArgPy tz off a).raises "TypeError" ∧
      (timezoneFromutcArgC tz off a).raises "TypeError")

theorem timezoneMethodArgs_proven : TimezoneMethodArgs := by
  intro tz off name a hk hok
  have hname := timezoneName_proven tz off name hk hok
  have hoff : off.Valid := by
    have h := hok; unfold Tz.Ok at h; rw [hk] at h; exact h.1
  refine ⟨?_, ?_, ?_, fun h => ?_, fun h => ?_, fun hv => ?_, fun h => ?_⟩
  · cases a <;> simp [timezoneUtcoffsetArgPy, timezoneUtcoffsetArgC, timezoneCheckArg, TzMethArg.ok,
      SameOutcome, bind, Except.bind, pure, Except.pure, PyExc.className]
  · cases a with
    | other => simp [timezoneTznameArgPy, timezoneTznameArgC, timezoneCheckArg, TzMethArg.ok, SameOutcome,
        PyExc.className, bind, Except.bind]
    | dt d => show SameOutcome (.ok _) (.ok _); simp only [SameOutcome]; rw [← hname]; cases name <;> rfl
    | none_ => show SameOutcome (.ok _) (.ok _); simp only [SameOutcome]; rw [← hname]; cases name <;> rfl
  · cases a <;> simp [timezoneDstArgPy, timezoneDstArgC, timezoneCheckArg, TzMethArg.ok,
      SameOutcome, bind, Except.bind, pure, Except.pure, PyExc.className]
  · subst h; exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩
  · cases a with
    | other => exact absurd rfl h
    | dt d => exact ⟨rfl, rfl, by cases name <;> rfl⟩
    | none_ => exact ⟨rfl, rfl, by cases name <;> rfl⟩
  · cases a with
    | dt d => exact timezoneFromutc_proven tz off d hoff (hv d rfl)
    | none_ => simp [timezoneFromutcArgPy, timezoneFromutcArgC, SameOutcome, PyExc.className]
    | other => simp [timezoneFromutcArgPy, timezoneFromutcArgC, SameOutcome, PyExc.className]
  · rcases h with rfl | rfl <;> exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

/-! ### `timezone(offset, name)` -/

/-- `timezone(offset, name)` on every `offset` object and `name`: an `offset` that is not a
`timedelta` is a `TypeError` in both twins whatever the name (it is checked first); a
`timedelta` goes on to the name and range checks, where the twins agree (`TimezoneNew`). -/
def TimezoneNewArg : Prop :=
  ∀ (oid : Nat) (offset : Option Delta) (name : TzName), (∀ o, offset = some o → o.Valid) →
    SameOutcome (timezoneNewArgPy oid offset name) (timezoneNewArgC oid offset name) ∧
    (offset = none → (timezoneNewArgPy oid offset name).raises "TypeError" ∧
      (timezoneNewArgC oid offset name).raises "TypeError")

theorem timezoneNewArg_proven : TimezoneNewArg := by
  intro oid offset name hv
  cases offset with
  | none => exact ⟨by simp [timezoneNewArgPy, timezoneNewArgC, SameOutcome, PyExc.className],
      fun _ => ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩⟩
  | some o => exact ⟨(timezoneNew_proven oid o name (hv o rfl)).1, fun h => by cases h⟩

/-! ### `timezone.__getinitargs__` and `__hash__` -/

/-- `timezone.__getinitargs__()` for every valid `timezone`: the twins return the same
arguments, the one-tuple `(offset,)` exactly when there is no name; and `timezone(*args)` (what
unpickling runs, through `tzinfo.__reduce__`) rebuilds a timezone with the same offset and name,
the `timezone.utc` singleton itself for `timezone.utc`. -/
def TimezoneGetinitargs : Prop :=
  ∀ (tz : Tz) (off : Delta) (name : Option String) (oid' : Nat), tz.kind = .timezone off name → tz.Ok →
    timezoneGetinitargsPy off name = timezoneGetinitargsC off name ∧
    (name = none → timezoneGetinitargsPy off name = .one off) ∧
    (∀ n, name = some n → timezoneGetinitargsPy off name = .two off n) ∧
    ∃ tz', timezoneFromInitargsPy oid' (timezoneGetinitargsPy off name) = .ok tz' ∧ tz'.kind = tz.kind ∧
      (tz.oid = 0 → tz' = tzUTC)

theorem timezoneGetinitargs_proven : TimezoneGetinitargs := by
  intro tz off name oid' hk hok
  have h := hok; unfold Tz.Ok at h; rw [hk] at h
  obtain ⟨hv, h1, h2, hu⟩ := h
  have hb := (timedeltaBoolHash_proven off off hv hv).1
  have hr := timezoneRange_proven off hv
  obtain ⟨o, ho⟩ := hr.1.mpr ⟨h1, h2⟩
  refine ⟨by cases name <;> rfl, fun h => by subst h; rfl, fun n h => by subst h; rfl, ?_⟩
  cases name with
  | none =>
    simp only [timezoneGetinitargsPy, timezoneFromInitargsPy, timezoneNewPy]
    by_cases hz : off.bool = true
    · simp only [hz, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ho]
      refine ⟨_, rfl, by rw [hk], fun h0 => ?_⟩
      have := (hu h0).1; subst this; simp [Delta.bool] at hz
    · have h0 : off.toUs = 0 := by
        by_cases hne : off.toUs = 0
        · exact hne
        · exact absurd (hb.mpr hne) hz
      have hoff : off = ⟨0, 0, 0⟩ := by
        obtain ⟨dd, ss, uu⟩ := off
        unfold Delta.Valid MAX_DELTA_DAYS at hv
        unfold Delta.toUs at h0
        simp only [Delta.mk.injEq] at hv h0 ⊢
        omega
      simp only [hz, Bool.not_false, ↓reduceIte]
      refine ⟨_, rfl, by rw [hk, hoff]; rfl, fun _ => rfl⟩
  | some n =>
    simp only [timezoneGetinitargsPy, timezoneFromInitargsPy, timezoneNewPy, ho]
    refine ⟨_, rfl, by rw [hk], fun h0 => ?_⟩
    have := (hu h0).2; cases this

/-- `hash(tz)` for every `timezone`: the twins hash the same key, the key of the offset, so
`hash(tz) == hash(tz.utcoffset(None))`, and two timezones hash alike exactly when their offsets
do (names play no part, as in `==`). -/
def TimezoneHash : Prop :=
  ∀ (off off2 : Delta), off.Valid → off2.Valid →
    timezoneHashKey off = timezoneHashKeyC off ∧ timezoneHashKey off = off.hashKey ∧
    (timezoneHashKey off = timezoneHashKey off2 ↔ off.toUs = off2.toUs)

theorem timezoneHash_proven : TimezoneHash := by
  intro off off2 h1 h2
  exact ⟨rfl, rfl, (timedeltaBoolHash_proven off off2 h1 h2).2.1⟩

/-! ### `datetime.combine` -/

/-- `datetime.combine(date, time, tzinfo)` on every argument: a `date` argument that is not a
`date` (or `datetime`) is a `TypeError` in both twins, checked first; then a `time` argument
that is not a `time`; for a valid date and time and a `tzinfo` omitted or given (not `True`),
both twins give exactly the datetime of the date's and time's fields with the time's fold and
the time's tzinfo when omitted (the given one otherwise, after the tzinfo type check). -/
def CombineArgs : Prop :=
  ∀ (d : DateObj) (t : TimeObj) (tz : TzParam),
    (d = .other → (dtCombineArgPy d t tz).raises "TypeError" ∧ (dtCombineArgC d t tz).raises "TypeError") ∧
    (∀ y m dd, d = .date y m dd → t = .other →
      (dtCombineArgPy d t tz).raises "TypeError" ∧ (dtCombineArgC d t tz).raises "TypeError") ∧
    (∀ y m dd (tm : TM), d = .date y m dd → t = .time tm → ValidDate y m dd → tm.Valid → tz ≠ .true_ →
      let r : Py DT := do
        let z ← checkTzinfoArgPy (tzParamPy tm.tz tz)
        return ⟨y, m, dd, tm.h, tm.mi, tm.s, tm.us, tm.fold, z⟩
      dtCombineArgPy d t tz = r ∧ dtCombineArgC d t tz = r)

theorem combineArgs_proven : CombineArgs := by
  intro d t tz
  refine ⟨fun h => by subst h; exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩,
    fun y m dd hd ht => by subst hd; subst ht; exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩,
    fun y m dd tm hd ht hvd hvt hnt => ?_⟩
  subst hd; subst ht
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, _⟩ := hvt
  have hcd := checkDate_ok y m dd hvd
  have hct := checkTime_ok tm.h tm.mi tm.s tm.us ⟨a1, a2⟩ ⟨a3, a4⟩ ⟨a5, a6⟩ ⟨a7, a8⟩
  have hcf := checkFold_ok tm.fold a9
  have htz : tzParamC tm.tz tz = tzParamPy tm.tz tz := by
    cases tz with
    | omitted => rfl
    | true_ => exact absurd rfl hnt
    | obj a => rfl
  refine ⟨?_, ?_⟩
  · simp only [dtCombineArgPy, datetimeNewPy, stateOf, checkDateFieldsArgPy, checkTimeFieldsArgPy,
      pyIndex, checkFoldArgPy, Arg.foldVal, bind, Except.bind, hcd, hct, hcf, pure, Except.pure]
  · simp only [dtCombineArgC, datetimeDatetimeImplC, bind, Except.bind, hcd, hct, hcf, htz,
      checkTzinfo_twin]

/-- `datetime.combine` agrees between the twins for every valid date and time and every
`tzinfo` argument. -/
def CombineTwins : Prop :=
  ∀ (y m dd : Int) (tm : TM) (tz : TzParam), ValidDate y m dd → tm.Valid →
    SameOutcome (dtCombineArgPy (.date y m dd) (.time tm) tz) (dtCombineArgC (.date y m dd) (.time tm) tz)

/-- `datetime.combine(date(2020, 1, 1), time(1, tzinfo=timezone.utc), tzinfo=True)`: Python's
`if tzinfo is True` keeps the time's tzinfo, C passes `True` on and `check_tzinfo_subclass`
raises `TypeError`. -/
theorem combineTwins_refuted : ¬CombineTwins := by
  intro h
  have := h 2020 1 1 ⟨1, 0, 0, 0, 0, some tzUTC⟩ .true_ (by decide)
    (by refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      Or.inl rfl, ?_⟩; simp [OptTzOk, Tz.Ok, tzUTC, Delta.Valid, MAX_DELTA_DAYS, Delta.toUs])
  exact this

/-! ### `datetime.astimezone` -/

/-- `datetime.astimezone(tz)` with a `tz` that is neither `None` nor a `tzinfo`: a `TypeError`
in both twins for every datetime and tzinfo environment, so before any `tzinfo` method or the
local time zone is consulted; `None` and a `tzinfo` take the paths of `dtAstimezonePy` and
`dtAstimezoneC`. -/
def AstimezoneArg : Prop :=
  ∀ (env : TzEnv) (self : DT),
    (dtAstimezoneArgPy env self .other).raises "TypeError" ∧ (dtAstimezoneArgC env self .other).raises "TypeError" ∧
    (∀ t, dtAstimezoneArgPy env self (.tz t) = dtAstimezonePy env self t ∧
      dtAstimezoneArgC env self (.tz t) = dtAstimezoneC env self t)

theorem astimezoneArg_proven : AstimezoneArg :=
  fun _ _ => ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩

/-! ### `time.__format__` -/

/-- `format(t, fmt)` for every `fmt` and every result of the `str` and `strftime` methods: the
twins agree (a non-`str` is a `TypeError` in both, with different messages); `''` gives
`str(t)` and a nonempty format `t.strftime(fmt)`, whatever those methods return or raise. -/
def TimeFormat : Prop :=
  ∀ {α : Type} (fmt : FmtArg) (str : Py String) (strftime : List Char → Py α),
    SameOutcome (timeFormatPy fmt str strftime) (timeFormatC fmt str strftime) ∧
    (timeFormatPy .other str strftime).raises "TypeError" ∧
    timeFormatPy (.str []) str strftime = Sum.inl <$> str ∧
    (∀ cs, cs ≠ [] → timeFormatPy (.str cs) str strftime = Sum.inr <$> strftime cs)

theorem timeFormat_proven : TimeFormat := by
  intro α fmt str strftime
  refine ⟨?_, ⟨_, rfl, rfl⟩, rfl, fun cs h => ?_⟩
  · cases fmt with
    | other => simp [timeFormatPy, timeFormatC, SameOutcome, PyExc.className]
    | str cs =>
      simp only [timeFormatPy, timeFormatC]
      by_cases h : cs.length = 0
      · rw [if_neg (by omega), if_pos h]; exact sameOutcome_refl _
      · rw [if_pos h, if_neg h]; exact sameOutcome_refl _
  · simp only [timeFormatPy]
    rw [if_pos (by cases cs <;> simp_all)]

/-! ### `fromisoformat` -/

/-- `time.fromisoformat` and `datetime.fromisoformat` on every argument: a non-`str` is a
`TypeError` in both twins, a `str` with a lone surrogate a `ValueError` in both, and a `str`
goes to the parser of each twin. -/
def FromisoArg : Prop :=
  (timeFromIsoArgPy .other).raises "TypeError" ∧ (timeFromIsoArgC .other).raises "TypeError" ∧
  (datetimeFromIsoArgPy .other).raises "TypeError" ∧ (datetimeFromIsoArgC .other).raises "TypeError" ∧
  (timeFromIsoArgPy .surrogateStr).raises "ValueError" ∧ (timeFromIsoArgC .surrogateStr).raises "ValueError" ∧
  (datetimeFromIsoArgPy .surrogateStr).raises "ValueError" ∧
  (datetimeFromIsoArgC .surrogateStr).raises "ValueError" ∧
  ∀ s, timeFromIsoArgPy (.str s) = timeFromIsoPy s ∧ timeFromIsoArgC (.str s) = timeFromIsoC s ∧
    datetimeFromIsoArgPy (.str s) = datetimeFromIsoPy s ∧ datetimeFromIsoArgC (.str s) = datetimeFromIsoC s

theorem fromisoArg_proven : FromisoArg :=
  ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩,
    ⟨_, rfl, rfl⟩, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-- `time.fromisoformat(s)` (Py:1645-1670) on every string, by what `_parse_isoformat_time`
returns for `s` without a leading `T`: a `ValueError` of the parser becomes
`Invalid isoformat string`, another exception propagates; an `error_from_tz` is raised as it is;
`error_from_components` (hour 24 with other fields) is
`Minute, second, and microsecond must be 0 when hour is 24`; otherwise the time of the parsed
fields and offset, checked by the constructor. -/
def TimeFromIsoBody : Prop :=
  ∀ (s : List Char) (t : TimeV) (nd : Bool) (e : PyExc) (m : String),
    (parseIsoTimePy (removePrefixT s) = .error (.valueError m) →
      timeFromIsoPy s = .error (.valueError "~Invalid isoformat string")) ∧
    (parseIsoTimePy (removePrefixT s) = .error e → e.className ≠ "ValueError" → timeFromIsoPy s = .error e) ∧
    (∀ ec, parseIsoTimePy (removePrefixT s) = .ok (t, nd, ec, some e) → timeFromIsoPy s = .error e) ∧
    (parseIsoTimePy (removePrefixT s) = .ok (t, nd, true, none) →
      timeFromIsoPy s = .error (.valueError "Minute, second, and microsecond must be 0 when hour is 24")) ∧
    (parseIsoTimePy (removePrefixT s) = .ok (t, nd, false, none) →
      timeFromIsoPy s = (do let _ ← checkTime t.h t.mi t.s t.us; return t))

theorem timeFromIsoBody_proven : TimeFromIsoBody := by
  intro s t nd e m
  refine ⟨fun h => ?_, fun h hc => ?_, fun ec h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    simp only [timeFromIsoPy, h, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw, ↓reduceIte, Bool.false_eq_true]
  · cases e <;> simp_all [PyExc.className]

end PyLean.Datetime
