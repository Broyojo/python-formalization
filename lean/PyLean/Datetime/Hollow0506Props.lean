import PyLean.Datetime.AstzProps

/-!
Rows the review 0506b7c0 found hollow, part 1: the `str` pickle state of `time(...)` and
`datetime(...)` on its success path, the timezone range error of `strptime` with `%z`, and the
`24:00` rollover of `datetime.fromisoformat` when its guard is false or the year overflows.
-/

namespace PyLean.Datetime
open PyLean

/-! ### `time(state)` and `datetime(state)` with a `str` state -/

theorem latin1_ok (kind : String) (cs : List Nat) (hb : ∀ x ∈ cs, x < 256) :
    latin1State kind cs = .ok cs := by
  have hany : cs.any (· > 255) = false := by
    rw [List.any_eq_false]; intro x hx; have := hb x hx; simp only [decide_eq_true_eq]; omega
  simp [latin1State, hany]

/-- `time(state, tzinfo)` with a `str` state, as unpickling a Python 2 pickle with
`encoding='latin1'` gives it: when the state passes the header test (six characters,
`ord(state[0]) & 0x7F < 24`, Py:1446-1447) and every character is at most U+00FF,
`state.encode('latin1')` succeeds (:1449-1451) and both twins build exactly the time the same
six bytes give: hour from the low seven bits of the first character, fold from its top bit,
minute, second and the 24-bit microsecond, with the tzinfo argument kept (`None` or a tzinfo).
A character above U+00FF is the latin-1 `ValueError` in both (`TimeNewPickle`). -/
def TimeNewStrState : Prop :=
  ∀ (cs : List Nat) (z : Option Tz),
    cs.length = 6 → cs.getD 0 0 % 128 < 24 → (∀ x ∈ cs, x < 256) →
      let v : TM := ⟨(cs.getD 0 0 % 128 : Nat), (cs.getD 1 0 : Nat), (cs.getD 2 0 : Nat),
        ((cs.getD 3 0 * 256 + cs.getD 4 0) * 256 + cs.getD 5 0 : Nat), if cs.getD 0 0 ≥ 128 then 1 else 0, z⟩
      timeCallPy [.str cs, tzArg z] (.int 0) = .ok v ∧ timeNewC [.str cs, tzArg z] (.int 0) = .ok v ∧
      timeCallPy [.str cs, tzArg z] (.int 0) = timeCallPy [.bytes cs, tzArg z] (.int 0) ∧
      timeNewC [.str cs, tzArg z] (.int 0) = timeNewC [.bytes cs, tzArg z] (.int 0)

theorem timeNewStrState_proven : TimeNewStrState := by
  intro cs z hl hh hb
  have hlat := latin1_ok "time" cs hb
  match cs, hl with
  | [b0, b1, b2, b3, b4, b5], _ =>
    have hd := tmSetstate_decode [b0, b1, b2, b3, b4, b5] z rfl hb
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hh hd ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases z <;> simp [timeCallPy, timeNewPy, stateOf, hlat, hh, tzArg, Arg.falsy, stateTz, hd, bind,
        Except.bind, pure, Except.pure]
    · cases z <;> simp [timeNewC, stateOf, hlat, hh, tzArg, stateTz, hd, bind, Except.bind, pure, Except.pure]
    · cases z <;> simp [timeCallPy, timeNewPy, stateOf, hlat, hh, tzArg, Arg.falsy, stateTz, hd, bind,
        Except.bind, pure, Except.pure]
    · cases z <;> simp [timeNewC, stateOf, hlat, hh, tzArg, stateTz, hd, bind, Except.bind, pure, Except.pure]

/-- `datetime(state, tzinfo)` with a `str` state: when it passes the header test (ten
characters, `1 <= ord(state[2]) & 0x7F <= 12`, Py:1802-1803) and every character is at most
U+00FF, `bytes(state, 'latin1')` succeeds (:1805-1807) and both twins build exactly the
datetime of the same ten bytes, with year, month (low seven bits), fold (top bit), day, hour,
minute, second and microsecond, and the tzinfo argument kept. -/
def DatetimeNewStrState : Prop :=
  ∀ (cs : List Nat) (z : Option Tz),
    cs.length = 10 → 1 ≤ cs.getD 2 0 % 128 → cs.getD 2 0 % 128 ≤ 12 → (∀ x ∈ cs, x < 256) →
      let v : DT := ⟨(cs.getD 0 0 * 256 + cs.getD 1 0 : Nat), (cs.getD 2 0 % 128 : Nat), cs.getD 3 0,
        cs.getD 4 0, cs.getD 5 0, cs.getD 6 0, ((cs.getD 7 0 * 256 + cs.getD 8 0) * 256 + cs.getD 9 0 : Nat),
        if cs.getD 2 0 ≥ 128 then 1 else 0, z⟩
      datetimeCallPy [.str cs, tzArg z] (.int 0) = .ok v ∧ datetimeNewC [.str cs, tzArg z] (.int 0) = .ok v ∧
      datetimeCallPy [.str cs, tzArg z] (.int 0) = datetimeCallPy [.bytes cs, tzArg z] (.int 0) ∧
      datetimeNewC [.str cs, tzArg z] (.int 0) = datetimeNewC [.bytes cs, tzArg z] (.int 0)

theorem datetimeNewStrState_proven : DatetimeNewStrState := by
  intro cs z hl hh1 hh2 hb
  have hlat := latin1_ok "datetime" cs hb
  match cs, hl with
  | [y1, y2, m, d, h, mi, s, u1, u2, u3], _ =>
    have hm := hb m (by simp)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hh1 hh2 ⊢
    have hdec : dtSetstate z [y1, y2, m, d, h, mi, s, u1, u2, u3] =
        some ⟨(y1 * 256 + y2 : Nat), (m % 128 : Nat), d, h, mi, s, ((u1 * 256 + u2) * 256 + u3 : Nat),
          if m ≥ 128 then 1 else 0, z⟩ := by
      simp only [dtSetstate]
      by_cases hmm : m > 127
      · have hm' : m ≥ 128 := by omega
        simp only [hmm, hm', ↓reduceIte, Option.some.injEq, DT.mk.injEq, and_true, true_and]
        omega
      · have hm' : ¬ m ≥ 128 := by omega
        simp only [hmm, hm', ↓reduceIte, Option.some.injEq, DT.mk.injEq, and_true, true_and]
        omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases z <;> simp [datetimeCallPy, datetimeNewPy, stateOf, hlat, hh1, hh2, tzArg, stateTz, hdec, bind,
        Except.bind, pure, Except.pure]
    · cases z <;> simp [datetimeNewC, stateOf, hlat, hh1, hh2, tzArg, stateTz, hdec, bind, Except.bind, pure,
        Except.pure]
    · cases z <;> simp [datetimeCallPy, datetimeNewPy, stateOf, hlat, hh1, hh2, tzArg, stateTz, hdec, bind,
        Except.bind, pure, Except.pure]
    · cases z <;> simp [datetimeNewC, stateOf, hlat, hh1, hh2, tzArg, stateTz, hdec, bind, Except.bind, pure,
        Except.pure]

/-! ### `strptime` with an offset `_parse_tz` refuses -/

/-- `time.strptime` and `datetime.strptime` when the parse has a UTC offset that
`_parse_tz` (_strptime.py:822-827) refuses: its exception is the result of both, nothing is
returned; and the `%z` group (_strptime.py:375) accepts any two digits for the hours, so
`'+9900'` with `'%z'` parses (99 hours, :706-711) and both raise the `timezone` range
`ValueError` (`offset must be a timedelta strictly between ...`), whatever the locale. -/
def StrptimeOffsetRange : Prop :=
  (∀ (lt : LocaleTimeV) (found : StrpFound) (r : StrpResult) (g : Int) (e : PyExc),
    strptimeCore lt found = .ok r → r.gmtoff = some g → parseTz r.tzname g r.gmtoffFraction = .error e →
      strptimeDatetimeTime lt found = .error e ∧ strptimeDatetime lt found = .error e) ∧
  (∀ lt : LocaleTimeV,
    strptimeDatetimeTime lt [("z", some "+9900")] = .error (.valueError
      "~offset must be a timedelta strictly between -timedelta(hours=24) and timedelta(hours=24)") ∧
    strptimeDatetime lt [("z", some "+9900")] = .error (.valueError
      "~offset must be a timedelta strictly between -timedelta(hours=24) and timedelta(hours=24)"))

theorem strptimeOffsetRange_proven : StrptimeOffsetRange := by
  refine ⟨fun lt found r g e h hg hz => ?_, fun lt => ?_⟩
  · simp [strptimeDatetimeTime, strptimeDatetime, h, hg, hz, bind, Except.bind]
  · refine ⟨?_, ?_⟩
    · simp [strptimeDatetimeTime, strptimeCore, strpStep, foundGet, bind, Except.bind, pure, Except.pure]
      decide
    · simp [strptimeDatetime, strptimeCore, strpStep, foundGet, bind, Except.bind, pure, Except.pure]
      decide

/-! ### `datetime.fromisoformat`: the `24:00` rollover on every date -/

/-- `datetime.fromisoformat(s)` when the time part is `24:00` (`became_next_day`), on every
parsed date, valid or not: the result is the constructor applied to the rolled-over date
(:1998-2010); when the guard `1 <= month <= 12 and day <= _days_in_month(year, month)` (:2001)
is false the date is left as parsed and the constructor's `ValueError` for it is the result
(so `2021-02-29T24:00` stays invalid); on `9999-12-31` the rollover reaches year 10000, which
the constructor refuses; and on concrete strings: `2021-02-29T24:00` is
`day 29 must be in range 1..28 for month 2 in year 2021`, `2021-02-28T24:00` is
`2021-03-01 00:00`, and `9999-12-31T24:00` is `year must be in 1..9999, not 10000`. -/
def DatetimeFromIsoRollover : Prop :=
  (∀ (s : List Char) (sep : Nat) (y m d : Int) (t : TimeV),
    7 ≤ s.length → findSepPy s = .ok sep → parseIsoDatePy (s.take sep) = .ok (y, m, d) →
    s.drop (sep + 1) ≠ [] → parseIsoTimePy (s.drop (sep + 1)) = .ok (t, true, false, none) →
      datetimeFromIsoPy s =
        (do let r := rolloverPy y m d
            let _ ← checkDate r.1 r.2.1 r.2.2
            let _ ← checkTime t.h t.mi t.s t.us
            return ⟨r.1, r.2.1, r.2.2, t⟩) ∧
      (¬ (1 ≤ m ∧ m ≤ 12 ∧ d ≤ daysInMonth y m) →
        ∃ e, checkDate y m d = .error e ∧ datetimeFromIsoPy s = .error e) ∧
      (y = 9999 → m = 12 → d = 31 →
        datetimeFromIsoPy s = .error (.valueError "year must be in 1..9999, not 10000"))) ∧
  datetimeFromIsoPy "2021-02-29T24:00".toList =
    .error (.valueError "day 29 must be in range 1..28 for month 2 in year 2021") ∧
  datetimeFromIsoPy "2021-02-28T24:00".toList = .ok ⟨2021, 3, 1, ⟨0, 0, 0, 0, none⟩⟩ ∧
  datetimeFromIsoPy "9999-12-31T24:00".toList = .error (.valueError "year must be in 1..9999, not 10000")

theorem checkDate_err_of_not_guard (y m d : Int) (h : ¬ (1 ≤ m ∧ m ≤ 12 ∧ d ≤ daysInMonth y m)) :
    ∃ e, checkDate y m d = .error e := by
  unfold checkDate
  by_cases hy : MINYEAR ≤ y ∧ y ≤ MAXYEAR
  · by_cases hm : 1 ≤ m ∧ m ≤ 12
    · have hd : ¬ (1 ≤ d ∧ d ≤ daysInMonth y m) := by
        intro hd; exact h ⟨hm.1, hm.2, hd.2⟩
      simp [hy, hm, hd]
    · simp [hy, hm]
  · simp [hy]

theorem datetimeFromIsoRollover_proven : DatetimeFromIsoRollover := by
  refine ⟨fun s sep y m d t hl hs hd hne hp => ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  have hpre : ¬ s.length < 7 := by omega
  have hmain : datetimeFromIsoPy s =
      (do let r := rolloverPy y m d
          let _ ← checkDate r.1 r.2.1 r.2.2
          let _ ← checkTime t.h t.mi t.s t.us
          return ⟨r.1, r.2.1, r.2.2, t⟩) := by
    simp [datetimeFromIsoPy, hpre, hs, hd, hne, hp, bind, Except.bind, pure, Except.pure]
  refine ⟨hmain, fun hg => ?_, fun hy hm hd' => ?_⟩
  · have hr : rolloverPy y m d = (y, m, d) := by unfold rolloverPy; rw [if_neg hg]
    obtain ⟨e, he⟩ := checkDate_err_of_not_guard y m d hg
    refine ⟨e, he, ?_⟩
    rw [hmain, hr]
    simp [he, bind, Except.bind]
  · subst hy; subst hm; subst hd'
    have hr : rolloverPy 9999 12 31 = (10000, 1, 1) := by decide
    rw [hmain, hr]
    rfl

/-! ### `repr` with a tzinfo whose `__repr__` can fail -/

/-- What `repr(obj)` gets back from a `tzinfo` subclass's `__repr__`: a `str` (a subclass
included, whose text is used), or an object of another type, named as `type(x).__name__`. -/
inductive ReprRet where
  | str (s : String)
  | other (ty : String)
  deriving DecidableEq, Inhabited

/-- The `__repr__` of each `tzinfo` subclass in play (indexed like `TzEnv`): it may return any
object or raise. -/
abbrev TzReprEnv := Nat → Py ReprRet

/-- `PyObject_Repr(tz)` (Objects/object.c:760-798), which both `'%r' % tz` (Py:1619, :2214)
and C's `%R` (`append_keyword_tzinfo`, :1642) call: a `timezone` gives `timezone.__repr__`
(infallible); a subclass's method result is checked, a non-`str` being
`TypeError("%T.__repr__() must return a str, not %T")`, and its exception propagates. -/
def tzReprObj (renv : TzReprEnv) (tz : Tz) : Py String :=
  match tz.kind with
  | .timezone offset name => .ok (timezoneRepr tz.oid offset name)
  | .custom i =>
    match renv i with
    | .ok (.str s) => .ok s
    | .ok (.other ty) => .error (.typeError s!"~__repr__() must return a str, not {ty}")
    | .error e => .error e

/-- `s[:-1] + ", tzinfo=%r" % self._tzinfo + ")"` (Py:1617-1619, :2212-2214) and
`append_keyword_tzinfo` (:1628-1645) with a fallible `repr`. -/
def appendTzinfoF (renv : TzReprEnv) (s : String) (tz : Option Tz) : Py String :=
  match tz with
  | none => .ok s
  | some t => do
    let r ← tzReprObj renv t
    return (s.dropEnd 1).toString ++ s!", tzinfo={r})"

/-- `time.__repr__`, Py:1606-1623: the class prefix and fields, then `tzinfo=%r` (which may
raise), then `fold=1`. -/
def tmReprPyF (renv : TzReprEnv) (c : ReprCls) (t : TM) : Py String := do
  let s ← appendTzinfoF renv (tmReprBodyPy (getClassModule c.module ++ c.tmQualname) t) t.tz
  return appendFold s t.fold

/-- `time_repr`, :4852-4876: `tp_name` and fields, `append_keyword_tzinfo` (NULL on a failed
`%R`, :4872-4873), then `append_keyword_fold`. -/
def tmReprCF (renv : TzReprEnv) (c : ReprCls) (t : TM) : Py String := do
  let s ← appendTzinfoF renv (tmReprBodyC c.tmTpName t) t.tz
  return appendFold s t.fold

/-- `datetime.__repr__`, Py:2201-2218: tzinfo, then fold. -/
def dtReprPyF (renv : TzReprEnv) (c : ReprCls) (dt : DT) : Py String := do
  let s ← appendTzinfoF renv (dtReprBodyPy (getClassModule c.module ++ c.dtQualname) dt) dt.tz
  return appendFold s dt.fold

/-- `datetime_repr`, :6378-6413: fold (:6406-6407), then tzinfo (:6408-6410). -/
def dtReprCF (renv : TzReprEnv) (c : ReprCls) (dt : DT) : Py String :=
  appendTzinfoF renv (appendFold (dtReprBodyC c.dtTpName dt) dt.fold) dt.tz

/-- The `__repr__` table of a `TzEnv`, every method returning a `str`. -/
def TzEnv.reprEnv (env : TzEnv) : TzReprEnv := fun i => .ok (.str (env.repr i))

theorem tzReprObj_env (env : TzEnv) (t : Tz) : tzReprObj env.reprEnv t = .ok (t.repr env) := by
  unfold tzReprObj Tz.repr TzEnv.reprEnv
  cases t.kind <;> rfl

theorem appendTzinfoF_env (env : TzEnv) (s : String) (tz : Option Tz) :
    appendTzinfoF env.reprEnv s tz = .ok (appendTzinfo env s tz) := by
  cases tz with
  | none => rfl
  | some t => simp [appendTzinfoF, appendTzinfo, tzReprObj_env, bind, Except.bind, pure, Except.pure]

/-- `repr(time)` with a `tzinfo` whose `__repr__` may raise or return a non-`str`: the twins
agree on every outcome for the base class and every plain subclass; if the tzinfo's `__repr__`
raises `e`, `repr(t)` raises `e` in both twins, and if it returns an object of another type
both raise `TypeError`; if it returns a `str` `r`, both give the fields with `, tzinfo=r` and
then `, fold=1` for fold 1; and for a table of `str` results it is exactly the text of
`tmReprClsPy`/`tmReprClsC` (`TimeReprCls`). -/
def TimeReprFallible : Prop :=
  ∀ (renv : TzReprEnv) (c : ReprCls) (t : TM),
    (c.Plain → tmReprPyF renv c t = tmReprCF renv c t) ∧
    (∀ oid i e, t.tz = some ⟨oid, .custom i⟩ → renv i = .error e →
      tmReprPyF renv c t = .error e ∧ tmReprCF renv c t = .error e) ∧
    (∀ oid i ty, t.tz = some ⟨oid, .custom i⟩ → renv i = .ok (.other ty) →
      (tmReprPyF renv c t).raises "TypeError" ∧ (tmReprCF renv c t).raises "TypeError") ∧
    (∀ oid i r, t.tz = some ⟨oid, .custom i⟩ → renv i = .ok (.str r) →
      tmReprPyF renv c t = .ok (appendFold
        (((tmReprBodyPy (getClassModule c.module ++ c.tmQualname) t).dropEnd 1).toString ++ s!", tzinfo={r})") t.fold) ∧
      tmReprCF renv c t = .ok (appendFold
        (((tmReprBodyC c.tmTpName t).dropEnd 1).toString ++ s!", tzinfo={r})") t.fold)) ∧
    (∀ env : TzEnv, tmReprPyF env.reprEnv c t = .ok (tmReprClsPy env c t) ∧
      tmReprCF env.reprEnv c t = .ok (tmReprClsC env c t))

theorem timeReprFallible_proven : TimeReprFallible := by
  intro renv c t
  refine ⟨fun hc => ?_, fun oid i e ht he => ?_, fun oid i ty ht he => ?_, fun oid i r ht he => ?_, fun env => ?_⟩
  · unfold tmReprPyF tmReprCF
    rw [tmReprBody_twin]
    have hp : getClassModule c.module ++ c.tmQualname = c.tmTpName := by
      rcases hc with rfl | ⟨mod, name, rfl, hm⟩
      · rfl
      · simp [getClassModule, hm, ReprCls.module, ReprCls.tmQualname, ReprCls.tmTpName]
    rw [hp]
  · simp [tmReprPyF, tmReprCF, appendTzinfoF, tzReprObj, ht, he, bind, Except.bind]
  · refine ⟨⟨.typeError s!"~__repr__() must return a str, not {ty}", ?_, rfl⟩,
      ⟨.typeError s!"~__repr__() must return a str, not {ty}", ?_, rfl⟩⟩ <;>
      simp [tmReprPyF, tmReprCF, appendTzinfoF, tzReprObj, ht, he, bind, Except.bind]
  · simp [tmReprPyF, tmReprCF, appendTzinfoF, tzReprObj, ht, he, bind, Except.bind, pure, Except.pure]
  · simp [tmReprPyF, tmReprCF, tmReprClsPy, tmReprClsC, appendTzinfoF_env, bind, Except.bind, pure, Except.pure]

/-- `repr(datetime)` with a `tzinfo` whose `__repr__` may raise or return a non-`str`: the
twins agree on every outcome for the base class and every plain subclass when the fold is 0,
there is no tzinfo, or the tzinfo's `__repr__` fails (C appends the fold first, so only the
order of a successful `fold=1, tzinfo=` differs, `datetime-repr-fold-tzinfo-twins`); a raising
`__repr__` makes both raise the same exception, a non-`str` result is `TypeError` in both, a
`str` result `r` gives the fields, `, tzinfo=r` and the fold in each twin's order, and for a
table of `str` results it is exactly `dtReprClsPy`/`dtReprClsC`. -/
def DatetimeReprFallible : Prop :=
  ∀ (renv : TzReprEnv) (c : ReprCls) (dt : DT),
    (c.Plain → dt.d ≠ 0 → (dt.fold = 0 ∨ dt.tz = none ∨ ∃ oid i, dt.tz = some ⟨oid, .custom i⟩ ∧ ¬ ∃ r, renv i = .ok (.str r)) →
      dtReprPyF renv c dt = dtReprCF renv c dt) ∧
    (∀ oid i e, dt.tz = some ⟨oid, .custom i⟩ → renv i = .error e →
      dtReprPyF renv c dt = .error e ∧ dtReprCF renv c dt = .error e) ∧
    (∀ oid i ty, dt.tz = some ⟨oid, .custom i⟩ → renv i = .ok (.other ty) →
      (dtReprPyF renv c dt).raises "TypeError" ∧ (dtReprCF renv c dt).raises "TypeError") ∧
    (∀ oid i r, dt.tz = some ⟨oid, .custom i⟩ → renv i = .ok (.str r) →
      dtReprPyF renv c dt = .ok (appendFold
        (((dtReprBodyPy (getClassModule c.module ++ c.dtQualname) dt).dropEnd 1).toString ++ s!", tzinfo={r})") dt.fold) ∧
      dtReprCF renv c dt = .ok
        (((appendFold (dtReprBodyC c.dtTpName dt) dt.fold).dropEnd 1).toString ++ s!", tzinfo={r})")) ∧
    (∀ env : TzEnv, dtReprPyF env.reprEnv c dt = .ok (dtReprClsPy env c dt) ∧
      dtReprCF env.reprEnv c dt = .ok (dtReprClsC env c dt))

theorem datetimeReprFallible_proven : DatetimeReprFallible := by
  intro renv c dt
  refine ⟨fun hc hd hf => ?_, fun oid i e ht he => ?_, fun oid i ty ht he => ?_, fun oid i r ht he => ?_,
    fun env => ?_⟩
  · unfold dtReprPyF dtReprCF
    rw [dtReprBody_twin _ _ hd]
    have hp : getClassModule c.module ++ c.dtQualname = c.dtTpName := by
      rcases hc with rfl | ⟨mod, name, rfl, hm⟩
      · rfl
      · simp [getClassModule, hm, ReprCls.module, ReprCls.dtQualname, ReprCls.dtTpName]
    rw [hp]
    rcases hf with h0 | h0 | ⟨oid, i, ht, hn⟩
    · simp [appendFold, h0, bind, Except.bind, pure, Except.pure]
      cases appendTzinfoF renv (dtReprBodyC c.dtTpName dt) dt.tz <;> rfl
    · simp [appendTzinfoF, h0, bind, Except.bind, pure, Except.pure]
    · rw [ht]
      cases hr : renv i with
      | error e => simp [appendTzinfoF, tzReprObj, hr, bind, Except.bind]
      | ok v =>
        cases v with
        | str r => exact absurd ⟨r, hr⟩ hn
        | other ty => simp [appendTzinfoF, tzReprObj, hr, bind, Except.bind]
  · simp [dtReprPyF, dtReprCF, appendTzinfoF, tzReprObj, ht, he, bind, Except.bind]
  · refine ⟨⟨.typeError s!"~__repr__() must return a str, not {ty}", ?_, rfl⟩,
      ⟨.typeError s!"~__repr__() must return a str, not {ty}", ?_, rfl⟩⟩ <;>
      simp [dtReprPyF, dtReprCF, appendTzinfoF, tzReprObj, ht, he, bind, Except.bind]
  · simp [dtReprPyF, dtReprCF, appendTzinfoF, tzReprObj, ht, he, bind, Except.bind, pure, Except.pure]
  · simp [dtReprPyF, dtReprCF, dtReprClsPy, dtReprClsC, appendTzinfoF_env, bind, Except.bind, pure, Except.pure]

/-- `repr(datetime)` agrees between the twins for every class, a nested subclass included. -/
def DatetimeReprClsTwins : Prop :=
  ∀ (renv : TzReprEnv) (c : ReprCls) (dt : DT), dt.Valid → dtReprPyF renv c dt = dtReprCF renv c dt

/-- `class Outer: class DT(datetime): pass`; `repr(Outer.DT(2020, 1, 1))`: `Outer.DT(2020, 1, 1,
0, 0)` in Python (`__qualname__`), `DT(2020, 1, 1, 0, 0)` in C (`tp_name`). -/
theorem datetimeReprClsTwins_refuted : ¬ DatetimeReprClsTwins := by
  intro h
  have := h (fun _ => .ok (.str "")) (.sub "__main__" "Outer.DT" "DT") ⟨2020, 1, 1, 0, 0, 0, 0, 0, none⟩
    (by refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, Or.inl rfl, trivial⟩)
  revert this
  decide

end PyLean.Datetime
