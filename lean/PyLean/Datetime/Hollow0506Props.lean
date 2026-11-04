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
`_parse_tz` (_strptime.py:821-826) refuses: its exception is the result of both, nothing is
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

end PyLean.Datetime
