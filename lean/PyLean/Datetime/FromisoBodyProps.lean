import PyLean.Datetime.Misc2Props

/-!
`datetime.fromisoformat` (Lib/_pydatetime.py:1964-2014) on every string, by what its parsers
return (review 50b4b958), with the `24:00` rollover stated as "the next day".
-/

namespace PyLean.Datetime
open PyLean

/-- The rollover of `datetime.fromisoformat` (:1998-2010) on a valid date is the next day:
its ordinal is one more, and it is a valid date except after 9999-12-31 (year 10000, which the
constructor then refuses). -/
theorem rollover_next (y m d : Int) (h : ValidDate y m d) :
    let r := rolloverPy y m d
    ymd2ord r.1 r.2.1 r.2.2 = ymd2ord y m d + 1 ∧ (¬ (y = 9999 ∧ m = 12 ∧ d = 31) → ValidDate r.1 r.2.1 r.2.2) := by
  intro r
  have hv := (validDate_iff y m d).mp h
  obtain ⟨hy1, hy2, hm1, hm2, hd1, hd2⟩ := hv
  unfold MINYEAR at hy1; unfold MAXYEAR at hy2
  have hdim : daysInMonth y m = dimL (isLeap y) m := daysInMonth_eq y m
  have hb := dimL_bounds (isLeap y) m ⟨hm1, hm2⟩
  have hr : r = rolloverPy y m d := rfl
  unfold rolloverPy at hr
  rw [if_pos ⟨hm1, hm2, by omega⟩] at hr
  simp only [hdim] at hr
  by_cases hlast : d + 1 > dimL (isLeap y) m
  · rw [if_pos hlast] at hr
    by_cases h12 : m + 1 > 12
    · rw [if_pos h12] at hr
      have hm : m = 12 := by omega
      subst hm
      have hd : d = dimL (isLeap y) 12 := by omega
      rw [hr]
      refine ⟨?_, fun hn => ?_⟩
      · simp only [ymd2ord, daysBeforeYear_succ, daysBeforeMonth_eq, dbmL_one]
        have := dbmL_twelve (isLeap y)
        omega
      · have hy : y + 1 ≤ 9999 := by
          by_cases hy : y = 9999
          · subst hy; exact absurd ⟨rfl, rfl, by rw [hd]; decide⟩ hn
          · omega
        rw [validDate_iff]; simp only [MINYEAR, MAXYEAR]
        have := dimL_bounds (isLeap (y + 1)) 1 ⟨by omega, by omega⟩
        omega
    · rw [if_neg h12] at hr
      rw [hr]
      have hd : d = dimL (isLeap y) m := by omega
      refine ⟨?_, fun _ => ?_⟩
      · simp only [ymd2ord, daysBeforeMonth_eq, dbmL_succ (isLeap y) m ⟨hm1, by omega⟩]
        omega
      · rw [validDate_iff]; simp only [MINYEAR, MAXYEAR]
        have := dimL_bounds (isLeap y) (m + 1) ⟨by omega, by omega⟩
        omega
  · rw [if_neg hlast] at hr
    rw [hr]
    refine ⟨by simp only [ymd2ord]; omega, fun _ => ?_⟩
    rw [validDate_iff]; simp only [MINYEAR, MAXYEAR]
    omega

/-- `datetime.fromisoformat(s)` on every string, by what its parsers return: fewer than seven
characters, or a separator or date part that `_find_isoformat_datetime_separator` and
`_parse_isoformat_date` refuse, is `Invalid isoformat string`; with nothing after the
separator the result is midnight of the parsed date (checked by the constructor); otherwise a
parser `ValueError` of the time part is `Invalid isoformat string`, `error_from_tz` is raised
as it is, hour 24 with other fields is
`minute, second, and microsecond must be 0 when hour is 24`, and `24:00` on a valid date moves
to midnight of the next day (`rollover_next`; on 9999-12-31 the constructor refuses year
10000). -/
def DatetimeFromIsoBody : Prop :=
  ∀ (s : List Char) (sep : Nat) (y m d : Int) (t : TimeV) (e : PyExc) (msg : String),
    (s.length < 7 → datetimeFromIsoPy s = .error (.valueError "~Invalid isoformat string")) ∧
    (7 ≤ s.length → findSepPy s = .error e → datetimeFromIsoPy s = .error (.valueError "~Invalid isoformat string")) ∧
    (7 ≤ s.length → findSepPy s = .ok sep → parseIsoDatePy (s.take sep) = .error e →
      datetimeFromIsoPy s = .error (.valueError "~Invalid isoformat string")) ∧
    (7 ≤ s.length → findSepPy s = .ok sep → parseIsoDatePy (s.take sep) = .ok (y, m, d) →
      let tstr := s.drop (sep + 1)
      (tstr = [] → datetimeFromIsoPy s =
        (do let _ ← checkDate y m d; let _ ← checkTime 0 0 0 0; return ⟨y, m, d, ⟨0, 0, 0, 0, none⟩⟩)) ∧
      (tstr ≠ [] → parseIsoTimePy tstr = .error (.valueError msg) →
        datetimeFromIsoPy s = .error (.valueError "~Invalid isoformat string")) ∧
      (tstr ≠ [] → ∀ nd ec, parseIsoTimePy tstr = .ok (t, nd, ec, some e) → datetimeFromIsoPy s = .error e) ∧
      (tstr ≠ [] → ∀ nd, parseIsoTimePy tstr = .ok (t, nd, true, none) →
        datetimeFromIsoPy s = .error (.valueError "minute, second, and microsecond must be 0 when hour is 24")) ∧
      (tstr ≠ [] → parseIsoTimePy tstr = .ok (t, false, false, none) →
        datetimeFromIsoPy s = (do let _ ← checkDate y m d; let _ ← checkTime t.h t.mi t.s t.us; return ⟨y, m, d, t⟩)) ∧
      (tstr ≠ [] → parseIsoTimePy tstr = .ok (t, true, false, none) → ValidDate y m d →
        ¬ (y = 9999 ∧ m = 12 ∧ d = 31) → 0 ≤ t.h ∧ t.h ≤ 23 → t.mi = 0 → t.s = 0 → t.us = 0 →
        ∃ v : DateTimeV, datetimeFromIsoPy s = .ok v ∧ v.t = t ∧ ValidDate v.y v.m v.d ∧
          ymd2ord v.y v.m v.d = ymd2ord y m d + 1))

theorem datetimeFromIsoBody_proven : DatetimeFromIsoBody := by
  intro s sep y m d t e msg
  refine ⟨fun h => ?_, fun hl h => ?_, fun hl hs h => ?_, fun hl hs hd => ?_⟩
  · simp [datetimeFromIsoPy, h, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  · simp [datetimeFromIsoPy, show ¬ s.length < 7 by omega, h, bind, Except.bind, throw, throwThe,
      MonadExcept.throw, MonadExceptOf.throw]
  · simp [datetimeFromIsoPy, show ¬ s.length < 7 by omega, hs, h, bind, Except.bind, throw, throwThe,
      MonadExcept.throw, MonadExceptOf.throw]
  · intro tstr
    have hpre : ¬ s.length < 7 := by omega
    refine ⟨fun h0 => ?_, fun hne hp => ?_, fun hne nd ec hp => ?_, fun hne nd hp => ?_, fun hne hp => ?_,
      fun hne hp hv hn hh hmi hs0 hus => ?_⟩
    · simp only [tstr] at h0
      simp [datetimeFromIsoPy, hpre, hs, hd, h0, bind, Except.bind, pure, Except.pure]
    · simp only [tstr] at hne hp
      simp [datetimeFromIsoPy, hpre, hs, hd, hne, hp, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExcept.throw, MonadExceptOf.throw]
    · simp only [tstr] at hne hp
      simp [datetimeFromIsoPy, hpre, hs, hd, hne, hp, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExcept.throw, MonadExceptOf.throw]
    · simp only [tstr] at hne hp
      simp [datetimeFromIsoPy, hpre, hs, hd, hne, hp, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExcept.throw, MonadExceptOf.throw]
    · simp only [tstr] at hne hp
      simp [datetimeFromIsoPy, hpre, hs, hd, hne, hp, bind, Except.bind, pure, Except.pure]
    · simp only [tstr] at hne hp
      have hr := rollover_next y m d hv
      simp only at hr
      obtain ⟨hord, hval⟩ := hr
      have hval := hval hn
      have hck := checkDate_ok _ _ _ hval
      have hct : checkTime t.h t.mi t.s t.us = .ok (t.h, t.mi, t.s, t.us) := by
        apply checkTime_ok <;> omega
      refine ⟨⟨(rolloverPy y m d).1, (rolloverPy y m d).2.1, (rolloverPy y m d).2.2, t⟩, ?_, rfl, hval, hord⟩
      simp [datetimeFromIsoPy, hpre, hs, hd, hne, hp, hck, hct, bind, Except.bind, pure, Except.pure]

end PyLean.Datetime
