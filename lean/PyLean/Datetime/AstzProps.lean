import PyLean.Datetime.FromisoBodyProps

/-!
`datetime.astimezone(tz)` to a `timezone`, from a tzinfo whose `utcoffset(self)` is a
timedelta in range (review 50b4b958): the narrowed agreement of the refuted
`AstimezoneTwins`.
-/

namespace PyLean.Datetime
open PyLean

theorem sameOutcome_raises {α : Type} (x y : Py α) (hx : x.raises "OverflowError") (hy : y.raises "OverflowError") :
    SameOutcome x y := by
  obtain ⟨e1, h1, c1⟩ := hx
  obtain ⟨e2, h2, c2⟩ := hy
  subst h1; subst h2
  simp [SameOutcome, c1, c2]

/-- `astimezone(tz)` with `tz` a `timezone`, for every valid datetime whose tzinfo `mytz`
returns from `utcoffset(self)` a timedelta strictly inside a day: both twins return `self`
when `tz is mytz` (identity), and otherwise the same datetime (`(self - offset)` with `tz`
attached, then `tz.fromutc`, i.e. plus `tz`'s offset) or the same `OverflowError` at either
end of the range. -/
theorem astimezoneToTimezone_proven : AstimezoneToTimezone := by
  intro env self tz off name mytz henv hv htz hk hmy hid ⟨o, ho, h1, h2⟩
  have hmyok : mytz.Ok := by have := hv.2.2.2.2.2.2.2.2.2.2; rw [hmy] at this; exact this
  have ov : o.Valid := raw_off_valid env henv mytz hmyok (some self) o ho
  have offv : off.Valid := by have := htz; unfold Tz.Ok at this; rw [hk] at this; exact this.1
  have hchk : callTzinfoCheckC "utcoffset" (.delta o) = .ok (some o) := by
    rw [← check_twin "utcoffset" (.delta o) (fun d hd => by cases hd; exact ov)]
    simp [checkUtcOffset, h1, h2]
  unfold dtAstimezonePy dtAstimezoneC
  simp only [hmy, ho, bind, Except.bind]
  by_cases he : tz.oid = mytz.oid
  · have he' : mytz.oid = tz.oid := he.symm
    simp only [eq_true he, eq_true he', ite_true]
    exact sameOutcome_refl _
  · have he' : ¬ mytz.oid = tz.oid := fun h => he h.symm
    simp only [eq_false he, eq_false he', ite_false, hchk]
    have hs := datetimeSubTimedelta_proven self o hv ov
    simp only at hs
    by_cases hr : 1 ≤ (self.totalUs - o.toUs) / 86400000000 ∧ (self.totalUs - o.toUs) / 86400000000 ≤ MAXORDINAL
    · obtain ⟨hp, hc⟩ := hs.1 hr
      rw [hp, hc]
      have hu : (dtFromTotal (self.totalUs - o.toUs) (some tz)).Valid :=
        dtFromTotal_valid _ _ hr.1 hr.2 htz
      have hrep : dtReplace (dtFromTotal (self.totalUs - o.toUs) self.tz) none none none none none none none none
          (some (some tz)) = .ok (dtFromTotal (self.totalUs - o.toUs) (some tz)) := by
        unfold dtReplace
        exact newDT_ok _ hu
      have hrc : ({ dtFromTotal (self.totalUs - o.toUs) self.tz with tz := some tz } : DT) =
          dtFromTotal (self.totalUs - o.toUs) (some tz) := rfl
      simp only [hrep, hrc]
      simp only [tzFromutcPy, tzFromutcC, hk, timezoneFromutcPy, timezoneFromutcC]
      have htzeq : (dtFromTotal (self.totalUs - o.toUs) (some tz)).tz = some tz := rfl
      simp only [htzeq, Option.map_some, ne_eq, not_true_eq_false, ↓reduceIte]
      have ha := datetimeAddTimedelta_proven (dtFromTotal (self.totalUs - o.toUs) (some tz)) off hu offv
      simp only at ha
      by_cases hr2 : 1 ≤ ((dtFromTotal (self.totalUs - o.toUs) (some tz)).totalUs + off.toUs) / 86400000000 ∧
          ((dtFromTotal (self.totalUs - o.toUs) (some tz)).totalUs + off.toUs) / 86400000000 ≤ MAXORDINAL
      · obtain ⟨p2, c2⟩ := ha.1 hr2
        rw [p2, c2]; simp [Functor.map, Except.map, SameOutcome]
      · obtain ⟨p2, c2⟩ := ha.2 hr2
        obtain ⟨e1, q1, k1⟩ := p2
        obtain ⟨e2, q2, k2⟩ := c2
        rw [q1, q2]; simp [Functor.map, Except.map, SameOutcome, k1, k2]
    · obtain ⟨p, c⟩ := hs.2 hr
      obtain ⟨e1, q1, k1⟩ := p
      obtain ⟨e2, q2, k2⟩ := c
      rw [q1, q2]; simp [SameOutcome, k1, k2]

end PyLean.Datetime
