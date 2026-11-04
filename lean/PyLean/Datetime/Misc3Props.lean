import PyLean.Datetime.Misc3
import PyLean.Datetime.IsoCalProps

/-!
Proofs and refutations for Misc3.lean, CPython 3.15.2.
-/

namespace PyLean.Datetime
open PyLean

theorem isoCalendarDateObj_proven : IsoCalendarDateObj := by
  refine ⟨fun y w d hy hw hd => ?_, fun y w d hy => ?_, fun y m d hv => ?_⟩
  · have e : isoCalTupC (.int y) (.int w) (.int d) = .ok (isoCalTupPy y w d) := by
      simp [isoCalTupC, parseI_int y hy, parseI_int w hw, parseI_int d hd, bind, Except.bind, pure, Except.pure,
        isoCalTupPy]
    rw [e]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨.overflowError "Python int too large to convert to C int",
      by simp only [isoCalTupC]; rw [parseI_big y hy]; rfl, rfl⟩
  · have h := (fromisocalendarIsocalendar_proven y m d hv).2
    have hf : fitsCInt (isocalendar y m d).1 ∧ fitsCInt (isocalendar y m d).2.1 ∧ fitsCInt (isocalendar y m d).2.2 := by
      by_cases hn : fitsCInt (isocalendar y m d).1 ∧ fitsCInt (isocalendar y m d).2.1 ∧ fitsCInt (isocalendar y m d).2.2
      · exact hn
      · unfold fromisocalendarC at h
        rw [if_pos hn] at h
        cases h
    refine ⟨[(isocalendar y m d).1, (isocalendar y m d).2.1, (isocalendar y m d).2.2], ?_, ?_, rfl, rfl, rfl⟩
    · simp [dateIsocalendarObjC, isoCalTupC, parseI_int _ hf.1, parseI_int _ hf.2.1, parseI_int _ hf.2.2, bind,
        Except.bind, pure, Except.pure]
    · simpa using h

theorem dateToordinalC_proven : DateToordinalC := by
  intro y m d hv
  have hp := validDate_pos _ _ _ hv
  have hm : 1 ≤ m ∧ m ≤ 12 := by unfold ValidDate at hv; omega
  have e : dateToordinalC y m d = toordinal y m d := by
    have := (ymdToOrdTwins_proven.1 y m d (by omega) (by unfold ValidDate at hv; omega) hm.1 hm.2).2.2.1
    simp only [dateToordinalC, toordinal, this]
  have hr := ymd2ord_range y m d hv
  refine ⟨e, ?_, ?_, ?_⟩
  · rw [e]; exact hr.1
  · rw [e]; exact hr.2
  · rw [e]; exact (fromordinalToordinal_proven y m d hv).2

theorem timezoneRichcompare_proven : TimezoneRichcompare := by
  intro op a other ha hb
  refine ⟨?_, fun h => ?_, fun h1 h2 => ?_, fun b hbo => ?_⟩
  · cases other with
    | none => cases op <;> rfl
    | some b =>
      have hbv := hb b rfl
      have hc := timedeltaCompare_proven a b op ha hbv
      have he := timedeltaCompare_proven a b .eq ha hbv
      cases op <;> simp_all [timezoneRichObjC, timezoneRichObjPy, CmpOp.holds]
  · subst h; cases op <;> rfl
  · cases op <;> simp_all [timezoneRichObjC]
  · subst hbo
    have hbv := hb b rfl
    have he := (timedeltaCompare_proven a b .eq ha hbv).2
    have hn := (timedeltaCompare_proven a b .ne ha hbv).2
    simp only [timezoneRichObjC]
    simp_all [CmpOp.holds]

theorem initTypesTwins_proven : InitTypesTwins := by
  refine ⟨by decide, ⟨_, rfl, by decide, by decide⟩, fun oid n => ?_, fun oid d s us n r hr hz => ?_⟩
  · cases n <;> rfl
  · simp only [createTzFromDeltaC, hr, bind, Except.bind, pure, Except.pure, createTimezoneC, lookUpTimezoneC]
    simp [hz]

theorem datetimeStrCall_proven : DatetimeStrCall :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩

/-- A subclass with `def isoformat(self, *args, **kwargs): return repr((args, kwargs))`: C's
`str()` passes `' '` positionally, Python's by keyword, so the results differ. -/
theorem datetimeStrTwins_refuted : ¬ DatetimeStrTwins := by
  intro h
  have := h (fun pos kw => if pos.isEmpty ∧ kw.length = 1 then .ok "kw" else .ok "pos")
  revert this
  decide

theorem datetimeNowChecks_proven : DatetimeNowChecks := by
  intro α best best' fromutc
  refine ⟨fun a ha hn => ?_, ?_, fun z => rfl⟩
  rotate_left
  · simp only [datetimeNowC, checkTzinfoSubclassC, bind, Except.bind]
    cases best none <;> rfl
  have e : checkTzinfoSubclassC a = .error (.typeError "~tzinfo argument must be None or of a tzinfo subclass") := by
    cases a with
    | none_ => exact absurd rfl hn
    | tz z => exact absurd rfl (ha z)
    | _ => rfl
  refine ⟨⟨.typeError "~tzinfo argument must be None or of a tzinfo subclass", by simp only [datetimeNowC, e, bind, Except.bind], rfl⟩, ?_⟩
  simp only [datetimeNowC, e, bind, Except.bind]

end PyLean.Datetime
