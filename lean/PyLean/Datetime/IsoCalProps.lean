import PyLean.Datetime.CalendarProps

/-!
ISO calendar: `date.isocalendar()` and `date.fromisocalendar()` are inverse
bijections between valid dates and valid ISO triples, including the 53-week
rule, and the C and Python `fromisocalendar` agree.
-/

namespace PyLean.Datetime

open PyLean

/-- Ordinal of January 1 of year `Y`. -/
def jan1 (Y : Int) : Int := daysBeforeYear Y + 1

theorem ymd2ord_jan1 (Y : Int) : ymd2ord Y 1 1 = jan1 Y := by
  unfold ymd2ord jan1 daysBeforeMonth daysBeforeMonthTable; simp

theorem w1_eq (Y : Int) : isoWeek1Monday Y =
    jan1 Y - (jan1 Y + 6) % 7 + (if (jan1 Y + 6) % 7 > 3 then 7 else 0) := by
  unfold isoWeek1Monday; rw [ymd2ord_jan1]
  dsimp only
  split <;> omega

theorem jan1_succ (Y : Int) : jan1 (Y + 1) = jan1 Y + 365 + (if isLeap Y then 1 else 0) := by
  unfold jan1; rw [daysBeforeYear_succ]; omega

/-- `Y` has 53 ISO weeks, by the test in `_isoweek_to_gregorian`. -/
def LongYear (Y : Int) : Prop := jan1 Y % 7 = 4 ∨ (jan1 Y % 7 = 3 ∧ isLeap Y = true)

/-- The ISO year `Y` has 364 or 371 days, 371 exactly when it is long; its
Monday of week 1 is a Monday within 3 days of January 1. -/
theorem isoYear_facts (Y : Int) :
    (isoWeek1Monday (Y + 1) - isoWeek1Monday Y = 364 ∨ isoWeek1Monday (Y + 1) - isoWeek1Monday Y = 371) ∧
    (isoWeek1Monday (Y + 1) - isoWeek1Monday Y = 371 ↔ LongYear Y) ∧
    isoWeek1Monday Y % 7 = 1 ∧ jan1 Y - 3 ≤ isoWeek1Monday Y ∧ isoWeek1Monday Y ≤ jan1 Y + 3 := by
  rw [w1_eq, w1_eq, jan1_succ]
  unfold LongYear
  by_cases hl : isLeap Y = true
  · simp only [hl, ite_true, and_true]
    split <;> split <;> omega
  · simp only [hl, ite_false, Bool.false_eq_true, and_false, or_false]
    split <;> split <;> omega

theorem jan1_mono (Y Y' : Int) (h1 : 1 ≤ Y) (h : Y < Y') : jan1 Y + 365 ≤ jan1 Y' := by
  unfold jan1; simp only [daysBeforeYear]; omega

theorem w1_mono (Y Y' : Int) (h1 : 1 ≤ Y) (h : Y ≤ Y') : isoWeek1Monday Y ≤ isoWeek1Monday Y' := by
  by_cases he : Y = Y'
  · subst he; omega
  · have := jan1_mono Y Y' h1 (by omega)
    have := (isoYear_facts Y).2.2
    have := (isoYear_facts Y').2.2
    omega

/-- A valid ISO triple: year in range, week within the year's 52 or 53 weeks,
weekday 1..7. -/
def ValidIso (Y W D : Int) : Prop :=
  MINYEAR ≤ Y ∧ Y ≤ MAXYEAR ∧ 1 ≤ W ∧ (W ≤ 52 ∨ (W = 53 ∧ LongYear Y)) ∧ 1 ≤ D ∧ D ≤ 7

/-- Ordinal of an ISO triple. -/
def isoOrd (Y W D : Int) : Int := isoWeek1Monday Y + (W - 1) * 7 + (D - 1)

theorem isoOrd_range (Y W D : Int) (h : ValidIso Y W D) :
    isoWeek1Monday Y ≤ isoOrd Y W D ∧ isoOrd Y W D < isoWeek1Monday (Y + 1) := by
  unfold ValidIso LongYear at h
  have f := isoYear_facts Y
  unfold isoOrd
  rcases h with ⟨_, _, hW1, hW | ⟨hW, hL⟩, hD1, hD2⟩
  · omega
  · have := f.2.1.mpr hL; omega

theorem isoOrd_inj (Y W D Y' W' D' : Int) (h : ValidIso Y W D) (h' : ValidIso Y' W' D')
    (he : isoOrd Y W D = isoOrd Y' W' D') : Y = Y' ∧ W = W' ∧ D = D' := by
  have r := isoOrd_range Y W D h
  have r' := isoOrd_range Y' W' D' h'
  have hY : Y = Y' := by
    unfold ValidIso MINYEAR at h h'
    by_cases hlt : Y < Y'
    · have := w1_mono (Y + 1) Y' (by omega) (by omega); omega
    · by_cases hgt : Y' < Y
      · have := w1_mono (Y' + 1) Y (by omega) (by omega); omega
      · omega
  subst hY
  unfold isoOrd at he
  unfold ValidIso at h h'
  omega

theorem isoweekToGregorianPy_ok (Y W D : Int) (h : ValidIso Y W D) :
    isoweekToGregorianPy Y W D = .ok (ord2ymd (isoOrd Y W D)) := by
  unfold isoweekToGregorianPy isoOrd
  have hv := h
  unfold ValidIso LongYear at h
  rw [if_neg (by omega)]
  rw [ymd2ord_jan1]
  have hw : ¬ (if ¬(0 < W ∧ W < 53) then
      (if W = 53 then ¬(jan1 Y % 7 = 4 ∨ (jan1 Y % 7 = 3 ∧ isLeap Y = true)) else True) else False) := by
    split
    · split
      · rcases h with ⟨_, _, _, hW | ⟨_, hL⟩, _, _⟩
        · omega
        · exact fun hn => hn hL
      · omega
    · simp
  rw [if_neg hw, if_neg (by omega)]
  dsimp only
  congr 2
  omega

theorem isoweekToGregorianPy_err (Y W D : Int) (h : ¬ ValidIso Y W D) :
    (isoweekToGregorianPy Y W D).raises "ValueError" := by
  unfold isoweekToGregorianPy
  unfold ValidIso LongYear MINYEAR MAXYEAR at h
  rw [ymd2ord_jan1]
  by_cases hy : ¬(MINYEAR ≤ Y ∧ Y ≤ MAXYEAR)
  · rw [if_pos hy]; exact ⟨_, rfl, rfl⟩
  · rw [if_neg hy]
    unfold MINYEAR MAXYEAR at hy
    by_cases hw : (if ¬(0 < W ∧ W < 53) then
        (if W = 53 then ¬(jan1 Y % 7 = 4 ∨ (jan1 Y % 7 = 3 ∧ isLeap Y = true)) else True) else False)
    · rw [if_pos hw]; exact ⟨_, rfl, rfl⟩
    · rw [if_neg hw]
      have hD : ¬(0 < D ∧ D < 8) := by
        intro hD; apply h
        split at hw
        · split at hw
          · refine ⟨by omega, by omega, by omega, Or.inr ⟨by omega, Classical.not_not.mp hw⟩, by omega, by omega⟩
          · exact absurd trivial hw
        · exact ⟨by omega, by omega, by omega, Or.inl (by omega), by omega, by omega⟩
      rw [if_pos hD]; exact ⟨_, rfl, rfl⟩

theorem checkDate_inv (y m d : Int) (r : Int × Int × Int) (h : checkDate y m d = .ok r) :
    ValidDate y m d ∧ r = (y, m, d) := by
  unfold checkDate at h
  split at h
  · cases h
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · cases h
      · cases h; refine ⟨?_, rfl⟩; unfold ValidDate; omega

/-- `isocalendar` returns a valid ISO triple naming the same day. -/
theorem isocalendar_spec (y m d : Int) (h : ValidDate y m d) :
    ValidIso (isocalendar y m d).1 (isocalendar y m d).2.1 (isocalendar y m d).2.2 ∧
    isoOrd (isocalendar y m d).1 (isocalendar y m d).2.1 (isocalendar y m d).2.2 = ymd2ord y m d := by
  have hr := ymd2ord_range y m d h
  have hv := h
  unfold ValidDate MINYEAR MAXYEAR at h
  obtain ⟨q, a, b, c, hq, ha0, ha1, hb0, hb1, hc0, hc1, hy, hd0, hd1, ho, -⟩ :=
    ymd2ord_decomp y m d (by omega) ⟨h.2.2.1, h.2.2.2.1⟩ ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩
  have hdy := daysBeforeYear_decomp q a b c ha0 ha1 hb0 hb1 hc0 hc1
  have hL := isLeap_decomp q a b c ha0 ha1 hb0 hb1 hc0 hc1
  rw [← hy] at hdy hL
  -- `today` lies in the Gregorian year `y`
  have hT1 : jan1 y ≤ ymd2ord y m d := by unfold jan1; omega
  have hT2 : ymd2ord y m d < jan1 (y + 1) := by
    rw [jan1_succ]; unfold jan1; rw [hL]; split at hd1 <;> simp_all <;> omega
  have fy := isoYear_facts y
  have fy0 := isoYear_facts (y - 1)
  rw [show y - 1 + 1 = y by omega] at fy0
  have j0 := jan1_succ (y - 1)
  rw [show y - 1 + 1 = y by omega] at j0
  have j1 := jan1_succ y
  have hj1 : jan1 1 = 1 := by decide
  have hw10000 : isoWeek1Monday 10000 = 3652062 := by decide
  unfold MAXORDINAL at hr
  unfold isocalendar ValidIso isoOrd MINYEAR MAXYEAR
  dsimp only
  generalize ymd2ord y m d = T at hr hT1 hT2 ⊢
  generalize hw0 : isoWeek1Monday (y - 1) = w0 at fy0 ⊢
  generalize hw : isoWeek1Monday y = w at fy fy0 ⊢
  generalize hw2 : isoWeek1Monday (y + 1) = w2 at fy ⊢
  split
  · -- `today` is before week 1: the last ISO week of `y - 1`
    have hy2 : 2 ≤ y := by
      by_cases hy1 : y = 1
      · subst hy1; rw [hj1] at fy; omega
      · omega
    simp only [hw0]
    refine ⟨⟨by omega, by omega, by omega, ?_, by omega, by omega⟩, by omega⟩
    by_cases h53 : (T - w0) / 7 + 1 ≤ 52
    · exact Or.inl h53
    · exact Or.inr ⟨by omega, fy0.2.1.mp (by omega)⟩
  · split
    · -- week 1 of `y + 1`
      have hy9 : y ≤ 9998 := by
        by_cases h9 : y = 9999
        · subst h9
          have : w2 = 3652062 := by rw [← hw2]; decide
          omega
        · omega
      simp only [hw2]
      refine ⟨⟨by omega, by omega, by omega, Or.inl (by omega), by omega, by omega⟩, ?_⟩
      have f2 := isoYear_facts (y + 1)
      rw [hw2] at f2
      omega
    · simp only [hw]
      refine ⟨⟨by omega, by omega, by omega, ?_, by omega, by omega⟩, by omega⟩
      by_cases h53 : (T - w) / 7 + 1 ≤ 52
      · exact Or.inl h53
      · exact Or.inr ⟨by omega, fy.2.1.mp (by omega)⟩

/-! ### Properties -/

/-- `date.fromisocalendar(*d.isocalendar()) == d` for every date, in both twins. -/
def FromisocalendarIsocalendar : Prop :=
  ∀ y m d : Int, ValidDate y m d →
    fromisocalendarPy (isocalendar y m d).1 (isocalendar y m d).2.1 (isocalendar y m d).2.2 = .ok (y, m, d) ∧
    fromisocalendarC (isocalendar y m d).1 (isocalendar y m d).2.1 (isocalendar y m d).2.2 = .ok (y, m, d)

/-- The C `iso_to_ymd` agrees with Python's `_isoweek_to_gregorian` on C ints. -/
theorem isoToYmdC_eq (Y W D : Int) :
    (ValidIso Y W D → isoToYmdC Y W D = .ok (ord2ymd (isoOrd Y W D))) ∧
    (¬ ValidIso Y W D → ∃ e, isoToYmdC Y W D = .error e) := by
  have hwd : 1 ≤ Y → (weekdayC Y 1 1 = 3 ↔ jan1 Y % 7 = 4) ∧ (weekdayC Y 1 1 = 2 ↔ jan1 Y % 7 = 3) := by
    intro hY
    unfold weekdayC
    rw [ymdToOrdC_eq Y 1 1 hY, ymd2ord_jan1]
    have : 0 ≤ jan1 Y := by unfold jan1; have := daysBeforeYear_nonneg Y hY; omega
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]
    omega
  constructor
  · intro h
    have hv := h
    unfold ValidIso LongYear MINYEAR MAXYEAR at h
    unfold isoToYmdC isoOrd MINYEAR MAXYEAR
    rw [if_neg (by omega)]
    have hw := hwd (by omega)
    have hw' : ¬ (if W ≤ 0 ∨ W ≥ 53 then
        (if W = 53 then ¬(weekdayC Y 1 1 = 3 ∨ (weekdayC Y 1 1 = 2 ∧ isLeap Y = true)) else True) else False) := by
      split
      · split
        · rcases h with ⟨_, _, _, hW | ⟨_, hL⟩, _, _⟩
          · omega
          · intro hn; apply hn; rw [hw.1, hw.2]; exact hL
        · omega
      · simp
    rw [if_neg hw', if_neg (by omega)]
    have := (isoOrd_range Y W D hv).1
    have fY := isoYear_facts Y
    have hj : 1 ≤ jan1 Y := by unfold jan1; have := daysBeforeYear_nonneg Y (by omega); omega
    have h1 : 1 ≤ isoWeek1Monday Y + ((W - 1) * 7 + D - 1) := by
      by_cases hY1 : Y = 1
      · subst hY1; have : isoWeek1Monday 1 = 1 := by decide
        omega
      · have := jan1_mono 1 Y (by omega) (by omega)
        have : jan1 1 = 1 := by decide
        omega
    dsimp only
    rw [(ord2ymd_spec _ h1).2.2.2.2.2.2]
    congr 2
    omega
  · intro h
    unfold isoToYmdC
    dsimp only
    by_cases hy : Y < MINYEAR ∨ Y > MAXYEAR
    · rw [if_pos hy]; exact ⟨_, rfl⟩
    · rw [if_neg hy]
      by_cases hw : (if W ≤ 0 ∨ W ≥ 53 then
          (if W = 53 then ¬(weekdayC Y 1 1 = 3 ∨ (weekdayC Y 1 1 = 2 ∧ isLeap Y = true)) else True) else False)
      · rw [if_pos hw]; exact ⟨_, rfl⟩
      · rw [if_neg hw]
        by_cases hd : D ≤ 0 ∨ D ≥ 8
        · rw [if_pos hd]; exact ⟨_, rfl⟩
        · exfalso; apply h
          unfold MINYEAR MAXYEAR at hy
          have hwd' := hwd (by omega)
          refine ⟨by unfold MINYEAR; omega, by unfold MAXYEAR; omega, ?_, ?_, by omega, by omega⟩
          · split at hw
            · split at hw
              · omega
              · exact absurd trivial hw
            · omega
          · split at hw
            · split at hw
              · right; refine ⟨by omega, ?_⟩
                have hw := Classical.not_not.mp hw
                unfold LongYear; rw [← hwd'.1, ← hwd'.2]; exact hw
              · exact absurd trivial hw
            · left; omega

theorem fromisocalendarIsocalendar_proven : FromisocalendarIsocalendar := by
  intro y m d h
  obtain ⟨hv, ho⟩ := isocalendar_spec y m d h
  have hrt := (ord_roundtrip y m d (by unfold ValidDate MINYEAR at h; omega)
    ⟨h.2.2.1, h.2.2.2.1⟩ ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩).1
  constructor
  · unfold fromisocalendarPy
    rw [isoweekToGregorianPy_ok _ _ _ hv, ho, hrt]
    exact checkDate_ok y m d h
  · unfold fromisocalendarC
    have hf : fitsCInt (isocalendar y m d).1 ∧ fitsCInt (isocalendar y m d).2.1 ∧
        fitsCInt (isocalendar y m d).2.2 := by
      unfold ValidIso MINYEAR MAXYEAR at hv; unfold fitsCInt; omega
    rw [if_neg (by simp [hf]), (isoToYmdC_eq _ _ _).1 hv, ho, hrt]
    exact checkDate_ok y m d h

/-- `date.fromisocalendar(Y, W, D)` succeeds only for valid ISO triples (week 53
only in long years), and the date it returns has `isocalendar() == (Y, W, D)`. -/
def FromisocalendarExact : Prop :=
  ∀ Y W D : Int, ∀ r : Int × Int × Int, fromisocalendarPy Y W D = .ok r →
    ValidIso Y W D ∧ isocalendar r.1 r.2.1 r.2.2 = (Y, W, D)

theorem fromisocalendarExact_proven : FromisocalendarExact := by
  intro Y W D r hr
  by_cases hv : ValidIso Y W D
  · refine ⟨hv, ?_⟩
    unfold fromisocalendarPy at hr
    rw [isoweekToGregorianPy_ok _ _ _ hv] at hr
    simp only [bind, Except.bind] at hr
    obtain ⟨hvr, hrr⟩ := checkDate_inv _ _ _ r hr
    subst hrr
    have hge : 1 ≤ isoOrd Y W D := by
      have := (isoOrd_range Y W D hv).1
      have fY := isoYear_facts Y
      unfold ValidIso MINYEAR at hv
      by_cases hY1 : Y = 1
      · subst hY1; have : isoWeek1Monday 1 = 1 := by decide
        omega
      · have := jan1_mono 1 Y (by omega) (by omega)
        have : jan1 1 = 1 := by decide
        omega
    have hord := (ord2ymd_spec _ hge).2.2.2.2.2.1
    obtain ⟨hv', ho'⟩ := isocalendar_spec _ _ _ hvr
    rw [hord] at ho'
    obtain ⟨e1, e2, e3⟩ := isoOrd_inj _ _ _ _ _ _ hv' hv ho'
    exact Prod.ext e1 (Prod.ext e2 e3)
  · exfalso
    obtain ⟨e, he, -⟩ := isoweekToGregorianPy_err Y W D hv
    unfold fromisocalendarPy at hr
    rw [he] at hr
    cases hr

/-- `date.fromisocalendar`: C and Python agree on the result and the exception
class for all ints. -/
def FromisocalendarTwins : Prop :=
  ∀ Y W D : Int, SameOutcome (fromisocalendarPy Y W D) (fromisocalendarC Y W D)

/-- `date.fromisocalendar(2**31, 1, 1)`: Python rejects the year with `ValueError`, and C
stops at the clinic `int` conversion with `OverflowError`. Until 3.14 C turned that
`OverflowError` into `ValueError`. -/
theorem fromisocalendarTwins_refuted : ¬FromisocalendarTwins := by
  intro h
  have h1 := h (2 ^ 31) 1 1
  have e1 : fromisocalendarPy (2 ^ 31) 1 1 = .error (.valueError s!"year must be in 1..9999, not {(2 : Int) ^ 31}") := by
    decide
  have e2 : fromisocalendarC (2 ^ 31) 1 1 =
      .error (.overflowError "Python int too large to convert to C int") := by decide
  rw [e1, e2] at h1
  simp [SameOutcome, PyExc.className] at h1

/-- The same with every component a C `int`, the domain the clinic conversion lets through:
C and Python agree on the result and the exception class. -/
def FromisocalendarTwinsCInt : Prop :=
  ∀ Y W D : Int, fitsCInt Y → fitsCInt W → fitsCInt D →
    SameOutcome (fromisocalendarPy Y W D) (fromisocalendarC Y W D)

theorem fromisocalendarTwinsCInt_proven : FromisocalendarTwinsCInt := by
  intro Y W D hY hW hD
  have hf : fitsCInt Y ∧ fitsCInt W ∧ fitsCInt D := ⟨hY, hW, hD⟩
  by_cases hv : ValidIso Y W D
  · unfold fromisocalendarPy fromisocalendarC
    rw [isoweekToGregorianPy_ok _ _ _ hv, if_neg (by simp [hf]), (isoToYmdC_eq _ _ _).1 hv]
    exact sameOutcome_refl _
  · obtain ⟨e, he, hc⟩ := isoweekToGregorianPy_err Y W D hv
    have hpy : fromisocalendarPy Y W D = .error e := by unfold fromisocalendarPy; rw [he]; rfl
    rw [hpy]
    unfold fromisocalendarC
    rw [if_neg (by simp [hf])]
    obtain ⟨e', he'⟩ := (isoToYmdC_eq Y W D).2 hv
    rw [he']
    split <;> first | (simp only [SameOutcome]; rw [hc]; rfl) | (exfalso; simp_all)

end PyLean.Datetime
