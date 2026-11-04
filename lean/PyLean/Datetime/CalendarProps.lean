import PyLean.Datetime.Ordinal
import PyLean.Datetime.Spec

/-!
`fromordinal`/`toordinal` round trips and `date + timedelta`, for both twins.
-/

namespace PyLean.Datetime

open PyLean

theorem isLeap_iff (y : Int) : isLeap y = true ↔ (y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0)) := by
  unfold isLeap
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, bne_iff_ne, ne_eq]

theorem daysBeforeYear_succ (y : Int) :
    daysBeforeYear (y + 1) = daysBeforeYear y + 365 + (if isLeap y then 1 else 0) := by
  simp only [daysBeforeYear]
  by_cases h : isLeap y = true
  · rw [if_pos h]; rw [isLeap_iff] at h; omega
  · rw [if_neg h]; rw [isLeap_iff] at h; omega

theorem dimL_bounds (leap : Bool) (m : Int) (hm : 1 ≤ m ∧ m ≤ 12) : 28 ≤ dimL leap m ∧ dimL leap m ≤ 31 := by
  unfold dimL daysInMonthTable
  rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
    m = 10 ∨ m = 11 ∨ m = 12) with h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> cases leap <;> decide

theorem dbmL_succ (leap : Bool) (m : Int) (hm : 1 ≤ m ∧ m ≤ 11) :
    dbmL leap (m + 1) = dbmL leap m + dimL leap m := by
  unfold dimL dbmL daysInMonthTable daysBeforeMonthTable
  rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
    m = 10 ∨ m = 11) with h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> cases leap <;> decide

theorem dbmL_one (leap : Bool) : dbmL leap 1 = 0 := by cases leap <;> decide

theorem dbmL_twelve (leap : Bool) : dbmL leap 12 + dimL leap 12 = 365 + (if leap then 1 else 0) := by
  cases leap <;> decide

theorem daysBeforeYear_nonneg (y : Int) (hy : 1 ≤ y) : 0 ≤ daysBeforeYear y := by
  simp only [daysBeforeYear]; omega

theorem dbmL_nonneg (leap : Bool) (m : Int) (hm : 1 ≤ m ∧ m ≤ 12) : 0 ≤ dbmL leap m := by
  unfold dbmL daysBeforeMonthTable
  rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
    m = 10 ∨ m = 11 ∨ m = 12) with h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> cases leap <;> decide

theorem checkDate_ok (y m d : Int) (h : ValidDate y m d) : checkDate y m d = .ok (y, m, d) := by
  unfold ValidDate at h
  unfold checkDate
  simp only [h, and_self, not_true_eq_false, ite_false]

theorem validDate_iff (y m d : Int) :
    ValidDate y m d ↔ (MINYEAR ≤ y ∧ y ≤ MAXYEAR ∧ 1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ dimL (isLeap y) m) := by
  unfold ValidDate; rw [daysInMonth_eq]

theorem isLeapC_eq (y : Int) (h0 : 0 ≤ y) (h1 : y < 2147483648) : isLeapC y = isLeap y := by
  unfold isLeapC isLeap
  have : y % 4294967296 = y := by omega
  simp only [this]

theorem daysInMonth_C (y m : Int) (h0 : 0 ≤ y) (h1 : y < 2147483648) (hm : 1 ≤ m ∧ m ≤ 12) :
    daysInMonth y m = daysInMonthC y m := by
  unfold daysInMonth daysInMonthC
  rw [isLeapC_eq y h0 h1]
  rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
    m = 10 ∨ m = 11 ∨ m = 12) with h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> cases isLeap y <;> decide

theorem checkDate_eq_C (y m d : Int) :
    checkDate y m d = (do checkDateArgsC y m d; return (y, m, d)) := by
  unfold checkDate checkDateArgsC MINYEAR MAXYEAR
  by_cases h1 : 1 ≤ y ∧ y ≤ 9999
  · have h1' : ¬(y < 1 ∨ y > 9999) := by omega
    rw [if_neg (not_not_intro h1), if_neg h1']
    by_cases h2 : 1 ≤ m ∧ m ≤ 12
    · have h2' : ¬(m < 1 ∨ m > 12) := by omega
      rw [if_neg (not_not_intro h2), if_neg h2']
      have e := daysInMonth_C y m (by omega) (by omega) h2
      dsimp only
      rw [e]
      by_cases h3 : 1 ≤ d ∧ d ≤ daysInMonthC y m
      · have h3' : ¬(d < 1 ∨ d > daysInMonthC y m) := by omega
        rw [if_neg (not_not_intro h3), if_neg h3']; rfl
      · have h3' : (d < 1 ∨ d > daysInMonthC y m) := by omega
        rw [if_pos h3, if_pos h3']; rfl
    · have h2' : (m < 1 ∨ m > 12) := by omega
      rw [if_pos h2, if_pos h2']; rfl
  · have h1' : (y < 1 ∨ y > 9999) := by omega
    rw [if_pos h1, if_pos h1']; rfl

theorem checkDateC_eq (y m d : Int) : checkDateC y m d = checkDate y m d := by
  rw [checkDate_eq_C]; rfl

/-- The ordinal of a valid date is in `1..MAXORDINAL`. -/
theorem ymd2ord_range (y m d : Int) (h : ValidDate y m d) : 1 ≤ ymd2ord y m d ∧ ymd2ord y m d ≤ MAXORDINAL := by
  have hv := h
  unfold ValidDate MINYEAR MAXYEAR at h
  obtain ⟨q, a, b, c, hq, ha0, ha1, hb0, hb1, hc0, hc1, hy, hd0, hd1, ho, -⟩ :=
    ymd2ord_decomp y m d (by omega) ⟨h.2.2.1, h.2.2.2.1⟩ ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩
  rw [ho]; unfold MAXORDINAL
  split at hd1 <;> omega

/-- `_ord2ymd(n)` for `1 <= n <= MAXORDINAL` is a valid date with ordinal `n`. -/
theorem ord2ymd_valid (n : Int) (h1 : 1 ≤ n) (h2 : n ≤ MAXORDINAL) :
    ValidDate (ord2ymd n).1 (ord2ymd n).2.1 (ord2ymd n).2.2 ∧
    ymd2ord (ord2ymd n).1 (ord2ymd n).2.1 (ord2ymd n).2.2 = n ∧ ordToYmdC n = ord2ymd n := by
  obtain ⟨hy, hm1, hm2, hd1, hd2, ho, hc⟩ := ord2ymd_spec n h1
  refine ⟨⟨hy, ?_, hm1, hm2, hd1, hd2⟩, ho, hc⟩
  obtain ⟨q, a, b, c, doy, hq, ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1', rfl⟩ := ord_decomp_exists n h1
  rw [ord2ymd_decomp q a b c doy ha0 ha1 hb0 hb1 hc0 hc1 hd0 hd1']
  unfold MAXORDINAL at h2; unfold MAXYEAR
  simp only
  split at hd1' <;> omega

/-! ### Properties -/

/-- `date.fromordinal(d.toordinal()) == d` for every date, in both twins. -/
def FromordinalToordinal : Prop :=
  ∀ y m d : Int, ValidDate y m d →
    fromordinalPy (toordinal y m d) = .ok (y, m, d) ∧ fromordinalC (toordinal y m d) = .ok (y, m, d)

theorem fromordinalToordinal_proven : FromordinalToordinal := by
  intro y m d h
  have hv := h
  unfold ValidDate MINYEAR at h
  obtain ⟨h1, h2⟩ := ord_roundtrip y m d (by omega) ⟨h.2.2.1, h.2.2.2.1⟩ ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩
  have hr := ymd2ord_range y m d hv
  unfold MAXORDINAL at hr
  refine ⟨?_, ?_⟩
  · unfold fromordinalPy toordinal; rw [h1]; exact checkDate_ok y m d hv
  · unfold fromordinalC toordinal
    rw [ymdToOrdC_eq y m d (by omega)] at h2
    have hf : fitsCInt (ymd2ord y m d) := by unfold fitsCInt; omega
    have hn : ¬ (ymd2ord y m d < 1) := by omega
    simp only [hf, not_true_eq_false, ite_false, hn, h2, checkDateC_eq]
    exact checkDate_ok y m d hv

/-- `date.fromordinal(n).toordinal() == n` for every `1 <= n <= MAXORDINAL`,
and both twins return the same date. -/
def ToordinalFromordinal : Prop :=
  ∀ n : Int, 1 ≤ n → n ≤ MAXORDINAL →
    ∃ y m d, ValidDate y m d ∧ toordinal y m d = n ∧
      fromordinalPy n = .ok (y, m, d) ∧ fromordinalC n = .ok (y, m, d)

theorem toordinalFromordinal_proven : ToordinalFromordinal := by
  intro n h1 h2
  obtain ⟨hv, ho, hc⟩ := ord2ymd_valid n h1 h2
  refine ⟨_, _, _, hv, ho, ?_, ?_⟩
  · unfold fromordinalPy; exact checkDate_ok _ _ _ hv
  · unfold MAXORDINAL at h2
    have hf : fitsCInt n := by unfold fitsCInt; omega
    have hn : ¬ (n < 1) := by omega
    unfold fromordinalC
    simp only [hf, not_true_eq_false, ite_false, hn, hc, checkDateC_eq]
    exact checkDate_ok _ _ _ hv

theorem dateAddPy_eq (y m d : Int) (t : Delta) (h : ValidDate y m d)
    (h1 : 1 ≤ toordinal y m d + t.days) (h2 : toordinal y m d + t.days ≤ MAXORDINAL) :
    dateAddPy y m d t = .ok (ord2ymd (toordinal y m d + t.days)) := by
  unfold dateAddPy
  rw [if_pos ⟨by omega, h2⟩]
  unfold fromordinalPy
  exact checkDate_ok _ _ _ (ord2ymd_valid _ h1 h2).1

/-- The C result, when the target ordinal is in range: some valid date with that
ordinal (hence, by the round trip, Python's date). -/
theorem normalizeYMDC_ok (y m d : Int) (t : Delta) (h : ValidDate y m d)
    (h1 : 1 ≤ toordinal y m d + t.days) (h2 : toordinal y m d + t.days ≤ MAXORDINAL) :
    ∃ y' m' d', normalizeYMDC y m (d + t.days) = .ok (y', m', d') ∧ ValidDate y' m' d' ∧
      ymd2ord y' m' d' = toordinal y m d + t.days := by
  have hv := h
  rw [validDate_iff] at h
  unfold MINYEAR MAXYEAR at h
  obtain ⟨hy1, hy2, hm1, hm2, hd1, hd2⟩ := h
  have hdim := dimL_bounds (isLeap y) m ⟨hm1, hm2⟩
  unfold toordinal at h1 h2 ⊢
  have hlin : ∀ e, ymd2ord y m e = daysBeforeYear y + dbmL (isLeap y) m + e := by
    intro e; unfold ymd2ord; rw [daysBeforeMonth_eq]
  unfold normalizeYMDC
  dsimp only
  simp only [daysInMonth_eq]
  by_cases hin : d + t.days < 1 ∨ d + t.days > dimL (isLeap y) m
  · rw [if_pos hin]
    by_cases h0 : d + t.days = 0
    · rw [if_pos h0]
      by_cases hm : m - 1 > 0
      · rw [if_pos hm]
        simp only
        rw [if_pos (by unfold MINYEAR MAXYEAR; omega)]
        refine ⟨_, _, _, rfl, ?_, ?_⟩
        · rw [validDate_iff, ← daysInMonth_eq]; unfold MINYEAR MAXYEAR
          have := dimL_bounds (isLeap y) (m - 1) ⟨by omega, by omega⟩
          rw [daysInMonth_eq]; omega
        · rw [hlin] at h1 h2 ⊢
          have := dbmL_succ (isLeap y) (m - 1) ⟨by omega, by omega⟩
          rw [show m - 1 + 1 = m by omega] at this
          unfold ymd2ord; rw [daysBeforeMonth_eq]; omega
      · rw [if_neg hm]
        have hm1' : m = 1 := by omega
        subst hm1'
        rw [hlin, dbmL_one] at h1
        have hy : 2 ≤ y := by
          by_cases hy : y = 1
          · subst hy; simp [daysBeforeYear] at h1; omega
          · omega
        simp only
        rw [if_pos (by unfold MINYEAR MAXYEAR; omega)]
        refine ⟨_, _, _, rfl, ?_, ?_⟩
        · rw [validDate_iff]; unfold MINYEAR MAXYEAR dimL daysInMonthTable; simp; omega
        · rw [hlin, dbmL_one]
          have := daysBeforeYear_succ (y - 1)
          rw [show y - 1 + 1 = y by omega] at this
          have h12 := dbmL_twelve (isLeap (y - 1))
          unfold ymd2ord; rw [daysBeforeMonth_eq]
          have : dimL (isLeap (y - 1)) 12 = 31 := by unfold dimL daysInMonthTable; simp
          omega
    · rw [if_neg h0]
      by_cases hn : d + t.days = dimL (isLeap y) m + 1
      · rw [if_pos hn]
        by_cases hm : m + 1 > 12
        · rw [if_pos hm]
          have hm12 : m = 12 := by omega
          subst hm12
          rw [hlin] at h2
          have hy : y ≤ 9998 := by
            by_cases hy : y = 9999
            · subst hy
              have := dbmL_twelve (isLeap 9999)
              unfold MAXORDINAL at h2
              have : daysBeforeYear 9999 = 3651694 := by decide
              have : isLeap 9999 = false := by decide
              simp_all
              omega
            · omega
          simp only
          rw [if_pos (by unfold MINYEAR MAXYEAR; omega)]
          refine ⟨_, _, _, rfl, ?_, ?_⟩
          · rw [validDate_iff]; unfold MINYEAR MAXYEAR dimL daysInMonthTable; simp; omega
          · rw [hlin]
            have := daysBeforeYear_succ y
            have h12 := dbmL_twelve (isLeap y)
            unfold ymd2ord; rw [daysBeforeMonth_eq, dbmL_one]
            split at h12 <;> split at this <;> simp_all <;> omega
        · rw [if_neg hm]
          simp only
          rw [if_pos (by unfold MINYEAR MAXYEAR; omega)]
          refine ⟨_, _, _, rfl, ?_, ?_⟩
          · rw [validDate_iff]; unfold MINYEAR MAXYEAR
            have := dimL_bounds (isLeap y) (m + 1) ⟨by omega, by omega⟩
            omega
          · rw [hlin]
            have := dbmL_succ (isLeap y) m ⟨by omega, by omega⟩
            unfold ymd2ord; rw [daysBeforeMonth_eq]; omega
      · rw [if_neg hn]
        have ho : ymdToOrdC y m 1 + (d + t.days) - 1 = ymd2ord y m d + t.days := by
          rw [ymdToOrdC_eq y m 1 (by omega), hlin, hlin]; omega
        rw [ho, if_neg (by omega)]
        obtain ⟨hv', ho', hc⟩ := ord2ymd_valid _ h1 h2
        rw [hc]
        simp only
        have hv'' := hv'
        unfold ValidDate MINYEAR MAXYEAR at hv''
        rw [if_pos ⟨hv''.1, hv''.2.1⟩]
        exact ⟨_, _, _, rfl, hv', ho'⟩
  · rw [if_neg hin]
    simp only
    rw [if_pos (by unfold MINYEAR MAXYEAR; omega)]
    refine ⟨_, _, _, rfl, ?_, ?_⟩
    · rw [validDate_iff]; unfold MINYEAR MAXYEAR; omega
    · rw [hlin, hlin]; omega

theorem normalizeYMDC_err (y m d : Int) (t : Delta) (h : ValidDate y m d)
    (hout : ¬(1 ≤ toordinal y m d + t.days ∧ toordinal y m d + t.days ≤ MAXORDINAL)) :
    (normalizeYMDC y m (d + t.days)).raises "OverflowError" := by
  rw [validDate_iff] at h
  unfold MINYEAR MAXYEAR at h
  obtain ⟨hy1, hy2, hm1, hm2, hd1, hd2⟩ := h
  have hdim := dimL_bounds (isLeap y) m ⟨hm1, hm2⟩
  unfold toordinal at hout
  have hlin : ∀ e, ymd2ord y m e = daysBeforeYear y + dbmL (isLeap y) m + e := by
    intro e; unfold ymd2ord; rw [daysBeforeMonth_eq]
  have hrange := ymd2ord_range y m d ((validDate_iff y m d).mpr ⟨hy1, hy2, hm1, hm2, hd1, hd2⟩)
  rw [hlin] at hrange hout
  have hdby := daysBeforeYear_nonneg y hy1
  have hdbm := dbmL_nonneg (isLeap y) m ⟨hm1, hm2⟩
  unfold normalizeYMDC
  dsimp only
  simp only [daysInMonth_eq]
  have herr : ∀ (r : Option (Int × Int × Int)),
      (∀ y' m' d', r = some (y', m', d') → ¬(MINYEAR ≤ y' ∧ y' ≤ MAXYEAR)) →
      Py.raises (match r with
        | some (y, m, d) =>
          if MINYEAR ≤ y ∧ y ≤ MAXYEAR then (Except.ok (y, m, d) : Py (Int × Int × Int))
          else .error (.overflowError "date value out of range")
        | none => .error (.overflowError "date value out of range")) "OverflowError" := by
    intro r hr
    match r, hr with
    | none, _ => exact ⟨_, rfl, rfl⟩
    | some (y', m', d'), hr => dsimp only; rw [if_neg (hr y' m' d' rfl)]; exact ⟨_, rfl, rfl⟩
  apply herr
  intro y' m' d' hr
  unfold MINYEAR MAXYEAR
  by_cases hin : d + t.days < 1 ∨ d + t.days > dimL (isLeap y) m
  · rw [if_pos hin] at hr
    by_cases h0 : d + t.days = 0
    · rw [if_pos h0] at hr
      by_cases hm : m - 1 > 0
      · rw [if_pos hm] at hr
        exfalso; apply hout
        have := dbmL_succ (isLeap y) (m - 1) ⟨by omega, by omega⟩
        rw [show m - 1 + 1 = m by omega] at this
        have := dimL_bounds (isLeap y) (m - 1) ⟨by omega, by omega⟩
        have := dbmL_nonneg (isLeap y) (m - 1) ⟨by omega, by omega⟩
        unfold MAXORDINAL at hrange ⊢
        constructor <;> omega
      · rw [if_neg hm] at hr
        simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl, rfl⟩ := hr
        have hm1' : m = 1 := by omega
        subst hm1'
        by_cases hy : y = 1
        · omega
        · exfalso; apply hout
          rw [dbmL_one]
          have := daysBeforeYear_nonneg (y - 1) (by omega)
          have := daysBeforeYear_succ (y - 1)
          rw [show y - 1 + 1 = y by omega] at this
          rw [dbmL_one] at hrange
          unfold MAXORDINAL at hrange ⊢
          constructor <;> split at this <;> omega
    · rw [if_neg h0] at hr
      by_cases hn : d + t.days = dimL (isLeap y) m + 1
      · rw [if_pos hn] at hr
        by_cases hm : m + 1 > 12
        · rw [if_pos hm] at hr
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          have hm12 : m = 12 := by omega
          subst hm12
          by_cases hy : y = 9999
          · omega
          · exfalso; apply hout
            have := daysBeforeYear_succ y
            have h12 := dbmL_twelve (isLeap y)
            have hb : daysBeforeYear (y + 1) ≤ daysBeforeYear 9999 := by
              simp only [daysBeforeYear]; omega
            have : daysBeforeYear 9999 = 3651694 := by decide
            unfold MAXORDINAL
            constructor <;> split at h12 <;> omega
        · rw [if_neg hm] at hr
          exfalso; apply hout
          have := dbmL_succ (isLeap y) m ⟨by omega, by omega⟩
          have := dimL_bounds (isLeap y) (m + 1) ⟨by omega, by omega⟩
          have hb := ymd2ord_range y (m + 1) 1 ((validDate_iff _ _ _).mpr ⟨hy1, hy2, by omega, by omega, by omega, by omega⟩)
          unfold ymd2ord at hb; rw [daysBeforeMonth_eq] at hb
          unfold MAXORDINAL at hrange hb ⊢
          constructor <;> omega
      · rw [if_neg hn] at hr
        have ho : ymdToOrdC y m 1 + (d + t.days) - 1 = daysBeforeYear y + dbmL (isLeap y) m + d + t.days := by
          rw [ymdToOrdC_eq y m 1 (by omega), hlin]; omega
        rw [ho] at hr
        rw [if_pos (by unfold MAXORDINAL at hout ⊢; omega)] at hr
        cases hr
  · rw [if_neg hin] at hr
    exfalso; apply hout
    have hb := ymd2ord_range y m (d + t.days) ((validDate_iff _ _ _).mpr ⟨hy1, hy2, hm1, hm2, by omega, by omega⟩)
    rw [hlin] at hb
    unfold MAXORDINAL at hb ⊢
    omega

/-- `date + timedelta` in both twins: when `d.toordinal() + td.days` is in
`1..MAXORDINAL`, both return the same valid date with that ordinal; otherwise
both raise `OverflowError`. -/
def DateAddTimedelta : Prop :=
  ∀ (y m d : Int) (t : Delta), ValidDate y m d → t.Valid →
    (1 ≤ toordinal y m d + t.days ∧ toordinal y m d + t.days ≤ MAXORDINAL →
      ∃ y' m' d', ValidDate y' m' d' ∧ toordinal y' m' d' = toordinal y m d + t.days ∧
        dateAddPy y m d t = .ok (y', m', d') ∧ dateAddC y m d t = .ok (y', m', d')) ∧
    (¬(1 ≤ toordinal y m d + t.days ∧ toordinal y m d + t.days ≤ MAXORDINAL) →
      (dateAddPy y m d t).raises "OverflowError" ∧ (dateAddC y m d t).raises "OverflowError")

theorem dateAddTimedelta_proven : DateAddTimedelta := by
  intro y m d t h _
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun hout => ⟨?_, ?_⟩⟩
  · obtain ⟨y', m', d', hn, hv, ho⟩ := normalizeYMDC_ok y m d t h h1 h2
    have hpy := dateAddPy_eq y m d t h h1 h2
    rw [← ho, (ord_roundtrip y' m' d' (by unfold ValidDate MINYEAR at hv; omega)
      ⟨hv.2.2.1, hv.2.2.2.1⟩ ⟨hv.2.2.2.2.1, hv.2.2.2.2.2⟩).1] at hpy
    refine ⟨y', m', d', hv, ho, hpy, ?_⟩
    unfold dateAddC
    rw [hn]
    exact checkDate_ok _ _ _ hv
  · unfold dateAddPy
    rw [if_neg (by omega)]
    exact ⟨_, rfl, rfl⟩
  · unfold dateAddC
    obtain ⟨e, he, hc⟩ := normalizeYMDC_err y m d t h hout
    rw [he]
    exact ⟨e, rfl, hc⟩

end PyLean.Datetime
