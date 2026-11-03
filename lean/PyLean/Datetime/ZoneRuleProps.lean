import PyLean.Datetime.ZoneRule

/-!
# Properties of the TZ rule dates (`zoneinfo`, CPython 3.15.2)

* the C and Python twins compute the same transition time for every rule either parser can
  build and every `datetime` year (proven);
* `Mm.w.d` is the `d`-th weekday of week `w` of month `m`, week 5 meaning the last one, as
  POSIX defines it (proven);
* `Jn` is day `n` of a year without February 29 (proven);
* the zero-based `n` is day `n` counted from January 1 (refuted: both twins are a day early).
-/

namespace PyLean.Datetime.Zone

open PyLean PyLean.Datetime

/-! ### Integer conversions that change nothing -/

theorem wrapS8_id (x : Int) (h1 : -128 ≤ x) (h2 : x < 128) : wrapS 8 x = x := by
  unfold wrapS
  simp only [show (2 : Int) ^ 8 = 256 from rfl, show (2 : Int) ^ (8 - 1) = 128 from rfl]
  split <;> omega

theorem wrapS16_id (x : Int) (h1 : -32768 ≤ x) (h2 : x < 32768) : wrapS 16 x = x := by
  unfold wrapS
  simp only [show (2 : Int) ^ 16 = 65536 from rfl, show (2 : Int) ^ (16 - 1) = 32768 from rfl]
  split <;> omega

theorem wrap32_id (x : Int) (h1 : -2147483648 ≤ x) (h2 : x < 2147483648) : wrap32 x = x := by
  unfold wrap32 wrapS
  simp only [show (2 : Int) ^ 32 = 4294967296 from rfl,
    show (2 : Int) ^ (32 - 1) = 2147483648 from rfl]
  split <;> omega

theorem wrap64_id (x : Int) (h1 : -9223372036854775808 ≤ x) (h2 : x < 9223372036854775808) :
    wrap64 x = x := by
  unfold wrap64 wrapS
  simp only [show (2 : Int) ^ 64 = 18446744073709551616 from rfl,
    show (2 : Int) ^ (64 - 1) = 9223372036854775808 from rfl]
  split <;> omega

theorem wrapU8_id (x : Int) (h1 : 0 ≤ x) (h2 : x < 256) : wrapU 8 x = x := by
  unfold wrapU
  simp only [show (2 : Int) ^ 8 = 256 from rfl]
  omega

theorem wrapU16_id (x : Int) (h1 : 0 ≤ x) (h2 : x < 65536) : wrapU 16 x = x := by
  unfold wrapU
  simp only [show (2 : Int) ^ 16 = 65536 from rfl]
  omega

/-! ### The C calendar helpers on `datetime` years -/

theorem isLeapC_eq (y : Int) (h0 : 0 ≤ y) (h1 : y < 4294967296) : isLeapC y = isLeap y := by
  unfold isLeapC isLeap wrapU
  simp only [show (2 : Int) ^ 32 = 4294967296 from rfl]
  rw [Int.emod_eq_of_lt h0 h1]

theorem ymdToOrdZ_eq (y m d : Int) (hy : 1 ≤ y) (hy2 : y ≤ 9999) :
    ymdToOrdZ y m d = daysBeforeYear y + daysBeforeMonthTable m +
      (if m > 2 ∧ isLeap y = true then 1 else 0) + d := by
  unfold ymdToOrdZ daysBeforeYear
  simp (disch := omega) only [Int.tdiv_eq_ediv_of_nonneg]
  rw [show y - 1 + 1 = y by omega, isLeapC_eq y (by omega) (by omega)]
  generalize (if m > 2 ∧ isLeap y = true then (1 : Int) else 0) = i
  omega

theorem ymd2ord_eq (y m d : Int) :
    ymd2ord y m d = daysBeforeYear y + daysBeforeMonthTable m +
      (if m > 2 ∧ isLeap y = true then 1 else 0) + d := by
  unfold ymd2ord daysBeforeMonth
  generalize (if m > 2 ∧ isLeap y = true then (1 : Int) else 0) = i
  omega

theorem postEpoch_eq (y : Int) : postEpochDaysBeforeYear y = daysBeforeYear y - EPOCHORDINAL := rfl

theorem daysBeforeYear_bounds (y : Int) (hy : 1 ≤ y) (hy2 : y ≤ 9999) :
    0 ≤ daysBeforeYear y ∧ daysBeforeYear y ≤ 3652059 := by
  unfold daysBeforeYear
  simp only
  omega

theorem month_tables (m : Int) (h1 : 1 ≤ m) (h2 : m ≤ 12) :
    28 ≤ daysInMonthTable m ∧ daysInMonthTable m ≤ 31 ∧ 0 ≤ daysBeforeMonthTable m ∧
      daysBeforeMonthTable m ≤ 334 ∧ (m > 2 ∨ daysBeforeMonthTable m + daysInMonthTable m ≤ 59) ∧
      (m ≤ 2 ∨ 59 ≤ daysBeforeMonthTable m) ∧ (m = 2 → daysInMonthTable m = 28) := by
  rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
    m = 10 ∨ m = 11 ∨ m = 12) with h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> decide

/-! ### The day of the month -/

set_option maxRecDepth 100000 in
/-- The C `int8_t` arithmetic and the Python ints agree on every first weekday, weekday,
week and month length. -/
theorem calMonthDay_table : ∀ fd d : Fin 7, ∀ w : Fin 5, ∀ k : Fin 4,
    calMonthDayC (fd : Nat) (28 + (k : Nat)) (d : Nat) ((w : Nat) + 1) =
      calMonthDayPy (fd : Nat) (28 + (k : Nat)) (d : Nat) ((w : Nat) + 1) := by
  decide

theorem calMonthDay_eq (fd dim d w : Int) (hfd : 0 ≤ fd ∧ fd ≤ 6) (hdim : 28 ≤ dim ∧ dim ≤ 31)
    (hd : 0 ≤ d ∧ d ≤ 6) (hw : 1 ≤ w ∧ w ≤ 5) :
    calMonthDayC fd dim d w = calMonthDayPy fd dim d w := by
  have := calMonthDay_table ⟨fd.toNat, by omega⟩ ⟨d.toNat, by omega⟩ ⟨(w - 1).toNat, by omega⟩
    ⟨(dim - 28).toNat, by omega⟩
  simp only at this
  rwa [show ((fd.toNat : Nat) : Int) = fd by omega, show ((d.toNat : Nat) : Int) = d by omega,
    show (((w - 1).toNat : Nat) : Int) + 1 = w by omega,
    show (28 : Int) + (((dim - 28).toNat : Nat) : Int) = dim by omega] at this

/-- The Python day of the month: the `d`-th weekday counted from Sunday, in week `w`, or the
last one for `w = 5`. -/
theorem calMonthDayPy_spec (fd dim d w : Int) (_hfd : 0 ≤ fd ∧ fd ≤ 6) (hdim : 28 ≤ dim ∧ dim ≤ 31)
    (hd : 0 ≤ d ∧ d ≤ 6) (hw : 1 ≤ w ∧ w ≤ 5) :
    let md := calMonthDayPy fd dim d w
    1 ≤ md ∧ md ≤ dim ∧ (fd + 1 + (md - 1)) % 7 = d ∧
      (w < 5 → 7 * (w - 1) < md ∧ md ≤ 7 * w) ∧ (w = 5 → dim < md + 7) := by
  unfold calMonthDayPy
  simp only
  split <;> omega

/-! ### Twins -/

/-- What a rule's fields can be after either parser: `calendarrule_new`/`dayrule_new` and
`_CalendarOffset`/`_DayOffset` check the date fields and the hour; the minute and second have
two digits and the sign of the hour (`parse_transition_time`, `_parse_transition_time`). -/
def RuleValid : TRule → Prop
  | .cal m w d h mi s => 1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ w ∧ w ≤ 5 ∧ 0 ≤ d ∧ d ≤ 6 ∧
      -167 ≤ h ∧ h ≤ 167 ∧ -99 ≤ mi ∧ mi ≤ 99 ∧ -99 ≤ s ∧ s ≤ 99
  | .day j d h mi s => (if j then 1 else 0) ≤ d ∧ d ≤ 365 ∧
      -167 ≤ h ∧ h ≤ 167 ∧ -99 ≤ mi ∧ mi ≤ 99 ∧ -99 ≤ s ∧ s ≤ 99

/-- The C and Python rules give the same local timestamp in every `datetime` year. -/
def RuleDateTwins : Prop :=
  ∀ (r : TRule) (year : Int), RuleValid r → 1 ≤ year → year ≤ 9999 →
    r.yearToTsC year = r.yearToEpochPy year

theorem calYearToTs_eq (m w d h mi s y : Int) (hv : RuleValid (.cal m w d h mi s))
    (hy : 1 ≤ y) (hy2 : y ≤ 9999) : calYearToTsC m w d h mi s y = calYearToEpochPy m w d h mi s y := by
  obtain ⟨hm1, hm2, hw1, hw2, hd1, hd2, hh1, hh2, hmi1, hmi2, hs1, hs2⟩ := hv
  have ht := month_tables m hm1 hm2
  have hdby := daysBeforeYear_bounds y hy hy2
  unfold calYearToTsC calYearToEpochPy monthrange calWeekday calYmd2ordPy
  simp only [hy, hy2, and_self, ite_true]
  rw [ymdToOrdZ_eq y m 1 hy hy2, ← ymd2ord_eq, isLeapC_eq y (by omega) (by omega)]
  have hpos : 0 ≤ ymd2ord y m 1 + 6 := by rw [ymd2ord_eq]; split <;> omega
  rw [Int.tmod_eq_emod_of_nonneg hpos, wrapS8_id ((ymd2ord y m 1 + 6) % 7) (by omega) (by omega),
    wrapU8_id (daysInMonthTable m) (by omega) (by omega)]
  have hdim : (if m = 2 ∧ isLeap y = true then wrapU 8 (daysInMonthTable m + 1) else daysInMonthTable m)
      = daysInMonthTable m + (if m = 2 ∧ isLeap y = true then 1 else 0) := by
    split
    · rw [wrapU8_id (daysInMonthTable m + 1) (by omega) (by omega)]
    · omega
  rw [hdim]
  have hfd : 0 ≤ (ymd2ord y m 1 + 6) % 7 ∧ (ymd2ord y m 1 + 6) % 7 ≤ 6 := by omega
  have hdim' : 28 ≤ daysInMonthTable m + (if m = 2 ∧ isLeap y = true then 1 else 0) ∧
      daysInMonthTable m + (if m = 2 ∧ isLeap y = true then 1 else 0) ≤ 31 := by
    constructor <;> split <;> omega
  rw [calMonthDay_eq _ _ _ _ hfd hdim' ⟨hd1, hd2⟩ ⟨hw1, hw2⟩]
  have hmd := calMonthDayPy_spec _ _ _ _ hfd hdim' ⟨hd1, hd2⟩ ⟨hw1, hw2⟩
  simp only at hmd
  generalize calMonthDayPy ((ymd2ord y m 1 + 6) % 7)
    (daysInMonthTable m + (if m = 2 ∧ isLeap y = true then 1 else 0)) d w = md at hmd ⊢
  rw [ymdToOrdZ_eq y m md hy hy2, postEpoch_eq]
  have hl : 0 ≤ (if m > 2 ∧ isLeap y = true then (1 : Int) else 0) ∧
      (if m > 2 ∧ isLeap y = true then (1 : Int) else 0) ≤ 1 := by constructor <;> split <;> omega
  rw [wrap64_id]
  · unfold EPOCHORDINAL; omega
  · unfold EPOCHORDINAL; omega
  · unfold EPOCHORDINAL; omega

theorem dayYearToTs_eq (j : Bool) (d h mi s y : Int) (hv : RuleValid (.day j d h mi s))
    (hy : 1 ≤ y) (hy2 : y ≤ 9999) : dayYearToTsC j d h mi s y = dayYearToEpochPy j d h mi s y := by
  obtain ⟨hd1, hd2, hh1, hh2, hmi1, hmi2, hs1, hs2⟩ := hv
  have hdby := daysBeforeYear_bounds y hy hy2
  have hj : 0 ≤ d := by split at hd1 <;> omega
  unfold dayYearToTsC dayYearToEpochPy
  simp only
  rw [ymdToOrdZ_eq y 1 1 hy hy2, postEpoch_eq, isLeapC_eq y (by omega) (by omega)]
  have hdd : (if j = true ∧ d ≥ 60 ∧ isLeap y = true then wrapU 16 (d + 1) else d) =
      (if j = true ∧ d ≥ 60 ∧ isLeap y = true then d + 1 else d) := by
    split
    · rw [wrapU16_id (d + 1) (by omega) (by omega)]
    · rfl
  rw [hdd]
  simp only [show daysBeforeMonthTable 1 = 0 from rfl, show ¬ ((1 : Int) > 2) by omega,
    false_and, ite_false]
  have hb : d ≤ (if j = true ∧ d ≥ 60 ∧ isLeap y = true then d + 1 else d) ∧
      (if j = true ∧ d ≥ 60 ∧ isLeap y = true then d + 1 else d) ≤ d + 1 := by
    constructor <;> split <;> omega
  generalize (if j = true ∧ d ≥ 60 ∧ isLeap y = true then d + 1 else d) = dd at hb ⊢
  rw [wrap64_id]
  · unfold EPOCHORDINAL; omega
  · unfold EPOCHORDINAL; omega
  · unfold EPOCHORDINAL; omega

theorem ruleDateTwins_proven : RuleDateTwins := by
  intro r year hv hy hy2
  cases r with
  | cal m w d h mi s => exact calYearToTs_eq m w d h mi s year hv hy hy2
  | day j d h mi s => exact dayYearToTs_eq j d h mi s year hv hy hy2

/-! ### What the rules mean (POSIX TZ, IEEE Std 1003.1-2024 §8.3; RFC 9636 §3.3.1) -/

/-- `Mm.w.d/time` is `time` on the `d`-th day of week `w` of month `m`: "Week 1 is the first
week in which the d'th day occurs", "week 5 means the last d day in month m", "Day zero is
Sunday" (`date(1, 1, 1)`, ordinal 1, was a Monday, so a day's weekday from Sunday is its
ordinal mod 7). For every `datetime` year and valid rule, the Python transition is at that day,
and so is the C one by `RuleDateTwins`. -/
def CalendarRuleMeaning : Prop :=
  ∀ (m w d h mi s year : Int), RuleValid (.cal m w d h mi s) → 1 ≤ year → year ≤ 9999 →
    ∃ md : Int,
      calYearToEpochPy m w d h mi s year =
        (ymd2ord year m md - EPOCHORDINAL) * 86400 + (h * 3600 + mi * 60 + s) ∧
      1 ≤ md ∧ md ≤ daysInMonth year m ∧ ymd2ord year m md % 7 = d ∧
      (w < 5 → 7 * (w - 1) < md ∧ md ≤ 7 * w) ∧ (w = 5 → daysInMonth year m < md + 7)

theorem calendarRuleMeaning_proven : CalendarRuleMeaning := by
  intro m w d h mi s y hv hy hy2
  obtain ⟨hm1, hm2, hw1, hw2, hd1, hd2, -⟩ := hv
  have ht := month_tables m hm1 hm2
  have hfd : 0 ≤ (ymd2ord y m 1 + 6) % 7 ∧ (ymd2ord y m 1 + 6) % 7 ≤ 6 := by omega
  have hdim : 28 ≤ daysInMonthTable m + (if m = 2 ∧ isLeap y = true then 1 else 0) ∧
      daysInMonthTable m + (if m = 2 ∧ isLeap y = true then 1 else 0) ≤ 31 := by
    constructor <;> split <;> omega
  have hmd := calMonthDayPy_spec _ _ _ _ hfd hdim ⟨hd1, hd2⟩ ⟨hw1, hw2⟩
  simp only at hmd
  refine ⟨calMonthDayPy ((ymd2ord y m 1 + 6) % 7)
    (daysInMonthTable m + (if m = 2 ∧ isLeap y = true then 1 else 0)) d w, ?_, ?_⟩
  · unfold calYearToEpochPy monthrange calWeekday calYmd2ordPy
    simp only [hy, hy2, and_self, ite_true]
    rw [postEpoch_eq, ymd2ord_eq y m (calMonthDayPy _ _ d w)]
    omega
  · have hdm : daysInMonth y m = daysInMonthTable m + (if m = 2 ∧ isLeap y = true then 1 else 0) := by
      unfold daysInMonth
      by_cases hc : m = 2 ∧ isLeap y = true
      · obtain ⟨rfl, h2⟩ := hc
        simp [h2, daysInMonthTable]
      · simp only [hc, ite_false]
        omega
    rw [hdm]
    have e1 : ymd2ord y m 1 = daysBeforeYear y + daysBeforeMonthTable m +
        (if m > 2 ∧ isLeap y = true then 1 else 0) + 1 := ymd2ord_eq y m 1
    refine ⟨hmd.1, hmd.2.1, ?_, hmd.2.2.2⟩
    rw [ymd2ord_eq]
    have := hmd.2.2.1
    omega

/-- `Jn/time`: "The Julian day n (1 <= n <= 365). Leap days shall not be counted. That is, in
all years-including leap years-February 28 is day 59 and March 1 is day 60." Day `n` is the
`(m, dd)` whose common-year position `daysBeforeMonthTable m + dd` is `n`, in every year. -/
def JulianRuleMeaning : Prop :=
  ∀ (m dd h mi s year : Int), 1 ≤ m → m ≤ 12 → 1 ≤ dd → dd ≤ daysInMonthTable m →
    dayYearToEpochPy true (daysBeforeMonthTable m + dd) h mi s year =
      (ymd2ord year m dd - EPOCHORDINAL) * 86400 + (h * 3600 + mi * 60 + s)

theorem julianRuleMeaning_proven : JulianRuleMeaning := by
  intro m dd h mi s y hm1 hm2 hdd1 hdd2
  have ht := month_tables m hm1 hm2
  unfold dayYearToEpochPy
  simp only
  rw [postEpoch_eq, ymd2ord_eq]
  by_cases hm : m > 2
  · have : daysBeforeMonthTable m + dd ≥ 60 := by omega
    by_cases hl : isLeap y = true
    · simp only [this, hl, hm, and_self, ite_true]
      omega
    · simp only [hl, and_false, ite_false, Bool.false_eq_true]
      omega
  · have : ¬ (daysBeforeMonthTable m + dd ≥ 60) := by omega
    simp only [this, hm, false_and, and_false, ite_false]
    omega

/-- `n/time`: "The zero-based Julian day (0 <= n <= 365). Leap days shall be counted, and it
is possible to refer to February 29." Day `n` is `n` days after January 1, in both twins. -/
def ZeroBasedRuleMeaning : Prop :=
  ∀ (n h mi s year : Int), 0 ≤ n → n ≤ 365 → 1 ≤ year → year ≤ 9999 →
    dayYearToEpochPy false n h mi s year =
        (ymd2ord year 1 1 + n - EPOCHORDINAL) * 86400 + (h * 3600 + mi * 60 + s) ∧
    dayYearToTsC false n h mi s year =
        (ymd2ord year 1 1 + n - EPOCHORDINAL) * 86400 + (h * 3600 + mi * 60 + s)

/-- `10/0` in 2021 is January 10 in both twins, not January 11. -/
theorem zeroBasedRuleMeaning_refuted : ¬ ZeroBasedRuleMeaning := by
  intro hz
  have := (hz 10 0 0 0 2021 (by decide) (by decide) (by decide) (by decide)).1
  revert this
  decide

end PyLean.Datetime.Zone
