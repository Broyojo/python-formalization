import PyLean.Datetime.Calendar

/-!
Proleptic Gregorian ordinals: `fromordinal` and `toordinal` are inverse
bijections between valid dates and `1..MAXORDINAL`, and the C and Python
conversions agree. The proofs decompose `year - 1` into 400-, 100- and 4-year
cycles; the month search is checked over every day of a common and a leap
year.
-/

namespace PyLean.Datetime

open PyLean

/-! ### Month search, checked day by day -/

/-- Days in month `m` of a leap (`true`) or common year. -/
def dimL (leap : Bool) (m : Int) : Int := daysInMonthTable m + (if m = 2 ∧ leap then 1 else 0)

/-- Days before month `m`. -/
def dbmL (leap : Bool) (m : Int) : Int := daysBeforeMonthTable m + (if m > 2 ∧ leap then 1 else 0)

theorem daysInMonth_eq (y m : Int) : daysInMonth y m = dimL (isLeap y) m := by
  unfold daysInMonth dimL
  by_cases h : m = 2 ∧ isLeap y = true
  · obtain ⟨rfl, h2⟩ := h
    simp [h2, daysInMonthTable]
  · simp only [h, ite_false]
    simp

theorem daysBeforeMonth_eq (y m : Int) : daysBeforeMonth y m = dbmL (isLeap y) m := rfl

set_option maxRecDepth 100000 in
theorem monthDay_forward_table : ∀ leap : Bool, ∀ m : Fin 12, ∀ d : Fin 31,
    ((d : Nat) : Int) + 1 ≤ dimL leap ((m : Nat) + 1) →
    monthDayPy leap (dbmL leap ((m : Nat) + 1) + (d : Nat)) = (((m : Nat) : Int) + 1, ((d : Nat) : Int) + 1) ∧
    dbmL leap ((m : Nat) + 1) + (d : Nat) ≤ 364 + (if leap then 1 else 0) := by
  decide

set_option maxRecDepth 100000 in
theorem monthDay_backward_table : ∀ leap : Bool, ∀ k : Fin 366,
    ((k : Nat) : Int) ≤ 364 + (if leap then 1 else 0) →
    1 ≤ (monthDayPy leap (k : Nat)).1 ∧ (monthDayPy leap (k : Nat)).1 ≤ 12 ∧
    1 ≤ (monthDayPy leap (k : Nat)).2 ∧
    (monthDayPy leap (k : Nat)).2 ≤ dimL leap (monthDayPy leap (k : Nat)).1 ∧
    dbmL leap (monthDayPy leap (k : Nat)).1 + (monthDayPy leap (k : Nat)).2 - 1 = (k : Nat) := by
  decide

theorem monthDay_forward (leap : Bool) (m d : Int) (hm : 1 ≤ m ∧ m ≤ 12) (hd : 1 ≤ d ∧ d ≤ dimL leap m) :
    monthDayPy leap (dbmL leap m + d - 1) = (m, d) ∧ dbmL leap m + d - 1 ≤ 364 + (if leap then 1 else 0) := by
  have hdim : dimL leap m ≤ 31 := by
    have := monthDay_backward_table
    unfold dimL daysInMonthTable
    have : m.toNat - 0 < 13 := by omega
    rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
      m = 10 ∨ m = 11 ∨ m = 12) with h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst h <;> cases leap <;> decide
  have := monthDay_forward_table leap ⟨(m - 1).toNat, by omega⟩ ⟨(d - 1).toNat, by omega⟩
  simp only at this
  have e1 : (((m - 1).toNat : Nat) : Int) + 1 = m := by omega
  have e2 : (((d - 1).toNat : Nat) : Int) + 1 = d := by omega
  have e3 : (((d - 1).toNat : Nat) : Int) = d - 1 := by omega
  rw [e1, e2, e3] at this
  have := this (by omega)
  constructor
  · rw [← this.1]; congr 1; omega
  · omega

theorem monthDay_backward (leap : Bool) (k : Int) (h0 : 0 ≤ k) (h1 : k ≤ 364 + (if leap then 1 else 0)) :
    1 ≤ (monthDayPy leap k).1 ∧ (monthDayPy leap k).1 ≤ 12 ∧ 1 ≤ (monthDayPy leap k).2 ∧
    (monthDayPy leap k).2 ≤ dimL leap (monthDayPy leap k).1 ∧
    dbmL leap (monthDayPy leap k).1 + (monthDayPy leap k).2 - 1 = k := by
  have := monthDay_backward_table leap ⟨k.toNat, by split at h1 <;> omega⟩
  simp only at this
  have e : ((k.toNat : Nat) : Int) = k := by omega
  rw [e] at this
  exact this h1

/-! ### Cycle decomposition -/

theorem isLeap_decomp (q a b c : Int) (ha0 : 0 ≤ a) (ha1 : a < 4) (hb0 : 0 ≤ b) (hb1 : b < 25)
    (hc0 : 0 ≤ c) (hc1 : c < 4) :
    isLeap (400 * q + 100 * a + 4 * b + c + 1) = decide (c = 3 ∧ (b ≠ 24 ∨ a = 3)) := by
  unfold isLeap
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  omega

theorem daysBeforeYear_decomp (q a b c : Int) (ha0 : 0 ≤ a) (ha1 : a < 4) (hb0 : 0 ≤ b)
    (hb1 : b < 25) (hc0 : 0 ≤ c) (hc1 : c < 4) :
    daysBeforeYear (400 * q + 100 * a + 4 * b + c + 1) = 146097 * q + 36524 * a + 1461 * b + 365 * c := by
  simp only [daysBeforeYear]
  omega

/-- `_ord2ymd` on an ordinal given by its cycle decomposition. -/
theorem ord2ymd_decomp (q a b c doy : Int) (ha0 : 0 ≤ a) (ha1 : a < 4)
    (hb0 : 0 ≤ b) (hb1 : b < 25) (hc0 : 0 ≤ c) (hc1 : c < 4) (hd0 : 0 ≤ doy)
    (hd1 : doy ≤ 364 + (if c = 3 ∧ (b ≠ 24 ∨ a = 3) then 1 else 0)) :
    ord2ymd (146097 * q + 36524 * a + 1461 * b + 365 * c + doy + 1) =
      (400 * q + 100 * a + 4 * b + c + 1, monthDayPy (decide (c = 3 ∧ (b ≠ 24 ∨ a = 3))) doy) := by
  have h365 : monthDayPy true 365 = (12, 31) := by decide
  unfold ord2ymd DI400Y DI100Y DI4Y
  have e1 : (146097 * q + 36524 * a + 1461 * b + 365 * c + doy + 1 - 1) / 146097 = q := by omega
  have e2 : (146097 * q + 36524 * a + 1461 * b + 365 * c + doy + 1 - 1) % 146097 =
      36524 * a + 1461 * b + 365 * c + doy := by omega
  simp only [e1, e2]
  by_cases hA : a = 3 ∧ b = 24 ∧ c = 3 ∧ doy = 365
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hA
    simp only [show (36524 * 3 + 1461 * 24 + 365 * 3 + 365 : Int) / 36524 = 4 by decide]
    simp [h365]
    omega
  · have f1 : (36524 * a + 1461 * b + 365 * c + doy) / 36524 = a := by split at hd1 <;> omega
    have f2 : (36524 * a + 1461 * b + 365 * c + doy) % 36524 = 1461 * b + 365 * c + doy := by
      split at hd1 <;> omega
    have f3 : (1461 * b + 365 * c + doy) / 1461 = b := by split at hd1 <;> omega
    have f4 : (1461 * b + 365 * c + doy) % 1461 = 365 * c + doy := by split at hd1 <;> omega
    simp only [f1, f2, f3, f4]
    by_cases hB : c = 3 ∧ doy = 365
    · obtain ⟨rfl, rfl⟩ := hB
      have hl : (b ≠ 24 ∨ a = 3) := by omega
      simp [hl, h365]
      omega
    · have g1 : (365 * c + doy) / 365 = c := by split at hd1 <;> omega
      have g2 : (365 * c + doy) % 365 = doy := by split at hd1 <;> omega
      simp only [g1, g2]
      have : ¬(c = 4 ∨ a = 4) := by omega
      simp only [this, ite_false]
      congr 1
      omega

/-- C `ord_to_ymd` on an ordinal given by its cycle decomposition. -/
theorem ordToYmdC_decomp (q a b c doy : Int) (hq : 0 ≤ q) (ha0 : 0 ≤ a) (ha1 : a < 4)
    (hb0 : 0 ≤ b) (hb1 : b < 25) (hc0 : 0 ≤ c) (hc1 : c < 4) (hd0 : 0 ≤ doy)
    (hd1 : doy ≤ 364 + (if c = 3 ∧ (b ≠ 24 ∨ a = 3) then 1 else 0)) :
    ordToYmdC (146097 * q + 36524 * a + 1461 * b + 365 * c + doy + 1) =
      ord2ymd (146097 * q + 36524 * a + 1461 * b + 365 * c + doy + 1) := by
  rw [ord2ymd_decomp q a b c doy ha0 ha1 hb0 hb1 hc0 hc1 hd0 hd1]
  have h365 : monthDayPy true 365 = (12, 31) := by decide
  have hmd : ∀ y k, monthDayC y (isLeap y) k = monthDayPy (isLeap y) k := by
    intro y k
    unfold monthDayC monthDayPy
    simp only [daysInMonth_eq, dimL]
  unfold ordToYmdC DI400Y DI100Y DI4Y
  simp (disch := omega) only [Int.tdiv_eq_ediv_of_nonneg, Int.tmod_eq_emod_of_nonneg]
  have e1 : (146097 * q + 36524 * a + 1461 * b + 365 * c + doy + 1 - 1) / 146097 = q := by omega
  have e2 : (146097 * q + 36524 * a + 1461 * b + 365 * c + doy + 1 - 1) % 146097 =
      36524 * a + 1461 * b + 365 * c + doy := by omega
  simp only [e1, e2]
  by_cases hA : a = 3 ∧ b = 24 ∧ c = 3 ∧ doy = 365
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hA
    simp only [show (36524 * 3 + 1461 * 24 + 365 * 3 + 365 : Int) / 36524 = 4 by decide]
    simp [h365]
    omega
  · have f1 : (36524 * a + 1461 * b + 365 * c + doy) / 36524 = a := by split at hd1 <;> omega
    have f2 : (36524 * a + 1461 * b + 365 * c + doy) % 36524 = 1461 * b + 365 * c + doy := by
      split at hd1 <;> omega
    have f3 : (1461 * b + 365 * c + doy) / 1461 = b := by split at hd1 <;> omega
    have f4 : (1461 * b + 365 * c + doy) % 1461 = 365 * c + doy := by split at hd1 <;> omega
    simp only [f1, f2, f3, f4]
    by_cases hB : c = 3 ∧ doy = 365
    · obtain ⟨rfl, rfl⟩ := hB
      have hl : (b ≠ 24 ∨ a = 3) := by omega
      simp [hl, h365]
      omega
    · have g1 : (365 * c + doy) / 365 = c := by split at hd1 <;> omega
      have g2 : (365 * c + doy) % 365 = doy := by split at hd1 <;> omega
      simp only [g1, g2]
      have : ¬(c = 4 ∨ a = 4) := by omega
      simp only [this, ite_false]
      have hy : q * 400 + 1 + a * 100 + b * 4 + c = 400 * q + 100 * a + 4 * b + c + 1 := by omega
      rw [hy, ← isLeap_decomp q a b c ha0 ha1 hb0 hb1 hc0 hc1, hmd]

/-- Every ordinal `n >= 1` has a cycle decomposition of the shape the lemmas
above expect. -/
theorem ord_decomp_exists (n : Int) (hn : 1 ≤ n) :
    ∃ q a b c doy, 0 ≤ q ∧ 0 ≤ a ∧ a < 4 ∧ 0 ≤ b ∧ b < 25 ∧ 0 ≤ c ∧ c < 4 ∧ 0 ≤ doy ∧
      doy ≤ 364 + (if c = 3 ∧ (b ≠ 24 ∨ a = 3) then 1 else 0) ∧
      n = 146097 * q + 36524 * a + 1461 * b + 365 * c + doy + 1 := by
  have hN : 0 ≤ n - 1 := by omega
  by_cases hA : (n - 1) % 146097 / 36524 = 4
  · refine ⟨(n - 1) / 146097, 3, 24, 3, 365, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, ?_, by omega⟩
    simp
  · by_cases hC : (n - 1) % 146097 % 36524 % 1461 / 365 = 4
    · refine ⟨(n - 1) / 146097, (n - 1) % 146097 / 36524, (n - 1) % 146097 % 36524 / 1461, 3, 365,
        by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_, by omega⟩
      have : (n - 1) % 146097 % 36524 / 1461 ≠ 24 := by omega
      simp [this]
    · refine ⟨(n - 1) / 146097, (n - 1) % 146097 / 36524, (n - 1) % 146097 % 36524 / 1461,
        (n - 1) % 146097 % 36524 % 1461 / 365, (n - 1) % 146097 % 36524 % 1461 % 365,
        by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_, by omega⟩
      split <;> omega

/-! ### Round trips -/

theorem ymdToOrdC_eq (y m d : Int) (hy : 1 ≤ y) : ymdToOrdC y m d = ymd2ord y m d := by
  unfold ymdToOrdC ymd2ord daysBeforeYearC daysBeforeYear
  simp (disch := omega) only [Int.tdiv_eq_ediv_of_nonneg]

/-- The decomposition of a date with `year >= 1`. -/
theorem ymd2ord_decomp (y m d : Int) (hy : 1 ≤ y) (hm : 1 ≤ m ∧ m ≤ 12)
    (hd : 1 ≤ d ∧ d ≤ daysInMonth y m) :
    ∃ q a b c, 0 ≤ q ∧ 0 ≤ a ∧ a < 4 ∧ 0 ≤ b ∧ b < 25 ∧ 0 ≤ c ∧ c < 4 ∧
      y = 400 * q + 100 * a + 4 * b + c + 1 ∧
      0 ≤ dbmL (isLeap y) m + d - 1 ∧
      dbmL (isLeap y) m + d - 1 ≤ 364 + (if c = 3 ∧ (b ≠ 24 ∨ a = 3) then 1 else 0) ∧
      ymd2ord y m d = 146097 * q + 36524 * a + 1461 * b + 365 * c + (dbmL (isLeap y) m + d - 1) + 1 ∧
      monthDayPy (decide (c = 3 ∧ (b ≠ 24 ∨ a = 3))) (dbmL (isLeap y) m + d - 1) = (m, d) := by
  refine ⟨(y - 1) / 400, (y - 1) % 400 / 100, (y - 1) % 100 / 4, (y - 1) % 4, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  have hyd : y = 400 * ((y - 1) / 400) + 100 * ((y - 1) % 400 / 100) + 4 * ((y - 1) % 100 / 4) +
      (y - 1) % 4 + 1 := by omega
  have hL := isLeap_decomp ((y - 1) / 400) ((y - 1) % 400 / 100) ((y - 1) % 100 / 4) ((y - 1) % 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [← hyd] at hL
  have hdy := daysBeforeYear_decomp ((y - 1) / 400) ((y - 1) % 400 / 100) ((y - 1) % 100 / 4) ((y - 1) % 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [← hyd] at hdy
  rw [daysInMonth_eq] at hd
  obtain ⟨hf1, hf2⟩ := monthDay_forward (isLeap y) m d hm hd
  have hif : (if isLeap y = true then (1 : Int) else 0) =
      (if (y - 1) % 4 = 3 ∧ ((y - 1) % 100 / 4 ≠ 24 ∨ (y - 1) % 400 / 100 = 3) then 1 else 0) := by
    rw [hL]; simp only [decide_eq_true_eq]
  rw [hif] at hf2
  rw [← hL]
  refine ⟨?_, ?_, ?_, hf1⟩
  · have : 0 ≤ dbmL (isLeap y) m := by
      unfold dbmL daysBeforeMonthTable
      rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
        m = 10 ∨ m = 11 ∨ m = 12) with h | h | h | h | h | h | h | h | h | h | h | h <;>
        subst h <;> cases isLeap y <;> decide
    omega
  · exact hf2
  · unfold ymd2ord; rw [hdy, daysBeforeMonth_eq]; omega

/-- `_ord2ymd(_ymd2ord(y, m, d)) == (y, m, d)` for every date with
`year >= 1`, and the C conversions agree. -/
theorem ord_roundtrip (y m d : Int) (hy : 1 ≤ y) (hm : 1 ≤ m ∧ m ≤ 12)
    (hd : 1 ≤ d ∧ d ≤ daysInMonth y m) :
    ord2ymd (ymd2ord y m d) = (y, m, d) ∧ ordToYmdC (ymdToOrdC y m d) = (y, m, d) := by
  obtain ⟨q, a, b, c, hq, ha0, ha1, hb0, hb1, hc0, hc1, hy', hd0, hd1, ho, hmd⟩ :=
    ymd2ord_decomp y m d hy hm hd
  have h1 : ord2ymd (ymd2ord y m d) = (y, m, d) := by
    rw [ho, ord2ymd_decomp q a b c _ ha0 ha1 hb0 hb1 hc0 hc1 hd0 hd1, hmd, hy']
  refine ⟨h1, ?_⟩
  rw [ymdToOrdC_eq y m d hy, ho, ordToYmdC_decomp q a b c _ hq ha0 ha1 hb0 hb1 hc0 hc1 hd0 hd1, ← ho, h1]

/-- For `n >= 1`, `_ord2ymd(n)` is a date with `year >= 1` whose ordinal is
`n`; C `ord_to_ymd` returns the same date. -/
theorem ord2ymd_spec (n : Int) (hn : 1 ≤ n) :
    1 ≤ (ord2ymd n).1 ∧ 1 ≤ (ord2ymd n).2.1 ∧ (ord2ymd n).2.1 ≤ 12 ∧ 1 ≤ (ord2ymd n).2.2 ∧
    (ord2ymd n).2.2 ≤ daysInMonth (ord2ymd n).1 (ord2ymd n).2.1 ∧
    ymd2ord (ord2ymd n).1 (ord2ymd n).2.1 (ord2ymd n).2.2 = n ∧ ordToYmdC n = ord2ymd n := by
  obtain ⟨q, a, b, c, doy, hq, ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1, rfl⟩ := ord_decomp_exists n hn
  rw [ordToYmdC_decomp q a b c doy hq ha0 ha1 hb0 hb1 hc0 hc1 hd0 hd1,
    ord2ymd_decomp q a b c doy ha0 ha1 hb0 hb1 hc0 hc1 hd0 hd1]
  simp only
  have hL := isLeap_decomp q a b c ha0 ha1 hb0 hb1 hc0 hc1
  have hdy := daysBeforeYear_decomp q a b c ha0 ha1 hb0 hb1 hc0 hc1
  have hb := monthDay_backward (decide (c = 3 ∧ (b ≠ 24 ∨ a = 3))) doy hd0 (by simpa using hd1)
  rw [daysInMonth_eq, hL]
  refine ⟨by omega, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, ?_, trivial⟩
  unfold ymd2ord
  rw [hdy, daysBeforeMonth_eq, hL]
  omega

end PyLean.Datetime
