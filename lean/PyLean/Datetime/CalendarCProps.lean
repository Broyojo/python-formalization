import PyLean.Datetime.CalendarProps

/-!
C `ymd_to_ord` from its helpers `days_before_year` and `days_before_month`, as written in
Modules/_datetimemodule.c (CPython 3.15.2), against Python's `_ymd2ord`.
-/

namespace PyLean.Datetime

open PyLean

theorem daysBeforeMonthC_eq (y m : Int) (h0 : 0 ≤ y) (h1 : y < 2147483648) (hm : 1 ≤ m ∧ m ≤ 12) :
    daysBeforeMonthC y m = daysBeforeMonth y m := by
  unfold daysBeforeMonthC daysBeforeMonth
  rw [isLeapC_eq y h0 h1]
  have : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 ∨ m = 12 := by
    omega
  rcases this with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    cases isLeap y <;> rfl

/-- C `ymd_to_ord` (:571-574) is Python's `_ymd2ord` (Py:68-75) for every year in
`1..9999` and month in `1..12` (the `date` type invariant; `days_before_year` asserts
`year >= 1`, :473, `days_before_month` `1 <= month <= 12`, :455-456): C's truncating
`y/4 - y/100 + y/400` (:475) is Python's floor division there, and C's table and `is_leap`
(the `unsigned` cast) give Python's `_days_before_month`. Outside the invariant they part:
`days_before_year(0)` is `-365` in C and `_days_before_year(0)` is `-366` in Python, which
unvalidated pickle state reaches (`date(b'\x00\x00\x01\x01').toordinal()` is `-364` in C and
`-365` in `_pydatetime` on CPython 3.15.2; pickle data is trusted, so this is not on record as
a defect). -/
def YmdToOrdTwins : Prop :=
  (∀ y m d : Int, 1 ≤ y → y ≤ 9999 → 1 ≤ m → m ≤ 12 →
    daysBeforeYearC y = daysBeforeYear y ∧ daysBeforeMonthC y m = daysBeforeMonth y m ∧
    ymdToOrdCSrc y m d = ymd2ord y m d ∧ ymdToOrdC y m d = ymdToOrdCSrc y m d) ∧
  daysBeforeYearC 0 = -365 ∧ daysBeforeYear 0 = -366

theorem ymdToOrdTwins_proven : YmdToOrdTwins := by
  refine ⟨fun y m d h1 h2 h3 h4 => ?_, by decide, by decide⟩
  have eY : daysBeforeYearC y = daysBeforeYear y := by
    unfold daysBeforeYearC daysBeforeYear
    simp (disch := omega) only [Int.tdiv_eq_ediv_of_nonneg]
  have eM := daysBeforeMonthC_eq y m (by omega) (by omega) ⟨h3, h4⟩
  refine ⟨eY, eM, ?_, ?_⟩
  · unfold ymdToOrdCSrc ymd2ord; rw [eY, eM]
  · unfold ymdToOrdC ymdToOrdCSrc; rw [eM]

end PyLean.Datetime
