import PyLean.Datetime.MiscProps
import PyLean.Datetime.Twins

/-!
Properties of the helpers whose C twin is now mirrored from its own source
(`Datetime/Twins.lean`): the month table, the field checks, `_check_tzinfo_arg`,
`_build_struct_time`, `_divide_and_round`, `repr`, `replace`, the constructor's pickle test,
`date - datetime`, `fromordinal` out of range and `fromtimestamp`.
-/

namespace PyLean.Datetime

open PyLean

/-! ### `_days_in_month` -/

/-- `_days_in_month(y, m)` for `1 <= m <= 12` is the Gregorian month length: the table
31, 28/29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 with February 29 exactly in the years
divisible by 4 but not by 100, or by 400. It agrees with C `days_in_month` on every year
`0 <= y < 2**31` (C casts the year to `unsigned`), it is the step of `_days_before_month`,
and the twelve months make 365 or 366 days. Precondition: the `assert 1 <= month <= 12`. -/
def DaysInMonth : Prop :=
  ∀ y m : Int, 1 ≤ m → m ≤ 12 →
    daysInMonth y m =
      [31, (if y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0) then 29 else 28), 31, 30, 31, 30, 31, 31,
        30, 31, 30, 31].getD (m - 1).toNat 0 ∧
    (0 ≤ y → y < 2147483648 → daysInMonth y m = daysInMonthC y m) ∧
    (m < 12 → daysBeforeMonth y (m + 1) = daysBeforeMonth y m + daysInMonth y m) ∧
    daysBeforeMonth y 12 + daysInMonth y 12 =
      365 + (if y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0) then 1 else 0)

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

theorem leap_cond {α : Type} (y : Int) (a b : α) :
    (if y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0) then a else b) = (if isLeap y then a else b) := by
  have hL := isLeap_iff y
  by_cases hl : isLeap y = true
  · rw [if_pos (hL.mp hl), if_pos hl]
  · rw [if_neg (mt hL.mpr hl), if_neg hl]

theorem daysInMonth_proven : DaysInMonth := by
  intro y m h1 h2
  refine ⟨?_, fun h0 h1' => daysInMonth_C y m h0 h1' ⟨h1, h2⟩, fun h3 => ?_, ?_⟩
  · rw [leap_cond]
    unfold daysInMonth daysInMonthTable
    rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
      m = 10 ∨ m = 11 ∨ m = 12) with h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst h <;> cases isLeap y <;> decide
  · rw [daysBeforeMonth_eq, daysBeforeMonth_eq, daysInMonth_eq]
    exact dbmL_succ _ m ⟨h1, by omega⟩
  · rw [daysBeforeMonth_eq, daysInMonth_eq, dbmL_twelve, leap_cond]

/-! ### `_check_date_fields` and `_check_time_fields` -/

/-- `_check_date_fields` (after `_index`) against C `check_date_args`, for every int triple:
the same result and the same message, so the same check order (year, month, day). It
succeeds exactly on valid dates, returns the fields unchanged, and raises `ValueError`
otherwise. With `DaysInMonth`, `ValidDate` is the Gregorian calendar. -/
def CheckDateFields : Prop :=
  ∀ y m d : Int,
    checkDate y m d = (do checkDateArgsC y m d; return (y, m, d)) ∧
    ((∃ r, checkDate y m d = .ok r) ↔ ValidDate y m d) ∧
    (∀ r, checkDate y m d = .ok r → r = (y, m, d)) ∧
    (¬ ValidDate y m d → (checkDate y m d).raises "ValueError")

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

theorem checkDate_err (y m d : Int) (h : ¬ ValidDate y m d) : (checkDate y m d).raises "ValueError" := by
  unfold ValidDate at h
  unfold checkDate
  split
  · exact ⟨_, rfl, rfl⟩
  · split
    · exact ⟨_, rfl, rfl⟩
    · dsimp only
      split
      · exact ⟨_, rfl, rfl⟩
      · exfalso; apply h; unfold MINYEAR MAXYEAR at *; omega

theorem checkDateFields_proven : CheckDateFields := by
  intro y m d
  refine ⟨checkDate_eq_C y m d, ⟨fun ⟨r, hr⟩ => (checkDate_inv y m d r hr).1,
    fun hv => ⟨_, checkDate_ok y m d hv⟩⟩, fun r hr => (checkDate_inv y m d r hr).2,
    checkDate_err y m d⟩

/-- `_check_time_fields` (after `_index`) against C `check_time_args`, for every int
quintuple: the same result and message (so the order hour, minute, second, microsecond,
fold); it succeeds exactly when `0 <= hour <= 23`, `0 <= minute, second <= 59`,
`0 <= microsecond <= 999999` and `fold` is 0 or 1, and raises `ValueError` otherwise. -/
def CheckTimeFields : Prop :=
  ∀ h m s us fold : Int,
    checkTimeFieldsPy h m s us fold = (do checkTimeArgsC h m s us fold; return (h, m, s, us, fold)) ∧
    ((∃ r, checkTimeFieldsPy h m s us fold = .ok r) ↔
      (0 ≤ h ∧ h ≤ 23 ∧ 0 ≤ m ∧ m ≤ 59 ∧ 0 ≤ s ∧ s ≤ 59 ∧ 0 ≤ us ∧ us ≤ 999999 ∧
        (fold = 0 ∨ fold = 1))) ∧
    ((∃ r, checkTimeFieldsPy h m s us fold = .ok r) ∨ (checkTimeFieldsPy h m s us fold).raises "ValueError")

theorem checkTimeFields_proven : CheckTimeFields := by
  intro h m s us fold
  have main : checkTimeFieldsPy h m s us fold = (do checkTimeArgsC h m s us fold; return (h, m, s, us, fold)) := by
    unfold checkTimeFieldsPy checkTime checkTimeArgsC checkFold
    by_cases h1 : 0 ≤ h ∧ h ≤ 23
    · rw [if_neg (not_not_intro h1), if_neg (by omega : ¬(h < 0 ∨ h > 23))]
      by_cases h2 : 0 ≤ m ∧ m ≤ 59
      · rw [if_neg (not_not_intro h2), if_neg (by omega : ¬(m < 0 ∨ m > 59))]
        by_cases h3 : 0 ≤ s ∧ s ≤ 59
        · rw [if_neg (not_not_intro h3), if_neg (by omega : ¬(s < 0 ∨ s > 59))]
          by_cases h4 : 0 ≤ us ∧ us ≤ 999999
          · rw [if_neg (not_not_intro h4), if_neg (by omega : ¬(us < 0 ∨ us > 999999))]
            by_cases h5 : fold = 0 ∨ fold = 1
            · rw [if_pos h5, if_neg (by omega : ¬(fold ≠ 0 ∧ fold ≠ 1))]; rfl
            · rw [if_neg h5, if_pos (by omega : (fold ≠ 0 ∧ fold ≠ 1))]; rfl
          · rw [if_pos h4, if_pos (by omega : (us < 0 ∨ us > 999999))]; rfl
        · rw [if_pos h3, if_pos (by omega : (s < 0 ∨ s > 59))]; rfl
      · rw [if_pos h2, if_pos (by omega : (m < 0 ∨ m > 59))]; rfl
    · rw [if_pos h1, if_pos (by omega : (h < 0 ∨ h > 23))]; rfl
  refine ⟨main, ?_, ?_⟩ <;> rw [main] <;> unfold checkTimeArgsC
  · constructor
    · intro ⟨r, hr⟩
      split at hr
      · cases hr
      · split at hr
        · cases hr
        · split at hr
          · cases hr
          · split at hr
            · cases hr
            · split at hr
              · cases hr
              · omega
    · intro hv
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact ⟨_, rfl⟩
  · split
    · exact Or.inr ⟨_, rfl, rfl⟩
    · split
      · exact Or.inr ⟨_, rfl, rfl⟩
      · split
        · exact Or.inr ⟨_, rfl, rfl⟩
        · split
          · exact Or.inr ⟨_, rfl, rfl⟩
          · split
            · exact Or.inr ⟨_, rfl, rfl⟩
            · exact Or.inl ⟨_, rfl⟩

/-! ### `_check_tzinfo_arg` -/

/-- `_check_tzinfo_arg` and C `check_tzinfo_subclass` on every argument: `None` and a
`tzinfo` pass (the latter as itself), anything else raises `TypeError` in both twins (with
different messages: Python's `not 'int'`, C's `not type 'int'`). -/
def TzinfoArg : Prop :=
  ∀ a : Arg,
    SameOutcome (checkTzinfoArgPy a) (checkTzinfoSubclassC a) ∧
    checkTzinfoArgPy .none_ = .ok none ∧
    (∀ t, checkTzinfoArgPy (.tz t) = .ok (some t)) ∧
    ((∀ t, a ≠ .tz t) → a ≠ .none_ → (checkTzinfoArgPy a).raises "TypeError")

theorem tzinfoArg_proven : TzinfoArg := by
  intro a
  refine ⟨?_, rfl, fun _ => rfl, fun h1 h2 => ?_⟩
  · cases a <;> simp [checkTzinfoArgPy, checkTzinfoSubclassC, SameOutcome, PyExc.className]
  · cases a with
    | none_ => exact absurd rfl h2
    | tz t => exact absurd rfl (h1 t)
    | _ => exact ⟨_, rfl, rfl⟩

/-! ### `_build_struct_time` -/

/-- `_build_struct_time(y, m, d, hh, mm, ss, dstflag)` for a valid date and any ints
`hh, mm, ss, dstflag`: the tuple is `(y, m, d, hh, mm, ss, wday, yday, dstflag)` in that
order, with `wday` the weekday (Monday 0) in `0..6` and `yday` the day of the year in
`1..366`, and it is C `build_struct_time`'s argument tuple. -/
def BuildStructTime : Prop :=
  ∀ y m d hh mm ss dstflag : Int, ValidDate y m d →
    buildStructTimePy y m d hh mm ss dstflag = buildStructTimeArgsC y m d hh mm ss dstflag ∧
    buildStructTimePy y m d hh mm ss dstflag =
      [y, m, d, hh, mm, ss, dateWeekdayPy y m d, toordinal y m d - toordinal y 1 1 + 1, dstflag] ∧
    0 ≤ dateWeekdayPy y m d ∧ dateWeekdayPy y m d < 7 ∧
    1 ≤ toordinal y m d - toordinal y 1 1 + 1 ∧ toordinal y m d - toordinal y 1 1 + 1 ≤ 366

theorem buildStructTime_proven : BuildStructTime := by
  intro y m d hh mm ss dstflag h
  have p := validDate_pos _ _ _ h
  have r := ymd2ord_range y m d h
  have e : ymd2ord y m d - ymd2ord y 1 1 + 1 = daysBeforeMonth y m + d := by
    have : daysBeforeMonth y 1 = 0 := by unfold daysBeforeMonth daysBeforeMonthTable; simp
    unfold ymd2ord; omega
  have pa := (validDate_iff y m d).mp h
  have fa := (monthDay_forward (isLeap y) m d ⟨pa.2.2.1, pa.2.2.2.1⟩ ⟨pa.2.2.2.2.1, pa.2.2.2.2.2⟩).2
  have nb := dbmL_nonneg (isLeap y) m ⟨pa.2.2.1, pa.2.2.2.1⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold buildStructTimePy buildStructTimeArgsC
    rw [ymdToOrdC_eq y m d (by omega)]
    have : (ymd2ord y m d + 6).tmod 7 = (ymd2ord y m d + 6) % 7 := by
      rw [Int.tmod_eq_emod_of_nonneg (by omega)]
    rw [this]
  · unfold buildStructTimePy dateWeekdayPy toordinal; rw [e]
  · unfold dateWeekdayPy; omega
  · unfold dateWeekdayPy; omega
  · unfold toordinal; rw [e, daysBeforeMonth_eq]; omega
  · unfold toordinal; rw [e, daysBeforeMonth_eq]
    generalize isLeap y = L at fa ⊢
    cases L <;> simp only [Bool.false_eq_true, ↓reduceIte] at fa <;> omega

/-! ### Outcome helpers -/

theorem sameOutcome_bind2 {α β : Type} (x y : Py α) (f g : α → Py β) (hxy : SameOutcome x y)
    (h : ∀ v, SameOutcome (f v) (g v)) : SameOutcome (x >>= f) (y >>= g) := by
  cases x <;> cases y <;> simp_all [bind, Except.bind, SameOutcome]

theorem sameOutcome_of_eq {α : Type} {x y : Py α} (h : x = y) : SameOutcome x y := by
  subst h; exact sameOutcome_refl _

theorem not_sameOutcome_ok_err {α : Type} (x y : Py α) (v : α) (hx : x = .ok v) (hy : y.isOk = false) :
    ¬ SameOutcome x y := by
  subst hx; cases y <;> simp_all [SameOutcome, Except.isOk, Except.toBool]

/-! ### `date.__repr__` and `_get_class_module` -/

/-- `repr(date)` is the same text in both twins for every class. -/
def DateReprTwins : Prop :=
  ∀ (c : ReprCls) (y m d : Int), ValidDate y m d → dateReprClsPy c y m d = dateReprClsC c y m d

/-- A subclass nested in a class: Python prints `__qualname__` (`Outer.D(2020, 1, 1)`), C prints
`tp_name`, which is `__name__` (`D(2020, 1, 1)`). -/
theorem dateReprTwins_refuted : ¬DateReprTwins := by
  intro h
  have := h (.sub "__main__" "Outer.D" "D") 2020 1 1 (by decide)
  revert this
  decide

/-- `repr(date)` agrees between the twins for the base class (`datetime.date(...)`, the
`'datetime.'` branch of `_get_class_module`) and for every subclass whose `__qualname__` is
its `__name__` and whose module is not named `datetime` (the `''` branch). -/
def DateRepr : Prop :=
  ∀ (c : ReprCls) (y m d : Int),
    (c = .base ∨ ∃ mod name, c = .sub mod name name ∧ mod ≠ "datetime") →
    dateReprClsPy c y m d = dateReprClsC c y m d

theorem dateRepr_proven : DateRepr := by
  intro c y m d h
  rcases h with rfl | ⟨mod, name, rfl, hm⟩
  · rfl
  · simp [dateReprClsPy, dateReprClsC, getClassModule, hm, ReprCls.module, ReprCls.qualname,
      ReprCls.tpName]
    rfl

/-! ### `date.replace` -/

/-- `date.replace` agrees between the twins for every combination of omitted, `None`, int
and other arguments (ints within C `int`; beyond it is gh-158778's class). -/
def DateReplaceTwins : Prop :=
  ∀ (y m d : Int) (ny nm nd : Option Arg), ValidDate y m d →
    (∀ n, ny = some (.int n) ∨ nm = some (.int n) ∨ nd = some (.int n) → fitsCInt n) →
    SameOutcome (dateReplacePy y m d ny nm nd) (dateReplaceC y m d ny nm nd)

/-- `date(2020, 1, 1).replace(year=None)`: Python keeps the year, C's `int` converter raises
`TypeError`. -/
theorem dateReplaceTwins_refuted : ¬DateReplaceTwins := by
  intro h
  have := h 2020 1 1 (some .none_) none none (by decide) (by intro n hn; simp at hn)
  exact not_sameOutcome_ok_err _ _ (2020, 1, 1) (by decide) (by decide) this

theorem replArg_twin (old : Int) (o : Option Arg) (hfit : ∀ n, o = some (.int n) → fitsCInt n)
    (hnone : o ≠ some .none_) :
    replKeep old o ≠ .none_ ∧ SameOutcome (pyIndex (replKeep old o)) (replConv old o) := by
  rcases o with _ | a
  · exact ⟨by simp [replKeep], sameOutcome_refl _⟩
  · cases a with
    | none_ => exact absurd rfl hnone
    | int n =>
      have := hfit n rfl
      simp only [replKeep, replConv, pyIndex, parseI_int n this]
      exact ⟨by simp, sameOutcome_refl _⟩
    | _ => exact ⟨by simp [replKeep], by simp [replKeep, replConv, pyIndex, parseI, SameOutcome, PyExc.className]⟩

/-- `date.replace`: with every argument omitted, or every argument `None` in Python, it
returns the same date; and when no argument is an explicit `None`, the twins agree for all
int and other arguments (ints within C `int`): the same date, `TypeError` for a non-int, or
`ValueError` for an invalid date. -/
def DateReplace : Prop :=
  ∀ (y m d : Int) (ny nm nd : Option Arg), ValidDate y m d →
    dateReplacePy y m d none none none = .ok (y, m, d) ∧
    dateReplaceC y m d none none none = .ok (y, m, d) ∧
    dateReplacePy y m d (some .none_) (some .none_) (some .none_) = .ok (y, m, d) ∧
    ((∀ n, ny = some (.int n) ∨ nm = some (.int n) ∨ nd = some (.int n) → fitsCInt n) →
      ny ≠ some .none_ → nm ≠ some .none_ → nd ≠ some .none_ →
      SameOutcome (dateReplacePy y m d ny nm nd) (dateReplaceC y m d ny nm nd))

theorem dateNewPy_noPickle (a b c : Arg) (hb : b ≠ .none_) :
    dateNewPy a b c = (do let y ← pyIndex a; let m ← pyIndex b; let d ← pyIndex c; checkDate y m d) := by
  cases a <;> simp [dateNewPy, stateOf, hb]

theorem dateReplace_proven : DateReplace := by
  intro y m d ny nm nd h
  have p := validDate_pos _ _ _ h
  have hc : fitsCInt y ∧ fitsCInt m ∧ fitsCInt d := by unfold fitsCInt; omega
  refine ⟨?_, ?_, ?_, fun hfit h1 h2 h3 => ?_⟩
  · unfold dateReplacePy
    rw [dateNewPy_noPickle _ _ _ (by simp [replKeep])]
    simp only [replKeep, pyIndex, bind, Except.bind]
    exact checkDate_ok y m d h
  · unfold dateReplaceC
    simp only [replConv]
    have := checkDate_ok y m d h
    rw [checkDate_eq_C] at this
    simpa [bind, Except.bind, pure, Except.pure] using this
  · unfold dateReplacePy
    rw [dateNewPy_noPickle _ _ _ (by simp [replKeep])]
    simp only [replKeep, pyIndex, bind, Except.bind]
    exact checkDate_ok y m d h
  · obtain ⟨n1, s1⟩ := replArg_twin y ny (fun n hn => hfit n (Or.inl hn)) h1
    obtain ⟨n2, s2⟩ := replArg_twin m nm (fun n hn => hfit n (Or.inr (Or.inl hn))) h2
    obtain ⟨n3, s3⟩ := replArg_twin d nd (fun n hn => hfit n (Or.inr (Or.inr hn))) h3
    unfold dateReplacePy dateReplaceC
    rw [dateNewPy_noPickle _ _ _ n2]
    refine sameOutcome_bind2 _ _ _ _ s1 (fun a => ?_)
    refine sameOutcome_bind2 _ _ _ _ s2 (fun b => ?_)
    refine sameOutcome_bind2 _ _ _ _ s3 (fun c => ?_)
    rw [checkDate_eq_C]
    exact sameOutcome_refl _

/-! ### `date.__new__` -/

/-- `date(*args)` agrees between the twins for every positional argument list (ints within C
`int`): the pickle state, int fields, and the refusals. -/
def DateNewTwins : Prop :=
  ∀ args : List Arg, (∀ n, Arg.int n ∈ args → fitsCInt n) →
    SameOutcome (dateCallPy args) (dateNewC args)

/-- `date(b'\x07\xd0\x01\x01', None)`: Python's pickle test is `month is None`, so it
unpickles `date(2000, 1, 1)`; C's is "exactly one positional argument", so the state goes
to the `int` converter, which raises `TypeError`. -/
theorem dateNewTwins_refuted : ¬DateNewTwins := by
  intro h
  have := h [.bytes [7, 208, 1, 1], .none_] (by intro n hn; simp at hn)
  exact not_sameOutcome_ok_err _ _ (2000, 1, 1) (by decide) (by decide) this

end PyLean.Datetime
