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

/-- `PyLong_AsInt` and `operator.index` agree on every argument that fits a C `int`. -/
theorem parseI_eq (a : Arg) (h : a.FitsC) : parseI a = pyIndex a := by
  match a, h with
  | .int n, h =>
    unfold Arg.FitsC fitsCInt at h
    simp only [parseI, pyIndex, asCInt, bind, Except.bind]
    rw [if_pos (by omega)]
  | .index (.ok (some n)), h =>
    unfold Arg.FitsC fitsCInt at h
    simp only [parseI, pyIndex, asCInt, bind, Except.bind]
    rw [if_pos (by omega)]
  | .index (.ok none), _ => rfl
  | .index (.error _), _ => rfl
  | .none_, _ => rfl
  | .bytes _, _ => rfl
  | .str _, _ => rfl
  | .tz _, _ => rfl
  | .float _, _ => rfl
  | .other, _ => rfl

theorem replArg_twin (old : Int) (o : Option Arg) (hfit : ∀ a, o = some a → a.FitsC)
    (hnone : o ≠ some .none_) :
    replKeep old o ≠ .none_ ∧ SameOutcome (pyIndex (replKeep old o)) (replConv old o) := by
  rcases o with _ | a
  · exact ⟨by simp [replKeep], sameOutcome_refl _⟩
  · have hf := hfit a rfl
    cases a with
    | none_ => exact absurd rfl hnone
    | _ =>
      simp only [replKeep, replConv]
      rw [parseI_eq _ hf]
      exact ⟨by simp, sameOutcome_refl _⟩

/-- `date.replace`: with every argument omitted, or every argument `None` in Python, it
returns the same date; and when no argument is an explicit `None`, the twins agree for all
int and other arguments (ints within C `int`): the same date, `TypeError` for a non-int, or
`ValueError` for an invalid date. -/
def DateReplace : Prop :=
  ∀ (y m d : Int) (ny nm nd : Option Arg), ValidDate y m d →
    dateReplacePy y m d none none none = .ok (y, m, d) ∧
    dateReplaceC y m d none none none = .ok (y, m, d) ∧
    dateReplacePy y m d (some .none_) (some .none_) (some .none_) = .ok (y, m, d) ∧
    ((∀ a, ny = some a ∨ nm = some a ∨ nd = some a → a.FitsC) →
      ny ≠ some .none_ → nm ≠ some .none_ → nd ≠ some .none_ →
      SameOutcome (dateReplacePy y m d ny nm nd) (dateReplaceC y m d ny nm nd))

theorem dateNewPy_noPickle (a b c : Arg) (hb : b ≠ .none_) :
    dateNewPy a b c = (do let y ← pyIndex a; let m ← pyIndex b; let d ← pyIndex c; checkDate y m d) := by
  cases a <;> simp [dateNewPy, checkDateFieldsArgPy, stateOf, hb]

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
  · obtain ⟨n1, s1⟩ := replArg_twin y ny (fun a hn => hfit a (Or.inl hn)) h1
    obtain ⟨n2, s2⟩ := replArg_twin m nm (fun a hn => hfit a (Or.inr (Or.inl hn))) h2
    obtain ⟨n3, s3⟩ := replArg_twin d nd (fun a hn => hfit a (Or.inr (Or.inr hn))) h3
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

/-! ### `date - x` -/

/-- `date - x` agrees between the twins for every valid right operand: a timedelta, a date,
a datetime or another object. -/
def DateSubTwins : Prop :=
  ∀ (a : Int × Int × Int) (x : SubOperand), ValidDate a.1 a.2.1 a.2.2 →
    (∀ y m d, (x = .date y m d ∨ x = .datetime y m d) → ValidDate y m d) →
    (∀ t, x = .delta t → t.Valid) →
    SameOutcome (binarySub (dateSubPy a.1 a.2.1 a.2.2 x)) (binarySub (dateSubC a.1 a.2.1 a.2.2 x))

/-- `date(2020, 1, 2) - datetime(2020, 1, 1)`: `isinstance(other, date)` holds for a
`datetime`, so Python returns `timedelta(days=1)`; C `date_subtract` returns `NotImplemented`
for any `datetime` operand and the subtraction raises `TypeError`. -/
theorem dateSubTwins_refuted : ¬DateSubTwins := by
  intro h
  have := h (2020, 1, 2) (.datetime 2020 1 1) (by decide)
    (by intro y m d hx; rcases hx with hx | hx <;> cases hx; decide) (by intro t ht; cases ht)
  exact not_sameOutcome_ok_err _ _ (.delta ⟨1, 0, 0⟩) (by decide) (by decide) this

theorem sameOutcome_map {α β : Type} (f : α → β) (x y : Py α) (h : SameOutcome x y) :
    SameOutcome (f <$> x) (f <$> y) := by
  cases x <;> cases y <;> simp_all [SameOutcome, Functor.map, Except.map]

/-- `date - x` for every right operand other than a `datetime`: the twins agree (the ordinal
difference for a date, the same date or `OverflowError` for a timedelta), and another
object is `NotImplemented` in both. -/
def DateSubOperand : Prop :=
  ∀ (a : Int × Int × Int) (x : SubOperand), ValidDate a.1 a.2.1 a.2.2 →
    (∀ y m d, x = .date y m d → ValidDate y m d) → (∀ t, x = .delta t → t.Valid) →
    (∀ y m d, x ≠ .datetime y m d) →
    SameOutcome (binarySub (dateSubPy a.1 a.2.1 a.2.2 x)) (binarySub (dateSubC a.1 a.2.1 a.2.2 x)) ∧
    (x = .other → dateSubPy a.1 a.2.1 a.2.2 x = none ∧ dateSubC a.1 a.2.1 a.2.2 x = none)

theorem dateSubOperand_proven : DateSubOperand := by
  intro a x ha hd ht hdt
  obtain ⟨y, m, d⟩ := a
  simp only at ha ⊢
  cases x with
  | delta t =>
    refine ⟨?_, fun h => by cases h⟩
    have := (dateSubtract_proven (y, m, d) (y, m, d) t ha ha (ht t rfl)).2.2
    simp only at this
    simp only [dateSubPy, dateSubC, binarySub]
    have e : ∀ r : Py (Int × Int × Int), (do let (y, m, d) ← r; return SubResult.date y m d) =
        (fun p : Int × Int × Int => SubResult.date p.1 p.2.1 p.2.2) <$> r := by
      intro r; cases r <;> rfl
    rw [e, e]
    exact sameOutcome_map _ _ _ this
  | date y2 m2 d2 =>
    refine ⟨?_, fun h => by cases h⟩
    have := dateSubtract_proven (y, m, d) (y2, m2, d2) ⟨0, 0, 0⟩ ha (hd y2 m2 d2 rfl) (by decide)
    simp only [dateSubPy, dateSubC, binarySub]
    rw [this.1, this.2.1]
    exact sameOutcome_refl _
  | datetime y2 m2 d2 => exact absurd rfl (hdt y2 m2 d2)
  | other => exact ⟨sameOutcome_refl _, fun _ => ⟨rfl, rfl⟩⟩

/-! ### `date.fromordinal` out of range -/

/-- `ord_decomp_exists` without the lower bound on `n`: the quotient by 400 years may be
negative. -/
theorem ord_decomp_any (n : Int) :
    ∃ q a b c doy, q = (n - 1) / 146097 ∧ 0 ≤ a ∧ a < 4 ∧ 0 ≤ b ∧ b < 25 ∧ 0 ≤ c ∧ c < 4 ∧ 0 ≤ doy ∧
      doy ≤ 364 + (if c = 3 ∧ (b ≠ 24 ∨ a = 3) then 1 else 0) ∧
      n = 146097 * q + 36524 * a + 1461 * b + 365 * c + doy + 1 := by
  by_cases hA : (n - 1) % 146097 / 36524 = 4
  · refine ⟨(n - 1) / 146097, 3, 24, 3, 365, rfl, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, ?_, by omega⟩
    simp
  · by_cases hC : (n - 1) % 146097 % 36524 % 1461 / 365 = 4
    · refine ⟨(n - 1) / 146097, (n - 1) % 146097 / 36524, (n - 1) % 146097 % 36524 / 1461, 3, 365,
        rfl, by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_, by omega⟩
      have : (n - 1) % 146097 % 36524 / 1461 ≠ 24 := by omega
      simp [this]
    · refine ⟨(n - 1) / 146097, (n - 1) % 146097 / 36524, (n - 1) % 146097 % 36524 / 1461,
        (n - 1) % 146097 % 36524 % 1461 / 365, (n - 1) % 146097 % 36524 % 1461 % 365,
        rfl, by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_, by omega⟩
      split <;> omega

theorem ord2ymd_year_nonpos (n : Int) (h : n ≤ 0) : (ord2ymd n).1 ≤ 0 := by
  obtain ⟨q, a, b, c, doy, hq, ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1, rfl⟩ := ord_decomp_any n
  rw [ord2ymd_decomp q a b c doy ha0 ha1 hb0 hb1 hc0 hc1 hd0 hd1]
  simp only
  omega

theorem ord2ymd_year_big (n : Int) (h : n > MAXORDINAL) : (ord2ymd n).1 > MAXYEAR := by
  obtain ⟨hy, hm1, hm2, hd1, hd2, ho, -⟩ := ord2ymd_spec n (by unfold MAXORDINAL at h; omega)
  apply Classical.byContradiction
  intro hc
  have hv : ValidDate (ord2ymd n).1 (ord2ymd n).2.1 (ord2ymd n).2.2 := by
    unfold ValidDate MINYEAR MAXYEAR; unfold MAXYEAR at hc; omega
  have := ymd2ord_range _ _ _ hv
  omega

/-- `date.fromordinal(n)` outside `1..date.max.toordinal()`: Python raises `ValueError` for
every such int (the documented refusal); C raises `ValueError` for every such C `int` and
`OverflowError` beyond it (gh-158778's class); for C ints the twins agree. -/
def FromordinalRange : Prop :=
  ∀ n : Int,
    ((n < 1 ∨ n > MAXORDINAL) → (fromordinalPy n).raises "ValueError") ∧
    (fitsCInt n → (n < 1 ∨ n > MAXORDINAL) → (fromordinalC n).raises "ValueError") ∧
    (¬ fitsCInt n → (fromordinalC n).raises "OverflowError") ∧
    (fitsCInt n → SameOutcome (fromordinalPy n) (fromordinalC n))

theorem fromordinalPy_range (n : Int) (h : n < 1 ∨ n > MAXORDINAL) : (fromordinalPy n).raises "ValueError" := by
  have e : fromordinalPy n = checkDate (ord2ymd n).1 (ord2ymd n).2.1 (ord2ymd n).2.2 := by
    unfold fromordinalPy; rfl
  rw [e]
  apply checkDate_err
  intro hv
  unfold ValidDate MINYEAR MAXYEAR at hv
  rcases h with h | h
  · have := ord2ymd_year_nonpos n (by omega); omega
  · have := ord2ymd_year_big n h; unfold MAXYEAR at this; omega

theorem fromordinalRange_proven : FromordinalRange := by
  intro n
  have pc : fitsCInt n → (n < 1 ∨ n > MAXORDINAL) → (fromordinalC n).raises "ValueError" := by
    intro hf h
    unfold fromordinalC
    rw [if_neg (not_not_intro hf)]
    by_cases h1 : n < 1
    · rw [if_pos h1]; exact ⟨_, rfl, rfl⟩
    · rw [if_neg h1]
      have hn : n > MAXORDINAL := by omega
      rw [(ord2ymd_spec n (by omega)).2.2.2.2.2.2]
      simp only [checkDateC_eq]
      exact fromordinalPy_range n (Or.inr hn)
  refine ⟨fromordinalPy_range n, pc, fun hf => ?_, fun hf => ?_⟩
  · unfold fromordinalC; rw [if_pos hf]; exact ⟨_, rfl, rfl⟩
  · by_cases hr : 1 ≤ n ∧ n ≤ MAXORDINAL
    · obtain ⟨y, m, d, -, -, e1, e2⟩ := toordinalFromordinal_proven n hr.1 hr.2
      rw [e1, e2]; exact sameOutcome_refl _
    · obtain ⟨e1, he1, c1⟩ := fromordinalPy_range n (by omega)
      obtain ⟨e2, he2, c2⟩ := pc hf (by omega)
      rw [he1, he2]; simp only [SameOutcome]; rw [c1, c2]

/-! ### `date.fromtimestamp` -/

/-- `date.fromtimestamp(t)` against C `date_fromtimestamp`, for every clock and argument:
`None` raises `TypeError` in Python whatever the clock (without the check at :1038-1039,
`time.localtime(None)` would give today), and in C from the timestamp conversion; otherwise
both take the date fields of `localtime` of the same `time_t` and check them, so they agree;
and a successful conversion gives the checked `localtime` fields. -/
def DateFromtimestamp : Prop :=
  ∀ (k : Clock) (t : Arg),
    (dateFromtimestampPy k .none_).raises "TypeError" ∧
    (dateFromtimestampC k .none_).raises "TypeError" ∧
    SameOutcome (dateFromtimestampPy k t) (dateFromtimestampC k t) ∧
    (t ≠ .none_ → ∀ y m d, (do let tt ← objectToTimeT k t; k.localtime tt) = .ok (y, m, d) →
      dateFromtimestampPy k t = checkDate y m d)

theorem dateFromtimestamp_proven : DateFromtimestamp := by
  intro k t
  refine ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ?_, fun hn y m d hl => ?_⟩
  · by_cases hn : t = .none_
    · subst hn
      simp [SameOutcome, PyExc.className, dateFromtimestampPy, dateFromtimestampC, objectToTimeT,
        bind, Except.bind]
    · have e : timeLocaltime k t = (do let tt ← objectToTimeT k t; k.localtime tt) := by
        cases t <;> first | exact absurd rfl hn | rfl
      unfold dateFromtimestampPy dateFromtimestampC
      rw [if_neg hn, e]
      cases h1 : objectToTimeT k t with
      | error e => exact sameOutcome_refl _
      | ok tt =>
        simp only [bind, Except.bind]
        cases h2 : k.localtime tt with
        | error e => exact sameOutcome_refl _
        | ok v =>
          obtain ⟨y, m, d⟩ := v
          simp only
          rw [checkDate_eq_C]
          exact sameOutcome_refl _
  · have e : timeLocaltime k t = (do let tt ← objectToTimeT k t; k.localtime tt) := by
      cases t <;> first | exact absurd rfl hn | rfl
    unfold dateFromtimestampPy
    rw [if_neg hn, e, hl]
    rfl

/-! ### `date.__new__` without a `None` second argument -/

theorem pyIndex_parseI (a : Arg) (h : a.FitsC) :
    SameOutcome (pyIndex a) (parseI a) := by
  rw [parseI_eq a h]; exact sameOutcome_refl _

/-- An argument whose `__index__`, if it has one, does not raise. -/
def Arg.NoRaise : Arg → Prop
  | .index (.error _) => False
  | _ => True

theorem pyIndex_none_err {β : Type} (x : Py Int) (f : Int → Py β) :
    (do let v ← x; let _ ← pyIndex .none_; f v).raises "TypeError" ∨ (∃ e, x = .error e) := by
  cases x with
  | error e => exact Or.inr ⟨e, rfl⟩
  | ok v => exact Or.inl ⟨_, rfl, rfl⟩

/-- `date(*args)` for every positional argument list whose second argument (if any) is not
`None`, whose ints (given or returned by `__index__`) fit a C `int`, and in which no
`__index__` raises: the twins agree, on the pickle state (one bytes or str argument), on
int fields (the same date or `ValueError`) and on every `TypeError` (a non-int field, a
missing field, too many arguments). With all three fields given, a raising `__index__`
propagates in both twins (`CheckDateFieldsIndex`); with fewer, `DateNewIndexMissing`
states the difference: Python runs `__index__` of the given fields before it reaches the
missing one, C counts the arguments first. -/
def DateNewArgs : Prop :=
  ∀ args : List Arg, (∀ a ∈ args, a.FitsC ∧ a.NoRaise) → (∀ b, args[1]? = some b → b ≠ .none_) →
    SameOutcome (dateCallPy args) (dateNewC args)

theorem pyIndex_err (a : Arg) (hn : a.NoRaise) (e : PyExc) (h : pyIndex a = .error e) :
    e.className = "TypeError" := by
  match a, hn with
  | .index (.error _), hn => exact absurd hn id
  | .index (.ok none), _ => simp [pyIndex] at h; subst h; rfl
  | .index (.ok (some _)), _ => simp [pyIndex] at h
  | .int _, _ => simp [pyIndex] at h
  | .none_, _ | .bytes _, _ | .str _, _ | .tz _, _ | .float _, _ | .other, _ =>
    simp [pyIndex] at h; subst h; rfl

theorem raises_typeError_three (a b : Arg) (ha : a.NoRaise) (hb : b.NoRaise) :
    (do let y ← pyIndex a; let m ← pyIndex b; let d ← pyIndex .none_; checkDate y m d).raises "TypeError" := by
  cases h1 : pyIndex a with
  | error e => exact ⟨e, by simp [bind, Except.bind], pyIndex_err a ha e h1⟩
  | ok y =>
    cases h2 : pyIndex b with
    | error e => exact ⟨e, by simp [bind, Except.bind, h2], pyIndex_err b hb e h2⟩
    | ok m => exact ⟨.typeError "~object cannot be interpreted as an integer",
        by simp [bind, Except.bind, h2, pyIndex], rfl⟩

theorem sameOutcome_typeErrors {α : Type} (x y : Py α) (hx : x.raises "TypeError") (hy : y.raises "TypeError") :
    SameOutcome x y := by
  obtain ⟨e1, h1, c1⟩ := hx
  obtain ⟨e2, h2, c2⟩ := hy
  rw [h1, h2]; simp only [SameOutcome]; rw [c1, c2]

theorem dateNewArgs_proven : DateNewArgs := by
  intro args hfit hsec
  match args, hfit, hsec with
  | [], _, _ =>
    apply sameOutcome_typeErrors
    · exact ⟨_, rfl, rfl⟩
    · exact ⟨_, rfl, rfl⟩
  | [a], hf, _ =>
    have hp : dateCallPy [a] = dateNewPy a .none_ .none_ := rfl
    rw [hp]
    cases a with
    | bytes bs =>
      by_cases hc : bs.length = 4 ∧ 1 ≤ bs.getD 2 0 ∧ bs.getD 2 0 ≤ 12
      · simp only [dateNewPy, dateNewC, stateOf, hc, true_and, and_self, ↓reduceIte]
        exact sameOutcome_refl _
      · apply sameOutcome_typeErrors
        · simp only [dateNewPy, stateOf, hc, and_false, ↓reduceIte]
          exact ⟨_, rfl, rfl⟩
        · simp only [dateNewC, stateOf, hc, ↓reduceIte]
          exact ⟨_, rfl, rfl⟩
    | str cs =>
      by_cases hc : cs.length = 4 ∧ 1 ≤ cs.getD 2 0 ∧ cs.getD 2 0 ≤ 12
      · simp only [dateNewPy, dateNewC, stateOf, hc, true_and, and_self, ↓reduceIte]
        exact sameOutcome_refl _
      · apply sameOutcome_typeErrors
        · simp only [dateNewPy, stateOf, hc, and_false, ↓reduceIte]
          exact ⟨_, rfl, rfl⟩
        · simp only [dateNewC, stateOf, hc, ↓reduceIte]
          exact ⟨_, rfl, rfl⟩
    | int n =>
      apply sameOutcome_typeErrors
      · exact ⟨_, rfl, rfl⟩
      · exact ⟨_, rfl, rfl⟩
    | none_ => exact sameOutcome_typeErrors _ _ ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩
    | tz t => exact sameOutcome_typeErrors _ _ ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩
    | other => exact sameOutcome_typeErrors _ _ ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩
    | float x => exact sameOutcome_typeErrors _ _ ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩
    | index r =>
      have hn := (hf (.index r) (by simp)).2
      apply sameOutcome_typeErrors
      · rcases r with e | (_ | n)
        · exact absurd hn id
        · exact ⟨_, rfl, rfl⟩
        · exact ⟨_, rfl, rfl⟩
      · exact ⟨_, rfl, rfl⟩
  | [a, b], hf, hs =>
    have hb : b ≠ .none_ := hs b rfl
    have hp : dateCallPy [a, b] = dateNewPy a b .none_ := rfl
    rw [hp, dateNewPy_noPickle a b .none_ hb]
    exact sameOutcome_typeErrors _ _
      (raises_typeError_three a b (hf a (by simp)).2 (hf b (by simp)).2) ⟨_, rfl, rfl⟩
  | [a, b, c], hf, hs =>
    have hb : b ≠ .none_ := hs b rfl
    have hp : dateCallPy [a, b, c] = dateNewPy a b c := rfl
    have hc : dateNewC [a, b, c] = (do
        let y ← parseI a; let m ← parseI b; let d ← parseI c; datetimeDateImplC y m d) := rfl
    rw [hp, dateNewPy_noPickle a b c hb, hc]
    refine sameOutcome_bind2 _ _ _ _ (pyIndex_parseI a (hf a (by simp)).1) (fun y => ?_)
    refine sameOutcome_bind2 _ _ _ _ (pyIndex_parseI b (hf b (by simp)).1) (fun m => ?_)
    refine sameOutcome_bind2 _ _ _ _ (pyIndex_parseI c (hf c (by simp)).1) (fun d => ?_)
    rw [datetimeDateImplC, checkDateC_eq]
    exact sameOutcome_refl _
  | a :: b :: c :: d :: rest, _, _ =>
    exact sameOutcome_typeErrors _ _ ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩

end PyLean.Datetime
