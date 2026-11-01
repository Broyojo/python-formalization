import PyLean.CoreLibs.CalStat.CalLemmas

/-! Properties of the `calendar` mirror: the date arithmetic. Each `def` is one registry
entry. All of them hold for every int year, inside and outside `datetime`'s range, and for
every int `firstweekday`. -/

namespace PyLean.CoreLibs.CalStat

open PyLean PyLean.Datetime

/-! ## Leap years -/

theorem rangeI_snoc (a : Int) (n : Nat) :
    rangeI a (a + (n + 1 : Nat)) = rangeI a (a + n) ++ [a + n] := by
  have h1 : (a + ((n + 1 : Nat) : Int) - a).toNat = n + 1 := by omega
  have h2 : (a + (n : Int) - a).toNat = n := by omega
  simp only [rangeI, h1, h2, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem isleap_iff (y : Int) : isleap y = true ↔ (y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0)) :=
  isLeap_iff y

theorem leapdays_step (y z : Int) :
    leapdays y (z + 1) = leapdays y z + (if isleap z = true then 1 else 0) := by
  unfold leapdays
  by_cases h : isleap z = true
  · rw [if_pos h]; rw [isleap_iff] at h; simp only; omega
  · rw [if_neg h]; rw [isleap_iff] at h; simp only; omega

/-- `leapdays(y1, y2)` is "number of leap years in range [y1, y2)" (its docstring,
under the documented `y1 <= y2`), counted with `isleap`, for all ints. -/
def LeapdaysCount : Prop :=
  ∀ y1 y2 : Int, y1 ≤ y2 → leapdays y1 y2 = ((rangeI y1 y2).filter isleap).length

theorem leapdaysCount_proven : LeapdaysCount := by
  intro y1 y2 h
  obtain ⟨n, rfl⟩ : ∃ n : Nat, y2 = y1 + n := ⟨(y2 - y1).toNat, by omega⟩
  clear h
  induction n with
  | zero =>
    have : (y1 + ((0 : Nat) : Int) - y1).toNat = 0 := by omega
    simp only [rangeI, this]
    unfold leapdays
    simp
  | succ n ih =>
    rw [rangeI_snoc, List.filter_append, List.length_append]
    have : y1 + ((n + 1 : Nat) : Int) = y1 + n + 1 := by omega
    rw [this, leapdays_step, ih]
    by_cases h : isleap (y1 + n) = true
    · simp [h]
    · simp [h]

/-- The Gregorian cycle: `isleap` has period 400 and every 400 consecutive years hold 97
leap years. -/
def IsleapCycle : Prop :=
  ∀ y : Int, isleap (y + 400) = isleap y ∧ leapdays y (y + 400) = 97

theorem isleapCycle_proven : IsleapCycle := by
  intro y
  refine ⟨?_, ?_⟩
  · apply Bool.eq_iff_iff.mpr
    rw [isleap_iff, isleap_iff]; omega
  · unfold leapdays; simp only; omega

/-! ## `weekday` -/

theorem cIntArg_eq {x z : Int} (h : cIntArg x = .ok z) : z = x := by
  unfold cIntArg at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h; rfl

theorem checkDate_eq {y m d : Int} {r : Date} (h : checkDate y m d = .ok r) :
    ValidDate y m d ∧ r = (y, m, d) := by
  unfold checkDate at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only at h
      split at h
      · cases h
      · cases h
        unfold ValidDate
        refine ⟨by omega, rfl⟩

theorem mkDate_eq {y m d : Int} {r : Date} (h : mkDate y m d = .ok r) :
    ValidDate y m d ∧ r = (y, m, d) := by
  unfold mkDate at h
  simp only [bind, Except.bind] at h
  cases h1 : cIntArg y with
  | error e => rw [h1] at h; cases h
  | ok a =>
    rw [h1] at h
    cases h2 : cIntArg m with
    | error e => rw [h2] at h; cases h
    | ok b =>
      rw [h2] at h
      cases h3 : cIntArg d with
      | error e => rw [h3] at h; cases h
      | ok c =>
        rw [h3] at h
        rw [cIntArg_eq h1, cIntArg_eq h2, cIntArg_eq h3] at h
        exact checkDate_eq h

theorem weekday_eq {y m d w : Int} (h : weekday y m d = .ok w) :
    (1 ≤ m ∧ m ≤ 12) ∧ (1 ≤ d ∧ d ≤ daysInMonth y m) ∧ w = wk y m d := by
  unfold weekday at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases h1 : mkDate (yearMap y) m d with
  | error e => rw [h1] at h; cases h
  | ok r =>
    rw [h1] at h
    obtain ⟨hv, rfl⟩ := mkDate_eq h1
    simp only at h
    cases h
    unfold ValidDate at hv
    rw [daysInMonth_yearMap] at hv
    exact ⟨⟨hv.2.2.1, hv.2.2.2.1⟩, ⟨hv.2.2.2.2.1, hv.2.2.2.2.2⟩, wk_yearMap y m d⟩

theorem isLeap_cycle (y k : Int) : isLeap (y + 400 * k) = isLeap y := by
  apply Bool.eq_iff_iff.mpr
  rw [isLeap_iff, isLeap_iff]; omega

theorem wk_cycle (y m d k : Int) : wk (y + 400 * k) m d = wk y m d := by
  unfold wk ymd2ord
  rw [daysBeforeMonth_eq, daysBeforeMonth_eq, isLeap_cycle]
  generalize dbmL (isLeap y) m = z
  unfold daysBeforeYear
  simp only
  omega

/-- `weekday` is exact on the whole line of int years: shifting the year by any multiple of
400 keeps the result. This is what makes the substitution `2000 + year % 400` at
calendar.py:158-159 right, across both ends of `datetime`'s year range. -/
def WeekdayCycle : Prop :=
  ∀ y m d k w : Int, weekday y m d = .ok w →
    0 ≤ w ∧ w ≤ 6 ∧ weekday (y + 400 * k) m d = .ok w

theorem weekdayCycle_proven : WeekdayCycle := by
  intro y m d k w h
  obtain ⟨hm, hd, rfl⟩ := weekday_eq h
  refine ⟨by unfold wk; omega, by unfold wk; omega, ?_⟩
  have : daysInMonth (y + 400 * k) m = daysInMonth y m := by
    rw [daysInMonth_eq, daysInMonth_eq, isLeap_cycle]
  rw [weekday_ok _ _ _ hm (by omega), wk_cycle]

/-- Consecutive days have consecutive weekdays, also over month and year ends and
across year 0 and year 10000, where the substitution of calendar.py:159 changes the year. -/
def WeekdayNextDay : Prop :=
  ∀ y m d : Int, (1 ≤ m ∧ m ≤ 12) → 1 ≤ d → d ≤ daysInMonth y m →
    ∃ w, weekday y m d = .ok w ∧
      (d < daysInMonth y m → weekday y m (d + 1) = .ok ((w + 1) % 7)) ∧
      (d = daysInMonth y m →
        weekday (nextmonth y m).1 (nextmonth y m).2 1 = .ok ((w + 1) % 7))

theorem weekdayNextDay_proven : WeekdayNextDay := by
  intro y m d hm h1 h2
  refine ⟨wk y m d, weekday_ok y m d hm ⟨h1, h2⟩, ?_, ?_⟩
  · intro hlt
    rw [weekday_ok y m (d + 1) hm ⟨by omega, by omega⟩]
    have := ymd2ord_day y m d
    have := ymd2ord_day y m (d + 1)
    unfold wk
    exact congrArg Except.ok (by omega)
  · intro heq
    subst heq
    have hr := nextmonth_range y m hm
    have hb := daysInMonth_bounds (nextmonth y m).1 (nextmonth y m).2 hr
    rw [weekday_ok _ _ _ hr (by omega)]
    have := ord_next y m hm
    unfold wk
    exact congrArg Except.ok (by omega)

/-! ## `monthrange`, `_monthlen`, `_prevmonth`, `_nextmonth` -/

/-- `monthrange` returns the weekday of the 1st and the length (docstring: "0-6 ~ Mon-Sun",
"28-31"), for every int year; a month outside 1..12 raises `IllegalMonthError` with
the source's message, before anything else. `_monthlen` agrees on 1..12. -/
def MonthrangeSpec : Prop :=
  ∀ y m : Int,
    ((1 ≤ m ∧ m ≤ 12) →
      ∃ d1 n, monthrange y m = .ok (d1, n) ∧ 0 ≤ d1 ∧ d1 ≤ 6 ∧ 28 ≤ n ∧ n ≤ 31 ∧
        weekday y m 1 = .ok d1 ∧ monthlen y m = .ok n ∧ (m = 2 → (n = 29 ↔ isleap y = true))) ∧
    (¬(1 ≤ m ∧ m ≤ 12) →
      monthrange y m = .error (.named "IllegalMonthError" s!"bad month number {m}; must be 1-12"))

theorem monthrangeSpec_proven : MonthrangeSpec := by
  intro y m
  refine ⟨fun hm => ?_, fun hm => monthrange_err y m hm⟩
  have hb := daysInMonth_bounds y m hm
  refine ⟨wk y m 1, daysInMonth y m, monthrange_ok y m hm, by unfold wk; omega,
    by unfold wk; omega, hb.1, hb.2, weekday_ok y m 1 hm (by omega), monthlen_ok y m hm, ?_⟩
  intro h2
  subst h2
  rw [isleap_eq, daysInMonth_eq]
  cases isLeap y <;> decide

/-- Consecutive months chain: the first weekday of the next month is
`(first weekday + length) % 7` in every int year. -/
def MonthrangeChain : Prop :=
  ∀ y m d n d' n' : Int, (1 ≤ m ∧ m ≤ 12) → monthrange y m = .ok (d, n) →
    monthrange (nextmonth y m).1 (nextmonth y m).2 = .ok (d', n') → d' = (d + n) % 7

theorem monthrangeChain_proven : MonthrangeChain := by
  intro y m d n d' n' hm h1 h2
  rw [monthrange_ok y m hm] at h1
  rw [monthrange_ok _ _ (nextmonth_range y m hm)] at h2
  have e1 := Except.ok.inj h1
  have e2 := Except.ok.inj h2
  simp only [Prod.mk.injEq] at e1 e2
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨rfl, -⟩ := e2
  have := ord_next y m hm
  have := ymd2ord_day y m (daysInMonth y m)
  unfold wk
  omega

/-- `_prevmonth` and `_nextmonth` stay in 1..12 and undo each other. -/
def PrevNextMonth : Prop :=
  ∀ y m : Int, (1 ≤ m ∧ m ≤ 12) →
    (1 ≤ (nextmonth y m).2 ∧ (nextmonth y m).2 ≤ 12) ∧
    (1 ≤ (prevmonth y m).2 ∧ (prevmonth y m).2 ≤ 12) ∧
    prevmonth (nextmonth y m).1 (nextmonth y m).2 = (y, m) ∧
    nextmonth (prevmonth y m).1 (prevmonth y m).2 = (y, m)

theorem prevNextMonth_proven : PrevNextMonth := fun y m hm =>
  ⟨nextmonth_range y m hm, prevmonth_range y m hm, prev_next y m hm, next_prev y m hm⟩

/-! ## `Calendar` -/

theorem iterweekdays_fw (c : Calendar) :
    (c.firstweekday = 0 ∧ c.iterweekdays = [0, 1, 2, 3, 4, 5, 6]) ∨
    (c.firstweekday = 1 ∧ c.iterweekdays = [1, 2, 3, 4, 5, 6, 0]) ∨
    (c.firstweekday = 2 ∧ c.iterweekdays = [2, 3, 4, 5, 6, 0, 1]) ∨
    (c.firstweekday = 3 ∧ c.iterweekdays = [3, 4, 5, 6, 0, 1, 2]) ∨
    (c.firstweekday = 4 ∧ c.iterweekdays = [4, 5, 6, 0, 1, 2, 3]) ∨
    (c.firstweekday = 5 ∧ c.iterweekdays = [5, 6, 0, 1, 2, 3, 4]) ∨
    (c.firstweekday = 6 ∧ c.iterweekdays = [6, 0, 1, 2, 3, 4, 5]) := by
  have h := firstweekday_range c
  unfold Calendar.iterweekdays
  generalize c.firstweekday = fw at h ⊢
  rcases (by omega : fw = 0 ∨ fw = 1 ∨ fw = 2 ∨ fw = 3 ∨ fw = 4 ∨ fw = 5 ∨ fw = 6) with
    h | h | h | h | h | h | h <;> subst h <;> simp <;> decide

/-- For every int passed to `Calendar()`/`setfirstweekday`, `getfirstweekday` is the
value mod 7 and `iterweekdays` is the seven weekdays starting there. A first weekday
`fw + 7` is the same calendar as `fw`. -/
def FirstweekdayModulo : Prop :=
  ∀ c : Calendar, ∀ fw : Int,
    (c.setfirstweekday fw).firstweekday = fw % 7 ∧
    (0 ≤ c.firstweekday ∧ c.firstweekday ≤ 6) ∧
    c.iterweekdays.head? = some c.firstweekday ∧
    c.iterweekdays.Perm [0, 1, 2, 3, 4, 5, 6] ∧
    (Calendar.mk (fw + 7)).iterweekdays = (Calendar.mk fw).iterweekdays

theorem firstweekdayModulo_proven : FirstweekdayModulo := by
  intro c fw
  refine ⟨rfl, firstweekday_range c, ?_, ?_, ?_⟩
  · rcases iterweekdays_fw c with h | h | h | h | h | h | h <;> rw [h.1, h.2] <;> rfl
  · rcases iterweekdays_fw c with h | h | h | h | h | h | h <;> rw [h.2] <;> decide
  · have : (Calendar.mk (fw + 7)).firstweekday = (Calendar.mk fw).firstweekday := by
      unfold Calendar.firstweekday; simp only; omega
    unfold Calendar.iterweekdays
    rw [this]

theorem length_days (c : Calendar) (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) :
    (List.replicate (daysB c y m).toNat (0 : Int) ++ rangeI 1 (daysInMonth y m + 1) ++
      List.replicate (daysA c y m).toNat 0).length = (daysB c y m + daysInMonth y m + daysA c y m).toNat := by
  have := daysB_range c y m
  have := daysA_range c y m
  have := daysInMonth_bounds y m hm
  simp only [List.length_append, List.length_replicate, rangeI_length]
  omega

theorem weeks_length_bounds (c : Calendar) (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) :
    let L := daysB c y m + daysInMonth y m + daysA c y m
    L % 7 = 0 ∧ 28 ≤ L ∧ L ≤ 42 := by
  have := daysB_range c y m
  have := daysA_range c y m
  have := daysInMonth_bounds y m hm
  have := weeks_multiple c y m
  simp only
  omega

/-- `itermonthdays` covers complete weeks: its length is a multiple of 7 between 28 and
42, its non-zero entries are exactly `1..ndays`, for every int year and first weekday. -/
def ItermonthdaysShape : Prop :=
  ∀ (c : Calendar) (y m : Int), (1 ≤ m ∧ m ≤ 12) →
    ∃ l, c.itermonthdays y m = .ok l ∧ l.length % 7 = 0 ∧ 28 ≤ l.length ∧ l.length ≤ 42 ∧
      l.filter (· != 0) = rangeI 1 (daysInMonth y m + 1)

theorem itermonthdaysShape_proven : ItermonthdaysShape := by
  intro c y m hm
  refine ⟨_, itermonthdays_ok c y m hm, ?_⟩
  have hl := length_days c y m hm
  have hb := weeks_length_bounds c y m hm
  simp only at hb
  rw [hl]
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [List.filter_append, List.filter_append]
  have h1 : ∀ n : Nat, (List.replicate n (0 : Int)).filter (· != 0) = [] := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ]
  rw [h1, h1]
  simp only [List.nil_append, List.append_nil]
  apply List.filter_eq_self.mpr
  intro a ha
  simp only [rangeI, List.mem_map, List.mem_range] at ha
  obtain ⟨i, _, rfl⟩ := ha
  simp only [bne_iff_ne, ne_eq]
  omega

/-- The projection of `days3` onto `itermonthdays`. -/
def dayIn (y m : Int) (t : Date) : Int := if t.1 = y ∧ t.2.1 = m then t.2.2 else 0

theorem map_rangeI_const {β : Type} (a b : Int) (v : β) (f : Int → β) (h : ∀ x, f x = v) :
    (rangeI a b).map f = List.replicate (b - a).toNat v := by
  simp only [rangeI, List.map_map]
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map, List.getElem?_range', List.getElem?_replicate]
  by_cases hi : i < (b - a).toNat
  · simp [hi, h]
  · simp [hi]

/-- `itermonthdays` is `itermonthdays3` with the adjacent months blanked out. -/
theorem days_eq_map (c : Calendar) (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) :
    List.replicate (daysB c y m).toNat (0 : Int) ++ rangeI 1 (daysInMonth y m + 1) ++
      List.replicate (daysA c y m).toNat 0 = (days3 c y m).map (dayIn y m) := by
  have hB := daysB_range c y m
  have hA := daysA_range c y m
  unfold days3
  simp only [List.map_append, List.map_map, List.append_assoc]
  have hp : ∀ x : Int, (dayIn y m ∘ fun d => (((prevmonth y m).1, (prevmonth y m).2, d) : Date)) x = 0 := by
    intro x
    simp only [Function.comp, dayIn, prevmonth]
    split <;> rename_i h1 <;> split <;> simp_all <;> omega
  have hn : ∀ x : Int, (dayIn y m ∘ fun d => (((nextmonth y m).1, (nextmonth y m).2, d) : Date)) x = 0 := by
    intro x
    simp only [Function.comp, dayIn, nextmonth]
    split <;> rename_i h1 <;> split <;> simp_all <;> omega
  have hs : ∀ x : Int, (dayIn y m ∘ fun d => ((y, m, d) : Date)) x = x := by
    intro x; simp [Function.comp, dayIn]
  rw [map_rangeI_const _ _ _ _ hp, map_rangeI_const _ _ _ _ hn]
  have e1 : (daysInMonth (prevmonth y m).1 (prevmonth y m).2 + 1 -
      (daysInMonth (prevmonth y m).1 (prevmonth y m).2 + 1 - daysB c y m)).toNat =
      (daysB c y m).toNat := by omega
  have e2 : (daysA c y m + 1 - 1).toNat = (daysA c y m).toNat := by omega
  rw [e1, e2]
  congr 2
  simp only [rangeI, List.map_map]
  apply List.map_congr_left
  intro a _
  simp [dayIn]

/-- `itermonthdays` agrees with `itermonthdays3`: an entry is the day number when
the triple lies in the requested month and 0 otherwise (the two docstrings), for every int
year and first weekday. -/
def ItermonthdaysVs3 : Prop :=
  ∀ (c : Calendar) (y m : Int), (1 ≤ m ∧ m ≤ 12) →
    ∃ l3, c.itermonthdays3 y m = .ok l3 ∧
      c.itermonthdays y m = .ok (l3.map (fun t => if t.1 = y ∧ t.2.1 = m then t.2.2 else 0))

theorem itermonthdaysVs3_proven : ItermonthdaysVs3 := by
  intro c y m hm
  refine ⟨_, itermonthdays3_ok c y m hm, ?_⟩
  rw [itermonthdays_ok c y m hm, days_eq_map c y m hm]
  rfl

/-- `itermonthdays2` pairs each day with its true weekday: for every int year and first
weekday, a non-zero day `d` comes with `wd = weekday(y, m, d)`; every `wd` is in 0..6. -/
def Itermonthdays2Weekday : Prop :=
  ∀ (c : Calendar) (y m : Int), (1 ≤ m ∧ m ≤ 12) →
    ∃ l, c.itermonthdays2 y m = .ok l ∧
      ∀ d wd, (d, wd) ∈ l → 0 ≤ wd ∧ wd ≤ 6 ∧ (d ≠ 0 → weekday y m d = .ok wd)

theorem itermonthdays2Weekday_proven : Itermonthdays2Weekday := by
  intro c y m hm
  refine ⟨_, itermonthdays2_ok c y m hm, ?_⟩
  intro d wd hm2
  simp only [List.mem_map, Prod.mk.injEq] at hm2
  obtain ⟨⟨i, x⟩, hp, rfl, rfl⟩ := hm2
  simp only at hp ⊢
  obtain ⟨j, rfl, hj⟩ := mem_enumFrom.mp hp
  refine ⟨by omega, by omega, ?_⟩
  intro hx
  rw [days_eq_map c y m hm, List.getElem?_map] at hj
  cases ht : (days3 c y m)[j]? with
  | none => rw [ht] at hj; cases hj
  | some t =>
    rw [ht] at hj
    simp only [Option.map_some, Option.some.injEq] at hj
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := days3_entry c y m hm j t ht
    unfold dayIn at hj
    split at hj
    · rename_i hc
      obtain ⟨t1, t2, t3⟩ := t
      simp only at hc h1 h2 h3 h4 h5 hj
      obtain ⟨rfl, rfl⟩ := hc
      subst hj
      rw [weekday_ok _ _ _ hm ⟨h3, h4⟩, h5]
    · subst hj; exact absurd rfl hx

/-- `itermonthdays4` gives the true weekday for all its entries, also the ones of the
adjacent months and the ones outside `datetime`'s year range ("Can be used for dates outside
of datetime.date range"), and `itermonthdays3` enumerates valid days of valid months. -/
def Itermonthdays4Weekday : Prop :=
  ∀ (c : Calendar) (y m : Int), (1 ≤ m ∧ m ≤ 12) →
    ∃ l, c.itermonthdays4 y m = .ok l ∧
      ∀ y' m' d' wd, (y', m', d', wd) ∈ l →
        (1 ≤ m' ∧ m' ≤ 12) ∧ 1 ≤ d' ∧ d' ≤ daysInMonth y' m' ∧ weekday y' m' d' = .ok wd

theorem itermonthdays4Weekday_proven : Itermonthdays4Weekday := by
  intro c y m hm
  refine ⟨_, itermonthdays4_ok c y m hm, ?_⟩
  intro y' m' d' wd hmem
  simp only [List.mem_map, Prod.mk.injEq] at hmem
  obtain ⟨⟨i, t⟩, hp, rfl, rfl, rfl, rfl⟩ := hmem
  obtain ⟨j, rfl, hj⟩ := mem_enumFrom.mp hp
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := days3_entry c y m hm j t hj
  simp only
  refine ⟨⟨h1, h2⟩, h3, h4, ?_⟩
  rw [weekday_ok _ _ _ ⟨h1, h2⟩ ⟨h3, h4⟩, h5]
  simp

/-- `itermonthdays3` walks consecutive calendar days, in complete weeks, starting on the
configured first weekday. -/
def Itermonthdays3Consecutive : Prop :=
  ∀ (c : Calendar) (y m : Int), (1 ≤ m ∧ m ≤ 12) →
    ∃ l, c.itermonthdays3 y m = .ok l ∧ l.length % 7 = 0 ∧
      (∀ j t t', l[j]? = some t → l[j + 1]? = some t' →
        ymd2ord t'.1 t'.2.1 t'.2.2 = ymd2ord t.1 t.2.1 t.2.2 + 1) ∧
      (∀ t, l[0]? = some t → weekday t.1 t.2.1 t.2.2 = .ok c.firstweekday)

theorem itermonthdays3Consecutive_proven : Itermonthdays3Consecutive := by
  intro c y m hm
  refine ⟨_, itermonthdays3_ok c y m hm, ?_, ?_, ?_⟩
  · have h := congrArg List.length (days_eq_map c y m hm)
    rw [length_days c y m hm, List.length_map] at h
    have hb := weeks_length_bounds c y m hm
    simp only at hb
    rw [← h]
    omega
  · intro j t t' h1 h2
    have e1 := (days3_entry c y m hm j t h1).2.2.2.2.2
    have e2 := (days3_entry c y m hm (j + 1) t' h2).2.2.2.2.2
    omega
  · intro t ht
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := days3_entry c y m hm 0 t ht
    rw [weekday_ok _ _ _ ⟨h1, h2⟩ ⟨h3, h4⟩, h5]
    have := firstweekday_range c
    exact congrArg Except.ok (by omega)

/-- `itermonthdates` is `itermonthdays3` as far as `date` allows: it equals the triples when
all years are in `1..9999` and raises otherwise, so the difference of the two iterators
is exactly the documented `datetime.date` restriction. -/
def ItermonthdatesRestricted : Prop :=
  ∀ (c : Calendar) (y m : Int) (l : List Date), (1 ≤ m ∧ m ≤ 12) → c.itermonthdays3 y m = .ok l →
    ((∀ t ∈ l, 1 ≤ t.1 ∧ t.1 ≤ 9999) → c.itermonthdates y m = .ok l) ∧
    ((∃ t ∈ l, ¬(1 ≤ t.1 ∧ t.1 ≤ 9999)) → ∃ e, c.itermonthdates y m = .error e)

theorem mem_days3 {c : Calendar} {y m : Int} (hm : 1 ≤ m ∧ m ≤ 12) {t : Date}
    (ht : t ∈ days3 c y m) :
    1 ≤ t.2.1 ∧ t.2.1 ≤ 12 ∧ 1 ≤ t.2.2 ∧ t.2.2 ≤ daysInMonth t.1 t.2.1 := by
  obtain ⟨j, hj⟩ := List.getElem?_of_mem ht
  obtain ⟨h1, h2, h3, h4, -⟩ := days3_entry c y m hm j t hj
  exact ⟨h1, h2, h3, h4⟩

theorem itermonthdatesRestricted_proven : ItermonthdatesRestricted := by
  intro c y m l hm hl
  rw [itermonthdays3_ok c y m hm] at hl
  have e := Except.ok.inj hl
  subst e
  have hunf : c.itermonthdates y m = mkDates (days3 c y m) := by
    unfold Calendar.itermonthdates
    rw [itermonthdays3_ok c y m hm]
    rfl
  rw [hunf]
  constructor
  · intro hall
    have : mkDates (days3 c y m) = .ok ((days3 c y m).map id) := by
      unfold mkDates
      apply mapM_ok
      intro t ht
      obtain ⟨h1, h2, h3, h4⟩ := mem_days3 hm ht
      have hy := hall t ht
      have := mkDate_ok t.1 t.2.1 t.2.2 (by unfold ValidDate MINYEAR MAXYEAR; omega)
      simpa using this
    simpa using this
  · rintro ⟨t, ht, hbad⟩
    unfold mkDates
    apply mapM_error _ _ t ht
    cases hr : mkDate t.1 t.2.1 t.2.2 with
    | error e => exact ⟨e, rfl⟩
    | ok r =>
      have := (mkDate_eq hr).1
      unfold ValidDate MINYEAR MAXYEAR at this
      omega

theorem chunk7 {α : Type} (l : List α) (h1 : l.length % 7 = 0) (h2 : 28 ≤ l.length)
    (h3 : l.length ≤ 42) :
    let w := chunks 7 l
    4 ≤ w.length ∧ w.length ≤ 6 ∧ (∀ r ∈ w, r.length = 7) ∧ w.flatten = l := by
  have hd : 7 ∣ l.length := Nat.dvd_of_mod_eq_zero h1
  have hl := chunksGo_length 7 (by decide) l.length l (Nat.le_refl _) hd
  have hf := chunksGo_full 7 (by decide) l.length l (Nat.le_refl _) hd
  simp only [chunks]
  refine ⟨by omega, by omega, hf, chunks_flatten 7 (by decide) l⟩

/-- The month matrices of `monthdayscalendar` and `monthdays2calendar` have 4 to 6
weeks of exactly 7 entries, and flatten to the iterators; for any year and first weekday. -/
def MonthMatrices : Prop :=
  ∀ (c : Calendar) (y m : Int), (1 ≤ m ∧ m ≤ 12) →
    (∃ w, c.monthdayscalendar y m = .ok w ∧ 4 ≤ w.length ∧ w.length ≤ 6 ∧
      (∀ r ∈ w, r.length = 7) ∧ c.itermonthdays y m = .ok w.flatten) ∧
    (∃ w, c.monthdays2calendar y m = .ok w ∧ 4 ≤ w.length ∧ w.length ≤ 6 ∧
      (∀ r ∈ w, r.length = 7) ∧ c.itermonthdays2 y m = .ok w.flatten)

theorem monthdayscalendar_ok (c : Calendar) (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) :
    ∃ l, c.itermonthdays y m = .ok l ∧ c.monthdayscalendar y m = .ok (chunks 7 l) ∧
      l.length % 7 = 0 ∧ 28 ≤ l.length ∧ l.length ≤ 42 := by
  have hl := length_days c y m hm
  have hb := weeks_length_bounds c y m hm
  simp only at hb
  refine ⟨_, itermonthdays_ok c y m hm, ?_, ?_⟩
  · unfold Calendar.monthdayscalendar
    rw [itermonthdays_ok c y m hm]
    rfl
  · rw [hl]; omega

theorem monthdays2calendar_ok (c : Calendar) (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) :
    ∃ l, c.itermonthdays2 y m = .ok l ∧ c.monthdays2calendar y m = .ok (chunks 7 l) ∧
      l.length % 7 = 0 ∧ 28 ≤ l.length ∧ l.length ≤ 42 := by
  have hl := length_days c y m hm
  have hb := weeks_length_bounds c y m hm
  simp only at hb
  refine ⟨_, itermonthdays2_ok c y m hm, ?_, ?_⟩
  · unfold Calendar.monthdays2calendar
    rw [itermonthdays2_ok c y m hm]
    rfl
  · simp only [List.length_map, enumFrom, List.length_zipIdx]
    rw [hl]; omega

theorem monthMatrices_proven : MonthMatrices := by
  intro c y m hm
  constructor
  · obtain ⟨l, h1, h2, h3, h4, h5⟩ := monthdayscalendar_ok c y m hm
    obtain ⟨a, b, d, e⟩ := chunk7 l h3 h4 h5
    exact ⟨_, h2, a, b, d, by rw [e, h1]⟩
  · obtain ⟨l, h1, h2, h3, h4, h5⟩ := monthdays2calendar_ok c y m hm
    obtain ⟨a, b, d, e⟩ := chunk7 l h3 h4 h5
    exact ⟨_, h2, a, b, d, by rw [e, h1]⟩

/-- `monthdatescalendar`: whenever it succeeds, weeks have 7 entries and they flatten
to `itermonthdates`. -/
def MonthDatesMatrix : Prop :=
  ∀ (c : Calendar) (y m : Int) (l : List Date), (1 ≤ m ∧ m ≤ 12) → c.itermonthdates y m = .ok l →
    ∃ w, c.monthdatescalendar y m = .ok w ∧ (∀ r ∈ w, r.length = 7) ∧ w.flatten = l ∧
      4 ≤ w.length ∧ w.length ≤ 6

theorem mapM_length {α β : Type} (f : α → Py β) (l : List α) (r : List β)
    (h : l.mapM f = .ok r) : r.length = l.length := by
  induction l generalizing r with
  | nil =>
    simp only [List.mapM_nil] at h
    cases h; rfl
  | cons a as ih =>
    simp only [List.mapM_cons] at h
    cases h1 : f a with
    | error e => rw [h1] at h; cases h
    | ok v =>
      rw [h1] at h
      cases h2 : as.mapM f with
      | error e => rw [h2] at h; cases h
      | ok vs =>
        rw [h2] at h
        cases h
        simp [ih vs h2]

theorem monthDatesMatrix_proven : MonthDatesMatrix := by
  intro c y m l hm hl
  have hunf : c.itermonthdates y m = mkDates (days3 c y m) := by
    unfold Calendar.itermonthdates
    rw [itermonthdays3_ok c y m hm]
    rfl
  have hlen : l.length = (days3 c y m).length := by
    rw [hunf] at hl
    exact mapM_length _ _ _ hl
  have hd := congrArg List.length (days_eq_map c y m hm)
  rw [length_days c y m hm, List.length_map] at hd
  have hb := weeks_length_bounds c y m hm
  simp only at hb
  obtain ⟨a, b, d, e⟩ := chunk7 l (by omega) (by omega) (by omega)
  refine ⟨_, ?_, d, e, a, b⟩
  unfold Calendar.monthdatescalendar
  rw [hl]
  rfl

theorem mem_months12 {m : Int} (h : m ∈ months12) : 1 ≤ m ∧ m ≤ 12 := by
  simp only [months12, List.mem_cons, List.not_mem_nil, or_false] at h
  omega

theorem mapM_get {α β : Type} (f : α → Py β) (l : List α) (r : List β)
    (h : l.mapM f = .ok r) (i : Nat) (x : β) (hi : r[i]? = some x) :
    ∃ a, l[i]? = some a ∧ f a = .ok x := by
  induction l generalizing r i with
  | nil =>
    simp only [List.mapM_nil] at h
    cases h; simp at hi
  | cons a as ih =>
    simp only [List.mapM_cons] at h
    cases h1 : f a with
    | error e => rw [h1] at h; cases h
    | ok v =>
      rw [h1] at h
      cases h2 : as.mapM f with
      | error e => rw [h2] at h; cases h
      | ok vs =>
        rw [h2] at h
        cases h
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi
          exact ⟨a, rfl, h1⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hi
          obtain ⟨b, hb, hfb⟩ := ih vs h2 i hi
          exact ⟨b, by simpa using hb, hfb⟩

theorem chunksGo_le {α : Type} (k : Nat) :
    ∀ (f : Nat) (l : List α), ∀ c ∈ chunksGo k f l, c.length ≤ k := by
  intro f
  induction f with
  | zero => intro l c hc; simp [chunksGo] at hc
  | succ f ih =>
    intro l c hc
    cases l with
    | nil => simp [chunksGo] at hc
    | cons x xs =>
      simp only [chunksGo, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp only [List.length_take]; omega
      · exact ih _ c hc

/-- The common shape of `yeardatescalendar`, `yeardays2calendar` and `yeardayscalendar`:
a list of rows of at most `width` months that flatten to January..December; a width of
zero raises the `range()` ValueError, and a negative width gives no rows. -/
def YearShape {β : Type} (f : Int → Py β) (r : Int → Py (List (List β))) : Prop :=
  ∀ width ms, months12.mapM f = .ok ms → r width = pyChunks width ms ∧
    (width > 0 → ∃ rows, r width = .ok rows ∧ (∀ row ∈ rows, (row.length : Int) ≤ width) ∧
      rows.flatten.length = 12 ∧
      ∀ (i : Nat) (x : β), rows.flatten[i]? = some x → f ((i : Int) + 1) = .ok x) ∧
    (width = 0 → r width = .error (.valueError "range() arg 3 must not be zero")) ∧
    (width < 0 → r width = .ok [])

theorem yearShape_of {β : Type} (f : Int → Py β) (r : Int → Py (List (List β)))
    (hr : ∀ width, r width = do pyChunks width (← months12.mapM f)) : YearShape f r := by
  intro width ms hms
  have hrw : r width = pyChunks width ms := by rw [hr, hms]; rfl
  refine ⟨hrw, ?_, ?_, ?_⟩
  · intro hw
    refine ⟨chunks width.toNat ms, ?_, ?_, ?_, ?_⟩
    · rw [hrw]; unfold pyChunks; rw [if_neg (by omega), if_neg (by omega)]
    · intro row hrow
      have := chunksGo_le width.toNat ms.length ms row hrow
      omega
    · rw [chunks_flatten _ (by omega)]
      exact mapM_length _ _ _ hms
    · intro i x hi
      rw [chunks_flatten _ (by omega)] at hi
      obtain ⟨a, ha, hfa⟩ := mapM_get f months12 ms hms i x hi
      have hlen : i < 12 := by
        have := List.getElem?_eq_some_iff.mp ha
        obtain ⟨h, _⟩ := this
        simpa [months12] using h
      have : a = (i : Int) + 1 := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨
          i = 9 ∨ i = 10 ∨ i = 11) with h | h | h | h | h | h | h | h | h | h | h | h <;>
          subst h <;> simp [months12] at ha <;> omega
      rw [← this]; exact hfa
  · intro h; rw [hrw]; unfold pyChunks; rw [if_pos h]
  · intro h; rw [hrw]; unfold pyChunks; rw [if_neg (by omega), if_pos h]

/-- The three year matrices have the shape `YearShape` for every first weekday and year. -/
def YearMatrices : Prop :=
  ∀ (c : Calendar) (y : Int),
    YearShape (c.monthdayscalendar y) (c.yeardayscalendar y) ∧
    YearShape (c.monthdays2calendar y) (c.yeardays2calendar y) ∧
    YearShape (c.monthdatescalendar y) (c.yeardatescalendar y)

theorem yearMatrices_proven : YearMatrices := fun c y =>
  ⟨yearShape_of _ _ (fun _ => rfl), yearShape_of _ _ (fun _ => rfl), yearShape_of _ _ (fun _ => rfl)⟩

/-! ## `timegm` -/

/-- `timegm` is the Unix time of the proleptic Gregorian date: for a valid date it is
`(toordinal - epoch) * 86400 + h*3600 + m*60 + s`; the epoch maps to 0. -/
def TimegmOrdinal : Prop :=
  (timegm 1970 1 1 0 0 0 = .ok 0) ∧
  ∀ y m d h mi s : Int, ValidDate y m d →
    timegm y m d h mi s = .ok ((toordinal y m d - epochOrd) * 86400 + h * 3600 + mi * 60 + s)

theorem timegm_ok (y m d h mi s : Int) (hy : 1 ≤ y ∧ y ≤ 9999) (hm : 1 ≤ m ∧ m ≤ 12) :
    timegm y m d h mi s =
      .ok ((((ymd2ord y m 1 - epochOrd + d - 1) * 24 + h) * 60 + mi) * 60 + s) := by
  have hb := daysInMonth_bounds y m hm
  have hv : ValidDate y m 1 := by unfold ValidDate MINYEAR MAXYEAR; omega
  unfold timegm
  rw [mkDate_ok _ _ _ hv]
  rfl

theorem timegmOrdinal_proven : TimegmOrdinal := by
  refine ⟨by decide, ?_⟩
  intro y m d h mi s hv
  have hv' := hv
  unfold ValidDate MINYEAR MAXYEAR at hv'
  rw [timegm_ok y m d h mi s ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  have := ymd2ord_day y m d
  unfold toordinal
  exact congrArg Except.ok (by omega)

/-- `timegm` inverts the civil conversion `gmtime` performs: for a non-negative time before the
end of year 9999, splitting it into a day number and a time of day, converting the day with
`date.fromordinal` and calling `timegm` gives the time back. -/
def TimegmRoundtrip : Prop :=
  ∀ t : Int, 0 ≤ t → t / 86400 + epochOrd ≤ MAXORDINAL →
    ∃ y m d, fromordinalPy (t / 86400 + epochOrd) = .ok (y, m, d) ∧
      timegm y m d (t % 86400 / 3600) (t % 3600 / 60) (t % 60) = .ok t

theorem timegmRoundtrip_proven : TimegmRoundtrip := by
  intro t h0 h1
  have hE : epochOrd = 719163 := by decide
  obtain ⟨y, m, d, hv, ho, hf, -⟩ := toordinalFromordinal_proven (t / 86400 + epochOrd)
    (by omega) h1
  refine ⟨y, m, d, hf, ?_⟩
  rw [timegmOrdinal_proven.2 y m d _ _ _ hv, ho]
  exact congrArg Except.ok (by omega)

end PyLean.CoreLibs.CalStat
