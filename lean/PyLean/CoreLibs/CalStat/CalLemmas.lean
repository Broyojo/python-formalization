import PyLean.CoreLibs.CalStat.CalFmt
import PyLean.Datetime.CalendarProps

/-! Supporting lemmas for the calendar properties: the validated paths of the
mirror reduce to pure ordinal arithmetic, for every year including those outside
`datetime.date`'s range. -/

namespace PyLean.CoreLibs.CalStat

open PyLean PyLean.Datetime

/-! ## Monad and list helpers -/

theorem mapM_ok {α β : Type} (f : α → Py β) (g : α → β) (l : List α)
    (h : ∀ x ∈ l, f x = .ok (g x)) : l.mapM f = .ok (l.map g) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs := ih (fun y hy => h y (by simp [hy]))
    simp only [List.mapM_cons, hx, hxs, List.map_cons]
    rfl

theorem mapM_error {α β : Type} (f : α → Py β) (l : List α) (x : α) (hx : x ∈ l)
    (h : ∃ e, f x = .error e) : ∃ e, l.mapM f = .error e := by
  induction l with
  | nil => simp at hx
  | cons a as ih =>
    simp only [List.mapM_cons]
    cases hfa : f a with
    | error e => exact ⟨e, rfl⟩
    | ok v =>
      rcases List.mem_cons.mp hx with rfl | hm
      · obtain ⟨e, he⟩ := h; rw [he] at hfa; cases hfa
      · obtain ⟨e, he⟩ := ih hm
        rw [he]
        exact ⟨e, rfl⟩

theorem rangeI_length (a b : Int) : (rangeI a b).length = (b - a).toNat := by simp [rangeI]

theorem map_rangeI_getElem? {β : Type} (f : Int → β) (a b : Int) (j : Nat) :
    ((rangeI a b).map f)[j]? = if j < (b - a).toNat then some (f (a + j)) else none := by
  simp only [rangeI, List.map_map, List.getElem?_map, List.getElem?_range']
  by_cases h : j < (b - a).toNat
  · simp [h]
  · simp [h]

theorem rangeI_getElem? (a b : Int) (j : Nat) :
    (rangeI a b)[j]? = if j < (b - a).toNat then some (a + j) else none := by
  have := map_rangeI_getElem? id a b j
  simpa using this

theorem mem_enumFrom {α : Type} {s k : Int} {l : List α} {x : α} :
    (k, x) ∈ enumFrom s l ↔ ∃ j : Nat, k = s + j ∧ l[j]? = some x := by
  unfold enumFrom
  simp only [List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a, i⟩, hm, h1, h2⟩
    have := List.mem_zipIdx_iff_getElem?.mp hm
    simp only at this h1 h2
    subst h2
    exact ⟨i, h1.symm, by simpa using this⟩
  · rintro ⟨j, h1, h2⟩
    refine ⟨(x, j), ?_, h1.symm, rfl⟩
    exact List.mem_zipIdx_iff_getElem?.mpr (by simpa using h2)

/-! ## Chunks -/

theorem chunksGo_flatten {α : Type} (k : Nat) (hk : 0 < k) :
    ∀ (f : Nat) (l : List α), l.length ≤ f → (chunksGo k f l).flatten = l := by
  intro f
  induction f with
  | zero => intro l hl; cases l with
    | nil => rfl
    | cons _ _ => simp at hl
  | succ f ih =>
    intro l hl
    cases l with
    | nil => rfl
    | cons x xs =>
      simp only [chunksGo, List.flatten_cons]
      rw [ih _ (by simp only [List.length_drop, List.length_cons] at hl ⊢; omega)]
      exact List.take_append_drop _ _

theorem chunks_flatten {α : Type} (k : Nat) (hk : 0 < k) (l : List α) :
    (chunks k l).flatten = l := chunksGo_flatten k hk _ _ (Nat.le_refl _)

theorem chunksGo_full {α : Type} (k : Nat) (hk : 0 < k) :
    ∀ (f : Nat) (l : List α), l.length ≤ f → k ∣ l.length →
      ∀ c ∈ chunksGo k f l, c.length = k := by
  intro f
  induction f with
  | zero => intro l _ _ c hc; simp [chunksGo] at hc
  | succ f ih =>
    intro l hl hd c hc
    cases l with
    | nil => simp [chunksGo] at hc
    | cons x xs =>
      simp only [chunksGo, List.mem_cons] at hc
      obtain ⟨q, hq⟩ := hd
      have hq0 : 0 < q := by
        cases q with
        | zero => simp at hq
        | succ _ => omega
      have hle : k ≤ (x :: xs).length := by
        rw [hq]; exact Nat.le_mul_of_pos_right _ hq0
      rcases hc with rfl | hc
      · simp only [List.length_take]; omega
      · refine ih _ ?_ ?_ c hc
        · simp only [List.length_drop, List.length_cons] at hl ⊢; omega
        · refine ⟨q - 1, ?_⟩
          simp only [List.length_drop]
          rw [hq, Nat.mul_sub, Nat.mul_one]

theorem chunksGo_length {α : Type} (k : Nat) (hk : 0 < k) :
    ∀ (f : Nat) (l : List α), l.length ≤ f → k ∣ l.length →
      (chunksGo k f l).length * k = l.length := by
  intro f
  induction f with
  | zero => intro l hl _; cases l with
    | nil => simp [chunksGo]
    | cons _ _ => simp at hl
  | succ f ih =>
    intro l hl hd
    cases l with
    | nil => simp [chunksGo]
    | cons x xs =>
      simp only [chunksGo, List.length_cons]
      obtain ⟨q, hq⟩ := hd
      have hq0 : 0 < q := by
        cases q with
        | zero => simp at hq
        | succ _ => omega
      have hle : k ≤ (x :: xs).length := by
        rw [hq]; exact Nat.le_mul_of_pos_right _ hq0
      have := ih ((x :: xs).drop k) (by simp only [List.length_drop, List.length_cons] at hl ⊢; omega)
        ⟨q - 1, by simp only [List.length_drop]; rw [hq, Nat.mul_sub, Nat.mul_one]⟩
      rw [Nat.add_mul, this]
      simp only [List.length_drop, List.length_cons] at hle ⊢
      omega

/-! ## Calendar arithmetic -/

theorem isleap_eq (y : Int) : isleap y = isLeap y := rfl

theorem isLeap_yearMap (y : Int) : isLeap (yearMap y) = isLeap y := by
  unfold yearMap
  split
  · rfl
  · apply Bool.eq_iff_iff.mpr
    rw [isLeap_iff, isLeap_iff]
    omega

theorem daysInMonth_yearMap (y m : Int) : daysInMonth (yearMap y) m = daysInMonth y m := by
  rw [daysInMonth_eq, daysInMonth_eq, isLeap_yearMap]

theorem yearMap_range (y : Int) : 1 ≤ yearMap y ∧ yearMap y ≤ 9999 := by
  unfold yearMap MINYEAR MAXYEAR
  split <;> omega

/-- The weekday `(ordinal + 6) % 7` extended to every int year by floor arithmetic. -/
def wk (y m d : Int) : Int := (ymd2ord y m d + 6) % 7

theorem wk_yearMap (y m d : Int) : wk (yearMap y) m d = wk y m d := by
  unfold wk ymd2ord
  rw [daysBeforeMonth_eq, daysBeforeMonth_eq, isLeap_yearMap]
  generalize dbmL (isLeap y) m = z
  unfold yearMap daysBeforeYear MINYEAR MAXYEAR
  split
  · rfl
  · simp only
    omega

theorem cIntArg_ok (x : Int) (h1 : -(2 ^ 31) ≤ x) (h2 : x ≤ 2 ^ 31 - 1) : cIntArg x = .ok x := by
  unfold cIntArg
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem mkDate_ok (y m d : Int) (h : ValidDate y m d) : mkDate y m d = .ok (y, m, d) := by
  have hb := (dimL_bounds (isLeap y) m ⟨h.2.2.1, h.2.2.2.1⟩).2
  have h' := h
  unfold ValidDate MINYEAR MAXYEAR at h'
  rw [daysInMonth_eq] at h'
  unfold mkDate
  rw [cIntArg_ok y (by omega) (by omega), cIntArg_ok m (by omega) (by omega),
    cIntArg_ok d (by omega) (by omega)]
  simp only [bind, Except.bind]
  exact checkDate_ok y m d h

theorem weekday_ok (y m d : Int) (hm : 1 ≤ m ∧ m ≤ 12) (hd : 1 ≤ d ∧ d ≤ daysInMonth y m) :
    weekday y m d = .ok (wk y m d) := by
  have hv : ValidDate (yearMap y) m d := by
    have := yearMap_range y
    unfold ValidDate MINYEAR MAXYEAR
    rw [daysInMonth_yearMap]
    omega
  unfold weekday
  rw [mkDate_ok _ _ _ hv]
  simp only [bind, Except.bind, pure, Except.pure]
  exact congrArg Except.ok (wk_yearMap y m d)

theorem dimL_table (leap : Bool) (m : Int) (hm : 1 ≤ m ∧ m ≤ 12) :
    pyIndex mdaysList m = .ok (daysInMonthTable m) := by
  rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
    m = 10 ∨ m = 11 ∨ m = 12) with h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> rfl

theorem table_febExtra (y m : Int) : daysInMonthTable m + febExtra y m = daysInMonth y m := by
  rw [daysInMonth_eq]
  simp only [dimL, febExtra, isleap_eq]
  by_cases h : m = 2 ∧ isLeap y = true <;> simp [h]

theorem validateMonth_ok (m : Int) (hm : 1 ≤ m ∧ m ≤ 12) : validateMonth m = .ok () := by
  unfold validateMonth
  rw [if_neg (by omega)]

theorem validateMonth_err (m : Int) (hm : ¬(1 ≤ m ∧ m ≤ 12)) :
    validateMonth m = .error (illegalMonth m) := by
  unfold validateMonth
  rw [if_pos hm]

theorem daysInMonth_bounds (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) :
    28 ≤ daysInMonth y m ∧ daysInMonth y m ≤ 31 := by
  rw [daysInMonth_eq]
  exact dimL_bounds _ _ hm

theorem monthrange_ok (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) :
    monthrange y m = .ok (wk y m 1, daysInMonth y m) := by
  have hb := daysInMonth_bounds y m hm
  unfold monthrange
  rw [validateMonth_ok m hm, weekday_ok y m 1 hm (by omega), dimL_table false m hm]
  simp only [bind, Except.bind, pure, Except.pure, table_febExtra]

theorem monthrange_err (y m : Int) (hm : ¬(1 ≤ m ∧ m ≤ 12)) :
    monthrange y m = .error (illegalMonth m) := by
  unfold monthrange
  rw [validateMonth_err m hm]
  rfl

theorem monthlen_ok (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) : monthlen y m = .ok (daysInMonth y m) := by
  unfold monthlen
  rw [dimL_table false m hm]
  simp only [bind, Except.bind, pure, Except.pure, table_febExtra]

theorem ymd2ord_day (y m d : Int) : ymd2ord y m d = ymd2ord y m 1 + d - 1 := by
  unfold ymd2ord; omega

theorem nextmonth_range (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) :
    1 ≤ (nextmonth y m).2 ∧ (nextmonth y m).2 ≤ 12 := by
  unfold nextmonth; split <;> simp only <;> omega

theorem prevmonth_range (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) :
    1 ≤ (prevmonth y m).2 ∧ (prevmonth y m).2 ≤ 12 := by
  unfold prevmonth; split <;> simp only <;> omega

theorem next_prev (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) :
    nextmonth (prevmonth y m).1 (prevmonth y m).2 = (y, m) := by
  unfold prevmonth nextmonth
  by_cases h : m = 1
  · subst h; simp
  · simp only [if_neg h]
    rw [if_neg (by omega)]
    simp

theorem prev_next (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) :
    prevmonth (nextmonth y m).1 (nextmonth y m).2 = (y, m) := by
  unfold prevmonth nextmonth
  by_cases h : m = 12
  · subst h; simp
  · simp only [if_neg h]
    rw [if_neg (by omega)]
    simp

/-- The first of the next month follows the last of this month, in every int year. -/
theorem ord_next (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) :
    ymd2ord (nextmonth y m).1 (nextmonth y m).2 1 = ymd2ord y m (daysInMonth y m) + 1 := by
  rw [daysInMonth_eq]
  unfold nextmonth ymd2ord
  by_cases h : m = 12
  · subst h
    simp only [if_true, daysBeforeMonth_eq, daysBeforeYear_succ]
    have h1 := dbmL_one (isLeap (y + 1))
    have h2 := dbmL_twelve (isLeap y)
    rw [h1]
    split at h2 <;> split <;> simp_all <;> omega
  · simp only [if_neg h, daysBeforeMonth_eq]
    have := dbmL_succ (isLeap y) m (by omega)
    omega

theorem ord_prev (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) :
    ymd2ord y m 1 = ymd2ord (prevmonth y m).1 (prevmonth y m).2
      (daysInMonth (prevmonth y m).1 (prevmonth y m).2) + 1 := by
  have h := ord_next (prevmonth y m).1 (prevmonth y m).2 (prevmonth_range y m hm)
  rw [next_prev y m hm] at h
  exact h

/-! ## Pure form of the month iterators -/

/-- `days_before`, calendar.py:253. -/
def daysB (c : Calendar) (y m : Int) : Int := (wk y m 1 - c.firstweekday) % 7
/-- `days_after`, calendar.py:256. -/
def daysA (c : Calendar) (y m : Int) : Int :=
  (c.firstweekday - wk y m 1 - daysInMonth y m) % 7

theorem firstweekday_range (c : Calendar) : 0 ≤ c.firstweekday ∧ c.firstweekday ≤ 6 := by
  unfold Calendar.firstweekday; omega

theorem daysB_range (c : Calendar) (y m : Int) : 0 ≤ daysB c y m ∧ daysB c y m ≤ 6 := by
  unfold daysB; omega

theorem daysA_range (c : Calendar) (y m : Int) : 0 ≤ daysA c y m ∧ daysA c y m ≤ 6 := by
  unfold daysA; omega

theorem weeks_multiple (c : Calendar) (y m : Int) :
    (daysB c y m + daysInMonth y m + daysA c y m) % 7 = 0 := by
  unfold daysB daysA; omega

theorem itermonthdays_ok (c : Calendar) (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) :
    c.itermonthdays y m = .ok (List.replicate (daysB c y m).toNat 0 ++
      rangeI 1 (daysInMonth y m + 1) ++ List.replicate (daysA c y m).toNat 0) := by
  unfold Calendar.itermonthdays
  rw [monthrange_ok y m hm]
  rfl

theorem itermonthdays_err (c : Calendar) (y m : Int) (hm : ¬(1 ≤ m ∧ m ≤ 12)) :
    c.itermonthdays y m = .error (illegalMonth m) := by
  unfold Calendar.itermonthdays
  rw [monthrange_err y m hm]
  rfl

/-- The list `itermonthdays3` yields. -/
def days3 (c : Calendar) (y m : Int) : List Date :=
  let py := (prevmonth y m).1
  let pm := (prevmonth y m).2
  let endd := daysInMonth py pm + 1
  (rangeI (endd - daysB c y m) endd).map (fun d => ((py, pm, d) : Date)) ++
  (rangeI 1 (daysInMonth y m + 1)).map (fun d => ((y, m, d) : Date)) ++
  (rangeI 1 (daysA c y m + 1)).map (fun d => (((nextmonth y m).1, (nextmonth y m).2, d) : Date))

theorem itermonthdays3_ok (c : Calendar) (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) :
    c.itermonthdays3 y m = .ok (days3 c y m) := by
  unfold Calendar.itermonthdays3
  rw [monthrange_ok y m hm]
  have h : monthlen (prevmonth y m).1 (prevmonth y m).2 =
      .ok (daysInMonth (prevmonth y m).1 (prevmonth y m).2) :=
    monthlen_ok _ _ (prevmonth_range y m hm)
  show (do
    let endd := (← monthlen (prevmonth y m).1 (prevmonth y m).2) + 1
    pure _ : Py _) = _
  rw [h]
  rfl

theorem itermonthdays4_ok (c : Calendar) (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) :
    c.itermonthdays4 y m = .ok ((enumFrom 0 (days3 c y m)).map
      (fun p => (p.2.1, p.2.2.1, p.2.2.2, (c.firstweekday + p.1) % 7))) := by
  unfold Calendar.itermonthdays4
  rw [itermonthdays3_ok c y m hm]
  rfl

theorem itermonthdays2_ok (c : Calendar) (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) :
    c.itermonthdays2 y m = .ok ((enumFrom c.firstweekday (List.replicate (daysB c y m).toNat 0 ++
      rangeI 1 (daysInMonth y m + 1) ++ List.replicate (daysA c y m).toNat 0)).map
        (fun p => (p.2, p.1 % 7))) := by
  unfold Calendar.itermonthdays2
  rw [itermonthdays_ok c y m hm]
  rfl

/-- Every entry of `days3`, with its position: a valid day of its month, and its weekday
agrees with the position. -/
theorem days3_entry (c : Calendar) (y m : Int) (hm : 1 ≤ m ∧ m ≤ 12) (j : Nat) (t : Date)
    (hj : (days3 c y m)[j]? = some t) :
    1 ≤ t.2.1 ∧ t.2.1 ≤ 12 ∧ 1 ≤ t.2.2 ∧ t.2.2 ≤ daysInMonth t.1 t.2.1 ∧
      wk t.1 t.2.1 t.2.2 = (c.firstweekday + (j : Int)) % 7 ∧
      ymd2ord t.1 t.2.1 t.2.2 = ymd2ord y m 1 - daysB c y m + j := by
  have hB := daysB_range c y m
  have hA := daysA_range c y m
  have hfw := firstweekday_range c
  have hn := daysInMonth_bounds y m hm
  have hpr := prevmonth_range y m hm
  have hnr := nextmonth_range y m hm
  have hpn := daysInMonth_bounds (prevmonth y m).1 (prevmonth y m).2 hpr
  have hnn := daysInMonth_bounds (nextmonth y m).1 (nextmonth y m).2 hnr
  have hop := ord_prev y m hm
  have hon := ord_next y m hm
  have hd1 := ymd2ord_day y m (daysInMonth y m)
  have hw : wk y m 1 = (ymd2ord y m 1 + 6) % 7 := rfl
  have hb : daysB c y m = (wk y m 1 - c.firstweekday) % 7 := rfl
  have ha : daysA c y m = (c.firstweekday - wk y m 1 - daysInMonth y m) % 7 := rfl
  have hL1 : (daysInMonth (prevmonth y m).1 (prevmonth y m).2 + 1 -
      (daysInMonth (prevmonth y m).1 (prevmonth y m).2 + 1 - daysB c y m)).toNat =
      (daysB c y m).toNat := by omega
  have hL2 : (daysInMonth y m + 1 - 1).toNat = (daysInMonth y m).toNat := by omega
  have hL3 : (daysA c y m + 1 - 1).toNat = (daysA c y m).toNat := by omega
  unfold days3 at hj
  simp only at hj
  rw [List.append_assoc, List.getElem?_append] at hj
  simp only [List.length_map, rangeI_length, hL1] at hj
  split at hj
  · rename_i hlt
    rw [map_rangeI_getElem?, if_pos (by rw [hL1]; exact hlt)] at hj
    cases hj
    simp only
    have hd2 := ymd2ord_day (prevmonth y m).1 (prevmonth y m).2
      (daysInMonth (prevmonth y m).1 (prevmonth y m).2 + 1 - daysB c y m + j)
    have hd3 := ymd2ord_day (prevmonth y m).1 (prevmonth y m).2
      (daysInMonth (prevmonth y m).1 (prevmonth y m).2)
    unfold wk
    refine ⟨by omega, by omega, by omega, by omega, ?_, by omega⟩
    omega
  · rename_i hge
    rw [List.getElem?_append] at hj
    simp only [List.length_map, rangeI_length, hL2] at hj
    split at hj
    · rename_i hlt
      rw [map_rangeI_getElem?, if_pos (by rw [hL2]; exact hlt)] at hj
      cases hj
      simp only
      have hd2 := ymd2ord_day y m (1 + ((j - (daysB c y m).toNat : Nat) : Int))
      unfold wk
      refine ⟨by omega, by omega, by omega, by omega, ?_, by omega⟩
      omega
    · rename_i hge2
      rw [map_rangeI_getElem?] at hj
      split at hj
      · rename_i hlt
        cases hj
        simp only
        rw [hL3] at hlt
        have hd2 := ymd2ord_day (nextmonth y m).1 (nextmonth y m).2
          (1 + ((j - (daysB c y m).toNat - (daysInMonth y m).toNat : Nat) : Int))
        unfold wk
        refine ⟨by omega, by omega, by omega, by omega, ?_, by omega⟩
        omega
      · cases hj

end PyLean.CoreLibs.CalStat
