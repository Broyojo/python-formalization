import PyLean.Datetime.ObjProps

/-!
`date` objects: comparison, hash, weekday, subtraction, `replace`, time tuples,
`ctime`, `repr`, pickle state and the constructor, in both twins. Theorems quantify
over valid dates, the type invariant of `date`.
-/

namespace PyLean.Datetime

open PyLean

theorem date_memcmp (y m d y' m' d' : Int) (h1 : 0 ≤ y) (h2 : 0 ≤ y') (h3 : 0 ≤ m) (h4 : 0 ≤ m')
    (h5 : 0 ≤ d) (h6 : 0 ≤ d') :
    memcmpBytes (dateData y m d) (dateData y' m' d') = cmpTuple [y, m, d] [y', m', d'] := by
  unfold dateData
  rw [mc_year _ _ h1 h2, mc_field _ _ h3 h4, mc_field _ _ h5 h6,
    cmpTuple_cons y y' [m, d] [m', d'] rfl, cmpTuple_cons m m' [d] [d'] rfl,
    cmpTuple_cons d d' [] [] rfl]
  rfl

theorem validDate_pos (y m d : Int) (h : ValidDate y m d) : 1 ≤ y ∧ y ≤ 9999 ∧ 1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ 31 := by
  have h' := (validDate_iff y m d).mp h
  unfold MINYEAR MAXYEAR at h'
  have := dimL_bounds (isLeap y) m ⟨h'.2.2.1, h'.2.2.2.1⟩
  omega

/-- `date` comparison: the twins agree, `==` is equality of the fields, and neither
compares with a `datetime`. -/
def DateCompare : Prop :=
  ∀ (a b : Int × Int × Int) (op : CmpOp), ValidDate a.1 a.2.1 a.2.2 → ValidDate b.1 b.2.1 b.2.2 →
    dateRichPy op a b false = dateRichC op a b false ∧
    dateRichPy op a b true = none ∧ dateRichC op a b true = none ∧
    (dateRichPy .eq a b false = some true ↔ a = b)

theorem dateCompare_proven : DateCompare := by
  intro a b op ha hb
  obtain ⟨y, m, d⟩ := a
  obtain ⟨y', m', d'⟩ := b
  have pa := validDate_pos _ _ _ ha
  have pb := validDate_pos _ _ _ hb
  simp only at pa pb
  refine ⟨?_, by simp [dateRichPy], by simp [dateRichC], ?_⟩
  · simp only [dateRichPy, dateRichC, dateCmpPy, ite_false, Bool.false_eq_true]
    rw [date_memcmp _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  · have hc := cmpTuple_sign [y, m, d] [y', m', d'] rfl
    simp only [dateRichPy, dateCmpPy, ite_false, Bool.false_eq_true, diffToBool, Option.some.injEq]
    simp [hc, Prod.ext_iff]

/-- Equal dates hash alike, in both twins. -/
def DateHash : Prop :=
  ∀ a b : Int × Int × Int, ValidDate a.1 a.2.1 a.2.2 → ValidDate b.1 b.2.1 b.2.2 →
    dateRichPy .eq a b false = some true →
    dateHashKeyPy a.1 a.2.1 a.2.2 = dateHashKeyPy b.1 b.2.1 b.2.2 ∧
    dateHashKeyC a.1 a.2.1 a.2.2 = dateHashKeyC b.1 b.2.1 b.2.2

theorem dateHash_proven : DateHash := by
  intro a b ha hb h
  have := (dateCompare_proven a b .eq ha hb).2.2.2.mp h
  subst this
  exact ⟨rfl, rfl⟩

theorem weekdayC_eq (y m d : Int) (h : ValidDate y m d) : weekdayC y m d = (ymd2ord y m d + 6) % 7 := by
  have p := validDate_pos _ _ _ h
  have r := ymd2ord_range y m d h
  unfold weekdayC
  rw [ymdToOrdC_eq y m d (by omega), Int.tmod_eq_emod_of_nonneg (by omega)]

/-- `weekday()` and `isoweekday()`: the twins agree, `isoweekday() == weekday() + 1`,
and `isoweekday()` is the third item of `isocalendar()`. -/
def DateWeekday : Prop :=
  ∀ y m d : Int, ValidDate y m d →
    dateWeekdayPy y m d = dateWeekdayC y m d ∧
    dateIsoweekdayPy y m d = dateIsoweekdayC y m d ∧
    dateIsoweekdayPy y m d = dateWeekdayPy y m d + 1 ∧
    dateIsoweekdayPy y m d = (isocalendar y m d).2.2

theorem dateWeekday_proven : DateWeekday := by
  intro y m d h
  have wc := weekdayC_eq y m d h
  obtain ⟨hv, ho⟩ := isocalendar_spec y m d h
  have f := (isoYear_facts (isocalendar y m d).1).2.2.1
  unfold ValidIso at hv
  unfold isoOrd at ho
  unfold dateWeekdayPy dateWeekdayC dateIsoweekdayPy dateIsoweekdayC toordinal
  rw [wc]
  dsimp only
  generalize ymd2ord y m d = T at *
  generalize (isocalendar y m d).2.2 = D at *
  generalize (isocalendar y m d).2.1 = W at *
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> split <;> omega

/-- `date - date` is the difference of ordinals, and `date - timedelta` agrees in
both twins: the same date, or `OverflowError`. -/
def DateSubtract : Prop :=
  ∀ (a b : Int × Int × Int) (t : Delta), ValidDate a.1 a.2.1 a.2.2 → ValidDate b.1 b.2.1 b.2.2 → t.Valid →
    dateSubDatePy a b = .ok ⟨toordinal a.1 a.2.1 a.2.2 - toordinal b.1 b.2.1 b.2.2, 0, 0⟩ ∧
    dateSubDateC a b = .ok ⟨toordinal a.1 a.2.1 a.2.2 - toordinal b.1 b.2.1 b.2.2, 0, 0⟩ ∧
    SameOutcome (dateSubDeltaPy a.1 a.2.1 a.2.2 t) (dateSubDeltaC a.1 a.2.1 a.2.2 t)

theorem dateSubtract_proven : DateSubtract := by
  intro a b t ha hb ht
  obtain ⟨y, m, d⟩ := a
  obtain ⟨y', m', d'⟩ := b
  simp only at ha hb ⊢
  have ra := ymd2ord_range y m d ha
  have rb := ymd2ord_range y' m' d' hb
  have pa := validDate_pos _ _ _ ha
  have pb := validDate_pos _ _ _ hb
  unfold MAXORDINAL at ra rb
  have ec : ymdToOrdC y m d - ymdToOrdC y' m' d' = ymd2ord y m d - ymd2ord y' m' d' := by
    rw [ymdToOrdC_eq y m d (by omega), ymdToOrdC_eq y' m' d' (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · unfold dateSubDatePy toordinal
    rw [deltaPy_eq]
    have hv : Delta.Valid ⟨ymd2ord y m d - ymd2ord y' m' d', 0, 0⟩ := by
      unfold Delta.Valid MAX_DELTA_DAYS; simp only; omega
    have := mkDeltaPy_of_valid _ hv
    have e : totalUs (ymd2ord y m d - ymd2ord y' m' d') 0 0 0 0 0 0 =
        Delta.toUs ⟨ymd2ord y m d - ymd2ord y' m' d', 0, 0⟩ := by
      unfold totalUs Delta.toUs; simp only; omega
    rw [e, this]
  · unfold dateSubDateC toordinal checkDeltaDayRange
    rw [ec]
    have : -MAX_DELTA_DAYS ≤ ymd2ord y m d - ymd2ord y' m' d' ∧
        ymd2ord y m d - ymd2ord y' m' d' ≤ MAX_DELTA_DAYS := by unfold MAX_DELTA_DAYS; omega
    simp [this, bind, Except.bind, pure, Except.pure]
  · have ht' := ht
    unfold Delta.Valid MAX_DELTA_DAYS at ht'
    have hv : Delta.Valid ⟨-t.days, 0, 0⟩ := by
      unfold Delta.Valid MAX_DELTA_DAYS; simp only; omega
    have hneg : deltaPy (-t.days) 0 0 0 0 0 0 = .ok ⟨-t.days, 0, 0⟩ := by
      rw [deltaPy_eq]
      have e : totalUs (-t.days) 0 0 0 0 0 0 = Delta.toUs ⟨-t.days, 0, 0⟩ := by
        unfold totalUs Delta.toUs; simp only; omega
      rw [e, mkDeltaPy_of_valid _ hv]
    have main := dateAddTimedelta_proven y m d ⟨-t.days, 0, 0⟩ ha hv
    unfold dateSubDeltaPy dateSubDeltaC
    simp only [hneg, bind, Except.bind]
    unfold dateAddC at main
    simp only [bind, Except.bind] at main
    by_cases hr : 1 ≤ toordinal y m d + -t.days ∧ toordinal y m d + -t.days ≤ MAXORDINAL
    · obtain ⟨y2, m2, d2, _, _, e1, e2⟩ := main.1 hr
      rw [e1]
      rw [e2]
      rfl
    · obtain ⟨⟨e1, he1, c1⟩, ⟨e2, he2, c2⟩⟩ := main.2 hr
      rw [he1, he2]
      simp only [SameOutcome]
      rw [c1, c2]

/-- `date.replace`: with no argument it returns the same date; on C `int` arguments
the twins agree (for arguments outside `int`, C raises `OverflowError` and Python
`ValueError`, the class upstream closed as not planned in gh-158778). -/
def DateReplace : Prop :=
  ∀ (y m d : Int) (ny nm nd : Option Int), ValidDate y m d →
    dateReplacePy y m d none none none = .ok (y, m, d) ∧
    dateReplaceC y m d none none none = .ok (y, m, d) ∧
    (fitsCInt (ny.getD y) → fitsCInt (nm.getD m) → fitsCInt (nd.getD d) →
      dateReplacePy y m d ny nm nd = dateReplaceC y m d ny nm nd)

theorem dateReplace_proven : DateReplace := by
  intro y m d ny nm nd h
  have p := validDate_pos _ _ _ h
  refine ⟨?_, ?_, ?_⟩
  · unfold dateReplacePy; exact checkDate_ok y m d h
  · unfold dateReplaceC
    have : fitsCInt y ∧ fitsCInt m ∧ fitsCInt d := by unfold fitsCInt; omega
    simp only [Option.getD_none]
    rw [if_neg (by simp [this])]
    exact checkDate_ok y m d h
  · intro h1 h2 h3
    unfold dateReplacePy dateReplaceC
    simp only
    rw [if_neg (by simp [h1, h2, h3])]

/-- `date.timetuple()`: the twins agree, and the tuple holds the fields, weekday,
day of the year and `tm_isdst == -1`. -/
def DateTimetuple : Prop :=
  ∀ y m d : Int, ValidDate y m d →
    dateTimetuplePy y m d = dateTimetupleC y m d ∧
    dateTimetuplePy y m d =
      [y, m, d, 0, 0, 0, dateWeekdayPy y m d, ymd2ord y m d - ymd2ord y 1 1 + 1, -1]

theorem buildStructTime_twins (y m d hh mm ss f : Int) (h : ValidDate y m d) :
    buildStructTimePy y m d hh mm ss f = buildStructTimeC y m d hh mm ss f := by
  unfold buildStructTimePy buildStructTimeC
  rw [weekdayC_eq y m d h]

theorem dateTimetuple_proven : DateTimetuple := by
  intro y m d h
  refine ⟨buildStructTime_twins y m d 0 0 0 (-1) h, ?_⟩
  unfold dateTimetuplePy buildStructTimePy dateWeekdayPy toordinal
  have e : ymd2ord y m d - ymd2ord y 1 1 + 1 = daysBeforeMonth y m + d := by
    have : daysBeforeMonth y 1 = 0 := by unfold daysBeforeMonth daysBeforeMonthTable; simp
    unfold ymd2ord; omega
  rw [e]

/-- `ctime()`: the twins agree on the same text for `date` and `datetime` fields. -/
def DateCtime : Prop :=
  ∀ y m d hh mm ss : Int, ValidDate y m d → ctimePy y m d hh mm ss = ctimeC y m d hh mm ss

theorem dateCtime_proven : DateCtime := by
  intro y m d hh mm ss h
  unfold ctimePy ctimeC toordinal
  rw [weekdayC_eq y m d h]
  have r := ymd2ord_range y m d h
  have e : (if ymd2ord y m d % 7 = 0 then 7 else ymd2ord y m d % 7) = (ymd2ord y m d + 6) % 7 + 1 := by
    split <;> omega
  dsimp only
  rw [e]

/-- `repr(date)` and `str(date)`: the twins produce the same text. -/
def DateRepr : Prop :=
  ∀ y m d : Int, dateReprPy y m d = dateReprC y m d ∧ getClassModule "datetime" = "datetime."

theorem dateRepr_proven : DateRepr := fun _ _ _ => ⟨rfl, rfl⟩

/-- `date(d.__reduce__()[1][0]) == d`, through the bytes state, in both twins. -/
def DatePickle : Prop :=
  ∀ y m d : Int, ValidDate y m d →
    dateSetstate (dateGetstate y m d) = some (y, m, d) ∧
    dateNewPy (.bytes (dateGetstate y m d)) .none_ .none_ = .ok (y, m, d) ∧
    dateNewC [.bytes (dateGetstate y m d)] = .ok (y, m, d)

theorem datePickle_proven : DatePickle := by
  intro y m d h
  have p := validDate_pos _ _ _ h
  have e1 : dateSetstate (dateGetstate y m d) = some (y, m, d) := by
    unfold dateGetstate dateData dateSetstate
    simp only [Option.some.injEq, Prod.mk.injEq]
    omega
  have hm : 1 ≤ m.toNat ∧ m.toNat ≤ 12 := by omega
  refine ⟨e1, ?_, ?_⟩
  · unfold dateNewPy
    simp only [stateOf, dateGetstate, dateData, List.length_cons, List.length_nil, List.getD_cons_succ,
      List.getD_cons_zero]
    simp only [dateGetstate, dateData] at e1
    simp [hm, e1, bind, Except.bind, pure, Except.pure]
  · unfold dateNewC
    simp only [stateOf, dateGetstate, dateData, List.length_cons, List.length_nil, List.getD_cons_succ,
      List.getD_cons_zero]
    simp only [dateGetstate, dateData] at e1
    simp [hm, e1, bind, Except.bind, pure, Except.pure]

/-- `date(y, m, d)` for ints that fit a C `int`: the twins agree. Out-of-`int`
arguments are the rejected class of gh-158778. -/
def DateCtorInt : Prop :=
  ∀ y m d : Int, fitsCInt y → fitsCInt m → fitsCInt d →
    dateNewPy (.int y) (.int m) (.int d) = dateNewC [.int y, .int m, .int d] ∧
    (ValidDate y m d → dateNewPy (.int y) (.int m) (.int d) = .ok (y, m, d))

theorem dateCtorInt_proven : DateCtorInt := by
  intro y m d h1 h2 h3
  have e : dateNewPy (.int y) (.int m) (.int d) = checkDate y m d := by
    simp [dateNewPy, stateOf, pyIndex, bind, Except.bind]
  refine ⟨?_, fun hv => by rw [e]; exact checkDate_ok y m d hv⟩
  rw [e]
  simp [dateNewC, datetimeDateClinicC, datetimeDateImplC, clinicArity, stateOf, parseI_int, h1, h2, h3, bind,
    Except.bind, pure, Except.pure]

/-- `IsoCalendarDate`: `year`, `week`, `weekday` are the three items of the tuple,
`__reduce__` gives a plain tuple, and `repr` names the fields in each twin. -/
def IsoCalendarDateFields : Prop :=
  ∀ y w d : Int,
    (y, w, d).1 = y ∧ (y, w, d).2.1 = w ∧ (y, w, d).2.2 = d ∧
    isoReprC y w d = "datetime." ++ isoReprPy y w d

theorem isoCalendarDateFields_proven : IsoCalendarDateFields := by
  intro y w d
  refine ⟨rfl, rfl, rfl, ?_⟩
  have e : ("datetime.IsoCalendarDate(year=" : String) = "datetime." ++ "IsoCalendarDate(year=" := by decide
  simp only [isoReprC, isoReprPy, toString, e, String.append_assoc]

end PyLean.Datetime
