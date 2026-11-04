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

/-- Within a year, a valid date's day of the year `dbmL m + d - 1` grows with `(m, d)`. -/
theorem dbmL_mono_table : ∀ leap : Bool, ∀ i j : Fin 12, i < j →
    dbmL leap ((i : Nat) + 1) + dimL leap ((i : Nat) + 1) ≤ dbmL leap ((j : Nat) + 1) := by
  decide

theorem dbmL_mono (leap : Bool) (m m' : Int) (h1 : 1 ≤ m) (h2 : m < m') (h3 : m' ≤ 12) :
    dbmL leap m + dimL leap m ≤ dbmL leap m' := by
  have := dbmL_mono_table leap ⟨(m - 1).toNat, by omega⟩ ⟨(m' - 1).toNat, by omega⟩
    (by simp only [Fin.mk_lt_mk]; omega)
  simp only at this
  have e1 : (((m - 1).toNat : Nat) : Int) + 1 = m := by omega
  have e2 : (((m' - 1).toNat : Nat) : Int) + 1 = m' := by omega
  rw [e1, e2] at this
  exact this

/-- `toordinal` is strictly increasing in the field order of valid dates. -/
theorem ymd2ord_lt_of_lex (y m d y' m' d' : Int) (ha : ValidDate y m d) (hb : ValidDate y' m' d')
    (h : y < y' ∨ (y = y' ∧ m < m') ∨ (y = y' ∧ m = m' ∧ d < d')) :
    ymd2ord y m d < ymd2ord y' m' d' := by
  have pa := (validDate_iff y m d).mp ha
  have pb := (validDate_iff y' m' d').mp hb
  unfold MINYEAR MAXYEAR at pa pb
  have fa := (monthDay_forward (isLeap y) m d ⟨pa.2.2.1, pa.2.2.2.1⟩ ⟨pa.2.2.2.2.1, pa.2.2.2.2.2⟩).2
  have hoa : ymd2ord y m d = jan1 y + (dbmL (isLeap y) m + d - 1) := by
    unfold ymd2ord jan1; rw [daysBeforeMonth_eq]; omega
  have hob : ymd2ord y' m' d' = jan1 y' + (dbmL (isLeap y') m' + d' - 1) := by
    unfold ymd2ord jan1; rw [daysBeforeMonth_eq]; omega
  have nb := dbmL_nonneg (isLeap y') m' ⟨pb.2.2.1, pb.2.2.2.1⟩
  rcases h with h | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩
  · have hs := jan1_succ y
    have hm : jan1 (y + 1) ≤ jan1 y' := by
      by_cases he : y + 1 = y'
      · rw [he]; omega
      · have := jan1_mono (y + 1) y' (by omega) (by omega); omega
    rw [hoa, hob]
    generalize isLeap y = L at hs fa ⊢
    cases L <;> simp only [Bool.false_eq_true, ↓reduceIte] at hs fa <;> omega
  · have := dbmL_mono (isLeap y) m m' pa.2.2.1 h pb.2.2.2.1
    rw [hoa, hob]; omega
  · rw [hoa, hob]; omega

/-- For valid dates, the field comparison `_cmp` has the sign of the ordinal difference. -/
theorem dateCmp_sign (y m d y' m' d' : Int) (ha : ValidDate y m d) (hb : ValidDate y' m' d') :
    (cmpTuple [y, m, d] [y', m', d'] = 0 ↔ ymd2ord y m d = ymd2ord y' m' d') ∧
    (cmpTuple [y, m, d] [y', m', d'] < 0 ↔ ymd2ord y m d < ymd2ord y' m' d') := by
  rw [cmpTuple_cons y y' [m, d] [m', d'] rfl, cmpTuple_cons m m' [d] [d'] rfl,
    cmpTuple_cons d d' [] [] rfl, cmpTuple_nil]
  have lt1 := ymd2ord_lt_of_lex y m d y' m' d' ha hb
  have lt2 := ymd2ord_lt_of_lex y' m' d' y m d hb ha
  by_cases h1 : y = y'
  · rw [if_pos h1]
    by_cases h2 : m = m'
    · rw [if_pos h2]
      by_cases h3 : d = d'
      · rw [if_pos h3]; subst h1 h2 h3; simp
      · rw [if_neg h3]
        by_cases h4 : d < d'
        · have := lt1 (Or.inr (Or.inr ⟨h1, h2, h4⟩))
          rw [if_pos h4]; constructor <;> constructor <;> intro <;> omega
        · have := lt2 (Or.inr (Or.inr ⟨h1.symm, h2.symm, by omega⟩))
          rw [if_neg h4]; constructor <;> constructor <;> intro <;> omega
    · rw [if_neg h2]
      by_cases h4 : m < m'
      · have := lt1 (Or.inr (Or.inl ⟨h1, h4⟩))
        rw [if_pos h4]; constructor <;> constructor <;> intro <;> omega
      · have := lt2 (Or.inr (Or.inl ⟨h1.symm, by omega⟩))
        rw [if_neg h4]; constructor <;> constructor <;> intro <;> omega
  · rw [if_neg h1]
    by_cases h4 : y < y'
    · have := lt1 (Or.inl h4)
      rw [if_pos h4]; constructor <;> constructor <;> intro <;> omega
    · have := lt2 (Or.inl (by omega))
      rw [if_neg h4]; constructor <;> constructor <;> intro <;> omega

/-- `date` comparison: every operator of each twin computes the order of the ordinals
(chronological order, `toordinal()`), for all valid dates; comparing with a `datetime` is
`NotImplemented` in both. A `__le__` computing `< 0` fails at `a == b`. -/
def DateCompare : Prop :=
  ∀ (a b : Int × Int × Int) (op : CmpOp), ValidDate a.1 a.2.1 a.2.2 → ValidDate b.1 b.2.1 b.2.2 →
    dateRichPy op a b false = some (op.holds (toordinal a.1 a.2.1 a.2.2) (toordinal b.1 b.2.1 b.2.2)) ∧
    dateRichC op a b false = some (op.holds (toordinal a.1 a.2.1 a.2.2) (toordinal b.1 b.2.1 b.2.2)) ∧
    dateRichPy op a b true = none ∧ dateRichC op a b true = none

theorem dateCompare_proven : DateCompare := by
  intro a b op ha hb
  obtain ⟨y, m, d⟩ := a
  obtain ⟨y', m', d'⟩ := b
  have pa := validDate_pos _ _ _ ha
  have pb := validDate_pos _ _ _ hb
  simp only at pa pb ha hb ⊢
  obtain ⟨s0, s1⟩ := dateCmp_sign y m d y' m' d' ha hb
  refine ⟨?_, ?_, by simp [dateRichPy], by simp [dateRichC]⟩
  · simp only [dateRichPy, dateCmpPy, Bool.false_eq_true, ite_false, toordinal]
    rw [← richPy_holds op _ _ _ s0 s1]
    cases op <;> rfl
  · simp only [dateRichC, Bool.false_eq_true, ite_false, toordinal]
    rw [date_memcmp _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    rw [diffToBool_holds op _ _ _ s0 s1]

/-- The hash key of each twin determines the date: two valid dates have the same key exactly
when they are equal (a constant key fails). Python hashes the one-element state tuple
`(bytes,)` and C the packed bytes themselves, both the pickle state `_getstate()`. -/
def DateHash : Prop :=
  ∀ a b : Int × Int × Int, ValidDate a.1 a.2.1 a.2.2 → ValidDate b.1 b.2.1 b.2.2 →
    (dateHashKeyPy a.1 a.2.1 a.2.2 = dateHashKeyPy b.1 b.2.1 b.2.2 ↔ a = b) ∧
    (dateHashKeyC a.1 a.2.1 a.2.2 = dateHashKeyC b.1 b.2.1 b.2.2 ↔ a = b) ∧
    dateHashKeyPy a.1 a.2.1 a.2.2 = .tuple1 (dateGetstate a.1 a.2.1 a.2.2) ∧
    dateHashKeyC a.1 a.2.1 a.2.2 = .bytes (dateGetstate a.1 a.2.1 a.2.2)

theorem dateData_inj (y m d y' m' d' : Int) (ha : ValidDate y m d) (hb : ValidDate y' m' d') :
    dateData y m d = dateData y' m' d' ↔ (y, m, d) = (y', m', d') := by
  have pa := validDate_pos _ _ _ ha
  have pb := validDate_pos _ _ _ hb
  unfold dateData
  simp only [List.cons.injEq, and_true, Prod.mk.injEq]
  omega

theorem dateHash_proven : DateHash := by
  intro a b ha hb
  obtain ⟨y, m, d⟩ := a
  obtain ⟨y', m', d'⟩ := b
  simp only at ha hb ⊢
  have := dateData_inj y m d y' m' d' ha hb
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp only [dateHashKeyPy, HashKey.tuple1.injEq]; exact this
  · simp only [dateHashKeyC, HashKey.bytes.injEq]; exact this

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
    unfold dateSubDeltaPy dateSubDeltaC normalizeDateC
    simp only [hneg, bind, Except.bind]
    unfold dateAddC normalizeDateC at main
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
    simp [dateNewPy, checkDateFieldsArgPy, stateOf, pyIndex, bind, Except.bind]
  refine ⟨?_, fun hv => by rw [e]; exact checkDate_ok y m d hv⟩
  rw [e]
  simp [dateNewC, datetimeDateClinicC, datetimeDateImplC, checkDateC_eq, clinicArity, stateOf, parseI_int, h1, h2, h3, bind,
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
