import PyLean.Datetime.TzProps

/-!
`time` objects and the parts of `datetime` that need no calendar arithmetic: offsets,
`repr`, `isoformat`, `replace`, `combine`, pickle state, the constructors, comparison
and hash. The type invariants are `TM.Valid`, `DT.Valid` and `TzEnv.Valid`.
-/

namespace PyLean.Datetime

open PyLean

/-- The field ranges every `time` object has. -/
def TM.Valid (t : TM) : Prop :=
  0 ≤ t.h ∧ t.h ≤ 23 ∧ 0 ≤ t.mi ∧ t.mi ≤ 59 ∧ 0 ≤ t.s ∧ t.s ≤ 59 ∧ 0 ≤ t.us ∧ t.us ≤ 999999 ∧
    (t.fold = 0 ∨ t.fold = 1) ∧ OptTzOk t.tz

/-- The field ranges every `datetime` object has. -/
def DT.Valid (dt : DT) : Prop :=
  ValidDate dt.y dt.m dt.d ∧
  0 ≤ dt.h ∧ dt.h ≤ 23 ∧ 0 ≤ dt.mi ∧ dt.mi ≤ 59 ∧ 0 ≤ dt.s ∧ dt.s ≤ 59 ∧ 0 ≤ dt.us ∧ dt.us ≤ 999999 ∧
    (dt.fold = 0 ∨ dt.fold = 1) ∧ OptTzOk dt.tz

theorem checkTime_ok (h mi s us : Int) (h1 : 0 ≤ h ∧ h ≤ 23) (h2 : 0 ≤ mi ∧ mi ≤ 59) (h3 : 0 ≤ s ∧ s ≤ 59)
    (h4 : 0 ≤ us ∧ us ≤ 999999) : checkTime h mi s us = .ok (h, mi, s, us) := by
  unfold checkTime
  simp [h1, h2, h3, h4]

theorem checkFold_ok (f : Int) (h : f = 0 ∨ f = 1) : checkFold f = .ok () := by
  unfold checkFold; simp [h]

theorem newDT_ok (dt : DT) (h : DT.Valid dt) : newDT dt = .ok dt := by
  obtain ⟨hd, h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ := h
  unfold newDT
  rw [checkDate_ok _ _ _ hd, checkTime_ok _ _ _ _ ⟨h1, h2⟩ ⟨h3, h4⟩ ⟨h5, h6⟩ ⟨h7, h8⟩, checkFold_ok _ h9]
  rfl

theorem newTM_ok (t : TM) (h : TM.Valid t) : newTM t = .ok t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ := h
  unfold newTM
  rw [checkTime_ok _ _ _ _ ⟨h1, h2⟩ ⟨h3, h4⟩ ⟨h5, h6⟩ ⟨h7, h8⟩, checkFold_ok _ h9]
  rfl

/-! ### Offsets -/

/-- `time.utcoffset()`, `.dst()`: the checked results agree between twins, for every
`tzinfo` subclass, and an accepted offset lies strictly inside ±24h. -/
def TimeOffsets : Prop :=
  ∀ (env : TzEnv) (t : TM), env.Valid → OptTzOk t.tz →
    t.utcoffsetPy env = t.utcoffsetC env ∧ t.dstPy env = t.dstC env ∧
    ∀ o, t.utcoffsetPy env = .ok (some o) → -86400000000 < o.toUs ∧ o.toUs < 86400000000

theorem timeOffsets_proven : TimeOffsets := by
  intro env t henv htz
  refine ⟨tm_utcoffset_twin env henv t htz, tm_dst_twin env henv t, ?_⟩
  intro o ho
  unfold TM.utcoffsetPy at ho
  split at ho
  · cases ho
  · cases hr : tzUtcoffsetRaw env _ none with
    | error e => rw [hr] at ho; cases ho
    | ok v => rw [hr] at ho; exact checked_range _ _ _ ho

/-- `datetime.utcoffset()`, `.dst()`: same statement for `datetime`. -/
def DatetimeOffsets : Prop :=
  ∀ (env : TzEnv) (dt : DT), env.Valid → OptTzOk dt.tz →
    dt.utcoffsetPy env = dt.utcoffsetC env ∧ dt.dstPy env = dt.dstC env ∧
    ∀ o, dt.utcoffsetPy env = .ok (some o) → -86400000000 < o.toUs ∧ o.toUs < 86400000000

theorem datetimeOffsets_proven : DatetimeOffsets := by
  intro env dt henv htz
  refine ⟨dt_utcoffset_twin env henv dt htz, dt_dst_twin env henv dt, ?_⟩
  intro o ho
  unfold DT.utcoffsetPy at ho
  split at ho
  · cases ho
  · cases hr : tzUtcoffsetRaw env _ (some dt) with
    | error e => rw [hr] at ho; cases ho
    | ok v => rw [hr] at ho; exact checked_range _ _ _ ho

theorem tzname_check_twin (r : NameRet) : SameOutcome (checkTzname r) (callTznameCheckC r) := by
  cases r <;> simp [checkTzname, callTznameCheckC, SameOutcome, PyExc.className]

theorem tzname_raw_twin (env : TzEnv) (tz : Tz) (a : Option DT) (h : tz.Ok) :
    tzTznameRawPy env tz a = tzTznameRawC env tz a := by
  unfold tzTznameRawPy tzTznameRawC
  split
  · rename_i off name hk
    rw [timezoneName_proven tz off name hk h]
  · rfl

/-- `time.tzname()` and `datetime.tzname()`: the twins agree on the name or on the
exception class, for every `tzinfo` subclass. -/
def TznameTwins : Prop :=
  ∀ (env : TzEnv) (t : TM) (dt : DT), OptTzOk t.tz → OptTzOk dt.tz →
    SameOutcome (t.tznamePy env) (t.tznameC env) ∧ SameOutcome (dt.tznamePy env) (dt.tznameC env)

theorem tznameTwins_proven : TznameTwins := by
  intro env t dt h1 h2
  constructor
  · unfold TM.tznamePy TM.tznameC
    split
    · exact sameOutcome_refl _
    · rename_i tz htz
      rw [htz] at h1
      rw [tzname_raw_twin env tz none h1]
      cases tzTznameRawC env tz none with
      | error e => exact sameOutcome_refl (.error e)
      | ok v => exact tzname_check_twin v
  · unfold DT.tznamePy DT.tznameC
    split
    · exact sameOutcome_refl _
    · rename_i tz htz
      rw [htz] at h2
      rw [tzname_raw_twin env tz (some dt) h2]
      cases tzTznameRawC env tz (some dt) with
      | error e => exact sameOutcome_refl (.error e)
      | ok v => exact tzname_check_twin v

/-! ### `repr` and `isoformat` -/

/-- `repr(time)`: the twins produce the same text. -/
def TimeRepr : Prop := ∀ (env : TzEnv) (t : TM), timeReprPy env t = timeReprC env t

theorem tmReprBase_twin (t : TM) : tmReprBasePy t = tmReprBaseC t := by
  have e : ("datetime.time(" : String) = "datetime." ++ "time(" := by decide
  unfold tmReprBasePy tmReprBaseC
  by_cases h1 : t.us = 0
  · by_cases h2 : t.s = 0
    · simp [h1, h2, getClassModule, toString, e, String.append_assoc]
    · simp [h1, h2, getClassModule, toString, e, String.append_assoc]
  · simp [h1, getClassModule, toString, e, String.append_assoc]

theorem timeRepr_proven : TimeRepr := by
  intro env t
  unfold timeReprPy timeReprC
  rw [tmReprBase_twin]

theorem dtReprBase_twin (dt : DT) : dtReprBasePy dt = dtReprBaseC dt := by
  have e : ("datetime.datetime(" : String) = "datetime." ++ "datetime(" := by decide
  unfold dtReprBasePy dtReprBaseC
  by_cases h1 : dt.us = 0
  · by_cases h2 : dt.s = 0
    · simp [h1, h2, getClassModule, toString, e, String.append_assoc]
    · simp [h1, h2, getClassModule, toString, e, String.append_assoc]
  · simp [h1, getClassModule, toString, e, String.append_assoc]

/-- `repr(datetime)`: the twins produce the same text unless both `fold=1` and a
tzinfo appear, where C prints `fold` first and Python `tzinfo` first. -/
def DatetimeRepr : Prop :=
  ∀ (env : TzEnv) (dt : DT), (dt.fold = 0 ∨ dt.tz = none) → dtReprPy env dt = dtReprC env dt

theorem datetimeRepr_proven : DatetimeRepr := by
  intro env dt hf
  unfold dtReprPy dtReprC
  rw [dtReprBase_twin]
  rcases hf with h0 | h0
  · simp [appendFold, h0]
  · simp [appendTzinfo, h0]

/-- `time.isoformat()` and `str(time)`: the twins agree for every `timespec`. -/
def TimeIsoformatTwins : Prop :=
  ∀ (env : TzEnv) (t : TM) (spec : TimeSpec), env.Valid → OptTzOk t.tz →
    tmIsoformatPy env t spec = tmIsoformatC env t spec

theorem timeIsoformatTwins_proven : TimeIsoformatTwins := by
  intro env t spec henv h
  unfold tmIsoformatPy tmIsoformatC tmTzstrPy
  rw [tm_utcoffset_twin env henv t h]
  cases t.utcoffsetC env <;> rfl

/-- `datetime.isoformat()` and `str(datetime)`: the twins agree for every `sep` and
`timespec`. -/
def DatetimeIsoformatTwins : Prop :=
  ∀ (env : TzEnv) (dt : DT) (sep : Char) (spec : TimeSpec), env.Valid → OptTzOk dt.tz →
    dtIsoformatPy env dt sep spec = dtIsoformatC env dt sep spec

theorem datetimeIsoformatTwins_proven : DatetimeIsoformatTwins := by
  intro env dt sep spec henv h
  unfold dtIsoformatPy dtIsoformatC
  rw [dt_utcoffset_twin env henv dt h]

/-! ### `replace`, `combine`, parts -/

/-- `t.replace()` and `dt.replace()` with no argument return an equal object;
`datetime.combine(d.date(), d.timetz()) == d`, and `d.time()` drops only the tzinfo. -/
def ReplaceCombine : Prop :=
  ∀ (t : TM) (dt : DT), t.Valid → dt.Valid →
    tmReplace t none none none none none none = .ok t ∧
    dtReplace dt none none none none none none none none none = .ok dt ∧
    dtCombine (dtDate dt) (dtTimetz dt) none = .ok dt ∧
    dtCombine (dtDate dt) (dtTime dt) (some dt.tz) = .ok dt ∧
    (dtTime dt).tz = none

theorem replaceCombine_proven : ReplaceCombine := by
  intro t dt ht hd
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · unfold tmReplace; simp only [Option.getD_none]; exact newTM_ok t ht
  · unfold dtReplace; simp only [Option.getD_none]; exact newDT_ok dt hd
  · unfold dtCombine; simp only [Option.getD_none]; exact newDT_ok dt hd
  · unfold dtCombine; simp only [Option.getD_some]; exact newDT_ok dt hd

/-! ### Pickle state -/

/-- `time(*t.__reduce_ex__(p)[1])`: protocols above 3 keep `fold` in the top bit of
the first byte, in both twins; older protocols return `fold=0`. -/
def TimePickle : Prop :=
  ∀ (t : TM) (p : Int), t.Valid →
    (p > 3 → tmSetstate t.tz (tmGetstate t p) = some t) ∧
    (p ≤ 3 → tmSetstate t.tz (tmGetstate t p) = some { t with fold := 0 })

theorem timePickle_proven : TimePickle := by
  intro t p ht
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ := ht
  obtain ⟨hh, mi, s, us, fold, tz⟩ := t
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢
  have eu : (((us / 65536).toNat * 256 + (us / 256 % 256).toNat) * 256 + (us % 256).toNat : Nat) = us.toNat := by
    omega
  have ehm : (hh.toNat : Int) = hh ∧ (mi.toNat : Int) = mi ∧ (s.toNat : Int) = s ∧ (us.toNat : Int) = us := by
    omega
  constructor
  · intro hp
    rcases h9 with h0 | h0
    · subst h0
      have hlt : ¬ hh.toNat > 127 := by omega
      have e1 : tmGetstate ⟨hh, mi, s, us, 0, tz⟩ p = [hh.toNat, mi.toNat, s.toNat, (us / 65536).toNat,
          (us / 256 % 256).toNat, (us % 256).toNat] := by simp [tmGetstate, timeData]
      rw [e1]
      simp only [tmSetstate, hlt, ite_false, Option.some.injEq, TM.mk.injEq, and_true]
      omega
    · subst h0
      have hgt : hh.toNat + 128 > 127 := by omega
      have e1 : tmGetstate ⟨hh, mi, s, us, 1, tz⟩ p = [hh.toNat + 128, mi.toNat, s.toNat, (us / 65536).toNat,
          (us / 256 % 256).toNat, (us % 256).toNat] := by simp [tmGetstate, timeData, hp]
      rw [e1]
      simp only [tmSetstate, hgt, ite_true, Option.some.injEq, TM.mk.injEq, and_true]
      omega
  · intro hp
    have hlt : ¬ hh.toNat > 127 := by omega
    have hne : ¬ (fold ≠ 0 ∧ p > 3) := by omega
    have e1 : tmGetstate ⟨hh, mi, s, us, fold, tz⟩ p = [hh.toNat, mi.toNat, s.toNat, (us / 65536).toNat,
        (us / 256 % 256).toNat, (us % 256).toNat] := by simp [tmGetstate, timeData, hne]
    rw [e1]
    simp only [tmSetstate, hlt, ite_false, Option.some.injEq, TM.mk.injEq, and_true]
    omega

/-- `datetime(*d.__reduce_ex__(p)[1])`: same statement, `fold` is the top bit of
the month byte. -/
def DatetimePickle : Prop :=
  ∀ (dt : DT) (p : Int), dt.Valid →
    (p > 3 → dtSetstate dt.tz (dtGetstate dt p) = some dt) ∧
    (p ≤ 3 → dtSetstate dt.tz (dtGetstate dt p) = some { dt with fold := 0 })

set_option maxRecDepth 20000 in
theorem datetimePickle_proven : DatetimePickle := by
  intro dt p hv
  obtain ⟨hd, h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ := hv
  have pd := validDate_pos _ _ _ hd
  obtain ⟨y, m, d, hh, mi, s, us, fold, tz⟩ := dt
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 pd ⊢
  have eu : (((us / 65536).toNat * 256 + (us / 256 % 256).toNat) * 256 + (us % 256).toNat : Nat) = us.toNat := by
    omega
  have ey : ((y / 256).toNat * 256 + (y % 256).toNat : Nat) = y.toNat := by omega
  have hm7 : ¬ m.toNat > 127 := by omega
  have hm8 : m.toNat + 128 > 127 := by omega
  have base : dtData ⟨y, m, d, hh, mi, s, us, fold, tz⟩ = [(y / 256).toNat, (y % 256).toNat, m.toNat, d.toNat,
      hh.toNat, mi.toNat, s.toNat, (us / 65536).toNat, (us / 256 % 256).toNat, (us % 256).toNat] := rfl
  constructor
  · intro hp
    rcases h9 with h0 | h0
    · subst h0
      have e1 : dtGetstate ⟨y, m, d, hh, mi, s, us, 0, tz⟩ p = dtData ⟨y, m, d, hh, mi, s, us, 0, tz⟩ := by
        simp [dtGetstate, base]
      rw [e1, base]
      simp only [dtSetstate, hm7, ite_false, Option.some.injEq, DT.mk.injEq, and_true]
      omega
    · subst h0
      have e1 : dtGetstate ⟨y, m, d, hh, mi, s, us, 1, tz⟩ p = [(y / 256).toNat, (y % 256).toNat, m.toNat + 128,
          d.toNat, hh.toNat, mi.toNat, s.toNat, (us / 65536).toNat, (us / 256 % 256).toNat, (us % 256).toNat] := by
        simp [dtGetstate, base, hp]
      rw [e1]
      simp only [dtSetstate, hm8, ite_true, Option.some.injEq, DT.mk.injEq, and_true]
      omega
  · intro hp
    have hne : ¬ (fold ≠ 0 ∧ p > 3) := by omega
    have e1 : dtGetstate ⟨y, m, d, hh, mi, s, us, fold, tz⟩ p = dtData ⟨y, m, d, hh, mi, s, us, fold, tz⟩ := by
      simp [dtGetstate, base, hne]
    rw [e1, base]
    simp only [dtSetstate, hm7, ite_false, Option.some.injEq, DT.mk.injEq, and_true]
    omega

/-- `time(h, m, s, us, tz, fold=f)` with C-`int` fields, `fold` among them: the twins agree.
Fields outside `int` are the rejected class of gh-158778; for `fold`, `TimeCtorFoldTwins` has
that case on record as a refutation. -/
def TimeCtorInt : Prop :=
  ∀ (h mi s us f : Int) (tz : Arg), fitsCInt h → fitsCInt mi → fitsCInt s → fitsCInt us → fitsCInt f →
    (tz = .none_ ∨ ∃ t, tz = .tz t) →
    timeNewPy (.int h) (.int mi) (.int s) (.int us) tz (.int f) =
      timeNewC [.int h, .int mi, .int s, .int us, tz] (.int f)

theorem checkTime_ok_eq {h mi s us : Int} {v : Int × Int × Int × Int} (hv : checkTime h mi s us = .ok v) :
    v = (h, mi, s, us) := by
  unfold checkTime at hv
  split at hv
  · cases hv
  · split at hv
    · cases hv
    · split at hv
      · cases hv
      · split at hv
        · cases hv
        · cases hv; rfl

theorem timeCtorInt_proven : TimeCtorInt := by
  intro h mi s us f tz h1 h2 h3 h4 h5 htz
  rcases htz with rfl | ⟨t, rfl⟩ <;>
  · cases hc : checkTime h mi s us with
    | error e =>
      simp [timeNewPy, timeNewC, datetimeTimeClinicC, datetimeTimeImplC, clinicArity, stateOf, pyIndex, parseI_int,
        checkTimeFieldsArgPy, checkFoldArgPy, Arg.foldVal, hc,
        h1, h2, h3, h4, h5, checkTzinfoArgPy, checkTzinfoSubclassC, bind, Except.bind, pure, Except.pure]
    | ok v =>
      obtain rfl := checkTime_ok_eq hc
      simp [timeNewPy, timeNewC, datetimeTimeClinicC, datetimeTimeImplC, clinicArity, stateOf, pyIndex, parseI_int,
        checkTimeFieldsArgPy, checkFoldArgPy, Arg.foldVal, hc,
        h1, h2, h3, h4, h5, checkTzinfoArgPy, checkTzinfoSubclassC, bind, Except.bind, pure, Except.pure]
      cases checkFold f <;> rfl

/-- `datetime(y, ..., us, tz, fold=f)` with C-`int` fields: the twins agree. -/
def DatetimeCtorInt : Prop :=
  ∀ (y m d h mi s us f : Int) (tz : Arg), fitsCInt y → fitsCInt m → fitsCInt d → fitsCInt h → fitsCInt mi →
    fitsCInt s → fitsCInt us → fitsCInt f → (tz = .none_ ∨ ∃ t, tz = .tz t) →
    datetimeNewPy (.int y) (.int m) (.int d) (.int h) (.int mi) (.int s) (.int us) tz (.int f) =
      datetimeNewC [.int y, .int m, .int d, .int h, .int mi, .int s, .int us, tz] (.int f)

theorem datetimeCtorInt_proven : DatetimeCtorInt := by
  intro y m d h mi s us f tz h1 h2 h3 h4 h5 h6 h7 h8 htz
  rcases htz with rfl | ⟨t, rfl⟩ <;>
  · cases hd : checkDate y m d with
    | error e =>
      simp [datetimeNewPy, datetimeNewC, datetimeDatetimeClinicC, datetimeDatetimeImplC, clinicArity, stateOf, pyIndex,
        parseI_int, checkDateFieldsArgPy, checkTimeFieldsArgPy, checkFoldArgPy, Arg.foldVal, hd,
        h1, h2, h3, h4, h5, h6, h7, h8, checkTzinfoArgPy, checkTzinfoSubclassC, bind, Except.bind, pure,
        Except.pure]
    | ok r =>
      obtain rfl := (checkDate_inv y m d r hd).2
      cases hc : checkTime h mi s us with
      | error e =>
        simp [datetimeNewPy, datetimeNewC, datetimeDatetimeClinicC, datetimeDatetimeImplC, clinicArity, stateOf, pyIndex,
          parseI_int, checkDateFieldsArgPy, checkTimeFieldsArgPy, checkFoldArgPy, Arg.foldVal, hd, hc,
          h1, h2, h3, h4, h5, h6, h7, h8, checkTzinfoArgPy, checkTzinfoSubclassC, bind, Except.bind, pure,
          Except.pure]
      | ok v =>
        obtain rfl := checkTime_ok_eq hc
        simp [datetimeNewPy, datetimeNewC, datetimeDatetimeClinicC, datetimeDatetimeImplC, clinicArity, stateOf, pyIndex,
          parseI_int, checkDateFieldsArgPy, checkTimeFieldsArgPy, checkFoldArgPy, Arg.foldVal, hd, hc,
          h1, h2, h3, h4, h5, h6, h7, h8, checkTzinfoArgPy, checkTzinfoSubclassC, bind, Except.bind, pure,
          Except.pure]
        cases checkFold f <;> rfl

/-- `time(h, m, s, us, tz, fold=f)` with C-`int` fields and any int `fold`: the twins agree. -/
def TimeCtorFoldTwins : Prop :=
  ∀ (h mi s us f : Int) (tz : Arg), fitsCInt h → fitsCInt mi → fitsCInt s → fitsCInt us →
    (tz = .none_ ∨ ∃ t, tz = .tz t) →
    timeNewPy (.int h) (.int mi) (.int s) (.int us) tz (.int f) =
      timeNewC [.int h, .int mi, .int s, .int us, tz] (.int f)

/-- `time(0, 0, 0, 0, None, fold=2**31)`: Python raises `ValueError` from the check on `fold`,
and C stops at the clinic `int` conversion with `OverflowError`. -/
theorem timeCtorFoldTwins_refuted : ¬TimeCtorFoldTwins := by
  intro h
  have hf : fitsCInt 0 := by unfold fitsCInt; decide
  have h1 := h 0 0 0 0 (2 ^ 31) .none_ hf hf hf hf (Or.inl rfl)
  have e1 : timeNewPy (.int 0) (.int 0) (.int 0) (.int 0) .none_ (.int (2 ^ 31)) =
      .error (.valueError s!"fold must be either 0 or 1, not {(2 ^ 31 : Int)}") := rfl
  have e2 : timeNewC [.int 0, .int 0, .int 0, .int 0, .none_] (.int (2 ^ 31)) =
      .error (.overflowError "Python int too large to convert to C int") := rfl
  rw [e1, e2] at h1
  simp at h1

/-- `datetime(y, ..., us, tz, fold=f)` with C-`int` fields and any int `fold`: the twins agree. -/
def DatetimeCtorFoldTwins : Prop :=
  ∀ (y m d h mi s us f : Int) (tz : Arg), fitsCInt y → fitsCInt m → fitsCInt d → fitsCInt h → fitsCInt mi →
    fitsCInt s → fitsCInt us → (tz = .none_ ∨ ∃ t, tz = .tz t) →
    datetimeNewPy (.int y) (.int m) (.int d) (.int h) (.int mi) (.int s) (.int us) tz (.int f) =
      datetimeNewC [.int y, .int m, .int d, .int h, .int mi, .int s, .int us, tz] (.int f)

/-- `datetime(1, 1, 1, 0, 0, 0, 0, None, fold=2**31)`, as for `time`. -/
theorem datetimeCtorFoldTwins_refuted : ¬DatetimeCtorFoldTwins := by
  intro h
  have hf : fitsCInt 0 := by unfold fitsCInt; decide
  have hg : fitsCInt 1 := by unfold fitsCInt; decide
  have h1 := h 1 1 1 0 0 0 0 (2 ^ 31) .none_ hg hg hg hf hf hf hf (Or.inl rfl)
  have e1 : datetimeNewPy (.int 1) (.int 1) (.int 1) (.int 0) (.int 0) (.int 0) (.int 0) .none_ (.int (2 ^ 31)) =
      .error (.valueError s!"fold must be either 0 or 1, not {(2 ^ 31 : Int)}") := rfl
  have e2 : datetimeNewC [.int 1, .int 1, .int 1, .int 0, .int 0, .int 0, .int 0, .none_] (.int (2 ^ 31)) =
      .error (.overflowError "Python int too large to convert to C int") := rfl
  rw [e1, e2] at h1
  simp at h1

/-! ### Comparison and hash -/

theorem time_memcmp (a b : TM) (ha : a.Valid) (hb : b.Valid) :
    memcmpBytes (timeData a) (timeData b) = cmpTuple a.base b.base := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, _⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, _⟩ := hb
  unfold timeData TM.base
  rw [mc_field _ _ a1 b1, mc_field _ _ a3 b3, mc_field _ _ a5 b5, mc_us _ _ a7 b7 (by omega) (by omega),
    cmpTuple_cons a.h b.h [a.mi, a.s, a.us] [b.mi, b.s, b.us] rfl, cmpTuple_cons a.mi b.mi [a.s, a.us] [b.s, b.us] rfl,
    cmpTuple_cons a.s b.s [a.us] [b.us] rfl, cmpTuple_cons a.us b.us [] [] rfl, cmpTuple_nil]

/-- `time` comparison when no offset arithmetic is needed (same tzinfo object, both
naive, or equal offsets): the twins agree, field by field. -/
def TimeCompareBase : Prop :=
  ∀ (env : TzEnv) (op : CmpOp) (a b : TM), env.Valid → a.Valid → b.Valid → sameTz a.tz b.tz = true →
    SameOutcome (tmRichPy env op a b) (tmRichC env op a b)

theorem timeCompareBase_proven : TimeCompareBase := by
  intro env op a b _ ha hb hs
  have hm := time_memcmp a b ha hb
  have hc : tmCmpPy env a b true = .ok (cmpTuple a.base b.base) ∧
      tmCmpPy env a b false = .ok (cmpTuple a.base b.base) := by
    simp [tmCmpPy, hs, bind, Except.bind, pure, Except.pure]
  have hr : tmRichC env op a b = .ok (diffToBool (cmpTuple a.base b.base) op) := by
    simp [tmRichC, hs, hm, bind, Except.bind, pure, Except.pure]
  rw [hr]
  generalize cmpTuple a.base b.base = c at hc
  by_cases h0 : c = 0 <;>
    cases op <;> simp [tmRichPy, hc.1, hc.2, h0, bind, Except.bind, pure, Except.pure, SameOutcome, diffToBool]

/-- An environment with no `tzinfo` subclass in play. -/
def emptyEnv : TzEnv := ⟨fun _ _ => .ok .none, fun _ _ => .ok .none, fun _ _ => .ok .none, fun _ => ""⟩

theorem emptyEnv_valid : emptyEnv.Valid := ⟨fun _ _ _ h => (by cases h), fun _ _ _ h => (by cases h)⟩

/-- `time` comparison with different offsets: C and Python agree for all valid times
and all `tzinfo`. -/
def TimeCompareTwins : Prop :=
  ∀ (env : TzEnv) (op : CmpOp) (a b : TM), env.Valid → a.Valid → b.Valid →
    SameOutcome (tmRichPy env op a b) (tmRichC env op a b)

/-- `time(12, 0, 30, tzinfo=timezone(timedelta(seconds=30))) == time(12, tzinfo=utc)`:
the same instant. C says yes; Python floors the offset to minutes and says no. -/
theorem timeCompareTwins_refuted : ¬TimeCompareTwins := by
  intro h
  let a : TM := ⟨12, 0, 30, 0, 0, some ⟨1, .timezone ⟨0, 30, 0⟩ none⟩⟩
  let b : TM := ⟨12, 0, 0, 0, 0, some tzUTC⟩
  have h1 := h emptyEnv .eq a b emptyEnv_valid
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, Or.inl rfl,
      by simp [a, OptTzOk, Tz.Ok, Delta.Valid, MAX_DELTA_DAYS, Delta.toUs]⟩
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, Or.inl rfl,
      by simp [b, OptTzOk, Tz.Ok, tzUTC, Delta.Valid, MAX_DELTA_DAYS, Delta.toUs]⟩
  have e1 : tmRichPy emptyEnv .eq a b = .ok false := by decide
  have e2 : tmRichC emptyEnv .eq a b = .ok true := by decide
  rw [e1, e2] at h1
  simp [SameOutcome] at h1

/-- `hash(time)` returns a value for every time with a valid offset. -/
def TimeHashTotal : Prop :=
  ∀ (env : TzEnv) (a : TM), env.Valid → a.Valid → (∃ o, a.utcoffsetPy env = .ok o) →
    ∃ k, tmHashKeyPy env a = .ok k

/-- `hash(_pydatetime.time(12, tzinfo=timezone(timedelta(seconds=30))))` raises
`AssertionError('whole minute')`. -/
theorem timeHashTotal_refuted : ¬TimeHashTotal := by
  intro h
  let a : TM := ⟨12, 0, 0, 0, 0, some ⟨1, .timezone ⟨0, 30, 0⟩ none⟩⟩
  have hv : a.Valid := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    Or.inl rfl, by simp [a, OptTzOk, Tz.Ok, Delta.Valid, MAX_DELTA_DAYS, Delta.toUs]⟩
  obtain ⟨k, hk⟩ := h emptyEnv a emptyEnv_valid hv ⟨some ⟨0, 30, 0⟩, by decide⟩
  have e : tmHashKeyPy emptyEnv a = .error (.assertionError "whole minute") := by decide
  rw [e] at hk
  cases hk

/-- Equal `time` objects hash alike in C: `a == b` implies `hash(a) == hash(b)`. -/
def TimeEqHash : Prop :=
  ∀ (env : TzEnv) (a b : TM), env.Valid → a.Valid → b.Valid → tmRichC env .eq a b = .ok true →
    tmHashKeyC env a = tmHashKeyC env b

/-- With offsets of 1 and 2 microseconds, `time(0, tzinfo=a) == time(0, tzinfo=b)` in
C (the comparison drops the offsets' microseconds), yet the hashes differ. -/
theorem timeEqHash_refuted : ¬TimeEqHash := by
  intro h
  let a : TM := ⟨0, 0, 0, 0, 0, some ⟨1, .timezone ⟨0, 0, 1⟩ none⟩⟩
  let b : TM := ⟨0, 0, 0, 0, 0, some ⟨2, .timezone ⟨0, 0, 2⟩ none⟩⟩
  have h1 := h emptyEnv a b emptyEnv_valid
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, Or.inl rfl,
      by simp [a, OptTzOk, Tz.Ok, Delta.Valid, MAX_DELTA_DAYS, Delta.toUs]⟩
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, Or.inl rfl,
      by simp [b, OptTzOk, Tz.Ok, Delta.Valid, MAX_DELTA_DAYS, Delta.toUs]⟩
    (by decide)
  have : tmHashKeyC emptyEnv a ≠ tmHashKeyC emptyEnv b := by decide
  exact this h1

end PyLean.Datetime
