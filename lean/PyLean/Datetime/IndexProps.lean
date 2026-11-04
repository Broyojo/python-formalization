import PyLean.Datetime.TwinsProps
import PyLean.Datetime.TimeProps

/-!
`__index__` and the field checks: `_check_date_fields` and `_check_time_fields` call
`operator.index` on every field (Lib/_pydatetime.py:579-581, :592-595) and C converts with
`PyLong_AsInt` (`PyNumber_Index`), so an object with `__index__` is a field in both twins,
a non-int result is a `TypeError` and an exception of `__index__` propagates. `fold` is the
exception in Python: `fold not in (0, 1)` (:605) compares without `_index`, while C converts
it like every other field; `date.fromordinal` has no `_index` either.
-/

namespace PyLean.Datetime

open PyLean

/-! ### `_check_date_fields` -/

/-- `_check_date_fields(year, month, day)` on any arguments. When every argument fits a C
`int` (an int, or an object whose `__index__` returns one), it equals C's clinic wrapper
`datetime_date` with its three `PyLong_AsInt` conversions and `check_date_args`, result
and message. The values `__index__` returns are the fields; an exception of `__index__`
propagates unchanged, the year's first, then the month's, then the day's; a non-int
returned by `__index__`, and a float, are `TypeError`. -/
def CheckDateFieldsIndex : Prop :=
  ∀ (y m d : Arg) (yi mi di : Int) (e : PyExc) (x : Binary64.F64),
    (y.FitsC → m.FitsC → d.FitsC → checkDateFieldsArgPy y m d = datetimeDateClinicC [y, m, d]) ∧
    checkDateFieldsArgPy (.index (.ok (some yi))) (.index (.ok (some mi))) (.index (.ok (some di))) =
      checkDate yi mi di ∧
    checkDateFieldsArgPy (.int yi) (.int mi) (.int di) = checkDate yi mi di ∧
    checkDateFieldsArgPy (.index (.error e)) m d = .error e ∧
    checkDateFieldsArgPy (.int yi) (.index (.error e)) d = .error e ∧
    checkDateFieldsArgPy (.int yi) (.int mi) (.index (.error e)) = .error e ∧
    (checkDateFieldsArgPy (.index (.ok none)) m d).raises "TypeError" ∧
    (checkDateFieldsArgPy (.float x) m d).raises "TypeError"

theorem checkDateFieldsIndex_proven : CheckDateFieldsIndex := by
  intro y m d yi mi di e x
  refine ⟨fun hy hm hd => ?_, rfl, rfl, rfl, rfl, rfl, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩
  have hc : datetimeDateClinicC [y, m, d] = (do
      let y ← parseI y; let m ← parseI m; let d ← parseI d; datetimeDateImplC y m d) := rfl
  rw [hc, parseI_eq y hy, parseI_eq m hm, parseI_eq d hd]
  unfold checkDateFieldsArgPy datetimeDateImplC
  cases pyIndex y <;> cases pyIndex m <;> cases pyIndex d <;> try rfl
  simp only [bind, Except.bind]
  rw [checkDateC_eq]

/-- `date(a, b)` where `a.__index__()` raises `e` (and `b` is not `None`): Python binds
`day=None` and runs `_check_date_fields`, whose first `_index` raises `e`; C's clinic wrapper
counts the arguments before converting any and raises `TypeError` for the missing `day`.
This is the case `DateNewArgs` excludes. -/
def DateNewIndexMissing : Prop :=
  ∀ (e : PyExc) (b : Arg), b ≠ .none_ →
    dateCallPy [.index (.error e), b] = .error e ∧ (dateNewC [.index (.error e), b]).raises "TypeError"

theorem dateNewIndexMissing_proven : DateNewIndexMissing := by
  intro e b hb
  refine ⟨?_, ⟨_, rfl, rfl⟩⟩
  show dateNewPy (.index (.error e)) b .none_ = .error e
  rw [dateNewPy_noPickle _ _ _ hb]
  rfl

/-! ### `_check_time_fields` -/

/-- `_check_time_fields(hour, minute, second, microsecond, fold)` on any arguments. On ints
it is the int-level check (`checkTimeFieldsPy`, whose order and messages `CheckTimeFields`
pins against C `check_time_args`), with `fold` returned as the object given; the values
`__index__` returns are the fields; an exception of `__index__` propagates unchanged, in
argument order, before any range check; a non-int result of `__index__` is `TypeError`.
And `time(h, m, s, us, fold=f)` (four fields, each an int or an object whose `__index__`
returns an int, all within a C `int`, `f` an int within a C `int`) is the same in both
twins, so C's clinic conversions agree with `_index`. -/
def CheckTimeFieldsIndex : Prop :=
  ∀ (h mi s us : Arg) (a b c u f : Int) (fold : Arg) (e : PyExc),
    checkTimeFieldsArgPy (.int a) (.int b) (.int c) (.int u) (.int f) =
      (fun r => (r.1, r.2.1, r.2.2.1, r.2.2.2.1, Arg.int r.2.2.2.2)) <$> checkTimeFieldsPy a b c u f ∧
    checkTimeFieldsArgPy (.index (.ok (some a))) (.index (.ok (some b))) (.index (.ok (some c)))
        (.index (.ok (some u))) fold =
      checkTimeFieldsArgPy (.int a) (.int b) (.int c) (.int u) fold ∧
    checkTimeFieldsArgPy (.index (.error e)) mi s us fold = .error e ∧
    checkTimeFieldsArgPy (.int a) (.index (.error e)) s us fold = .error e ∧
    checkTimeFieldsArgPy (.int a) (.int b) (.index (.error e)) us fold = .error e ∧
    checkTimeFieldsArgPy (.int a) (.int b) (.int c) (.index (.error e)) fold = .error e ∧
    (checkTimeFieldsArgPy (.index (.ok none)) mi s us fold).raises "TypeError" ∧
    (h.FitsC → mi.FitsC → s.FitsC → us.FitsC → (∀ k, h ≠ .bytes k ∧ h ≠ .str k) → fitsCInt f →
      timeCallPy [h, mi, s, us] (.int f) = timeNewC [h, mi, s, us] (.int f))

theorem checkTimeFieldsIndex_proven : CheckTimeFieldsIndex := by
  intro h mi s us a b c u f fold e
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, ⟨_, rfl, rfl⟩, fun hh hm hs hu hnp hf => ?_⟩
  · simp only [checkTimeFieldsArgPy, checkTimeFieldsPy, checkFoldArgPy, pyIndex]
    cases hc : checkTime a b c u with
    | error e => simp [hc, bind, Except.bind, Functor.map, Except.map]
    | ok v =>
      obtain rfl := checkTime_ok_eq hc
      cases hf : checkFold f <;> simp [hc, hf, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  · have hst : stateOf "time" h = none := by
      cases h with
      | bytes k => exact absurd rfl (hnp k).1
      | str k => exact absurd rfl (hnp k).2
      | _ => rfl
    have hpy : timeCallPy [h, mi, s, us] (.int f) = (do
        let (h, mi, s, u, f) ← checkTimeFieldsArgPy h mi s us (.int f)
        let t ← checkTzinfoArgPy .none_
        return (⟨h, mi, s, u, f.foldVal, t⟩ : TM)) := by
      simp [timeCallPy, timeNewPy, hst]
    have hcc : timeNewC [h, mi, s, us] (.int f) = (do
        let h ← parseI h; let mi ← parseI mi; let s ← parseI s; let u ← parseI us
        let f ← parseI (.int f)
        datetimeTimeImplC h mi s u .none_ f) := by
      simp [timeNewC, hst, datetimeTimeClinicC, clinicArity]
    rw [hpy, hcc, parseI_eq h hh, parseI_eq mi hm, parseI_eq s hs, parseI_eq us hu, parseI_int f hf]
    unfold checkTimeFieldsArgPy datetimeTimeImplC
    cases pyIndex h <;> cases pyIndex mi <;> cases pyIndex s <;> cases pyIndex us <;> try rfl
    rename_i a1 a2 a3 a4
    cases hc : checkTime a1 a2 a3 a4 with
    | error e => simp [bind, Except.bind, hc]
    | ok v =>
      obtain rfl := checkTime_ok_eq hc
      simp [bind, Except.bind, hc, checkFoldArgPy, Arg.foldVal, checkTzinfoArgPy, checkTzinfoSubclassC,
        pure, Except.pure]
      cases checkFold f <;> rfl

/-! ### `fold` -/

/-- `time(fold=x)` agrees between the twins for every `fold` that fits a C `int`. -/
def TimeFoldTwins : Prop :=
  ∀ fold : Arg, fold.FitsC → SameOutcome (timeCallPy [] fold) (timeNewC [] fold)

/-- `time(fold=1.0)`: Python's `fold not in (0, 1)` finds `1.0 == 1` and accepts it; C's
`int` converter raises `TypeError` for a float. -/
theorem timeFoldTwins_refuted : ¬TimeFoldTwins := by
  intro h
  exact not_sameOutcome_ok_err _ _ ⟨0, 0, 0, 0, 1, none⟩ (by rfl) (by rfl) (h (.float Binary64.F64.one) trivial)

/-- `datetime(y, m, d, fold=x)` agrees between the twins for every `fold` that fits a C `int`. -/
def DatetimeFoldTwins : Prop :=
  ∀ fold : Arg, fold.FitsC →
    SameOutcome (datetimeCallPy [.int 2020, .int 1, .int 1] fold) (datetimeNewC [.int 2020, .int 1, .int 1] fold)

/-- `datetime(2020, 1, 1, fold=1.0)`, as for `time`. -/
theorem datetimeFoldTwins_refuted : ¬DatetimeFoldTwins := by
  intro h
  exact not_sameOutcome_ok_err _ _ ⟨2020, 1, 1, 0, 0, 0, 0, 1, none⟩ (by rfl) (by rfl)
    (h (.float Binary64.F64.one) trivial)

/-- `time(fold=x)` for every `x` in scope: Python accepts an int 0 or 1 and a float equal to
0.0 or 1.0 (`-0.0` included) and refuses every other object with `ValueError`, among them an
object whose `__index__` returns 0 or 1; C converts with `PyLong_AsInt`, so it refuses every
float with `TypeError` and accepts an `__index__` object exactly as the int it returns. On
ints the twins agree (`TimeCtorInt`). -/
def TimeFoldArg : Prop :=
  ∀ (x : Binary64.F64) (n : Int),
    ((∃ t, timeCallPy [] (.float x) = .ok t) ↔ (x.isZero = true ∨ Binary64.F64.eq x Binary64.F64.one = true)) ∧
    (timeNewC [] (.float x)).raises "TypeError" ∧
    (timeCallPy [] (.index (.ok (some n)))).raises "ValueError" ∧
    timeNewC [] (.index (.ok (some n))) = timeNewC [] (.int n)

theorem timeFoldArg_proven : TimeFoldArg := by
  intro x n
  refine ⟨?_, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl⟩
  have e : timeCallPy [] (.float x) =
      if x.isZero || Binary64.F64.eq x Binary64.F64.one then
        .ok ⟨0, 0, 0, 0, if x.isZero then 0 else 1, none⟩
      else .error (.valueError "~fold must be either 0 or 1, not <float>") := by
    simp only [timeCallPy, timeNewPy, checkTimeFieldsArgPy, checkFoldArgPy, stateOf, pyIndex]
    by_cases hz : (x.isZero || Binary64.F64.eq x Binary64.F64.one) = true
    · simp [hz, checkTime, checkTzinfoArgPy, Arg.foldVal, bind, Except.bind, pure, Except.pure]
    · simp only [Bool.not_eq_true] at hz
      simp [hz, checkTime, bind, Except.bind]
  rw [e]
  by_cases hz : (x.isZero || Binary64.F64.eq x Binary64.F64.one) = true
  · simp only [hz, ↓reduceIte]
    exact ⟨fun _ => by simpa using hz, fun _ => ⟨_, rfl⟩⟩
  · simp only [Bool.not_eq_true] at hz
    simp only [hz]
    constructor
    · rintro ⟨t, ht⟩; cases ht
    · intro h; simp_all

/-! ### `date.fromordinal` -/

/-- `date.fromordinal(x)` agrees between the twins for every argument that fits a C `int`. -/
def FromordinalIndexTwins : Prop :=
  ∀ a : Arg, a.FitsC → SameOutcome (fromordinalArgPy a) (fromordinalArgC a)

/-- `date.fromordinal(obj)` where `obj.__index__()` returns 5: C converts it and returns
`date(1, 1, 5)`; Python's `_ord2ymd` computes `n -= 1` on the object and raises
`TypeError`. -/
theorem not_sameOutcome_err_ok {α : Type} (x y : Py α) (v : α) (hx : x.isOk = false) (hy : y = .ok v) :
    ¬ SameOutcome x y := by
  subst hy; cases x <;> simp_all [SameOutcome, Except.isOk, Except.toBool]

theorem fromordinalIndexTwins_refuted : ¬FromordinalIndexTwins := by
  intro h
  exact not_sameOutcome_err_ok _ _ (1, 1, 5) (by rfl) (by decide)
    (h (.index (.ok (some 5))) (by unfold Arg.FitsC fitsCInt; decide))

/-- `date.fromordinal(x)` on every argument: an int is the int-level `fromordinalPy` and
`fromordinalC` (which `FromordinalRange` proves agree within a C `int`, with the ValueError
and OverflowError outside); an object whose `__index__` returns `n` is `fromordinal(n)` in C
and a `TypeError` in Python; an exception of `__index__` propagates in C; every argument
without `__index__` (None, str, bytes, float, any other object) is a `TypeError` in both. -/
def FromordinalArg : Prop :=
  ∀ (n : Int) (e : PyExc) (a : Arg),
    fromordinalArgPy (.int n) = fromordinalPy n ∧ fromordinalArgC (.int n) = fromordinalC n ∧
    fromordinalArgC (.index (.ok (some n))) = fromordinalArgC (.int n) ∧
    (fromordinalArgPy (.index (.ok (some n)))).raises "TypeError" ∧
    fromordinalArgC (.index (.error e)) = .error e ∧
    ((∀ m, a ≠ .int m) → (∀ r, a ≠ .index r) →
      (fromordinalArgPy a).raises "TypeError" ∧ (fromordinalArgC a).raises "TypeError")

theorem fromordinalArg_proven : FromordinalArg := by
  intro n e a
  refine ⟨rfl, rfl, rfl, ⟨_, rfl, rfl⟩, rfl, fun h1 h2 => ?_⟩
  cases a with
  | int m => exact absurd rfl (h1 m)
  | index r => exact absurd rfl (h2 r)
  | _ => exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

end PyLean.Datetime
