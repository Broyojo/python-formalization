import PyLean.Datetime.TimeProps
import PyLean.Datetime.DateProps

/-!
The C constructors that may call a subclass (Modules/_datetimemodule.c:1166-1373, CPython
3.15.2): `new_date_ex`, `new_date_subclass_ex`, `new_datetime_ex`, `new_time_ex`,
`call_subclass_fold`, `new_datetime_subclass_fold_ex` and `new_time_subclass_fold_ex`, against
the Python expressions they stand for: `cls(y, m, d)` (Py:1041, 1057, 1082, 1192) and
`type(self)(..., fold=fold)` (Py:1747, 2116-2117).

A subclass is abstracted by what calling it returns (`SubCall`): a fallible function of the
positional arguments and the `fold` keyword (`none` when it is not passed). Classes are
compared by identity (a metaclass overriding `__call__` is a subclass call like any other).
-/

namespace PyLean.Datetime

open PyLean

/-- What `cls(*args, **kwargs)` does for a subclass: the positional arguments and the `fold`
keyword (`none`: not passed). -/
abbrev SubCall (α : Type) := List Arg → Option Int → Py α

/-- `call_subclass_fold(cls, fold, format, ...)`, :1254-1285: `cls(*args)`, with
`fold=fold` added as a keyword only when `fold` is nonzero (:1265-1278). -/
def callSubclassFoldC {α : Type} (cls : SubCall α) (fold : Int) (args : List Arg) : Py α :=
  cls args (if fold ≠ 0 then some fold else none)

/-- `new_date_ex`, :1166-1179: `check_date_args`, then a new date (allocation aside). A date
is the midnight `DT` without tzinfo in this result type. -/
def newDateExC (y m d : Int) : Py DT := do
  checkDateArgsC y m d
  return ⟨y, m, d, 0, 0, 0, 0, 0, none⟩

/-- `new_datetime_ex`, :1243-1248: `new_datetime_ex2` with `fold = 0`. `new_datetime_ex2`
(:1209-1240: `check_date_args`, `check_time_args`, `check_tzinfo_subclass`) is
`datetimeDatetimeImplC`. It is also the C API's `DateTime_FromDateAndTime` (:7393). -/
def newDatetimeExC (y m d h mi s us : Int) (tz : Arg) : Py DT :=
  datetimeDatetimeImplC y m d h mi s us tz 0

/-- `new_time_ex`, :1348-1352: `new_time_ex2` (:1316-1345, `datetimeTimeImplC`) with
`fold = 0`. Only the C API's `Time_FromTime` (:7394) calls it. -/
def newTimeExC (h mi s us : Int) (tz : Arg) : Py TM :=
  datetimeTimeImplC h mi s us tz 0

/-- The `cls` of `new_date_subclass_ex`. -/
inductive DateClsC where
  | date
  | datetime
  | sub (call : SubCall DT)

/-- `new_date_subclass_ex(year, month, day, cls)`, :1191-1206: the `date` fast path
`new_date_ex`, the `datetime` fast path `new_datetime_ex(..., 0, 0, 0, 0, Py_None, cls)`,
otherwise `PyObject_CallFunction(cls, "iii", year, month, day)`. -/
def newDateSubclassExC (y m d : Int) : DateClsC → Py DT
  | .date => newDateExC y m d
  | .datetime => newDatetimeExC y m d 0 0 0 0 .none_
  | .sub call => call [.int y, .int m, .int d] none

/-- Python's `cls(y, m, d)`: `date(y, m, d)` (Py:1153-1184), `datetime(y, m, d)` with the
defaults `0, 0, 0, 0, None, fold=0` (Py:1800-1833), or the subclass call. -/
def dateClsCallPy (y m d : Int) : DateClsC → Py DT
  | .date => (fun r => (⟨r.1, r.2.1, r.2.2, 0, 0, 0, 0, 0, none⟩ : DT)) <$> dateNewPy (.int y) (.int m) (.int d)
  | .datetime => datetimeNewPy (.int y) (.int m) (.int d) (.int 0) (.int 0) (.int 0) (.int 0) .none_ (.int 0)
  | .sub call => call [.int y, .int m, .int d] none

/-- The `cls` of `new_datetime_subclass_fold_ex` and `new_time_subclass_fold_ex`: the base
class itself (the fast path) or another class. -/
inductive ClsC (α : Type) where
  | base
  | sub (call : SubCall α)

/-- `new_datetime_subclass_fold_ex`, :1288-1305: the fast path `new_datetime` (`new_datetime_ex2`
with `DATETIME_TYPE`) for `datetime`, else `call_subclass_fold(cls, fold, "iiiiiiiO", ...)`. -/
def newDatetimeSubclassFoldExC (y m d h mi s us : Int) (tz : Arg) (fold : Int) : ClsC DT → Py DT
  | .base => datetimeDatetimeImplC y m d h mi s us tz fold
  | .sub call => callSubclassFoldC call fold [.int y, .int m, .int d, .int h, .int mi, .int s, .int us, tz]

/-- `datetime.replace`'s `type(self)(year, month, day, hour, minute, second, microsecond,
tzinfo, fold=fold)`, Py:2116-2117: `fold` is always passed. -/
def dtClsCallFoldPy (y m d h mi s us : Int) (tz : Arg) (fold : Int) : ClsC DT → Py DT
  | .base => datetimeNewPy (.int y) (.int m) (.int d) (.int h) (.int mi) (.int s) (.int us) tz (.int fold)
  | .sub call => call [.int y, .int m, .int d, .int h, .int mi, .int s, .int us, tz] (some fold)

/-- `new_time_subclass_fold_ex`, :1358-1373: `new_time` for `time`, else
`call_subclass_fold(cls, fold, "iiiiO", ...)`. -/
def newTimeSubclassFoldExC (h mi s us : Int) (tz : Arg) (fold : Int) : ClsC TM → Py TM
  | .base => datetimeTimeImplC h mi s us tz fold
  | .sub call => callSubclassFoldC call fold [.int h, .int mi, .int s, .int us, tz]

/-- `time.replace`'s `type(self)(hour, minute, second, microsecond, tzinfo, fold=fold)`,
Py:1747. -/
def tmClsCallFoldPy (h mi s us : Int) (tz : Arg) (fold : Int) : ClsC TM → Py TM
  | .base => timeNewPy (.int h) (.int mi) (.int s) (.int us) tz (.int fold)
  | .sub call => call [.int h, .int mi, .int s, .int us, tz] (some fold)

/-! ### Bridges to the constructor models -/

theorem datetimeNewPy_impl (y m d h mi s us f : Int) (tz : Arg) (h1 : fitsCInt y) (h2 : fitsCInt m)
    (h3 : fitsCInt d) (h4 : fitsCInt h) (h5 : fitsCInt mi) (h6 : fitsCInt s) (h7 : fitsCInt us)
    (h8 : fitsCInt f) (htz : tz = .none_ ∨ ∃ t, tz = .tz t) :
    datetimeNewPy (.int y) (.int m) (.int d) (.int h) (.int mi) (.int s) (.int us) tz (.int f) =
      datetimeDatetimeImplC y m d h mi s us tz f := by
  rw [datetimeCtorInt_proven y m d h mi s us f tz h1 h2 h3 h4 h5 h6 h7 h8 htz]
  rcases htz with rfl | ⟨t, rfl⟩ <;>
  · simp [datetimeNewC, datetimeDatetimeClinicC, clinicArity, stateOf, parseI_int, h1, h2, h3, h4, h5, h6, h7,
      h8, bind, Except.bind, pure, Except.pure]

theorem timeNewPy_impl (h mi s us f : Int) (tz : Arg) (h4 : fitsCInt h) (h5 : fitsCInt mi)
    (h6 : fitsCInt s) (h7 : fitsCInt us) (h8 : fitsCInt f) (htz : tz = .none_ ∨ ∃ t, tz = .tz t) :
    timeNewPy (.int h) (.int mi) (.int s) (.int us) tz (.int f) = datetimeTimeImplC h mi s us tz f := by
  rw [timeCtorInt_proven h mi s us f tz h4 h5 h6 h7 h8 htz]
  rcases htz with rfl | ⟨t, rfl⟩ <;>
  · simp [timeNewC, datetimeTimeClinicC, clinicArity, stateOf, parseI_int, h4, h5, h6, h7, h8, bind,
      Except.bind, pure, Except.pure]

/-! ### Properties -/

/-- `new_date_subclass_ex(y, m, d, cls)` is Python's `cls(y, m, d)` for every class and all
C-int fields: for `date` the fast path checks the fields exactly as `date(y, m, d)` does (the
same `ValueError` text), for `datetime` as `datetime(y, m, d)` does, giving midnight, and
another class is called with the three fields as positional arguments in that order and no
keyword. Invalid fields are `ValueError` on both fast paths; valid ones give the date. -/
def DateSubclassCtor : Prop :=
  ∀ y m d : Int, fitsCInt y → fitsCInt m → fitsCInt d →
    (∀ cls : DateClsC, newDateSubclassExC y m d cls = dateClsCallPy y m d cls) ∧
    (¬ ValidDate y m d →
      (newDateSubclassExC y m d .date).raises "ValueError" ∧ (newDateSubclassExC y m d .datetime).raises "ValueError") ∧
    (ValidDate y m d →
      newDateSubclassExC y m d .date = .ok ⟨y, m, d, 0, 0, 0, 0, 0, none⟩ ∧
      newDateSubclassExC y m d .datetime = .ok ⟨y, m, d, 0, 0, 0, 0, 0, none⟩)

theorem checkDate_err_value (y m d : Int) (h : ¬ ValidDate y m d) : (checkDate y m d).raises "ValueError" := by
  unfold checkDate
  split
  · exact ⟨_, rfl, rfl⟩
  · split
    · exact ⟨_, rfl, rfl⟩
    · simp only
      split
      · exact ⟨_, rfl, rfl⟩
      · exfalso; apply h; unfold ValidDate; omega

theorem newDateExC_eq (y m d : Int) :
    newDateExC y m d = (fun r => (⟨r.1, r.2.1, r.2.2, 0, 0, 0, 0, 0, none⟩ : DT)) <$> checkDate y m d := by
  have e := checkDateC_eq y m d
  unfold checkDateC at e
  unfold newDateExC
  rw [← e]
  cases checkDateArgsC y m d <;> rfl

theorem newDatetimeExC_date (y m d : Int) :
    newDatetimeExC y m d 0 0 0 0 .none_ = (fun r => (⟨r.1, r.2.1, r.2.2, 0, 0, 0, 0, 0, none⟩ : DT)) <$> checkDate y m d := by
  unfold newDatetimeExC datetimeDatetimeImplC
  cases hc : checkDate y m d with
  | error e => simp [hc, bind, Except.bind, Functor.map, Except.map]
  | ok r =>
    obtain rfl := (checkDate_inv y m d r hc).2
    simp [hc, checkTime, checkFold, checkTzinfoSubclassC, bind, Except.bind, pure, Except.pure, Functor.map,
      Except.map]

theorem dateSubclassCtor_proven : DateSubclassCtor := by
  intro y m d h1 h2 h3
  have epy : dateNewPy (.int y) (.int m) (.int d) = checkDate y m d := by
    simp [dateNewPy, checkDateFieldsArgPy, stateOf, pyIndex, bind, Except.bind]
  refine ⟨fun cls => ?_, fun hv => ?_, fun hv => ?_⟩
  · cases cls with
    | date => simp only [newDateSubclassExC, dateClsCallPy]; rw [newDateExC_eq, epy]
    | datetime =>
      simp only [newDateSubclassExC, dateClsCallPy]
      rw [datetimeNewPy_impl y m d 0 0 0 0 0 .none_ h1 h2 h3 (by decide) (by decide) (by decide) (by decide)
        (by decide) (Or.inl rfl)]
      rfl
    | sub call => rfl
  · obtain ⟨e, he, hc⟩ := checkDate_err_value y m d hv
    simp only [newDateSubclassExC]
    rw [newDateExC_eq, newDatetimeExC_date, he]
    exact ⟨⟨e, rfl, hc⟩, ⟨e, rfl, hc⟩⟩
  · simp only [newDateSubclassExC]
    rw [newDateExC_eq, newDatetimeExC_date, checkDate_ok y m d hv]
    exact ⟨rfl, rfl⟩

/-- `new_datetime_ex` (the C API's `DateTime_FromDateAndTime`) is Python's
`datetime(y, m, d, hh, mm, ss, us, tzinfo)` with the default `fold=0`, and `new_time_ex`
(`Time_FromTime`) is `time(hh, mm, ss, us, tzinfo)`, for all C-int fields and a `tzinfo` that
is `None` or a `tzinfo`: the same checks in the same order with the same messages, and fold 0
in the result. -/
def NewDatetimeExTwins : Prop :=
  (∀ (y m d h mi s us : Int) (tz : Arg), fitsCInt y → fitsCInt m → fitsCInt d → fitsCInt h →
    fitsCInt mi → fitsCInt s → fitsCInt us → (tz = .none_ ∨ ∃ t, tz = .tz t) →
    newDatetimeExC y m d h mi s us tz =
      datetimeNewPy (.int y) (.int m) (.int d) (.int h) (.int mi) (.int s) (.int us) tz (.int 0) ∧
    ∀ v, newDatetimeExC y m d h mi s us tz = .ok v → v.fold = 0) ∧
  (∀ (h mi s us : Int) (tz : Arg), fitsCInt h → fitsCInt mi → fitsCInt s → fitsCInt us →
    (tz = .none_ ∨ ∃ t, tz = .tz t) →
    newTimeExC h mi s us tz = timeNewPy (.int h) (.int mi) (.int s) (.int us) tz (.int 0) ∧
    ∀ v, newTimeExC h mi s us tz = .ok v → v.fold = 0)

theorem newDatetimeExTwins_proven : NewDatetimeExTwins := by
  refine ⟨fun y m d h mi s us tz h1 h2 h3 h4 h5 h6 h7 htz => ⟨?_, fun v hv => ?_⟩,
    fun h mi s us tz h4 h5 h6 h7 htz => ⟨?_, fun v hv => ?_⟩⟩
  · rw [datetimeNewPy_impl y m d h mi s us 0 tz h1 h2 h3 h4 h5 h6 h7 (by decide) htz]; rfl
  · unfold newDatetimeExC datetimeDatetimeImplC at hv
    simp only [bind, Except.bind] at hv
    split at hv <;> try cases hv
    split at hv <;> try cases hv
    split at hv <;> try cases hv
    split at hv <;> cases hv
    rfl
  · rw [timeNewPy_impl h mi s us 0 tz h4 h5 h6 h7 (by decide) htz]; rfl
  · unfold newTimeExC datetimeTimeImplC at hv
    simp only [bind, Except.bind] at hv
    split at hv <;> try cases hv
    split at hv <;> try cases hv
    split at hv <;> cases hv
    rfl

/-- `new_datetime_subclass_fold_ex` and `new_time_subclass_fold_ex` (through
`call_subclass_fold`) against `type(self)(..., fold=fold)` of `replace`: for the base classes
both run the constructor's checks (the same outcome, message included); a subclass is called
with the fields as positional arguments in the source order, the `tzinfo` last, and `fold`
as a keyword, which C passes only when it is nonzero. So the twins agree for every class whose
constructor treats an omitted `fold` like `fold=0` (every subclass that keeps the base
signature, whose `fold` defaults to 0), for all C-int fields and folds and a `tzinfo` that is
`None` or a `tzinfo`; `DtReplaceSubclassAnyTwins` drops that assumption and is refuted. -/
def SubclassFoldTwins : Prop :=
  (∀ {α : Type} (call : SubCall α) (fold : Int) (args : List Arg),
    callSubclassFoldC call fold args = if fold = 0 then call args none else call args (some fold)) ∧
  (∀ (y m d h mi s us f : Int) (tz : Arg) (cls : ClsC DT), fitsCInt y → fitsCInt m → fitsCInt d →
    fitsCInt h → fitsCInt mi → fitsCInt s → fitsCInt us → fitsCInt f → (tz = .none_ ∨ ∃ t, tz = .tz t) →
    (∀ call, cls = .sub call → ∀ args, call args none = call args (some 0)) →
    newDatetimeSubclassFoldExC y m d h mi s us tz f cls = dtClsCallFoldPy y m d h mi s us tz f cls) ∧
  (∀ (h mi s us f : Int) (tz : Arg) (cls : ClsC TM), fitsCInt h → fitsCInt mi → fitsCInt s →
    fitsCInt us → fitsCInt f → (tz = .none_ ∨ ∃ t, tz = .tz t) →
    (∀ call, cls = .sub call → ∀ args, call args none = call args (some 0)) →
    newTimeSubclassFoldExC h mi s us tz f cls = tmClsCallFoldPy h mi s us tz f cls)

theorem callSubclassFoldC_eq {α : Type} (call : SubCall α) (fold : Int) (args : List Arg) :
    callSubclassFoldC call fold args = if fold = 0 then call args none else call args (some fold) := by
  unfold callSubclassFoldC
  by_cases h : fold = 0 <;> simp [h]

theorem subclassFoldTwins_proven : SubclassFoldTwins := by
  refine ⟨callSubclassFoldC_eq, fun y m d h mi s us f tz cls h1 h2 h3 h4 h5 h6 h7 h8 htz hcls => ?_,
    fun h mi s us f tz cls h4 h5 h6 h7 h8 htz hcls => ?_⟩
  · cases cls with
    | base =>
      simp only [newDatetimeSubclassFoldExC, dtClsCallFoldPy]
      rw [datetimeNewPy_impl y m d h mi s us f tz h1 h2 h3 h4 h5 h6 h7 h8 htz]
    | sub call =>
      simp only [newDatetimeSubclassFoldExC, dtClsCallFoldPy]
      rw [callSubclassFoldC_eq]
      by_cases h0 : f = 0
      · subst h0; rw [if_pos rfl]; exact hcls call rfl _
      · rw [if_neg h0]
  · cases cls with
    | base =>
      simp only [newTimeSubclassFoldExC, tmClsCallFoldPy]
      rw [timeNewPy_impl h mi s us f tz h4 h5 h6 h7 h8 htz]
    | sub call =>
      simp only [newTimeSubclassFoldExC, tmClsCallFoldPy]
      rw [callSubclassFoldC_eq]
      by_cases h0 : f = 0
      · subst h0; rw [if_pos rfl]; exact hcls call rfl _
      · rw [if_neg h0]

/-- `datetime.replace` on a subclass agrees between the twins for every subclass constructor. -/
def DtReplaceSubclassAnyTwins : Prop :=
  ∀ (y m d h mi s us f : Int) (tz : Arg) (call : SubCall DT), fitsCInt y → fitsCInt m → fitsCInt d →
    fitsCInt h → fitsCInt mi → fitsCInt s → fitsCInt us → fitsCInt f → (tz = .none_ ∨ ∃ t, tz = .tz t) →
    SameOutcome (dtClsCallFoldPy y m d h mi s us tz f (.sub call))
      (newDatetimeSubclassFoldExC y m d h mi s us tz f (.sub call))

/-- `class D(datetime): def __new__(cls, *a): return super().__new__(cls, *a)` (a subclass
whose constructor takes no `fold` keyword); `D(2000, 1, 1).replace(day=2)`: Python calls
`D(2000, 1, 2, 0, 0, 0, 0, None, fold=0)` and gets `TypeError: D.__new__() got an unexpected
keyword argument 'fold'`; C's `call_subclass_fold` leaves out a zero `fold` and returns
`D(2000, 1, 2, 0, 0)` (CPython 3.15.2). -/
theorem dtReplaceSubclassAnyTwins_refuted : ¬ DtReplaceSubclassAnyTwins := by
  intro h
  let call : SubCall DT := fun args kw =>
    match kw with
    | none => .ok ⟨2000, 1, 2, 0, 0, 0, 0, 0, none⟩
    | some _ => .error (.typeError "~D.__new__() got an unexpected keyword argument 'fold'")
  have := h 2000 1 2 0 0 0 0 0 .none_ call (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Or.inl rfl)
  simp [dtClsCallFoldPy, newDatetimeSubclassFoldExC, callSubclassFoldC, call, SameOutcome] at this

end PyLean.Datetime
