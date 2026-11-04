import PyLean.Datetime.SubObj

/-!
Properties of the object-level models of `add_datetime_timedelta`, `utctimetuple`,
`astimezone` and `pep495_eq_exception` (SubObj.lean), CPython 3.15.2.
-/

namespace PyLean.Datetime
open PyLean

/-! ### Lemmas -/

theorem normalizeTailC_ok {hh mi s us : Int} {q : Py (Int × Int × Int)} {r : DT}
    (h : normalizeTailC hh mi s us q = .ok r) : r.fold = 0 ∧ r.tz = none := by
  unfold normalizeTailC at h
  split at h
  · injection h with h; subst h; exact ⟨rfl, rfl⟩
  · cases h

theorem normalizeDatetimeC_ok {y m d h mi s us : Int} {r : DT} (h : normalizeDatetimeC y m d h mi s us = .ok r) :
    r.fold = 0 ∧ r.tz = none := by
  unfold normalizeDatetimeC at h
  exact normalizeTailC_ok h

theorem implC_eq_newDT (r : DT) (tz : Option Tz) (hf : r.fold = 0) :
    datetimeDatetimeImplC r.y r.m r.d r.h r.mi r.s r.us (tzArgOf tz) 0 = newDT { r with tz := tz } := by
  obtain ⟨y, m, d, hh, mi, s, us, fold, t⟩ := r
  simp only at hf
  subst hf
  unfold datetimeDatetimeImplC newDT
  cases checkDate y m d <;> cases checkTime hh mi s us <;> cases tz <;>
    simp [bind, Except.bind, checkFold, checkTzinfoSubclassC, tzArgOf, pure, Except.pure]

theorem newDT_ok' {v r : DT} (h : newDT v = .ok r) : r = v ∧ (∃ a, checkDate v.y v.m v.d = .ok a) ∧
    (∃ b, checkTime v.h v.mi v.s v.us = .ok b) ∧ checkFold v.fold = .ok () := by
  unfold newDT at h
  cases h1 : checkDate v.y v.m v.d <;> cases h2 : checkTime v.h v.mi v.s v.us <;>
    cases h3 : checkFold v.fold <;> simp_all [bind, Except.bind, pure, Except.pure]

theorem addDatetimeTimedeltaC_newDT {dt : DT} {delta : Delta} {f : Int} {r : DT}
    (h : addDatetimeTimedeltaC dt delta f = .ok r) : ∃ v, newDT v = .ok r := by
  unfold addDatetimeTimedeltaC at h
  revert h
  generalize normalizeDatetimeC dt.y dt.m (dt.d + delta.days * f) dt.h dt.mi (dt.s + delta.seconds * f)
    (dt.us + delta.us * f) = q
  intro h
  cases q with
  | error e => cases h
  | ok q => exact ⟨_, h⟩

/-- `add_datetime_timedelta` for the base class is the `DT` model `addDatetimeTimedeltaC`. -/
theorem addDtDeltaObjC_base (dt : DT) (delta : Delta) (f : Int) :
    addDtDeltaObjC .base dt delta f = (DtAny.dt 0 ·) <$> addDatetimeTimedeltaC dt delta f := by
  unfold addDtDeltaObjC addDatetimeTimedeltaC
  cases h : normalizeDatetimeC dt.y dt.m (dt.d + delta.days * f) dt.h dt.mi (dt.s + delta.seconds * f)
      (dt.us + delta.us * f) with
  | error e => rfl
  | ok r =>
    simp only [bind, Except.bind, newDtSubFoldObjC]
    rw [implC_eq_newDT r dt.tz (normalizeDatetimeC_ok h).1]

/-! ### `add_datetime_timedelta` -/

/-- `datetime + timedelta` and `datetime - timedelta` in C (`add_datetime_timedelta`, with
`factor` 1 or -1), for every receiver type: the normalized fields are computed first, and an
error there (`OverflowError` out of range) comes before any constructor call; for `datetime`
itself the result is the base `DT` model (`addDatetimeTimedeltaC`, which
`DatetimeAddTimedelta`/`DatetimeSubTimedelta` pin against Python) as a `datetime` object; for
a subclass the class is called once with the eight normalized fields and the receiver's
tzinfo as positional arguments and no `fold` keyword, and whatever it returns (any object, or
its exception) is the result. -/
def AddDatetimeTimedeltaObj : Prop :=
  (∀ (dt : DT) (delta : Delta) (f : Int),
    addDtDeltaObjC .base dt delta f = (DtAny.dt 0 ·) <$> addDatetimeTimedeltaC dt delta f) ∧
  (∀ (id : Nat) (call : SubCall DtAny) (dt : DT) (delta : Delta) (f : Int) (r : DT),
    normalizeDatetimeC dt.y dt.m (dt.d + delta.days * f) dt.h dt.mi (dt.s + delta.seconds * f)
      (dt.us + delta.us * f) = .ok r →
    addDtDeltaObjC (.sub id call) dt delta f =
      call [.int r.y, .int r.m, .int r.d, .int r.h, .int r.mi, .int r.s, .int r.us, tzArgOf dt.tz] none) ∧
  (∀ (cls : DtType) (dt : DT) (delta : Delta) (f : Int) (e : PyExc),
    normalizeDatetimeC dt.y dt.m (dt.d + delta.days * f) dt.h dt.mi (dt.s + delta.seconds * f)
      (dt.us + delta.us * f) = .error e →
    addDtDeltaObjC cls dt delta f = .error e)

theorem addDatetimeTimedeltaObj_proven : AddDatetimeTimedeltaObj := by
  refine ⟨addDtDeltaObjC_base, fun id call dt delta f r h => ?_, fun cls dt delta f e h => ?_⟩
  · simp only [addDtDeltaObjC, h, bind, Except.bind, newDtSubFoldObjC, callSubclassFoldC]
    rfl
  · simp only [addDtDeltaObjC, h, bind, Except.bind]

/-! ### `utctimetuple` -/

theorem dtUtctimetupleObjC_base (env : TzEnv) (self : DT) :
    dtUtctimetupleObjC env .base self = some (dtUtctimetupleC env self) := by
  unfold dtUtctimetupleObjC dtUtctimetupleC
  cases htz : self.tz with
  | none =>
    have : self.utcoffsetC env = .ok none := by simp [DT.utcoffsetC, htz]
    simp [this, bind, Except.bind, pure, Except.pure, DtType.tyId]
  | some z =>
    simp only
    cases ho : self.utcoffsetC env with
    | error e => simp [bind, Except.bind]
    | ok o =>
      cases o with
      | none => simp [bind, Except.bind, pure, Except.pure, DtType.tyId]
      | some o =>
        simp only [bind, Except.bind]
        rw [addDtDeltaObjC_base]
        cases addDatetimeTimedeltaC self o (-1) <;> rfl

/-- `datetime.utctimetuple()` in C for every receiver type: for `datetime` itself it is the
base model `dtUtctimetupleC` (pinned against Python by `DatetimeUtctimetuple`); for a subclass
with an aware receiver whose `utcoffset()` is any timedelta `o`, zero included (Python's
`if offset:` skips zero), the class is called on the normalized `self - o` fields and the
receiver's tzinfo, and when it returns a datetime object the struct_time is that object's
fields with `tm_isdst` 0; a naive receiver or a `None` offset never calls the class. -/
def UtctimetupleObj : Prop :=
  (∀ (env : TzEnv) (self : DT), dtUtctimetupleObjC env .base self = some (dtUtctimetupleC env self)) ∧
  (∀ (env : TzEnv) (id : Nat) (call : SubCall DtAny) (self : DT) (o : Delta) (r : DT) (ty : Nat) (v : DT),
    self.tz.isSome → self.utcoffsetC env = .ok (some o) →
    normalizeDatetimeC self.y self.m (self.d + o.days * -1) self.h self.mi (self.s + o.seconds * -1)
      (self.us + o.us * -1) = .ok r →
    call [.int r.y, .int r.m, .int r.d, .int r.h, .int r.mi, .int r.s, .int r.us, tzArgOf self.tz] none =
      .ok (.dt ty v) →
    dtUtctimetupleObjC env (.sub id call) self = some (.ok (buildStructTimeC v.y v.m v.d v.h v.mi v.s 0))) ∧
  (∀ (env : TzEnv) (id : Nat) (call : SubCall DtAny) (self : DT),
    self.tz = none ∨ self.utcoffsetC env = .ok none →
    dtUtctimetupleObjC env (.sub id call) self =
      some (.ok (buildStructTimeC self.y self.m self.d self.h self.mi self.s 0)))

theorem utctimetupleObj_proven : UtctimetupleObj := by
  refine ⟨dtUtctimetupleObjC_base, ?_, ?_⟩
  · intro env id call self o r ty v hs ho hn hc
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hs
    have hsub := (addDatetimeTimedeltaObj_proven.2.1 id call self o (-1) r hn).trans hc
    simp only [dtUtctimetupleObjC, hz, ho, bind, Except.bind, hsub]
  · intro env id call self h
    rcases h with h | h
    · simp [dtUtctimetupleObjC, h]
    · cases hz : self.tz with
      | none => simp [dtUtctimetupleObjC, hz]
      | some z => simp [dtUtctimetupleObjC, hz, h, bind, Except.bind, pure, Except.pure]

/-- No receiver makes C `utctimetuple` read memory it does not own: for every receiver type
the result of the subtraction it reads is a datetime. -/
def UtctimetupleObjDefined : Prop :=
  ∀ (env : TzEnv) (cls : DtType) (self : DT), (dtUtctimetupleObjC env cls self).isSome = true

/-- `class D(datetime)` whose `__new__` returns `bytearray(200)` when given eight positional
arguments: `D(2000, 1, 1, 12, tzinfo=timezone(timedelta(hours=1))).utctimetuple()` reads the
datetime fields of the bytearray (on 3.15.2 a `struct_time` of garbage, tm_year 0, tm_wday -2;
`object()` gives tm_year 65535). -/
theorem utctimetupleObjDefined_refuted : ¬ UtctimetupleObjDefined := by
  intro h
  have := h ⟨fun _ _ => .ok .none, fun _ _ => .ok .none, fun _ _ => .ok .none, fun _ => ""⟩
    (.sub 0 (fun _ _ => .ok (.other "bytearray")))
    ⟨2000, 1, 1, 12, 0, 0, 0, 0, some ⟨1, .timezone ⟨0, 3600, 0⟩ none⟩⟩
  revert this
  decide

/-! ### `astimezone` -/

theorem implC_utc {r : DT} (h1 : ∃ a, checkDate r.y r.m r.d = .ok a) (h2 : ∃ b, checkTime r.h r.mi r.s r.us = .ok b)
    (h3 : checkFold r.fold = .ok ()) :
    datetimeDatetimeImplC r.y r.m r.d r.h r.mi r.s r.us (.tz tzUTC) r.fold = .ok { r with tz := some tzUTC } := by
  obtain ⟨a, h1⟩ := h1
  obtain ⟨b, h2⟩ := h2
  simp [datetimeDatetimeImplC, h1, h2, h3, bind, Except.bind, checkTzinfoSubclassC, pure, Except.pure]

theorem tzinfoUTC_ok_of_newDT {v r : DT} (h : newDT v = .ok r) :
    datetimeDatetimeImplC r.y r.m r.d r.h r.mi r.s r.us (.tz tzUTC) r.fold = .ok { r with tz := some tzUTC } := by
  obtain ⟨hrv, h1, h2, h3⟩ := newDT_ok' h
  subst hrv
  exact implC_utc h1 h2 h3

/-- The UTC step of `astimezone` (:6963-6984) on a valid result: either branch gives the result
with tzinfo `utc`. -/
theorem astzUtcStep {v r : DT} (h : newDT v = .ok r) : astzUtcC r = .ok { r with tz := some tzUTC } := by
  unfold astzUtcC
  split
  · exact tzinfoUTC_ok_of_newDT h
  · rfl

theorem astzObjFinishC_base (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 : Nat) (self : DT)
    (tzinfo : Option Tz) (o : Delta) :
    astzObjFinishC env ltz o1 (builtinFromutcObj env) .base self tzinfo o =
      some ((DtAny.dt 0 ·) <$> astzCFinish env ltz o1 self tzinfo o) := by
  unfold astzObjFinishC astzCFinish
  rw [addDtDeltaObjC_base]
  cases hr : addDatetimeTimedeltaC self o (-1) with
  | error e => rfl
  | ok r =>
    obtain ⟨v, hv⟩ := addDatetimeTimedeltaC_newDT hr
    dsimp only [Functor.map, Except.map]
    rw [astzUtcStep hv]
    cases tzinfo with
    | some t => simp only [astzTargetC, bind, Except.bind, pure, Except.pure, builtinFromutcObj, Functor.map, Except.map]
    | none =>
      simp only [astzTargetC, bind, Except.bind]
      cases localTimezoneC env ltz o1 { r with tz := some tzUTC } with
      | error e => rfl
      | ok t => simp only [builtinFromutcObj, Functor.map, Except.map]

/-- The old model's utcoffset step, in the form the object model uses. -/
theorem astzCAfterLocal_eq (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 : Nat) (self : DT)
    (tzinfo : Option Tz) (z : Tz) :
    astzCAfterLocal env ltz o1 self tzinfo z =
      (if tzinfo.map (·.oid) = some z.oid then .ok self
      else match tzUtcoffsetRaw env z (some self) >>= callTzinfoCheckC "utcoffset" with
        | .error e => .error e
        | .ok (some o) => astzCFinish env ltz o1 self tzinfo o
        | .ok none => .error .modelFuel) := by
  unfold astzCAfterLocal
  split
  · rfl
  · cases tzUtcoffsetRaw env z (some self) with
    | error e => rfl
    | ok w =>
      simp only [bind, Except.bind]
      cases callTzinfoCheckC "utcoffset" w with
      | error e => rfl
      | ok oo => cases oo <;> rfl

theorem astzObjAfterLocalC_base (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 : Nat) (self : DT)
    (tzinfo : Option Tz) (z : Tz) :
    astzObjAfterLocalC env ltz o1 (builtinFromutcObj env) .base self tzinfo z =
      some ((DtAny.dt 0 ·) <$> astzCAfterLocal env ltz o1 self tzinfo z) := by
  rw [astzCAfterLocal_eq]
  unfold astzObjAfterLocalC
  split
  · rfl
  · cases tzUtcoffsetRaw env z (some self) >>= callTzinfoCheckC "utcoffset" with
    | error e => rfl
    | ok oo =>
      cases oo with
      | none => rfl
      | some o => exact astzObjFinishC_base env ltz o1 self tzinfo o

theorem dtAstimezoneFullC_eq (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 o2 : Nat) (self : DT) (tzinfo : Option Tz)
    (z : Tz) (hz : self.tz = some z) (arg : AstzArg) (harg : arg ≠ .other)
    (htz : tzinfo = (match arg with | .tz t => some t | _ => none)) :
    dtAstimezoneFullC env ltz o1 o2 self arg =
      (if tzinfo.map (·.oid) = some z.oid then .ok self
      else match tzUtcoffsetRaw env z (some self) >>= callTzinfoCheckC "utcoffset" with
        | .error e => .error e
        | .ok (some o) => astzCFinish env ltz o1 self tzinfo o
        | .ok none => do astzCAfterLocal env ltz o1 self tzinfo (← localTimezoneFromLocalC ltz o2 self)) := by
  subst htz
  unfold dtAstimezoneFullC
  cases arg with
  | other => exact absurd rfl harg
  | none_ | tz t =>
    simp only [bind, Except.bind, pure, Except.pure, hz]
    split
    · rfl
    · cases tzUtcoffsetRaw env z (some self) with
      | error e => rfl
      | ok w =>
        simp only
        cases callTzinfoCheckC "utcoffset" w with
        | error e => rfl
        | ok oo => cases oo <;> rfl

/-- `astimezone` for the base class is the `DT` model `dtAstimezoneFullC` (pinned against
Python by the astimezone entries), when the target's `fromutc` is the built-in one. -/
theorem dtAstimezoneObjC_base (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 o2 : Nat) (self : DT) (arg : AstzArg) :
    dtAstimezoneObjC env ltz o1 o2 (builtinFromutcObj env) .base self arg =
      some ((DtAny.dt 0 ·) <$> dtAstimezoneFullC env ltz o1 o2 self arg) := by
  cases harg : arg with
  | other => rfl
  | none_ | tz t =>
    cases hs : self.tz with
    | none =>
      unfold dtAstimezoneObjC dtAstimezoneFullC
      simp only [hs, bind, Except.bind, pure, Except.pure]
      cases localTimezoneFromLocalC ltz o2 self with
      | error e => rfl
      | ok z => exact astzObjAfterLocalC_base env ltz o1 self _ z
    | some z =>
      rw [dtAstimezoneFullC_eq env ltz o1 o2 self _ z hs _ (by simp) rfl]
      unfold dtAstimezoneObjC
      simp only [hs]
      split
      · rfl
      · cases tzUtcoffsetRaw env z (some self) >>= callTzinfoCheckC "utcoffset" with
        | error e => rfl
        | ok oo =>
          cases oo with
          | some o => exact astzObjFinishC_base env ltz o1 self _ o
          | none =>
            simp only [bind, Except.bind]
            cases localTimezoneFromLocalC ltz o2 self with
            | error e => rfl
            | ok z' => exact astzObjAfterLocalC_base env ltz o1 self _ z'

/-- `datetime.astimezone(tz)` in C for every receiver type: for `datetime` with the built-in
`fromutc` it is the base model `dtAstimezoneFullC`; for a subclass with an aware receiver,
a target `tzinfo` `t` that is not the receiver's own and a timedelta offset `o`, the class
is called once with the normalized `self - o` fields and the receiver's tzinfo and no `fold`
keyword; when that returns a datetime object (aware, or naive and then rebuilt aware in its
own type without another constructor call), that object with `tzinfo` `t` is passed to
`t.fromutc`, whose result is returned. -/
def AstimezoneObj : Prop :=
  (∀ (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 o2 : Nat) (self : DT) (arg : AstzArg),
    dtAstimezoneObjC env ltz o1 o2 (builtinFromutcObj env) .base self arg =
      some ((DtAny.dt 0 ·) <$> dtAstimezoneFullC env ltz o1 o2 self arg)) ∧
  (∀ (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 o2 : Nat) (fromutc : Tz → DtAny → Py DtAny)
      (id : Nat) (call : SubCall DtAny) (self : DT) (z t : Tz) (o : Delta) (r : DT) (ty : Nat) (v : DT),
    self.tz = some z → t.oid ≠ z.oid →
    (tzUtcoffsetRaw env z (some self) >>= callTzinfoCheckC "utcoffset") = .ok (some o) →
    normalizeDatetimeC self.y self.m (self.d + o.days * -1) self.h self.mi (self.s + o.seconds * -1)
      (self.us + o.us * -1) = .ok r →
    call [.int r.y, .int r.m, .int r.d, .int r.h, .int r.mi, .int r.s, .int r.us, .tz z] none = .ok (.dt ty v) →
    (∃ a, checkDate v.y v.m v.d = .ok a) → (∃ b, checkTime v.h v.mi v.s v.us = .ok b) → checkFold v.fold = .ok () →
    dtAstimezoneObjC env ltz o1 o2 fromutc (.sub id call) self (.tz t) =
      some (fromutc t (.dt ty { v with tz := some t })))

theorem astimezoneObj_proven : AstimezoneObj := by
  refine ⟨dtAstimezoneObjC_base, ?_⟩
  intro env ltz o1 o2 fromutc id call self z t o r ty v hz ht ho hn hc h1 h2 h3
  have hsub : addDtDeltaObjC (.sub id call) self o (-1) = .ok (.dt ty v) := by
    rw [addDatetimeTimedeltaObj_proven.2.1 id call self o (-1) r hn, hz]; exact hc
  have hne : ¬ (Option.map (·.oid) (some t) = some z.oid) := by simpa using ht
  have hstep : astzUtcC v = .ok { v with tz := some tzUTC } := by
    unfold astzUtcC
    split
    · exact implC_utc h1 h2 h3
    · rfl
  unfold dtAstimezoneObjC
  dsimp only
  rw [hz]
  dsimp only
  rw [if_neg hne, ho]
  dsimp only
  unfold astzObjFinishC
  rw [hsub]
  dsimp only
  rw [hstep]
  rfl

/-- No receiver makes C `astimezone` read or write memory it does not own: for every receiver
type, `fromutc` and argument, the result of the subtraction whose `tzinfo` it reads and writes
is a datetime. -/
def AstimezoneObjDefined : Prop :=
  ∀ (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 o2 : Nat) (fromutc : Tz → DtAny → Py DtAny)
    (cls : DtType) (self : DT) (arg : AstzArg),
    (dtAstimezoneObjC env ltz o1 o2 fromutc cls self arg).isSome = true

/-- `D(2000, 1, 1, 12, tzinfo=timezone(timedelta(hours=1))).astimezone(timezone.utc)` with
`D.__new__` returning a non-datetime for eight positional arguments: C reads `HASTZINFO` of
that object and writes its "tzinfo" slot (segfault on 3.15.2 for `object()` and `1`). -/
theorem astimezoneObjDefined_refuted : ¬ AstimezoneObjDefined := by
  intro h
  have := h ⟨fun _ _ => .ok .none, fun _ _ => .ok .none, fun _ _ => .ok .none, fun _ => ""⟩
    (fun _ => .error .modelFuel) 5 6 (fun _ x => .ok x)
    (.sub 0 (fun _ _ => .ok (.other "object")))
    ⟨2000, 1, 1, 12, 0, 0, 0, 0, some ⟨1, .timezone ⟨0, 3600, 0⟩ none⟩⟩ (.tz tzUTC)
  revert this
  decide

/-! ### `pep495_eq_exception` -/

/-- On `timedelta`s, `delta_cmp` is zero exactly for equal values. -/
theorem cmpC_eq_zero (a b : Delta) : a.cmpC b = 0 ↔ a = b := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  unfold Delta.cmpC
  simp only [Delta.mk.injEq]
  constructor
  · intro h
    split at h
    · split at h <;> omega
    · omega
  · rintro ⟨rfl, rfl, rfl⟩; simp

/-- One object has one value: two `OffObj`s with the same identity hold the same timedelta. -/
def OffObj.Coherent (f o : OffObj) : Prop := ∀ i a b, f = .td i a → o = .td i b → a = b

/-- When the two offsets of each side are both `None` or both `timedelta`s, the pointer test and
`delta_cmp` give the value test of Python's `_cmp`: C's `pep495_eq_exception` is
`pep495EqExceptionPy` on the values (the same `True`/`False`, the same exception of either
flip-offset call, the second flip offset consulted only when the first test does not fire),
and the pointer test only skips comparing an object with itself. -/
def Pep495ObjSameKind : Prop :=
  ∀ (f1 f2 : Py OffObj) (o1 o2 : OffObj),
    (∀ f, f1 = .ok f → (f = .none_ ↔ o1 = .none_) ∧ f.Coherent o1) →
    (∀ f, f2 = .ok f → (f = .none_ ↔ o2 = .none_) ∧ f.Coherent o2) →
    pep495EqExceptionObjC f1 f2 o1 o2 = some (pep495EqExceptionPy (OffObj.val <$> f1) (OffObj.val <$> f2) o1.val o2.val)

theorem pep495StepC_val (f o : OffObj) (h : f = .none_ ↔ o = .none_) (hc : f.Coherent o) :
    pep495StepC f o = some (!offEq o.val f.val) := by
  unfold pep495StepC
  cases f with
  | none_ =>
    cases o with
    | none_ => rfl
    | td j b => simp at h
  | td i a =>
    cases o with
    | none_ => simp at h
    | td j b =>
      simp only [OffObj.ptrNe, deltaCmpObjC, OffObj.val, offEq]
      by_cases hij : i = j
      · subst hij
        obtain rfl := hc i a b rfl rfl
        simp
      · have hb : (i != j) = true := by simp [hij]
        have hcmp := cmpC_eq_zero a b
        simp only [hb, ↓reduceIte, Option.map_some, Option.some.injEq]
        by_cases hab : a = b
        · subst hab; have := hcmp.mpr rfl; simp [this]
        · have hba : ¬ b = a := fun e => hab e.symm
          simp [hab, hba, hcmp]

theorem pep495ObjSameKind_proven : Pep495ObjSameKind := by
  intro f1 f2 o1 o2 h1 h2
  unfold pep495EqExceptionObjC pep495EqExceptionPy
  cases f1 with
  | error e => rfl
  | ok f =>
    obtain ⟨k1, c1⟩ := h1 f rfl
    dsimp only
    rw [pep495StepC_val f o1 k1 c1]
    dsimp only [Functor.map, Except.map, bind, Except.bind, pure, Except.pure]
    cases hb : offEq o1.val f.val
    · rfl
    · cases f2 with
      | error e => rfl
      | ok g =>
        obtain ⟨k2, c2⟩ := h2 g rfl
        dsimp only
        rw [pep495StepC_val g o2 k2 c2]
        rfl

/-- `pep495_eq_exception` never reads a non-`timedelta` as one: for all flip offsets and
offsets (`None` or `timedelta`s, as `call_utcoffset` returns them), it has a defined result. -/
def Pep495ObjDefined : Prop :=
  ∀ (f1 f2 : Py OffObj) (o1 o2 : OffObj), (pep495EqExceptionObjC f1 f2 o1 o2).isSome = true

/-- A `tzinfo` whose `utcoffset` is `None` for fold 0 and `timedelta(0)` for fold 1: two equal
naive-looking datetimes with distinct such tzinfos reach `pep495_eq_exception` with
`offset_self` `None` and the flip offset `timedelta(0)`, and `delta_cmp` reads `Py_None` as a
timedelta (on 3.15.2 the bytes past `_Py_NoneStruct` are zero, so C answers `==` True where
`_pydatetime` answers False). -/
theorem pep495ObjDefined_refuted : ¬ Pep495ObjDefined := by
  intro h
  have := h (.ok (.td 7 ⟨0, 0, 0⟩)) (.ok (.td 8 ⟨0, 0, 0⟩)) .none_ .none_
  revert this
  decide

end PyLean.Datetime
