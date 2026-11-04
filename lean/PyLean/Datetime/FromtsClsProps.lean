import PyLean.Datetime.FromtimestampProps
import PyLean.Datetime.SubclassCtor
import PyLean.Binary64.Props2

/-!
`date.fromtimestamp` with its class: C `date_fromtimestamp(cls, obj)`
(Modules/_datetimemodule.c:3291-3306) and `datetime_date_fromtimestamp_impl`
(:3369-3373), against `date.fromtimestamp(cls, t)` (Lib/_pydatetime.py:1035-1041), and the floor
of a finite float in `_PyTime_ObjectToTime_t(obj, ROUND_FLOOR)` (Python/pytime.c:484-520) on
exact binary64 doubles. CPython 3.15.2.
-/

namespace PyLean.Datetime

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-- `date_fromtimestamp(cls, obj)`, :3291-3306: `_PyTime_ObjectToTime_t(obj, &t,
_PyTime_ROUND_FLOOR)` (:3296-3297), `_PyTime_localtime(t, &tm)` (:3299-3300), then
`new_date_subclass_ex(tm.tm_year + 1900, tm.tm_mon + 1, tm.tm_mday, cls)` (:3302-3305) with the
class the method was called on. The clock's `localtime` gives those three fields. -/
def dateFromtimestampClsC (k : Clock) (cls : DateClsC) (t : Arg) : Py DT := do
  let tt ← objectToTimeT k t
  let (y, m, d) ← k.localtime tt
  newDateSubclassExC y m d cls

/-- `datetime_date_fromtimestamp_impl(type, timestamp)`, :3369-3373:
`date_fromtimestamp(type, timestamp)`. -/
def datetimeDateFromtimestampImplC (k : Clock) (cls : DateClsC) (t : Arg) : Py DT :=
  dateFromtimestampClsC k cls t

/-- `date.fromtimestamp(cls, t)`, Py:1035-1041: the `None` check (:1038-1039),
`_time.localtime(t)` (:1040), then `cls(y, m, d)` (:1041). -/
def dateFromtimestampClsPy (k : Clock) (cls : DateClsC) (t : Arg) : Py DT :=
  if t = .none_ then .error (.typeError "'NoneType' object cannot be interpreted as an integer")
  else do
    let (y, m, d) ← timeLocaltime k t
    dateClsCallPy y m d cls

/-- `date.fromtimestamp` in both twins, for every class and argument, given a clock whose
`localtime` fields are C ints (the `int` members of `struct tm`, which `time.localtime` hands
on unchanged): `None` is `TypeError` in both; otherwise C and Python are the same computation,
the conversion and `localtime` followed by `cls(y, m, d)`: for `date` the checked date (the base
`dateFromtimestampC`), for `datetime` midnight of it, and a subclass is called with the three
fields positionally and nothing else; an error of the conversion or of `localtime` comes before
any call. -/
def DateFromtimestampCls : Prop :=
  ∀ (k : Clock) (cls : DateClsC) (t : Arg),
    (∀ tt y m d, k.localtime tt = .ok (y, m, d) → fitsCInt y ∧ fitsCInt m ∧ fitsCInt d) →
    (dateFromtimestampClsPy k cls .none_).raises "TypeError" ∧
    (datetimeDateFromtimestampImplC k cls .none_).raises "TypeError" ∧
    (t ≠ .none_ → datetimeDateFromtimestampImplC k cls t = dateFromtimestampClsPy k cls t) ∧
    datetimeDateFromtimestampImplC k .date t =
      (fun r => (⟨r.1, r.2.1, r.2.2, 0, 0, 0, 0, 0, none⟩ : DT)) <$> dateFromtimestampC k t ∧
    (∀ call y m d, (do let tt ← objectToTimeT k t; k.localtime tt) = .ok (y, m, d) →
      datetimeDateFromtimestampImplC k (.sub call) t = call [.int y, .int m, .int d] none) ∧
    (∀ e, (do let tt ← objectToTimeT k t; k.localtime tt) = .error e →
      datetimeDateFromtimestampImplC k cls t = .error e)

theorem dateFromtimestampCls_proven : DateFromtimestampCls := by
  intro k cls t hk
  refine ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, fun hn => ?_, ?_, fun call y m d h => ?_, fun e h => ?_⟩
  · have ht : timeLocaltime k t = (do let tt ← objectToTimeT k t; k.localtime tt) := by
      unfold timeLocaltime
      cases t <;> first | rfl | exact absurd rfl hn
    unfold datetimeDateFromtimestampImplC dateFromtimestampClsC dateFromtimestampClsPy
    rw [if_neg hn, ht]
    cases hc : objectToTimeT k t with
    | error e => rfl
    | ok tt =>
      cases hl : k.localtime tt with
      | error e => simp [bind, Except.bind, hl]
      | ok r =>
        obtain ⟨y, m, d⟩ := r
        obtain ⟨h1, h2, h3⟩ := hk tt y m d hl
        simp only [bind, Except.bind, hl]
        exact (dateSubclassCtor_proven y m d h1 h2 h3).1 cls
  · unfold datetimeDateFromtimestampImplC dateFromtimestampClsC dateFromtimestampC
    cases hc : objectToTimeT k t with
    | error e => rfl
    | ok tt =>
      cases hl : k.localtime tt with
      | error e => simp [bind, Except.bind, hl, Functor.map, Except.map]
      | ok r =>
        obtain ⟨y, m, d⟩ := r
        simp only [bind, Except.bind, hl, newDateSubclassExC, newDateExC]
        cases checkDateArgsC y m d <;> rfl
  · unfold datetimeDateFromtimestampImplC dateFromtimestampClsC
    cases hc : objectToTimeT k t with
    | error e => simp [hc, bind, Except.bind] at h
    | ok tt =>
      simp only [hc, bind, Except.bind] at h
      simp only [bind, Except.bind, h, newDateSubclassExC]
  · unfold datetimeDateFromtimestampImplC dateFromtimestampClsC
    cases hc : objectToTimeT k t with
    | error e' =>
      simp only [hc, bind, Except.bind, Except.error.injEq] at h
      subst h; rfl
    | ok tt =>
      simp only [hc, bind, Except.bind] at h
      simp only [bind, Except.bind, h]

/-! ### The floor of a finite float -/

theorem ofInt_m63 : (F64.ofInt (-2 ^ 63)).isFinite = true ∧
    (F64.ofInt (-2 ^ 63)).toRat = ((-9223372036854775808 : Int) : Rat) := by
  decide +kernel

theorem ofInt_p63 : (F64.ofInt (2 ^ 63)).isFinite = true ∧
    (F64.ofInt (2 ^ 63)).toRat = ((9223372036854775808 : Int) : Rat) := by
  decide +kernel

/-- `_PyTime_ObjectToTime_t(x, ROUND_FLOOR)` on a finite float: `floor(x)` as an exact
integer when `-2**63 <= floor(x) < 2**63`, `OverflowError` otherwise (`pytime_round` then the
range test of `_PyTime_DoubleToDenominator`'s caller, pytime.c:503-516). -/
theorem objectToTimeT_finite (k : Clock) (x : F64) (hx : x.isFinite = true) :
    objectToTimeT k (.float x) =
      if -2 ^ 63 ≤ x.toRat.floor ∧ x.toRat.floor < 2 ^ 63 then .ok x.toRat.floor else .error timeTOverflow := by
  have hn := isNaN_false_of_finite hx
  obtain ⟨hf, hv⟩ := floor_value hx
  obtain ⟨a1, b1⟩ := ofInt_m63
  obtain ⟨a2, b2⟩ := ofInt_p63
  have e1 : F64.le (F64.ofInt (-2 ^ 63)) (F64.floor x) = decide (-2 ^ 63 ≤ x.toRat.floor) := by
    unfold F64.le
    rw [lt_of_finite a1 hf, eq_of_finite a1 hf, b1, hv, ← Bool.decide_or]
    exact decide_eq_decide.mpr (Rat.le_iff_lt_or_eq.symm.trans Rat.intCast_le_intCast)
  have e2 : F64.lt (F64.floor x) (F64.ofInt (2 ^ 63)) = decide (x.toRat.floor < 2 ^ 63) := by
    rw [lt_of_finite hf a2, b2, hv]
    exact decide_eq_decide.mpr Rat.intCast_lt_intCast
  have et : (F64.floor x).truncInt = x.toRat.floor := truncInt_of_int hv
  simp only [objectToTimeT, hn, Bool.false_eq_true, ite_false]
  rw [e1, e2, et, ← Bool.decide_and]
  simp only [decide_eq_true_eq]

/-- `date.fromtimestamp(x)` for every finite float `x` and every class, in both twins: the
timestamp is `floor(x)` (toward minus infinity, so `-1.5` is `-2` and `-1e-300` is `-1`) when
it lies in `[-2**63, 2**63)`, handed to `localtime` and then to `cls(y, m, d)`; outside that
range both raise `OverflowError: timestamp out of range for platform time_t` before `localtime`. -/
def TimestampFloor : Prop :=
  ∀ (k : Clock) (cls : DateClsC) (x : F64), x.isFinite = true →
    let inRange := -2 ^ 63 ≤ x.toRat.floor ∧ x.toRat.floor < 2 ^ 63
    objectToTimeT k (.float x) = (if inRange then .ok x.toRat.floor else .error timeTOverflow) ∧
    datetimeDateFromtimestampImplC k cls (.float x) =
      (if inRange then (do let (y, m, d) ← k.localtime x.toRat.floor; newDateSubclassExC y m d cls)
       else .error timeTOverflow) ∧
    dateFromtimestampClsPy k cls (.float x) =
      (if inRange then (do let (y, m, d) ← k.localtime x.toRat.floor; dateClsCallPy y m d cls)
       else .error timeTOverflow)

theorem timestampFloor_proven : TimestampFloor := by
  intro k cls x hx
  have e := objectToTimeT_finite k x hx
  refine ⟨e, ?_, ?_⟩
  · unfold datetimeDateFromtimestampImplC dateFromtimestampClsC
    rw [e]
    split <;> rfl
  · unfold dateFromtimestampClsPy timeLocaltime
    rw [if_neg (by intro h; cases h)]
    simp only
    rw [e]
    split <;> rfl

/-- The values at the edges, as CPython 3.15.2 gives them (`time.localtime` aside):
`-1.5` floors to `-2`, `-1e-300` to `-1`, `-0.0` to `0`, `-2.0**63` is accepted and `2.0**63`
is `OverflowError`. -/
theorem timestampFloor_examples (k : Clock) :
    objectToTimeT k (.float (F64.ofBits 0xbff8000000000000)) = .ok (-2) ∧
    objectToTimeT k (.float (F64.ofBits 0x81a56e1fc2f8f359)) = .ok (-1) ∧
    objectToTimeT k (.float (F64.ofBits 0x8000000000000000)) = .ok 0 ∧
    objectToTimeT k (.float (F64.ofBits 0xc3e0000000000000)) = .ok (-9223372036854775808) ∧
    objectToTimeT k (.float (F64.ofBits 0x43e0000000000000)) = .error timeTOverflow := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [objectToTimeT_finite k _ (by decide +kernel)]
    decide +kernel

end PyLean.Datetime
