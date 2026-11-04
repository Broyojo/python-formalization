import PyLean.Datetime.Twins2
import PyLean.Datetime.TwinsProps
import PyLean.Datetime.CmpProps
import PyLean.Datetime.MiscProps

/-!
Properties of the twin differences in `Twins2`: each broad agreement is refuted on its
witness, and the narrowed agreement that remains is proven.
-/

namespace PyLean.Datetime
open PyLean

/-! ### `tzinfo.__reduce__` -/

/-- `tzinfo.__reduce__` in each twin, for every lookup outcome, attribute object and state:
an exception of the lookup propagates; a missing `__getinitargs__` gives `()` and the state;
Python then tests the object's truth (an exception there propagates), gives `()` for a false
object without calling it, and calls a true one; C calls whatever it found; an exception of
the call propagates before the state is asked for; otherwise the result and the state. -/
def TzinfoReduceBody : Prop :=
  ∀ {α σ : Type} (o : InitArgsObj α) (st : Py σ) (e : PyExc) (a : α),
    tzinfoReducePy (α := α) (.error e) st = .error e ∧ tzinfoReduceC (α := α) (.error e) st = .error e ∧
    tzinfoReducePy (α := α) (.ok none) st = (fun v => ((.empty : ReduceArgs α), v)) <$> st ∧
    tzinfoReduceC (α := α) (.ok none) st = (fun v => ((.empty : ReduceArgs α), v)) <$> st ∧
    (o.truth = .error e → tzinfoReducePy (.ok (some o)) st = .error e) ∧
    (o.truth = .ok false → tzinfoReducePy (.ok (some o)) st = (fun v => ((.empty : ReduceArgs α), v)) <$> st) ∧
    (o.truth = .ok true → o.call = .error e → tzinfoReducePy (.ok (some o)) st = .error e) ∧
    (o.truth = .ok true → o.call = .ok a → tzinfoReducePy (.ok (some o)) st = (fun v => (ReduceArgs.obj a, v)) <$> st) ∧
    (o.call = .error e → tzinfoReduceC (.ok (some o)) st = .error e) ∧
    (o.call = .ok a → tzinfoReduceC (.ok (some o)) st = (fun v => (ReduceArgs.obj a, v)) <$> st)

theorem tzinfoReduceBody_proven : TzinfoReduceBody := by
  intro α σ o st e a
  refine ⟨rfl, rfl, ?_, ?_, fun h => ?_, fun h => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h => ?_, fun h => ?_⟩ <;>
    simp [tzinfoReducePy, tzinfoReduceC, bind, Except.bind, pure, Except.pure, Functor.map, Except.map, *] <;>
    cases st <;> rfl

/-- The twins of `tzinfo.__reduce__` agree for every `__getinitargs__` attribute. -/
def TzinfoReduceTwins : Prop :=
  ∀ {α σ : Type} (attr : Py (Option (InitArgsObj α))) (st : Py σ),
    SameOutcome (tzinfoReducePy attr st) (tzinfoReduceC attr st)

/-- `__getinitargs__ = None` on a `tzinfo` subclass: Python's `if getinitargs:` is false, so
`__reduce__()` is `(cls, (), state)`; C calls `None` and raises `TypeError`. -/
theorem tzinfoReduceTwins_refuted : ¬TzinfoReduceTwins := by
  intro h
  have := @h Unit Unit (.ok (some ⟨.ok false, .error (.typeError "'NoneType' object is not callable")⟩)) (.ok ())
  simp [tzinfoReducePy, tzinfoReduceC, SameOutcome, bind, Except.bind, pure, Except.pure, Functor.map,
    Except.map] at this

/-- The twins of `tzinfo.__reduce__` return the same thing (value or exception) whenever the
attribute is missing or true, which every function and bound method is: the documented way
to define `__getinitargs__`. -/
def TzinfoReduceTwinsTruthy : Prop :=
  ∀ {α σ : Type} (attr : Py (Option (InitArgsObj α))) (st : Py σ),
    (∀ o, attr = .ok (some o) → o.truth = .ok true) →
    tzinfoReducePy attr st = tzinfoReduceC attr st

theorem tzinfoReduceTwinsTruthy_proven : TzinfoReduceTwinsTruthy := by
  intro α σ attr st h
  rcases attr with e | (_ | o)
  · rfl
  · rfl
  · have := h o rfl
    simp [tzinfoReducePy, tzinfoReduceC, this, bind, Except.bind, pure, Except.pure]

/-! ### `datetime.isoformat(sep)` -/

/-- `datetime.isoformat(sep, timespec)` agrees between the twins for every `sep` object. -/
def IsoformatSepTwins : Prop :=
  ∀ (env : TzEnv) (dt : DT) (sep : Arg) (spec : TimeSpec), env.Valid → OptTzOk dt.tz →
    SameOutcome (dtIsoformatArgPy env dt sep spec) (dtIsoformatArgC env dt sep spec)

/-- A valid tzinfo environment whose methods return `None`. -/
def envNone : TzEnv := ⟨fun _ _ => .ok .none, fun _ _ => .ok .none, fun _ _ => .ok .none, fun _ => ""⟩

theorem envNone_valid : envNone.Valid := by
  refine ⟨fun i a d h => ?_, fun i a d h => ?_⟩ <;> simp [envNone] at h

/-- `datetime(2020, 1, 1).isoformat(sep=65)`: Python formats `'%c' % 65`, `'A'`, and returns
`'2020-01-01A00:00:00'`; C's `sep` converter accepts only a `str` and raises `TypeError`. -/
theorem isoformatSepTwins_refuted : ¬IsoformatSepTwins := by
  intro h
  have := h envNone ⟨2020, 1, 1, 0, 0, 0, 0, 0, none⟩ (.int 65) .auto envNone_valid trivial
  exact this

/-- `isoformat(sep)` on every `sep`: for a one-character `str` the twins return the same text
(whatever the tzinfo, as `DatetimeIsoformatTwins` for a `Char`); any other `str` is a
`TypeError` in both; every object that is not a `str` is a `TypeError` in C, while Python's
`'%c'` takes an int `n` in `0..0x10FFFF` as the character `chr(n)` (so `sep=65` is `sep='A'`
and `sep=True` is `'\x01'`) and refuses an int outside it with `OverflowError`. -/
def IsoformatSepArg : Prop :=
  ∀ (env : TzEnv) (dt : DT) (spec : TimeSpec), env.Valid → OptTzOk dt.tz →
    (∀ c, dtIsoformatArgPy env dt (.str [c]) spec = dtIsoformatArgC env dt (.str [c]) spec) ∧
    (∀ cs, cs.length ≠ 1 → (dtIsoformatArgPy env dt (.str cs) spec).raises "TypeError" ∧
      (dtIsoformatArgC env dt (.str cs) spec).raises "TypeError") ∧
    (∀ a, (∀ cs, a ≠ .str cs) → (dtIsoformatArgC env dt a spec).raises "TypeError") ∧
    (∀ n : Int, 0 ≤ n → n ≤ 0x10FFFF →
      dtIsoformatArgPy env dt (.int n) spec = dtIsoformatArgPy env dt (.str [n.toNat]) spec) ∧
    (∀ n : Int, (n < 0 ∨ 0x10FFFF < n) → (dtIsoformatArgPy env dt (.int n) spec).raises "OverflowError")

theorem isoformatSepArg_proven : IsoformatSepArg := by
  intro env dt spec henv htz
  have hoff := dt_utcoffset_twin env henv dt htz
  refine ⟨fun c => ?_, fun cs hl => ⟨?_, ?_⟩, fun a ha => ?_, fun n h0 h1 => ?_, fun n hn => ?_⟩
  · simp [dtIsoformatArgPy, dtIsoformatArgC, pctCharPy, sepClinicC, hoff]
  · rcases cs with _ | ⟨c, _ | ⟨c2, r⟩⟩
    · exact ⟨_, rfl, rfl⟩
    · simp at hl
    · exact ⟨_, rfl, rfl⟩
  · rcases cs with _ | ⟨c, _ | ⟨c2, r⟩⟩
    · exact ⟨_, rfl, rfl⟩
    · simp at hl
    · exact ⟨_, rfl, rfl⟩
  · cases a with
    | str cs => exact absurd rfl (ha cs)
    | _ => exact ⟨_, rfl, rfl⟩
  · simp [dtIsoformatArgPy, pctCharPy, pyIndex, h0, h1]
  · have : ¬ (0 ≤ n ∧ n ≤ 0x10FFFF) := by omega
    simp only [dtIsoformatArgPy, pctCharPy, pyIndex, this, ↓reduceIte]
    exact ⟨_, rfl, rfl⟩

/-! ### `datetime` comparison when a flipped-fold `utcoffset` raises -/

/-- `datetime` comparison agrees between the twins for every valid tzinfo environment and
valid operands, with no assumption on the flipped-fold offsets. -/
def DatetimeCompareTwinsAll : Prop :=
  ∀ (env : TzEnv) (op : CmpOp) (a b : DT), env.Valid → a.Valid → b.Valid →
    SameOutcome (dtRichPy env op a b) (dtRichC env op a b)

/-- A tzinfo whose `utcoffset` is one hour for fold 0 and raises `RuntimeError` for fold 1. -/
def envFoldRaises : TzEnv :=
  ⟨fun _ a => match a with
    | some dt => if dt.fold = 1 then .error (.named "RuntimeError" "fold1") else .ok (.delta ⟨0, 3600, 0⟩)
    | none => .ok (.delta ⟨0, 3600, 0⟩),
   fun _ _ => .ok .none, fun _ _ => .ok .none, fun _ => "TZ()"⟩

theorem envFoldRaises_valid : envFoldRaises.Valid := by
  refine ⟨fun i a d h => ?_, fun i a d h => ?_⟩
  · simp only [envFoldRaises] at h
    rcases a with _ | dt
    · simp at h; subst h; decide
    · by_cases hf : dt.fold = 1
      · simp [hf] at h
      · simp [hf] at h; subst h; decide
  · simp [envFoldRaises] at h

/-- `datetime(2020, 1, 1, tzinfo=TZ()) == datetime(2020, 1, 2, tzinfo=TZ())` with two
instances of a tzinfo whose `utcoffset` raises for fold 1: Python's `_cmp(allow_mixed=True)`
asks for the flipped-fold offset first (:2315-2318) and raises; C finds the offsets equal and
the fields different, never reaches `pep495_eq_exception` and returns `False`. -/
theorem datetimeCompareTwinsAll_refuted : ¬DatetimeCompareTwinsAll := by
  intro h
  have := h envFoldRaises .eq ⟨2020, 1, 1, 0, 0, 0, 0, 0, some ⟨1, .custom 0⟩⟩
    ⟨2020, 1, 2, 0, 0, 0, 0, 0, some ⟨2, .custom 0⟩⟩ envFoldRaises_valid
    (by refine ⟨by decide, ?_⟩; simp [OptTzOk, Tz.Ok]) (by refine ⟨by decide, ?_⟩; simp [OptTzOk, Tz.Ok])
  exact this

/-! ### `time.replace` and `datetime.replace` -/

theorem replKeep_int (old : Int) (o : Option Int) : replKeep old (o.map .int) = .int (o.getD old) := by
  cases o <;> rfl

theorem replConv_int (old : Int) (o : Option Int) (h : ∀ n, o = some n → fitsCInt n) :
    replConv old (o.map .int) = .ok (o.getD old) := by
  cases o with
  | none => rfl
  | some n => exact parseI_int n (h n rfl)

theorem checkTime_val (a b c d : Int) (x : Int × Int × Int × Int) (h : checkTime a b c d = .ok x) :
    x = (a, b, c, d) := by
  unfold checkTime at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h; rfl

theorem checkDate_val (a b c : Int) (x : Int × Int × Int) (h : checkDate a b c = .ok x) :
    x = (a, b, c) := by
  unfold checkDate at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only at h
      split at h
      · cases h
      · cases h; rfl

theorem checkTzinfo_twin (a : Arg) : checkTzinfoSubclassC a = checkTzinfoArgPy a := by
  cases a <;> rfl

/-- `time.replace` agrees between the twins for every combination of omitted, `None`, int and
other arguments, on every valid time. -/
def TimeReplaceTwins : Prop :=
  ∀ (t : TM) (h mi s us tz fold : Option Arg), t.Valid →
    SameOutcome (tmReplaceArgPy t h mi s us tz fold) (tmReplaceArgC t h mi s us tz fold)

/-- `time(1, 2, 3).replace(hour=None)`: Python keeps the hour (`if hour is None`), C's `int`
converter raises `TypeError`. -/
theorem timeReplaceTwins_refuted : ¬TimeReplaceTwins := by
  intro h
  have := h ⟨1, 2, 3, 0, 0, none⟩ (some .none_) none none none none none (by simp [TM.Valid, OptTzOk])
  exact this

/-- `datetime.replace` agrees between the twins for every combination of omitted, `None`, int
and other arguments, on every valid datetime. -/
def DatetimeReplaceTwins : Prop :=
  ∀ (dt : DT) (y m d h mi s us tz fold : Option Arg), dt.Valid →
    SameOutcome (dtReplaceArgPy dt y m d h mi s us tz fold) (dtReplaceArgC dt y m d h mi s us tz fold)

/-- `datetime(2020, 2, 3).replace(year=None)`: Python keeps the year, C raises `TypeError`. -/
theorem datetimeReplaceTwins_refuted : ¬DatetimeReplaceTwins := by
  intro h
  have := h ⟨2020, 2, 3, 0, 0, 0, 0, 0, none⟩ (some .none_) none none none none none none none none
    (by refine ⟨by decide, ?_⟩; simp [OptTzOk])
  exact this

/-- `time.replace(...)` with int arguments (each omitted or an int within C `int`) and any
`tzinfo` argument, on any time: both twins give exactly the time built from the new fields,
each omitted field taken from `self`, checked as the constructor checks it (the hour, minute,
second and microsecond ranges in that order, then fold, then the tzinfo type), with the
constructor's messages. So a `replace` that ignores an argument, or always fails, does not
satisfy it. -/
def TimeReplaceInt : Prop :=
  ∀ (t : TM) (h mi s us fold : Option Int) (tz : Option Arg),
    (∀ n, h = some n ∨ mi = some n ∨ s = some n ∨ us = some n ∨ fold = some n → fitsCInt n) →
    let r : Py TM := do
      let _ ← checkTime (h.getD t.h) (mi.getD t.mi) (s.getD t.s) (us.getD t.us)
      checkFold (fold.getD t.fold)
      let z ← checkTzinfoArgPy (tzKeep t.tz tz)
      return ⟨h.getD t.h, mi.getD t.mi, s.getD t.s, us.getD t.us, fold.getD t.fold, z⟩
    tmReplaceArgPy t (h.map .int) (mi.map .int) (s.map .int) (us.map .int) tz (fold.map .int) = r ∧
    tmReplaceArgC t (h.map .int) (mi.map .int) (s.map .int) (us.map .int) tz (fold.map .int) = r

theorem timeReplaceInt_proven : TimeReplaceInt := by
  intro t h mi s us fold tz hfit r
  refine ⟨?_, ?_⟩
  · simp only [tmReplaceArgPy, replKeep_int, timeNewPy, stateOf, checkTimeFieldsArgPy, pyIndex,
      checkFoldArgPy, Arg.foldVal, bind, Except.bind, r]
    cases hc : checkTime (h.getD t.h) (mi.getD t.mi) (s.getD t.s) (us.getD t.us) with
    | error e => rfl
    | ok x =>
      have := checkTime_val _ _ _ _ x hc; subst this
      simp only
      cases checkFold (fold.getD t.fold) <;> rfl
  · simp only [tmReplaceArgC, replConv_int t.h h (fun n hn => hfit n (Or.inl hn)),
      replConv_int t.mi mi (fun n hn => hfit n (Or.inr (Or.inl hn))),
      replConv_int t.s s (fun n hn => hfit n (Or.inr (Or.inr (Or.inl hn)))),
      replConv_int t.us us (fun n hn => hfit n (Or.inr (Or.inr (Or.inr (Or.inl hn))))),
      replConv_int t.fold fold (fun n hn => hfit n (Or.inr (Or.inr (Or.inr (Or.inr hn))))),
      datetimeTimeImplC, checkTzinfo_twin, bind, Except.bind, r]

/-- `datetime.replace(...)` with int arguments (each omitted or an int within C `int`) and any
`tzinfo` argument, on any datetime: both twins give exactly the datetime built from the new
fields, each omitted one taken from `self`, checked as the constructor checks it (date, then
time ranges, then fold, then the tzinfo type). -/
def DatetimeReplaceInt : Prop :=
  ∀ (dt : DT) (y m d h mi s us fold : Option Int) (tz : Option Arg),
    (∀ n, y = some n ∨ m = some n ∨ d = some n ∨ h = some n ∨ mi = some n ∨ s = some n ∨
      us = some n ∨ fold = some n → fitsCInt n) →
    let r : Py DT := do
      let _ ← checkDate (y.getD dt.y) (m.getD dt.m) (d.getD dt.d)
      let _ ← checkTime (h.getD dt.h) (mi.getD dt.mi) (s.getD dt.s) (us.getD dt.us)
      checkFold (fold.getD dt.fold)
      let z ← checkTzinfoArgPy (tzKeep dt.tz tz)
      return ⟨y.getD dt.y, m.getD dt.m, d.getD dt.d, h.getD dt.h, mi.getD dt.mi, s.getD dt.s,
        us.getD dt.us, fold.getD dt.fold, z⟩
    dtReplaceArgPy dt (y.map .int) (m.map .int) (d.map .int) (h.map .int) (mi.map .int) (s.map .int)
      (us.map .int) tz (fold.map .int) = r ∧
    dtReplaceArgC dt (y.map .int) (m.map .int) (d.map .int) (h.map .int) (mi.map .int) (s.map .int)
      (us.map .int) tz (fold.map .int) = r

theorem datetimeReplaceInt_proven : DatetimeReplaceInt := by
  intro dt y m d h mi s us fold tz hfit r
  refine ⟨?_, ?_⟩
  · simp only [dtReplaceArgPy, replKeep_int, datetimeNewPy, stateOf, checkDateFieldsArgPy,
      checkTimeFieldsArgPy, pyIndex, checkFoldArgPy, Arg.foldVal, bind, Except.bind, r]
    cases hd : checkDate (y.getD dt.y) (m.getD dt.m) (d.getD dt.d) with
    | error e => rfl
    | ok x =>
      have := checkDate_val _ _ _ x hd; subst this
      simp only
      cases hc : checkTime (h.getD dt.h) (mi.getD dt.mi) (s.getD dt.s) (us.getD dt.us) with
      | error e => rfl
      | ok x =>
        have := checkTime_val _ _ _ _ x hc; subst this
        simp only
        cases checkFold (fold.getD dt.fold) <;> rfl
  · have f := fun (o : Option Int) (k : Nat) (hk : ∀ n, o = some n → fitsCInt n) => hk
    simp only [dtReplaceArgC,
      replConv_int dt.y y (fun n hn => hfit n (Or.inl hn)),
      replConv_int dt.m m (fun n hn => hfit n (by simp [hn])),
      replConv_int dt.d d (fun n hn => hfit n (by simp [hn])),
      replConv_int dt.h h (fun n hn => hfit n (by simp [hn])),
      replConv_int dt.mi mi (fun n hn => hfit n (by simp [hn])),
      replConv_int dt.s s (fun n hn => hfit n (by simp [hn])),
      replConv_int dt.us us (fun n hn => hfit n (by simp [hn])),
      replConv_int dt.fold fold (fun n hn => hfit n (by simp [hn])),
      datetimeDatetimeImplC, checkTzinfo_twin, bind, Except.bind, r]

/-! ### `_mktime` and `local_to_seconds` -/

/-- Fields `localtime` can give that `datetime(y, m, d, hh, mm, ss)` accepts. -/
def LocalTmValid (r : LocalTm) : Prop :=
  ValidDate r.1 r.2.1 r.2.2.1 ∧ 0 ≤ r.2.2.2.1 ∧ r.2.2.2.1 ≤ 23 ∧ 0 ≤ r.2.2.2.2.1 ∧ r.2.2.2.2.1 ≤ 59 ∧
    0 ≤ r.2.2.2.2.2 ∧ r.2.2.2.2.2 ≤ 59

theorem toordinal_epoch : toordinal 1970 1 1 = 719163 := by decide

theorem localC_shift (lt : Int → Py LocalTm) (hv : ∀ v r, lt v = .ok r → LocalTmValid r) (u : Int) :
    localC lt (u + epochC) = (· + epochC) <$> localPy lt u := by
  unfold localC localPy timeLocaltimePy
  simp only [show u + epochC - epochC = u by omega]
  by_cases hf : fitsTimeT u
  · simp only [hf, not_true_eq_false, ↓reduceIte]
    cases h : lt u with
    | error e => rfl
    | ok r =>
      obtain ⟨y, m, d, hh, mm, ss⟩ := r
      obtain ⟨hd, h1, h2, h3, h4, h5, h6⟩ := hv u _ h
      have hy : 1 ≤ y ∧ y ≤ 9999 := by unfold ValidDate at hd; unfold MINYEAR MAXYEAR at hd; omega
      have hn : newDT ⟨y, m, d, hh, mm, ss, 0, 0, none⟩ = .ok ⟨y, m, d, hh, mm, ss, 0, 0, none⟩ :=
        newDT_ok _ ⟨hd, h1, h2, h3, h4, h5, h6, by simp, by simp, by simp, trivial⟩
      simp only [bind, Except.bind, hn, pure, Except.pure, Functor.map, Except.map, utcToSecondsC,
        MINYEAR, MAXYEAR]
      have hc : ¬ (y < 1 ∨ y > 9999) := by omega
      simp only [hc, ↓reduceIte, ymdToOrdC_eq y m d hy.1, toordinal, epochC]
      congr 1
      omega
  · simp [hf, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw, Functor.map,
      Except.map]

set_option linter.unusedSimpArgs false in
theorem mktime_shift (loc loc' : Int → Py Int) (E : Int) (h : ∀ u, loc' (u + E) = (· + E) <$> loc u)
    (t fold : Int) :
    localToSecondsC loc' (t + E) fold = (· + E) <$> mktimePy loc t fold := by
  have h' : ∀ v, loc' v = (· + E) <$> loc (v - E) := fun v => by
    have := h (v - E); simp only [Int.sub_add_cancel] at this; exact this
  unfold localToSecondsC mktimePy
  simp only [h', Int.add_sub_cancel]
  cases h1 : loc t with
  | error e => rfl
  | ok x =>
    simp only [Functor.map, Except.map, bind, Except.bind, pure, Except.pure]
    rw [show t + E - (x + E - (t + E)) - E = t - (x - t) by omega]
    cases h2 : loc (t - (x - t)) with
    | error e => rfl
    | ok y =>
      simp only [show (y + E = t + E) ↔ (y = t) by omega]
      by_cases hy : y = t
      · have hy2 := hy.symm; subst hy2
        simp only [ite_true]
        by_cases hf : fold = 0
        · simp only [hf, ne_eq, not_true_eq_false, ite_false, ite_true]
          rw [show t + E - (x + E - (t + E)) - 24 * 3600 - E = t - (x - t) + -(24 * 3600) by omega]
          cases h3 : loc (t - (x - t) + -(24 * 3600)) with
          | error e => rfl
          | ok z =>
            simp only []
            simp only [show (x + E - (t + E) = z + E - (t + E - (x + E - (t + E)) - 24 * 3600)) ↔
              (x - t = z - (t - (x - t) + -(24 * 3600))) by omega]
            by_cases hz : decide (x - t = z - (t - (x - t) + -(24 * 3600))) = true
            · simp only [hz, ite_true]; congr 1; omega
            · simp only [hz]
              rw [show t + E - (z + E - (t + E - (x + E - (t + E)) - 24 * 3600)) - E =
                t - (z - (t - (x - t) + -(24 * 3600))) by omega]
              cases h4 : loc (t - (z - (t - (x - t) + -(24 * 3600)))) with
              | error e => rfl
              | ok w =>
                simp only [show (w + E = t + E) ↔ (w = t) by omega]
                by_cases hw : w = t
                · simp only [hw, ite_true, Bool.false_eq_true, ↓reduceIte]; congr 1; omega
                · simp only [hw, ite_false, ite_true, Bool.false_eq_true, ↓reduceIte]; congr 1; omega
        · simp only [hf, ne_eq, not_false_eq_true, ite_false, ite_true, ↓reduceIte]
          rw [show t + E - (x + E - (t + E)) + 24 * 3600 - E = t - (x - t) + 24 * 3600 by omega]
          cases h3 : loc (t - (x - t) + 24 * 3600) with
          | error e => rfl
          | ok z =>
            simp only []
            simp only [show (x + E - (t + E) = z + E - (t + E - (x + E - (t + E)) + 24 * 3600)) ↔
              (x - t = z - (t - (x - t) + 24 * 3600)) by omega]
            by_cases hz : decide (x - t = z - (t - (x - t) + 24 * 3600)) = true
            · simp only [hz, ite_true]; congr 1; omega
            · simp only [hz]
              rw [show t + E - (z + E - (t + E - (x + E - (t + E)) + 24 * 3600)) - E =
                t - (z - (t - (x - t) + 24 * 3600)) by omega]
              cases h4 : loc (t - (z - (t - (x - t) + 24 * 3600))) with
              | error e => rfl
              | ok w =>
                simp only [show (w + E = t + E) ↔ (w = t) by omega]
                by_cases hw : w = t
                · simp only [hw, ite_true, Bool.false_eq_true, ↓reduceIte]; congr 1; omega
                · simp only [hw, ite_false, ite_true, Bool.false_eq_true, ↓reduceIte]; congr 1; omega
      · simp only [hy, ite_false, Bool.false_eq_true, ↓reduceIte]
        rw [show t + E - (y + E - (t + E - (x + E - (t + E)))) - E = t - (y - (t - (x - t))) by omega]
        cases h3 : loc (t - (y - (t - (x - t)))) with
        | error e => rfl
        | ok w =>
          simp only [show (w + E = t + E) ↔ (w = t) by omega]
          by_cases hw : w = t
          · simp only [hw, ite_true, Bool.false_eq_true, ↓reduceIte]; congr 1; omega
          · simp only [hw, hy, ite_false, Bool.false_eq_true, ↓reduceIte]
            congr 1
            by_cases hf : fold = 0 <;> simp only [hf, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] <;> omega


/-- `datetime.timestamp()`/`_mktime()` of a naive datetime: Python's `_mktime` (Py:2029-2061,
with `local` building a `datetime` from `localtime`'s fields) and C's
`local_to_seconds(...) - epoch` (:7032-7077, with `local` feeding the fields to
`utc_to_seconds`) give the same seconds or the same exception, for every valid datetime and
fold and every C-library `localtime` that returns fields a `datetime` accepts (an error of
`localtime`, or a timestamp outside `time_t`, propagates in both). -/
def MktimeLocalTwins : Prop :=
  ∀ (lt : Int → Py LocalTm) (self : DT), self.Valid → (∀ v r, lt v = .ok r → LocalTmValid r) →
    dtMktimePy lt self = dtLocalToSecondsC lt self

theorem utcToSeconds_epoch (self : DT) (h : self.Valid) :
    utcToSecondsC self.y self.m self.d self.h self.mi self.s =
      .ok (((toordinal self.y self.m self.d - 719163) * 86400 + self.h * 3600 + self.mi * 60 + self.s) +
        epochC) := by
  have hy : 1 ≤ self.y ∧ self.y ≤ 9999 := by
    have := h.1; unfold ValidDate MINYEAR MAXYEAR at this; omega
  have hc : ¬ (self.y < MINYEAR ∨ self.y > MAXYEAR) := by unfold MINYEAR MAXYEAR; omega
  simp only [utcToSecondsC, hc, ↓reduceIte, ymdToOrdC_eq _ _ _ hy.1, toordinal, epochC]
  congr 1
  omega

theorem mktimeLocalTwins_proven : MktimeLocalTwins := by
  intro lt self hs hv
  unfold dtMktimePy dtLocalToSecondsC
  rw [utcToSeconds_epoch self hs]
  simp only [bind, Except.bind]
  rw [mktime_shift (localPy lt) (localC lt) epochC (localC_shift lt hv)]
  cases mktimePy (localPy lt) _ self.fold with
  | error e => rfl
  | ok r => simp [Functor.map, Except.map, pure, Except.pure]

/-- The same agreement for every C-library `localtime`, including one that returns second 60
(a leap-second-aware zone such as `right/UTC`). -/
def MktimeLocalTwinsAll : Prop :=
  ∀ (lt : Int → Py LocalTm) (self : DT), self.Valid →
    SameOutcome (dtMktimePy lt self) (dtLocalToSecondsC lt self)

/-- A `localtime` that reports the leap second `1972-06-30 23:59:60` for every timestamp, and
`datetime(1972, 7, 1)`: Python's `local()` builds `datetime(1972, 6, 30, 23, 59, 60)` and
raises `ValueError`, C's `utc_to_seconds` takes the second as it is. (A real leap-second zone
reports it for one timestamp only; the bug record's reproducer uses one.) -/
theorem mktimeLocalTwinsAll_refuted : ¬MktimeLocalTwinsAll := by
  intro h
  have := h (fun _ => .ok (1972, 6, 30, 23, 59, 60)) ⟨1972, 7, 1, 0, 0, 0, 0, 0, none⟩
    (by refine ⟨by decide, ?_⟩; simp [OptTzOk])
  exact this

/-- `datetime._local_timezone()` (Py:2121-2135) and C's `local_timezone_from_local`/
`local_timezone` (:6831-6903) pick the same timestamp for the `localtime` call that makes the
`timezone`, for every valid datetime and every `localtime` with fields a `datetime` accepts:
for a naive datetime both compute the seconds for its fold and for the other fold, and in a gap
or fold (the two differ) take the other one exactly when it is the later one for fold 1 or the
earlier one for fold 0. -/
def LocalTimezoneTwins : Prop :=
  ∀ (lt : Int → Py LocalTm) (self : DT) (utcSecs : Int), self.Valid →
    (∀ v r, lt v = .ok r → LocalTmValid r) →
    localTimezoneTsPy lt self utcSecs = localTimezoneTsC lt self utcSecs

theorem localTimezoneTwins_proven : LocalTimezoneTwins := by
  intro lt self u hs hv
  have hf : self.fold = 0 ∨ self.fold = 1 := hs.2.2.2.2.2.2.2.2.2.1
  have hflip : ({ self with fold := 1 - self.fold } : DT) = { self with fold := if self.fold ≠ 0 then 0 else 1 } := by
    rcases hf with h | h <;> simp [h]
  have hs2 : ({ self with fold := 1 - self.fold } : DT).Valid := by
    obtain ⟨a, b, c, d, e, f, g, i, j, k, l⟩ := hs
    exact ⟨a, b, c, d, e, f, g, i, j, by rcases hf with h | h <;> simp [h], l⟩
  unfold localTimezoneTsPy localTimezoneTsC
  rw [← hflip, ← mktimeLocalTwins_proven lt self hs hv, ← mktimeLocalTwins_proven lt _ hs2 hv]
  cases self.tz.isNone with
  | false => rfl
  | true =>
    simp only [↓reduceIte, bind, Except.bind]
    cases dtMktimePy lt self with
    | error e => rfl
    | ok a =>
      cases dtMktimePy lt { self with fold := 1 - self.fold } with
      | error e => rfl
      | ok b =>
        have : (decide (self.fold = 1)) = decide (self.fold ≠ 0) := by rcases hf with h | h <;> simp [h]
        rw [this]
        by_cases hab : b = a
        · simp [hab, pure, Except.pure]
        · simp only [hab, ne_eq, not_false_eq_true, true_and, ↓reduceIte]
          try (split <;> rfl)

/-- The same choice for every `localtime`, a leap-second zone included. -/
def LocalTimezoneTwinsAll : Prop :=
  ∀ (lt : Int → Py LocalTm) (self : DT) (utcSecs : Int), self.Valid →
    SameOutcome (localTimezoneTsPy lt self utcSecs) (localTimezoneTsC lt self utcSecs)

/-- `datetime(1972, 7, 1).astimezone()` under a `localtime` that reports second 60: Python's
`_mktime` raises `ValueError`, C picks a timestamp. -/
theorem localTimezoneTwinsAll_refuted : ¬LocalTimezoneTwinsAll := by
  intro h
  have := h (fun _ => .ok (1972, 6, 30, 23, 59, 60)) ⟨1972, 7, 1, 0, 0, 0, 0, 0, none⟩ 0
    (by refine ⟨by decide, ?_⟩; simp [OptTzOk])
  exact this

end PyLean.Datetime
