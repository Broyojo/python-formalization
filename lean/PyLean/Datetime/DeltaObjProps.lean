import PyLean.Datetime.DeltaObj
import PyLean.Datetime.FloatProps

/-!
Properties of the C timedelta helpers and objects of `DeltaObj.lean`: the C `divmod` helper
and the normalizers, `new_delta_ex` with its class and singleton, `microseconds_to_delta_ex`
with `checked_divmod` on any object, the `*` and `/` dispatch, and `__reduce__` with the
class.
-/

namespace PyLean.Datetime

open PyLean

/-! ### `divmod`, `normalize_pair`, `normalize_d_s_us` -/

/-- The C `divmod` helper (:373-386) is Python's `divmod` for every positive divisor
(the precondition `y > 0` is its `assert`, :377): truncation then one step down for a
negative remainder is floor division. `normalize_pair(hi, lo, factor)` (:724-735), for
`factor > 0` (its `assert`, :727), keeps `hi * factor + lo` and leaves `0 <= lo < factor`,
and leaves an in-range pair alone. `normalize_d_s_us` (:744-762) keeps
`(d * 86400 + s) * 10**6 + us`, leaves `0 <= s < 86400` and `0 <= us < 10**6`, and leaves
in-range fields alone. The C `int` arithmetic is exact here: the callers keep the inputs
within a few times the field ranges (the comments at :719-721 and :740-743). -/
def CNormalizeHelpers : Prop :=
  (∀ x y : Int, 0 < y → pyDivmod x y = .ok (cDivmod x y)) ∧
  (∀ hi lo factor : Int, 0 < factor →
    (normalizePair hi lo factor).1 * factor + (normalizePair hi lo factor).2 = hi * factor + lo ∧
    0 ≤ (normalizePair hi lo factor).2 ∧ (normalizePair hi lo factor).2 < factor ∧
    (0 ≤ lo → lo < factor → normalizePair hi lo factor = (hi, lo))) ∧
  (∀ d s us : Int,
    ((normalizeDSUsC d s us).1 * 86400 + (normalizeDSUsC d s us).2.1) * 1000000 +
        (normalizeDSUsC d s us).2.2 = (d * 86400 + s) * 1000000 + us ∧
    0 ≤ (normalizeDSUsC d s us).2.1 ∧ (normalizeDSUsC d s us).2.1 < 86400 ∧
    0 ≤ (normalizeDSUsC d s us).2.2 ∧ (normalizeDSUsC d s us).2.2 < 1000000 ∧
    (0 ≤ s → s < 86400 → 0 ≤ us → us < 1000000 → normalizeDSUsC d s us = (d, s, us)))

theorem cNormalizeHelpers_proven : CNormalizeHelpers := by
  refine ⟨fun x y hy => ?_, fun hi lo factor hf => ?_, fun d s us => ?_⟩
  · rw [cDivmod_eq x y hy]
    unfold pyDivmod
    rw [if_neg (by omega), Int.fdiv_eq_ediv_of_nonneg x (by omega),
      Int.fmod_eq_emod_of_nonneg x (by omega)]
  · rw [normalizePair_pos hi lo factor hf]
    have h1 := Int.mul_ediv_add_emod lo factor
    have h2 := Int.emod_nonneg lo (by omega : factor ≠ 0)
    have h3 := Int.emod_lt_of_pos lo hf
    by_cases h : lo < 0 ∨ lo ≥ factor
    · simp only [h, ite_true]
      refine ⟨?_, h2, h3, fun a b => absurd h (by omega)⟩
      rw [Int.add_mul, Int.mul_comm (lo / factor) factor]; omega
    · simp only [h, ite_false]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | omega | (intros; trivial)
  · obtain ⟨h0, h1, h2, h3, h4⟩ := normalizeDSUsC_spec d s us
    refine ⟨h0, h1, h2, h3, h4, fun a b c e => ?_⟩
    unfold normalizeDSUsC
    simp [show ¬(us < 0 ∨ us ≥ 1000000) by omega, show ¬(s < 0 ∨ s ≥ 86400) by omega]

/-! ### `new_delta_ex` and `look_up_delta` -/

/-- `new_delta_ex(d, s, us, normalize, type)` returns the normalized value of
`(d * 86400 + s) * 10**6 + us` microseconds, as an object of class `type`, except that a
zero value of class `timedelta` is the static `zero_delta` (`look_up_delta`), so
`timedelta(0) is timedelta(0)` in C; out of the day range it raises `OverflowError` with
`check_delta_day_range`'s message. With `normalize` false, the precondition is the one the
`assert`s state (:1391-1392): `0 <= s < 86400` and `0 <= us < 10**6`. The arguments are C
`int`s for which normalization does not overflow (the comment at :1378-1382). The value-level
`new_delta(d, s, us, 1)` used elsewhere (`newDeltaNormC`) is its value. -/
def NewDeltaEx : Prop :=
  (∀ (d s us : Int) (normalize : Bool) (ty : TdCls),
    (normalize = false → 0 ≤ s ∧ s < 86400 ∧ 0 ≤ us ∧ us < 1000000) →
    newDeltaExC d s us normalize ty = tdObjOf ty <$> mkDeltaN ((d * 86400 + s) * 1000000 + us)) ∧
  (∀ d s us : Int, newDeltaNormC d s us = TdObjC.val <$> newDeltaExC d s us true .base)

theorem tdObjOf_val (ty : TdCls) (v : Delta) : (tdObjOf ty v).val = v := by
  unfold tdObjOf
  split
  · rename_i h; rw [h.1]; rfl
  · rfl

theorem tdObjOf_cls (ty : TdCls) (v : Delta) : (tdObjOf ty v).cls = ty := by
  unfold tdObjOf
  split
  · rename_i h; rw [h.2]; rfl
  · rfl

theorem newDeltaExTail_eq (d s us : Int) (ty : TdCls) :
    newDeltaExTail d s us ty =
      if -MAX_DELTA_DAYS ≤ d ∧ d ≤ MAX_DELTA_DAYS then .ok (tdObjOf ty ⟨d, s, us⟩)
      else .error (.overflowError s!"days={d}; must have magnitude <= 999999999") := by
  unfold newDeltaExTail checkDeltaDayRange lookUpDeltaC tdObjOf
  by_cases hc : -MAX_DELTA_DAYS ≤ d ∧ d ≤ MAX_DELTA_DAYS
  · simp only [hc, and_self, ite_true, bind, Except.bind, pure, Except.pure]
    by_cases hz : d = 0 ∧ s = 0 ∧ us = 0 ∧ ty = .base
    · obtain ⟨h1, h2, h3, h4⟩ := hz
      subst h1 h2 h3 h4
      rfl
    · rw [if_neg hz, if_neg (fun hh => hz (by
        simp only [Delta.mk.injEq] at hh
        exact ⟨hh.1.1, hh.1.2.1, hh.1.2.2, hh.2⟩))]
  · simp only [hc, ite_false, bind, Except.bind]

theorem checkThen_eq (d s us : Int) :
    (do checkDeltaDayRange d; return (⟨d, s, us⟩ : Delta) : Py Delta) =
      if -MAX_DELTA_DAYS ≤ d ∧ d ≤ MAX_DELTA_DAYS then .ok ⟨d, s, us⟩
      else .error (.overflowError s!"days={d}; must have magnitude <= 999999999") := by
  unfold checkDeltaDayRange
  by_cases hc : -MAX_DELTA_DAYS ≤ d ∧ d ≤ MAX_DELTA_DAYS
  · simp only [hc, and_self, ite_true, bind, Except.bind, pure, Except.pure]
  · simp only [hc, ite_false, bind, Except.bind]

theorem tdObjOf_map_ite (ty : TdCls) (c : Prop) [Decidable c] (v : Delta) (e : PyExc) :
    tdObjOf ty <$> (if c then (.ok v : Py Delta) else .error e) =
      if c then .ok (tdObjOf ty v) else .error e := by
  by_cases h : c <;> simp [h, Functor.map, Except.map]

theorem newDeltaExC_true (d s us : Int) (ty : TdCls) :
    newDeltaExC d s us true ty = tdObjOf ty <$> newDeltaNormC d s us := by
  unfold newDeltaExC newDeltaNormC
  simp only [ite_true]
  generalize normalizeDSUsC d s us = p
  obtain ⟨d2, s2, us2⟩ := p
  simp only
  rw [newDeltaExTail_eq, checkThen_eq, tdObjOf_map_ite]

theorem newDeltaExC_norm_val (d s us : Int) :
    newDeltaNormC d s us = TdObjC.val <$> newDeltaExC d s us true .base := by
  rw [newDeltaExC_true]
  cases newDeltaNormC d s us <;> simp [Functor.map, Except.map, tdObjOf_val]

theorem newDeltaEx_proven : NewDeltaEx := by
  refine ⟨fun d s us normalize ty hn => ?_, newDeltaExC_norm_val⟩
  cases normalize with
  | true => rw [newDeltaExC_true, newDeltaNormC_eq]
  | false =>
    obtain ⟨h1, h2, h3, h4⟩ := hn rfl
    unfold newDeltaExC
    simp only [Bool.false_eq_true, ite_false]
    rw [newDeltaExTail_eq]
    have e1 : ((d * 86400 + s) * 1000000 + us) / 86400000000 = d := by omega
    have e2 : ((d * 86400 + s) * 1000000 + us) / 1000000 % 86400 = s := by omega
    have e3 : ((d * 86400 + s) * 1000000 + us) % 1000000 = us := by omega
    unfold mkDeltaN
    rw [e1, e2, e3, tdObjOf_map_ite]

/-! ### `microseconds_to_delta_ex` and `checked_divmod` -/

theorem usToDeltaExC_int (n : Int) (ty : TdCls) :
    usToDeltaExC (.int n) ty = tdObjOf ty <$> usToDeltaC n := by
  have e1 : Int.fdiv n 1000000 = n / 1000000 := Int.fdiv_eq_ediv_of_nonneg n (by decide)
  have e2 : Int.fmod n 1000000 = n % 1000000 := Int.fmod_eq_emod_of_nonneg n (by decide)
  have e3 : Int.fdiv (n / 1000000) 86400 = n / 1000000 / 86400 := Int.fdiv_eq_ediv_of_nonneg _ (by decide)
  have e4 : Int.fmod (n / 1000000) 86400 = n / 1000000 % 86400 := Int.fmod_eq_emod_of_nonneg _ (by decide)
  have r1 : asCInt (n % 1000000) = .ok (n % 1000000) := by
    unfold asCInt; rw [if_pos (by omega)]
  have r2 : asCInt (n / 1000000 % 86400) = .ok (n / 1000000 % 86400) := by
    unfold asCInt; rw [if_pos (by omega)]
  have c1 : ¬¬(0 ≤ n % 1000000 ∧ n % 1000000 < 1000000) := by omega
  have c2 : ¬¬(0 ≤ n / 1000000 % 86400 ∧ n / 1000000 % 86400 < 24 * 3600) := by omega
  unfold usToDeltaExC usToDeltaC newDeltaExC
  simp only [checkedDivmodC, pyDivmod, pyLongAsIntC, show (1000000 : Int) ≠ 0 by decide,
    show (86400 : Int) ≠ 0 by decide, ite_false, e1, e2, e3, e4, r1, r2, c1, c2,
    bind, Except.bind, pure, Except.pure, Bool.false_eq_true]
  cases h : asCInt (n / 1000000 / 86400) with
  | error e => rfl
  | ok d =>
    simp only
    rw [newDeltaExTail_eq]
    have := checkThen_eq d (n / 1000000 % 86400) (n % 1000000)
    simp only [bind, Except.bind, pure, Except.pure] at this
    rw [this, tdObjOf_map_ite]

/-- `microseconds_to_delta_ex(pyus, type)` (:2218-2284) with `checked_divmod` (:2193-2213),
for every object. An int converts exactly as the value model `usToDeltaC` does (whose
agreement with Python's `timedelta(0, 0, n)` is `TimedeltaCtorTwins`), as an object of class
`type`. Any other object `o` is divided by `divmod(o, 10**6)`: when that raises, the error
propagates; a non-tuple is `TypeError: divmod() returned non-tuple (type T)`; a tuple of
another size than 2 is `TypeError: divmod() returned a tuple of size N`; a remainder that is
an int outside `[0, 10**6)` is `TypeError: divmod() returned a value out of range` (a C-int
one; a larger one is the `OverflowError` of `PyLong_AsInt`); a remainder without `__index__`
is `TypeError: 'T' object cannot be interpreted as an integer`; and a pair of ints
`(q, r)` with `0 <= r < 10**6` converts like the int `q * 10**6 + r`. -/
def UsToDeltaExObj : Prop :=
  (∀ (n : Int) (ty : TdCls), usToDeltaExC (.int n) ty = tdObjOf ty <$> usToDeltaC n) ∧
  ∀ (tp : String) (idx : Option (Py Int)) (dm : Int → DmOut) (ty : TdCls),
    (∀ e, dm 1000000 = .raise e → usToDeltaExC (.other tp idx dm) ty = .error e) ∧
    (∀ t, dm 1000000 = .nontuple t →
      usToDeltaExC (.other tp idx dm) ty = .error (.typeError s!"~divmod() returned non-tuple (type {t})")) ∧
    (∀ n : Nat, n ≠ 2 → dm 1000000 = .tupleOf n →
      usToDeltaExC (.other tp idx dm) ty = .error (.typeError s!"divmod() returned a tuple of size {n}")) ∧
    (∀ (q : PObj) (r : Int), dm 1000000 = .pair q (.int r) → fitsCInt r →
      ¬(0 ≤ r ∧ r < 1000000) → usToDeltaExC (.other tp idx dm) ty = .error badDivmod) ∧
    (∀ (q : PObj) (tp' : String) (dm' : Int → DmOut), dm 1000000 = .pair q (.other tp' none dm') →
      usToDeltaExC (.other tp idx dm) ty =
        .error (.typeError s!"~'{tp'}' object cannot be interpreted as an integer")) ∧
    (∀ q r : Int, dm 1000000 = .pair (.int q) (.int r) → 0 ≤ r → r < 1000000 →
      usToDeltaExC (.other tp idx dm) ty = usToDeltaExC (.int (q * 1000000 + r)) ty)

theorem usToDeltaExObj_proven : UsToDeltaExObj := by
  refine ⟨usToDeltaExC_int, fun tp idx dm ty => ⟨fun e he => ?_, fun t ht => ?_, fun n hl hi => ?_,
    fun q r hd hf hr => ?_, fun q tp' dm' hd => ?_, fun q r hd h0 h1 => ?_⟩⟩
  · simp [usToDeltaExC, checkedDivmodC, he, bind, Except.bind]
  · simp [usToDeltaExC, checkedDivmodC, ht, bind, Except.bind]
  · simp [usToDeltaExC, checkedDivmodC, hi, bind, Except.bind]
  · unfold fitsCInt at hf
    have : asCInt r = .ok r := by unfold asCInt; rw [if_pos hf]
    simp [usToDeltaExC, checkedDivmodC, hd, pyLongAsIntC, this, hr, bind, Except.bind]
  · simp [usToDeltaExC, checkedDivmodC, hd, pyLongAsIntC, bind, Except.bind]
  · have hr : asCInt r = .ok r := by unfold asCInt; rw [if_pos (by omega)]
    have e1 : Int.fdiv (q * 1000000 + r) 1000000 = q := by
      rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]; omega
    have e2 : Int.fmod (q * 1000000 + r) 1000000 = r := by
      rw [Int.fmod_eq_emod_of_nonneg _ (by decide)]; omega
    have c : ¬¬(0 ≤ r ∧ r < 1000000) := by omega
    simp only [usToDeltaExC, checkedDivmodC, hd, pyDivmod, pyLongAsIntC, hr, e1, e2, c,
      show (1000000 : Int) ≠ 0 by decide, ite_false, bind, Except.bind, pure, Except.pure]

/-- `timedelta(...)` with int arguments in C, through `delta_new_impl`'s
`microseconds_to_delta_ex(x, type)`, for every class: the value of the value model `deltaC`
(which agrees with Python, `TimedeltaCtorTwins`), as an object of that class, the zero value
of `timedelta` itself being the `zero_delta` singleton (`timedelta(0) is timedelta(0)` is
`True` in C, `False` in Python, where every call makes a new object; identity of equal
timedeltas is not promised, so that is not a defect). A subclass never gets the singleton. -/
def TimedeltaCtorObj : Prop :=
  (∀ (ty : TdCls) (days seconds microseconds milliseconds minutes hours weeks : Int),
    deltaObjC ty days seconds microseconds milliseconds minutes hours weeks =
      tdObjOf ty <$> deltaC days seconds microseconds milliseconds minutes hours weeks) ∧
  deltaObjC .base 0 0 0 0 0 0 0 = .ok .zeroSingleton ∧
  (∀ i, deltaObjC (.sub i) 0 0 0 0 0 0 0 = .ok (.fresh (.sub i) ⟨0, 0, 0⟩))

theorem timedeltaCtorObj_proven : TimedeltaCtorObj := by
  refine ⟨fun ty days seconds microseconds milliseconds minutes hours weeks => ?_, ?_, fun i => ?_⟩
  · unfold deltaObjC deltaC; exact usToDeltaExC_int _ ty
  · unfold deltaObjC; rw [usToDeltaExC_int]; decide
  · unfold deltaObjC; rw [usToDeltaExC_int]; rfl

/-! ### `timedelta * n` with an int subclass -/

/-- `timedelta * n` agrees between the twins for every int operand, an int subclass whose
`__mul__` is overridden included. -/
def TimedeltaMulIntSubclassTwins : Prop :=
  ∀ (a : Delta) (k : IntOperand), a.Valid →
    SameOutcome (deltaMultiplyPy (.td a) (.int k)) ((Option.map TdObjC.val) <$> deltaMultiplyC (.td a) (.int k))

/-- A float `2.5` as `microseconds_to_delta` sees it: `divmod(2.5, n)` is a pair of floats,
which have no `__index__`. -/
def float25Obj : PObj :=
  .other "float" none (fun _ => .pair (.other "float" none (fun _ => .raise .modelFuel))
    (.other "float" none (fun _ => .raise .modelFuel)))

/-- `class I(int): __mul__ = lambda s, o: 2.5`; `timedelta(1) * I(2)`: Python computes
`self._days * other` with `int.__mul__` and returns `timedelta(days=2)`; C's
`multiply_int_timedelta` computes `PyNumber_Multiply(intobj, us)`, with the int on the left,
so `I.__mul__` runs and returns `2.5`, and `microseconds_to_delta` raises
`TypeError: 'float' object cannot be interpreted as an integer`. -/
theorem timedeltaMulIntSubclassTwins_refuted : ¬ TimedeltaMulIntSubclassTwins := by
  intro h
  have := h ⟨1, 0, 0⟩ ⟨2, fun _ => .ok float25Obj⟩ (by decide)
  have e1 : deltaMultiplyPy (.td ⟨1, 0, 0⟩) (.int ⟨2, fun _ => .ok float25Obj⟩) = .ok (some ⟨2, 0, 0⟩) := by
    decide
  have e2 : deltaMultiplyC (.td ⟨1, 0, 0⟩) (.int ⟨2, fun _ => .ok float25Obj⟩) =
      .error (.typeError "~'float' object cannot be interpreted as an integer") := rfl
  rw [e1, e2] at this
  exact this

/-! ### The dispatch of `*` and `/` -/

/-- An operand with no overridden arithmetic: a timedelta, an `int`, a `float`, another
object. -/
inductive PlainOp where
  | td (t : Delta)
  | int (n : Int)
  | float (x : Binary64.F64)
  | other

def PlainOp.op : PlainOp → TdOperand
  | .td t => .td t
  | .int n => .int (IntOperand.exact n)
  | .float x => .float x
  | .other => .other

def PlainOp.isTd : PlainOp → Bool
  | .td _ => true
  | _ => false

/-- Every timedelta operand is a valid timedelta. -/
def PlainOp.Ok : PlainOp → Prop
  | .td t => t.Valid
  | _ => True

theorem sameOutcome_some {α : Type} (x y : Py α) (h : SameOutcome x y) :
    SameOutcome (some <$> x) (some <$> y) := by
  cases x <;> cases y <;> simp_all [SameOutcome, Functor.map, Except.map]

theorem multiplyIntExact (n : Int) (a : Delta) :
    multiplyIntTimedeltaC (IntOperand.exact n) a = tdObjOf .base <$> a.mulC n := by
  unfold multiplyIntTimedeltaC IntOperand.exact Delta.mulC
  simp only [bind, Except.bind]
  exact usToDeltaExC_int _ _

theorem map_val_tdObjOf {ty : TdCls} (x : Py Delta) :
    (Option.map TdObjC.val) <$> (some <$> (tdObjOf ty <$> x)) = some <$> x := by
  cases x <;> simp [Functor.map, Except.map, tdObjOf_val]

/-- `left * right` with a timedelta on either side (`delta_multiply`, :2579-2602, against
`timedelta.__mul__`/`__rmul__`, Py:858-871) for operands without overridden arithmetic:
the twins agree on `NotImplemented` (two timedeltas, another object) and on the outcome of
`timedelta * int`, `int * timedelta`, `timedelta * float` and `float * timedelta` (the int and
float results being `TimedeltaOpsTwins` and `TimedeltaFloatOps`), and C's result is always of
class `timedelta`. Precondition: the timedelta operands are valid (the type invariant). -/
def TimedeltaMulDispatch : Prop :=
  ∀ l r : PlainOp, (l.isTd ∨ r.isTd) → l.Ok → r.Ok →
    SameOutcome (deltaMultiplyPy l.op r.op) ((Option.map TdObjC.val) <$> deltaMultiplyC l.op r.op) ∧
    (∀ o, deltaMultiplyC l.op r.op = .ok (some o) → o.cls = .base)

theorem cls_of_map {x : Py Delta} {o : TdObjC} (h : some <$> (tdObjOf .base <$> x) = (.ok (some o) : Py (Option TdObjC))) :
    o.cls = .base := by
  cases x with
  | error e => simp [Functor.map, Except.map] at h
  | ok v =>
    simp only [Functor.map, Except.map, Except.ok.injEq, Option.some.injEq] at h
    rw [← h, tdObjOf_cls]

theorem timedeltaMulDispatch_proven : TimedeltaMulDispatch := by
  intro l r hl hr ho
  have hops := timedeltaOpsTwins_proven
  have hfl := timedeltaFloatOps_proven
  cases l with
  | td a =>
    cases r with
    | td b => exact ⟨rfl, fun o h => by cases h⟩
    | int n =>
      simp only [PlainOp.op, deltaMultiplyC, deltaMultiplyPy, tdMulPy]
      rw [multiplyIntExact, map_val_tdObjOf]
      refine ⟨sameOutcome_some _ _ (hops a a n hr hr).2.2.2.2.1, fun o h => ?_⟩
      exact cls_of_map h
    | float x =>
      simp only [PlainOp.op, deltaMultiplyC, deltaMultiplyPy, tdMulPy]
      rw [map_val_tdObjOf]
      exact ⟨sameOutcome_some _ _ (hfl a x hr).1, fun o h => cls_of_map h⟩
    | other => exact ⟨rfl, fun o h => by cases h⟩
  | int n =>
    cases r with
    | td a =>
      simp only [PlainOp.op, deltaMultiplyC, deltaMultiplyPy, tdMulPy]
      rw [multiplyIntExact, map_val_tdObjOf]
      refine ⟨sameOutcome_some _ _ (hops a a n ho ho).2.2.2.2.1, fun o h => ?_⟩
      exact cls_of_map h
    | _ => simp [PlainOp.isTd] at hl
  | float x =>
    cases r with
    | td a =>
      simp only [PlainOp.op, deltaMultiplyC, deltaMultiplyPy, tdMulPy]
      rw [map_val_tdObjOf]
      exact ⟨sameOutcome_some _ _ (hfl a x ho).1, fun o h => cls_of_map h⟩
    | _ => simp [PlainOp.isTd] at hl
  | other =>
    cases r with
    | td a => exact ⟨rfl, fun o h => by cases h⟩
    | _ => simp [PlainOp.isTd] at hl

theorem map_val_tdObjOf_inl {β : Type} {ty : TdCls} (x : Py Delta) :
    (Option.map (Sum.map TdObjC.val (id : β → β))) <$>
        ((some ∘ (Sum.inl : TdObjC → Sum TdObjC β) ∘ tdObjOf ty) <$> x) =
      (some ∘ (Sum.inl : Delta → Sum Delta β)) <$> x := by
  cases x <;> simp [Functor.map, Except.map, tdObjOf_val]

theorem sameOutcome_inl {α β : Type} (x y : Py α) (h : SameOutcome x y) :
    SameOutcome ((some ∘ (Sum.inl : α → Sum α β)) <$> x) ((some ∘ Sum.inl) <$> y) := by
  cases x <;> cases y <;> simp_all [SameOutcome, Functor.map, Except.map]

/-- `left / right` with a timedelta on either side (`delta_truedivide`, :2627-2647, against
`timedelta.__truediv__`, Py:886-896) for operands without overridden arithmetic: the twins
agree on `NotImplemented` (a timedelta right operand under a non-timedelta left one, another
object) and on the outcome of `timedelta / timedelta` (a float), `timedelta / int` and
`timedelta / float` (`TimedeltaOpsTwins`, `TimedeltaFloatOps`); in C, `timedelta / timedelta`
is `long_true_divide` of the two microsecond counts (`truedivide_timedelta_timedelta`,
:2414-2434; its rounding is the open `datetime-timedelta-truediv-delta`) and a timedelta
result is of class `timedelta`. Precondition: the timedelta operands are valid. -/
def TimedeltaTruedivDispatch : Prop :=
  ∀ l r : PlainOp, (l.isTd ∨ r.isTd) → l.Ok → r.Ok →
    SameOutcome (deltaTruedividePy l.op r.op)
      ((Option.map (Sum.map TdObjC.val id)) <$> deltaTruedivideC l.op r.op) ∧
    (∀ a b : Delta, l = .td a → r = .td b →
      deltaTruedivideC l.op r.op = (some ∘ Sum.inr) <$> LongObj.trueDivide (.ofInt a.toUs) (.ofInt b.toUs)) ∧
    (∀ o, deltaTruedivideC l.op r.op = .ok (some (.inl o)) → o.cls = .base)

theorem cls_of_inl {x : Py Delta} {o : TdObjC}
    (h : (some ∘ Sum.inl ∘ tdObjOf .base) <$> x = (.ok (some (.inl o)) : Py (Option TdDivRes))) :
    o.cls = .base := by
  cases x with
  | error e => simp [Functor.map, Except.map] at h
  | ok v =>
    simp only [Functor.map, Except.map, Function.comp, Except.ok.injEq, Option.some.injEq, Sum.inl.injEq] at h
    rw [← h, tdObjOf_cls]

theorem timedeltaTruedivDispatch_proven : TimedeltaTruedivDispatch := by
  intro l r hl hr ho
  have hops := timedeltaOpsTwins_proven
  have hfl := timedeltaFloatOps_proven
  refine ⟨?_, ?_, ?_⟩
  · cases l with
    | td a =>
      cases r with
      | td b =>
        simp only [PlainOp.op, deltaTruedivideC, deltaTruedividePy]
        unfold Delta.truedivDeltaPy Delta.truedivDeltaC
        cases LongObj.trueDivide (.ofInt a.toUs) (.ofInt b.toUs) <;>
          simp [SameOutcome, Functor.map, Except.map]
      | int n =>
        simp only [PlainOp.op, deltaTruedivideC, deltaTruedividePy, IntOperand.exact]
        rw [map_val_tdObjOf_inl]
        exact sameOutcome_inl _ _ (hops a a n hr hr).2.2.2.2.2.2.1
      | float x =>
        simp only [PlainOp.op, deltaTruedivideC, deltaTruedividePy]
        rw [map_val_tdObjOf_inl]
        exact sameOutcome_inl _ _ (hfl a x hr).2.1
      | other => exact rfl
    | int n => cases r <;> first | exact rfl | simp [PlainOp.isTd] at hl
    | float x => cases r <;> first | exact rfl | simp [PlainOp.isTd] at hl
    | other => cases r <;> first | exact rfl | simp [PlainOp.isTd] at hl
  · intro a b h1 h2
    subst h1 h2
    rfl
  · intro o h
    cases l with
    | td a =>
      cases r with
      | td b =>
        simp only [PlainOp.op, deltaTruedivideC] at h
        cases hq : a.truedivDeltaC b <;> simp [hq, Functor.map, Except.map] at h
      | int n => exact cls_of_inl h
      | float x => exact cls_of_inl h
      | other => simp [PlainOp.op, deltaTruedivideC] at h
    | int n => cases r <;> simp [PlainOp.op, deltaTruedivideC] at h
    | float x => cases r <;> simp [PlainOp.op, deltaTruedivideC] at h
    | other => cases r <;> simp [PlainOp.op, deltaTruedivideC] at h

/-! ### `__reduce__` with the class -/

/-- A C timedelta as C makes it: a valid value, and never a new object of class
`timedelta` with the zero value (`new_delta_ex` hands out `zero_delta` for that). -/
def TdObjC.Canon (o : TdObjC) : Prop := o.val.Valid ∧ o ≠ .fresh .base ⟨0, 0, 0⟩

/-- `t.__reduce__()` is `(type(t), (days, seconds, microseconds))` in both twins, for every
class (`Py_TYPE(self)` in C, `self.__class__` in Python), and calling that class on those
arguments gives back `t`: in C an object of the same class with the same value, the
`zero_delta` singleton for a zero `timedelta` (so `copy.copy` and `pickle` preserve
`timedelta(0) is timedelta(0)`), and in Python the same value. -/
def TimedeltaReduceCls : Prop :=
  ∀ o : TdObjC, o.Canon →
    o.reduceC = Delta.reducePy o.cls o.val ∧
    deltaObjC o.reduceC.1 (o.reduceC.2.getD 0 0) (o.reduceC.2.getD 1 0) (o.reduceC.2.getD 2 0) 0 0 0 0 = .ok o ∧
    deltaPy ((Delta.reducePy o.cls o.val).2.getD 0 0) ((Delta.reducePy o.cls o.val).2.getD 1 0)
      ((Delta.reducePy o.cls o.val).2.getD 2 0) 0 0 0 0 = .ok o.val

theorem timedeltaReduceCls_proven : TimedeltaReduceCls := by
  intro o ⟨hv, hne⟩
  refine ⟨rfl, ?_, (timedeltaReduce_proven o.val hv).1⟩
  have hc := (timedeltaReduce_proven o.val hv).2
  have e : o.reduceC.2 = o.val.reduceArgs := rfl
  rw [e, timedeltaCtorObj_proven.1, hc]
  show Except.ok (tdObjOf o.cls o.val) = Except.ok o
  congr 1
  cases o with
  | zeroSingleton => rfl
  | fresh c v =>
    show tdObjOf c v = .fresh c v
    unfold tdObjOf
    by_cases h : v = ⟨0, 0, 0⟩ ∧ c = .base
    · obtain ⟨h1, h2⟩ := h; subst h1 h2; exact absurd rfl hne
    · rw [if_neg h]

end PyLean.Datetime
