import PyLean.Binary64.FloatObj

/-!
Properties of the object-level float paths in `FloatObj.lean`. Each is stated for every
object, every slot result (exceptions included) and both settings of the warnings filter.
-/

namespace PyLean.Binary64

open PyLean F64

/-- The object is not a float of any value (`!PyFloat_Check`). -/
def NotFloat (o : FObj) : Prop := ∀ x, o.kind ≠ .float x

/-- The object is not an int of any value (`!PyLong_Check`). -/
def NotInt (o : FObj) : Prop := ∀ n, o.kind ≠ .int n

/-! ## `_PyNumber_Index` and `PyFloat_AsDouble` -/

/-- `_PyNumber_Index` (abstract.c:1410-1453) for every object and slot result: an int gives
its value; otherwise a NULL `nb_index` is `TypeError`, an exception from `__index__`
propagates, an exact int result is taken, a strict int subclass result raises the
`DeprecationWarning` when the filter makes it an error and is taken otherwise, and any
other result is `TypeError`. -/
def NumberIndexSpec : Prop :=
  ∀ (warnErr : Bool) (o : FObj),
    (∀ n, o.kind = .int n → numberIndex warnErr o = .ok n) ∧
    (NotInt o → o.nbIndex = none →
      numberIndex warnErr o = .error (.typeError s!"'{o.tp.take 200}' object cannot be interpreted as an integer")) ∧
    (∀ e, NotInt o → o.nbIndex = some (.error e) → numberIndex warnErr o = .error e) ∧
    (∀ res n, NotInt o → o.nbIndex = some (.ok res) → res.kind = .int n →
      numberIndex warnErr o =
        if res.exact then .ok n
        else if warnErr then .error (.named "DeprecationWarning" (deprecationMsgIndex o res)) else .ok n) ∧
    (∀ res, NotInt o → o.nbIndex = some (.ok res) → NotInt res →
      numberIndex warnErr o = .error (.typeError s!"{o.fq}.__index__() must return an int, not {res.fq}"))

/-- `_PyNumber_Index` past its `PyLong_Check`. -/
theorem numberIndex_notInt {w : Bool} {o : FObj} (hn : NotInt o) :
    numberIndex w o =
      match o.nbIndex with
      | none => .error (.typeError s!"'{o.tp.take 200}' object cannot be interpreted as an integer")
      | some (.error e) => .error e
      | some (.ok res) =>
        match res.kind with
        | .int n =>
          if res.exact then .ok n
          else if w then .error (.named "DeprecationWarning" (deprecationMsgIndex o res))
          else .ok n
        | _ => .error (.typeError s!"{o.fq}.__index__() must return an int, not {res.fq}") := by
  obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
  cases k with
  | int m => exact absurd rfl (hn m)
  | _ => rfl

theorem numberIndexSpec_proven : NumberIndexSpec := by
  intro w o
  refine ⟨fun n h => ?_, fun hn h => ?_, fun e hn h => ?_, fun res n hn h hr => ?_, fun res hn h hr => ?_⟩
  · obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
    simp only [FObj.kind] at h; subst h; rfl
  · rw [numberIndex_notInt hn, h]
  · rw [numberIndex_notInt hn, h]
  · rw [numberIndex_notInt hn, h]; simp only []; rw [hr]
  · rw [numberIndex_notInt hn, h]; simp only []
    generalize hk : res.kind = k at hr
    cases k with
    | int m => exact absurd hk (hr m)
    | _ => rfl

/-- `PyFloat_AsDouble` (floatobject.c:247-303) for every object and slot result. A float
(a subclass too, whatever its `__float__`) gives its value (:259-261). Otherwise: with a
NULL `nb_float`, an `nb_index` goes through `_PyNumber_Index` and `PyLong_AsDouble`
(:263-272), and with neither it is `TypeError` (:273-275); an exception from `__float__`
propagates (:278-281); an exact float result is taken, a strict float subclass result
raises the `DeprecationWarning` when the filter makes it an error (:290-297) and is taken
otherwise, and any other result is `TypeError` (:283-288). -/
def AsDoubleSpec : Prop :=
  ∀ (warnErr : Bool) (o : FObj),
    (∀ x, o.kind = .float x → asDoubleO warnErr o = .ok x) ∧
    (NotFloat o → o.nbFloat = none → o.nbIndex ≠ none →
      asDoubleO warnErr o = (numberIndex warnErr o).bind PyLong_AsDouble) ∧
    (NotFloat o → o.nbFloat = none → o.nbIndex = none →
      asDoubleO warnErr o = .error (.typeError s!"must be real number, not {o.tp.take 50}")) ∧
    (∀ e, NotFloat o → o.nbFloat = some (.error e) → asDoubleO warnErr o = .error e) ∧
    (∀ res x, NotFloat o → o.nbFloat = some (.ok res) → res.kind = .float x →
      asDoubleO warnErr o =
        if res.exact then .ok x
        else if warnErr then .error (.named "DeprecationWarning" (deprecationMsgFloat o res)) else .ok x) ∧
    (∀ res, NotFloat o → o.nbFloat = some (.ok res) → NotFloat res →
      asDoubleO warnErr o = .error (.typeError s!"{o.fq}.__float__() must return a float, not {res.fq}"))

/-- `PyFloat_AsDouble` past its `PyFloat_Check`. -/
theorem asDouble_notFloat {w : Bool} {o : FObj} (hn : NotFloat o) :
    asDoubleO w o =
      match o.nbFloat with
      | none =>
        match o.nbIndex with
        | some _ => (numberIndex w o).bind PyLong_AsDouble
        | none => .error (.typeError s!"must be real number, not {o.tp.take 50}")
      | some (.error e) => .error e
      | some (.ok res) =>
        match res.kind with
        | .float x =>
          if res.exact then .ok x
          else if w then .error (.named "DeprecationWarning" (deprecationMsgFloat o res))
          else .ok x
        | _ => .error (.typeError s!"{o.fq}.__float__() must return a float, not {res.fq}") := by
  obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
  cases k with
  | float y => exact absurd rfl (hn y)
  | _ => rfl

theorem asDoubleSpec_proven : AsDoubleSpec := by
  intro w o
  refine ⟨fun x h => ?_, fun hn h hi => ?_, fun hn h hi => ?_, fun e hn h => ?_,
    fun res x hn h hr => ?_, fun res hn h hr => ?_⟩
  · obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
    simp only [FObj.kind] at h; subst h; rfl
  · rw [asDouble_notFloat hn, h]
    simp only []
    cases hc : o.nbIndex with
    | none => exact absurd hc hi
    | some r => rfl
  · rw [asDouble_notFloat hn, h]; simp only []; rw [hi]
  · rw [asDouble_notFloat hn, h]
  · rw [asDouble_notFloat hn, h]; simp only []; rw [hr]
  · rw [asDouble_notFloat hn, h]; simp only []
    generalize hk : res.kind = k at hr
    cases k with
    | float y => exact absurd hk (hr y)
    | _ => rfl

/-- An object whose `__index__` returns `10**400` and that has no `__float__` makes
`PyFloat_AsDouble` raise `OverflowError`, from `PyLong_AsDouble`. -/
theorem asDouble_index_overflow (w : Bool) :
    asDoubleO w (.mk 5 .plain true "C" "m.C" none (some (.ok (.mk 6 (.int (10 ^ 400)) true "int" "int" none none)))) =
      .error (.overflowError "int too large to convert to float") := by
  cases w <;> decide +kernel

/-! ## `PyFloat_FromString` and `PyNumber_Float` -/

/-- `PyFloat_FromString`'s dispatch (floatobject.c:189-221): a str through the decimal and
space transform, bytes, bytearray and buffers as bytes, and `TypeError` for anything
else, which `float([])` reaches. -/
def FromStringDispatch : Prop :=
  ∀ o : FObj,
    (∀ cps, o.kind = .str cps → fromStringO o = PyFloat_FromString (.str cps)) ∧
    (∀ b, (o.kind = .bytes b ∨ o.kind = .bytearray b ∨ o.kind = .buffer b) →
      fromStringO o = PyFloat_FromString (.bytes b)) ∧
    ((o.kind = .plain ∨ (∃ x, o.kind = .float x) ∨ (∃ n, o.kind = .int n)) →
      fromStringO o = .error (.typeError
        s!"float() argument must be a string or a real number, not '{o.tp.take 200}'"))

theorem fromStringDispatch_proven : FromStringDispatch := by
  intro o
  obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
  refine ⟨fun c h => ?_, fun b h => ?_, fun h => ?_⟩
  · simp only [FObj.kind] at h; subst h; rfl
  · simp only [FObj.kind] at h; rcases h with h | h | h <;> subst h <;> rfl
  · simp only [FObj.kind] at h
    rcases h with h | ⟨x, h⟩ | ⟨n, h⟩ <;> subst h <;> rfl

/-- `PyNumber_Float` (abstract.c:1602-1657) and `float_new_impl` (floatobject.c:1567-1585)
for `type == float`, every object and slot result. `float()` is a new `0.0`; an exact str
goes straight to `PyFloat_FromString`; an exact float is returned itself. Anything else
asks its `nb_float` first, so a float or str subclass overriding `__float__` gets its
override: an exception propagates, an exact float result is returned as that object, a
strict float subclass result raises the `DeprecationWarning` under an error filter and is
copied into a new float otherwise, and any other result is `TypeError`. With a NULL
`nb_float`, `nb_index` is used through `PyLong_AsDouble`; with neither, a float subclass
gives a new float of its value and anything else goes to `PyFloat_FromString`. -/
def FloatNewSpec : Prop :=
  ∀ (warnErr : Bool) (o : FObj),
    floatNew warnErr none none = .ok (.fresh d0) ∧
    (∀ cps, o.kind = .str cps → o.exact = true →
      floatNew warnErr none (some o) = (PyFloat_FromString (.str cps)).map .fresh) ∧
    (∀ x, o.kind = .float x → o.exact = true → floatNew warnErr none (some o) = .ok (.same x)) ∧
    (∀ e, o.isExactFloat = false → (∀ cps, o.kind = .str cps → o.exact = false) →
      o.nbFloat = some (.error e) → floatNew warnErr none (some o) = .error e) ∧
    (∀ res x, o.isExactFloat = false → (∀ cps, o.kind = .str cps → o.exact = false) →
      o.nbFloat = some (.ok res) → res.kind = .float x →
      floatNew warnErr none (some o) =
        if res.exact then .ok (.obj res x)
        else if warnErr then .error (.named "DeprecationWarning" (deprecationMsgFloat o res))
        else .ok (.fresh x)) ∧
    (∀ res, o.isExactFloat = false → (∀ cps, o.kind = .str cps → o.exact = false) →
      o.nbFloat = some (.ok res) → NotFloat res →
      floatNew warnErr none (some o) =
        .error (.typeError s!"{o.fq}.__float__() must return a float, not {res.fq}")) ∧
    (o.isExactFloat = false → (∀ cps, o.kind = .str cps → o.exact = false) →
      o.nbFloat = none → o.nbIndex ≠ none →
      floatNew warnErr none (some o) =
        ((numberIndex warnErr o).bind PyLong_AsDouble).map .fresh) ∧
    (∀ x, o.kind = .float x → o.exact = false → o.nbFloat = none → o.nbIndex = none →
      floatNew warnErr none (some o) = .ok (.fresh x)) ∧
    (NotFloat o → (∀ cps, o.kind = .str cps → o.exact = false) →
      o.nbFloat = none → o.nbIndex = none →
      floatNew warnErr none (some o) = (fromStringO o).map .fresh)

/-- `PyNumber_Float` past its `PyFloat_CheckExact`. -/
theorem numberFloat_notExact {w : Bool} {o : FObj} (hx : o.isExactFloat = false) :
    numberFloat w o =
      match o.nbFloat with
      | some (.error e) => .error e
      | some (.ok res) =>
        match res.kind with
        | .float x =>
          if res.exact then .ok (.obj res x)
          else if w then .error (.named "DeprecationWarning" (deprecationMsgFloat o res))
          else .ok (.fresh x)
        | _ => .error (.typeError s!"{o.fq}.__float__() must return a float, not {res.fq}")
      | none =>
        match o.nbIndex with
        | some _ => ((numberIndex w o).bind PyLong_AsDouble).map .fresh
        | none =>
          match o.kind with
          | .float x => .ok (.fresh x)
          | _ => (fromStringO o).map .fresh := by
  obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
  cases k with
  | float y =>
    cases ex with
    | true => simp [FObj.isExactFloat, FObj.kind, FObj.exact] at hx
    | false =>
      simp only [numberFloat, FObj.kind, FObj.exact, FObj.nbFloat, FObj.nbIndex]
      rcases f with _ | (_ | _) <;> rcases i with _ | (_ | _) <;> try rfl
      all_goals simp [bind, Except.bind, Except.map, pure, Except.pure]
      all_goals (split <;> rfl)
  | _ =>
    simp only [numberFloat, FObj.kind, FObj.exact, FObj.nbFloat, FObj.nbIndex]
    rcases f with _ | (_ | _) <;> rcases i with _ | (_ | _) <;> try rfl
    all_goals simp [bind, Except.bind, Except.map, pure, Except.pure]
    all_goals (split <;> rfl)

/-- `float_new_impl` for `float` itself, past its `PyUnicode_CheckExact`. -/
theorem floatNew_notStr {w : Bool} {o : FObj} (hs : ∀ cps, o.kind = .str cps → o.exact = false) :
    floatNew w none (some o) = numberFloat w o := by
  obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
  cases k with
  | str c =>
    have := hs c rfl
    simp only [FObj.exact] at this
    subst this; rfl
  | _ => rfl

theorem floatNewSpec_proven : FloatNewSpec := by
  intro w o
  refine ⟨rfl, fun c hk he => ?_, fun x hk he => ?_, fun e hx hs h => ?_, fun res x hx hs h hr => ?_,
    fun res hx hs h hr => ?_, fun hx hs h hi => ?_, fun x hk he h hi => ?_, fun hx hs h hi => ?_⟩
  · obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
    simp only [FObj.kind, FObj.exact] at hk he; subst hk; subst he; rfl
  · obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
    simp only [FObj.kind, FObj.exact] at hk he; subst hk; subst he; rfl
  · rw [floatNew_notStr hs, numberFloat_notExact hx, h]
  · rw [floatNew_notStr hs, numberFloat_notExact hx, h]; simp only []; rw [hr]
  · rw [floatNew_notStr hs, numberFloat_notExact hx, h]; simp only []
    generalize hk : res.kind = k at hr
    cases k with
    | float y => exact absurd hk (hr y)
    | _ => rfl
  · rw [floatNew_notStr hs, numberFloat_notExact hx, h]; simp only []
    cases hc : o.nbIndex with
    | none => exact absurd hc hi
    | some r => rfl
  · have hx : o.isExactFloat = false := by simp [FObj.isExactFloat, hk, he]
    have hs : ∀ cps, o.kind = .str cps → o.exact = false := by intro c hc; rw [hk] at hc; cases hc
    rw [floatNew_notStr hs, numberFloat_notExact hx, h]; simp only []; rw [hi]; simp only []; rw [hk]
  · have hx' : o.isExactFloat = false := by
      unfold FObj.isExactFloat
      generalize hk : o.kind = k
      cases k with
      | float y => exact absurd hk (hx y)
      | _ => rfl
    rw [floatNew_notStr hs, numberFloat_notExact hx', h]; simp only []; rw [hi]; simp only []
    generalize hk : o.kind = k
    cases k with
    | float y => exact absurd hk (hx y)
    | _ => rfl

end PyLean.Binary64
