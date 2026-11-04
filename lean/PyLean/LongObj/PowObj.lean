import PyLean.LongObj.Props
import PyLean.LongObj.Binop

/-!
`long_pow(v, w, x)`, `Objects/longobject.c:4969-5249` (CPython 3.15.2), at the object
level: `CHECK_BINOP`, the type test on the modulus, the float hand-off, and the
mirrored exponentiation loops `powLoop` (small exponent, left-to-right binary, and the
sliding window of :5117-5225) through `longPowNone` and `longPowMod`.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt PyLean.Registry

/-- What `long_pow` returns when it does not raise: an int, or the result of handing
the call to `PyFloat_Type.tp_as_number->nb_power(v, w, x)` (:5013), which is outside the
integer model. -/
inductive PowOut where
  | int (r : Int)
  | floatPow
  deriving DecidableEq, Repr

/-- `long_pow(v, w, x)`, longobject.c:4969-5249. `x = none` is `Py_None`. `none` in the
result is `NotImplemented`: from `CHECK_BINOP(v, w)` (:4992) or from a modulus that is
neither an int nor `None` (:4995-5004). A negative exponent with no modulus goes to
`float_pow` (:5006-5014). -/
def longPowObj {α : Type} (v w : Obj α) (x : Option (Obj α)) : Py (Option PowOut) :=
  match v, w with
  | .int a, .int b =>
    match x with
    | some (.other _) => .ok none
    | none =>
      if b.neg then .ok (some .floatPow)
      else .ok (some (.int (powLoop a.toInt (digitsOf b.toInt.toNat) none)))
    | some (.int c) =>
      match longPowMod a.toInt b.toInt c.toInt with
      | .ok r => .ok (some (.int r))
      | .error e => .error e
  | _, _ => .ok none

/-- `pow(v, w, x)` for ints: NotImplemented for a non-int base or exponent and for a
modulus that is neither an int nor `None`; with no modulus, a negative exponent is handed
to `float_pow` and otherwise the result is exactly `v**w` on all three exponentiation
paths; with a modulus, ValueError for `x == 0`, and for `w >= 0` the Python remainder of
`v**w` by `x`; and the mirrored loops agree with `MathInt.powMod` for every argument
(which `mathint-pow-neg-exp-inverse` uses for negative exponents). -/
def LongPowExact : Prop :=
  ∀ (α : Type) (o : α) (y : Obj α) (x : Option (Obj α)) (v w : Int),
    longPowObj (.other o) y x = .ok none ∧
    longPowObj y (.other o) x = .ok none ∧
    longPowObj (.int (.ofInt v)) (.int (.ofInt w)) (some (.other o)) = .ok none ∧
    (w < 0 → longPowObj (.int (.ofInt v) : Obj α) (.int (.ofInt w)) none = .ok (some .floatPow)) ∧
    (0 ≤ w → longPowObj (.int (.ofInt v) : Obj α) (.int (.ofInt w)) none =
      .ok (some (.int (v ^ w.toNat)))) ∧
    longPowObj (.int (.ofInt v) : Obj α) (.int (.ofInt w)) (some (.int (.ofInt 0))) =
      .error (.valueError "pow() 3rd argument cannot be 0") ∧
    (∀ c : Int, longPowObj (.int (.ofInt v) : Obj α) (.int (.ofInt w)) (some (.int (.ofInt c))) =
      match powMod v w c with
      | .ok r => .ok (some (.int r))
      | .error e => .error e) ∧
    (0 ≤ w → ∀ c : Int, c ≠ 0 → ∃ q r,
      longPowObj (.int (.ofInt v) : Obj α) (.int (.ofInt w)) (some (.int (.ofInt c))) =
        .ok (some (.int r)) ∧ IsFloorDivmod (v ^ w.toNat) c q r)

theorem longPowExact_proven : LongPowExact := by
  intro α o y x v w
  have hneg : (Long.ofInt w).neg = decide (w < 0) := rfl
  refine ⟨by cases y <;> rfl, by cases y <;> cases x <;> rfl, rfl, fun hw => ?_, fun hw => ?_, ?_,
    fun c => ?_, fun hw c hc => ?_⟩
  · simp [longPowObj, hneg, hw]
  · have h1 : ¬ w < 0 := by omega
    have e := longPowNone_spec v w hw
    simp only [longPowNone, if_neg h1] at e
    simp only [longPowObj, hneg, h1, decide_false, Bool.false_eq_true, ite_false,
      Long.toInt_ofInt]
    rw [Option.some.inj e]
  · simp only [longPowObj, Long.toInt_ofInt]
    rw [show longPowMod v w 0 = .error (.valueError "pow() 3rd argument cannot be 0") from by
      first | rfl | (simp [longPowMod, powModWith]; rfl)]
  · simp only [longPowObj, Long.toInt_ofInt, longPowMod_eq]
  · obtain ⟨q, r, e, f⟩ := longPowMod_floor v w c hw hc
    refine ⟨q, r, ?_, f⟩
    simp only [longPowObj, Long.toInt_ofInt, e]

end PyLean.LongObj
