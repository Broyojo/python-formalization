import PyLean.MathInt.FltLemmas
import PyLean.Binary64.Props2

/-!
# Properties: `floor`, `ceil`, `trunc`

`math_floor`, `math_ceil`, `math_trunc` (Modules/mathmodule.c:990-1082, 1412-1430) against
Doc/library/math.rst: the floor, ceiling and truncation of a float as an exact int, and
delegation to `__floor__`, `__ceil__`, `__trunc__` for anything that is not a float.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-- What converting a float to an int raises (`PyLong_FromDouble`, longobject.c:469-514),
or the exact integer `n`. -/
def intOfFloat (x : F64) (n : Int) : Py Ret :=
  if x.isNaN then .error (.valueError "cannot convert float NaN to integer")
  else if x.isInf then .error (.overflowError "cannot convert float infinity to integer")
  else .ok (.int n)

/-- `floor`, `ceil` and `trunc` for every argument object.

* An exact float, or a float subclass that does not override the method: the exact floor
  ("the largest integer less than or equal to x"), ceiling ("the smallest integer greater
  than or equal to x") and truncation ("rounds toward 0") as an `int`, with `ValueError`
  for a NaN and `OverflowError` for an infinity. The C fast path for exact floats and
  `float.__floor__`/`__ceil__`/`__trunc__` agree.
* A float subclass that overrides the method: that method's result or exception.
* An `int` or `bool`: its value, exactly (no float conversion, so no `OverflowError` for
  huge ints).
* Any other object: "delegates to `x.__floor__`" (`__ceil__`, `__trunc__`): its result,
  whatever it is, or its exception. Without the method, `floor` and `ceil` convert with
  `__float__`/`__index__` (and raise what that raises), and `trunc` raises `TypeError`. -/
def FloorCeilTrunc : Prop :=
  (∀ x : F64,
    math_floor (.float x) = intOfFloat x x.toRat.floor ∧
    math_ceil (.float x) = intOfFloat x x.toRat.ceil ∧
    math_trunc (.float x) = intOfFloat x (if x.toRat < 0 then x.toRat.ceil else x.toRat.floor)) ∧
  (∀ t x, math_floor (.floatSub t x none none none) = math_floor (.float x) ∧
    math_ceil (.floatSub t x none none none) = math_ceil (.float x) ∧
    math_trunc (.floatSub t x none none none) = math_trunc (.float x)) ∧
  (∀ t x fl ce tr r, (fl = some r → math_floor (.floatSub t x fl ce tr) = r) ∧
    (ce = some r → math_ceil (.floatSub t x fl ce tr) = r) ∧
    (tr = some r → math_trunc (.floatSub t x fl ce tr) = r)) ∧
  (∀ n : Int, math_floor (.int n) = .ok (.int n) ∧ math_ceil (.int n) = .ok (.int n) ∧
    math_trunc (.int n) = .ok (.int n)) ∧
  (∀ b : Bool, math_floor (.bool b) = .ok (.int (if b then 1 else 0)) ∧
    math_ceil (.bool b) = .ok (.int (if b then 1 else 0)) ∧
    math_trunc (.bool b) = .ok (.int (if b then 1 else 0))) ∧
  (∀ ty fq df di fl ce tr,
    let o := Arg.other ty fq df di fl ce tr
    (∀ r, fl = some r → math_floor o = r) ∧ (∀ r, ce = some r → math_ceil o = r) ∧
    (∀ r, tr = some r → math_trunc o = r) ∧
    (fl = none → ∀ e, asDouble o = .error e → math_floor o = .error e) ∧
    (ce = none → ∀ e, asDouble o = .error e → math_ceil o = .error e) ∧
    (fl = none → ∀ x, asDouble o = .ok x → math_floor o = math_floor (.float x)) ∧
    (ce = none → ∀ x, asDouble o = .ok x → math_ceil o = math_ceil (.float x)) ∧
    (tr = none → math_trunc o = .error (.typeError s!"type {ty} doesn't define __trunc__ method")))

theorem float_conv_spec (x : F64) (r : Py Int) (n : Int)
    (hfin : x.isFinite = true → r = .ok n)
    (hnan : x.isNaN = true → r = .error (.valueError "cannot convert float NaN to integer"))
    (hinf : x.isInf = true → r = .error (.overflowError "cannot convert float infinity to integer")) :
    r.map Ret.int = intOfFloat x n := by
  unfold intOfFloat
  rcases classify x with h | h | h
  · rw [hfin h, isNaN_false_of_finite h, isInf_false_of_finite h]; rfl
  · rw [hinf h, not_nan_of_inf h, h]; rfl
  · rw [hnan h, h]; rfl

theorem floorCeilTrunc_proven : FloorCeilTrunc := by
  refine ⟨fun x => ?_, fun t x => ⟨rfl, rfl, rfl⟩, fun t x fl ce tr r => ?_, fun n => ⟨rfl, rfl, rfl⟩,
    fun b => ⟨rfl, rfl, rfl⟩, fun ty fq df di fl ce tr => ?_⟩
  · have hc := floatIntConversions_proven x
    refine ⟨?_, ?_, ?_⟩
    · exact float_conv_spec x (float_floor x) _ (fun h => (hc.1 h).1) (fun h => (hc.2.1 h).2.1)
        (fun h => (hc.2.2 h).2.1)
    · exact float_conv_spec x (float_ceil x) _ (fun h => (hc.1 h).2.1) (fun h => (hc.2.1 h).2.2)
        (fun h => (hc.2.2 h).2.2)
    · exact float_conv_spec x (float_trunc x) _ (fun h => (hc.1 h).2.2) (fun h => (hc.2.1 h).1)
        (fun h => (hc.2.2 h).1)
  · refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> subst h <;> rfl
  · refine ⟨fun r h => ?_, fun r h => ?_, fun r h => ?_, fun h e he => ?_, fun h e he => ?_,
      fun h x hx => ?_, fun h x hx => ?_, fun h => ?_⟩
    · subst h; rfl
    · subst h; rfl
    · subst h; rfl
    · subst h; simp [math_floor, floorMethod, he, bind, Except.bind]
    · subst h; simp [math_ceil, ceilMethod, he, bind, Except.bind]
    · subst h; simp [math_floor, floorMethod, hx, bind, Except.bind]
    · subst h; simp [math_ceil, ceilMethod, hx, bind, Except.bind]
    · subst h; rfl

end PyLean.MathInt
