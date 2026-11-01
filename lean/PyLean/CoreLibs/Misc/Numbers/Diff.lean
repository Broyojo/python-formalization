import PyLean.CoreLibs.Misc.Common
import PyLean.CoreLibs.Misc.Numbers.Model
import PyLean.PyIO.Double

/-! `misc.numbers` cases: `{"m": <method>, "a": int, "b": int, "fail": [<dunder>, ...]}`. The
concrete subclass wraps an int and raises `ArithmeticError(<dunder>)` from the methods in `fail`,
which makes the order of primitive calls observable. Floats are compared as sign, 53-bit
significand and exponent, computed exactly by `PyLean.PyIO.roundRat`. -/

namespace PyLean.CoreLibs.Misc.Numbers

open Lean PyLean PyLean.Diff PyLean.CoreLibs.Misc

/-- A finite nonzero-or-zero float: sign and value. -/
structure SF where
  neg : Bool
  d : PyIO.Dbl

def sfJson (f : SF) : Json := Json.arr #[jBool f.neg, toJson f.d.m, jInt f.d.e]

def failing (fail : List String) (name : String) {β : Type} (x : Py β) : Py β :=
  if fail.contains name then .error (.named "ArithmeticError" name) else x

def divSF (a b : Int) : Py SF :=
  if b = 0 then .error (.zeroDivisionError "division by zero")
  else .ok { neg := (decide (a < 0)) != (decide (b < 0)), d := PyIO.roundRat a.natAbs b.natAbs }

def prims (fail : List String) (rat : Option (Int × Int)) : Prims Int SF (SF × SF) where
  zero := 0
  one := 1
  eq := fun a b => failing fail "__eq__" (.ok (decide (a = b)))
  add := fun a b => failing fail "__add__" (.ok (a + b))
  neg := fun a => failing fail "__neg__" (.ok (-a))
  pos := fun a => failing fail "__pos__" (.ok a)
  floordiv := fun a b => failing fail "__floordiv__"
    (if b = 0 then .error (.zeroDivisionError "division by zero") else .ok (a.fdiv b))
  mod := fun a b => failing fail "__mod__"
    (if b = 0 then .error (.zeroDivisionError "division by zero") else .ok (a.fmod b))
  float := fun a => failing fail "__float__" (.ok { neg := decide (a < 0), d := PyIO.roundRat a.natAbs 1 })
  complexOf := fun f => .ok (f, { neg := false, d := ⟨0, 0⟩ })
  toInt := fun a => if rat.isSome then .ok a else failing fail "__int__" (.ok a)
  numerator := fun a => failing fail "numerator" (.ok (match rat with
    | some r => r.1
    | none => a))
  denominator := fun _ => failing fail "denominator" (.ok (match rat with
    | some r => r.2
    | none => 1))
  intDiv := divSF
  intFloat := fun n => .ok { neg := decide (n < 0), d := PyIO.roundRat n.natAbs 1 }

def stub2 (m : String) (a b : Int) : Option (Py Int) :=
  match m with
  | "Complex.real" => some (Complex.real a)
  | "Complex.imag" => some (Complex.imag a)
  | "Complex.__add__" => some (Complex.__add__ a b)
  | "Complex.__radd__" => some (Complex.__radd__ a b)
  | "Complex.__neg__" => some (Complex.__neg__ a)
  | "Complex.__pos__" => some (Complex.__pos__ a)
  | "Complex.__mul__" => some (Complex.__mul__ a b)
  | "Complex.__rmul__" => some (Complex.__rmul__ a b)
  | "Complex.__truediv__" => some (Complex.__truediv__ a b)
  | "Complex.__rtruediv__" => some (Complex.__rtruediv__ a b)
  | "Complex.__pow__" => some (Complex.__pow__ a b)
  | "Complex.__rpow__" => some (Complex.__rpow__ a b)
  | "Complex.__abs__" => some (Complex.__abs__ a)
  | "Complex.conjugate" => some (Complex.conjugate a)
  | "Real.__float__" => some (Real.__float__ (F := Int) a)
  | "Real.__trunc__" => some (Real.__trunc__ a)
  | "Real.__floor__" => some (Real.__floor__ a)
  | "Real.__ceil__" => some (Real.__ceil__ a)
  | "Real.__round__" => some (Real.__round__ a)
  | "Real.__floordiv__" => some (Real.__floordiv__ a b)
  | "Real.__rfloordiv__" => some (Real.__rfloordiv__ a b)
  | "Real.__mod__" => some (Real.__mod__ a b)
  | "Real.__rmod__" => some (Real.__rmod__ a b)
  | "Rational.numerator" => some (Rational.numerator a)
  | "Rational.denominator" => some (Rational.denominator a)
  | "Integral.__int__" => some (Integral.__int__ a)
  | "Integral.__pow__" => some (Integral.__pow__ a b)
  | "Integral.__lshift__" => some (Integral.__lshift__ a b)
  | "Integral.__rlshift__" => some (Integral.__rlshift__ a b)
  | "Integral.__rshift__" => some (Integral.__rshift__ a b)
  | "Integral.__rrshift__" => some (Integral.__rrshift__ a b)
  | "Integral.__and__" => some (Integral.__and__ a b)
  | "Integral.__rand__" => some (Integral.__rand__ a b)
  | "Integral.__xor__" => some (Integral.__xor__ a b)
  | "Integral.__rxor__" => some (Integral.__rxor__ a b)
  | "Integral.__or__" => some (Integral.__or__ a b)
  | "Integral.__ror__" => some (Integral.__ror__ a b)
  | "Integral.__invert__" => some (Integral.__invert__ a)
  | _ => none

def runCase (j : Json) : Except String Json := do
  let m ← getStr j "m"
  let a ← getInt j "a"
  let b ← getInt j "b"
  let fail ← (← jArr (← field j "fail")).mapM (fun x => x.getStr?)
  let p := prims fail none
  let pr := prims fail (some (a, b))
  let pair (x : Int × Int) : Json := Json.arr #[jInt x.1, jInt x.2]
  let r : Json := match m with
    | "Complex.__complex__" => encR jUnit (Complex.__complex__ a)
    | "Complex.__eq__" => encR jBool (Complex.__eq__ a b)
    | "Real.__lt__" => encR jBool (Real.__lt__ a b)
    | "Real.__le__" => encR jBool (Real.__le__ a b)
    | "Complex.__bool__" => encR jBool (Complex.__bool__ p a)
    | "Complex.__sub__" => encR jInt (Complex.__sub__ p a b)
    | "Complex.__rsub__" => encR jInt (Complex.__rsub__ p a b)
    | "Real.__divmod__" => encR pair (Real.__divmod__ p a b)
    | "Real.__rdivmod__" => encR pair (Real.__rdivmod__ p a b)
    | "Real.__complex__" =>
      encR (fun c => Json.arr #[sfJson c.1, sfJson c.2]) (Real.__complex__ p a)
    | "Real.real" => encR jInt (Real.real p a)
    | "Real.imag" => encR jInt (Real.imag p a)
    | "Real.conjugate" => encR jInt (Real.conjugate p a)
    | "Rational.__float__" => encR sfJson (Rational.__float__ pr a)
    | "Integral.__index__" => encR jInt (Integral.__index__ p a)
    | "Integral.__float__" => encR sfJson (Integral.__float__ p a)
    | "Integral.numerator" => encR jInt (Integral.numerator p a)
    | "Integral.denominator" => encR jInt (Integral.denominator p a)
    | _ => match stub2 m a b with
      | some r => encR jInt r
      | none => jStr s!"unknown {m}"
  return Json.mkObj [("ok", r)]

end PyLean.CoreLibs.Misc.Numbers
