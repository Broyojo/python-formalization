import PyLean.DiffCore
import PyLean.Binary64.Model

/-! Differential-testing handler for `binary64` cases (`"mod": "binary64"`). -/

namespace PyLean.Binary64

open Lean PyLean PyLean.Diff

/-- A float travels as its 64-bit pattern, and a NaN result as the string "nan",
since hardware NaN payloads are not part of the model. -/
def encF (x : F64) : Json :=
  if x.isNaN then Json.str "nan" else toJson x.bits

def getF (j : Json) (key : String) : Except String F64 := do
  return F64.ofBits (← getNat j key)

def runRaw (fn : String) (j : Json) : Except String Json := do
  let a := getF j "x"
  let b := getF j "y"
  let c := getF j "z"
  let f1 (g : F64 → F64) : Except String Json := do return encF (g (← a))
  let f2 (g : F64 → F64 → F64) : Except String Json := do return encF (g (← a) (← b))
  let p2 (g : F64 → F64 → Bool) : Except String Json := do return toJson (g (← a) (← b))
  match fn with
  | "add" => f2 F64.add
  | "sub" => f2 F64.sub
  | "mul" => f2 F64.mul
  | "div" => f2 F64.div
  | "fma" => return encF (F64.fma (← a) (← b) (← c))
  | "sqrt" => f1 F64.sqrt
  | "fmod" => f2 F64.fmod
  | "eq" => p2 F64.eq
  | "ne" => p2 F64.ne
  | "lt" => p2 F64.lt
  | "le" => p2 F64.le
  | "gt" => p2 F64.gt
  | "ge" => p2 F64.ge
  | "floor" => f1 F64.floor
  | "ceil" => f1 F64.ceil
  | "trunc" => f1 F64.trunc
  | "roundAway" => f1 F64.roundAway
  | "neg" => f1 F64.neg
  | "abs" => f1 F64.abs
  | "copysign" => f2 F64.copysign
  | "nextafter" => f2 F64.nextafter
  | "ulp" => f1 F64.ulp
  | "frexp" =>
    let (m, e) := F64.frexp (← a)
    return Json.arr #[encF m, toJson e]
  | "ldexp" => return encF (F64.ldexp (← a) (← getInt j "n"))
  | "ofInt" => return encF (F64.ofInt (← getInt j "n"))
  | "ratio" =>
    return encF (F64.ofRat ((← getInt j "n") / ((← getInt j "d") : Rat)))
  | _ => throw s!"unknown fn {fn}"

def run (fn : String) (j : Json) : Except String Json := do
  return Json.mkObj [("ok", ← runRaw fn j)]

def handler : Handler := fun fn j => some (run fn j)

end PyLean.Binary64
