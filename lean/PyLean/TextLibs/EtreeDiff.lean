import PyLean.DiffCore
import PyLean.TextLibs.EtreeModel

/-! `etree.*` difftest cases; see `EtreeArea` in `difftest/textlibs_diff.py`. A child is a
number: below 1000 an Element whose tag is `e<n>`, otherwise the int `n` (not an Element). -/

namespace PyLean.TextLibs.Etree

open Lean PyLean PyLean.Diff
open PyLean.RangeSlice (Slice)

def caseTy : Ty Nat := { isElem := (· < 1000), tpName := fun _ => "int", pyName := fun _ => "int" }

def nats (j : Json) : Except String (List Nat) := do (← j.getArr?).toList.mapM Json.getNat?

def optInt (j : Json) : Except String (Option Int) :=
  match j with
  | .null => .ok none
  | v => some <$> v.getInt?

def getSlice (j : Json) : Except String Slice := do
  match (← (← field j "slice").getArr?).toList with
  | [a, b, c] => return { start := ← optInt a, stop := ← optInt b, step := ← optInt c }
  | _ => throw "slice"

/-- Effects a generator runs on the element at its first `__next__`. -/
def effOf : Nat → List Nat → List Nat
  | 1 => fun _ => []
  | 2 => fun l => l ++ [50]
  | 3 => fun l => l.dropLast
  | _ => id

def getArg (j : Json) : Except String (Arg Nat) := do
  let a ← field j "arg"
  let xs ← nats (← field a "xs")
  match ← getStr a "kind" with
  | "seq" => return .seq xs
  | "iter" =>
    let stop := if (← getBool a "raise") then some (.valueError "boom") else none
    return .iter xs stop (effOf (← getNat a "eff"))
  | _ => return .notIter "int"

def encOut (o : Out Nat) : Json :=
  Json.mkObj [("ok", Json.mkObj [("kids", toJson o.1), ("out", encPy (fun (_ : Unit) => Json.null) o.2)])]

def run (fn : String) (j : Json) : Except String Json := do
  let kids ← nats (← field j "kids")
  let c := (← getStr j "impl") == "c"
  let isIdx := (j.getObjVal? "idx").isOk
  match fn with
  | "etree.get" =>
    if isIdx then
      let i ← getInt j "idx"
      return encPy (fun (n : Nat) => toJson n) (if c then getItemC kids i else getItemPy kids i)
    else
      let s ← getSlice j
      return encPy (fun (r : List Nat) => toJson r) (if c then getSliceC kids s else getSlicePy kids s)
  | "etree.set" =>
    if isIdx then
      let i ← getInt j "idx"
      let x ← getNat j "obj"
      return encOut (if c then assItemC caseTy kids i (some x) else setItemPy caseTy kids i x)
    else
      let s ← getSlice j
      let a ← getArg j
      return encOut (if c then setSliceC caseTy kids s a else setSlicePy caseTy kids s a)
  | "etree.del" =>
    if isIdx then
      let i ← getInt j "idx"
      return encOut (if c then assItemC caseTy kids i none else delItemPy kids i)
    else
      let s ← getSlice j
      return encOut (if c then delSliceC kids s else delSlicePy kids s)
  | _ => throw s!"unknown fn {fn}"

end PyLean.TextLibs.Etree
