import PyLean.DiffCore
import PyLean.PyIO.Newline

/-! Difftest handler for `IncrementalNewlineDecoder`: `none` for a `fn` this area
does not own. -/

namespace PyLean.PyIO

open Lean PyLean PyLean.Diff

def nNats (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM Json.getNat?

def stepND (dec : NDec → List Nat → Bool → Py (NDec × List Nat)) (bytesMode : Bool)
    (d : NDec) (op : Json) : Except String (NDec × Json) := do
  match ← getStr op "op" with
  | "decode" =>
    match dec d (← nNats (← field op "s")) (← getBool op "final") with
    | .ok (d', out) => return (d', Json.mkObj [("ok", Json.mkObj [("s", toJson out)])])
    | .error e => return (d, encPy (fun (_ : Unit) => Json.null) (.error e))
  | "getstate" =>
    let (b, f) := d.getstate
    return (d, Json.mkObj [("ok", Json.arr #[Json.mkObj [("b", toJson b)], toJson f])])
  | "setstate" =>
    return (d.setstate (← nNats (← field op "b")) (← getInt op "flag"), Json.mkObj [("ok", Json.null)])
  | "reset" => return (d.reset, Json.mkObj [("ok", Json.null)])
  | "newlines" =>
    let v : Json := match newlinesVal d.seennl with
      | .atom .none => Json.null
      | .atom (.str s) => Json.mkObj [("s", toJson s)]
      | .list l => Json.arr (l.map fun a => match a with
          | .str s => Json.mkObj [("s", toJson s)]
          | _ => Json.null).toArray
      | _ => Json.null
    return (d, Json.mkObj [("ok", v)])
  | o =>
    let _ := bytesMode
    throw s!"unknown op {o}"

def runText (fn : String) (j : Json) : Option (Except String Json) :=
  match fn with
  | "nldec_c" | "nldec_py" => some do
    let translate ← getBool j "translate"
    let inner ← getBool j "inner"
    let ops ← (← field j "ops").getArr?
    let dec := if fn = "nldec_c" then NC.decode else NP.decode
    let mut d := NDec.fresh (if inner then some [] else none) translate
    let mut out : Array Json := #[]
    for op in ops do
      let (d', r) ← stepND dec inner d op
      d := d'
      out := out.push r
    return Json.mkObj [("ok", Json.arr out)]
  | _ => none

end PyLean.PyIO
