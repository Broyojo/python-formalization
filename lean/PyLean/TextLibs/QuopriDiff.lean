import PyLean.DiffCore
import PyLean.TextLibs.BinasciiDiff
import PyLean.TextLibs.QuopriModel

/-! `quopri.*` difftest cases; see `difftest/textlibs_diff.py`. -/

namespace PyLean.TextLibs.Quopri

open Lean PyLean PyLean.Diff PyLean.TextLibs.Binascii

def nats (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM Json.getNat?

def decLines (j : Json) : Except String (List (Py (List Nat))) := do
  (← (← field j "lines").getArr?).toList.mapM fun l => do
    if let .ok x := l.getObjVal? "raise" then return (.error (← decExcJ x) : Py (List Nat))
    return .ok (← nats l)

def decRd (j : Json) : Except String (Py (List Nat)) := do
  let l ← field j "rd"
  if let .ok x := l.getObjVal? "raise" then return (.error (← decExcJ x) : Py (List Nat))
  return .ok (← nats l)

def run (fn : String) (j : Json) : Except String Json := do
  let q := (j.getObjValAs? Bool "q").toOption.getD false
  let h := (j.getObjValAs? Bool "h").toOption.getD false
  let writes ← match j.getObjVal? "writes" with
    | .ok w => (← w.getArr?).toList.mapM decWrite
    | .error _ => pure []
  let f : FileSim := { data := [], writes }
  let ok (x : List Nat) : Json := encPy toJson (.ok x : Py (List Nat))
  match fn with
  | "quopri.encodestring" => return ok (encodestringC (← nats (← field j "d")) q h)
  | "quopri.decodestring" =>
    return encPy toJson (a2bQp (.bytes (← nats (← field j "d"))) h)
  | "quopri.py_encodestring" => return ok (encodestringPy (← nats (← field j "d")) q h)
  | "quopri.py_decodestring" => return ok (decodestringPy (← nats (← field j "d")) h)
  | "quopri.encode_c" =>
    let (f, x) := encodeC (← decRd j) f q h
    return encFile f x
  | "quopri.decode_c" =>
    let (f, x) := decodeC (← decRd j) f h
    return encFile f x
  | "quopri.encode_py" =>
    let (f, x) := encodePy (← decLines j) f q h
    return encFile f x
  | "quopri.decode_py" =>
    let (f, x) := decodePy (← decLines j) f h
    return encFile f x
  | "quopri.helpers" =>
    let c ← getNat j "c"
    return ok ([if needsQuoting c q h then 1 else 0, if ishex c then 1 else 0] ++ quote c ++
      (if ishex c then [unhex [c, c]] else []))
  | _ => throw s!"unknown fn {fn}"

end PyLean.TextLibs.Quopri
