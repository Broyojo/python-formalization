import PyLean.DiffCore
import PyLean.StrSearch.Diff
import PyLean.UnicodeObj.ObjectKinds

/-! Difftest handler for the object slice (`fn` names start with `obj_`). -/

namespace PyLean.UnicodeObj.ObjectDiff

open Lean PyLean PyLean.Diff PyLean.StrSearch

/-- `[PyUnicode_KIND(s), s.isascii()]`. -/
def encKind (k : Kind) : Json := Json.arr #[toJson k.width, toJson (k == .ascii)]

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "obj_concat" =>
    let l ← getSeq j "l"
    let r ← getSeq j "r"
    return encPy (fun (p : Str × Nat) => Json.arr #[toJson p.1, encKind (kindOfMax p.2)])
      (pyUnicodeConcat l r)
  | "obj_slice" =>
    return encPy encKind (.ok (kindOfMax (sliceMaxChar (← getSeq j "s") (← getSeq j "sub"))) : Py Kind)
  | "obj_repeat" => return encPy toJson (unicodeRepeat (← getSeq j "s") (← getInt j "n"))
  | "obj_compare" =>
    return encPy toJson (.ok (unicodeCompare (← getSeq j "a") (← getSeq j "b")) : Py Int)
  | _ => throw s!"unknown fn {fn}"

def handler : Handler := fun fn j =>
  if fn.startsWith "obj_" then some (run fn j) else none

end PyLean.UnicodeObj.ObjectDiff
