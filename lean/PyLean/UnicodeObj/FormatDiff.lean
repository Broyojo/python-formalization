import PyLean.DiffCore
import PyLean.StrSearch.Diff
import PyLean.UnicodeObj.FormatSpec
import PyLean.UnicodeObj.FormatNumber
import PyLean.UnicodeObj.FormatPercent

/-! Difftest handler for the formatting slice (`fn` names start with `fmt_`). -/

namespace PyLean.UnicodeObj.FormatDiff

open Lean PyLean PyLean.Diff PyLean.StrSearch

/-- An int sent as a hex string, because `json` refuses ints over 4300 digits. -/
def getHexInt (j : Json) (key : String) : Except String Int := do
  let s ← getStr j key
  let (neg, body) := if s.startsWith "-" then (true, s.drop 1) else (false, s.toSlice)
  let v := body.toString.foldl (fun acc c =>
    acc * 16 + (if c ≤ '9' then c.toNat - 48 else c.toNat - 87)) 0
  return if neg then -(v : Int) else v

def getObj (j : Json) : Except String FObj := do
  match ← getStr j "t" with
  | "int" => return .int (← getHexInt j "v")
  | "bool" => return .bool (← getBool j "v")
  | "float" => return .float (Binary64.F64.ofBits (← getHexInt j "v").toNat)
  | "str" => return .str (← getSeq j "s")
  | "none" => return .none
  | t => throw s!"bad obj {t}"

def getArgs (j : Json) : Except String FArgs := do
  match ← getStr j "k" with
  | "tuple" =>
    let arr ← (← field j "items").getArr?
    return .tuple (← arr.toList.mapM getObj)
  | "dict" =>
    let arr ← (← field j "items").getArr?
    return .dict (← arr.toList.mapM fun e => do
      let pair ← e.getArr?
      let k ← (pair[0]!).getArr?
      return (← k.toList.mapM (·.getNat?), ← getObj pair[1]!))
  | _ => return .single (← getObj (← field j "item"))

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "fmt_str" =>
    return encPy toJson (formatStrAdvanced (← getSeq j "s") (← getSeq j "spec"))
  | "fmt_int" =>
    let v ← getHexInt j "v"
    let name ← getStr j "name"
    let shown : Str := if name == "bool" then lit (if v == 1 then "True" else "False")
      else match longFormat v 10 false with | .ok s => s | .error _ => []
    let spec ← getSeq j "spec"
    if spec.isEmpty && name == "int" then
      return encPy (fun (s : Str) => toJson s) (longFormat v 10 false)
    return encPy toJson (do
      match ← formatLongAdvanced v name spec shown with
      | some s => .ok s
      | none => formatLongAsFloat v spec name)
  | "fmt_percent" =>
    return encPy toJson (pyUnicodeFormat (← getSeq j "fmt") (← getArgs (← field j "args")))
  | "fmt_float" =>
    let x := Binary64.F64.ofBits (← getHexInt j "x").toNat
    return encPy toJson (formatFloatAdvanced x (← getSeq j "spec"))
  | "fmt_complex" =>
    let re := Binary64.F64.ofBits (← getHexInt j "re").toNat
    let im := Binary64.F64.ofBits (← getHexInt j "im").toNat
    return encPy toJson (formatComplexAdvanced re im (← getSeq j "spec"))
  | _ => throw s!"unknown fn {fn}"

def handler : Handler := fun fn j =>
  if fn.startsWith "fmt_" then some (run fn j) else none

end PyLean.UnicodeObj.FormatDiff
