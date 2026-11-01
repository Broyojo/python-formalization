import PyLean.DiffCore
import PyLean.TextLibs.HtmlModel

/-! `html.*` difftest cases; see `difftest/textlibs_diff.py`. -/

namespace PyLean.TextLibs.Html

open Lean PyLean PyLean.Diff

def nats (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM Json.getNat?

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "html.escape" =>
    return encPy toJson (.ok (escape (← nats (← field j "s")) (← getBool j "quote")) : Py (List Nat))
  | "html.unescape" => return encPy toJson (unescape (← nats (← field j "s")))
  | _ => throw s!"unknown fn {fn}"

end PyLean.TextLibs.Html
