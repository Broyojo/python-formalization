import PyLean.DiffCore
import PyLean.TextLibs.SimpleQueueGet

/-! Difftest handler for `sq.*` cases: `get(block, timeout)` on a queue holding one item, for the
C accelerator (`sq.get_c`) and the pure-Python twin (`sq.get_py`). The timeout travels as its kind
and an exact ratio, in decimal strings. -/

namespace PyLean.TextLibs.SQ

open Lean PyLean PyLean.Diff

def run (fn : String) (j : Json) : Except String Json := do
  let block ← getBool j "block"
  let k ← getStr j "k"
  let n ← match (← getStr j "n").toInt? with
    | some v => pure v
    | none => throw "sq: n is not an int"
  let d ← match (← getStr j "d").toNat? with
    | some v => pure v
    | none => throw "sq: d is not a nat"
  let t : TO :=
    if k == "none" then .none else if k == "int" then .int n else if k == "inf" then .inf
    else if k == "nan" then .nan else .num n d
  let r : Py Nat := if fn == "sq.get_c" then getC block t 7 else getPy block t 7
  return encPy toJson r

end PyLean.TextLibs.SQ
