import PyLean.DiffCore
import PyLean.Bytecode.GenObj.Diff

/-! Differential-testing handler for `bytecode` cases (`"mod": "bytecode"`). -/

namespace PyLean.Bytecode

open Lean PyLean PyLean.Diff

def run (fn : String) (j : Json) : Except String Json :=
  match GenObj.run? fn j with
  | some r => r
  | none => throw s!"unknown fn {fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.Bytecode
