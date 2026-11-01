import PyLean.DiffCore

/-! Differential-testing handler for `corelibs` cases with `"fn": "operator.<name>"`.
The dispatcher in `CoreLibs/Diff.lean` strips the `operator.` prefix. -/

namespace PyLean.CoreLibs.Operator

open Lean PyLean PyLean.Diff

def run (fn : String) (_j : Json) : Except String Json :=
  throw s!"unknown fn operator.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.Operator
