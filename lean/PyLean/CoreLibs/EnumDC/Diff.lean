import PyLean.DiffCore

/-! Differential-testing handler for `corelibs` cases with `"fn": "enumdc.<name>"`.
The dispatcher in `CoreLibs/Diff.lean` strips the `enumdc.` prefix. -/

namespace PyLean.CoreLibs.EnumDC

open Lean PyLean PyLean.Diff

def run (fn : String) (_j : Json) : Except String Json :=
  throw s!"unknown fn enumdc.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.EnumDC
