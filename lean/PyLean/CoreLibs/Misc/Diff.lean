import PyLean.DiffCore

/-! Differential-testing handler for `corelibs` cases with `"fn": "misc.<name>"`.
The dispatcher in `CoreLibs/Diff.lean` strips the `misc.` prefix. -/

namespace PyLean.CoreLibs.Misc

open Lean PyLean PyLean.Diff

def run (fn : String) (_j : Json) : Except String Json :=
  throw s!"unknown fn misc.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.Misc
