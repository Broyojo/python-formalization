import PyLean.DiffCore

/-! Differential-testing handler for `corelibs` cases with `"fn": "calstat.<name>"`.
The dispatcher in `CoreLibs/Diff.lean` strips the `calstat.` prefix. -/

namespace PyLean.CoreLibs.CalStat

open Lean PyLean PyLean.Diff

def run (fn : String) (_j : Json) : Except String Json :=
  throw s!"unknown fn calstat.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.CalStat
