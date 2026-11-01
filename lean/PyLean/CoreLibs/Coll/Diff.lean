import PyLean.DiffCore

/-! Differential-testing handler for `corelibs` cases with `"fn": "coll.<name>"`.
The dispatcher in `CoreLibs/Diff.lean` strips the `coll.` prefix. -/

namespace PyLean.CoreLibs.Coll

open Lean PyLean PyLean.Diff

def run (fn : String) (_j : Json) : Except String Json :=
  throw s!"unknown fn coll.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.Coll
