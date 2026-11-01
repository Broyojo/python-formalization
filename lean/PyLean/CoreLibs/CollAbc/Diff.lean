import PyLean.DiffCore

/-! Differential-testing handler for `corelibs` cases with `"fn": "collabc.<name>"`.
The dispatcher in `CoreLibs/Diff.lean` strips the `collabc.` prefix. -/

namespace PyLean.CoreLibs.CollAbc

open Lean PyLean PyLean.Diff

def run (fn : String) (_j : Json) : Except String Json :=
  throw s!"unknown fn collabc.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.CollAbc
