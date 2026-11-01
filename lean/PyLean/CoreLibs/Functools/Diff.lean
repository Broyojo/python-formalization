import PyLean.DiffCore

/-! Differential-testing handler for `corelibs` cases with `"fn": "functools.<name>"`.
The dispatcher in `CoreLibs/Diff.lean` strips the `functools.` prefix. -/

namespace PyLean.CoreLibs.Functools

open Lean PyLean PyLean.Diff

def run (fn : String) (_j : Json) : Except String Json :=
  throw s!"unknown fn functools.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.Functools
