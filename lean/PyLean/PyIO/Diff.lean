import PyLean.DiffCore

/-! Differential-testing handler for `pyio` cases (`"mod": "pyio"`). -/

namespace PyLean.PyIO

open Lean PyLean PyLean.Diff

def run (fn : String) (_j : Json) : Except String Json :=
  throw s!"unknown fn {fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.PyIO
