import PyLean.DiffCore

/-! Differential-testing handler for `binary64` cases (`"mod": "binary64"`). -/

namespace PyLean.Binary64

open Lean PyLean PyLean.Diff

def run (fn : String) (_j : Json) : Except String Json :=
  throw s!"unknown fn {fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.Binary64
