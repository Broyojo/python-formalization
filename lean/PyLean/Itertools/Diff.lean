import PyLean.DiffCore

/-! Differential-testing handler for `itertools` cases (`"mod": "itertools"`). -/

namespace PyLean.Itertools

open Lean PyLean PyLean.Diff

def run (fn : String) (_j : Json) : Except String Json :=
  throw s!"unknown fn {fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.Itertools
