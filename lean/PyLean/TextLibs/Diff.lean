import PyLean.DiffCore
import PyLean.TextLibs.StructDiff

/-! Differential-testing handler for `textlibs` cases (`"mod": "textlibs"`).
The function name's prefix (`struct.`, ...) selects the sub-handler. -/

namespace PyLean.TextLibs

open Lean PyLean PyLean.Diff

def run (fn : String) (j : Json) : Except String Json :=
  if fn.startsWith "struct." then Struct.run fn j
  else throw s!"unknown fn {fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.TextLibs
