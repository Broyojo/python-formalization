import PyLean.DiffCore
import PyLean.TextLibs.StructDiff
import PyLean.TextLibs.BinasciiDiff
import PyLean.TextLibs.CsvDiff
import PyLean.TextLibs.ReDiff
import PyLean.TextLibs.PathDiff

/-! Differential-testing handler for `textlibs` cases (`"mod": "textlibs"`).
The function name's prefix (`struct.`, `binascii.`, ...) selects the sub-handler. -/

namespace PyLean.TextLibs

open Lean PyLean PyLean.Diff

def run (fn : String) (j : Json) : Except String Json :=
  if fn.startsWith "struct." then Struct.run fn j
  else if fn.startsWith "binascii." || fn.startsWith "base64." then Binascii.run fn j
  else if fn.startsWith "csv." then Csv.run fn j
  else if fn.startsWith "re." then Re.run fn j
  else if fn.startsWith "path." then Path.run fn j
  else throw s!"unknown fn {fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.TextLibs
