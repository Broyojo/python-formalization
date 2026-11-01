import PyLean.CoreLibs.Misc.Common

/-!
`Lib/keyword.py`, CPython 3.14.7. `iskeyword` and `issoftkeyword` are the `__contains__` of a
frozenset of a literal list (Lib/keyword.py:62-63).
-/

namespace PyLean.CoreLibs.Misc.Keyword

open Lean PyLean PyLean.Diff PyLean.CoreLibs.Misc

/-- `kwlist`, Lib/keyword.py:17-53. -/
def kwlist : List String :=
  ["False", "None", "True", "and", "as", "assert", "async", "await", "break", "class", "continue",
   "def", "del", "elif", "else", "except", "finally", "for", "from", "global", "if", "import",
   "in", "is", "lambda", "nonlocal", "not", "or", "pass", "raise", "return", "try", "while",
   "with", "yield"]

/-- `softkwlist`, Lib/keyword.py:55-60. -/
def softkwlist : List String := ["_", "case", "match", "type"]

/-- `iskeyword`, Lib/keyword.py:62. -/
def iskeyword (s : String) : Bool := kwlist.contains s

/-- `issoftkeyword`, Lib/keyword.py:63. -/
def issoftkeyword (s : String) : Bool := softkwlist.contains s

def runCase (j : Json) : Except String Json := do
  let s ← getStr j "s"
  return Json.mkObj [("ok", Json.arr #[jBool (iskeyword s), jBool (issoftkeyword s),
    toJson kwlist, toJson softkwlist])]

end PyLean.CoreLibs.Misc.Keyword
