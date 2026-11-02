import PyLean.DiffCore
import PyLean.CoreLibs.Coll.Diff
import PyLean.CoreLibs.CollAbc.Diff
import PyLean.CoreLibs.Functools.Diff
import PyLean.CoreLibs.Operator.Diff
import PyLean.CoreLibs.EnumDC.Diff
import PyLean.CoreLibs.Misc.Diff
import PyLean.CoreLibs.CalStat.Diff
import PyLean.CoreLibs.Rand.Diff
import PyLean.CoreLibs.Warn.Diff

/-! Differential-testing handler for `corelibs` cases (`"mod": "corelibs"`).
`fn` is `<area>.<name>`; the area's handler gets `<name>`. -/

namespace PyLean.CoreLibs

open Lean PyLean PyLean.Diff

def areas : List (String × Handler) := [
  ("coll", Coll.handler),
  ("collabc", CollAbc.handler),
  ("functools", Functools.handler),
  ("operator", Operator.handler),
  ("enumdc", EnumDC.handler),
  ("misc", Misc.handler),
  ("calstat", CalStat.handler),
  ("rand", Rand.handler),
  ("warn", Warn.handler)
]

def handler : Handler := fun fn j =>
  match fn.splitOn "." with
  | area :: rest =>
    match areas.lookup area with
    | some h => h (".".intercalate rest) j
    | none => none
  | [] => none

end PyLean.CoreLibs
