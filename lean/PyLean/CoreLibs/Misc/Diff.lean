import PyLean.DiffCore
import PyLean.CoreLibs.Misc.Graphlib.Diff
import PyLean.CoreLibs.Misc.Sched.Diff
import PyLean.CoreLibs.Misc.Queue.Diff
import PyLean.CoreLibs.Misc.Numbers.Diff
import PyLean.CoreLibs.Misc.Keyword
import PyLean.CoreLibs.Misc.Types.Diff

/-! Differential-testing handler for `corelibs` cases with `"fn": "misc.<name>"`.
The dispatcher in `CoreLibs/Diff.lean` strips the `misc.` prefix. -/

namespace PyLean.CoreLibs.Misc

open Lean PyLean PyLean.Diff

def run (fn : String) (j : Json) : Except String Json :=
  match fn with
  | "graphlib" => Graphlib.run j
  | "sched" => Sched.runCase j
  | "queue" => Queue.runCase j
  | "numbers" => Numbers.runCase j
  | "keyword" => Keyword.runCase j
  | "types" => Types.runCase j
  | _ => throw s!"unknown fn misc.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.Misc
