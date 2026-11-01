import PyLean.DiffCore
import PyLean.CoreLibs.CalStat.DiffCal
import PyLean.CoreLibs.CalStat.DiffStat

/-! Differential-testing handler for `corelibs` cases with `"fn": "calstat.<name>"`.
The dispatcher in `CoreLibs/Diff.lean` strips the `calstat.` prefix. -/

namespace PyLean.CoreLibs.CalStat

open Lean PyLean PyLean.Diff

/-- Handlers of total functions return a bare value; give it the `{"ok": v}` shape. -/
def wrapOk (v : Json) : Json :=
  match v.getObjVal? "ok", v.getObjVal? "exc" with
  | .error _, .error _ => Json.mkObj [("ok", v)]
  | _, _ => v

def run (fn : String) (j : Json) : Except String Json :=
  match runCal fn j with
  | some r => wrapOk <$> r
  | none =>
    match runStat fn j with
    | some r => wrapOk <$> r
    | none => throw s!"unknown fn calstat.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.CalStat
