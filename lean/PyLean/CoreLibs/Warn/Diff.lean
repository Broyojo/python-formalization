import PyLean.CoreLibs.Warn.DiffWe
import PyLean.CoreLibs.Warn.DiffOps
import PyLean.CoreLibs.Warn.DiffCall
import PyLean.CoreLibs.Warn.DiffCtx

/-! The `warn` area's difftest handler: `warn_explicit` cases (`DiffWe`), filters-list and `-W`
cases (`DiffOps`), `warnings.warn` cases (`DiffCall`) and `catch_warnings` cases (`DiffCtx`). -/

namespace PyLean.CoreLibs.Warn

open PyLean.Diff

def handler : Handler := fun fn j =>
  (weHandler fn j).orElse fun _ => (opsHandler fn j).orElse fun _ =>
    (callHandler fn j).orElse fun _ => ctxHandler fn j

end PyLean.CoreLibs.Warn
