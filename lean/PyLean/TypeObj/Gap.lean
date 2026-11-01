import Lean

/-!
`gap%` marks a branch the model leaves out, as a term of type `M α`. It expands to
`gapAt "File.lean:line"`, so a difftest that reaches the branch reports which one it was
(`PyErr.gap`), and `difftest/typeobj_gaps.py` can tally the sites. A gap is never a Python
outcome: the model stops there, and CPython goes on to do something the model does not say.
-/

namespace PyLean.TypeObj

open Lean Elab Term

/-- `gap%`: this branch is not modelled. See the module docstring. -/
elab "gap%" : term <= expected => do
  let some pos := (← getRef).getPos? | throwError "gap%: no source position"
  let line := ((← getFileMap).toPosition pos).line
  let file := (System.FilePath.mk (← getFileName)).fileName.getD "?"
  let site := Syntax.mkStrLit s!"{file}:{line}"
  let fn := mkIdent `PyLean.TypeObj.gapAt
  elabTermEnsuringType (← `($fn $site)) expected

end PyLean.TypeObj
