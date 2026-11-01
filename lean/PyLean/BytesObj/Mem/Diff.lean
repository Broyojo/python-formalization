import PyLean.DiffCore

/-! Differential-testing handler for memoryview: `fn` names start with `mem.`. -/

namespace PyLean.BytesObj.Mem

open Lean PyLean PyLean.Diff

def handler : Handler := fun _ _ => none

end PyLean.BytesObj.Mem
