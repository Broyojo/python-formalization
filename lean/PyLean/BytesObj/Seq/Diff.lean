import PyLean.DiffCore

/-! Differential-testing handler for tuple and list: `fn` names start with `tuple.` or `list.`. -/

namespace PyLean.BytesObj.Seq

open Lean PyLean PyLean.Diff

def handler : Handler := fun _ _ => none

end PyLean.BytesObj.Seq
