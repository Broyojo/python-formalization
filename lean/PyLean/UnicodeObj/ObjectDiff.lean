import PyLean.DiffCore
import PyLean.UnicodeObj.Basic

/-! Difftest handler for the object slice (`fn` names start with `obj_`). -/

namespace PyLean.UnicodeObj.ObjectDiff

open Lean PyLean PyLean.Diff

def handler : Handler := fun _ _ => none

end PyLean.UnicodeObj.ObjectDiff
