import PyLean.DiffCore
import PyLean.UnicodeObj.Basic

/-! Difftest handler for the text slice (`fn` names start with `text_`). -/

namespace PyLean.UnicodeObj.TextDiff

open Lean PyLean PyLean.Diff

def handler : Handler := fun _ _ => none

end PyLean.UnicodeObj.TextDiff
