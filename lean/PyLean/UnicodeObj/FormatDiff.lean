import PyLean.DiffCore
import PyLean.UnicodeObj.Basic

/-! Difftest handler for the formatting slice (`fn` names start with `fmt_`). -/

namespace PyLean.UnicodeObj.FormatDiff

open Lean PyLean PyLean.Diff

def handler : Handler := fun _ _ => none

end PyLean.UnicodeObj.FormatDiff
