import PyLean.DiffCore
import PyLean.UnicodeObj.Basic

/-! Difftest handler for the codecs slice (`fn` names start with `codec_`). -/

namespace PyLean.UnicodeObj.CodecDiff

open Lean PyLean PyLean.Diff

def handler : Handler := fun _ _ => none

end PyLean.UnicodeObj.CodecDiff
