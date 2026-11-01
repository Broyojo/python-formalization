import PyLean.DiffCore

/-! Differential-testing handler for bytes and bytearray: `fn` names start with `bytes.` or
`bytearray.`. -/

namespace PyLean.BytesObj.Bytes

open Lean PyLean PyLean.Diff

def handler : Handler := fun _ _ => none

end PyLean.BytesObj.Bytes
