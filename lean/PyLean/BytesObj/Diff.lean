import PyLean.DiffCore
import PyLean.BytesObj.Seq.Diff
import PyLean.BytesObj.Bytes.Diff
import PyLean.BytesObj.Bytes.HeapDiff
import PyLean.BytesObj.Mem.Diff

/-! Differential-testing handler for `bytesobj` cases (`"mod": "bytesobj"`).
Each family has its own sub-handler; a handler returns `none` for a `fn` it does
not know. -/

namespace PyLean.BytesObj

open Lean PyLean PyLean.Diff

def handler : Handler := fun fn j =>
  (Seq.handler fn j) <|> (Bytes.handler fn j) <|> (Bytes.heapHandler fn j) <|> (Mem.handler fn j)

end PyLean.BytesObj
