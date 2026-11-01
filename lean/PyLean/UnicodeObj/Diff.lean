import PyLean.UnicodeObj.ObjectDiff
import PyLean.UnicodeObj.CodecDiff
import PyLean.UnicodeObj.FormatDiff
import PyLean.UnicodeObj.TextDiff

/-! Differential-testing handler for `unicodeobj` cases (`"mod": "unicodeobj"`). -/

namespace PyLean.UnicodeObj

open Lean PyLean PyLean.Diff

def handler : Handler := fun fn j =>
  (ObjectDiff.handler fn j) <|> (CodecDiff.handler fn j) <|> (FormatDiff.handler fn j)
    <|> (TextDiff.handler fn j) <|> some (throw s!"unknown fn {fn}")

end PyLean.UnicodeObj
