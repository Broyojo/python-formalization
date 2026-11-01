import PyLean.DiffCore

/-! Difftest handler for TextIOWrapper, IncrementalNewlineDecoder, TextIOBase: `none` for a `fn` this area does not own. -/

namespace PyLean.PyIO

open Lean PyLean PyLean.Diff

def runText (_fn : String) (_j : Json) : Option (Except String Json) := none

end PyLean.PyIO
