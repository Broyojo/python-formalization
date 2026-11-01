import PyLean.DiffCore

/-! Difftest handler for FileIO, IOBase, RawIOBase, open, text_encoding: `none` for a `fn` this area does not own. -/

namespace PyLean.PyIO

open Lean PyLean PyLean.Diff

def runFile (_fn : String) (_j : Json) : Option (Except String Json) := none

end PyLean.PyIO
