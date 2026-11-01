import PyLean.DiffCore

/-! Difftest handler for BufferedReader/Writer/Random/RWPair, BufferedIOBase: `none` for a `fn` this area does not own. -/

namespace PyLean.PyIO

open Lean PyLean PyLean.Diff

def runBuffered (_fn : String) (_j : Json) : Option (Except String Json) := none

end PyLean.PyIO
