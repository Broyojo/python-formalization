import PyLean.DiffCore
import PyLean.PyGrammar.Ast

/-! Difftest handler for the PEG interpreter and parser actions: `fn` starts with `peg.`. -/

namespace PyLean.PyGrammar.Peg

open Lean PyLean PyLean.Diff

def handler : Handler := fun _ _ => none

end PyLean.PyGrammar.Peg
