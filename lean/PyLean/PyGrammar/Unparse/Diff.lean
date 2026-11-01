import PyLean.DiffCore
import PyLean.PyGrammar.Ast

/-! Difftest handler for `Lib/_ast_unparse.py`, `Lib/ast.py` and `Python/ast_unparse.c`:
`fn` starts with `unparse.`. -/

namespace PyLean.PyGrammar.Unparse

open Lean PyLean PyLean.Diff

def handler : Handler := fun _ _ => none

end PyLean.PyGrammar.Unparse
