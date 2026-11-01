import PyLean.DiffCore
import PyLean.PyGrammar.Ast

/-! Difftest handler for `Python/ast.c` and `Python/ast_preprocess.c`: `fn` starts with `check.`. -/

namespace PyLean.PyGrammar.Check

open Lean PyLean PyLean.Diff

def handler : Handler := fun _ _ => none

end PyLean.PyGrammar.Check
