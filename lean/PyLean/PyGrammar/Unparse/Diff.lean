import PyLean.DiffCore
import PyLean.PyGrammar.Ast
import PyLean.PyGrammar.Unparse.Python
import PyLean.PyGrammar.Check.Validate

/-! Difftest handler for `Lib/_ast_unparse.py`, `Lib/ast.py` and `Python/ast_unparse.c`:
`fn` starts with `unparse.`. -/

namespace PyLean.PyGrammar.Unparse

open Lean PyLean PyLean.Diff

def handler : Handler := fun fn j =>
  if fn == "unparse.py" then
    some do
      let t ← Ast.ofJ (← field j "tree")
      return encPy toJson (unparseN (Check.astSize t) t)
  else none

end PyLean.PyGrammar.Unparse
