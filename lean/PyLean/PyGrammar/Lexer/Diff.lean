import PyLean.DiffCore
import PyLean.PyGrammar.Ast

/-! Difftest handler for the lexer and tokenize parts: `fn` starts with `lex.`. -/

namespace PyLean.PyGrammar.Lexer

open Lean PyLean PyLean.Diff

def handler : Handler := fun _ _ => none

end PyLean.PyGrammar.Lexer
