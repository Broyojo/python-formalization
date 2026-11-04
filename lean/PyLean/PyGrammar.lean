import PyLean.Registry
import PyLean.PyGrammar.Diff
import PyLean.PyGrammar.Lexer.Entries
import PyLean.PyGrammar.Unparse.Entries
import PyLean.PyGrammar.Check.Entries
import PyLean.PyGrammar.Peg.Entries

/-!
Syntax: `Grammar/python.gram`, `Parser/lexer/`, `Parser/tokenizer/`, `Parser/string_parser.c`, `Parser/action_helpers.c`, `Lib/tokenize.py`, `Lib/ast.py`, CPython 3.15.2.

Four parts share `PyGrammar/Ast.lean`, each with its own entries list:
`Lexer` (tokenizer, `Lib/tokenize.py`), `Peg` (grammar as data, interpreter, actions),
`Unparse` (`Lib/_ast_unparse.py`, `Lib/ast.py`, `Python/ast_unparse.c`),
`Check` (`Python/ast.c`, `Python/ast_preprocess.c`). `Peg/Rules/` states, rule by rule, what
the generated rule functions return.
-/

namespace PyLean.PyGrammar

open PyLean.Registry

def entries : List Entry :=
  Lexer.entries ++ Peg.entries ++ Unparse.entries ++ Check.entries

end PyLean.PyGrammar
