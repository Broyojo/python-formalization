import PyLean.DiffCore
import PyLean.PyGrammar.Lexer.Diff
import PyLean.PyGrammar.Unparse.Diff
import PyLean.PyGrammar.Check.Diff
import PyLean.PyGrammar.Peg.Diff

/-! Differential-testing handler for `pygrammar` cases (`"mod": "pygrammar"`).
A case's `fn` is `<part>.<name>`; each part has its own handler. -/

namespace PyLean.PyGrammar

open Lean PyLean PyLean.Diff

def run (fn : String) (j : Json) : Except String Json :=
  match Lexer.handler fn j <|> Unparse.handler fn j <|> Check.handler fn j <|> Peg.handler fn j with
  | some r => r
  | none => throw s!"unknown fn {fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.PyGrammar
