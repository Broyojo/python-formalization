import PyLean.PyGrammar.Peg.Interp

open PyLean.PyGrammar PyLean.PyGrammar.Peg

def isOkB (r : Except Lexer.PyError Ast) : Bool :=
  match r with
  | .ok _ => true
  | .error _ => false

set_option maxRecDepth 100000 in
theorem t1 : isOkB (parseStr {} [120, 10] .file) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem t2 : isOkB (parseStr {} [120, 43, 10] .file) = false := by decide +kernel
