import PyLean.PyGrammar.Peg.Interp

/-! `async with (...)` and type comments, run on real text. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- A parse that ends in a tree. -/
def parsedOk : Except PyError Ast → Bool
  | .ok _ => true
  | .error _ => false

/-- `"with"` and `"async "` as bytes. -/
def withBytes : List Nat := [119, 105, 116, 104]
def asyncSpBytes : List Nat := [97, 115, 121, 110, 99, 32]

/-- The four plain alternatives of `with_stmt` (`Grammar/python.gram:423-430`) are the same two
forms with and without `async`, and `async with` adds nothing but the keyword and the version
check. The statement: with type comments on (`ast.parse(..., type_comments=True)`), whatever
follows `with`, if `with ...` parses then `async with ...` parses. -/
def AsyncWithTypeComment : Prop := ∀ rest : List Nat,
  parsedOk (parseStr {} (withBytes ++ rest) .file (typeComments := true)) = true →
  parsedOk (parseStr {} (asyncSpBytes ++ withBytes ++ rest) .file (typeComments := true)) = true

set_option maxRecDepth 100000 in
/-- `with(a as b):#type:c\n x\n` parses, `async with(a as b):#type:c\n x\n` does not: the
parenthesised `async with` alternative (`Grammar/python.gram:427`) has no `tc=[TYPE_COMMENT]`
before its block, so its block fails at the `TYPE_COMMENT` token, the unparenthesised alternative
cannot read `(a as b)` as an expression, and the second pass ends in "invalid syntax". -/
theorem asyncWithTypeComment_refuted : ¬ AsyncWithTypeComment := fun h =>
  absurd (h [40, 97, 32, 97, 115, 32, 98, 41, 58, 35, 116, 121, 112, 101, 58, 99, 10, 32, 120, 10]
    (by decide +kernel)) (by decide +kernel)

end PyLean.PyGrammar.Peg
