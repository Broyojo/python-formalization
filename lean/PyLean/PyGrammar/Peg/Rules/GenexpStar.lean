import PyLean.PyGrammar.Peg.Rules.Lazy

/-! Unpacking in comprehensions (PEP 798, new in 3.15), run on real text: a starred element of a
generator expression against the same element of a list comprehension. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- `" for x in y"` as bytes. -/
def forXInY : List Nat := [32, 102, 111, 114, 32, 120, 32, 105, 110, 32, 121]

/-- The language reference (`Doc/reference/expressions.rst`, "Generator expressions"): "The
syntax for generator expressions is the same as for list comprehensions, except that they are
enclosed in parentheses instead of brackets", with `comprehension: flexible_expression
for_if_clause+` and `starred_expression: "*" or_expr | expression`. The statement: for every
element text `e`, `(e for x in y)` parses exactly when `[e for x in y]` does. -/
def GenexpLikeListcomp : Prop := ∀ e : List Nat,
  (errMsgOf (parseStr {} ([40] ++ e ++ forXInY ++ [41, 10]) .file)).isNone =
    (errMsgOf (parseStr {} ([91] ++ e ++ forXInY ++ [93, 10]) .file)).isNone

set_option maxRecDepth 100000 in
/-- `e = *a or b`: `genexp`'s element `_tmp_89` ends in `starred_expression` (`'*' expression`,
the call-argument form), so `(*a or b for x in y)` is a `GeneratorExp` of `Starred(a or b)`;
`listcomp` takes `star_named_expression` (`'*' bitwise_or`), so `[*a or b for x in y]` is a
`SyntaxError`. -/
theorem genexpLikeListcomp_refuted : ¬ GenexpLikeListcomp := fun h =>
  absurd (h [42, 97, 32, 111, 114, 32, 98]) (by decide +kernel)

end PyLean.PyGrammar.Peg
