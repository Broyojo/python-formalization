import PyLean.PyGrammar.Peg.Rules.Lazy

/-! `invalid_dotted_as_name` and `invalid_import_from_as_name` (`Grammar/python.gram:1438-1445`),
run on real text: the "cannot use %s as import target" message for a plain name. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- `"import a as b"` and `"from x import a as b"` as bytes. -/
def importAsBytes : List Nat := importBytes ++ [32, 97, 32, 97, 115, 32, 98]
def fromImportAsBytes : List Nat := [102, 114, 111, 109, 32, 120, 32] ++ importAsBytes

/-- A plain name is a valid `as` target (`import a as b` parses), so whatever follows it, the
error is never "cannot use name as import target". Source: the implementation against itself:
`dotted_as_name` takes `'as' NAME`, and `invalid_dotted_as_name` (`Grammar/python.gram:1438-1441`)
raises `"cannot use %s as import target"` with `_PyPegen_get_expr_name(a)`, which says "name" for a
`Name`. -/
def DottedAsNameNameTarget : Prop := ∀ rest : List Nat,
  errMsgOf (parseStr {} (importAsBytes ++ rest) .file) ≠ some "cannot use name as import target"

set_option maxRecDepth 100000 in
/-- `import a as b c\n`: the lookahead `!(NAME (',' | ')' | ';' | NEWLINE))` holds because `b` is
followed by `c`, `expression` takes `b` alone, and the action names it. -/
theorem dottedAsNameNameTarget_refuted : ¬ DottedAsNameNameTarget := fun h =>
  h [32, 99, 10] (by decide +kernel)

/-- As `DottedAsNameNameTarget`, for `from x import a as b` and `invalid_import_from_as_name`
(`Grammar/python.gram:1442-1445`). -/
def ImportFromAsNameNameTarget : Prop := ∀ rest : List Nat,
  errMsgOf (parseStr {} (fromImportAsBytes ++ rest) .file) ≠ some "cannot use name as import target"

set_option maxRecDepth 100000 in
/-- `from x import a as b c\n`. -/
theorem importFromAsNameNameTarget_refuted : ¬ ImportFromAsNameNameTarget := fun h =>
  h [32, 99, 10] (by decide +kernel)

/-- `import a as (c)\n`: a one-letter name in parentheses after `as`, then `NEWLINE`. The target is
wrong because of the parentheses, so the message never says that the name itself cannot be an
import target. This is the case the fix proposed in gh-146493 still reaches: its rule keeps
`!(NAME (',' | ')' | ';' | NEWLINE)) a=expression` and adds `(',' | ')' | ';' | NEWLINE)` after
the expression, and here `(` is not a `NAME`, `expression` gives the `Name` inside, and
`NEWLINE` follows. -/
def ParenNameTarget : Prop := ∀ c : Nat, 97 ≤ c → c ≤ 122 →
  errMsgOf (parseStr {} (importBytes ++ [32, 97, 32, 97, 115, 32, 40, c, 41, 10]) .file) ≠
    some "cannot use name as import target"

set_option maxRecDepth 100000 in
/-- `import a as (b)\n`. -/
theorem parenNameTarget_refuted : ¬ ParenNameTarget := fun h =>
  h 98 (by decide) (by decide) (by decide +kernel)

end PyLean.PyGrammar.Peg
