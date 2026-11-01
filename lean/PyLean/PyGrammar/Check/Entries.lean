import PyLean.Registry
import PyLean.PyGrammar.RowNames
import PyLean.PyGrammar.Check.Props

/-! Registry entries for the `Check` part of `PyGrammar`. -/

namespace PyLean.PyGrammar.Check

open PyLean.Registry

def entries : List Entry := [
  { id := "pygrammar-check-try-twin"
    pyFile := "Python/ast.c"
    pyFns := Rows.check_try_twin
    statement := "validate accepts the same handlers for Try and TryStar: for every handler " ++
      "tree, the two copies of the case in validate_stmt agree."
    source := "the implementation against itself"
    status := .refuted
    prop := ``TryHandlersTwin
    thm := some ``tryHandlersTwin_refuted
    bug := some "pygrammar-check-trystar-handlers" },
  { id := "pygrammar-check-no-null-deref"
    pyFile := "Python/ast.c"
    pyFns := ["validate_stmt", "validate_pattern", "validate_patterns"]
    statement := "On no tree does _PyAST_Validate dereference NULL."
    source := "invariant: no crash"
    status := .refuted
    prop := ``ValidateNoNullDeref
    thm := some ``validateNoNullDeref_refuted
    bug := some "pygrammar-check-none-in-list-segfault" },
  { id := "pygrammar-check-names-always"
    pyFile := "Python/ast.c"
    pyFns := Rows.check_names_always
    statement := "A name refused as a plain expression is refused as a NamedExpr target."
    source := "the assert in Python/codegen.c:3189 (codegen_nameop)"
    status := .refuted
    prop := ``NamesAlwaysChecked
    thm := some ``namesAlwaysChecked_refuted
    bug := some "pygrammar-check-namedexpr-target" },
  { id := "pygrammar-check-validate-name"
    pyFile := "Python/ast.c"
    pyFns := Rows.check_validate_name
    statement := "validate_name refuses exactly None, True and False."
    source := "invariant"
    status := .proven
    prop := ``ValidateNameExact
    thm := some ``validateNameExact_proven },
  { id := "pygrammar-check-positions"
    pyFile := "Python/ast.c"
    pyFns := ["_PyAST_Validate"]
    statement := "For non-negative starts, VALIDATE_POSITIONS accepts exactly ordered ranges."
    source := "invariant"
    status := .proven
    prop := ``ValidatePositionsOrdered
    thm := some ``validatePositionsOrdered_proven },
  { id := "pygrammar-check-nonempty"
    pyFile := "Python/ast.c"
    pyFns := Rows.check_nonempty
    statement := "_validate_nonempty_seq accepts exactly non-empty sequences."
    source := "invariant"
    status := .proven
    prop := ``NonemptySeqExact
    thm := some ``nonemptySeqExact_proven },
  { id := "pygrammar-check-docstring-body"
    pyFile := "Python/ast_preprocess.c"
    pyFns := Rows.check_docstring_body
    statement := "Removing a docstring leaves a non-empty body, for a located first statement."
    source := "Python/ast_preprocess.c remove_docstring comment"
    status := .proven
    prop := ``DocstringRemovalKeepsBody
    thm := some ``docstringRemovalKeepsBody_proven },
  { id := "pygrammar-check-fold-value"
    pyFile := "Python/ast_preprocess.c"
    pyFns := Rows.check_fold_value
    statement := "Constant folding of match literals gives the constant PyNumber_Negative, " ++
      "PyNumber_Add or PyNumber_Subtract gives, at the node's location."
    source := "invariant: constant folding preserves value"
    status := .proven
    prop := ``FoldPreservesValue
    thm := some ``foldPreservesValue_proven },
  { id := "pygrammar-check-format-args"
    pyFile := "Python/ast_preprocess.c"
    pyFns := Rows.check_format_args
    statement := "The '%' fold puts each tuple item in exactly one FormattedValue."
    source := "invariant"
    status := .proven
    prop := ``FormatUsesEveryArg
    thm := some ``formatUsesEveryArg_proven },
  { id := "pygrammar-check-syntax-only-identity"
    pyFile := "Python/ast_preprocess.c"
    pyFns := Rows.check_syntax_only_identity
    statement := "With syntax_check_only and optimize < 2, the fold leaves every tree unchanged."
    source := "Python/compile.c _PyCompile_AstPreprocess no_const_folding"
    status := .proven
    prop := ``SyntaxOnlyIdentity
    thm := some ``syntaxOnlyIdentity_proven }
]

end PyLean.PyGrammar.Check
