import PyLean.Registry
import PyLean.PyGrammar.RowNames
import PyLean.PyGrammar.Check.FoldProps
import PyLean.PyGrammar.Check.NullSites
import PyLean.PyGrammar.Check.TableCovers

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
    pyFns := Rows.check_no_null_deref
    statement := "On no tree does _PyAST_Validate dereference NULL."
    source := "invariant: no crash"
    status := .refuted
    prop := ``ValidateNoNullDeref
    thm := some ``validateNoNullDeref_refuted
    bug := some "pygrammar-check-none-in-list-segfault" },
  { id := "pygrammar-check-null-sites"
    pyFile := "Python/ast.c"
    pyFns := Rows.check_null_sites
    statement := "_PyAST_Validate dereferences NULL on a tree only if a None sits at one of its " ++
      "unchecked fields: Try or TryStar handlers, the patterns of MatchSequence, MatchOr, " ++
      "MatchMapping or MatchClass, MatchMapping keys, MatchClass kwd_attrs, or a required field."
    source := "invariant: no crash, exact form of pygrammar-check-none-in-list-segfault"
    status := .proven
    prop := ``NullSites
    thm := some ``nullSites_proven
    notes := "One direction: a None there can crash; the refutation shows one does. Proved " ++
      "over all 24 validators, so it also says every other path is free of this crash." },
  { id := "pygrammar-check-rejects"
    pyFile := "Python/ast.c"
    pyFns := Rows.check_rejects
    statement := "_PyAST_Validate accepts a tree only if every position of it satisfies the table " ++
      "`spec`: node rules (BoolOp arity, equal lengths in Dict and Compare, nonempty bodies and " ++
      "generators, Try shape, literal pattern shapes, positions, context, names), a None only " ++
      "where a list allows one, and the same for each child, for every tree."
    source := "invariant: the checks of Python/ast.c, each stated as a condition"
    status := .proven
    prop := ``ValidateRejects
    thm := some ``validateRejects_proven
    notes := "One direction: accepted implies in the table. That the table holds no rule the " ++
      "validators lack follows from this; that it omits none is checked for children by " ++
      "pygrammar-check-table-covers, and for node rules only by reading the table. Which check " ++
      "fails first and its message are the difftest's. expr_context_name and validate_constant " ++
      "are not credited: the first is message text, the second is modelled as always passing." },
  { id := "pygrammar-check-table-covers"
    pyFile := "Python/ast.c"
    pyFns := Rows.check_table_covers
    statement := "Every present child that Parser/Python.asdl gives a node of the right arity is " ++
      "listed in its row of the validator table, except NamedExpr.target."
    source := "Parser/Python.asdl, through the generated Ctor.fields"
    status := .proven
    prop := ``TableCovers
    thm := some ``tableCovers_proven
    notes := "A fact about the table of pygrammar-check-rejects, so it credits no row. The one " ++
      "exception is the refutation pygrammar-check-names-always." },
  { id := "pygrammar-check-names-always"
    pyFile := "Python/ast.c"
    pyFns := Rows.check_names_always
    statement := "A name refused as a plain expression is refused as a NamedExpr target."
    source := "the assert in Python/codegen.c:3189 (codegen_nameop)"
    status := .refuted
    prop := ``NamesAlwaysChecked
    thm := some ``namesAlwaysChecked_refuted
    bug := some "pygrammar-check-namedexpr-target" },
  { id := "pygrammar-check-fold-reaches"
    pyFile := "Python/ast_preprocess.c"
    pyFns := Rows.check_fold_reaches
    statement := "After folding, no Name('__debug__', Load) is left in any expression or pattern " ++
      "field of the module, except annotations under the __future__ import."
    source := "Python/ast_preprocess.c astfold_pattern 'We still recurse into all " ++
      "subexpressions and subpatterns anyway'"
    status := .refuted
    prop := ``FoldReachesAll
    thm := some ``foldReachesAll_refuted
    bug := some "pygrammar-check-debug-in-pattern" },
  { id := "pygrammar-check-fold-reaches-narrow"
    pyFile := "Python/ast_preprocess.c"
    pyFns := Rows.check_fold_reaches_narrow
    statement := "With MatchValue values and MatchMapping keys set aside, folding reaches every " ++
      "node-typed field of Python.asdl: no Name('__debug__', Load) survives anywhere else."
    source := "the implementation against Parser/Python.asdl"
    status := .proven
    prop := ``FoldReachesNames
    thm := some ``foldReachesNames_proven
    notes := "Depends on each row of visits: dropping a field from a row breaks coverOK." },
  { id := "pygrammar-check-fold-docstring"
    pyFile := "Python/ast_preprocess.c"
    pyFns := Rows.check_fold_docstring
    statement := "Below optimize 2 folding keeps a body's docstring as it is and never creates " ++
      "one; at optimize 2 a folded body has no docstring at all."
    source := "Python/ast_preprocess.c astfold_body 'so that it is not mistaken for a docstring'"
    status := .proven
    prop := ``FoldKeepsDocstring
    thm := some ``foldKeepsDocstring_proven },
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
    pyFns := []
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
