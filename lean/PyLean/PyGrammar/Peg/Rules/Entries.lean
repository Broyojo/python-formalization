import PyLean.Registry
import PyLean.PyGrammar.RowNames
import PyLean.PyGrammar.Peg.Rules.Stmts
import PyLean.PyGrammar.Peg.Rules.Stmts2
import PyLean.PyGrammar.Peg.Rules.Exprs
import PyLean.PyGrammar.Peg.Rules.Lazy
import PyLean.PyGrammar.Peg.Rules.Start
import PyLean.PyGrammar.Peg.Rules.Aug
import PyLean.PyGrammar.Peg.Rules.Compound
import PyLean.PyGrammar.Peg.Rules.Simple
import PyLean.PyGrammar.Peg.Rules.Exprs2

/-! Registry entries for the rule-by-rule statements of `Peg/Rules/`. Each one is about the
generated rule function of one rule, run by `callRule` on `GrammarData.lean`, and says what it
returns for every outcome of the token readers and sub-rules it calls. -/

namespace PyLean.PyGrammar.Peg

open PyLean.Registry

private def scheme : String :=
  "Rule-specific: callRule on this rule's data from any entry state (no error, below MAXSTACK, " ++
  "mark within the tokens, token under the mark read), for every result of the sub-rule calls " ++
  "and token reads, given as equations. Written from the rule text, not the data, so another " ++
  "order of alternatives, a dropped lookahead or another action fails it."

def ruleEntries : List Entry := [
  { id := "pygrammar-rule-keyword-stmts"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_keyword_stmts
    statement := "pass_stmt, break_stmt, continue_stmt: at the keyword token the rule takes " ++
      "exactly it and returns Pass/Break/Continue located at that token; at any other token " ++
      "NULL with the mark unmoved."
    source := "Grammar/python.gram:194-201"
    status := .proven
    prop := ``KeywordStmts
    thm := some ``keywordStmts_proven
    notes := scheme },
  { id := "pygrammar-rule-return-stmt"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_return_stmt
    statement := "return_stmt: at 'return', star_expressions runs on the next token; an error " ++
      "there fails the rule with the mark back, otherwise Return(a) from 'return' to the last " ++
      "token, a = NULL for a bare return. Any other token: NULL."
    source := "Grammar/python.gram:185-186"
    status := .proven
    prop := ``ReturnStmt
    thm := some ``returnStmt_proven
    notes := scheme },
  { id := "pygrammar-rule-raise-stmt"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_raise_stmt
    statement := "raise_stmt, first pass: 'raise a from b' gives Raise(a, b); 'raise a' with no " ++
      "'from' backs up and gives Raise(a', NULL) from the third alternative; 'raise' with no " ++
      "expression gives Raise(NULL, NULL) at the raise token; other tokens NULL."
    source := "Grammar/python.gram:188-192"
    status := .proven
    prop := ``RaiseStmt
    thm := some ``raiseStmt_proven
    notes := scheme ++ " The first-pass hypotheses include callInvalidRules = false on the " ++
      "states the skipped invalid_ alternative is tested in." },
  { id := "pygrammar-rule-raise-stmt-invalid"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_raise_stmt_invalid
    statement := "raise_stmt, second pass: when the first alternative fails, invalid_raise_stmt " ++
      "runs before the plain alternatives, and if it raises, the rule fails with that error."
    source := "Grammar/python.gram:188-192"
    status := .proven
    prop := ``RaiseStmtInvalid
    thm := some ``raiseStmtInvalid_proven
    notes := scheme },
  { id := "pygrammar-rule-invalid-raise-stmt"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_invalid_raise_stmt
    statement := "invalid_raise_stmt: 'raise from' raises \"did you forget an expression " ++
      "between 'raise' and 'from'?\" over raise..from; 'raise a from' raises \"did you forget " ++
      "an expression after 'from'?\" at 'from'; other tokens NULL with no error."
    source := "Grammar/python.gram:1321-1325"
    status := .proven
    prop := ``InvalidRaiseStmt
    thm := some ``invalidRaiseStmt_proven
    notes := scheme ++ " The final state is the one RAISE_ERROR_KNOWN_LOCATION leaves, whose " ++
      "contract is pygrammar-peg-raise-known-location." },
  { id := "pygrammar-rule-factor"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_factor
    statement := "factor (memo): at '+', '-', '~' the unary node over factor parsed one token on; " ++
      "otherwise power's result; memoized at the start mark."
    source := "Grammar/python.gram:856-860"
    status := .proven
    prop := ``Factor
    thm := some ``factor_proven
    notes := scheme ++ " Hypothesis: no memo entry for factor yet at this position; a memo hit " ++
      "is pygrammar-peg-memo-cache." },
  { id := "pygrammar-rule-power"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_power
    statement := "power: 'a ** b' is BinOp(a, Pow, b) with b a factor (right grouping, signed " ++
      "exponent); without '**' the mark goes back and await_primary is the result."
    source := "Grammar/python.gram:862-864"
    status := .proven
    prop := ``Power
    thm := some ``power_proven
    notes := scheme },
  { id := "pygrammar-rule-signed-number"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_signed_number
    statement := "signed_number (3.15): NUMBER as the number token gives it; '+' NUMBER gives " ++
      "UnaryOp(UAdd); '-' NUMBER gives UnaryOp(USub); any other token NULL."
    source := "Grammar/python.gram:556-559"
    status := .proven
    prop := ``SignedNumber
    thm := some ``signedNumber_proven
    notes := scheme },
  { id := "pygrammar-rule-yield-expr"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_yield_expr
    statement := "yield_expr: 'yield from a' gives YieldFrom(a); 'yield' without 'from' backs up " ++
      "and gives Yield(a), a from the optional star_expressions; other tokens NULL."
    source := "Grammar/python.gram:727-729"
    status := .proven
    prop := ``YieldExpr
    thm := some ``yieldExpr_proven
    notes := scheme },
  { id := "pygrammar-rule-yield-stmt"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_yield_stmt
    statement := "yield_stmt: Expr(y) around yield_expr's result; NULL with the mark back if it fails."
    source := "Grammar/python.gram:213"
    status := .proven
    prop := ``YieldStmt
    thm := some ``yieldStmt_proven
    notes := scheme },
  { id := "pygrammar-rule-assert-stmt"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_assert_stmt
    statement := "assert_stmt, first pass: invalid_assert_stmt skipped; 'assert a [, b]' gives " ++
      "Assert(a, b); other tokens NULL."
    source := "Grammar/python.gram:215-217"
    status := .proven
    prop := ``AssertStmt
    thm := some ``assertStmt_proven
    notes := scheme ++ " The optional part is the artificial rule _tmp_16, taken as a sub-call." },
  { id := "pygrammar-rule-import-name"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_import_name
    statement := "import_name: '\"lazy\"? import names' gives Import(names, is_lazy), is_lazy 1 " ++
      "exactly when the soft keyword read returned a non-NULL value; an error in that read, a " ++
      "missing 'import', or a failing dotted_as_names fails the rule with the mark back."
    source := "Grammar/python.gram:227-228"
    status := .proven
    prop := ``ImportName
    thm := some ``importName_proven
    notes := scheme },
  { id := "pygrammar-rule-invalid-import"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_invalid_import
    statement := "invalid_import: 'import a.b from c' raises \"Did you mean to use 'from ... " ++
      "import ...' instead?\" from 'import'; 'import' NEWLINE raises \"Expected one or more " ++
      "names after 'import'\" at the NEWLINE; any other token, 'lazy' included, NULL."
    source := "Grammar/python.gram:1433-1437"
    status := .proven
    prop := ``InvalidImport
    thm := some ``invalidImport_proven
    notes := scheme },
  { id := "pygrammar-rule-del-stmt"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_del_stmt
    statement := "del_stmt, first pass: 'del targets' followed by ';' or NEWLINE (a lookahead, " ++
      "nothing consumed) gives Delete(targets); followed by anything else the rule fails with " ++
      "the mark back although del_targets matched."
    source := "Grammar/python.gram:209-211"
    status := .proven
    prop := ``DelStmt
    thm := some ``delStmt_proven
    notes := scheme },
  { id := "pygrammar-rule-augassign"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_augassign
    statement := "augassign: each of the 13 augmented assignment tokens gives " ++
      "_PyPegen_augoperator(p, Op) for its operator (+= Add ... //= FloorDiv) and is taken; '@=' " ++
      "with feature_version < 5 fails CHECK_VERSION with the exception for \"The '@' operator " ++
      "is only supported in Python 3.5 and greater\"; any other token NULL."
    source := "Grammar/python.gram:170-183"
    status := .proven
    prop := ``AugAssign
    thm := some ``augAssign_proven
    notes := scheme },
  { id := "pygrammar-rule-del-stmt-invalid"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_del_stmt_invalid
    statement := "del_stmt, second pass: when the first alternative fails at its lookahead, " ++
      "invalid_del_stmt runs from the start mark and the rule ends in its outcome."
    source := "Grammar/python.gram:209-211"
    status := .proven
    prop := ``DelStmtInvalid
    thm := some ``delStmtInvalid_proven
    notes := scheme },
  { id := "pygrammar-rule-assert-stmt-invalid"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_assert_stmt_invalid
    statement := "assert_stmt, second pass: invalid_assert_stmt (first in 3.15) runs before " ++
      "anything else; if it raises, the rule fails with its error and the assert alternative " ++
      "is not tried; if it returns NULL with no error, 'assert a [, b]' gives Assert(a, b)."
    source := "Grammar/python.gram:215-217"
    status := .proven
    prop := ``AssertStmtInvalid
    thm := some ``assertStmtInvalid_proven
    notes := scheme },
  { id := "pygrammar-rule-for-stmt"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_for_stmt
    statement := "for_stmt: 'for t in ex: body [else]' gives For(t, ex, b, el, type_comment); a " ++
      "failure of star_expressions after 'in' hits the cut: NULL with the mark back, and in the " ++
      "second pass invalid_for_target, the last alternative, is not run."
    source := "Grammar/python.gram:410-416"
    status := .proven
    prop := ``ForStmt
    thm := some ``forStmt_proven
    notes := scheme },
  { id := "pygrammar-rule-compound-stmt"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_compound_stmt
    statement := "compound_stmt: lookahead dispatch in order: function_def behind def/@/async; if_stmt at " ++
      "'if'; at a decorator a failing function_def falls through to class_def; with every " ++
      "lookahead failing, match_stmt decides."
    source := "Grammar/python.gram:137-145"
    status := .proven
    prop := ``CompoundStmt
    thm := some ``compoundStmt_proven
    notes := scheme ++ " Lookaheads are the rule calls _tmp_4 to _tmp_7 and token reads." },
  { id := "pygrammar-rule-simple-stmt"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_simple_stmt
    statement := "simple_stmt (memo): assignment first and winning when it succeeds; then, past the type " ++
      "and import lookaheads, Expr(star_expressions); only then keyword statements (return_stmt " ++
      "behind &'return', pass_stmt behind &'pass' after the raise lookahead fails); memoized."
    source := "Grammar/python.gram:121-135"
    status := .proven
    prop := ``SimpleStmt
    thm := some ``simpleStmt_proven
    notes := scheme ++ " Hypothesis: no memo entry yet at the position." },
  { id := "pygrammar-rule-global-nonlocal"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_global_nonlocal
    statement := "global_stmt, nonlocal_stmt: at the keyword, the comma-separated names become " ++
      "Global/Nonlocal of their ids; a failure of the names gives NULL with the mark back; " ++
      "other tokens NULL."
    source := "Grammar/python.gram:203-207"
    status := .proven
    prop := ``GlobalNonlocal
    thm := some ``globalNonlocal_proven
    notes := scheme },
  { id := "pygrammar-rule-inversion"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_inversion
    statement := "inversion (memo): 'not' a gives UnaryOp(Not, a) over inversion one token on; any " ++
      "other token gives comparison's result; memoized."
    source := "Grammar/python.gram:777-779"
    status := .proven
    prop := ``Inversion
    thm := some ``inversion_proven
    notes := scheme },
  { id := "pygrammar-rule-comparison"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_comparison
    statement := "comparison: bitwise_or followed by one or more comparison pairs gives one Compare " ++
      "node with the operators and right operands in order; without a pair the mark goes back " ++
      "and bitwise_or parsed again is the result."
    source := "Grammar/python.gram:784-791"
    status := .proven
    prop := ``Comparison
    thm := some ``comparison_proven
    notes := scheme },
  { id := "pygrammar-rule-await-primary"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_await_primary
    statement := "await_primary (memo): 'await' primary gives Await(a) with feature_version >= 5 and " ++
      "fails with an error below; any other token gives primary's result; memoized."
    source := "Grammar/python.gram:871-873"
    status := .proven
    prop := ``AwaitPrimary
    thm := some ``awaitPrimary_proven
    notes := scheme },
  { id := "pygrammar-rule-assignment-aug"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_assignment_aug
    statement := "assignment, 'x op= v' (earlier alternatives failing): AugAssign(x, op, v); a " ++
      "failing annotated_rhs after the operator hits the cut: NULL with the mark back in either " ++
      "pass, invalid_assignment not run."
    source := "Grammar/python.gram:151-166"
    status := .proven
    prop := ``AssignmentAug
    thm := some ``assignmentAug_proven
    notes := scheme },
  { id := "pygrammar-rule-assignment-ann-plain"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_assignment_ann_plain
    statement := "assignment: 'x: T [= v]' gives AnnAssign(x in Store, T, v, 1) and '(x): T' " ++
      "AnnAssign(x, T, v, 0), both under CHECK_VERSION(6); 'targets = v' with no further '=' " ++
      "(negative lookahead) gives Assign(targets, v, type_comment)."
    source := "Grammar/python.gram:151-166"
    status := .proven
    prop := ``AssignmentAnnPlain
    thm := some ``assignmentAnnPlain_proven
    notes := scheme },
  { id := "pygrammar-rule-assignment-invalid"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_assignment_invalid
    statement := "assignment, second pass: with every alternative failing before a cut, " ++
      "invalid_assignment runs from the start mark and its outcome is the rule's."
    source := "Grammar/python.gram:151-166"
    status := .proven
    prop := ``AssignmentInvalid
    thm := some ``assignmentInvalid_proven
    notes := scheme },
  { id := "pygrammar-rule-file"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_file
    statement := "file: after the optional statements the next token must be ENDMARKER, giving " ++
      "Module(a, type_ignores); another token, or an error in statements, fails the rule."
    source := "Grammar/python.gram:89"
    status := .proven
    prop := ``FileRule
    thm := some ``fileRule_proven
    notes := scheme },
  { id := "pygrammar-rule-eval"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_eval
    statement := "eval: expressions, newlines, then ENDMARKER gives Expression(a); without " ++
      "ENDMARKER the rule fails."
    source := "Grammar/python.gram:91"
    status := .proven
    prop := ``EvalRule
    thm := some ``evalRule_proven
    notes := scheme },
  { id := "pygrammar-rule-interactive"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_interactive
    statement := "interactive: Interactive(a) around statement_newline, NULL if it fails."
    source := "Grammar/python.gram:90"
    status := .proven
    prop := ``InteractiveRule
    thm := some ``interactiveRule_proven
    notes := scheme },
  { id := "pygrammar-rule-statement"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_statement
    statement := "statement: compound_stmt first, its one-statement sequence through " ++
      "_PyPegen_register_stmts; only if it fails, simple_stmts from the same mark."
    source := "Grammar/python.gram:99-103"
    status := .proven
    prop := ``StatementRule
    thm := some ``statementRule_proven
    notes := scheme },
  { id := "pygrammar-rule-lazy-import-diagnosed"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_lazy_import_diagnosed
    statement := "Whatever follows, when 'import ...' gets \"Expected one or more names after " ++
      "'import'\", so does 'lazy import ...'."
    source := "the implementation against itself: import_name takes \"lazy\"?, invalid_import does not"
    status := .refuted
    prop := ``LazyImportDiagnosed
    thm := some ``lazyImportDiagnosed_refuted
    bug := some "pygrammar-lazy-import-diagnostics"
    notes := "Counterexample run in the kernel: 'lazy import\\n' gives 'invalid syntax'." }
]

end PyLean.PyGrammar.Peg
