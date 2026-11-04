import PyLean.Registry
import PyLean.PyGrammar.RowNames
import PyLean.PyGrammar.Peg.Rules.Stmts
import PyLean.PyGrammar.Peg.Rules.Stmts2
import PyLean.PyGrammar.Peg.Rules.Exprs
import PyLean.PyGrammar.Peg.Rules.Lazy

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
      "exactly when the soft keyword read returned a non-NULL value."
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
