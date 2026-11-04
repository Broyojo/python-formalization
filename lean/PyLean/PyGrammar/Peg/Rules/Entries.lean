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
import PyLean.PyGrammar.Peg.Rules.Exprs3
import PyLean.PyGrammar.Peg.Rules.Blocks
import PyLean.PyGrammar.Peg.Rules.Try
import PyLean.PyGrammar.Peg.Rules.Except
import PyLean.PyGrammar.Peg.Rules.With
import PyLean.PyGrammar.Peg.Rules.Defs
import PyLean.PyGrammar.Peg.Rules.AsyncWith
import PyLean.PyGrammar.Peg.Rules.LeftRec
import PyLean.PyGrammar.Peg.Rules.LeftRec2
import PyLean.PyGrammar.Peg.Rules.InvalidAssert
import PyLean.PyGrammar.Peg.Rules.Match
import PyLean.PyGrammar.Peg.Rules.Decorators
import PyLean.PyGrammar.Peg.Rules.Primary
import PyLean.PyGrammar.Peg.Rules.TPrimary
import PyLean.PyGrammar.Peg.Rules.Atom
import PyLean.PyGrammar.Peg.Rules.Targets
import PyLean.PyGrammar.Peg.Rules.Targets2
import PyLean.PyGrammar.Peg.Rules.Imports
import PyLean.PyGrammar.Peg.Rules.Patterns
import PyLean.PyGrammar.Peg.Rules.InvalidTargets
import PyLean.PyGrammar.Peg.Rules.SumCompose
import PyLean.PyGrammar.Peg.Rules.AsTarget
import PyLean.PyGrammar.Peg.Rules.AsTarget2
import PyLean.PyGrammar.Peg.Rules.Entries2
import PyLean.PyGrammar.Peg.Rules.Entries3

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

private def LR : String :=
  "Left-recursive leader: GrowSeedChain is the seed loop of the generated leader (_PyPegen_update_memo, then the _raw function, then the growth test), proven by induction on the rounds; the round theorem unfolds the _raw function on this rule's data from any state whose memo holds the seed, the recursive call returning the seed through _PyPegen_is_memoized. Hypotheses: the token at the start mark is read, the seed ends within the tokens read, below MAXSTACK; and for the whole rule, no memo entry yet at the start."

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
    statement := "for_stmt: For(...) for 'for'; AsyncFor under CHECK_VERSION(5) for 'async for' " ++
      "(with the error message below 5); NULL at any other token; the cut after 'in' ends the " ++
      "rule in both passes; second pass: invalid_for_stmt's error ends the rule, and a failure " ++
      "before the cut lets invalid_for_target decide."
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
    notes := scheme ++ " Lookaheads are the rule calls _tmp_6 to _tmp_9 and token reads." },
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
  { id := "pygrammar-rule-import-stmt"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_import_stmt
    statement := "import_stmt (memo): first pass import_name before import_from; second pass " ++
      "invalid_import first, its error ending the rule unmemoized, its NULL leading to " ++
      "import_name; results memoized."
    source := "Grammar/python.gram:219-222"
    status := .proven
    prop := ``ImportStmt
    thm := some ``importStmt_proven
    notes := scheme ++ " Hypothesis: no memo entry yet at the position." },
  { id := "pygrammar-rule-import-from"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_import_from
    statement := "import_from: '[lazy] from [dots] mod import targets' is " ++
      "_PyPegen_checked_from_import's result; '[lazy] from dots import targets' backs up and " ++
      "gives ImportFrom(NULL, targets, dots counted, is_lazy); second pass: an error from " ++
      "invalid_import_from ends the rule."
    source := "Grammar/python.gram:231-236"
    status := .proven
    prop := ``ImportFrom
    thm := some ``importFrom_proven
    notes := scheme ++ " _PyPegen_checked_from_import itself is pygrammar-peg-checked-from-import." },
  { id := "pygrammar-rule-assignment-more"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_assignment_more
    statement := "assignment: CHECK_VERSION(6) failing for both annotated forms, with their " ++
      "messages; the !'=' lookahead failing (x = v = w) makes the Assign alternative fail; second " ++
      "pass after a NAME (f() = 1): invalid_assignment decides."
    source := "Grammar/python.gram:151-166"
    status := .proven
    prop := ``AssignmentMore
    thm := some ``assignmentMore_proven
    notes := scheme },
  { id := "pygrammar-rule-compound-stmt-more"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_compound_stmt_more
    statement := "compound_stmt: class_def, with_stmt, for_stmt (for 'for', and for 'async' after " ++
      "function_def and with_stmt fail), try_stmt and while_stmt, each behind its lookahead with " ++
      "the earlier ones failing."
    source := "Grammar/python.gram:137-145"
    status := .proven
    prop := ``CompoundStmtMore
    thm := some ``compoundStmtMore_proven
    notes := scheme },
  { id := "pygrammar-rule-simple-stmt-more"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_simple_stmt_more
    statement := "simple_stmt: type_alias behind \"type\"; import_stmt behind (import|from|lazy) " ++
      "before star_expressions; and each of the ten keyword statements behind its keyword, in " ++
      "grammar order, when the earlier keyword lookaheads fail; memoized."
    source := "Grammar/python.gram:121-135"
    status := .proven
    prop := ``SimpleStmtMore
    thm := some ``simpleStmtMore_proven
    notes := scheme },
  { id := "pygrammar-rule-del-stmt-targets"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_del_stmt_targets
    statement := "del_stmt: del_targets failing after 'del' gives NULL with the mark back in the " ++
      "first pass, and in the second pass invalid_del_stmt's outcome."
    source := "Grammar/python.gram:209-211"
    status := .proven
    prop := ``DelStmtTargets
    thm := some ``delStmtTargets_proven
    notes := scheme },
  { id := "pygrammar-rule-while-stmt"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_while_stmt
    statement := "while_stmt: While(a, b, else) after 'while a: b'; NULL at any other token; second " ++
      "pass: invalid_while_stmt's error ends the rule, its NULL leads on to the while alternative."
    source := "Grammar/python.gram:403-405"
    status := .proven
    prop := ``WhileStmt
    thm := some ``whileStmt_proven
    notes := scheme },
  { id := "pygrammar-rule-if-stmt"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_if_stmt
    statement := "if_stmt: If(a, b, [elif]) with an elif chain; without one, backs up and gives If(a, b, " ++
      "else); NULL at any other token; second pass: invalid_if_stmt first, its error ending the rule."
    source := "Grammar/python.gram:386-390"
    status := .proven
    prop := ``IfStmt
    thm := some ``ifStmt_proven
    notes := scheme },
  { id := "pygrammar-rule-else-block"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_else_block
    statement := "else_block: 'else: b' gives b; after 'else' the forced ':' either matches or fails " ++
      "the rule in its error state; NULL at any other token; second pass: invalid_else_stmt's " ++
      "error ends the rule."
    source := "Grammar/python.gram:396-398"
    status := .proven
    prop := ``ElseBlock
    thm := some ``elseBlock_proven
    notes := scheme },
  { id := "pygrammar-rule-block"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_block
    statement := "block (memo): NEWLINE INDENT statements DEDENT gives the statements; another first " ++
      "token gives simple_stmts' result; second pass: NEWLINE without INDENT and no simple_stmts " ++
      "leaves invalid_block to decide; memoized."
    source := "Grammar/python.gram:266-269"
    status := .proven
    prop := ``Block
    thm := some ``block_proven
    notes := scheme ++ " Hypothesis: no memo entry yet at the position." },
  { id := "pygrammar-rule-func-type"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_func_type
    statement := "func_type: '(' [types] ')' '->' expression NEWLINE* ENDMARKER gives " ++
      "FunctionType(types, returns); without ENDMARKER, or at any token but '(', NULL."
    source := "Grammar/python.gram:92"
    status := .proven
    prop := ``FuncTypeRule
    thm := some ``funcTypeRule_proven
    notes := scheme },
  { id := "pygrammar-rule-expression"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_expression
    statement := "expression (memo): first pass if_expression, then disjunction, then lambdef; second " ++
      "pass the three invalid_ rules first, an error from any ending the rule unmemoized."
    source := "Grammar/python.gram:716-722"
    status := .proven
    prop := ``ExpressionRule
    thm := some ``expressionRule_proven
    notes := scheme ++ " Hypothesis: no memo entry yet at the position." },
  { id := "pygrammar-rule-star-expressions"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_star_expressions
    statement := "star_expressions: 'a, b, ...' gives a Load Tuple of all elements; 'a,' backs up and " ++
      "gives a one-element Tuple; with no comma, backs up again and gives the star_expression."
    source := "Grammar/python.gram:731-737"
    status := .proven
    prop := ``StarExpressions
    thm := some ``starExpressions_proven
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
  { id := "pygrammar-rule-elif-stmt"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_elif_stmt
    statement := "elif_stmt: If(a, b, [elif]) with a further elif; without one, backs up and gives " ++
      "If(a, b, else); NULL at any other token; second pass: invalid_elif_stmt first, its error " ++
      "ending the rule, its NULL leading to the nested alternative."
    source := "Grammar/python.gram:391-395"
    status := .proven
    prop := ``ElifStmt
    thm := some ``elifStmt_proven
    notes := scheme },
  { id := "pygrammar-rule-finally-block"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_finally_block
    statement := "finally_block: 'finally: a' gives a; after 'finally' the forced ':' either matches " ++
      "or ends the rule with its error set; NULL at any other token; second pass: " ++
      "invalid_finally_stmt's error ends the rule, its NULL leads to the plain alternative."
    source := "Grammar/python.gram:480-482"
    status := .proven
    prop := ``FinallyBlock
    thm := some ``finallyBlock_proven
    notes := scheme },
  { id := "pygrammar-rule-try-stmt"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_try_stmt
    statement := "try_stmt: 'try: b finally: f' gives Try(b, [], [], f); with no finally, backs up " ++
      "for Try(b, handlers, orelse, final); with no except either, TryStar under " ++
      "CHECK_VERSION(11) with the exact message below 11; the forced ':' failing ends the rule " ++
      "with its error; second pass: invalid_try_stmt first."
    source := "Grammar/python.gram:441-447"
    status := .proven
    prop := ``TryStmt
    thm := some ``tryStmt_proven
    notes := scheme },
  { id := "pygrammar-rule-except-block"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_except_block
    statement := "except_block: 'except e: b', then 'except e as n: b', then 'except A, B: b' under " ++
      "CHECK_VERSION(14) with the exact message, then bare 'except: b', each reached when the one " ++
      "before fails; second pass: invalid_except_stmt_indent first and invalid_except_stmt last."
    source := "Grammar/python.gram:453-466"
    status := .proven
    prop := ``ExceptBlock
    thm := some ``exceptBlock_proven
    notes := scheme },
  { id := "pygrammar-rule-except-star-block"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_except_star_block
    statement := "except_star_block: as except_block with '*' after 'except' and no bare form; " ++
      "'except' without '*' fails every alternative (NULL in the first pass, " ++
      "invalid_except_star_stmt deciding in the second)."
    source := "Grammar/python.gram:467-479"
    status := .proven
    prop := ``ExceptStarBlock
    thm := some ``exceptStarBlock_proven
    notes := scheme },
  { id := "pygrammar-rule-with-stmt"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_with_stmt
    statement := "with_stmt: the parenthesised form first, then the plain one (also after 'with (...)' " ++
      "not followed by ':'), then 'async with (...)' giving AsyncWith(a, b, NULL) and plain " ++
      "'async with' giving AsyncWith(a, b, tc), both under CHECK_VERSION(5); a block failing in " ++
      "the parenthesised async form falls back to the plain one; second pass: " ++
      "invalid_with_stmt_indent first, invalid_with_stmt last."
    source := "Grammar/python.gram:421-431"
    status := .proven
    prop := ``WithStmt
    thm := some ``withStmt_proven
    notes := scheme },
  { id := "pygrammar-rule-async-with-type-comment"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_async_with_type_comment
    statement := "With type comments on, whatever follows 'with', if 'with ...' parses then " ++
      "'async with ...' parses."
    source := "the implementation against itself: the sync and async parenthesised alternatives of with_stmt"
    status := .refuted
    prop := ``AsyncWithTypeComment
    thm := some ``asyncWithTypeComment_refuted
    bug := some "pygrammar-async-with-type-comment"
    notes := "Counterexample run in the kernel: 'with(a as b):#type:c\\n x\\n' parses, the async " ++
      "form does not." },
  { id := "pygrammar-rule-with-item"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_with_item
    statement := "with_item: 'e as t' followed by ',', ')' or ':' gives withitem(e, t); otherwise " ++
      "backs up and gives withitem(e, NULL), in the second pass after invalid_with_item, whose " ++
      "error ends the rule."
    source := "Grammar/python.gram:433-436"
    status := .proven
    prop := ``WithItem
    thm := some ``withItem_proven
    notes := scheme },
  { id := "pygrammar-rule-import-from-targets"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_import_from_targets
    statement := "import_from_targets: '(names ,?)' gives the names; names not followed by ',' give " ++
      "the names; names followed by ',' fail (invalid_import_from_targets decides in the second " ++
      "pass); '*' gives [alias('*')] located at the star."
    source := "Grammar/python.gram:237-241"
    status := .proven
    prop := ``ImportFromTargets
    thm := some ``importFromTargets_proven
    notes := scheme },
  { id := "pygrammar-rule-class-def"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_class_def
    statement := "class_def: decorators then class_def_raw gives the ClassDef with the decorators " ++
      "and every other field, location included, unchanged; no decorators gives class_def_raw's " ++
      "result; decorators with no class after them give NULL."
    source := "Grammar/python.gram:276-278"
    status := .proven
    prop := ``ClassDef
    thm := some ``classDef_proven
    notes := scheme },
  { id := "pygrammar-rule-function-def"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_function_def
    statement := "function_def: as class_def, for FunctionDef and AsyncFunctionDef alike."
    source := "Grammar/python.gram:291-293"
    status := .proven
    prop := ``FunctionDef
    thm := some ``functionDef_proven
    notes := scheme },
  { id := "pygrammar-rule-class-def-raw"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_class_def_raw
    statement := "class_def_raw: 'class n[tp](args): c' gives ClassDef(n.id, args.args, " ++
      "args.keywords, c, [], tp), bases and keywords empty without an argument list; NULL at any " ++
      "other token; second pass: invalid_class_def_raw first."
    source := "Grammar/python.gram:280-286"
    status := .proven
    prop := ``ClassDefRaw
    thm := some ``classDefRaw_proven
    notes := scheme },
  { id := "pygrammar-rule-function-def-raw"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_function_def_raw
    statement := "function_def_raw: 'def n[tp](params) -> r: tc b' gives FunctionDef with empty " ++
      "arguments for '()'; 'async def' gives AsyncFunctionDef under CHECK_VERSION(5) with the exact " ++
      "message; NULL at any other token; second pass: invalid_def_raw first."
    source := "Grammar/python.gram:295-309"
    status := .proven
    prop := ``FunctionDefRaw
    thm := some ``functionDefRaw_proven
    notes := scheme },
  { id := "pygrammar-rule-annotation-default"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_annotation_default
    statement := "annotation, star_annotation, default: the expression after ':' (star_expression for " ++
      "star_annotation) or '='; NULL at any other token; default in the second pass with nothing " ++
      "after '=': invalid_default decides."
    source := "Grammar/python.gram:379-381"
    status := .proven
    prop := ``AnnotationDefault
    thm := some ``annotationDefault_proven
    notes := scheme },
  { id := "pygrammar-rule-sum"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_sum
    statement := "sum: the seed loop returns the last seed that grew; each round with seed v gives " ++
      "BinOp(v, Add, term) after '+', BinOp(v, Sub, term) after '-' (after the '+' alternative fails " ++
      "and the seed is found again), and term from the start mark otherwise; the first round, with " ++
      "no seed, is term. So a - b - c is BinOp(BinOp(a, Sub, b), Sub, c)."
    source := "Grammar/python.gram:842-845"
    status := .proven
    prop := ``SumRule
    thm := some ``sumRule_proven
    notes := LR },
  { id := "pygrammar-rule-bitwise-or"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_bitwise_or
    statement := "bitwise_or: as sum with the one operator '|' (BitOr) over bitwise_xor."
    source := "Grammar/python.gram:821-823"
    status := .proven
    prop := ``BitwiseOrRule
    thm := some ``bitwiseOrRule_proven
    notes := LR },
  { id := "pygrammar-rule-bitwise-xor"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_bitwise_xor
    statement := "bitwise_xor: as sum with the one operator '^' (BitXor) over bitwise_and."
    source := "Grammar/python.gram:825-827"
    status := .proven
    prop := ``BitwiseXorRule
    thm := some ``bitwiseXorRule_proven
    notes := LR },
  { id := "pygrammar-rule-bitwise-and"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_bitwise_and
    statement := "bitwise_and: as sum with the one operator '&' (BitAnd) over shift_expr."
    source := "Grammar/python.gram:829-831"
    status := .proven
    prop := ``BitwiseAndRule
    thm := some ``bitwiseAndRule_proven
    notes := LR },
  { id := "pygrammar-rule-term"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_term
    statement := "term: the seed loop returns the last seed that grew; a round with seed v tries '*', " ++
      "'/', '//', '%', '@' in that order, each after the ones before fail at their token, giving " ++
      "BinOp(v, op, factor), '@' under CHECK_VERSION(5) with the exact message; with no seed or no " ++
      "operator, factor from the start mark, in the second pass after invalid_factor, whose error " ++
      "ends the round."
    source := "Grammar/python.gram:847-854"
    status := .proven
    prop := ``TermRule
    thm := some ``termRule_proven
    notes := LR },
  { id := "pygrammar-rule-shift-expr"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_shift_expr
    statement := "shift_expr: as term with '<<' then '>>' over sum, and invalid_arithmetic before the " ++
      "operand alternative in the second pass."
    source := "Grammar/python.gram:833-837"
    status := .proven
    prop := ``ShiftExprRule
    thm := some ``shiftExprRule_proven
    notes := LR },
  { id := "pygrammar-rule-invalid-assert-stmt"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_invalid_assert_stmt
    statement := "invalid_assert_stmt: 'assert a = b' raises \"cannot assign to <name> here. Maybe you " ++
      "meant '==' instead of '='?\" over a..b with <name> = _PyPegen_get_expr_name(a); then 'assert " ++
      "t, a = b' the same about a; then 'assert a := b' and 'assert t, a := b' raise \"cannot use " ++
      "named expression without parentheses here\" over a..b; each in order after the ones before " ++
      "fail; any other token: NULL, no error."
    source := "Grammar/python.gram:1329-1347"
    status := .proven
    prop := ``InvalidAssertStmt
    thm := some ``invalidAssertStmt_proven
    notes := scheme ++ " Hypothesis exprName a = some nm: every node expression returns has a " ++
      "name (only Slice lacks one, and only a subscript holds a Slice)." },
  { id := "pygrammar-rule-match-stmt"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_match_stmt
    statement := "match_stmt: soft keyword 'match', subject, ':' NEWLINE INDENT case_block+ DEDENT " ++
      "gives Match(subject, cases) under CHECK_VERSION(10) with the exact message below 10; no " ++
      "soft keyword: NULL in the first pass; second pass, with no soft keyword or no ':' after " ++
      "the subject, invalid_match_stmt decides."
    source := "Grammar/python.gram:487-490"
    status := .proven
    prop := ``MatchStmt
    thm := some ``matchStmt_proven
    notes := scheme },
  { id := "pygrammar-rule-decorators"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_decorators
    statement := "decorators: each line '@' named_expression NEWLINE gives the expression (NULL " ++
      "without the NEWLINE or the '@'); the rule is the lines in source order as one sequence, " ++
      "ending after the last NEWLINE, and NULL with no line (the + loop, proven by induction on " ++
      "the rounds of handle_alt_loop)."
    source := "Grammar/python.gram:271"
    status := .proven
    prop := ``DecoratorsRule
    thm := some ``decoratorsRule_proven
    notes := scheme },
  { id := "pygrammar-rule-primary"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_primary
    statement := "primary: the seed loop returns the last seed that grew; each round with seed v " ++
      "gives Attribute(v, NAME.id, Load) after '.' NAME, Call(v, [genexp]) when a genexp follows " ++
      "(an error in genexp ends the round with NULL), Call(v, args, keywords) after '(' " ++
      "[arguments] ')' once genexp failed, Subscript(v, slices, Load) after '[' slices ']', and " ++
      "atom from the start mark otherwise; the first round is atom (NULL when atom fails)."
    source := "Grammar/python.gram:875-884"
    status := .proven
    prop := ``PrimaryRule
    thm := some ``primaryRule_proven
    notes := LR ++ " After a failed genexp call the state keeps the seed's memo entry and " ++
      "p->level (SeedKept), as every rule function's return does." },
  { id := "pygrammar-rule-t-primary"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_t_primary
    statement := "t_primary: as primary, in the order '.', '[', genexp, '(' and with &t_lookahead " ++
      "after every alternative: a trailer is taken only when another '(' '[' '.' follows it; " ++
      "with '.' NAME, '[' slices ']', a genexp or '(' [arguments] ')' and no trailer after it, " ++
      "that alternative fails and the round falls through the later ones to atom &t_lookahead " ++
      "from the start mark (so 'a.b = 1', 'a[0] = 1' and 'f(x) = 1' leave the seed a or f); " ++
      "with no seed, atom with the lookahead holding, NULL without."
    source := "Grammar/python.gram:1154-1164"
    status := .proven
    prop := ``TPrimaryRule
    thm := some ``tPrimaryRule_proven
    notes := LR ++ " The lookahead and genexp outcome states keep the seed (SeedKept) where a " ++
      "later alternative calls t_primary again." },
  { id := "pygrammar-rule-t-lookahead"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_t_lookahead
    statement := "t_lookahead: at '(' '[' or '.' that token with the mark past it; NULL with the " ++
      "state unchanged at any other token."
    source := "Grammar/python.gram:1166"
    status := .proven
    prop := ``TLookahead
    thm := some ``tLookahead_proven
    notes := scheme },
  { id := "pygrammar-rule-atom"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_atom
    statement := "atom: NAME is the name token; True, False, None and '...' give their Constant; " ++
      "past those, the string lookahead holding gives strings; NUMBER the number token; '(' '[' " ++
      "'{' their group after the lookahead on that token; any other token NULL with the mark back."
    source := "Grammar/python.gram:894-904"
    status := .proven
    prop := ``Atom
    thm := some ``atom_proven
    notes := scheme },
  { id := "pygrammar-rule-slices"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_slices
    statement := "slices: a slice not followed by ',' is the result; followed by ',', or with no " ++
      "slice, Tuple(gather, Load) from the start mark with an optional trailing ','; an error in " ++
      "slice gives NULL."
    source := "Grammar/python.gram:886-888"
    status := .proven
    prop := ``Slices
    thm := some ``slices_proven
    notes := scheme },
  { id := "pygrammar-rule-slice"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_slice
    statement := "slice: [expression] ':' [expression] [':' [expression]] gives Slice(lower, " ++
      "upper, step), each possibly NULL; no ':' gives named_expression from the start mark; an " ++
      "error in the first optional expression gives NULL."
    source := "Grammar/python.gram:890-892"
    status := .proven
    prop := ``Slice
    thm := some ``slice_proven
    notes := scheme },
  { id := "pygrammar-rule-star-targets"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_star_targets
    statement := "star_targets: a star_target not followed by ',' is the result; followed by ',', " ++
      "Tuple([a] + rest, Store) of star_target again, the (',' star_target)* loop and an optional " ++
      "','; no star_target gives NULL."
    source := "Grammar/python.gram:1118-1121"
    status := .proven
    prop := ``StarTargets
    thm := some ``starTargets_proven
    notes := scheme },
  { id := "pygrammar-rule-star-target"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_star_target
    statement := "star_target (memo): '*' (!'*' star_target) gives Starred(a in Store context, " ++
      "Store); otherwise target_with_star_atom from the start mark; memoized."
    source := "Grammar/python.gram:1129-1132"
    status := .proven
    prop := ``StarTarget
    thm := some ``starTarget_proven
    notes := scheme },
  { id := "pygrammar-rule-target-with-star-atom"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_target_with_star_atom
    statement := "target_with_star_atom (memo): t_primary '.' NAME with no trailer after it gives " ++
      "Attribute(Store), t_primary '[' slices ']' with no trailer after it Subscript(Store); with " ++
      "a trailer after either, or no t_primary, star_atom from the start mark; memoized."
    source := "Grammar/python.gram:1134-1137"
    status := .proven
    prop := ``TargetWithStarAtom
    thm := some ``targetWithStarAtom_proven
    notes := scheme },
  { id := "pygrammar-rule-del-targets"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_del_targets
    statement := "del_targets: the ','.del_target+ gather with an optional trailing ','; NULL " ++
      "with the mark back when the gather fails."
    source := "Grammar/python.gram:1171"
    status := .proven
    prop := ``DelTargets
    thm := some ``delTargets_proven
    notes := scheme },
  { id := "pygrammar-rule-del-target"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_del_target
    statement := "del_target (memo): as target_with_star_atom with Del for Store and del_t_atom " ++
      "for star_atom."
    source := "Grammar/python.gram:1173-1176"
    status := .proven
    prop := ``DelTarget
    thm := some ``delTarget_proven
    notes := scheme },
  { id := "pygrammar-rule-dotted-name"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_dotted_name
    statement := "dotted_name: the seed loop returns the last seed that grew; each round with seed " ++
      "v gives the Name v.id + '.' + NAME.id from the start of v to the end of NAME after '.' " ++
      "NAME, and NAME from the start mark otherwise; the first round is NAME."
    source := "Grammar/python.gram:256-258"
    status := .proven
    prop := ``DottedNameRule
    thm := some ``dottedNameRule_proven
    notes := LR },
  { id := "pygrammar-rule-join-names"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.rule_join_names
    statement := "_PyPegen_join_names_with_dot(p, a, b), as dotted_name's action: the Name " ++
      "\"%U.%U\" of the two ids, Load, located from a's start to b's end (EXTRA_EXPR)."
    source := "Parser/action_helpers.c:123-139"
    status := .proven
    prop := ``DottedNameStep
    thm := some ``dottedNameStep_proven
    notes := "The third conjunct of DottedNameStep evaluates the action through callHelper. " ++
      "Allocation failure (PyUnicode_FromFormat, _PyArena_AddPyObject returning NULL) is not " ++
      "modelled; interning has no observable effect on the tree." },
  { id := "pygrammar-rule-dotted-as-name"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_dotted_as_name
    statement := "dotted_as_name: dotted_name and an optional 'as' NAME give alias(name, asname or " ++
      "NULL); no dotted_name gives NULL; in the second pass invalid_dotted_as_name runs first and " ++
      "its error ends the rule."
    source := "Grammar/python.gram:251-254"
    status := .proven
    prop := ``DottedAsName
    thm := some ``dottedAsName_proven
    notes := scheme },
  { id := "pygrammar-rule-import-from-as-name"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_import_from_as_name
    statement := "import_from_as_name: NAME and an optional 'as' NAME give alias(name, asname or " ++
      "NULL); no NAME gives NULL; in the second pass invalid_import_from_as_name runs first and " ++
      "its error ends the rule."
    source := "Grammar/python.gram:244-247"
    status := .proven
    prop := ``ImportFromAsName
    thm := some ``importFromAsName_proven
    notes := scheme },
  { id := "pygrammar-rule-as-names"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_as_names
    statement := "import_from_as_names and dotted_as_names: the ','.x+ gather is the result, no " ++
      "trailing ','; NULL with the mark back without it."
    source := "Grammar/python.gram:242-250"
    status := .proven
    prop := ``AsNames
    thm := some ``asNames_proven
    notes := scheme },
  { id := "pygrammar-rule-closed-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_closed_pattern
    statement := "closed_pattern (memo): the ordered choice of literal, capture, wildcard, value, " ++
      "group, sequence, mapping and class patterns, in that order, from the start mark; an error " ++
      "ends it; memoized."
    source := "Grammar/python.gram:522-530"
    status := .proven
    prop := ``ClosedPattern
    thm := some ``closedPattern_proven
    notes := scheme ++ " choiceRes is the ordered choice of rule calls (choice_run proves the " ++
      "generated alternatives run it)." },
  { id := "pygrammar-rule-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_pattern
    statement := "pattern: the ordered choice of as_pattern then or_pattern."
    source := "Grammar/python.gram:509-511"
    status := .proven
    prop := ``PatternRule
    thm := some ``patternRule_proven
    notes := scheme },
  { id := "pygrammar-rule-maybe-star-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_maybe_star_pattern
    statement := "maybe_star_pattern: the ordered choice of star_pattern then pattern."
    source := "Grammar/python.gram:607-609"
    status := .proven
    prop := ``MaybeStarPattern
    thm := some ``maybeStarPattern_proven
    notes := scheme },
  { id := "pygrammar-rule-or-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_or_pattern
    statement := "or_pattern: the '|'.closed_pattern+ gather with one element is that element, " ++
      "with more MatchOr(patterns); no gather gives NULL."
    source := "Grammar/python.gram:518-520"
    status := .proven
    prop := ``OrPattern
    thm := some ``orPattern_proven
    notes := scheme },
  { id := "pygrammar-rule-capture-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_capture_pattern
    statement := "capture_pattern: MatchAs(NULL, name) from pattern_capture_target; NULL without it."
    source := "Grammar/python.gram:572-573"
    status := .proven
    prop := ``CapturePattern
    thm := some ``capturePattern_proven
    notes := scheme },
  { id := "pygrammar-rule-wildcard-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_wildcard_pattern
    statement := "wildcard_pattern: the soft keyword '_' gives MatchAs(NULL, NULL); NULL without it."
    source := "Grammar/python.gram:579-580"
    status := .proven
    prop := ``WildcardPattern
    thm := some ``wildcardPattern_proven
    notes := scheme },
  { id := "pygrammar-rule-group-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_group_pattern
    statement := "group_pattern: '(' pattern ')' is the inner pattern; any other token, or no " ++
      "inner pattern, NULL with the mark back."
    source := "Grammar/python.gram:593-594"
    status := .proven
    prop := ``GroupPattern
    thm := some ``groupPattern_proven
    notes := scheme },
  { id := "pygrammar-rule-sequence-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_sequence_pattern
    statement := "sequence_pattern: '[' [maybe_sequence_pattern] ']' and, after the first " ++
      "alternative fails at '(', '(' [open_sequence_pattern] ')' give MatchSequence; other tokens " ++
      "NULL."
    source := "Grammar/python.gram:596-598"
    status := .proven
    prop := ``SequencePattern
    thm := some ``sequencePattern_proven
    notes := scheme },
  { id := "pygrammar-rule-patterns"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_patterns
    statement := "patterns: open_sequence_pattern gives MatchSequence; without it pattern from the " ++
      "start mark; an error in open_sequence_pattern gives NULL."
    source := "Grammar/python.gram:504-507"
    status := .proven
    prop := ``Patterns
    thm := some ``patterns_proven
    notes := scheme },
  { id := "pygrammar-rule-subject-expr"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_subject_expr
    statement := "subject_expr: star_named_expression ',' [star_named_expressions] gives " ++
      "Tuple([value] + values, Load); otherwise named_expression from the start mark."
    source := "Grammar/python.gram:492-495"
    status := .proven
    prop := ``SubjectExpr
    thm := some ``subjectExpr_proven
    notes := scheme },
  { id := "pygrammar-rule-invalid-del-stmt"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_invalid_del_stmt
    statement := "invalid_del_stmt: other tokens than 'del' give NULL and no error; 'del' " ++
      "star_expressions with no node _PyPegen_get_invalid_target(DEL_TARGETS) rejects gives NULL " ++
      "and no error, and with one, t, raises \"cannot delete <name of t>\" over t; no " ++
      "star_expressions gives NULL with the mark back."
    source := "Grammar/python.gram:1326-1328"
    status := .proven
    prop := ``InvalidDelStmt
    thm := some ``invalidDelStmt_proven
    notes := scheme ++ " exprName t = some nm excludes only get_expr_name's default branch " ++
      "(Slice), which get_invalid_target never returns from a star_expressions result." },
  { id := "pygrammar-rule-invalid-ann-assign-target"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_invalid_ann_assign_target
    statement := "invalid_ann_assign_target: list, else tuple, else '(' invalid_ann_assign_target " ++
      "')' (the inner target), each from the start mark; NULL otherwise."
    source := "Grammar/python.gram:1317-1320"
    status := .proven
    prop := ``InvalidAnnAssignTarget
    thm := some ``invalidAnnAssignTarget_proven
    notes := scheme },
  { id := "pygrammar-rule-invalid-assignment"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_invalid_assignment
    statement := "invalid_assignment: a list/tuple target before ':' annotation raises \"only " ++
      "single target (not <name>) can be annotated\"; a star_named_expression ',' ... ':' raises " ++
      "the tuple message at the first element; an expression ':' annotation raises \"illegal " ++
      "target for annotation\"; once those fail, (star_targets '=')* star_expressions '=' " ++
      "raises \"cannot assign to <name of t>\" over the first invalid target t " ++
      "(_PyPegen_get_invalid_target(a, STAR_TARGETS)), or with none gives NULL with no error and " ++
      "the mark after '='; with star_expressions NULL, (star_targets '=')* yield_expr '=' raises " ++
      "\"assignment to yield expression not possible\" over the yield expression; and after the " ++
      "annotation and '=' alternatives fail, star_expressions augassign annotated_rhs raises " ++
      "\"'<name>' is an illegal expression for augmented assignment\"; each raise over that " ++
      "expression, NULL with error_indicator set."
    source := "Grammar/python.gram:1297-1316"
    status := .proven
    prop := ``InvalidAssignmentRule
    thm := some ``invalidAssignmentRule_proven
    notes := scheme ++ " AnnAltsFail lets alternatives 2 and 3 fail at any of their items " ++
      "(no star_named_expression, no ',', no ':' after the loop; no expression, no ':'); the " ++
      "'=' clauses take that as a hypothesis." },
  { id := "pygrammar-rule-sum-sub-sub"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_sum_sub_sub
    statement := "sum, composed: from entry, term a, then '-' term b, then '-' term c, then no " ++
      "operator gives BinOp(BinOp(a, Sub, b), Sub, c), at the mark after c (LeaderLoop with " ++
      "three growing rounds, each from SumStep)."
    source := "Grammar/python.gram:842-845"
    status := .proven
    prop := ``SumSubSub
    thm := some ``sumSubSub_proven
    notes := LR ++ " RoundOK on each round's end state: no error, p->level restored, the start " ++
      "mark within memo (memo.size = fill) and the tokens." },
  { id := "pygrammar-rule-dotted-as-name-name-target"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_dotted_as_name_name_target
    statement := "Whatever follows 'import a as b', the error is never \"cannot use name as " ++
      "import target\" (a name is a valid as-target)."
    source := "the implementation against itself: dotted_as_name takes 'as' NAME"
    status := .refuted
    prop := ``DottedAsNameNameTarget
    thm := some ``dottedAsNameNameTarget_refuted
    bug := some "pygrammar-import-as-name-target"
    notes := "Counterexample run in the kernel: 'import a as b c\\n'. Duplicate of gh-146492." },
  { id := "pygrammar-rule-import-from-as-name-name-target"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_import_from_as_name_name_target
    statement := "Whatever follows 'from x import a as b', the error is never \"cannot use name " ++
      "as import target\"."
    source := "the implementation against itself: import_from_as_name takes 'as' NAME"
    status := .refuted
    prop := ``ImportFromAsNameNameTarget
    thm := some ``importFromAsNameNameTarget_refuted
    bug := some "pygrammar-import-as-name-target"
    notes := "Counterexample run in the kernel: 'from x import a as b c\\n'. Duplicate of " ++
      "gh-146492." },
  { id := "pygrammar-rule-invalid-dotted-as-name"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_invalid_dotted_as_name
    statement := "invalid_dotted_as_name: dotted_name 'as', the lookahead group _tmp_139 failing, " ++
      "and an expression a raise \"cannot use <name of a> as import target\" over a (\"literal\" " ++
      "for 'import a as 1'), NULL with error_indicator set; with _tmp_139 matching (a NAME " ++
      "followed by ',' ')' ';' or NEWLINE, as in a valid target) NULL with the mark back and no " ++
      "error; a missing dotted_name, 'as' or expression gives NULL with the mark back. _tmp_139 " ++
      "is NAME then _tmp_175, and _tmp_175 takes exactly ',' ')' ';' NEWLINE."
    source := "Grammar/python.gram:1438-1441"
    status := .proven
    prop := ``InvalidAsNameRules
    thm := some ``invalidAsNameRules_proven
    notes := scheme ++ " Shared with invalid_import_from_as_name; the refutation " ++
      "pygrammar-rule-dotted-as-name-name-target is the case where the lookahead passes over a " ++
      "valid name." },
  { id := "pygrammar-rule-invalid-import-from-as-name"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_invalid_import_from_as_name
    statement := "invalid_import_from_as_name: NAME 'as', the lookahead group _tmp_139 failing, " ++
      "and an expression a raise \"cannot use <name of a> as import target\" over a, NULL with " ++
      "error_indicator set; with _tmp_139 matching NULL with the mark back and no error; a " ++
      "missing NAME, 'as' or expression gives NULL with the mark back."
    source := "Grammar/python.gram:1442-1445"
    status := .proven
    prop := ``InvalidAsNameRules
    thm := some ``invalidAsNameRules_proven
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
] ++ patternEntries ++ paramEntries

end PyLean.PyGrammar.Peg
