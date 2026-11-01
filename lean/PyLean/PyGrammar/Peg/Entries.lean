import PyLean.Registry
import PyLean.PyGrammar.RowNames
import PyLean.PyGrammar.Peg.Props
import PyLean.PyGrammar.Peg.TokenProps
import PyLean.PyGrammar.Peg.RuleFacts

/-! Registry entries for the `Peg` part of `PyGrammar`. -/

namespace PyLean.PyGrammar.Peg

open PyLean.Registry

def entries : List Entry := [
  { id := "pygrammar-grammar-left-recursion"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.grammar_left_recursion
    statement := "Over every rule, artificial ones included: with leader back edges cut, the " ++
      "left-call graph (rules callable before a token is consumed) is acyclic, so at one " ++
      "position a call chain can repeat a rule only through a seed-growing leader's memo entry."
    source := "invariant"
    status := .proven
    prop := ``LeftRecursionGuarded
    thm := some ``leftRecursionGuarded_proven
    notes := "Static half of 'left recursion terminates on all inputs'. The dynamic half, a " ++
      "fuel bound for the whole interpreter, is pygrammar-peg-terminates, open." },
  { id := "pygrammar-grammar-refs"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.grammar_left_recursion
    statement := "Every rule reference in the grammar data resolves to a rule."
    source := "invariant"
    status := .proven
    prop := ``GrammarRefsResolve
    thm := some ``grammarRefsResolve_proven },
  { id := "pygrammar-grammar-nullable-fixpoint"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.grammar_left_recursion
    statement := "The computed nullable set is a fixed point of the nullability equations."
    source := "invariant"
    status := .proven
    prop := ``NullableIsFixedPoint
    thm := some ``nullableIsFixedPoint_proven },
  { id := "pygrammar-grammar-loops-consume"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.grammar_left_recursion
    statement := "No `_loop0`/`_loop1` body can match empty input, so `while (items)` advances."
    source := "invariant"
    status := .proven
    prop := ``LoopsConsume
    thm := some ``loopsConsume_proven },
  { id := "pygrammar-grammar-keywords"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.grammar_left_recursion
    statement := "Hard and soft keywords are disjoint; keyword token numbers are distinct and " ++
      "above Grammar/Tokens."
    source := "invariant"
    status := .proven
    prop := ``KeywordsDistinct
    thm := some ``keywordsDistinct_proven },
  { id := "pygrammar-grammar-rule-names"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.grammar_left_recursion
    statement := "Rule names are distinct, so memo keys identify rules."
    source := "invariant"
    status := .proven
    prop := ``RuleNamesDistinct
    thm := some ``ruleNamesDistinct_proven },
  { id := "pygrammar-grammar-start-rules"
    pyFile := "Grammar/python.gram"
    pyFns := []
    statement := "The four start rules dispatched by the trailer are the rules of those names."
    source := "invariant"
    status := .proven
    prop := ``StartRulesNamed
    thm := some ``startRulesNamed_proven },
  { id := "pygrammar-grammar-invalid-first-pass"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.grammar_left_recursion
    statement := "As the comment at the top of the grammar says, invalid_ rules are not used " ++
      "in the first pass: every alternative calling one is guarded by call_invalid_rules."
    source := "Grammar/python.gram:36 comment"
    status := .refuted
    prop := ``InvalidRulesGuarded
    thm := some ``invalidRulesGuarded_refuted
    bug := some "pygrammar-grammar-invalid-first-pass"
    notes := "dict's second alternative. Narrowed in pygrammar-grammar-invalid-but-dict." },
  { id := "pygrammar-grammar-invalid-but-dict"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.grammar_left_recursion
    statement := "Apart from the rule dict, every call of an invalid_ rule is guarded."
    source := "Grammar/python.gram:36 comment"
    status := .proven
    prop := ``InvalidRulesGuardedButDict
    thm := some ``invalidRulesGuardedButDict_proven },
  { id := "pygrammar-peg-first-error"
    pyFile := "Parser/pegen_errors.c"
    pyFns := Rows.peg_first_error
    statement := "Once error_indicator and an exception are set, no raise entry point changes " ++
      "the parser state or the exception."
    source := "Parser/pegen_errors.c 'Bail out if we already have an error set'"
    status := .proven
    prop := ``FirstErrorWins
    thm := some ``firstErrorWins_proven },
  { id := "pygrammar-peg-make-arguments"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_make_arguments
    statement := "With at most one of the two slash forms given, _PyPegen_make_arguments yields no " ++
      "more positional defaults than positional parameters, so validate_arguments accepts them."
    source := "invariant"
    status := .proven
    prop := ``MakeArgumentsDefaultsFit
    thm := some ``makeArgumentsDefaultsFit_proven },
  { id := "pygrammar-peg-concat"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_concat
    statement := "The folding loop of _build_concatenated_str leaves no empty string constant."
    source := "Parser/action_helpers.c 'Drop all empty contanst strings'"
    status := .proven
    prop := ``ConcatNormalForm
    thm := some ``concatNormalForm_proven },
  { id := "pygrammar-peg-roundtrip-parser"
    pyFile := "Parser/pegen.c"
    pyFns := Rows.peg_roundtrip_parser
    statement := "Parsing is inverted by ast.unparse: parse(unparse(parse s)) equals parse s, " ++
      "ignoring locations, for every source s."
    source := "Lib/_ast_unparse.py Unparser.visit docstring"
    status := .refuted
    prop := ``UnparseRoundTrip
    thm := some ``unparseRoundTrip_refuted
    bug := some "pygrammar-unparse-format-spec-escapes"
    notes := "The refutation runs lexer, PEG interpreter and actions in the kernel on real text." },
  { id := "pygrammar-peg-roundtrip-actions"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_roundtrip_actions
    statement := "Same round trip, as it bears on the tree the action helpers build."
    source := "Lib/_ast_unparse.py Unparser.visit docstring"
    status := .refuted
    prop := ``UnparseRoundTrip
    thm := some ``unparseRoundTrip_refuted
    bug := some "pygrammar-unparse-format-spec-escapes" },
  { id := "pygrammar-unparse-roundtrip"
    pyFile := "Lib/_ast_unparse.py"
    pyFns := Rows.unparse_roundtrip
    statement := "ast.parse of ast.unparse of a parsed tree gives back that tree, ignoring " ++
      "locations."
    source := "Lib/_ast_unparse.py Unparser.visit docstring"
    status := .refuted
    prop := ``UnparseRoundTrip
    thm := some ``unparseRoundTrip_refuted
    bug := some "pygrammar-unparse-format-spec-escapes" },
  { id := "pygrammar-unparse-c-roundtrip"
    pyFile := "Python/ast_unparse.c"
    pyFns := Rows.unparse_c_roundtrip
    statement := "The string _PyAST_ExprAsUnicode makes of a parsed expression parses back to " ++
      "that expression, ignoring locations."
    source := "PEP 563: annotations are stored as the string form of their expression"
    status := .refuted
    prop := ``CUnparseRoundTrip
    thm := some ``cUnparseRoundTrip_refuted
    bug := some "pygrammar-unparse-c-fstring-repr" },
  { id := "pygrammar-grammar-call-rule-sound"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.grammar_call_rule_sound
    statement := "When callRule succeeds on any rule with no error, from any state with an empty " ++
      "memo and the mark within the tokens read, the tokens it consumed match that rule's " ++
      "alternatives in the grammar data, item by item, left recursion included."
    source := "the implementation against itself: Parser/parser.c against Grammar/python.gram"
    status := .proven
    prop := ``CallRuleSound
    thm := some ``callRuleSound_proven
    notes := "One direction only: lookaheads and alternative order are not in RuleM, and what " ++
      "an action computes is not claimed. Peg/RuleFacts.lean has the per-rule statements." },
  { id := "pygrammar-grammar-rule-starts"
    pyFile := "Grammar/python.gram"
    pyFns := []
    statement := "A rule that succeeds starts with a token of a type in its FIRST set, or matched " ++
      "nothing and is nullable; the table is checked closed over all 445 rules."
    source := "invariant"
    status := .proven
    prop := ``AllRulesStart
    thm := some ``allRulesStart_proven },
  { id := "pygrammar-peg-progress"
    pyFile := "Parser/parser.c"
    pyFns := []
    statement := "Every iteration of a loop rule moves p->mark forward, and at MAXSTACK a rule " ++
      "sets error_indicator and returns NULL at once."
    source := "invariant: no hang"
    status := .proven
    prop := ``ParserProgress
    thm := some ``parserProgress_proven
    notes := "What ParserTerminates would be built on. Rows of Parser/parser.c stay generated." },
  { id := "pygrammar-peg-actions-frame"
    pyFile := "Parser/action_helpers.c"
    pyFns := []
    statement := "No action moves the mark, drops a token, touches the memo or clears " ++
      "error_indicator."
    source := "invariant"
    status := .proven
    prop := ``ActionsFrame
    thm := some ``actionsFrame_proven
    notes := "Holds of any pure helper, so it credits no helper row." },
  { id := "pygrammar-peg-token-readers"
    pyFile := "Parser/pegen.c"
    pyFns := Rows.peg_token_readers
    statement := "name_token, soft_keyword_token, expect_soft_keyword and expect_forced_token " ++
      "take the token they promise and move the mark past it, or leave it, or end in an error."
    source := "invariant"
    status := .proven
    prop := ``TokenReaders
    thm := some ``tokenReaders_proven },
  { id := "pygrammar-peg-never-silent"
    pyFile := "Parser/pegen.c"
    pyFns := Rows.peg_never_silent
    statement := "_PyPegen_run_parser never returns NULL without an exception set, from any state."
    source := "invariant: SystemError 'parser returned NULL without error' is an internal error"
    status := .proven
    prop := ``ParserNeverSilent
    thm := some ``parserNeverSilent_proven },
  { id := "pygrammar-peg-tokenizer-error"
    pyFile := "Parser/pegen_errors.c"
    pyFns := Rows.peg_tokenizer_error
    statement := "Every arm of _Pypegen_tokenizer_error returns -1 with an exception set, and " ++
      "leaves mark, tokens and memo alone."
    source := "invariant"
    status := .proven
    prop := ``TokenizerErrorSets
    thm := some ``tokenizerErrorSets_proven },
  { id := "pygrammar-peg-set-syntax-error"
    pyFile := "Parser/pegen_errors.c"
    pyFns := Rows.peg_set_syntax_error
    statement := "_Pypegen_set_syntax_error always leaves an exception set, and an INDENT or " ++
      "DEDENT last token gives the matching IndentationError."
    source := "invariant"
    status := .proven
    prop := ``SetSyntaxError
    thm := some ``setSyntaxError_proven },
  { id := "pygrammar-peg-tokenize-full-source"
    pyFile := "Parser/pegen_errors.c"
    pyFns := Rows.peg_tokenize_full_source
    statement := "Interactive input is left alone; otherwise a tokenizer error in regular mode " ++
      "replaces the current exception, and any other outcome restores it."
    source := "Parser/pegen_errors.c 'We don't want to tokenize to the end for interactive input'"
    status := .proven
    prop := ``TokenizeFullSource
    thm := some ``tokenizeFullSource_proven },
  { id := "pygrammar-peg-raise-known-location"
    pyFile := "Parser/pegen_errors.c"
    pyFns := Rows.peg_raise_known_location
    statement := "With no exception yet, the raise sets class, message and line and resolves " ++
      "CURRENT_POS; it never moves the parser."
    source := "invariant"
    status := .proven
    prop := ``RaiseKnownLocation
    thm := some ``raiseKnownLocation_proven },
  { id := "pygrammar-peg-raise-error"
    pyFile := "Parser/pegen_errors.c"
    pyFns := Rows.peg_raise_error
    statement := "RAISE_ERROR sets its class and message at the known error token, or line 0 " ++
      "with no token read."
    source := "invariant"
    status := .proven
    prop := ``RaiseErrorContract
    thm := some ``raiseErrorContract_proven },
  { id := "pygrammar-peg-raise-unclosed"
    pyFile := "Parser/pegen_errors.c"
    pyFns := Rows.peg_raise_unclosed
    statement := "The unclosed-bracket error names the innermost open bracket, at its line."
    source := "invariant"
    status := .proven
    prop := ``RaiseUnclosed
    thm := some ``raiseUnclosed_proven },
  { id := "pygrammar-peg-decode-error"
    pyFile := "Parser/pegen_errors.c"
    pyFns := Rows.peg_decode_error
    statement := "_Pypegen_raise_decode_error returns -1; a decoding error becomes a SyntaxError " ++
      "naming its kind, and any other exception is untouched."
    source := "invariant"
    status := .proven
    prop := ``RaiseDecodeError
    thm := some ``raiseDecodeError_proven },
  { id := "pygrammar-peg-fill-token"
    pyFile := "Parser/pegen.c"
    pyFns := Rows.peg_fill_token
    statement := "On success and on both failure paths, _PyPegen_fill_token appends one token " ++
      "and one empty memo slot and leaves earlier tokens and the mark alone."
    source := "invariant"
    status := .proven
    prop := ``FillToken
    thm := some ``fillToken_proven },
  { id := "pygrammar-peg-expect-token"
    pyFile := "Parser/pegen.c"
    pyFns := Rows.peg_expect_token
    statement := "_PyPegen_expect_token takes a token exactly when its type matches, reads one " ++
      "first at the end of the tokens, and on a read failure returns NULL with the mark unmoved."
    source := "invariant"
    status := .proven
    prop := ``ExpectToken
    thm := some ``expectToken_proven },
  { id := "pygrammar-peg-memo-cache"
    pyFile := "Parser/pegen.c"
    pyFns := Rows.peg_memo_cache
    statement := "What _PyPegen_insert_memo or _PyPegen_update_memo stores at a read token is " ++
      "what _PyPegen_is_memoized finds there, with the parser resuming at the stored mark."
    source := "invariant"
    status := .proven
    prop := ``MemoReturnsStored
    thm := some ``memoReturnsStored_proven },
  { id := "pygrammar-peg-last-token"
    pyFile := "Parser/pegen.c"
    pyFns := Rows.peg_last_token
    statement := "With a token behind the mark, the result is the last token behind it that is " ++
      "not NEWLINE, INDENT, DEDENT or ENDMARKER, or the very first token."
    source := "invariant"
    status := .proven
    prop := ``LastNonWhitespace
    thm := some ``lastNonWhitespace_proven },
  { id := "pygrammar-peg-strip-interpolation"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_strip_interpolation
    statement := "What _strip_interpolation_expr returns does not end in whitespace or '='."
    source := "invariant"
    status := .proven
    prop := ``StripInterpolation
    thm := some ``stripInterpolation_proven },
  { id := "pygrammar-peg-register-stmts"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_register_stmts
    statement := "_PyPegen_register_stmts does nothing in the first pass; in the second it " ++
      "records the last statement unless a later one is recorded."
    source := "invariant"
    status := .proven
    prop := ``RegisterStmts
    thm := some ``registerStmts_proven },
  { id := "pygrammar-peg-identifier-not-constant"
    pyFile := "Parser/pegen.c"
    pyFns := []
    statement := "No identifier from _PyPegen_new_identifier is None, True or False, after NFKC."
    source := "invariant"
    status := .open
    prop := ``IdentifierNeverConstant
    notes := "Stated; needs List.find? reasoning over the forbidden table." },
  { id := "pygrammar-peg-decimal-value"
    pyFile := "Parser/pegen.c"
    pyFns := []
    statement := "A decimal literal of up to 19 digits, not starting with 0, reads as its value."
    source := "invariant"
    status := .open
    prop := ``DecimalValue
    notes := "Stated. roundToBits, the exact float conversion, has no correctness proof either." },
  { id := "pygrammar-peg-terminates"
    pyFile := "Parser/pegen.c"
    pyFns := []
    statement := "For every source, runParser with default fuel does not exhaust its fuel."
    source := "invariant"
    status := .open
    prop := ``ParserTerminates
    notes := "Not refuted: a stress test to 10000 nested levels of 17 shapes never ran out. " ++
      "ParserProgress gives the loops and the depth. Missing: a bound on the token count from " ++
      "the lexer, and a fuel bound across nested left recursion, where the seed rounds on one " ++
      "path are only bounded by using the memo (a leader grows once per position). " ++
      "Estimated over 1000 lines; a measure on depth alone gives depth times tokens, which the " ++
      "default fuel does not cover." },
  { id := "pygrammar-peg-parser-output-validates"
    pyFile := "Python/ast.c"
    pyFns := []
    statement := "Every tree parseStr returns passes validate."
    source := "invariant: the assert behind Py_DEBUG in _PyPegen_run_parser"
    status := .open
    prop := ``ParserOutputValidates
    notes := "True on every difftest case. Not reachable as stated: it needs, for each of the " ++
      "action expressions in the grammar, that the node built meets validate_expr and " ++
      "validate_stmt, plus VALIDATE_POSITIONS, which needs lexer facts that token positions " ++
      "increase. CallRuleSound says nothing about what actions compute, so it does not help." }
]

end PyLean.PyGrammar.Peg
