import PyLean.Registry
import PyLean.PyGrammar.RowNames
import PyLean.PyGrammar.Peg.Props
import PyLean.PyGrammar.Peg.TokenProps
import PyLean.PyGrammar.Peg.ImportProps
import PyLean.PyGrammar.Peg.ReaderProps
import PyLean.PyGrammar.Peg.ErrorArms
import PyLean.PyGrammar.Peg.HelperProps
import PyLean.PyGrammar.Peg.RuleFacts
import PyLean.PyGrammar.Peg.Rules.Entries

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
  { id := "pygrammar-peg-make-arguments-exact"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_make_arguments_exact
    statement := "For each of its five arguments NULL or not, _PyPegen_make_arguments builds " ++
      "arguments(posonlyargs = slash_without_default, else the plain names then the pair names " ++
      "of slash_with_default; args = plain names then the names of names_with_default; vararg, " ++
      "kwonlyargs = names of the keyword-only pairs, kw_defaults = their defaults, kwarg from " ++
      "star_etc, empty or NULL without it; defaults = the defaults of slash_with_default's pairs " ++
      "then those of names_with_default)."
    source := "Parser/action_helpers.c:504-692"
    status := .proven
    prop := ``MakeArgumentsExact
    thm := some ``makeArgumentsExact_proven
    notes := "No hypothesis: when both slash forms are given, slash_without_default wins for " ++
      "posonlyargs and slash_with_default's defaults are still used, as in the C. The " ++
      "assert(0) branch of _make_posargs is included." },
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
      "an action computes is not claimed, so it credits no rule row; the rule-specific " ++
      "statements are the pygrammar-rule-* entries of Peg/Rules/." },
  { id := "pygrammar-grammar-rule-starts"
    pyFile := "Grammar/python.gram"
    pyFns := []
    statement := "A rule that succeeds starts with a token of a type in its FIRST set, or matched " ++
      "nothing and is nullable; the table is checked closed over all 458 rules."
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
  { id := "pygrammar-peg-tokenizer-error-arms"
    pyFile := "Parser/pegen_errors.c"
    pyFns := Rows.peg_tokenizer_error_arms
    statement := "_Pypegen_tokenizer_error returns -1 and, with no exception set before, sets " ++
      "error_indicator and raises by tok->done: E_TOKEN 'invalid token', E_EOF the unclosed " ++
      "bracket or 'unexpected EOF while parsing', E_DEDENT IndentationError 'unindent does not " ++
      "match any outer indentation level', E_INTR KeyboardInterrupt, E_NOMEM MemoryError, " ++
      "E_TABSPACE TabError, E_TOODEEP IndentationError 'too many levels of indentation', " ++
      "E_LINECONT 'unexpected character after line continuation character', E_COLUMNOVERFLOW " ++
      "OverflowError, anything else 'unknown parsing error'; the known-location arms on the " ++
      "tokenizer's line. With an exception already set it changes nothing."
    source := "Parser/pegen_errors.c:23-81"
    status := .proven
    prop := ``TokenizerErrorArms
    thm := some ``tokenizerErrorArms_proven },
  { id := "pygrammar-peg-set-syntax-error-arms"
    pyFile := "Parser/pegen_errors.c"
    pyFns := Rows.peg_set_syntax_error_arms
    statement := "_Pypegen_set_syntax_error keeps an existing exception (refined by the " ++
      "full-source check only for a SyntaxError with the tokenizer fine), and otherwise raises " ++
      "for the first pass's last token: the unclosed bracket or 'unexpected EOF while parsing' " ++
      "for an ERRORTOKEN at EOF, 'unexpected indent'/'unexpected unindent' for INDENT/DEDENT, " ++
      "and else 'invalid syntax' at that token's line followed by the full-source check."
    source := "Parser/pegen_errors.c:383-424"
    status := .proven
    prop := ``SetSyntaxErrorArms
    thm := some ``setSyntaxErrorArms_proven
    notes := "p->fill == 0 is not stated: unreachable, the first pass always counts a token." },
  { id := "pygrammar-peg-memo-frontier"
    pyFile := "Parser/pegen.c"
    pyFns := Rows.peg_memo_frontier
    statement := "_PyPegen_is_memoized at mark == fill fills a token, returning -1 with " ++
      "error_indicator set if that fails and a miss on the filled state otherwise; with the " ++
      "token read and no entry of the rule's type it is a miss that leaves the parser alone."
    source := "Parser/pegen.c:341-373"
    status := .proven
    prop := ``MemoFrontier
    thm := some ``memoFrontier_proven
    notes := "memo.size = fill is the invariant FillToken keeps." },
  { id := "pygrammar-peg-raise-error-exact"
    pyFile := "Parser/pegen_errors.c"
    pyFns := Rows.peg_raise_error_exact
    statement := "_PyPegen_raise_error bails out on an earlier error, raises at line 0 with no " ++
      "token read, and otherwise raises at known_err_token or else tokens[mark] (use_mark) or " ++
      "tokens[fill - 1], one-based columns or the tokenizer's column for a token without one, " ++
      "on that token's line; with use_mark at the frontier it fills a token first and on " ++
      "failure only sets error_indicator."
    source := "Parser/pegen_errors.c:197-241"
    status := .proven
    prop := ``RaiseErrorExact
    thm := some ``raiseErrorExact_proven },
  { id := "pygrammar-peg-tokenize-rest-stops"
    pyFile := "Parser/pegen_errors.c"
    pyFns := Rows.peg_tokenize_rest_stops
    statement := "The loop of _PyPegen_tokenize_full_source_to_check_for_errors reads tokens up " ++
      "to the first ERRORTOKEN or ENDMARKER and stops there; at an ERRORTOKEN with no tokenizer " ++
      "exception and a bracket still open on a line before the generic error's, it raises " ++
      "\"'c' was never closed\" for it, and otherwise raises nothing."
    source := "Parser/pegen_errors.c:154-177"
    status := .proven
    prop := ``TokenizeRestStops
    thm := some ``tokenizeRestStops_proven
    notes := "With pygrammar-peg-tokenize-full-source (the prompt check and which exception " ++
      "survives) this covers the function." },
  { id := "pygrammar-peg-run-parser-paths"
    pyFile := "Parser/pegen.c"
    pyFns := Rows.peg_run_parser_paths
    statement := "_PyPegen_run_parser drops a result with an exception pending; with no result " ++
      "raises _IncompleteInputError at the end of incomplete input, returns a non-SyntaxError " ++
      "as is, and otherwise runs the second pass from the reset state (no recorded statement, " ++
      "memo cleared, mark 0, invalid rules on) and sets the syntax error from the first pass's " ++
      "last token; with a result it refuses a single input with more statements and otherwise " ++
      "returns it."
    source := "Parser/pegen.c:940-992"
    status := .proven
    prop := ``RunParserPaths
    thm := some ``runParserPaths_proven
    notes := "_PyAST_Validate under Py_DEBUG is not modelled; reset_parser_state_for_error_pass's " ++
      "interactive_underflow is interactive-only." },
  { id := "pygrammar-peg-token-readers-exact"
    pyFile := "Parser/pegen.c"
    pyFns := Rows.peg_token_readers_exact
    statement := "With the token at the mark read: expect_forced_token bails out on an earlier " ++
      "error, takes a token of the type and moves the mark, and otherwise raises SyntaxError " ++
      "\"expected '<x>'\" at that token's line without moving; expect_soft_keyword takes a NAME " ++
      "spelled kw as a Name, and leaves the parser untouched otherwise; name_token takes a NAME " ++
      "as a Name, and leaves the parser untouched otherwise; soft_keyword_token takes a NAME " ++
      "that is a soft keyword, returns NULL past any other NAME, and leaves other tokens alone."
    source := "Parser/pegen.c:435-478, 585-612"
    status := .proven
    prop := ``TokenReadersExact
    thm := some ``tokenReadersExact_proven },
  { id := "pygrammar-peg-token-readers-frontier"
    pyFile := "Parser/pegen.c"
    pyFns := Rows.peg_token_readers_frontier
    statement := "At the mark == fill frontier each token reader first fills a token: if that " ++
      "fails it returns NULL with error_indicator set on the state the fill left, and " ++
      "otherwise it reads the new token as when it was already there."
    source := "Parser/pegen.c:407-411, 437-441, 459-463"
    status := .proven
    prop := ``TokenReadersFrontier
    thm := some ``tokenReadersFrontier_proven },
  { id := "pygrammar-peg-name-from-token"
    pyFile := "Parser/pegen.c"
    pyFns := Rows.peg_name_from_token
    statement := "_PyPegen_name_from_token builds Name(id, Load) at the token's location from " ++
      "the identifier _PyPegen_new_identifier makes of its bytes, and returns NULL with " ++
      "error_indicator set when the identifier is refused."
    source := "Parser/pegen.c:565-582"
    status := .proven
    prop := ``NameFromToken
    thm := some ``nameFromToken_proven },
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
    statement := "_strip_interpolation_debug_expr removes the whitespace after a debug '=' and " ++
      "keeps what is before it, and it removes nothing but a final '=' and the whitespace and " ++
      "continuation backslashes after it."
    source := "the comments in Parser/action_helpers.c:1548-1549 and 1570"
    status := .proven
    prop := ``StripInterpolation
    thm := some ``stripInterpolation_proven },
  { id := "pygrammar-peg-strip-continuations"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_strip_continuations
    statement := "After a debug '=', whitespace followed by any number of explicit line " ++
      "continuations (a backslash, then whitespace holding a line end) is removed with the '=', " ++
      "and what precedes the '=' is kept."
    source := "the comment in Parser/action_helpers.c:1548-1549"
    status := .proven
    prop := ``StripContinuations
    thm := some ``stripContinuations_proven
    notes := "Needs the outer loop of 1550-1568: a body that strips only one whitespace run " ++
      "returns 'x=\\' plus newline unchanged and fails it." },
  { id := "pygrammar-peg-decode-known"
    pyFile := "Parser/pegen_errors.c"
    pyFns := Rows.peg_decode_known
    statement := "_Pypegen_raise_decode_error_known_location turns a decode error into a " ++
      "SyntaxError naming its kind on the line of the node, and leaves other exceptions alone."
    source := "invariant"
    status := .proven
    prop := ``RaiseDecodeKnown
    thm := some ``raiseDecodeKnown_proven },
  { id := "pygrammar-peg-decode-format-spec"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_decode_format_spec
    statement := "compile raises no bare UnicodeDecodeError: a string that does not decode is a " ++
      "SyntaxError, as _PyPegen_decode_fstring_part and _PyPegen_constant_from_string make it."
    source := "the implementation disagreeing with itself"
    status := .refuted
    prop := ``DecodeErrorsAreSyntaxErrors
    thm := some ``decodeErrorsAreSyntaxErrors_refuted
    bug := some "pygrammar-peg-format-spec-decode-error"
    notes := "Duplicates the open python/cpython#157890." },
  { id := "pygrammar-peg-missing-comma"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_missing_comma
    statement := "_PyPegen_raise_error_for_missing_comma is silent on legacy statements and " ++
      "outside brackets, and otherwise raises, on the last line of a multi-line left operand."
    source := "the comments in Parser/action_helpers.c:967-978"
    status := .proven
    prop := ``MissingComma
    thm := some ``missingComma_proven },
  { id := "pygrammar-peg-warn-lazy"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_warn_lazy
    statement := "_warn_relative_import_of_lazy warns on `from . lazy import x` with the right " ++
      "number of dots and returns 0, and does nothing on `from .lazy import x` or on the second " ++
      "pass; when the warnings filter makes SyntaxWarning an error it raises SyntaxError with " ++
      "the warning's message at the module name and returns -1."
    source := "the comments in Parser/action_helpers.c:2034-2037"
    status := .proven
    prop := ``WarnRelativeLazy
    thm := some ``warnRelativeLazy_proven
    notes := "The filter is Cfg.warnErrors, by category; filters on message, module or line " ++
      "are out of scope. text is None: the model's filename names no file." },
  { id := "pygrammar-peg-checked-from-import"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_checked_from_import
    statement := "_PyPegen_checked_from_import refuses lazy from __future__, returns NULL when " ++
      "the lazy-import warning fails (an error filter), otherwise builds the ImportFrom of the " ++
      "module, names, dots and lazy flag, and only from __future__ import barry_as_FLUFL turns " ++
      "on `<>`."
    source := "PEP 810 and Parser/action_helpers.c:2082-2114"
    status := .proven
    prop := ``CheckedFromImport
    thm := some ``checkedFromImport_proven },
  { id := "pygrammar-peg-register-stmts"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_register_stmts
    statement := "_PyPegen_register_stmts returns its statements unchanged; it leaves the " ++
      "parser alone in the first pass and for no statements, and in the second records the " ++
      "last statement's line and column unless the recorded one is on a later line."
    source := "Parser/action_helpers.c:2116-2134; read by _PyPegen_set_syntax_error_metadata"
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
      "increase. CallRuleSound says nothing about what actions compute, so it does not help." },
  { id := "pygrammar-peg-check-fstring-conversion"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_check_fstring_conversion
    statement := "_PyPegen_check_fstring_conversion: a name not adjacent to '!' raises \"f-string: " ++
      "conversion type must come right after the exclamation mark\" over both, checked first; a " ++
      "name other than s, r, a raises \"...invalid conversion character 'x': expected 's', 'r', " ++
      "or 'a'\" at the name (repr of the name, t- for t-strings); else the result record."
    source := "Parser/action_helpers.c:1005-1027"
    status := .proven
    prop := ``CheckFstringConversion
    thm := some ``checkFstringConversion_proven },
  { id := "pygrammar-peg-expr-name"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_expr_name
    statement := "_PyPegen_get_expr_name names all 28 switch cases (Constant by value identity); " ++
      "among expression kinds only Slice reaches the default: NULL with SystemError " ++
      "\"unexpected expression in assignment 29 (line N)\"."
    source := "Parser/action_helpers.c:1083-1159"
    status := .proven
    prop := ``ExprNameTable
    thm := some ``exprNameTable_proven
    notes := "No grammar call site passes a Slice; a NULL name formatted with %s would be " ++
      "strlen(NULL) in unicode_fromformat_write_utf8, where the model formats \"\"." },
  { id := "pygrammar-peg-arguments-parsing-error"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_arguments_parsing_error
    statement := "_PyPegen_arguments_parsing_error raises \"positional argument follows keyword " ++
      "argument unpacking\" when a keyword is a ** unpacking, \"positional argument follows " ++
      "keyword argument\" otherwise, at the last token, and gives NULL."
    source := "Parser/action_helpers.c:1271-1288"
    status := .proven
    prop := ``ArgumentsParsingError
    thm := some ``argumentsParsingError_proven },
  { id := "pygrammar-peg-last-comprehension-item"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_last_comprehension_item
    statement := "_PyPegen_get_last_comprehension_item is the last if of the comprehension, or its " ++
      "iter when it has none."
    source := "Parser/action_helpers.c:1161-1167"
    status := .proven
    prop := ``LastComprehensionItem
    thm := some ``lastComprehensionItem_proven },
  { id := "pygrammar-peg-nonparen-genexp"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_nonparen_genexp
    statement := "_PyPegen_nonparen_genexp_in_call is silent with at most one positional argument; " ++
      "with more it raises \"Generator expression must be parenthesized\" from the last " ++
      "argument to the last item of the last comprehension."
    source := "Parser/action_helpers.c:1290-1312"
    status := .proven
    prop := ``NonparenGenexp
    thm := some ``nonparenGenexp_proven },
  { id := "pygrammar-peg-check-legacy-stmt"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_check_legacy_stmt
    statement := "_PyPegen_check_legacy_stmt is 1 exactly for a Name print or exec, 0 otherwise."
    source := "Parser/action_helpers.c:950-962"
    status := .proven
    prop := ``CheckLegacyStmt
    thm := some ``checkLegacyStmt_proven },
  { id := "pygrammar-peg-check-barry"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_check_barry
    statement := "_PyPegen_check_barry_as_flufl: under barry_as_FLUFL '!=' raises \"with Barry as " ++
      "BDFL, use '<>' instead of '!='\" (-1) and '<>' is 0; without it '!=' is 0 and '<>' nonzero."
    source := "Parser/action_helpers.c:934-948"
    status := .proven
    prop := ``CheckBarry
    thm := some ``checkBarry_proven },
  { id := "pygrammar-peg-ensure-complex"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_ensure_complex
    statement := "_PyPegen_ensure_imaginary passes a complex Constant, _PyPegen_ensure_real any other " ++
      "Constant; everything else raises \"imaginary/real number required in complex literal\" " ++
      "at the node."
    source := "Parser/action_helpers.c:853-872"
    status := .proven
    prop := ``EnsureComplexParts
    thm := some ``ensureComplexParts_proven },
  { id := "pygrammar-peg-concatenate-strings"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_concatenate_strings
    statement := "_PyPegen_concatenate_strings: bytes with non-bytes raises \"cannot mix bytes and " ++
      "nonbytes literals\"; one literal is itself; two or more bytes or str literals are one " ++
      "Constant of the concatenation with the first's kind; with an f-string, a JoinedStr of " ++
      "_build_concatenated_str."
    source := "Parser/action_helpers.c:1688-1785, 1943-2029; reference: string literal concatenation"
    status := .proven
    prop := ``ConcatenateStrings
    thm := some ``concatenateStrings_proven
    notes := "_build_concatenated_bytes' size-overflow MemoryError (3.15) is allocation, out of scope." },
  { id := "pygrammar-peg-concatenate-tstrings"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_concatenate_tstrings
    statement := "_PyPegen_concatenate_tstrings is the TemplateStr of _build_concatenated_str; for " ++
      "the same parts it is the f-string JoinedStr with the constructor changed."
    source := "Parser/action_helpers.c:1956-1968"
    status := .proven
    prop := ``ConcatenateTstrings
    thm := some ``concatenateTstrings_proven },
  { id := "pygrammar-peg-concat-folds"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_concat_folds
    statement := "_build_concatenated_str keeps the text (characters and nodes, in order), folds " ++
      "every run of adjacent constants into one, and leaves no empty str constant."
    source := "Parser/action_helpers.c:1788-1941"
    status := .proven
    prop := ``ConcatFolds
    thm := some ``concatFolds_proven },
  { id := "pygrammar-peg-setup-format-spec"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_setup_format_spec
    statement := "_PyPegen_setup_full_format_spec drops empty constants; none or one constant left " ++
      "is a JoinedStr of it, two or more constants a Constant, anything with a field the " ++
      "JoinedStr of _build_concatenated_str; NULL spec gives NULL."
    source := "Parser/action_helpers.c:1029-1081"
    status := .proven
    prop := ``SetupFullFormatSpec
    thm := some ``setupFullFormatSpec_proven },
  { id := "pygrammar-peg-format-spec-joinedstr"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_format_spec_joinedstr
    statement := "Every format spec _PyPegen_setup_full_format_spec builds is a JoinedStr, as " ++
      "Doc/library/ast.rst documents for FormattedValue and Interpolation."
    source := "Doc/library/ast.rst:319-320, 402-405; python/cpython#122300"
    status := .refuted
    prop := ``FormatSpecIsJoinedStr
    thm := some ``formatSpecIsJoinedStr_refuted
    bug := some "pygrammar-format-spec-constant"
    notes := "Counterexample: the two decoded constants of f'{x:\\N{DIGIT ONE}b}'." },
  { id := "pygrammar-peg-interpolation-conversion"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_interpolation_conversion
    statement := "_get_interpolation_conversion is the conversion name's first character, else " ++
      "'r' for a debug = without a format spec, else -1."
    source := "Parser/action_helpers.c:1526-1541"
    status := .proven
    prop := ``InterpolationConversion
    thm := some ``interpolationConversion_proven },
  { id := "pygrammar-peg-formatted-value-interpolation"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_formatted_value_interpolation
    statement := "_PyPegen_formatted_value and _PyPegen_interpolation build the same node (conversion, " ++
      "format spec, location) inside the same debug wrapper; the Interpolation also keeps the " ++
      "expression text, stripped after a debug =."
    source := "Parser/action_helpers.c:1578-1686"
    status := .proven
    prop := ``FormattedValueInterpolation
    thm := some ``formattedValueInterpolation_proven
    notes := "The inventory has no rows for _PyPegen_formatted_value and _PyPegen_interpolation " ++
      "(one-line definitions it missed), so this entry credits none." },
  { id := "pygrammar-peg-debug-info-source"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_debug_info_source
    statement := "The debug text ends at the conversion name, else just past the format spec's " ++
      "start, else at the field's end, with that token's metadata."
    source := "Parser/action_helpers.c:1589-1603, 1658-1672"
    status := .proven
    prop := ``DebugInfoSource
    thm := some ``debugInfoSource_proven
    notes := "Shared by _PyPegen_formatted_value and _PyPegen_interpolation, which have no rows." },
  { id := "pygrammar-peg-joined-str-parts"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_joined_str_parts
    statement := "_PyPegen_joined_str/_PyPegen_template_str over parts with nothing to decode: the " ++
      "parts in order with debug pairs spliced in, from start to end token; a JoinedStr part that " ++
      "is not a pair raises SystemError \"unexpected JoinedStr (TemplateStr) node without debug " ++
      "data in f-string (t-string) at line N\"."
    source := "Parser/action_helpers.c:1347-1455"
    status := .proven
    prop := ``JoinedStrParts
    thm := some ``joinedStrParts_proven },
  { id := "pygrammar-peg-joined-str-literal"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_joined_str_literal
    statement := "_PyPegen_joined_str/_PyPegen_template_str over one literal part decode its text " ++
      "(raw for an r prefix or no backslash), drop an empty result, and turn a decode error into " ++
      "the SyntaxError of _Pypegen_raise_decode_error_known_location at the part."
    source := "Parser/action_helpers.c:1316-1345, 1347-1455, 1483-1500"
    status := .proven
    prop := ``JoinedStrLiteral
    thm := some ``joinedStrLiteral_proven },
  { id := "pygrammar-peg-fstring-literal-twin"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_fstring_literal_twin
    statement := "The literal text of f'''...''' (rf, t, rt) decodes to the value the plain " ++
      "string '''...''' (r) with the same text has, and fails exactly when it fails."
    source := "the implementation agreeing with itself (f-string vs plain string)"
    status := .proven
    prop := ``FstringLiteralTwin
    thm := some ``fstringLiteralTwin_proven },
  { id := "pygrammar-peg-escape-warning-line"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_escape_warning_line
    statement := "An invalid escape in the text of a plain string and of the same f-string is " ++
      "warned about on the same line."
    source := "the implementation disagreeing with itself; python/cpython#160491's intent"
    status := .refuted
    prop := ``EscapeWarningLineTwin
    thm := some ``escapeWarningLineTwin_refuted
    bug := some "pygrammar-fstring-escape-warning-line"
    notes := "Counterexample run in the kernel: body \\n\\d\\n warns on line 2 in '''...''' and on " ++
      "line 4 in f'''...''', counted from the end token _get_resized_exprs passes." },
  { id := "pygrammar-peg-constant-from-string"
    pyFile := "Parser/action_helpers.c"
    pyFns := Rows.peg_constant_from_string
    statement := "_PyPegen_constant_from_string is the Constant of _PyPegen_parse_string's value at " ++
      "the token, kind 'u' exactly for a lowercase u prefix; a failure is NULL after " ++
      "_Pypegen_raise_decode_error."
    source := "Parser/action_helpers.c:1501-1524"
    status := .proven
    prop := ``ConstantFromString
    thm := some ``constantFromString_proven
    notes := "U\"a\" has no kind (the_str[0] == 'u'), as python/cpython#149267 observed." }
] ++ ruleEntries

end PyLean.PyGrammar.Peg
