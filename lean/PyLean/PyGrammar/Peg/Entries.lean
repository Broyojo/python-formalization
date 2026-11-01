import PyLean.Registry
import PyLean.PyGrammar.RowNames
import PyLean.PyGrammar.Peg.Props
import PyLean.PyGrammar.Peg.Facts

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
    pyFns := ["rule:file", "rule:interactive", "rule:eval", "rule:func_type", "_PyPegen_parse"]
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
  { id := "pygrammar-peg-tokenizer-error-fails"
    pyFile := "Parser/pegen_errors.c"
    pyFns := ["_Pypegen_tokenizer_error"]
    statement := "_Pypegen_tokenizer_error returns -1 from every branch of its switch."
    source := "invariant"
    status := .open
    prop := ``TokenizerErrorIsFailure
    notes := "Stated; the case split over the monadic body is not done." },
  { id := "pygrammar-peg-memo-cache"
    pyFile := "Parser/pegen.c"
    pyFns := ["_PyPegen_update_memo", "_PyPegen_is_memoized"]
    statement := "What _PyPegen_update_memo stores at the current token is what " ++
      "_PyPegen_is_memoized finds there."
    source := "invariant"
    status := .open
    prop := ``MemoReturnsStored
    notes := "Stated; needs Array.modify lemmas through the state monad." },
  { id := "pygrammar-peg-identifier-not-constant"
    pyFile := "Parser/pegen.c"
    pyFns := ["_PyPegen_new_identifier"]
    statement := "No identifier from _PyPegen_new_identifier is None, True or False, after NFKC."
    source := "invariant"
    status := .open
    prop := ``IdentifierNeverConstant
    notes := "Stated; needs List.find? reasoning over the forbidden table." },
  { id := "pygrammar-peg-decimal-value"
    pyFile := "Parser/pegen.c"
    pyFns := ["parsenumber_raw", "parsenumber"]
    statement := "A decimal literal of up to 19 digits, not starting with 0, reads as its value."
    source := "invariant"
    status := .open
    prop := ``DecimalValue
    notes := "Stated. roundToBits, the exact float conversion, has no correctness proof either." },
  { id := "pygrammar-peg-terminates"
    pyFile := "Parser/pegen.c"
    pyFns := ["_PyPegen_run_parser"]
    statement := "For every source, runParser with default fuel does not exhaust its fuel."
    source := "invariant"
    status := .open
    prop := ``ParserTerminates
    notes := "Needs a measure over the whole mutual recursion: position, then rank in the " ++
      "acyclic left-call graph of LeftRecursionGuarded, then the seed loop's strictly growing " ++
      "mark. Nothing short of that is proved." },
  { id := "pygrammar-peg-parser-output-validates"
    pyFile := "Python/ast.c"
    pyFns := ["_PyAST_Validate"]
    statement := "Every tree parseStr returns passes validate."
    source := "invariant: the assert behind Py_DEBUG in _PyPegen_run_parser"
    status := .open
    prop := ``ParserOutputValidates
    notes := "Numerically true on the difftest corpus. Open: needs induction over all actions." }
]

end PyLean.PyGrammar.Peg
