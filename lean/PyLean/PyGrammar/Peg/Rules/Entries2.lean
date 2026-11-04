import PyLean.Registry
import PyLean.PyGrammar.RowNames
import PyLean.PyGrammar.Peg.Rules.Patterns6

/-! Registry entries for the pattern rules of `Peg/Rules/Patterns2.lean` and after, in the scheme
of `Entries.lean`. -/

namespace PyLean.PyGrammar.Peg

open PyLean.Registry

private def scheme : String :=
  "Rule-specific: callRule on this rule's data from any entry state (no error, below MAXSTACK, " ++
  "mark within the tokens, token under the mark read), for every result of the sub-rule calls " ++
  "and token reads, given as equations. Written from the rule text, not the data, so another " ++
  "order of alternatives, a dropped lookahead or another action fails it."

def patternEntries : List Entry := [
  { id := "pygrammar-rule-literal-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_literal_pattern
    statement := "literal_pattern: signed_number not followed by '+'/'-' (_tmp_41, which takes " ++
      "exactly those two) gives MatchValue(value); once that fails, complex_number gives " ++
      "MatchValue(BinOp); then strings MatchValue(strings); then 'None' 'True' 'False' " ++
      "MatchSingleton of that constant spanning the keyword; any other token NULL with the mark back."
    source := "Grammar/python.gram:533-540"
    status := .proven
    prop := ``LiteralPatternRule
    thm := some ``literalPatternRule_proven
    notes := scheme ++ " Tmp41 (tmp41_proven) states the '+'/'-' group." },
  { id := "pygrammar-rule-literal-expr"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_literal_expr
    statement := "literal_expr: in literal_pattern's order, signed_number !('+'|'-'), " ++
      "complex_number and (behind the STRING/FSTRING_START/TSTRING_START lookahead) strings give " ++
      "the expression itself; 'None' 'True' 'False' give Constant(None/True/False, NULL) " ++
      "spanning the keyword; any other token NULL with the mark back."
    source := "Grammar/python.gram:542-548"
    status := .proven
    prop := ``LiteralExpr
    thm := some ``literalExpr_proven
    notes := scheme },
  { id := "pygrammar-rule-complex-number"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_complex_number
    statement := "complex_number: signed_real_number '+' imaginary_number gives BinOp(real, Add, " ++
      "imag); once that fails with no error, signed_real_number '-' imaginary_number from the " ++
      "start mark gives BinOp(real, Sub, imag); an error in the first (ensure_imaginary " ++
      "raising) gives NULL; both failing NULL with the mark back."
    source := "Grammar/python.gram:550-554"
    status := .proven
    prop := ``ComplexNumber
    thm := some ``complexNumber_proven
    notes := scheme },
  { id := "pygrammar-rule-signed-real-number"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_signed_real_number
    statement := "signed_real_number: real_number is the result; without it, '+' real_number " ++
      "gives UnaryOp(UAdd), '-' real_number UnaryOp(USub); any other token NULL with the mark back."
    source := "Grammar/python.gram:561-564"
    status := .proven
    prop := ``SignedRealNumber
    thm := some ``signedRealNumber_proven
    notes := scheme },
  { id := "pygrammar-rule-real-imaginary-number"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_real_imaginary_number
    statement := "real_number: a NUMBER that is a non-complex Constant is the result, a complex " ++
      "one raises \"real number required in complex literal\" over it; imaginary_number: a " ++
      "complex Constant is the result, any other raises \"imaginary number required in complex " ++
      "literal\"; no NUMBER NULL with the mark back (_PyPegen_ensure_real/_imaginary)."
    source := "Grammar/python.gram:566-570; Parser/action_helpers.c:853-871"
    status := .proven
    prop := ``RealImaginaryNumber
    thm := some ``realImaginaryNumber_proven
    notes := scheme },
  { id := "pygrammar-rule-pattern-capture-target"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_pattern_capture_target
    statement := "pattern_capture_target: with the soft keyword '_' not under the mark, a NAME " ++
      "not followed by '.' '(' '=' (_tmp_43, which takes exactly those three) is the name with " ++
      "Store context; '_', no NAME, or the lookahead holding gives NULL with the mark back."
    source := "Grammar/python.gram:575-577"
    status := .proven
    prop := ``PatternCaptureTargetRule
    thm := some ``patternCaptureTargetRule_proven
    notes := scheme },
  { id := "pygrammar-rule-value-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_value_pattern
    statement := "value_pattern: an attr not followed by '.' '(' '=' gives MatchValue(attr); " ++
      "with the lookahead holding, or no attr, NULL with the mark back."
    source := "Grammar/python.gram:582-583"
    status := .proven
    prop := ``ValuePatternRule
    thm := some ``valuePatternRule_proven
    notes := scheme },
  { id := "pygrammar-rule-star-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_star_pattern
    statement := "star_pattern (memo): '*' pattern_capture_target gives MatchStar(name); without " ++
      "the target, '*' wildcard_pattern MatchStar(NULL); another token or neither NULL with the " ++
      "mark back; the result memoized at the start mark."
    source := "Grammar/python.gram:611-615"
    status := .proven
    prop := ``StarPattern
    thm := some ``starPattern_proven
    notes := scheme },
  { id := "pygrammar-rule-double-star-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_double_star_pattern
    statement := "double_star_pattern: '**' pattern_capture_target gives the target; another " ++
      "token or no target NULL with the mark back."
    source := "Grammar/python.gram:643-644"
    status := .proven
    prop := ``DoubleStarPattern
    thm := some ``doubleStarPattern_proven
    notes := scheme },
  { id := "pygrammar-rule-key-value-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_key_value_pattern
    statement := "key_value_pattern: the key (literal_expr, then attr: _tmp_48 as ordered " ++
      "choice), ':' and pattern give the pair (key, pattern); a missing key, ':' or pattern gives " ++
      "NULL with the mark back."
    source := "Grammar/python.gram:639-641"
    status := .proven
    prop := ``KeyValuePatternRule
    thm := some ``keyValuePatternRule_proven
    notes := scheme },
  { id := "pygrammar-rule-keyword-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_keyword_pattern
    statement := "keyword_pattern: NAME '=' pattern gives the pair (name, pattern); a missing " ++
      "NAME, '=' or pattern gives NULL with the mark back."
    source := "Grammar/python.gram:674-675"
    status := .proven
    prop := ``KeywordPattern
    thm := some ``keywordPattern_proven
    notes := scheme },
  { id := "pygrammar-rule-open-sequence-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_open_sequence_pattern
    statement := "open_sequence_pattern: maybe_star_pattern ',' and the optional " ++
      "maybe_sequence_pattern give the first pattern in front of the rest; no first pattern or " ++
      "no ',' gives NULL with the mark back."
    source := "Grammar/python.gram:600-602"
    status := .proven
    prop := ``OpenSequencePattern
    thm := some ``openSequencePattern_proven
    notes := scheme },
  { id := "pygrammar-rule-maybe-sequence-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_maybe_sequence_pattern
    statement := "maybe_sequence_pattern: the ','.maybe_star_pattern+ gather (all the patterns " ++
      "in source order, each after a ',', a trailing ',' left unread by the gather) and an " ++
      "optional ',' give the sequence; no first pattern NULL with the mark back."
    source := "Grammar/python.gram:604-605"
    status := .proven
    prop := ``MaybeSequencePatternRule
    thm := some ``maybeSequencePatternRule_proven
    notes := scheme ++ " GatherSep: the _gather_ and _loop0_ helpers, the loop by induction on " ++
      "its rounds; hypothesis that the first element's call restores p->level." },
  { id := "pygrammar-rule-items-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_items_pattern
    statement := "items_pattern: the ','.key_value_pattern+ gather, all the pairs in source " ++
      "order; no first pair NULL with the mark back."
    source := "Grammar/python.gram:636-637"
    status := .proven
    prop := ``ItemsPatternRule
    thm := some ``itemsPatternRule_proven
    notes := scheme ++ " GatherSep as for maybe_sequence_pattern." },
  { id := "pygrammar-rule-keyword-patterns"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_keyword_patterns
    statement := "keyword_patterns: the ','.keyword_pattern+ gather, all the pairs in source " ++
      "order; no first pair NULL with the mark back."
    source := "Grammar/python.gram:671-672"
    status := .proven
    prop := ``KeywordPatternsRule
    thm := some ``keywordPatternsRule_proven
    notes := scheme ++ " GatherSep as for maybe_sequence_pattern." },
  { id := "pygrammar-rule-positional-patterns"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_positional_patterns
    statement := "positional_patterns: the ','.pattern+ gather, all the patterns in source " ++
      "order; no first pattern NULL with the mark back."
    source := "Grammar/python.gram:668-669"
    status := .proven
    prop := ``PositionalPatternsRule
    thm := some ``positionalPatternsRule_proven
    notes := scheme ++ " GatherSep as for maybe_sequence_pattern." },
  { id := "pygrammar-rule-guard"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_guard
    statement := "guard: 'if' named_expression gives the expression; another token or no " ++
      "expression NULL with the mark back."
    source := "Grammar/python.gram:502"
    status := .proven
    prop := ``Guard
    thm := some ``guard_proven
    notes := scheme },
  { id := "pygrammar-rule-attr"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_attr
    statement := "attr: the seed loop returns the last seed that grew; each round with seed v " ++
      "gives Attribute(v, NAME.id, Load) after '.' NAME (name_or_attr returning the seed through " ++
      "the memo), the first round Attribute(NAME, NAME.id, Load), so a.b.c groups as (a.b).c; " ++
      "without '.' NAME the round is NULL with the mark back."
    source := "Grammar/python.gram:585-587"
    status := .proven
    prop := ``AttrRule
    thm := some ``attrRule_proven
    notes := scheme ++ " Left-recursive leader: AttrStep is one round from a state whose memo " ++
      "holds the seed, LeaderLoop the seed loop (GrowSeedChain)." },
  { id := "pygrammar-rule-name-or-attr"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_name_or_attr
    statement := "name_or_attr inside a round of attr: with a seed in the memo, the seed, " ++
      "resuming at its end (attr is tried first); with none, the NAME under the mark, NULL with " ++
      "the mark back without one."
    source := "Grammar/python.gram:589-591"
    status := .proven
    prop := ``NameOrAttr
    thm := some ``nameOrAttr_proven
    notes := scheme },
  { id := "pygrammar-rule-as-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_as_pattern
    statement := "as_pattern: or_pattern 'as' pattern_capture_target gives MatchAs(pattern, " ++
      "name); once that fails, NULL with the mark back in the first pass, the result of " ++
      "invalid_as_pattern from the start mark in the second."
    source := "Grammar/python.gram:513-516"
    status := .proven
    prop := ``AsPattern
    thm := some ``asPattern_proven
    notes := scheme ++ " The pass flag is read from the state the failed alternative left." },
  { id := "pygrammar-rule-case-block"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_case_block
    statement := "case_block: \"case\" patterns [guard] ':' block gives match_case(pattern, " ++
      "guard, body); without \"case\" NULL with the mark back; in the second pass " ++
      "invalid_case_block first, its error ending the rule and its NULL leading to the same " ++
      "alternative."
    source := "Grammar/python.gram:497-500"
    status := .proven
    prop := ``CaseBlock
    thm := some ``caseBlock_proven
    notes := scheme },
  { id := "pygrammar-rule-mapping-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_mapping_pattern
    statement := "mapping_pattern: at '{', '}' gives the empty MatchMapping; once that fails, " ++
      "'**' rest [','] '}' MatchMapping(rest=name); then items ',' '**' rest [','] '}' " ++
      "MatchMapping(keys, patterns, rest); then items [','] '}' MatchMapping(keys, patterns), " ++
      "keys and patterns the fields of the items' pairs; each alternative from the '{' again; " ++
      "all failing (or another token) NULL with the mark back in the first pass, the result of " ++
      "invalid_mapping_pattern in the second."
    source := "Grammar/python.gram:617-634"
    status := .proven
    prop := ``MappingPattern
    thm := some ``mappingPattern_proven
    notes := scheme ++ " Each failed alternative is stated through MapA*Fails, which lists every " ++
      "item at which it can fail without an error." },
  { id := "pygrammar-rule-class-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_class_pattern
    statement := "class_pattern: name_or_attr '(' then ')' gives MatchClass(cls); once that fails, " ++
      "positional_patterns [','] ')' MatchClass(cls, patterns); then keyword_patterns [','] ')' " ++
      "MatchClass(cls, [], names of the keyword pairs, their patterns); then positional ',' " ++
      "keyword [','] ')' all four; each alternative from the start mark; all failing NULL with " ++
      "the mark back in the first pass, the result of invalid_class_pattern in the second."
    source := "Grammar/python.gram:646-666"
    status := .proven
    prop := ``ClassPattern
    thm := some ``classPattern_proven
    notes := scheme ++ " Each failed alternative is stated through ClsA*Fails." }
]

end PyLean.PyGrammar.Peg
