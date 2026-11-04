import PyLean.Registry
import PyLean.PyGrammar.RowNames
import PyLean.PyGrammar.Peg.Rules.SpecPos

/-! Registry entries for the rules stated as equations (`Peg/Rules/Spec.lean` and the
`Spec*.lean` files after it). -/

namespace PyLean.PyGrammar.Peg

open PyLean.Registry

private def scheme : String :=
  "Rule-specific equation: callRule on this rule's data, from any entry state (no error, below " ++
  "MAXSTACK), equals specAlts over the rule's alternatives written from its text in " ++
  "Grammar/python.gram (items with their lookaheads and options, the invalid_ guard, and each " ++
  "action as the exception it raises, with class, message and location, or the value it builds). " ++
  "specAlts mirrors handle_alt_normal (guard, error check, mark reset, cut, NULL past the last); " ++
  "runAlts_spec matches it to the data, so reordered alternatives, a dropped item or lookahead, " ++
  "another message, location or node fail it."

/-- An entry for an equation-style rule statement. -/
def specEntry (id : String) (rows : List String) (stmt src : String) (prop thm : Lean.Name)
    (extra : String := "") : Entry :=
  { id := id, pyFile := "Grammar/python.gram", pyFns := rows, statement := stmt, source := src,
    status := .proven, prop := prop, thm := some thm, notes := scheme ++ extra }

def specEntries : List Entry := [
  specEntry "pygrammar-rule-invalid-kwds" Rows.rule_invalid_kwds
    ("invalid_kwds: '**' param '=' raises \"var-keyword parameter cannot have default value\" at " ++
     "the '='; '**' param ',' param, then '**' param ',' ('*'|'**'|'/') raise \"parameters cannot " ++
     "follow var-keyword parameter\" at the parameter or token after the comma.")
    "Grammar/python.gram:1381-1384" ``InvalidKwds ``invalidKwds_proven
    " Tmp129 pins the group _tmp_129 to '*' | '**' | '/'.",
  specEntry "pygrammar-rule-invalid-lambda-kwds" Rows.rule_invalid_lambda_kwds
    ("invalid_lambda_kwds: invalid_kwds with lambda_param: the same three alternatives and " ++
     "messages.")
    "Grammar/python.gram:1409-1412" ``InvalidLambdaKwds ``invalidLambdaKwds_proven
    " One statement (InvalidKwdsOf) over the rule numbers covers both twins.",
  specEntry "pygrammar-rule-invalid-block" Rows.rule_invalid_block
    "invalid_block: NEWLINE not followed by INDENT raises IndentationError \"expected an indented block\"."
    "Grammar/python.gram:1348-1349" ``InvalidBlock ``invalidBlock_proven,
  specEntry "pygrammar-rule-invalid-double-type-comments" Rows.rule_invalid_double_type_comments
    ("invalid_double_type_comments: TYPE_COMMENT NEWLINE TYPE_COMMENT NEWLINE INDENT raises " ++
     "\"Cannot have two type comments on def\".")
    "Grammar/python.gram:1413-1415" ``InvalidDoubleTypeComments ``invalidDoubleTypeComments_proven,
  specEntry "pygrammar-rule-invalid-type-params" Rows.rule_invalid_type_params
    "invalid_type_params: '[' ']' raises \"Type parameter list cannot be empty\" from the ']' on."
    "Grammar/python.gram:1642-1646" ``InvalidTypeParams ``invalidTypeParams_proven,
  specEntry "pygrammar-rule-invalid-noteq" Rows.rule_invalid_noteq
    ("invalid_noteq: '<' '>' adjacent (the first ends where the second starts) raise \"invalid " ++
     "syntax.  Maybe you meant '!=' instead of '<>'?\" over both; apart, the action's NULL without " ++
     "an exception is the result.")
    "Grammar/python.gram:1648-1653; Parser/pegen.h:212-216" ``InvalidNoteq ``invalidNoteq_proven,
  specEntry "pygrammar-rule-invalid-factor" Rows.rule_invalid_factor
    ("invalid_factor: ('+'|'-'|'~') 'not' factor raises \"'not' after an operator must be " ++
     "parenthesized\" over 'not' .. the operand.")
    "Grammar/python.gram:1639-1640" ``InvalidFactor ``invalidFactor_proven
    " Tmp158 pins the operator group.",
  specEntry "pygrammar-rule-invalid-arithmetic" Rows.rule_invalid_arithmetic
    ("invalid_arithmetic: sum ('+'|'-'|'*'|'/'|'%'|'//'|'@') 'not' inversion raises \"'not' after " ++
     "an operator must be parenthesized\" over 'not' .. the operand.")
    "Grammar/python.gram:1637-1638" ``InvalidArithmetic ``invalidArithmetic_proven
    " Tmp157 pins the operator group (no '|', '&', '^', '<<', '>>', '**').",
  specEntry "pygrammar-rule-invalid-starred-expression" Rows.rule_invalid_starred_expression
    "invalid_starred_expression: '*' raises \"Invalid star expression\" at the last token read."
    "Grammar/python.gram:1585-1586" ``InvalidStarredExpression ``invalidStarredExpression_proven,
  specEntry "pygrammar-rule-invalid-if-expression" Rows.rule_invalid_if_expression
    ("invalid_if_expression: disjunction 'if' disjunction 'else' '*' raises \"cannot unpack only " ++
     "part of a conditional expression\" at the '*'; with '**' \"cannot use dict unpacking on only " ++
     "part of a conditional expression\" at the '**'.")
    "Grammar/python.gram:1281-1285" ``InvalidIfExpression ``invalidIfExpression_proven,
  specEntry "pygrammar-rule-invalid-kvpair-unpacking" Rows.rule_invalid_kvpair_unpacking
    ("invalid_kvpair_unpacking (3.15): the five alternatives in order: '**' if_expression, '*' " ++
     "and '**' bitwise_or ':' expression (dictionary key), expression ':' '*' and '**' bitwise_or " ++
     "(dictionary value), each raising its message over the star .. the operand.")
    "Grammar/python.gram:1564-1570" ``InvalidKvpairUnpacking ``invalidKvpairUnpacking_proven,
  specEntry "pygrammar-rule-invalid-kvpair" Rows.rule_invalid_kvpair
    ("invalid_kvpair: expression not followed by ':' raises \"':' expected after dictionary key\" " ++
     "from the key's last column (end column -1 + 1); expression ':' '*' / '**' bitwise_or raise " ++
     "from the star to the end of the line; expression ':' followed by '}' or ',' raises " ++
     "\"expression expected after dictionary key and ':'\" at the ':'.")
    "Grammar/python.gram:1571-1576; Parser/pegen.h:187-200" ``InvalidKvpair ``invalidKvpair_proven
    " Tmp151 pins the lookahead group to '}' | ','.",
  specEntry "pygrammar-rule-invalid-if-stmt" Rows.rule_invalid_if_stmt
    ("invalid_if_stmt: 'if' named_expression NEWLINE raises \"expected ':'\"; 'if' named_expression " ++
     "':' NEWLINE not followed by INDENT raises IndentationError \"expected an indented block after " ++
     "'if' statement on line N\", N the line of the 'if'.")
    "Grammar/python.gram:1531-1534" ``InvalidIfStmt ``invalidIfStmt_proven,
  specEntry "pygrammar-rule-invalid-elif-stmt" Rows.rule_invalid_elif_stmt
    "invalid_elif_stmt: as invalid_if_stmt with 'elif' and \"... after 'elif' statement on line N\"."
    "Grammar/python.gram:1535-1538" ``InvalidElifStmt ``invalidElifStmt_proven,
  specEntry "pygrammar-rule-invalid-else-stmt" Rows.rule_invalid_else_stmt
    ("invalid_else_stmt: 'else' ':' NEWLINE without INDENT raises the IndentationError with the " ++
     "line of 'else'; 'else' ':' block 'elif' raises \"'elif' block follows an 'else' block\".")
    "Grammar/python.gram:1539-1542" ``InvalidElseStmt ``invalidElseStmt_proven,
  specEntry "pygrammar-rule-invalid-while-stmt" Rows.rule_invalid_while_stmt
    "invalid_while_stmt: as invalid_if_stmt with 'while' and \"... after 'while' statement on line N\"."
    "Grammar/python.gram:1543-1546" ``InvalidWhileStmt ``invalidWhileStmt_proven,
  specEntry "pygrammar-rule-invalid-for-stmt" Rows.rule_invalid_for_stmt
    ("invalid_for_stmt: ['async'] 'for' star_targets 'in' star_expressions NEWLINE raises " ++
     "\"expected ':'\"; with ':' NEWLINE and no INDENT the IndentationError with the line of 'for'.")
    "Grammar/python.gram:1547-1550" ``InvalidForStmt ``invalidForStmt_proven,
  specEntry "pygrammar-rule-invalid-def-raw" Rows.rule_invalid_def_raw
    ("invalid_def_raw: a def header ending in ':' NEWLINE without INDENT raises \"expected an " ++
     "indented block after function definition on line N\" (N of 'def'); otherwise a def with " ++
     "forced '(' and ':' and a block gives the dummy result.")
    "Grammar/python.gram:1551-1554" ``InvalidDefRawRule ``invalidDefRawRule_proven
    " Tmp26 pins ['->' expression].",
  specEntry "pygrammar-rule-invalid-class-def-raw" Rows.rule_invalid_class_def_raw
    ("invalid_class_def_raw: 'class' NAME [type_params] ['(' [arguments] ')'] NEWLINE raises " ++
     "\"expected ':'\"; with ':' NEWLINE and no INDENT \"expected an indented block after class " ++
     "definition on line N\".")
    "Grammar/python.gram:1555-1558" ``InvalidClassDefRawRule ``invalidClassDefRawRule_proven
    " Tmp25 pins ['(' [arguments] ')'].",
  specEntry "pygrammar-rule-invalid-try-stmt" Rows.rule_invalid_try_stmt
    ("invalid_try_stmt: the four alternatives in order: no indented block after 'try' " ++
     "(IndentationError with its line), a block followed by neither 'except' nor 'finally', " ++
     "except_block+ then 'except' '*' (range 'except' .. '*'), except_star_block+ then a plain " ++
     "'except' (at the 'except'), the last two \"cannot have both 'except' and 'except*' on the " ++
     "same 'try'\".")
    "Grammar/python.gram:1469-1476" ``InvalidTryStmtRule ``invalidTryStmtRule_proven
    " The groups, block* and the except loops are pinned (Tmp144, Loop0_145, Loop1_36, Loop1_37, Tmp21, Tmp146).",
  specEntry "pygrammar-rule-invalid-except-stmt" Rows.rule_invalid_except_stmt
    ("invalid_except_stmt: 'except' expression ',' expressions 'as' NAME ':' raises \"multiple " ++
     "exception types must be parenthesized when using 'as'\" from the first type on; a missing ':' " ++
     "(with or without a type) \"expected ':'\"; 'except' expression 'as' expression ':' block " ++
     "\"cannot use except statement with <name of target>\" at the target.")
    "Grammar/python.gram:1477-1484" ``InvalidExceptStmtRule ``invalidExceptStmtRule_proven,
  specEntry "pygrammar-rule-invalid-except-star-stmt" Rows.rule_invalid_except_star_stmt
    ("invalid_except_star_stmt: the except* twins of invalid_except_stmt, and 'except' '*' " ++
     "followed by NEWLINE or ':' raises \"expected one or more exception types\".")
    "Grammar/python.gram:1485-1492" ``InvalidExceptStarStmtRule ``invalidExceptStarStmtRule_proven,
  specEntry "pygrammar-rule-invalid-finally-stmt" Rows.rule_invalid_finally_stmt
    "invalid_finally_stmt: 'finally' ':' NEWLINE without INDENT raises the IndentationError with its line."
    "Grammar/python.gram:1493-1495" ``InvalidFinallyStmt ``invalidFinallyStmt_proven,
  specEntry "pygrammar-rule-invalid-except-stmt-indent" Rows.rule_invalid_except_stmt_indent
    ("invalid_except_stmt_indent: 'except' expression ['as' NAME] ':' NEWLINE, then 'except' ':' " ++
     "NEWLINE, without INDENT raise the IndentationError with the line of 'except'.")
    "Grammar/python.gram:1496-1499" ``InvalidExceptStmtIndentRule ``invalidExceptStmtIndentRule_proven,
  specEntry "pygrammar-rule-invalid-except-star-stmt-indent" Rows.rule_invalid_except_star_stmt_indent
    "invalid_except_star_stmt_indent: as invalid_except_stmt_indent for 'except' '*' expression."
    "Grammar/python.gram:1500-1502" ``InvalidExceptStarStmtIndentRule ``invalidExceptStarStmtIndentRule_proven,
  specEntry "pygrammar-rule-invalid-match-stmt" Rows.rule_invalid_match_stmt
    ("invalid_match_stmt: \"match\" subject_expr NEWLINE raises \"expected ':'\" and CHECK_VERSION's " ++
     "NULL sets error_indicator; a match header without INDENT raises the IndentationError; " ++
     "\"case\" patterns guard? ':' block outside a match raises \"case statement must be inside " ++
     "match statement\" over \"case\" .. ':'.")
    "Grammar/python.gram:1503-1510" ``InvalidMatchStmt ``invalidMatchStmt_proven,
  specEntry "pygrammar-rule-invalid-case-block" Rows.rule_invalid_case_block
    ("invalid_case_block: \"case\" patterns guard? NEWLINE raises \"expected ':'\"; with ':' " ++
     "NEWLINE and no INDENT the IndentationError with the line of \"case\".")
    "Grammar/python.gram:1511-1514" ``InvalidCaseBlock ``invalidCaseBlock_proven,
  specEntry "pygrammar-rule-invalid-with-stmt" Rows.rule_invalid_with_stmt
    ("invalid_with_stmt: items then ',' ':' raises \"the last 'with' item has a trailing comma\" " ++
     "at the comma; items, or a parenthesized list, then NEWLINE raise \"expected ':'\".")
    "Grammar/python.gram:1458-1462" ``InvalidWithStmtRule ``invalidWithStmtRule_proven
    " The item gathers and groups are pinned (WithGathers).",
  specEntry "pygrammar-rule-invalid-with-stmt-indent" Rows.rule_invalid_with_stmt_indent
    ("invalid_with_stmt_indent: a with header, plain or parenthesized, ending ':' NEWLINE without " ++
     "INDENT raises the IndentationError with the line of 'with'.")
    "Grammar/python.gram:1463-1467" ``InvalidWithStmtIndentRule ``invalidWithStmtIndentRule_proven,
  specEntry "pygrammar-rule-invalid-with-item" Rows.rule_invalid_with_item
    ("invalid_with_item: expression 'as' expression followed by ',' ')' or ':' runs " ++
     "RAISE_SYNTAX_ERROR_INVALID_TARGET(STAR_TARGETS) on the target: \"cannot assign to <name>\" " ++
     "over its first invalid part, or NULL without an exception when it is a valid target.")
    "Grammar/python.gram:1416-1418; Parser/pegen.h:245-264" ``InvalidWithItemRule ``invalidWithItemRule_proven,
  specEntry "pygrammar-rule-invalid-for-target" Rows.rule_invalid_for_target
    ("invalid_for_target: 'async'? 'for' star_expressions runs " ++
     "RAISE_SYNTAX_ERROR_INVALID_TARGET(FOR_TARGETS) on the target.")
    "Grammar/python.gram:1424-1426; Parser/pegen.h:245-264" ``InvalidForTarget ``invalidForTarget_proven,
  specEntry "pygrammar-rule-invalid-for-if-clause" Rows.rule_invalid_for_if_clause
    ("invalid_for_if_clause: 'async'? 'for' (bitwise_or (',' bitwise_or)* [',']) not followed by " ++
     "'in' raises \"'in' expected after for-loop variables\".")
    "Grammar/python.gram:1420-1422" ``InvalidForIfClauseRule ``invalidForIfClauseRule_proven,
  specEntry "pygrammar-rule-invalid-import-from" Rows.rule_invalid_import_from
    ("invalid_import_from (3.15): 'from' dots dotted_name \"lazy\" 'import' import_from_targets " ++
     "raises \"use 'lazy from ... ' instead of 'from ... lazy import'\" at \"lazy\".")
    "Grammar/python.gram:1447-1450" ``InvalidImportFromRule ``invalidImportFromRule_proven,
  specEntry "pygrammar-rule-invalid-import-from-targets" Rows.rule_invalid_import_from_targets
    ("invalid_import_from_targets: import_from_as_names ',' NEWLINE raises \"trailing comma not " ++
     "allowed without surrounding parentheses\"; a bare NEWLINE \"Expected one or more names after " ++
     "'import'\" from the NEWLINE on.")
    "Grammar/python.gram:1452-1456" ``InvalidImportFromTargets ``invalidImportFromTargets_proven,
  specEntry "pygrammar-rule-invalid-as-pattern" Rows.rule_invalid_as_pattern
    ("invalid_as_pattern: or_pattern 'as' \"_\" raises \"cannot use '_' as a target\"; or_pattern " ++
     "'as' expression \"cannot use <name> as pattern target\", both at the target.")
    "Grammar/python.gram:1515-1519" ``InvalidAsPattern ``invalidAsPattern_proven,
  specEntry "pygrammar-rule-invalid-class-pattern" Rows.rule_invalid_class_pattern
    ("invalid_class_pattern: name_or_attr '(' invalid_class_argument_pattern raises \"positional " ++
     "patterns follow keyword patterns\" from the first to the last of those positional patterns.")
    "Grammar/python.gram:1520-1524" ``InvalidClassPattern ``invalidClassPattern_proven,
  specEntry "pygrammar-rule-invalid-mapping-pattern" Rows.rule_invalid_mapping_pattern
    ("invalid_mapping_pattern (3.15): '{' (items_pattern ',')? double_star_pattern ',' " ++
     "items_pattern ','? '}' raises \"double star pattern must be the last (right-most) subpattern " ++
     "in the mapping pattern\" at the '**' pattern.")
    "Grammar/python.gram:1525-1528" ``InvalidMappingPatternRule ``invalidMappingPatternRule_proven,
  specEntry "pygrammar-rule-invalid-class-argument-pattern" Rows.rule_invalid_class_argument_pattern
    ("invalid_class_argument_pattern: [positional_patterns ','] keyword_patterns ',' " ++
     "positional_patterns gives the positional patterns after the keyword ones.")
    "Grammar/python.gram:1529-1530" ``InvalidClassArgumentPatternRule ``invalidClassArgumentPatternRule_proven,
  specEntry "pygrammar-rule-statements" Rows.rule_statements
    "statements: statement+ (_loop1_2, pinned) gives the statements of each statement, flattened in order."
    "Grammar/python.gram:97" ``StatementsRule ``statementsRule_proven,
  specEntry "pygrammar-rule-single-compound-stmt" Rows.rule_single_compound_stmt
    ("single_compound_stmt: compound_stmt gives the one-statement sequence, through " ++
     "_PyPegen_register_stmts (which, in the second pass, records the statement's start).")
    "Grammar/python.gram:105-107; Parser/action_helpers.c (_PyPegen_register_stmts)"
    ``SingleCompoundStmt ``singleCompoundStmt_proven,
  specEntry "pygrammar-rule-statement-newline" Rows.rule_statement_newline
    ("statement_newline: single_compound_stmt NEWLINE, then simple_stmts, then a NEWLINE alone (one " ++
     "Pass spanning it), then ENDMARKER (NULL from _PyPegen_interactive_exit), in that order.")
    "Grammar/python.gram:109-113" ``StatementNewline ``statementNewline_proven,
  specEntry "pygrammar-rule-simple-stmts" Rows.rule_simple_stmts
    ("simple_stmts: simple_stmt not followed by ';' then NEWLINE gives the one-statement sequence; " ++
     "otherwise ';'.simple_stmt+ [';'] NEWLINE gives the gathered statements.")
    "Grammar/python.gram:115-117" ``SimpleStmts ``simpleStmts_proven
    " The ';' gather _gather_4 is not restated (GatherSep is for ',').",
  specEntry "pygrammar-rule-annotated-rhs" Rows.rule_annotated_rhs
    "annotated_rhs: yield_expr, then star_expressions, each from the start mark."
    "Grammar/python.gram:168" ``AnnotatedRhs ``annotatedRhs_proven,
  specEntry "pygrammar-rule-type-alias" Rows.rule_type_alias
    ("type_alias: \"type\" NAME [type_params] '=' expression gives TypeAlias(name in Store " ++
     "context, params, value) with EXTRA; CHECK on the context, and below feature version 12 " ++
     "\"Type statement is only supported in Python 3.12 and greater\" with error_indicator set.")
    "Grammar/python.gram:680-683" ``TypeAlias ``typeAlias_proven,
  specEntry "pygrammar-rule-star-targets-list-seq" Rows.rule_star_targets_list_seq
    "star_targets_list_seq: ','.star_target+ [','] gives the gathered targets."
    "Grammar/python.gram:1123" ``StarTargetsListSeqRule ``starTargetsListSeqRule_proven
    " Gather99 pins the gather.",
  specEntry "pygrammar-rule-star-targets-tuple-seq" Rows.rule_star_targets_tuple_seq
    ("star_targets_tuple_seq: star_target (',' star_target)+ [','] gives all the targets; then " ++
     "star_target ',' the one-target sequence.")
    "Grammar/python.gram:1125-1127" ``StarTargetsTupleSeqRule ``starTargetsTupleSeqRule_proven,
  specEntry "pygrammar-rule-star-atom" Rows.rule_star_atom
    ("star_atom: NAME in Store context; '(' target_with_star_atom ')' in Store context; '(' " ++
     "[star_targets_tuple_seq] ')' Tuple(Store); '[' [star_targets_list_seq] ']' List(Store), with EXTRA.")
    "Grammar/python.gram:1139-1143" ``StarAtom ``starAtom_proven,
  specEntry "pygrammar-rule-single-subscript-attribute-target" Rows.rule_single_subscript_attribute_target
    ("single_subscript_attribute_target: t_primary '.' NAME and t_primary '[' slices ']', each not " ++
     "followed by t_lookahead, give Attribute and Subscript in Store context with EXTRA.")
    "Grammar/python.gram:1150-1152" ``SingleSubscriptAttributeTarget ``singleSubscriptAttributeTarget_proven,
  specEntry "pygrammar-rule-del-t-atom" Rows.rule_del_t_atom
    "del_t_atom: star_atom's four alternatives with del_target/del_targets and Del context."
    "Grammar/python.gram:1178-1182" ``DelTAtom ``delTAtom_proven,
  specEntry "pygrammar-rule-type-expressions" Rows.rule_type_expressions
    ("type_expressions: the seven alternatives in order, the '*' and '**' expressions appended " ++
     "to the gathered plain ones.")
    "Grammar/python.gram:1188-1203" ``TypeExpressionsRule ``typeExpressionsRule_proven
    " Gather105 pins the gather.",
  specEntry "pygrammar-rule-func-type-comment" Rows.rule_func_type_comment
    ("func_type_comment: NEWLINE TYPE_COMMENT followed by NEWLINE INDENT gives the comment; then, " ++
     "in the second pass only, invalid_double_type_comments; then TYPE_COMMENT.")
    "Grammar/python.gram:1205-1208" ``FuncTypeCommentRule ``funcTypeCommentRule_proven,
  specEntry "pygrammar-rule-expression-without-invalid" Rows.rule_expression_without_invalid
    ("expression_without_invalid: with call_invalid_rules off (restored after), disjunction 'if' " ++
     "disjunction 'else' expression gives IfExp(test, body, orelse) with EXTRA; then disjunction; " ++
     "then lambdef.")
    "Grammar/python.gram:1242-1245" ``ExpressionWithoutInvalid ``expressionWithoutInvalid_proven
]

end PyLean.PyGrammar.Peg
