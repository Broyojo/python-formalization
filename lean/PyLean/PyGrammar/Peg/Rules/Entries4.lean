import PyLean.Registry
import PyLean.PyGrammar.RowNames
import PyLean.PyGrammar.Peg.Rules.SpecInv1

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
    " Tmp151 pins the lookahead group to '}' | ','."
]

end PyLean.PyGrammar.Peg
