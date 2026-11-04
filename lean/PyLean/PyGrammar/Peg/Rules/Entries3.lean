import PyLean.Registry
import PyLean.PyGrammar.RowNames
import PyLean.PyGrammar.Peg.Rules.Args2
import PyLean.PyGrammar.Peg.Rules.GenexpStar
import PyLean.PyGrammar.Peg.Rules.Invalid3

/-! Registry entries for the parameter rules (`Peg/Rules/Params*.lean`) and `invalid_group`
(`Peg/Rules/Invalid2.lean`), in the scheme of `Entries.lean`. -/

namespace PyLean.PyGrammar.Peg

open PyLean.Registry

private def scheme : String :=
  "Rule-specific: callRule on this rule's data from any entry state (no error, below MAXSTACK), " ++
  "for every result of the sub-rule calls and token reads, given as equations; each alternative " ++
  "after the first starts from the state the failed one left (its ...Fails predicate lists every " ++
  "way it fails without an error) with the mark back. Written from the rule text, not the data, " ++
  "so another order of alternatives, a dropped lookahead or another action fails it."

private def twin : String :=
  " One statement over the rule numbers covers the function rule and its lambda twin; each " ++
  "instance is proven against that rule's data (`_of rfl`)."

def paramEntries : List Entry := [
  { id := "pygrammar-rule-invalid-group"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_invalid_group
    statement := "invalid_group: '(' starred_expression ')' raises \"cannot use starred " ++
      "expression here\" located at the starred expression; once that fails, '(' '**' expression " ++
      "')' raises \"cannot use double starred expression here\" located at the '**' token; both " ++
      "end the rule with NULL and error_indicator set; neither matching gives NULL with the mark " ++
      "back and no error."
    source := "Grammar/python.gram:1428-1432"
    status := .proven
    prop := ``InvalidGroup
    thm := some ``invalidGroup_proven
    notes := scheme ++ " In 3.15 (**a) raises earlier, in tuple's star_named_expression_sequence " ++
      "(\"cannot use dict unpacking here\"); only an operand that is not a bitwise_or, such as " ++
      "(**not a), reaches the second alternative through atom." },
  { id := "pygrammar-rule-param"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_param
    statement := "param: NAME and the optional annotation give arg(name, annotation, NULL) " ++
      "spanning them; no NAME gives NULL with the mark back."
    source := "Grammar/python.gram:377"
    status := .proven
    prop := ``ParamRule
    thm := some ``paramRule_proven
    notes := scheme },
  { id := "pygrammar-rule-param-star-annotation"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_param_star_annotation
    statement := "param_star_annotation: NAME and a mandatory star_annotation give arg(name, " ++
      "annotation, NULL); no NAME, or no star_annotation after it, NULL with the mark back."
    source := "Grammar/python.gram:378"
    status := .proven
    prop := ``ParamStarAnnotation
    thm := some ``paramStarAnnotation_proven
    notes := scheme },
  { id := "pygrammar-rule-lambda-param"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_lambda_param
    statement := "lambda_param: NAME gives arg(name, NULL, NULL) spanning it; no NAME gives NULL " ++
      "with the mark back."
    source := "Grammar/python.gram:964"
    status := .proven
    prop := ``LambdaParam
    thm := some ``lambdaParam_proven
    notes := scheme },
  { id := "pygrammar-rule-lambda-param-no-default"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_lambda_param_no_default
    statement := "lambda_param_no_default: lambda_param ',' gives the parameter; once that fails, " ++
      "lambda_param followed by ':' (not consumed) from the start mark; otherwise NULL with the " ++
      "mark back."
    source := "Grammar/python.gram:955-957"
    status := .proven
    prop := ``LambdaParamNoDefault
    thm := some ``lambdaParamNoDefault_proven
    notes := scheme },
  { id := "pygrammar-rule-param-no-default"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_param_no_default
    statement := "param_no_default: param ',' TYPE_COMMENT? gives the parameter with that type " ++
      "comment (_PyPegen_add_type_comment_to_arg); once that fails, param TYPE_COMMENT? followed " ++
      "by ')' (not consumed); otherwise NULL with the mark back."
    source := "Grammar/python.gram:365-367"
    status := .proven
    prop := ``ParamNoDefaultRule
    thm := some ``paramNoDefaultRule_proven
    notes := scheme ++ " ParamNoDefault 45 49." },
  { id := "pygrammar-rule-param-no-default-star-annotation"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_param_no_default_star_annotation
    statement := "param_no_default_star_annotation: as param_no_default with " ++
      "param_star_annotation for param."
    source := "Grammar/python.gram:368-370"
    status := .proven
    prop := ``ParamNoDefaultStarAnnotationRule
    thm := some ``paramNoDefaultStarAnnotationRule_proven
    notes := scheme ++ " ParamNoDefault 46 50, the same statement as param_no_default." },
  { id := "pygrammar-rule-param-with-default"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_param_with_default
    statement := "param_with_default: param default ',' TYPE_COMMENT? gives NameDefaultPair(the " ++
      "parameter with that type comment, the default); once that fails, param default " ++
      "TYPE_COMMENT? followed by ')'; otherwise NULL with the mark back."
    source := "Grammar/python.gram:371-373"
    status := .proven
    prop := ``ParamWithDefault
    thm := some ``paramWithDefault_proven
    notes := scheme },
  { id := "pygrammar-rule-param-maybe-default"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_param_maybe_default
    statement := "param_maybe_default: as param_with_default with the default optional (NULL in " ++
      "the pair without one)."
    source := "Grammar/python.gram:374-376"
    status := .proven
    prop := ``ParamMaybeDefault
    thm := some ``paramMaybeDefault_proven
    notes := scheme },
  { id := "pygrammar-rule-lambda-param-with-default"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_lambda_param_with_default
    statement := "lambda_param_with_default: lambda_param default ',' gives NameDefaultPair(param, " ++
      "default) with no type comment; once that fails, lambda_param default followed by ':'; " ++
      "otherwise NULL with the mark back."
    source := "Grammar/python.gram:958-960"
    status := .proven
    prop := ``LambdaParamWithDefault
    thm := some ``lambdaParamWithDefault_proven
    notes := scheme },
  { id := "pygrammar-rule-lambda-param-maybe-default"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_lambda_param_maybe_default
    statement := "lambda_param_maybe_default: as lambda_param_with_default with the default " ++
      "optional."
    source := "Grammar/python.gram:961-963"
    status := .proven
    prop := ``LambdaParamMaybeDefault
    thm := some ``lambdaParamMaybeDefault_proven
    notes := scheme },
  { id := "pygrammar-rule-slash-no-default"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_slash_no_default
    statement := "slash_no_default: param_no_default+ '/' ',' gives the loop's sequence; once that " ++
      "fails, param_no_default+ '/' followed by ')' from the start mark; otherwise NULL with the " ++
      "mark back; the + loop _loop1_29 by induction."
    source := "Grammar/python.gram:331-333"
    status := .proven
    prop := ``SlashNoDefaultRule
    thm := some ``slashNoDefaultRule_proven
    notes := scheme ++ twin },
  { id := "pygrammar-rule-lambda-slash-no-default"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_lambda_slash_no_default
    statement := "lambda_slash_no_default: as slash_no_default over lambda_param_no_default+ " ++
      "(_loop1_74) with ':' for ')'."
    source := "Grammar/python.gram:935-937"
    status := .proven
    prop := ``LambdaSlashNoDefaultRule
    thm := some ``lambdaSlashNoDefaultRule_proven
    notes := scheme ++ twin },
  { id := "pygrammar-rule-slash-with-default"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_slash_with_default
    statement := "slash_with_default: param_no_default* param_with_default+ '/' ',' gives " ++
      "SlashWithDefault(the two sequences); once that fails, the loops and '/' followed by ')' " ++
      "from the start mark; otherwise NULL with the mark back; the loops _loop0_27 and _loop1_30 " ++
      "by induction (the * loop gives the empty sequence with no round)."
    source := "Grammar/python.gram:334-336"
    status := .proven
    prop := ``SlashWithDefaultRule
    thm := some ``slashWithDefaultRule_proven
    notes := scheme ++ twin },
  { id := "pygrammar-rule-lambda-slash-with-default"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_lambda_slash_with_default
    statement := "lambda_slash_with_default: as slash_with_default over the lambda parameters " ++
      "(_loop0_72, _loop1_75) with ':' for ')'."
    source := "Grammar/python.gram:939-941"
    status := .proven
    prop := ``LambdaSlashWithDefaultRule
    thm := some ``lambdaSlashWithDefaultRule_proven
    notes := scheme ++ twin },
  { id := "pygrammar-rule-kwds"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_kwds
    statement := "kwds: in the second pass invalid_kwds first (its result, NULL on its error); " ++
      "then '**' param_no_default gives the parameter; no '**' or no parameter NULL with the mark " ++
      "back."
    source := "Grammar/python.gram:348-350"
    status := .proven
    prop := ``KwdsRule
    thm := some ``kwdsRule_proven
    notes := scheme ++ twin },
  { id := "pygrammar-rule-lambda-kwds"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_lambda_kwds
    statement := "lambda_kwds: as kwds with invalid_lambda_kwds and lambda_param_no_default."
    source := "Grammar/python.gram:951-953"
    status := .proven
    prop := ``LambdaKwdsRule
    thm := some ``lambdaKwdsRule_proven
    notes := scheme ++ twin },
  { id := "pygrammar-rule-star-etc"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_star_etc
    statement := "star_etc: in the second pass invalid_star_etc first; then '*' param_no_default " ++
      "param_maybe_default* [kwds] gives StarEtc(vararg, kwonly, kwarg); then the same with " ++
      "param_no_default_star_annotation; then '*' ',' param_maybe_default+ [kwds] gives " ++
      "StarEtc(NULL, kwonly, kwarg); then kwds alone StarEtc(NULL, NULL, kwarg); otherwise NULL " ++
      "with the mark back; the loops by induction."
    source := "Grammar/python.gram:338-346"
    status := .proven
    prop := ``StarEtcRule
    thm := some ``starEtcRule_proven
    notes := scheme },
  { id := "pygrammar-rule-lambda-star-etc"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_lambda_star_etc
    statement := "lambda_star_etc: as star_etc without the star_annotation alternative, over the " ++
      "lambda sub-rules."
    source := "Grammar/python.gram:943-949"
    status := .proven
    prop := ``LambdaStarEtcRule
    thm := some ``lambdaStarEtcRule_proven
    notes := scheme },
  { id := "pygrammar-rule-parameters"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_parameters
    statement := "parameters: in order, slash_no_default param_no_default* param_with_default* " ++
      "[star_etc] and slash_with_default param_with_default* [star_etc] give " ++
      "_PyPegen_make_arguments behind CHECK_VERSION 8 (below it NULL with \"Positional-only " ++
      "parameters are only supported in Python 3.8 and greater\"); then param_no_default+ " ++
      "param_with_default* [star_etc]; param_with_default+ [star_etc]; star_etc; each from the " ++
      "start mark with the arguments in their make_arguments slots; otherwise NULL with the mark " ++
      "back; the loops by induction."
    source := "Grammar/python.gram:318-327"
    status := .proven
    prop := ``ParametersRule
    thm := some ``parametersRule_proven
    notes := scheme ++ twin },
  { id := "pygrammar-rule-lambda-parameters"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_lambda_parameters
    statement := "lambda_parameters: as parameters over the lambda sub-rules."
    source := "Grammar/python.gram:925-933"
    status := .proven
    prop := ``LambdaParametersRule
    thm := some ``lambdaParametersRule_proven
    notes := scheme ++ twin },
  { id := "pygrammar-rule-params"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_params
    statement := "params: invalid_parameters | parameters: the first pass gives parameters' " ++
      "result; the second invalid_parameters first (its result; NULL on its error), then " ++
      "parameters from the start mark."
    source := "Grammar/python.gram:314-316"
    status := .proven
    prop := ``ParamsRule
    thm := some ``paramsRule_proven
    notes := scheme ++ twin },
  { id := "pygrammar-rule-lambda-params"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_lambda_params
    statement := "lambda_params: invalid_lambda_parameters | lambda_parameters, as params."
    source := "Grammar/python.gram:917-919"
    status := .proven
    prop := ``LambdaParamsRule
    thm := some ``lambdaParamsRule_proven
    notes := scheme ++ twin },
  { id := "pygrammar-rule-star-named-expression-sequence"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_star_named_expression_sequence
    statement := "star_named_expression_sequence (3.15): invalid_starred_expression_unpacking_sequence " ++
      "| star_named_expression: the first pass gives star_named_expression's result; the second " ++
      "the invalid rule first (its result; NULL on its error), then star_named_expression from the " ++
      "start mark."
    source := "Grammar/python.gram:749-751"
    status := .proven
    prop := ``StarNamedExpressionSequenceRule
    thm := some ``starNamedExpressionSequenceRule_proven
    notes := scheme ++ " InvOr 117 267 116, the statement params uses." }
]

def compEntries : List Entry := [
  { id := "pygrammar-rule-star-named-expressions"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_star_named_expressions
    statement := "star_named_expressions: ','.star_named_expression+ [','] gives the gather's " ++
      "sequence (a trailing ',' read and dropped); no element NULL with the mark back; the gather " ++
      "_gather_58 by induction (every element in order, a trailing ',' left unread by the loop)."
    source := "Grammar/python.gram:741"
    status := .proven
    prop := ``StarNamedExpressionsRule
    thm := some ``starNamedExpressionsRule_proven
    notes := scheme ++ " GatherOptComma 114 335 and GatherSep." },
  { id := "pygrammar-rule-star-named-expressions-sequence"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_star_named_expressions_sequence
    statement := "star_named_expressions_sequence (3.15): as star_named_expressions over " ++
      "star_named_expression_sequence (_gather_60)."
    source := "Grammar/python.gram:743"
    status := .proven
    prop := ``StarNamedExpressionsSequenceRule
    thm := some ``starNamedExpressionsSequenceRule_proven
    notes := scheme ++ " GatherOptComma 115 337 and GatherSep." },
  { id := "pygrammar-rule-double-starred-kvpairs"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_double_starred_kvpairs
    statement := "double_starred_kvpairs: ','.double_starred_kvpair+ [','] gives the gather's " ++
      "sequence; no pair NULL with the mark back; the gather _gather_86 by induction."
    source := "Grammar/python.gram:1036"
    status := .proven
    prop := ``DoubleStarredKvpairsRule
    thm := some ``doubleStarredKvpairsRule_proven
    notes := scheme ++ " GatherOptComma 178 363 and GatherSep." },
  { id := "pygrammar-rule-kvpair"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_kvpair
    statement := "kvpair: expression ':' expression gives the KeyValuePair record (key, value); " ++
      "a missing key, ':' or value gives NULL with the mark back."
    source := "Grammar/python.gram:1042"
    status := .proven
    prop := ``Kvpair
    thm := some ``kvpair_proven
    notes := scheme },
  { id := "pygrammar-rule-double-starred-kvpair"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_double_starred_kvpair
    statement := "double_starred_kvpair: '**' bitwise_or gives the record (NULL, value); once " ++
      "that fails, kvpair from the start mark."
    source := "Grammar/python.gram:1038-1040"
    status := .proven
    prop := ``DoubleStarredKvpair
    thm := some ``doubleStarredKvpair_proven
    notes := scheme },
  { id := "pygrammar-rule-dict"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_dict
    statement := "dict: '{' [double_starred_kvpairs] '}' gives Dict(keys, values) (NULL keys for " ++
      "'**' items, {} empty); once that fails, '{' invalid_double_starred_kvpairs '}' from the " ++
      "start mark (not guarded by call_invalid_rules, so it runs in the first pass) gives the " ++
      "dummy name; another token NULL with the mark back."
    source := "Grammar/python.gram:1028-1034"
    status := .proven
    prop := ``DictRule
    thm := some ``dictRule_proven
    notes := scheme },
  { id := "pygrammar-rule-listcomp"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_listcomp
    statement := "listcomp: '[' star_named_expression for_if_clauses ']' gives ListComp(elt, " ++
      "generators); once that fails, NULL with the mark back in the first pass; in the second an " ++
      "error already set gives NULL, otherwise invalid_comprehension from the start mark."
    source := "Grammar/python.gram:1058-1060"
    status := .proven
    prop := ``ListcompRule
    thm := some ``listcompRule_proven
    notes := scheme ++ " CompRule 183 9 116 10 ListComp; one statement for listcomp, setcomp, " ++
      "genexp, each proven against its rule's data." },
  { id := "pygrammar-rule-setcomp"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_setcomp
    statement := "setcomp: as listcomp with '{' '}' and SetComp."
    source := "Grammar/python.gram:1062-1064"
    status := .proven
    prop := ``SetcompRule
    thm := some ``setcompRule_proven
    notes := scheme ++ " CompRule 184 25 116 26 SetComp." },
  { id := "pygrammar-rule-genexp"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_genexp
    statement := "genexp: as listcomp with '(' ')' and GeneratorExp, the element " ++
      "_tmp_89 = assignment_expression | expression !':=' | starred_expression (so '*' takes any " ++
      "expression here, as in a call argument)."
    source := "Grammar/python.gram:1066-1068"
    status := .proven
    prop := ``GenexpRule
    thm := some ``genexpRule_proven
    notes := scheme ++ " CompRule 185 7 366 8 GeneratorExp and Tmp89." },
  { id := "pygrammar-rule-dictcomp"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_dictcomp
    statement := "dictcomp: '{' kvpair for_if_clauses '}' gives DictComp(key, value, generators) " ++
      "from the pair; once that fails, '{' '**' expression for_if_clauses '}' from the start mark " ++
      "gives DictComp(a, NULL, generators); otherwise NULL with the mark back."
    source := "Grammar/python.gram:1070-1072"
    status := .proven
    prop := ``Dictcomp
    thm := some ``dictcomp_proven
    notes := scheme },
  { id := "pygrammar-rule-for-if-clauses"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_for_if_clauses
    statement := "for_if_clauses: the for_if_clause+ loop's sequence; no clause NULL with the mark " ++
      "back; the loop _loop1_87 by induction."
    source := "Grammar/python.gram:1047-1048"
    status := .proven
    prop := ``ForIfClausesRule
    thm := some ``forIfClausesRule_proven
    notes := scheme },
  { id := "pygrammar-rule-for-if-clause"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_for_if_clause
    statement := "for_if_clause: 'async' 'for' star_targets 'in' ~ disjunction ('if' " ++
      "disjunction)* gives comprehension(target, iter, ifs, 1) behind CHECK_VERSION 6 (\"Async " ++
      "comprehensions are only supported in Python 3.6 and greater\"); a failure after the cut " ++
      "ends the rule with NULL; then the same without 'async' gives comprehension(..., 0), same " ++
      "cut; once both fail before their cuts, NULL in the first pass, invalid_for_if_clause then " ++
      "invalid_for_target in the second; the 'if' loop and its group stated with it."
    source := "Grammar/python.gram:1050-1056"
    status := .proven
    prop := ``ForIfClauseRule
    thm := some ``forIfClauseRule_proven
    notes := scheme ++ " The pass flag of the second invalid_ alternative is read from the state " ++
      "the first left." },
  { id := "pygrammar-rule-expressions"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_expressions
    statement := "expressions: expression (',' expression)+ [','] gives Tuple([a] + rest, Load); " ++
      "once that fails, expression ',' gives Tuple([a], Load); then expression alone; otherwise " ++
      "NULL with the mark back; the + loop _loop1_55 and its group stated with it."
    source := "Grammar/python.gram:710-714"
    status := .proven
    prop := ``ExpressionsRuleFull
    thm := some ``expressionsRuleFull_proven
    notes := scheme }
]

def argEntries : List Entry := [
  { id := "pygrammar-rule-starred-expression"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_starred_expression
    statement := "starred_expression: in the second pass invalid_starred_expression_unpacking " ++
      "first (its result; NULL on its error); then '*' expression gives Starred(a, Load); once " ++
      "that fails, NULL with the mark back in the first pass and invalid_starred_expression from " ++
      "the start mark in the second."
    source := "Grammar/python.gram:1094-1097"
    status := .proven
    prop := ``StarredExpression
    thm := some ``starredExpression_proven
    notes := scheme },
  { id := "pygrammar-rule-kwarg-or-starred"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_kwarg_or_starred
    statement := "kwarg_or_starred: in the second pass invalid_kwarg first; then NAME '=' " ++
      "expression gives KeywordOrStarred(keyword(name, value), 1); once that fails, " ++
      "starred_expression gives KeywordOrStarred(it, 0); otherwise NULL with the mark back."
    source := "Grammar/python.gram:1099-1103"
    status := .proven
    prop := ``KwargOrStarred
    thm := some ``kwargOrStarred_proven
    notes := scheme },
  { id := "pygrammar-rule-kwarg-or-double-starred"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_kwarg_or_double_starred
    statement := "kwarg_or_double_starred: as kwarg_or_starred, the last alternative '**' " ++
      "expression giving KeywordOrStarred(keyword(NULL, value), 1)."
    source := "Grammar/python.gram:1105-1110"
    status := .proven
    prop := ``KwargOrDoubleStarred
    thm := some ``kwargOrDoubleStarred_proven
    notes := scheme },
  { id := "pygrammar-rule-kwargs"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_kwargs
    statement := "kwargs: ','.kwarg_or_starred+ ',' ','.kwarg_or_double_starred+ gives the two " ++
      "sequences joined; then the first gather alone; then the second; otherwise NULL with the " ++
      "mark back; both gathers by induction."
    source := "Grammar/python.gram:1089-1092"
    status := .proven
    prop := ``KwargsRule
    thm := some ``kwargsRule_proven
    notes := scheme },
  { id := "pygrammar-rule-args"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_args
    statement := "args: the positional gather and an optional ', kwargs' give " ++
      "_PyPegen_collect_call_seqs(a, b, EXTRA); once that fails, kwargs alone gives the dummy " ++
      "Call with its starred items as args and its keywords as keywords; otherwise NULL with the " ++
      "mark back; the gather, its element groups (_tmp_167, _tmp_178) and ', kwargs' stated with it."
    source := "Grammar/python.gram:1081-1087"
    status := .proven
    prop := ``ArgsRuleFull
    thm := some ``argsRuleFull_proven
    notes := scheme ++ " The kwargs clause assumes no exception pending (errOccurred = false), " ++
      "under which CHECK_NULL_ALLOWED of an empty part raises nothing." },
  { id := "pygrammar-rule-arguments"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_arguments
    statement := "arguments (memo): args [','] followed by ')' (not consumed) gives args' Call; " ++
      "once that fails, NULL in the first pass, invalid_arguments in the second; memoized at the " ++
      "start mark."
    source := "Grammar/python.gram:1077-1079"
    status := .proven
    prop := ``Arguments
    thm := some ``arguments_proven
    notes := scheme },
  { id := "pygrammar-rule-type-params"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_type_params
    statement := "type_params: in the second pass invalid_type_params first; then '[' " ++
      "type_param_seq ']' gives the sequence behind CHECK_VERSION 12 (\"Type parameter lists are " ++
      "only supported in Python 3.12 and greater\"); otherwise NULL with the mark back."
    source := "Grammar/python.gram:688-691"
    status := .proven
    prop := ``TypeParams
    thm := some ``typeParams_proven
    notes := scheme },
  { id := "pygrammar-rule-type-param-seq"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_type_param_seq
    statement := "type_param_seq: ','.type_param+ [','] gives the gather's sequence; the gather " ++
      "_gather_54 by induction."
    source := "Grammar/python.gram:693"
    status := .proven
    prop := ``TypeParamSeqRule
    thm := some ``typeParamSeqRule_proven
    notes := scheme },
  { id := "pygrammar-rule-type-param"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_type_param
    statement := "type_param (memo): NAME [type_param_bound] [type_param_default] gives " ++
      "TypeVar(name, bound, default); with no NAME, invalid_type_param in the second pass, then " ++
      "'*' NAME [type_param_starred_default] gives TypeVarTuple(name, default), then '**' NAME " ++
      "[type_param_default] ParamSpec(name, default); otherwise NULL with the mark back; memoized."
    source := "Grammar/python.gram:695-699"
    status := .proven
    prop := ``TypeParam
    thm := some ``typeParam_proven
    notes := scheme },
  { id := "pygrammar-rule-type-param-bound"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_type_param_bound
    statement := "type_param_bound: ':' expression gives the expression; another token or no " ++
      "expression NULL with the mark back."
    source := "Grammar/python.gram:701"
    status := .proven
    prop := ``TypeParamBoundRule
    thm := some ``typeParamBoundRule_proven
    notes := scheme ++ " TokThen 105 11 109." },
  { id := "pygrammar-rule-type-param-default"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_type_param_default
    statement := "type_param_default: '=' expression gives the expression behind CHECK_VERSION 13 " ++
      "(\"Type parameter defaults are only supported in Python 3.13 and greater\"); another token " ++
      "or no expression NULL with the mark back."
    source := "Grammar/python.gram:702-703"
    status := .proven
    prop := ``TypeParamDefaultRule
    thm := some ``typeParamDefaultRule_proven
    notes := scheme ++ " TokThenCV 106 22 109 13, proven against the rule's data." },
  { id := "pygrammar-rule-type-param-starred-default"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_type_param_starred_default
    statement := "type_param_starred_default: '=' star_expression, as type_param_default."
    source := "Grammar/python.gram:704-705"
    status := .proven
    prop := ``TypeParamStarredDefaultRule
    thm := some ``typeParamStarredDefaultRule_proven
    notes := scheme ++ " TokThenCV 107 22 113 13." }
]

def findingEntries : List Entry := [
  { id := "pygrammar-rule-genexp-like-listcomp"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_genexp_like_listcomp
    statement := "For every element text e, (e for x in y) parses exactly when [e for x in y] " ++
      "does (the reference: generator expressions have the syntax of list comprehensions)."
    source := "Doc/reference/expressions.rst, Generator expressions; the implementation against itself"
    status := .refuted
    prop := ``GenexpLikeListcomp
    thm := some ``genexpLikeListcomp_refuted
    bug := some "pygrammar-genexp-star-precedence"
    notes := "Counterexample run in the kernel: e = '*a or b'. genexp's element ends in " ++
      "starred_expression ('*' expression), listcomp's star_named_expression ('*' bitwise_or)." }
]

private def cmpEntry (id : String) (fns : List String) (name tok op line : String) (prop thm : Lean.Name) : Entry :=
  { id := id
    pyFile := "Grammar/python.gram"
    pyFns := fns
    statement := name ++ ": " ++ tok ++ " bitwise_or gives the CmpopExprPair record (" ++ op ++
      ", operand); another token, or no bitwise_or after it, NULL with the mark back."
    source := "Grammar/python.gram:" ++ line
    status := .proven
    prop := prop
    thm := some thm
    notes := scheme ++ " One statement (CmpPair / CmpPair2) over the token and operator, proven " ++
      "against each rule's data." }

def cmpEntries : List Entry := [
  { id := "pygrammar-rule-compare-op-bitwise-or-pair"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_compare_op_bitwise_or_pair
    statement := "compare_op_bitwise_or_pair: the ordered choice of eq, noteq, lte, invalid_noteq " ++
      "(second pass only), lt, gte, gt, notin, in, isnot, is (_bitwise_or rules), each from the " ++
      "start mark."
    source := "Grammar/python.gram:793-804"
    status := .proven
    prop := ``CompareOpPair
    thm := some ``compareOpPair_proven
    notes := scheme ++ " choiceResG: choice_run with invalid_ alternatives skipped by the pass flag " ++
      "of the state reached, by induction on the alternatives." },
  cmpEntry "pygrammar-rule-eq-bitwise-or" Rows.rule_eq_bitwise_or "eq_bitwise_or" "'=='" "Eq" "806"
    ``EqBitwiseOr ``eqBitwiseOr_proven,
  cmpEntry "pygrammar-rule-lte-bitwise-or" Rows.rule_lte_bitwise_or "lte_bitwise_or" "'<='" "LtE" "809"
    ``LteBitwiseOr ``lteBitwiseOr_proven,
  cmpEntry "pygrammar-rule-lt-bitwise-or" Rows.rule_lt_bitwise_or "lt_bitwise_or" "'<'" "Lt" "810"
    ``LtBitwiseOr ``ltBitwiseOr_proven,
  cmpEntry "pygrammar-rule-gte-bitwise-or" Rows.rule_gte_bitwise_or "gte_bitwise_or" "'>='" "GtE" "811"
    ``GteBitwiseOr ``gteBitwiseOr_proven,
  cmpEntry "pygrammar-rule-gt-bitwise-or" Rows.rule_gt_bitwise_or "gt_bitwise_or" "'>'" "Gt" "812"
    ``GtBitwiseOr ``gtBitwiseOr_proven,
  cmpEntry "pygrammar-rule-notin-bitwise-or" Rows.rule_notin_bitwise_or "notin_bitwise_or" "'not' 'in'"
    "NotIn" "813" ``NotinBitwiseOr ``notinBitwiseOr_proven,
  cmpEntry "pygrammar-rule-in-bitwise-or" Rows.rule_in_bitwise_or "in_bitwise_or" "'in'" "In" "814"
    ``InBitwiseOr ``inBitwiseOr_proven,
  cmpEntry "pygrammar-rule-isnot-bitwise-or" Rows.rule_isnot_bitwise_or "isnot_bitwise_or" "'is' 'not'"
    "IsNot" "815" ``IsnotBitwiseOr ``isnotBitwiseOr_proven,
  cmpEntry "pygrammar-rule-is-bitwise-or" Rows.rule_is_bitwise_or "is_bitwise_or" "'is'" "Is" "816"
    ``IsBitwiseOr ``isBitwiseOr_proven,
  { id := "pygrammar-rule-noteq-bitwise-or"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_noteq_bitwise_or
    statement := "noteq_bitwise_or: the operator group and bitwise_or give (NotEq, operand); the " ++
      "group _tmp_64 takes NOTEQUAL: without barry_as_FLUFL '!=' is the operator and '<>' gives " ++
      "NULL with no error; with it '<>' is the operator and '!=' raises \"with Barry as BDFL, use " ++
      "'<>' instead of '!='\" and gives NULL with error_indicator set (an error return, so no " ++
      "later comparison operator is tried)."
    source := "Grammar/python.gram:807-808; Parser/action_helpers.c:934-948"
    status := .proven
    prop := ``NoteqBitwiseOrRule
    thm := some ``noteqBitwiseOrRule_proven
    notes := scheme ++ " The '<>' without barry clause assumes no exception pending." }
]

def invalid3Entries : List Entry := [
  { id := "pygrammar-rule-invalid-starred-expression-unpacking"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_invalid_starred_expression_unpacking
    statement := "invalid_starred_expression_unpacking (3.15): '*' if_expression raises \"invalid " ++
      "starred expression. Did you forget to wrap the conditional expression in parentheses?\" " ++
      "over '*' .. the conditional; once that fails, '*' expression '=' expression raises " ++
      "\"cannot assign to iterable argument unpacking\" over '*' .. the value; both end with NULL " ++
      "and error_indicator set; otherwise NULL with the mark back."
    source := "Grammar/python.gram:1577-1580"
    status := .proven
    prop := ``InvalidStarredExpressionUnpacking
    thm := some ``invalidStarredExpressionUnpacking_proven
    notes := scheme ++ " raisedAt: RAISE_SYNTAX_ERROR_KNOWN_RANGE's exception state and error return." },
  { id := "pygrammar-rule-invalid-starred-expression-unpacking-sequence"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_invalid_starred_expression_unpacking_sequence
    statement := "invalid_starred_expression_unpacking_sequence (3.15): '**' bitwise_or raises " ++
      "\"cannot use dict unpacking here\" at the '**' token; once that fails, " ++
      "invalid_starred_expression_unpacking from the start mark in the second pass; otherwise " ++
      "NULL with the mark back."
    source := "Grammar/python.gram:1581-1584"
    status := .proven
    prop := ``InvalidStarredExpressionUnpackingSequence
    thm := some ``invalidStarredExpressionUnpackingSequence_proven
    notes := scheme },
  { id := "pygrammar-rule-invalid-default"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_invalid_default
    statement := "invalid_default: '=' followed by ')' or ',' (not consumed) raises \"expected " ++
      "default value expression\" at the '='; otherwise NULL with the mark back (so a lambda's " ++
      "'a=:' is not diagnosed: ':' is neither)."
    source := "Grammar/python.gram:1373-1374"
    status := .proven
    prop := ``InvalidDefaultRule
    thm := some ``invalidDefaultRule_proven
    notes := scheme ++ " Tmp126 pins the lookahead group _tmp_126 (r403) to ')' | ','." }
]

end PyLean.PyGrammar.Peg
