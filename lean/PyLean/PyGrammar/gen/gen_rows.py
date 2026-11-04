#!/usr/bin/env python3
"""Generate lean/PyLean/PyGrammar/RowNames.lean and settle the coverage rows of this module.

A row is `modelled` only if `CREDIT` names it, and `CREDIT` is written by hand, row by row: the
entry's theorem must depend on that function's body. For a refutation that means the function is
on the path the bug takes, not merely run by the counterexample. Everything else is `todo`, even
where the model and the difftest exist. Rows in `EXCLUDE` become `excluded` with the given reason.
Lean gets the names as lists, so `pyFns` in the registry can never disagree with the tsv.
"""

import csv
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
METHODS = ROOT / "coverage" / "methods"
FIELDS = ["file", "line", "endline", "name", "signature", "status", "entry", "note"]
OUT = Path(__file__).resolve().parent.parent / "RowNames.lean"

GENERATED = ("generated: emitted by pegen from Grammar/python.gram; Peg/GrammarData.lean holds the "
             "same rules, checked byte for byte against this file by gen/gen_grammar.py --check")

GRAM = "Grammar__python.gram"

STEMS = [
    "Grammar__python.gram", "Parser__lexer__lexer.c", "Parser__lexer__state.c",
    "Parser__lexer__buffer.c", "Parser__token.c", "Parser__tokenizer__helpers.c",
    "Parser__tokenizer__readline_tokenizer.c", "Parser__tokenizer__string_tokenizer.c",
    "Parser__tokenizer__utf8_tokenizer.c", "Parser__tokenizer__file_tokenizer.c",
    "Parser__myreadline.c", "Python__Python-tokenize.c", "Parser__action_helpers.c",
    "Parser__pegen.c", "Parser__pegen_errors.c", "Parser__string_parser.c", "Parser__peg_api.c",
    "Parser__parser.c", "Lib___ast_unparse.py", "Python__ast_unparse.c", "Lib__tokenize.py",
    "Lib__ast.py", "Lib__token.py", "Python__ast.c", "Python__ast_preprocess.c",
]

# entry -> {file stem: [row names]}
CREDIT = {
    # Rule-specific statements of `Peg/Rules/`.
    "pygrammar-rule-keyword-stmts": {GRAM: ["rule:pass_stmt", "rule:break_stmt",
                                            "rule:continue_stmt"]},
    "pygrammar-rule-return-stmt": {GRAM: ["rule:return_stmt"]},
    "pygrammar-rule-raise-stmt": {GRAM: ["rule:raise_stmt"]},
    "pygrammar-rule-raise-stmt-invalid": {GRAM: ["rule:raise_stmt"]},
    "pygrammar-rule-invalid-raise-stmt": {GRAM: ["rule:invalid_raise_stmt"]},
    "pygrammar-rule-factor": {GRAM: ["rule:factor"]},
    "pygrammar-rule-power": {GRAM: ["rule:power"]},
    "pygrammar-rule-signed-number": {GRAM: ["rule:signed_number"]},
    "pygrammar-rule-yield-expr": {GRAM: ["rule:yield_expr"]},
    "pygrammar-rule-yield-stmt": {GRAM: ["rule:yield_stmt"]},
    "pygrammar-rule-assert-stmt": {GRAM: ["rule:assert_stmt"]},
    "pygrammar-rule-import-name": {GRAM: ["rule:import_name"]},
    "pygrammar-rule-invalid-import": {GRAM: ["rule:invalid_import"]},
    "pygrammar-rule-lazy-import-diagnosed": {GRAM: ["rule:invalid_import"]},
    "pygrammar-rule-file": {GRAM: ["rule:file"]},
    "pygrammar-rule-del-stmt": {GRAM: ["rule:del_stmt"]},
    "pygrammar-rule-augassign": {GRAM: ["rule:augassign"]},
    "pygrammar-rule-del-stmt-invalid": {GRAM: ["rule:del_stmt"]},
    "pygrammar-rule-assert-stmt-invalid": {GRAM: ["rule:assert_stmt"]},
    "pygrammar-rule-for-stmt": {GRAM: ["rule:for_stmt"]},
    "pygrammar-rule-while-stmt": {GRAM: ["rule:while_stmt"]},
    "pygrammar-rule-if-stmt": {GRAM: ["rule:if_stmt"]},
    "pygrammar-rule-else-block": {GRAM: ["rule:else_block"]},
    "pygrammar-rule-block": {GRAM: ["rule:block"]},
    "pygrammar-rule-func-type": {GRAM: ["rule:func_type"]},
    "pygrammar-rule-expression": {GRAM: ["rule:expression"]},
    "pygrammar-rule-star-expressions": {GRAM: ["rule:star_expressions"]},
    "pygrammar-rule-assignment-more": {GRAM: ["rule:assignment"]},
    "pygrammar-rule-compound-stmt-more": {GRAM: ["rule:compound_stmt"]},
    "pygrammar-rule-simple-stmt-more": {GRAM: ["rule:simple_stmt"]},
    "pygrammar-rule-del-stmt-targets": {GRAM: ["rule:del_stmt"]},
    "pygrammar-rule-import-stmt": {GRAM: ["rule:import_stmt"]},
    "pygrammar-rule-import-from": {GRAM: ["rule:import_from"]},
    "pygrammar-rule-assignment-aug": {GRAM: ["rule:assignment"]},
    "pygrammar-rule-assignment-ann-plain": {GRAM: ["rule:assignment"]},
    "pygrammar-rule-assignment-invalid": {GRAM: ["rule:assignment"]},
    "pygrammar-rule-compound-stmt": {GRAM: ["rule:compound_stmt"]},
    "pygrammar-rule-simple-stmt": {GRAM: ["rule:simple_stmt"]},
    "pygrammar-rule-global-nonlocal": {GRAM: ["rule:global_stmt", "rule:nonlocal_stmt"]},
    "pygrammar-rule-inversion": {GRAM: ["rule:inversion"]},
    "pygrammar-rule-comparison": {GRAM: ["rule:comparison"]},
    "pygrammar-rule-await-primary": {GRAM: ["rule:await_primary"]},
    "pygrammar-rule-eval": {GRAM: ["rule:eval"]},
    "pygrammar-rule-interactive": {GRAM: ["rule:interactive"]},
    "pygrammar-rule-statement": {GRAM: ["rule:statement"]},
    "pygrammar-rule-elif-stmt": {GRAM: ["rule:elif_stmt"]},
    "pygrammar-rule-finally-block": {GRAM: ["rule:finally_block"]},
    "pygrammar-rule-try-stmt": {GRAM: ["rule:try_stmt"]},
    "pygrammar-rule-except-block": {GRAM: ["rule:except_block"]},
    "pygrammar-rule-except-star-block": {GRAM: ["rule:except_star_block"]},
    "pygrammar-rule-with-stmt": {GRAM: ["rule:with_stmt"]},
    "pygrammar-rule-async-with-type-comment": {GRAM: ["rule:with_stmt"]},
    "pygrammar-rule-with-item": {GRAM: ["rule:with_item"]},
    "pygrammar-rule-import-from-targets": {GRAM: ["rule:import_from_targets"]},
    "pygrammar-rule-class-def": {GRAM: ["rule:class_def"]},
    "pygrammar-rule-function-def": {GRAM: ["rule:function_def"]},
    "pygrammar-rule-class-def-raw": {GRAM: ["rule:class_def_raw"]},
    "pygrammar-rule-function-def-raw": {GRAM: ["rule:function_def_raw"]},
    "pygrammar-rule-sum": {GRAM: ["rule:sum"]},
    "pygrammar-rule-bitwise-or": {GRAM: ["rule:bitwise_or"]},
    "pygrammar-rule-bitwise-xor": {GRAM: ["rule:bitwise_xor"]},
    "pygrammar-rule-bitwise-and": {GRAM: ["rule:bitwise_and"]},
    "pygrammar-rule-term": {GRAM: ["rule:term"]},
    "pygrammar-rule-shift-expr": {GRAM: ["rule:shift_expr"]},
    "pygrammar-rule-invalid-assert-stmt": {GRAM: ["rule:invalid_assert_stmt"]},
    "pygrammar-rule-primary": {GRAM: ["rule:primary"]},
    "pygrammar-rule-t-primary": {GRAM: ["rule:t_primary"]},
    "pygrammar-rule-t-lookahead": {GRAM: ["rule:t_lookahead"]},
    "pygrammar-rule-atom": {GRAM: ["rule:atom"]},
    "pygrammar-rule-slices": {GRAM: ["rule:slices"]},
    "pygrammar-rule-slice": {GRAM: ["rule:slice"]},
    "pygrammar-rule-star-targets": {GRAM: ["rule:star_targets"]},
    "pygrammar-rule-star-target": {GRAM: ["rule:star_target"]},
    "pygrammar-rule-target-with-star-atom": {GRAM: ["rule:target_with_star_atom"]},
    "pygrammar-rule-del-targets": {GRAM: ["rule:del_targets"]},
    "pygrammar-rule-del-target": {GRAM: ["rule:del_target"]},
    "pygrammar-rule-dotted-name": {GRAM: ["rule:dotted_name"]},
    "pygrammar-rule-join-names": {"Parser__action_helpers.c": ["_PyPegen_join_names_with_dot"]},
    "pygrammar-rule-dotted-as-name": {GRAM: ["rule:dotted_as_name"]},
    "pygrammar-rule-import-from-as-name": {GRAM: ["rule:import_from_as_name"]},
    "pygrammar-rule-as-names": {GRAM: ["rule:import_from_as_names", "rule:dotted_as_names"]},
    "pygrammar-rule-closed-pattern": {GRAM: ["rule:closed_pattern"]},
    "pygrammar-rule-pattern": {GRAM: ["rule:pattern"]},
    "pygrammar-rule-maybe-star-pattern": {GRAM: ["rule:maybe_star_pattern"]},
    "pygrammar-rule-or-pattern": {GRAM: ["rule:or_pattern"]},
    "pygrammar-rule-capture-pattern": {GRAM: ["rule:capture_pattern"]},
    "pygrammar-rule-wildcard-pattern": {GRAM: ["rule:wildcard_pattern"]},
    "pygrammar-rule-group-pattern": {GRAM: ["rule:group_pattern"]},
    "pygrammar-rule-sequence-pattern": {GRAM: ["rule:sequence_pattern"]},
    "pygrammar-rule-patterns": {GRAM: ["rule:patterns"]},
    "pygrammar-rule-subject-expr": {GRAM: ["rule:subject_expr"]},
    "pygrammar-rule-invalid-del-stmt": {GRAM: ["rule:invalid_del_stmt"]},
    "pygrammar-rule-invalid-ann-assign-target": {GRAM: ["rule:invalid_ann_assign_target"]},
    "pygrammar-rule-invalid-assignment": {GRAM: ["rule:invalid_assignment"]},
    "pygrammar-rule-sum-sub-sub": {GRAM: ["rule:sum"]},
    "pygrammar-rule-dotted-as-name-name-target": {GRAM: ["rule:invalid_dotted_as_name"]},
    "pygrammar-rule-import-from-as-name-name-target": {GRAM: ["rule:invalid_import_from_as_name"]},
    "pygrammar-rule-paren-name-target": {GRAM: ["rule:invalid_dotted_as_name"]},
    "pygrammar-rule-invalid-dotted-as-name": {GRAM: ["rule:invalid_dotted_as_name"]},
    "pygrammar-rule-invalid-import-from-as-name": {GRAM: ["rule:invalid_import_from_as_name"]},
    "pygrammar-rule-literal-pattern": {GRAM: ["rule:literal_pattern"]},
    "pygrammar-rule-literal-expr": {GRAM: ["rule:literal_expr"]},
    "pygrammar-rule-complex-number": {GRAM: ["rule:complex_number"]},
    "pygrammar-rule-signed-real-number": {GRAM: ["rule:signed_real_number"]},
    "pygrammar-rule-real-imaginary-number": {GRAM: ["rule:real_number", "rule:imaginary_number"]},
    "pygrammar-rule-pattern-capture-target": {GRAM: ["rule:pattern_capture_target"]},
    "pygrammar-rule-value-pattern": {GRAM: ["rule:value_pattern"]},
    "pygrammar-rule-star-pattern": {GRAM: ["rule:star_pattern"]},
    "pygrammar-rule-double-star-pattern": {GRAM: ["rule:double_star_pattern"]},
    "pygrammar-rule-key-value-pattern": {GRAM: ["rule:key_value_pattern"]},
    "pygrammar-rule-keyword-pattern": {GRAM: ["rule:keyword_pattern"]},
    "pygrammar-rule-open-sequence-pattern": {GRAM: ["rule:open_sequence_pattern"]},
    "pygrammar-rule-maybe-sequence-pattern": {GRAM: ["rule:maybe_sequence_pattern"]},
    "pygrammar-rule-items-pattern": {GRAM: ["rule:items_pattern"]},
    "pygrammar-rule-keyword-patterns": {GRAM: ["rule:keyword_patterns"]},
    "pygrammar-rule-positional-patterns": {GRAM: ["rule:positional_patterns"]},
    "pygrammar-rule-guard": {GRAM: ["rule:guard"]},
    "pygrammar-rule-attr": {GRAM: ["rule:attr"]},
    "pygrammar-rule-name-or-attr": {GRAM: ["rule:name_or_attr"]},
    "pygrammar-rule-as-pattern": {GRAM: ["rule:as_pattern"]},
    "pygrammar-rule-case-block": {GRAM: ["rule:case_block"]},
    "pygrammar-rule-mapping-pattern": {GRAM: ["rule:mapping_pattern"]},
    "pygrammar-rule-class-pattern": {GRAM: ["rule:class_pattern"]},
    "pygrammar-rule-named-expression": {GRAM: ["rule:named_expression"]},
    "pygrammar-rule-assignment-expression": {GRAM: ["rule:assignment_expression"]},
    "pygrammar-rule-star-named-expression": {GRAM: ["rule:star_named_expression"]},
    "pygrammar-rule-star-expression": {GRAM: ["rule:star_expression"]},
    "pygrammar-rule-if-expression": {GRAM: ["rule:if_expression"]},
    "pygrammar-rule-group": {GRAM: ["rule:group"]},
    "pygrammar-rule-lambdef": {GRAM: ["rule:lambdef"]},
    "pygrammar-rule-list": {GRAM: ["rule:list"]},
    "pygrammar-rule-tuple": {GRAM: ["rule:tuple"]},
    "pygrammar-rule-set": {GRAM: ["rule:set"]},
    "pygrammar-rule-single-target": {GRAM: ["rule:single_target"]},
    "pygrammar-rule-disjunction": {GRAM: ["rule:disjunction"]},
    "pygrammar-rule-conjunction": {GRAM: ["rule:conjunction"]},
    "pygrammar-rule-match-stmt": {GRAM: ["rule:match_stmt"]},
    "pygrammar-rule-decorators": {GRAM: ["rule:decorators"]},
    "pygrammar-rule-annotation-default": {GRAM: ["rule:annotation", "rule:star_annotation",
                                                 "rule:default"]},
    "pygrammar-rule-invalid-group": {GRAM: ["rule:invalid_group"]},
    "pygrammar-rule-param": {GRAM: ["rule:param"]},
    "pygrammar-rule-param-star-annotation": {GRAM: ["rule:param_star_annotation"]},
    "pygrammar-rule-lambda-param": {GRAM: ["rule:lambda_param"]},
    "pygrammar-rule-lambda-param-no-default": {GRAM: ["rule:lambda_param_no_default"]},
    "pygrammar-rule-param-no-default": {GRAM: ["rule:param_no_default"]},
    "pygrammar-rule-param-no-default-star-annotation": {
        GRAM: ["rule:param_no_default_star_annotation"]},
    "pygrammar-rule-param-with-default": {GRAM: ["rule:param_with_default"]},
    "pygrammar-rule-param-maybe-default": {GRAM: ["rule:param_maybe_default"]},
    "pygrammar-rule-lambda-param-with-default": {GRAM: ["rule:lambda_param_with_default"]},
    "pygrammar-rule-lambda-param-maybe-default": {GRAM: ["rule:lambda_param_maybe_default"]},
    "pygrammar-rule-slash-no-default": {GRAM: ["rule:slash_no_default"]},
    "pygrammar-rule-lambda-slash-no-default": {GRAM: ["rule:lambda_slash_no_default"]},
    "pygrammar-rule-slash-with-default": {GRAM: ["rule:slash_with_default"]},
    "pygrammar-rule-lambda-slash-with-default": {GRAM: ["rule:lambda_slash_with_default"]},
    "pygrammar-rule-kwds": {GRAM: ["rule:kwds"]},
    "pygrammar-rule-lambda-kwds": {GRAM: ["rule:lambda_kwds"]},
    "pygrammar-rule-star-etc": {GRAM: ["rule:star_etc"]},
    "pygrammar-rule-lambda-star-etc": {GRAM: ["rule:lambda_star_etc"]},
    "pygrammar-rule-parameters": {GRAM: ["rule:parameters"]},
    "pygrammar-rule-lambda-parameters": {GRAM: ["rule:lambda_parameters"]},
    "pygrammar-rule-params": {GRAM: ["rule:params"]},
    "pygrammar-rule-lambda-params": {GRAM: ["rule:lambda_params"]},
    "pygrammar-rule-star-named-expression-sequence": {
        GRAM: ["rule:star_named_expression_sequence"]},
    "pygrammar-rule-star-named-expressions": {GRAM: ["rule:star_named_expressions"]},
    "pygrammar-rule-star-named-expressions-sequence": {
        GRAM: ["rule:star_named_expressions_sequence"]},
    "pygrammar-rule-double-starred-kvpairs": {GRAM: ["rule:double_starred_kvpairs"]},
    "pygrammar-rule-kvpair": {GRAM: ["rule:kvpair"]},
    "pygrammar-rule-double-starred-kvpair": {GRAM: ["rule:double_starred_kvpair"]},
    "pygrammar-rule-dict": {GRAM: ["rule:dict"]},
    "pygrammar-rule-listcomp": {GRAM: ["rule:listcomp"]},
    "pygrammar-rule-setcomp": {GRAM: ["rule:setcomp"]},
    "pygrammar-rule-genexp": {GRAM: ["rule:genexp"]},
    "pygrammar-rule-dictcomp": {GRAM: ["rule:dictcomp"]},
    "pygrammar-rule-for-if-clauses": {GRAM: ["rule:for_if_clauses"]},
    "pygrammar-rule-for-if-clause": {GRAM: ["rule:for_if_clause"]},
    "pygrammar-rule-expressions": {GRAM: ["rule:expressions"]},
    "pygrammar-rule-starred-expression": {GRAM: ["rule:starred_expression"]},
    "pygrammar-rule-kwarg-or-starred": {GRAM: ["rule:kwarg_or_starred"]},
    "pygrammar-rule-kwarg-or-double-starred": {GRAM: ["rule:kwarg_or_double_starred"]},
    "pygrammar-rule-kwargs": {GRAM: ["rule:kwargs"]},
    "pygrammar-rule-args": {GRAM: ["rule:args"]},
    "pygrammar-rule-arguments": {GRAM: ["rule:arguments"]},
    "pygrammar-rule-type-params": {GRAM: ["rule:type_params"]},
    "pygrammar-rule-type-param-seq": {GRAM: ["rule:type_param_seq"]},
    "pygrammar-rule-type-param": {GRAM: ["rule:type_param"]},
    "pygrammar-rule-type-param-bound": {GRAM: ["rule:type_param_bound"]},
    "pygrammar-rule-type-param-default": {GRAM: ["rule:type_param_default"]},
    "pygrammar-rule-type-param-starred-default": {GRAM: ["rule:type_param_starred_default"]},
    "pygrammar-rule-genexp-like-listcomp": {GRAM: ["rule:genexp", "rule:listcomp"]},
    "pygrammar-rule-compare-op-bitwise-or-pair": {GRAM: ["rule:compare_op_bitwise_or_pair"]},
    "pygrammar-rule-eq-bitwise-or": {GRAM: ["rule:eq_bitwise_or"]},
    "pygrammar-rule-noteq-bitwise-or": {GRAM: ["rule:noteq_bitwise_or"]},
    "pygrammar-rule-lte-bitwise-or": {GRAM: ["rule:lte_bitwise_or"]},
    "pygrammar-rule-lt-bitwise-or": {GRAM: ["rule:lt_bitwise_or"]},
    "pygrammar-rule-gte-bitwise-or": {GRAM: ["rule:gte_bitwise_or"]},
    "pygrammar-rule-gt-bitwise-or": {GRAM: ["rule:gt_bitwise_or"]},
    "pygrammar-rule-notin-bitwise-or": {GRAM: ["rule:notin_bitwise_or"]},
    "pygrammar-rule-in-bitwise-or": {GRAM: ["rule:in_bitwise_or"]},
    "pygrammar-rule-isnot-bitwise-or": {GRAM: ["rule:isnot_bitwise_or"]},
    "pygrammar-rule-is-bitwise-or": {GRAM: ["rule:is_bitwise_or"]},
    "pygrammar-rule-invalid-starred-expression-unpacking": {
        GRAM: ["rule:invalid_starred_expression_unpacking"]},
    "pygrammar-rule-invalid-starred-expression-unpacking-sequence": {
        GRAM: ["rule:invalid_starred_expression_unpacking_sequence"]},
    "pygrammar-rule-invalid-default": {GRAM: ["rule:invalid_default"]},
    "pygrammar-rule-statements": {GRAM: ["rule:statements"]},
    "pygrammar-rule-single-compound-stmt": {GRAM: ["rule:single_compound_stmt"]},
    "pygrammar-rule-statement-newline": {GRAM: ["rule:statement_newline"]},
    "pygrammar-rule-simple-stmts": {GRAM: ["rule:simple_stmts"]},
    "pygrammar-rule-annotated-rhs": {GRAM: ["rule:annotated_rhs"]},
    "pygrammar-rule-type-alias": {GRAM: ["rule:type_alias"]},
    "pygrammar-rule-star-targets-list-seq": {GRAM: ["rule:star_targets_list_seq"]},
    "pygrammar-rule-star-targets-tuple-seq": {GRAM: ["rule:star_targets_tuple_seq"]},
    "pygrammar-rule-star-atom": {GRAM: ["rule:star_atom"]},
    "pygrammar-rule-single-subscript-attribute-target": {GRAM: ["rule:single_subscript_attribute_target"]},
    "pygrammar-rule-del-t-atom": {GRAM: ["rule:del_t_atom"]},
    "pygrammar-rule-type-expressions": {GRAM: ["rule:type_expressions"]},
    "pygrammar-rule-func-type-comment": {GRAM: ["rule:func_type_comment"]},
    "pygrammar-rule-expression-without-invalid": {GRAM: ["rule:expression_without_invalid"]},
    "pygrammar-rule-invalid-if-stmt": {GRAM: ["rule:invalid_if_stmt"]},
    "pygrammar-rule-invalid-elif-stmt": {GRAM: ["rule:invalid_elif_stmt"]},
    "pygrammar-rule-invalid-else-stmt": {GRAM: ["rule:invalid_else_stmt"]},
    "pygrammar-rule-invalid-while-stmt": {GRAM: ["rule:invalid_while_stmt"]},
    "pygrammar-rule-invalid-for-stmt": {GRAM: ["rule:invalid_for_stmt"]},
    "pygrammar-rule-invalid-def-raw": {GRAM: ["rule:invalid_def_raw"]},
    "pygrammar-rule-invalid-class-def-raw": {GRAM: ["rule:invalid_class_def_raw"]},
    "pygrammar-rule-invalid-try-stmt": {GRAM: ["rule:invalid_try_stmt"]},
    "pygrammar-rule-invalid-except-stmt": {GRAM: ["rule:invalid_except_stmt"]},
    "pygrammar-rule-invalid-except-star-stmt": {GRAM: ["rule:invalid_except_star_stmt"]},
    "pygrammar-rule-invalid-finally-stmt": {GRAM: ["rule:invalid_finally_stmt"]},
    "pygrammar-rule-invalid-except-stmt-indent": {GRAM: ["rule:invalid_except_stmt_indent"]},
    "pygrammar-rule-invalid-except-star-stmt-indent": {GRAM: ["rule:invalid_except_star_stmt_indent"]},
    "pygrammar-rule-invalid-match-stmt": {GRAM: ["rule:invalid_match_stmt"]},
    "pygrammar-rule-invalid-case-block": {GRAM: ["rule:invalid_case_block"]},
    "pygrammar-rule-invalid-with-stmt": {GRAM: ["rule:invalid_with_stmt"]},
    "pygrammar-rule-invalid-with-stmt-indent": {GRAM: ["rule:invalid_with_stmt_indent"]},
    "pygrammar-rule-invalid-with-item": {GRAM: ["rule:invalid_with_item"]},
    "pygrammar-rule-invalid-for-target": {GRAM: ["rule:invalid_for_target"]},
    "pygrammar-rule-invalid-for-if-clause": {GRAM: ["rule:invalid_for_if_clause"]},
    "pygrammar-rule-invalid-import-from": {GRAM: ["rule:invalid_import_from"]},
    "pygrammar-rule-invalid-import-from-targets": {GRAM: ["rule:invalid_import_from_targets"]},
    "pygrammar-rule-invalid-as-pattern": {GRAM: ["rule:invalid_as_pattern"]},
    "pygrammar-rule-invalid-class-pattern": {GRAM: ["rule:invalid_class_pattern"]},
    "pygrammar-rule-invalid-mapping-pattern": {GRAM: ["rule:invalid_mapping_pattern"]},
    "pygrammar-rule-invalid-class-argument-pattern": {GRAM: ["rule:invalid_class_argument_pattern"]},
    "pygrammar-rule-invalid-kwds": {GRAM: ["rule:invalid_kwds"]},
    "pygrammar-rule-invalid-lambda-kwds": {GRAM: ["rule:invalid_lambda_kwds"]},
    "pygrammar-rule-invalid-block": {GRAM: ["rule:invalid_block"]},
    "pygrammar-rule-invalid-double-type-comments": {GRAM: ["rule:invalid_double_type_comments"]},
    "pygrammar-rule-invalid-type-params": {GRAM: ["rule:invalid_type_params"]},
    "pygrammar-rule-invalid-noteq": {GRAM: ["rule:invalid_noteq"]},
    "pygrammar-rule-invalid-factor": {GRAM: ["rule:invalid_factor"]},
    "pygrammar-rule-invalid-arithmetic": {GRAM: ["rule:invalid_arithmetic"]},
    "pygrammar-rule-invalid-starred-expression": {GRAM: ["rule:invalid_starred_expression"]},
    "pygrammar-rule-invalid-if-expression": {GRAM: ["rule:invalid_if_expression"]},
    "pygrammar-rule-invalid-kvpair-unpacking": {GRAM: ["rule:invalid_kvpair_unpacking"]},
    "pygrammar-rule-invalid-kvpair": {GRAM: ["rule:invalid_kvpair"]},
    "pygrammar-lex-nextc-in-buffer": {
        "Parser__lexer__lexer.c": ["tok_nextc"],
        "Parser__tokenizer__string_tokenizer.c": ["tok_underflow_string"],
        "Parser__tokenizer__utf8_tokenizer.c": ["tok_underflow_string"],
    },
    "pygrammar-lex-comment-loops": {"Parser__lexer__lexer.c": ["set_ftstring_expr"]},
    "pygrammar-lex-byte-col": {"Parser__tokenizer__helpers.c": ["byte_col_to_char_col"]},
    "pygrammar-peg-decode-known": {
        "Parser__pegen_errors.c": ["_Pypegen_raise_decode_error_known_location"]},
    "pygrammar-peg-decode-format-spec": {
        "Parser__action_helpers.c": ["_PyPegen_decoded_constant_from_token"]},
    "pygrammar-peg-missing-comma": {
        "Parser__action_helpers.c": ["_PyPegen_raise_error_for_missing_comma"]},
    "pygrammar-peg-warn-lazy": {"Parser__action_helpers.c": ["_warn_relative_import_of_lazy"]},
    "pygrammar-peg-checked-from-import": {
        "Parser__action_helpers.c": ["_PyPegen_checked_from_import"]},
    "pygrammar-lex-stacks": {
        "Parser__lexer__lexer.c": ["tok_get_normal_mode", "tok_get_fstring_mode", "tok_get",
                                   "_PyTokenizer_Get"]},
    "pygrammar-unparse-str-repr": {
        "Parser__string_parser.c": ["_PyPegen_parse_string", "decode_unicode_with_escapes",
                                    "_PyPegen_decode_string"],
        "Lib___ast_unparse.py": ["Unparser._write_constant"]},
    "pygrammar-lex-untokenize-lossless": {
        "Lib__tokenize.py": ["Untokenizer.add_whitespace",
                             "Untokenizer.add_backslash_continuation"]},
    "pygrammar-ast-pad-whitespace": {"Lib__ast.py": ["_pad_whitespace"]},
    "pygrammar-ast-docstring-twins": {"Python__ast.c": ["_PyAST_GetDocString"]},
    "pygrammar-unparse-roundtrip": {
        "Lib__ast.py": ["unparse"],
        "Lib___ast_unparse.py": ["Unparser._write_ftstring_inner"]},
    "pygrammar-unparse-c-roundtrip": {"Python__ast_unparse.c": ["append_joinedstr"]},
    "pygrammar-check-validate-name": {"Python__ast.c": ["validate_name"]},
    "pygrammar-check-rejects": {
        "Python__ast.c": [
            "validate_comprehension", "validate_keywords", "validate_args", "validate_arguments",
            "validate_expr", "ensure_literal_number", "ensure_literal_signed",
            "validate_import_names",
            "ensure_literal_complex", "validate_pattern_match_value", "validate_capture",
            "_validate_nonempty_seq", "validate_assignlist", "validate_body", "validate_stmt",
            "validate_stmts", "validate_exprs", "validate_typeparam", "validate_type_params"]},
    "pygrammar-check-null-sites": {
        "Python__ast.c": ["validate_pattern", "validate_patterns", "_PyAST_Validate"]},
    "pygrammar-check-targets": {
        "Parser__action_helpers.c": [
            "_PyPegen_set_expr_context", "_set_seq_context", "_set_name_context",
            "_set_tuple_context", "_set_list_context", "_set_subscript_context",
            "_set_attribute_context", "_set_starred_context", "_PyPegen_get_invalid_target"]},
    "pygrammar-check-fold-reaches": {"Python__ast_preprocess.c": ["astfold_pattern"]},
    "pygrammar-check-fold-reaches-narrow": {
        "Python__ast_preprocess.c": [
            "astfold_mod", "astfold_expr", "astfold_keyword", "astfold_comprehension",
            "astfold_arguments", "astfold_arg", "astfold_stmt", "astfold_excepthandler",
            "astfold_withitem", "astfold_match_case", "astfold_type_param"]},
    "pygrammar-check-fold-docstring": {"Python__ast_preprocess.c": ["astfold_body"]},
    "pygrammar-check-fold-value": {
        "Python__ast_preprocess.c": ["fold_const_match_patterns", "make_const"]},
    "pygrammar-check-format-args": {
        "Python__ast_preprocess.c": ["parse_format", "optimize_format"]},
    "pygrammar-check-docstring-body": {"Python__ast_preprocess.c": ["remove_docstring"]},
    "pygrammar-peg-make-arguments": {
        "Parser__action_helpers.c": ["_PyPegen_make_arguments", "_get_names", "_get_defaults"]},
    "pygrammar-peg-concat": {"Parser__action_helpers.c": ["_build_concatenated_str"]},
    "pygrammar-peg-strip-interpolation": {
        "Parser__action_helpers.c": ["_strip_interpolation_debug_expr"]},
    "pygrammar-peg-register-stmts": {"Parser__action_helpers.c": ["_PyPegen_register_stmts"]},
    "pygrammar-peg-never-silent": {"Parser__pegen.c": ["_PyPegen_run_parser"]},
    "pygrammar-peg-token-readers": {
        "Parser__pegen.c": ["_PyPegen_name_token", "_PyPegen_soft_keyword_token",
                            "_PyPegen_expect_soft_keyword", "_PyPegen_expect_forced_token"]},
    "pygrammar-peg-fill-token": {"Parser__pegen.c": ["_PyPegen_fill_token"]},
    "pygrammar-peg-expect-token": {"Parser__pegen.c": ["_PyPegen_expect_token"]},
    "pygrammar-peg-memo-cache": {
        "Parser__pegen.c": ["_PyPegen_insert_memo", "_PyPegen_update_memo", "_PyPegen_is_memoized"]},
    "pygrammar-peg-last-token": {"Parser__pegen.c": ["_PyPegen_get_last_nonnwhitespace_token"]},
    "pygrammar-peg-raise-unclosed": {"Parser__pegen_errors.c": ["raise_unclosed_parentheses_error"]},
    "pygrammar-peg-tokenizer-error": {"Parser__pegen_errors.c": ["_Pypegen_tokenizer_error"]},
    "pygrammar-peg-decode-error": {"Parser__pegen_errors.c": ["_Pypegen_raise_decode_error"]},
    "pygrammar-peg-tokenize-full-source": {
        "Parser__pegen_errors.c": ["_PyPegen_tokenize_full_source_to_check_for_errors"]},
    "pygrammar-peg-raise-error": {"Parser__pegen_errors.c": ["_PyPegen_raise_error"]},
    "pygrammar-peg-raise-known-location": {
        "Parser__pegen_errors.c": ["_PyPegen_raise_error_known_location"]},
    "pygrammar-peg-set-syntax-error": {"Parser__pegen_errors.c": ["_Pypegen_set_syntax_error"]},
}

# Entries that hold as properties but credit no row: `Rows.<id>` is empty for them.
NO_ROWS = ["grammar-left-recursion", "grammar-call-rule-sound", "peg-first-error",
           "check-syntax-only-identity", "check-no-null-deref", "peg-roundtrip-parser",
           "peg-roundtrip-actions", "lex-exact-tokens", "check-nonempty", "check-table-covers",
           "check-try-twin", "check-names-always", "check-target-legal",
           "check-set-context-last", "check-set-context-restores"]

# A row may be credited by several entries; the tsv lists them comma-separated.
CREDITED = {}
for _entry, _files in CREDIT.items():
    for _stem, _names in _files.items():
        for _name in _names:
            CREDITED.setdefault((_stem, _name), []).append(_entry)

WITHDRAWN = ("withdrawn: the model and difftest exist, but no theorem yet depends on this body")

NOBEH = "no-behaviour: "
TOKEN_GEN = "generated: emitted by Tools/build/generate_token.py from Grammar/Tokens"
EXCLUDE = {
    ("Parser__token.c", "_PyToken_OneChar"): TOKEN_GEN,
    ("Parser__token.c", "_PyToken_TwoChars"): TOKEN_GEN,
    ("Parser__token.c", "_PyToken_ThreeChars"): TOKEN_GEN,
    ("Lib__token.py", "ISTERMINAL"): TOKEN_GEN,
    ("Lib__token.py", "ISNONTERMINAL"): TOKEN_GEN,
    ("Lib__token.py", "ISEOF"): TOKEN_GEN,
    ("Parser__lexer__state.c", "free_fstring_expressions"): NOBEH + "frees f-string buffers at teardown",
    ("Parser__lexer__state.c", "_PyTokenizer_Free"): NOBEH + "frees the tokenizer state",
    ("Parser__lexer__state.c", "_PyToken_Free"): NOBEH + "drops a metadata reference",
    ("Parser__lexer__buffer.c", "_PyLexer_remember_fstring_buffers"):
        NOBEH + "pointer fix-up around realloc; the model holds offsets",
    ("Parser__lexer__buffer.c", "_PyLexer_restore_fstring_buffers"):
        NOBEH + "pointer fix-up around realloc; the model holds offsets",
    ("Parser__lexer__buffer.c", "_PyLexer_tok_reserve_buf"):
        NOBEH + "grows the readline buffer; only allocation failure is observable",
    ("Parser__tokenizer__helpers.c", "_PyTokenizer_new_string"): NOBEH + "strdup with an allocation check",
    ("Parser__tokenizer__helpers.c", "_PyTokenizer_print_escape"): "test-support: Py_DEBUG tracing only",
    ("Parser__tokenizer__helpers.c", "_PyTokenizer_tok_dump"): "test-support: Py_DEBUG tracing only",
    ("Parser__pegen.c", "_PyPegen_clear_memo_statistics"): "test-support: Py_DEBUG statistics",
    ("Parser__pegen.c", "_PyPegen_get_memo_statistics"): "test-support: Py_DEBUG statistics",
    ("Parser__pegen.c", "growable_comment_array_init"): NOBEH + "allocation; the model keeps a list",
    ("Parser__pegen.c", "growable_comment_array_add"): NOBEH + "allocation; the model keeps a list",
    ("Parser__pegen.c", "growable_comment_array_deallocate"): NOBEH + "frees comments",
    ("Parser__pegen.c", "_resize_tokens_array"): NOBEH + "grows the token array; only allocation failure is observable",
    ("Parser__pegen.c", "_PyPegen_Parser_Free"): NOBEH + "frees the parser",
    ("Parser__pegen.c", "init_normalization"): NOBEH + "imports unicodedata.normalize once; Cfg.nfkc stands for its result",
    ("Python__Python-tokenize.c", "get_tokenize_state"): NOBEH + "module state accessor",
    ("Python__Python-tokenize.c", "tokenizeriter_dealloc"): NOBEH + "frees the iterator",
    ("Python__Python-tokenize.c", "tokenizemodule_exec"): "internal-bootstrap: module init",
    ("Python__Python-tokenize.c", "tokenizemodule_traverse"): NOBEH + "GC traversal",
    ("Python__Python-tokenize.c", "tokenizemodule_clear"): NOBEH + "GC clear",
    ("Python__Python-tokenize.c", "tokenizemodule_free"): NOBEH + "GC free",
    ("Python__Python-tokenize.c", "PyInit__tokenize"): "internal-bootstrap: module init",
    ("Parser__myreadline.c", "my_fgets"): "platform: terminal line input",
    ("Parser__myreadline.c", "_PyOS_WindowsConsoleReadline"): "platform: Windows console input",
    ("Parser__myreadline.c", "PyOS_StdioReadline"): "platform: terminal line input",
    ("Parser__myreadline.c", "PyOS_Readline"): "platform: terminal line input",
}


def read(stem):
    with (METHODS / f"{stem}.tsv").open(newline="") as f:
        return list(csv.DictReader(f, delimiter="\t", quoting=csv.QUOTE_NONE, escapechar="\\"))


def write(stem, rows):
    with (METHODS / f"{stem}.tsv").open("w", newline="") as f:
        w = csv.DictWriter(f, FIELDS, delimiter="\t", quoting=csv.QUOTE_NONE, escapechar="\\",
                           lineterminator="\n")
        w.writeheader()
        w.writerows(rows)


def main():
    lean = ["/-! GENERATED by `gen/gen_rows.py` from `coverage/methods/`. Do not edit. -/", "",
            "namespace PyLean.PyGrammar.Rows", ""]
    per_entry = {e: [] for e in CREDIT}
    per_entry.update({"pygrammar-" + e: [] for e in NO_ROWS})
    withdrawn = {}
    missing = [k for k, _ in CREDITED.items() if k[1] not in {r["name"] for r in read(k[0])}]
    if missing:
        sys.exit(f"credited rows missing from the inventory: {missing}")
    for stem in STEMS:
        rows = read(stem)
        for r in rows:
            key = (stem, r["name"])
            was = r["status"]
            if r["note"].startswith("changed-in-3.15:"):
                # Left for whoever rechecks the body against 3.15.2 (AGENTS.md).
                continue
            if stem == "Parser__parser.c":
                r.update(status="excluded", entry="", note=GENERATED)
            elif key in EXCLUDE:
                r.update(status="excluded", entry="", note=EXCLUDE[key])
            elif key in CREDITED:
                r.update(status="modelled", entry=",".join(CREDITED[key]), note="")
                for e in CREDITED[key]:
                    per_entry[e].append(r["name"])
            elif stem == "Grammar__python.gram":
                # A rule row is credited only by a rule-specific entry in `CREDIT` (`Peg/Rules/`).
                # `CallRuleSound` holds for any grammar data, so it credits none; the other rows
                # keep their status and review note.
                pass
            elif r["entry"].startswith("pygrammar-") or r["note"].startswith("withdrawn:"):
                r.update(status="todo", entry="", note=WITHDRAWN)
            if was == "modelled" and r["status"] != "modelled":
                withdrawn[stem] = withdrawn.get(stem, 0) + 1
        if "--write" in sys.argv:
            write(stem, rows)
    for entry, names in sorted(per_entry.items()):
        lid = entry.replace("pygrammar-", "").replace("-", "_")
        seen = list(dict.fromkeys(names))
        body = ",\n  ".join(", ".join('"' + n.replace('"', '\\"') + '"' for n in seen[i:i + 6])
                            for i in range(0, len(seen), 6))
        lean += [f"def {lid} : List String := [\n  {body}]", ""]
    lean.append("end PyLean.PyGrammar.Rows")
    OUT.write_text("\n".join(lean) + "\n")
    print("withdrawn or reclassified:", withdrawn, sum(withdrawn.values()))
    print("credited:", {k: len(v) for k, v in per_entry.items() if v})


if __name__ == "__main__":
    main()
