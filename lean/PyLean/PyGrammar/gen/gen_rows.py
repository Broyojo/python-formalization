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
    "pygrammar-rule-invalid-dotted-as-name": {GRAM: ["rule:invalid_dotted_as_name"]},
    "pygrammar-rule-invalid-import-from-as-name": {GRAM: ["rule:invalid_import_from_as_name"]},
    "pygrammar-rule-literal-pattern": {GRAM: ["rule:literal_pattern"]},
    "pygrammar-rule-literal-expr": {GRAM: ["rule:literal_expr"]},
    "pygrammar-rule-complex-number": {GRAM: ["rule:complex_number"]},
    "pygrammar-rule-signed-real-number": {GRAM: ["rule:signed_real_number"]},
    "pygrammar-rule-real-imaginary-number": {GRAM: ["rule:real_number", "rule:imaginary_number"]},
    "pygrammar-rule-match-stmt": {GRAM: ["rule:match_stmt"]},
    "pygrammar-rule-decorators": {GRAM: ["rule:decorators"]},
    "pygrammar-rule-annotation-default": {GRAM: ["rule:annotation", "rule:star_annotation",
                                                 "rule:default"]},
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
