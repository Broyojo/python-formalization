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
    "pygrammar-lex-nextc-in-buffer": {
        "Parser__lexer__lexer.c": ["tok_nextc"],
        "Parser__tokenizer__string_tokenizer.c": ["tok_underflow_string"],
        "Parser__tokenizer__utf8_tokenizer.c": ["tok_underflow_string"],
    },
    "pygrammar-lex-debug-text": {"Parser__lexer__lexer.c": ["set_ftstring_expr"]},
    "pygrammar-lex-accepts-valid": {
        "Parser__lexer__lexer.c": ["_PyLexer_update_ftstring_expr", "tok_get_normal_mode",
                                   "tok_get_fstring_mode", "tok_get", "_PyTokenizer_Get"]},
    "pygrammar-lex-untokenize-lossless": {
        "Lib__tokenize.py": ["Untokenizer.add_whitespace",
                             "Untokenizer.add_backslash_continuation"]},
    "pygrammar-ast-pad-whitespace": {"Lib__ast.py": ["_pad_whitespace"]},
    "pygrammar-ast-docstring-twins": {"Python__ast.c": ["_PyAST_GetDocString"]},
    "pygrammar-unparse-roundtrip": {
        "Lib__ast.py": ["unparse"],
        "Lib___ast_unparse.py": [
            "Unparser._write_ftstring_inner", "Unparser._write_ftstring", "Unparser.visit_JoinedStr",
            "Unparser.visit_FormattedValue", "Unparser._write_interpolation",
            "Unparser._ftstring_helper", "Unparser._unparse_interpolation_value"],
    },
    "pygrammar-unparse-c-roundtrip": {
        "Python__ast_unparse.c": ["append_joinedstr", "build_ftstring_body",
                                  "append_fstring_element", "append_formattedvalue",
                                  "append_ast_expr", "expr_as_unicode", "_PyAST_ExprAsUnicode"]},
    "pygrammar-check-validate-name": {"Python__ast.c": ["validate_name"]},
    "pygrammar-check-try-twin": {"Python__ast.c": ["validate_stmt"]},
    "pygrammar-check-no-null-deref": {"Python__ast.c": ["validate_pattern", "validate_patterns"]},
    "pygrammar-check-names-always": {"Python__ast.c": ["validate_expr"]},
    "pygrammar-check-syntax-only-identity": {
        "Python__ast_preprocess.c": [
            "astfold_body", "astfold_mod", "astfold_expr", "astfold_keyword",
            "astfold_comprehension", "astfold_arguments", "astfold_arg", "astfold_stmt",
            "astfold_excepthandler", "astfold_withitem", "astfold_pattern", "astfold_match_case",
            "astfold_type_param", "_PyAST_Preprocess"]},
    "pygrammar-check-fold-value": {
        "Python__ast_preprocess.c": ["fold_const_match_patterns", "make_const"]},
    "pygrammar-check-format-args": {
        "Python__ast_preprocess.c": ["parse_format", "optimize_format"]},
    "pygrammar-check-docstring-body": {"Python__ast_preprocess.c": ["remove_docstring"]},
    "pygrammar-peg-make-arguments": {
        "Parser__action_helpers.c": ["_PyPegen_make_arguments", "_get_names", "_get_defaults"]},
    "pygrammar-peg-concat": {"Parser__action_helpers.c": ["_build_concatenated_str"]},
    "pygrammar-peg-strip-interpolation": {"Parser__action_helpers.c": ["_strip_interpolation_expr"]},
    "pygrammar-peg-register-stmts": {"Parser__action_helpers.c": ["_PyPegen_register_stmts"]},
    "pygrammar-peg-never-silent": {"Parser__pegen.c": ["_PyPegen_run_parser"]},
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
NO_ROWS = ["grammar-left-recursion", "peg-first-error", "peg-roundtrip-parser",
           "peg-roundtrip-actions", "lex-exact-tokens", "check-nonempty"]

CREDITED = {(stem, name): entry for entry, files in CREDIT.items()
            for stem, names in files.items() for name in names}

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
            if stem == "Parser__parser.c":
                r.update(status="excluded", entry="", note=GENERATED)
            elif key in EXCLUDE:
                r.update(status="excluded", entry="", note=EXCLUDE[key])
            elif key in CREDITED:
                r.update(status="modelled", entry=CREDITED[key], note="")
                per_entry[CREDITED[key]].append(r["name"])
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
