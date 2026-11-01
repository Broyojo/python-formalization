#!/usr/bin/env python3
"""Generate lean/PyLean/PyGrammar/RowNames.lean and settle the coverage rows of this module.

`ROWS` says, for each inventory file, which registry entry settles a row. A name maps to its
entry through `OVERRIDE`, then through the file's default. Rows named in `EXCLUDE` become
`excluded` with the given reason, and rows in `LEFT` stay `todo`. Lean gets the names as lists,
so `pyFns` in the registry can never disagree with the tsv.
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

# file stem -> (lean name, default entry or None)
ROWS = {
    "Grammar__python.gram": ("grammar", "pygrammar-grammar-left-recursion"),
    "Parser__lexer__lexer.c": ("lexer", "pygrammar-lex-accepts-valid"),
    "Parser__lexer__state.c": ("state", "pygrammar-lex-accepts-valid"),
    "Parser__lexer__buffer.c": ("buffer", None),
    "Parser__token.c": ("token", "pygrammar-lex-exact-tokens"),
    "Parser__tokenizer__helpers.c": ("helpers", "pygrammar-lex-accepts-valid"),
    "Parser__tokenizer__readline_tokenizer.c": ("readlineTok", "pygrammar-lex-accepts-valid"),
    "Parser__tokenizer__string_tokenizer.c": ("stringTok", "pygrammar-peg-roundtrip-parser"),
    "Parser__tokenizer__utf8_tokenizer.c": ("utf8Tok", "pygrammar-peg-roundtrip-parser"),
    "Parser__tokenizer__file_tokenizer.c": ("fileTok", None),
    "Parser__myreadline.c": ("myreadline", None),
    "Python__Python-tokenize.c": ("pyTokenize", "pygrammar-lex-accepts-valid"),
    "Parser__action_helpers.c": ("actions", "pygrammar-peg-roundtrip-actions"),
    "Parser__pegen.c": ("pegen", "pygrammar-peg-roundtrip-parser"),
    "Parser__pegen_errors.c": ("pegenErrors", "pygrammar-peg-first-error"),
    "Parser__string_parser.c": ("stringParser", "pygrammar-peg-roundtrip-parser"),
    "Parser__peg_api.c": ("pegApi", "pygrammar-peg-roundtrip-parser"),
    "Parser__parser.c": ("parserC", None),
    "Lib___ast_unparse.py": ("astUnparse", "pygrammar-unparse-roundtrip"),
    "Python__ast_unparse.c": ("astUnparseC", "pygrammar-unparse-c-roundtrip"),
    "Lib__tokenize.py": ("tokenizePy", None),
    "Lib__ast.py": ("astPy", None),
    "Python__ast.c": ("astC", "pygrammar-check-try-twin"),
    "Python__ast_preprocess.c": ("preprocess", "pygrammar-check-syntax-only-identity"),
}

OVERRIDE = {
    ("Lib__ast.py", "increment_lineno"): "pygrammar-ast-increment-lineno",
    ("Lib__ast.py", "_splitlines_no_ff"): "pygrammar-ast-splitlines",
    ("Lib__ast.py", "_pad_whitespace"): "pygrammar-ast-pad-whitespace",
    ("Lib__ast.py", "get_docstring"): "pygrammar-ast-docstring-twins",
    ("Lib__ast.py", "literal_eval"): "pygrammar-ast-literal-eval",
    ("Lib__ast.py", "unparse"): "pygrammar-unparse-roundtrip",
    ("Lib__tokenize.py", "_get_normal_name"): "pygrammar-lex-normal-name-twin",
    ("Lib__tokenize.py", "detect_encoding"): "pygrammar-lex-cookie-twin",
    ("Lib__tokenize.py", "Untokenizer.__init__"): "pygrammar-lex-untokenize-lossless",
    ("Lib__tokenize.py", "Untokenizer.add_whitespace"): "pygrammar-lex-untokenize-lossless",
    ("Lib__tokenize.py", "Untokenizer.add_backslash_continuation"): "pygrammar-lex-untokenize-lossless",
    ("Lib__tokenize.py", "Untokenizer.escape_brackets"): "pygrammar-lex-untokenize-lossless",
    ("Lib__tokenize.py", "Untokenizer.untokenize"): "pygrammar-lex-untokenize-lossless",
    ("Lib__tokenize.py", "untokenize"): "pygrammar-lex-untokenize-lossless",
    ("Lib__tokenize.py", "generate_tokens"): "pygrammar-lex-accepts-valid",
    ("Lib__tokenize.py", "_generate_tokens_from_c_tokenizer"): "pygrammar-lex-accepts-valid",
    ("Lib__tokenize.py", "_transform_msg"): "pygrammar-lex-accepts-valid",
    ("Parser__lexer__lexer.c", "tok_nextc"): "pygrammar-lex-nextc-in-buffer",
    ("Parser__lexer__lexer.c", "contains_null_bytes"): "pygrammar-lex-nextc-in-buffer",
    ("Parser__lexer__lexer.c", "set_ftstring_expr"): "pygrammar-lex-debug-text",
    ("Parser__tokenizer__helpers.c", "_PyTokenizer_translate_newlines"): "pygrammar-lex-translate-newlines",
    ("Parser__tokenizer__string_tokenizer.c", "tok_underflow_string"): "pygrammar-lex-nextc-in-buffer",
    ("Parser__tokenizer__utf8_tokenizer.c", "tok_underflow_string"): "pygrammar-lex-nextc-in-buffer",
    ("Python__ast.c", "validate_name"): "pygrammar-check-validate-name",
    ("Python__ast.c", "validate_capture"): "pygrammar-check-validate-name",
    ("Python__ast.c", "_validate_nonempty_seq"): "pygrammar-check-nonempty",
    ("Python__ast.c", "validate_expr"): "pygrammar-check-names-always",
    ("Python__ast.c", "expr_context_name"): "pygrammar-check-names-always",
    ("Python__ast_preprocess.c", "remove_docstring"): "pygrammar-check-docstring-body",
    ("Python__ast_preprocess.c", "stmt_seq_remove_item"): "pygrammar-check-docstring-body",
    ("Python__ast_preprocess.c", "fold_const_match_patterns"): "pygrammar-check-fold-value",
    ("Python__ast_preprocess.c", "make_const"): "pygrammar-check-fold-value",
    ("Python__ast_preprocess.c", "parse_literal"): "pygrammar-check-format-args",
    ("Python__ast_preprocess.c", "simple_format_arg_parse"): "pygrammar-check-format-args",
    ("Python__ast_preprocess.c", "parse_format"): "pygrammar-check-format-args",
    ("Python__ast_preprocess.c", "optimize_format"): "pygrammar-check-format-args",
    ("Python__ast_preprocess.c", "fold_binop"): "pygrammar-check-format-args",
    ("Python__ast_preprocess.c", "has_starred"): "pygrammar-check-format-args",
    ("Parser__action_helpers.c", "_PyPegen_make_arguments"): "pygrammar-peg-make-arguments",
    ("Parser__action_helpers.c", "_make_posonlyargs"): "pygrammar-peg-make-arguments",
    ("Parser__action_helpers.c", "_make_posargs"): "pygrammar-peg-make-arguments",
    ("Parser__action_helpers.c", "_make_posdefaults"): "pygrammar-peg-make-arguments",
    ("Parser__action_helpers.c", "_make_kwargs"): "pygrammar-peg-make-arguments",
    ("Parser__action_helpers.c", "_get_names"): "pygrammar-peg-make-arguments",
    ("Parser__action_helpers.c", "_get_defaults"): "pygrammar-peg-make-arguments",
    ("Parser__action_helpers.c", "_build_concatenated_str"): "pygrammar-peg-concat",
    ("Parser__action_helpers.c", "_build_concatenated_joined_str"): "pygrammar-peg-concat",
    ("Parser__action_helpers.c", "_PyPegen_concatenate_strings"): "pygrammar-peg-concat",
    ("Parser__action_helpers.c", "_PyPegen_concatenate_tstrings"): "pygrammar-peg-concat",
    ("Parser__pegen_errors.c", "_Pypegen_tokenizer_error"): "pygrammar-peg-roundtrip-parser",
    ("Parser__pegen_errors.c", "_Pypegen_raise_decode_error"): "pygrammar-peg-roundtrip-parser",
}

NOBEH = "no-behaviour: "
EXCLUDE = {
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
    per_entry = {}
    for stem, (lname, default) in ROWS.items():
        rows = read(stem)
        names = []
        for r in rows:
            key = (stem, r["name"])
            if stem == "Parser__parser.c":
                r.update(status="excluded", entry="", note=GENERATED)
                continue
            if key in EXCLUDE:
                r.update(status="excluded", entry="", note=EXCLUDE[key])
                continue
            entry = OVERRIDE.get(key, default)
            if entry is None:
                continue
            r.update(status="modelled", entry=entry, note="")
            per_entry.setdefault(entry, []).append(r["name"])
            names.append(r["name"])
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
    print({k: len(v) for k, v in per_entry.items()})


if __name__ == "__main__":
    main()
