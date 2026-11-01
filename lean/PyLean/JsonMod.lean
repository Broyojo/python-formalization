import PyLean.Registry
import PyLean.JsonMod.Diff
import PyLean.JsonMod.DecProps
import PyLean.JsonMod.EncTwins
import PyLean.JsonMod.RoundTripStr

/-!
`Lib/json/` pure-Python scanner/encoder vs `Modules/_json.c`, CPython 3.14.7.

The model covers both decoders (`py_scanstring`, `JSONObject`, `JSONArray`,
`py_make_scanner`, `NUMBER_RE` against `scanstring_unicode`,
`_parse_object_unicode`, `_parse_array_unicode`, `_match_number_unicode`,
`scan_once_unicode`) with `strict`, `object_pairs_hook` and `parse_int`, exact
`JSONDecodeError` messages and positions, Python's negative-index semantics in
`raw_decode`, and the 4300-digit int limit; and both encoders
(`py_encode_basestring(_ascii)`/`_make_iterencode` against
`c_encode_basestring(_ascii)`/`c_make_encoder`) with `ensure_ascii`,
`check_circular` (reference cycles), `sort_keys` with mixed key types,
`skipkeys`, non-str keys, `indent` and separators. Floats are out of scope:
`parse_float` and `parse_constant` are modelled as hooks receiving the matched
text, and float values and keys are not encoded. Recursion limits are out of
scope.
-/

namespace PyLean.JsonMod

open PyLean.Registry

def entries : List Entry := [
  { id := "json-loads-twins", pyFile := "Lib/json/decoder.py"
    pyFns := ["json.loads", "py_scanstring", "JSONObject", "JSONArray", "py_make_scanner", "C scan_once_unicode"]
    statement := "For every str s and every strict/object_pairs_hook/parse_int setting, json.loads(s) with _json and without it return the same value or raise the same exception with the same message."
    source := "invariant: C accelerator vs pure-Python twin (test_json runs every test on both)", status := .refuted
    prop := ``LoadsTwins, thm := some ``loadsTwins_refuted
    bug := some "json-scanstring-error-twins"
    notes := "Witness '\"\\x01\"': 'Invalid control character at' (C) vs \"Invalid control character '\\\\x01' at\" (Python), same position." },
  { id := "json-loads-twins-pos", pyFile := "Lib/json/decoder.py"
    pyFns := ["json.loads", "py_scanstring", "C scanstring_unicode"]
    statement := "For every str s, json.loads(s) with and without _json return the same value, or raise JSONDecodeError at the same pos (hence lineno, colno), whatever the message text."
    source := "invariant: C/Python twins; test_fail.py checks pos/lineno/colno against both", status := .refuted
    prop := ``LoadsTwinsPos, thm := some ``loadsTwinsPos_refuted
    bug := some "json-scanstring-error-twins"
    notes := "Witness '\"\\\\x\"': C reports the backslash (pos 1), Python the escaped character (pos 2)." },
  { id := "json-loads-twins-scan", pyFile := "Lib/json/decoder.py"
    pyFns := ["json.loads", "py_scanstring", "JSONObject", "JSONArray", "NUMBER_RE", "C scanstring_unicode", "C _parse_object_unicode", "C _parse_array_unicode", "C _match_number_unicode"]
    statement := "For every str s (len(s) <= sys.maxsize) and every strict/object_pairs_hook/parse_int setting, json.loads(s) agrees exactly (value, or exception class, msg, pos, lineno, colno) between the twins, except that an invalid control character is reported with a different message at the same position, and an invalid escape \\c at backslash q is reported by C at q and by Python at q+1 with a different message."
    source := "invariant: C/Python twins", status := .proven
    prop := ``LoadsTwinsScan, thm := some ``loadsTwinsScan_proven
    notes := "Covers NUMBER_RE vs _match_number_unicode (leading zeros, '-', exponents and backtracking, the 4300-digit limit, parse_int hook), NaN/Infinity/-Infinity, white space, surrogate pairs (valid, lone, reversed, truncated, C's `end + 6 < len`), every error position, duplicate keys and object_pairs_hook." },
  { id := "json-raw-decode-twins", pyFile := "Lib/json/scanner.py"
    pyFns := ["JSONDecoder.raw_decode", "py_make_scanner", "C scanner_call"]
    statement := "For every str s and every int idx, JSONDecoder().raw_decode(s, idx) agrees between the twins up to the two string-error differences of json-loads-twins-scan."
    source := "invariant: C/Python twins; bpo-21529 check `idx cannot be negative`", status := .refuted
    prop := ``RawDecodeTwins, thm := some ``rawDecodeTwins_refuted
    bug := some "json-py-raw-decode-negative-index"
    notes := "raw_decode('12', -1) is (12, 2) in Python, ValueError in C. idx > sys.maxsize: OverflowError (C) vs JSONDecodeError (Python)." },
  { id := "json-raw-decode-twins-in-range", pyFile := "Lib/json/scanner.py"
    pyFns := ["JSONDecoder.raw_decode", "py_make_scanner", "JSONObject", "JSONArray", "C scan_once_unicode"]
    statement := "For every str s, 0 <= idx <= sys.maxsize and every decoder setting, raw_decode(s, idx) agrees between the twins up to the two string-error differences (in particular the same end index and the same JSONDecodeError positions)."
    source := "invariant: C/Python twins", status := .proven
    prop := ``RawDecodeTwinsInRange, thm := some ``rawDecodeTwinsInRange_proven
    notes := "The bounds on idx are exactly the refuted cases of json-raw-decode-twins." },
  { id := "json-dumps-twins", pyFile := "Lib/json/encoder.py"
    pyFns := ["json.dumps", "_make_iterencode", "py_encode_basestring", "py_encode_basestring_ascii", "C c_make_encoder", "C ascii_escape_unicode", "C escape_unicode"]
    statement := "For every value built from None, bool, int, str (code points <= 0x10FFFF), list, dict with str/int/bool/None/tuple keys, reference cycles and unknown objects, and every ensure_ascii, check_circular, sort_keys, skipkeys, indent and separators, json.dumps with c_make_encoder and with _make_iterencode return the same text or raise the same exception."
    source := "invariant: C accelerator vs pure-Python twin", status := .proven
    prop := ``DumpsTwins, thm := some ``dumpsTwins_proven
    notes := "Exception messages agree exactly except TypeError from sort_keys with mixed key types, which both take from list.sort (modelled with '~'). Floats and default= are out of scope." },
  { id := "json-roundtrip-str", pyFile := "Lib/json/encoder.py"
    pyFns := ["json.dumps", "json.loads", "py_encode_basestring_ascii", "py_scanstring"]
    statement := "For every str t, json.loads(json.dumps(t, ...)) == t, for every ensure_ascii setting, both encoders and both decoders."
    source := "round trip (json docs: dumps/loads)", status := .refuted
    prop := ``RoundTripStr, thm := some ``roundTripStr_refuted
    bug := some "json-roundtrip-surrogate-pair"
    notes := "'\\ud834\\udd1e' (two code points) comes back as '\\U0001d11e' with ensure_ascii=True. Known: gh-94527 (open)." }
]

end PyLean.JsonMod
