import PyLean.Registry
import PyLean.JsonMod.Diff
import PyLean.JsonMod.DecProps
import PyLean.JsonMod.DecFuel
import PyLean.JsonMod.EncTwins
import PyLean.JsonMod.RoundTripTop
import PyLean.JsonMod.Strict
import PyLean.JsonMod.DocProps
import PyLean.JsonMod.HookProps
import PyLean.JsonMod.ToolProps

/-!
`Lib/json/` against `Modules/_json.c`, CPython 3.15.2.

The model covers the whole package. Both decoders (`py_scanstring`, `JSONObject`,
`JSONArray`, `py_make_scanner`, `NUMBER_RE` against `scanstring_unicode`,
`_parse_object_unicode`, `_parse_array_unicode`, `_match_number_unicode`,
`scan_once_unicode`), with every hook as an arbitrary function, `array_hook`
included, exact
`JSONDecodeError` messages and positions, Python's negative-index semantics in
`raw_decode`, and the 4300-digit int limit. Both encoders
(`py_encode_basestring(_ascii)`, `_make_iterencode`, as chunks too, against
`c_encode_basestring(_ascii)`, `c_make_encoder`), with `allow_nan`, `default`,
`check_circular`, `sort_keys`, `skipkeys`, non-str keys, `indent` and separators;
a `frozendict` is encoded as a `dict`.
The public layer (`loads`, `load`, `dumps`, `dump`, `detect_encoding`,
`JSONDecoder.__init__`, `JSONEncoder.__init__`, `JSONDecodeError`), the Python
surface of `_json` (`make_scanner`, `make_encoder`, the indent cache) and
`json.tool`.

A float value is its IEEE-754 bits, which decide every branch, and the text of
`float.__repr__`, which is data: `float()` and `repr()` belong to the binary64
model, and what depends on them stays open. Recursion limits, `cls=`, and
container subclasses are out of scope, as is mutating a container from `default`
or a hook while it is being encoded.
-/

namespace PyLean.JsonMod

open PyLean.Registry

def entries : List Entry := [
  { id := "json-loads-twins", pyFile := "Lib/json/decoder.py"
    pyFns := ["JSONDecoder.decode", "JSONDecoder.raw_decode", "py_make_scanner", "py_scanstring", "scanstring_unicode", "scan_once_unicode", "scanner_call", "raise_errmsg"]
    statement := "For every str s and every decoder setting, JSONDecoder().decode(s) with _json and without it return the same value or raise the same exception with the same message."
    source := "invariant: C accelerator vs pure-Python twin (test_json runs every test on both)", status := .refuted
    prop := ``LoadsTwins, thm := some ``loadsTwins_refuted
    bug := some "json-scanstring-error-twins"
    notes := "Witness '\"\\x01\"': 'Invalid control character at' (C) vs \"Invalid control character '\\\\x01' at\" (Python), same position." },
  { id := "json-loads-twins-pos", pyFile := "Lib/json/decoder.py"
    pyFns := ["JSONDecoder.decode", "JSONDecoder.raw_decode", "py_scanstring", "scanstring_unicode", "scan_once_unicode"]
    statement := "For every str s, JSONDecoder().decode(s) with and without _json return the same value, or raise JSONDecodeError at the same pos (hence lineno, colno), whatever the message text."
    source := "invariant: C/Python twins; test_fail.py checks pos/lineno/colno against both", status := .refuted
    prop := ``LoadsTwinsPos, thm := some ``loadsTwinsPos_refuted
    bug := some "json-scanstring-error-twins"
    notes := "Witness '\"\\\\x\"': C reports the backslash (pos 1), Python the escaped character (pos 2)." },
  { id := "json-loads-twins-scan", pyFile := "Lib/json/decoder.py"
    pyFns := ["JSONDecoder.decode", "JSONDecoder.raw_decode", "py_scanstring", "_decode_uXXXX", "JSONObject", "JSONArray", "py_make_scanner", "scanstring_unicode", "_parse_object_unicode", "_parse_array_unicode", "_parse_constant", "_match_number_unicode", "scan_once_unicode", "scanner_call", "raise_errmsg", "raise_stop_iteration"]
    statement := "For every str s (len(s) <= sys.maxsize) and every decoder setting, for arbitrary object_hook, object_pairs_hook, array_hook, parse_float, parse_int and parse_constant, JSONDecoder.decode(s) agrees exactly (value, or exception class, msg, pos, lineno, colno) between the twins, except that an invalid control character is reported with a different message at the same position, and an invalid escape \\c at backslash q is reported by C at q and by Python at q+1 with a different message."
    source := "invariant: C/Python twins", status := .proven
    prop := ``LoadsTwinsScan, thm := some ``loadsTwinsScan_proven
    notes := "Covers NUMBER_RE vs _match_number_unicode (leading zeros, '-', exponents and backtracking, the 4300-digit limit), NaN/Infinity/-Infinity, white space, surrogate pairs (valid, lone, reversed, truncated, C's `end + 6 < len`), every error position, duplicate keys, hooks that raise (StopIteration included), and C's fast path for a string without escapes (_PyUnicodeWriter_IsEmpty, cScanLoop_none)." },
  { id := "json-raw-decode-twins", pyFile := "Lib/json/scanner.py"
    pyFns := ["JSONDecoder.raw_decode", "py_make_scanner", "scan_once_unicode", "scanner_call"]
    statement := "For every str s and every int idx, JSONDecoder().raw_decode(s, idx) agrees between the twins up to the two string-error differences of json-loads-twins-scan."
    source := "invariant: C/Python twins; bpo-21529 check `idx cannot be negative`", status := .refuted
    prop := ``RawDecodeTwins, thm := some ``rawDecodeTwins_refuted
    bug := some "json-py-raw-decode-negative-index"
    notes := "raw_decode('12', -1) is (12, 2) in Python, ValueError in C. idx > sys.maxsize: OverflowError (C) vs JSONDecodeError (Python)." },
  { id := "json-raw-decode-twins-in-range", pyFile := "Lib/json/scanner.py"
    pyFns := ["JSONDecoder.raw_decode", "py_make_scanner", "JSONObject", "JSONArray", "scan_once_unicode", "scanner_call", "_build_rval_index_tuple", "_parse_object_unicode", "_parse_array_unicode", "_match_number_unicode"]
    statement := "For every str s, 0 <= idx <= sys.maxsize and every decoder setting, raw_decode(s, idx) agrees between the twins up to the two string-error differences (in particular the same end index and the same JSONDecodeError positions)."
    source := "invariant: C/Python twins", status := .proven
    prop := ``RawDecodeTwinsInRange, thm := some ``rawDecodeTwinsInRange_proven
    notes := "The bounds on idx are exactly the refuted cases of json-raw-decode-twins." },
  { id := "json-dumps-twins", pyFile := "Lib/json/encoder.py"
    pyFns := ["JSONEncoder.encode", "JSONEncoder.iterencode", "_make_iterencode", "py_encode_basestring", "py_encode_basestring_ascii", "ascii_escape_unicode", "ascii_escape_unichar", "escape_unicode", "encoder_listencode_obj", "encoder_listencode_list", "encoder_listencode_dict", "encoder_encode_key_value", "encoder_encode_float", "encoder_write_string", "_encoded_const", "_steal_accumulate", "write_escaped_ascii", "write_escaped_unicode", "ascii_escape_size", "escape_size", "ascii_escape_unicode_and_size", "escape_unicode_and_size"]
    statement := "For every value built from None, bool, int, float, str (code points <= 0x10FFFF), list, dict or frozendict with str/int/float/bool/None/tuple keys, reference cycles and unknown objects, every default() returning such values, and every ensure_ascii, check_circular, allow_nan, sort_keys, skipkeys, indent and separators, JSONEncoder.encode with c_make_encoder and with _make_iterencode return the same text or raise the same exception."
    source := "invariant: C accelerator vs pure-Python twin", status := .proven
    prop := ``DumpsTwins, thm := some ``dumpsTwins_proven
    notes := "Exception messages agree exactly except TypeError from sort_keys with mixed key types, which both take from list.sort (modelled with '~'). The text of float.__repr__ is a parameter (ASCII, a type invariant); NaN keys with sort_keys are out of scope because the order then depends on the sort." },
  { id := "json-dumps-api-twins", pyFile := "Lib/json/__init__.py"
    pyFns := ["dumps"]
    statement := "json.dumps with _json and without it, for every keyword argument (with the type invariants of json-dumps-twins): the same text or the same exception."
    source := "invariant: C/Python twins", status := .proven
    prop := ``DumpsApiTwins, thm := some ``dumpsApiTwins_proven },
  { id := "json-dumps-fast-path", pyFile := "Lib/json/__init__.py"
    pyFns := ["dumps", "dump", "JSONEncoder.__init__"]
    statement := "With every keyword argument at its default, the cached encoder of dumps and dump is the encoder JSONEncoder(...) would build."
    source := "invariant: fast path vs slow path, Lib/json/__init__.py:166-168, 231-233", status := .proven
    prop := ``DumpsFastPath, thm := some ``dumpsFastPath_proven },
  { id := "json-dump-is-dumps", pyFile := "Lib/json/__init__.py"
    pyFns := ["dump", "dumps", "_make_iterencode", "JSONEncoder.iterencode"]
    statement := "json.dump writes what json.dumps returns: with a write that does not fail, the chunks join to the text of dumps, or the generator raises what dumps raises, for every option and value of json-dumps-twins."
    source := "json docs (dump and dumps); invariant: dump uses the Python generator even with _json", status := .proven
    prop := ``DumpIsDumps, thm := some ``dumpIsDumps_proven },
  { id := "json-dump-prefix", pyFile := "Lib/json/__init__.py"
    pyFns := ["dump"]
    statement := "When fp.write fails, json.dump has written a prefix of the chunks of the generator."
    source := "invariant", status := .proven
    prop := ``DumpPrefix, thm := some ``dumpPrefix_proven },
  { id := "json-iterencode-join", pyFile := "Lib/json/encoder.py"
    pyFns := ["JSONEncoder.iterencode", "_make_iterencode"]
    statement := "For every value and option, ''.join(JSONEncoder().iterencode(o)) is JSONEncoder().encode(o) with the pure-Python encoder, or the generator ends with the same exception."
    source := "JSONEncoder.iterencode docstring, invariant: _one_shot only changes speed", status := .proven
    prop := ``IterencodeJoin, thm := some ``iterencodeJoin_proven },
  { id := "json-allow-nan", pyFile := "Lib/json/encoder.py"
    pyFns := ["JSONEncoder.iterencode", "encoder_encode_float"]
    statement := "For every float in both encoders: a finite one gives its repr; a non-finite one gives NaN, Infinity or -Infinity, or with allow_nan=False raises ValueError naming its repr."
    source := "JSONEncoder.__init__ docstring (allow_nan)", status := .proven
    prop := ``AllowNan, thm := some ``allowNan_proven
    notes := "Exact statements on the IEEE-754 bit pattern; no float arithmetic is involved and repr is a parameter." },
  { id := "json-default-typeerror", pyFile := "Lib/json/encoder.py"
    pyFns := ["JSONEncoder.default"]
    statement := "Under JSONEncoder.default, an object the encoder does not know raises TypeError naming its type, in both encoders."
    source := "JSONEncoder.default docstring", status := .proven
    prop := ``DefaultTypeError, thm := some ``defaultTypeError_proven
    notes := "default= in general is part of json-dumps-twins." },
  { id := "json-default-separators", pyFile := "Lib/json/encoder.py"
    pyFns := ["JSONEncoder.__init__"]
    statement := "Without separators, key_separator is ': ' and item_separator is ', ' when indent is None and ',' otherwise."
    source := "JSONEncoder.__init__ docstring, Lib/json/encoder.py:138-142", status := .proven
    prop := ``DefaultSeparators, thm := some ``defaultSeparators_proven },
  { id := "json-encode-basestring-twins", pyFile := "Lib/json/encoder.py"
    pyFns := ["py_encode_basestring", "py_encode_basestring_ascii"]
    statement := "encode_basestring and encode_basestring_ascii: the C functions and their Python twins agree on every str; a non-str gets TypeError from C."
    source := "invariant: C/Python twins", status := .proven
    prop := ``EncodeBasestringTwins, thm := some ``encodeBasestringTwins_proven },
  { id := "json-c-encode-basestring", pyFile := "Modules/_json.c"
    pyFns := ["py_encode_basestring_impl", "py_encode_basestring_ascii_impl", "ascii_escape_unichar", "ascii_escape_unicode", "ascii_escape_unicode_and_size", "escape_unicode", "escape_unicode_and_size"]
    statement := "As json-encode-basestring-twins, for the C wrappers, with the type check and message of their Argument Clinic signature."
    source := "invariant: C/Python twins", status := .proven
    prop := ``EncodeBasestringTwins, thm := some ``encodeBasestringTwins_proven
    notes := "The OverflowError for a string too long to escape needs more than 2^59 code points and is not modelled." },
  { id := "json-write-escaped", pyFile := "Modules/_json.c"
    pyFns := ["write_escaped_ascii", "write_escaped_unicode", "ascii_escape_size", "escape_size"]
    statement := "write_escaped_ascii and write_escaped_unicode write what ascii_escape_unicode and escape_unicode return, for every str: their direct path, taken on output_size == input_chars + 2, is taken exactly when no character needs escaping."
    source := "invariant: the two paths of write_escaped_*, Modules/_json.c:241-276, :388-419", status := .proven
    prop := ``WriteEscaped, thm := some ``writeEscaped_proven
    notes := "str subclasses take these paths too, without str() (gh-148241); the difftest runs them with a __str__ that would show." },
  { id := "json-roundtrip-str", pyFile := "Lib/json/encoder.py"
    pyFns := ["py_encode_basestring_ascii", "ascii_escape_unicode", "scanstring_unicode"]
    statement := "For every str t, json.loads(json.dumps(t, ...)) == t, for every ensure_ascii setting, both encoders and both decoders."
    source := "round trip (json docs: dumps/loads)", status := .refuted
    prop := ``RoundTripStr, thm := some ``roundTripStr_refuted
    bug := some "json-roundtrip-surrogate-pair"
    notes := "'\\ud834\\udd1e' (two code points) comes back as '\\U0001d11e' with ensure_ascii=True. Known: gh-94527 (open)." },
  { id := "json-roundtrip", pyFile := "Lib/json/encoder.py"
    pyFns := ["JSONEncoder.encode", "encoder_listencode_obj", "encoder_listencode_list", "encoder_listencode_dict", "JSONObject", "JSONArray", "scan_once_unicode"]
    statement := "loads(dumps(v)) == v for every JSON-representable v (None, bool, int, str, list, dict with str keys), both encoders and decoders, every strict, every default, every white-space indent and every separators built from ',' and ':' with white space, provided that with ensure_ascii=True no string holds a high surrogate immediately followed by a low surrogate."
    source := "round trip (json docs); the proviso is exactly json-roundtrip-str", status := .proven
    prop := ``RoundTrip, thm := some ``roundTrip_proven
    notes := "Hypotheses: Layout (the output is JSON at all), DCfg.Rec (hooks build the items), sort_keys=False (with it dict items come back reordered, which dict equality ignores; objects are compared as item lists here), default parse_int, Python value invariants (str code points, distinct dict keys). Ints of more than 4300 digits: dumps raises, so the statement is about values dumps accepts." },
  { id := "json-dumps-accepted", pyFile := "Lib/json/encoder.py"
    pyFns := ["JSONEncoder.encode", "encoder_listencode_obj", "scan_once_unicode"]
    statement := "If dumps(v) returns a text, for any value without float values, every default, ensure_ascii, sort_keys, skipkeys and check_circular, a white-space indent and separators built from ',' and ':', then loads accepts that text, in both decoders, for every strict and for hooks that return."
    source := "json docs: dumps serializes to a JSON formatted str; invariant", status := .proven
    prop := ``DumpsAccepted, thm := some ``dumpsAccepted_proven
    notes := "Includes non-str keys (int, float, bool, None), skipped keys, lone surrogates and surrogate pairs. Float values: json-dumps-accepted-float." },
  { id := "json-decode-terminates", pyFile := "Lib/json/decoder.py"
    pyFns := ["JSONDecoder.raw_decode", "py_make_scanner", "scan_once_unicode"]
    statement := "For every str s, every decoder setting and 0 <= idx <= sys.maxsize, raw_decode(s, idx) ends with a value or a Python exception in both twins (the models never exhaust their fuel, so the twin theorems are about real outcomes)."
    source := "invariant: no hang", status := .proven
    prop := ``DecodeTerminates, thm := some ``decodeTerminates_proven
    notes := "RecursionError on deep nesting is out of scope." },
  { id := "json-strict-only-control", pyFile := "Lib/json/decoder.py"
    pyFns := ["JSONDecoder.__init__", "py_scanstring", "scanstring_unicode"]
    statement := "For every document, loads with strict=True gives the same result as with strict=False, or an 'Invalid control character' error at a character of code 0-31, in both twins."
    source := "JSONDecoder.__init__ docstring, Lib/json/decoder.py:334-337", status := .proven
    prop := ``StrictOnlyControl, thm := some ``strictOnlyControl_proven },
  { id := "json-strict-literal", pyFile := "Lib/json/decoder.py"
    pyFns := ["py_scanstring", "scanstring_unicode"]
    statement := "A string literal without quotes or backslashes is accepted with strict=False and gives its characters back; with strict=True it is accepted exactly when it has no character of code 0-31; in both twins."
    source := "JSONDecoder.__init__ docstring, Lib/json/decoder.py:334-337", status := .proven
    prop := ``StrictLiteral, thm := some ``strictLiteral_proven },
  { id := "json-ensure-ascii-output", pyFile := "Lib/json/encoder.py"
    pyFns := ["JSONEncoder.encode", "py_encode_basestring_ascii", "ascii_escape_unicode", "ascii_escape_unichar"]
    statement := "With ensure_ascii=True, every code point of the output of either encoder is ASCII, for every value and default, unless indent or a separator is itself non-ASCII."
    source := "JSONEncoder.__init__ docstring, Lib/json/encoder.py:114-115", status := .proven
    prop := ``EnsureAsciiOutput, thm := some ``ensureAsciiOutput_proven },
  { id := "json-int-literal", pyFile := "Lib/json/scanner.py"
    pyFns := ["py_make_scanner", "_match_number_unicode"]
    statement := "A JSON int literal (optional '-', no leading zeros) under the default parse_int is decoded to its value when it has at most 4300 digits, and raises the ValueError of int() naming its digit count otherwise, in both twins."
    source := "int/str conversion length limit docs; JSONDecoder docstring (parse_int equivalent to int(num_str))", status := .proven
    prop := ``IntLiteral, thm := some ``intLiteral_proven },
  { id := "json-loads-api-twins", pyFile := "Lib/json/__init__.py"
    pyFns := ["loads", "load", "detect_encoding"]
    statement := "json.loads with _json and without it, for every keyword argument and every str, bytes or other argument: the same value, or exceptions of the same class."
    source := "invariant: C/Python twins", status := .proven
    prop := ``LoadsApiTwins, thm := some ``loadsApiTwins_proven
    notes := "Type invariant: the document has at most sys.maxsize characters. Messages differ only as in json-loads-twins-scan. bytes.decode with surrogatepass is modelled for the eight encodings detect_encoding returns; UnicodeDecodeError matches on class." },
  { id := "json-loads-rejects", pyFile := "Lib/json/__init__.py"
    pyFns := ["loads"]
    statement := "json.loads rejects an argument that is not str, bytes or bytearray with TypeError naming its type, and a str with a leading U+FEFF with JSONDecodeError at pos 0, whatever the options."
    source := "Lib/json/__init__.py:357-365", status := .proven
    prop := ``LoadsRejects, thm := some ``loadsRejects_proven },
  { id := "json-loads-fast-path", pyFile := "Lib/json/__init__.py"
    pyFns := ["loads", "JSONDecoder.__init__"]
    statement := "The fast path of json.loads agrees with an explicit JSONDecoder with the default options, on every argument."
    source := "invariant: fast path vs slow path, Lib/json/__init__.py:367-371", status := .proven
    prop := ``LoadsFastPath, thm := some ``loadsFastPath_proven },
  { id := "json-load-read", pyFile := "Lib/json/__init__.py"
    pyFns := ["load", "loads"]
    statement := "json.load(fp) is json.loads(fp.read()) with the same options, and an exception of read() propagates."
    source := "json.load docstring", status := .proven
    prop := ``LoadRead, thm := some ``loadRead_proven },
  { id := "json-detect-encoding", pyFile := "Lib/json/__init__.py"
    pyFns := ["detect_encoding"]
    statement := "A str of at least two characters whose first two are ASCII and not NUL, encoded in UTF-8, UTF-16-LE/BE or UTF-32-LE/BE without a BOM, is detected as that encoding."
    source := "RFC 4627 section 3, cited by Lib/json/__init__.py:247-274", status := .proven
    prop := ``DetectEncoding, thm := some ``detectEncoding_proven
    notes := "Hypothesis: ASCII and not NUL is what RFC 4627 relies on. A one-character text: json-detect-encoding-1." },
  { id := "json-detect-bom", pyFile := "Lib/json/__init__.py"
    pyFns := ["detect_encoding"]
    statement := "With a BOM, detect_encoding names the codec that consumes it: utf-8-sig, utf-32, utf-16, unless a UTF-16-LE BOM is followed by two NUL bytes, which is the UTF-32-LE BOM."
    source := "Lib/json/__init__.py:249-254", status := .proven
    prop := ``DetectBom, thm := some ``detectBom_proven },
  { id := "json-detect-encoding-1", pyFile := "Lib/json/__init__.py"
    pyFns := ["detect_encoding"]
    statement := "A one-character ASCII text, not NUL, encoded in any of the five encodings, is detected as that encoding."
    source := "RFC 4627 section 3", status := .proven
    prop := ``DetectEncoding1, thm := some ``detectEncoding1_proven },
  { id := "json-decode-error-reduce", pyFile := "Lib/json/decoder.py"
    pyFns := ["JSONDecodeError.__init__", "JSONDecodeError.__reduce__", "raise_errmsg"]
    statement := "JSONDecodeError(*e.__reduce__()[1]) has the same attributes and text as e for every message, document and position; str(e) is what the decoders print; and for pos >= 0, lineno >= 1 and 1 <= colno <= pos + 1."
    source := "invariant: pickle support; JSONDecodeError docstring", status := .proven
    prop := ``JdeReduce, thm := some ``jdeReduce_proven },
  { id := "json-decode-uxxxx", pyFile := "Lib/json/decoder.py"
    pyFns := ["_decode_uXXXX"]
    statement := "_decode_uXXXX reads back every \\uXXXX the encoders write, and reports the position of the u when four hex digits are not there."
    source := "round trip; Lib/json/decoder.py:60-68", status := .proven
    prop := ``DecodeUXXXX, thm := some ``decodeUXXXX_proven },
  { id := "json-decoder-init", pyFile := "Lib/json/decoder.py"
    pyFns := ["JSONDecoder.__init__"]
    statement := "JSONDecoder.__init__: the defaults give the default decoder, a false parse_float, parse_int or parse_constant behaves as if it were not given, object_hook, object_pairs_hook and array_hook are kept as given, and an unknown keyword raises TypeError."
    source := "Lib/json/decoder.py:339-350", status := .proven
    prop := ``DecoderInit, thm := some ``decoderInit_proven
    notes := "The false-callable behaviour is `parse_float or float`; bugforge reported it as cpython#158729, closed." },
  { id := "json-pairs-hook-priority", pyFile := "Lib/json/decoder.py"
    pyFns := ["JSONObject", "_parse_object_unicode", "JSONDecoder.__init__"]
    statement := "When object_pairs_hook is given, object_hook is never called: for every document, setting object_hook changes nothing, in both twins."
    source := "JSONDecoder.__init__ docstring, Lib/json/decoder.py:304-309", status := .proven
    prop := ``PairsHookPriority, thm := some ``pairsHookPriority_proven },
  { id := "json-array-hook", pyFile := "Lib/json/decoder.py"
    pyFns := ["JSONArray", "_parse_array_unicode", "JSONDecoder.__init__", "py_make_scanner"]
    statement := "array_hook replaces the list: one that gives its list back changes nothing, for every document and option, in both twins; on [] the result is what the hook returns or raises, StopIteration becoming JSONDecodeError at raw_decode."
    source := "JSONDecoder.__init__ docstring, Lib/json/decoder.py:311-317", status := .proven
    prop := ``ArrayHook, thm := some ``arrayHook_proven
    notes := "Agreement of the twins for an arbitrary hook on every document is json-loads-twins-scan." },
  { id := "json-scanstring-twins", pyFile := "Lib/json/decoder.py"
    pyFns := ["py_scanstring"]
    statement := "scanstring(s, end, strict): the C function and py_scanstring agree up to the two string-error differences, for every int end."
    source := "invariant: C/Python twins", status := .refuted
    prop := ``ScanstringTwins, thm := some ``scanstringTwins_refuted
    bug := some "json-py-raw-decode-negative-index"
    notes := "scanstring('ab', 5): ValueError (C) vs JSONDecodeError at char 4 (Python)." },
  { id := "json-scanstring-twins-in-range", pyFile := "Lib/json/decoder.py"
    pyFns := ["py_scanstring"]
    statement := "For 0 <= end <= len(s), scanstring(s, end, strict) agrees between the twins up to the two string-error differences."
    source := "invariant: C/Python twins", status := .proven
    prop := ``ScanstringTwinsInRange, thm := some ``scanstringTwinsInRange_proven
    notes := "The bounds on end are exactly the refuted cases of json-scanstring-twins." },
  { id := "json-c-scanstring", pyFile := "Modules/_json.c"
    pyFns := ["py_scanstring_impl", "scanstring_unicode", "_build_rval_index_tuple"]
    statement := "As json-scanstring-twins-in-range, for the C wrapper."
    source := "invariant: C/Python twins", status := .proven
    prop := ``ScanstringTwinsInRange, thm := some ``scanstringTwinsInRange_proven },
  { id := "json-scanner-call-raw", pyFile := "Modules/_json.c"
    pyFns := ["scanner_call", "raise_stop_iteration", "_build_rval_index_tuple"]
    statement := "JSONDecoder.raw_decode with the C scanner is scanner_call with StopIteration turned into JSONDecodeError, on every str and int index."
    source := "Lib/json/decoder.py:373-376", status := .proven
    prop := ``ScannerCallRaw, thm := some ``scannerCallRaw_proven },
  { id := "json-scanner-new", pyFile := "Modules/_json.c"
    pyFns := ["scanner_new"]
    statement := "make_scanner accepts an object with the seven attributes, reading strict by truth value, and one without strict raises AttributeError naming it."
    source := "Modules/_json.c:1255-1280", status := .proven
    prop := ``ScannerNew, thm := some ``scannerNew_proven },
  { id := "json-encoder-new", pyFile := "Modules/_json.c"
    pyFns := ["encoder_new"]
    statement := "c_make_encoder as JSONEncoder.iterencode calls it keeps every option."
    source := "invariant; Lib/json/encoder.py:254-257", status := .proven
    prop := ``EncoderNew, thm := some ``encoderNew_proven },
  { id := "json-encoder-new-sep-typeerror", pyFile := "Modules/_json.c"
    pyFns := ["encoder_new"]
    statement := "c_make_encoder refuses a key_separator that is not a str with TypeError, whatever its type."
    source := "invariant: PyArg_ParseTupleAndKeywords raises TypeError for an argument of the wrong type", status := .refuted
    prop := ``EncoderNewSepTypeError, thm := some ``encoderNewSepTypeError_refuted
    bug := some "getargs-snprintf-cut-utf8-decode"
    notes := "Witness: a type named 'a' + 'é' * 30. converterr (Python/getargs.c:682-684) cuts the name to 50 bytes with PyOS_snprintf, inside a character, and PyErr_SetString (seterror, :477) raises UnicodeDecodeError at byte 92. The model mirrors only the U unit's refusal path of convertsimple, converterr and seterror, so those rows are not claimed. The record's second site, set_mro_error, is a gap% in TypeObj/TypeNew.lean (setMroError): the TypeObj model has no UnicodeDecodeError object to raise." },
  { id := "json-encoder-call", pyFile := "Modules/_json.c"
    pyFns := ["encoder_call"]
    statement := "c_make_encoder(...)(o, 0) is the 1-tuple whose item is the text of dumps, or the same exception, with the two C encoders."
    source := "invariant; Lib/json/encoder.py:202-205", status := .proven
    prop := ``EncoderCallDumps, thm := some ``encoderCallDumps_proven },
  { id := "json-encoder-string", pyFile := "Modules/_json.c"
    pyFns := ["encoder_write_string"]
    statement := "encoder_write_string: with fast_encode what the C escape returns; otherwise the result of encoder, which must be a str, and its exception propagates."
    source := "Modules/_json.c:1537-1557", status := .proven
    prop := ``EncoderString, thm := some ``encoderString_proven },
  { id := "json-indent-cache", pyFile := "Modules/_json.c"
    pyFns := ["create_indent_cache", "update_indent_cache", "get_item_separator", "write_newline_indent"]
    statement := "From create_indent_cache at any level i >= 0, at every level k reached one at a time, get_item_separator returns item_separator + '\\n' + indent * (k + i), write_newline_indent returns '\\n' + indent * (k + i), and the invariant of the comment holds."
    source := "the comment at Modules/_json.c:1362-1371", status := .proven
    prop := ``IndentCacheSpec, thm := some ``indentCacheSpec_proven
    notes := "This is what makes cEnc, which writes those strings directly, faithful to the C code. A negative level cannot come from iterencode, which passes 0." },
  { id := "json-indent-cache-size", pyFile := "Modules/_json.c"
    pyFns := ["update_indent_cache"]
    statement := "Entry 2*k of the indent cache has 1 + (k + i) * len(indent) characters, and entry 2*k-1 is longer by len(item_separator): the cache is quadratic in the depth."
    source := "invariant", status := .proven
    prop := ``IndentCacheSize, thm := some ``indentCacheSize_proven
    notes := "With check_circular=False and a cycle this reaches gigabytes: bugs/json-indent-recursion-memory.yaml." },
  { id := "json-tool-colorize", pyFile := "Lib/json/tool.py"
    pyFns := ["_colorize_json"]
    statement := "_colorize_json only inserts theme strings: with a theme of empty strings every text comes back unchanged, valid JSON or not."
    source := "invariant", status := .proven
    prop := ``ColorizeStrip, thm := some ``colorizeStrip_proven },
  { id := "json-tool-invalid", pyFile := "Lib/json/tool.py"
    pyFns := ["main"]
    statement := "python -m json.tool on an invalid document writes nothing and ends with SystemExit carrying the text of the exception."
    source := "Lib/json/tool.py:115-116", status := .proven
    prop := ``ToolInvalid, thm := some ``toolInvalid_proven
    notes := "main is modelled after parser.parse_args(); argparse itself is out of scope." },
  { id := "json-tool-lines", pyFile := "Lib/json/tool.py"
    pyFns := ["main"]
    statement := "With --json-lines the objects are decoded lazily: a line is written before the next one is decoded, so the lines before a bad one reach the output."
    source := "Lib/json/tool.py:93", status := .proven
    prop := ``ToolLinesPrefix, thm := some ``toolLinesPrefix_proven },
  { id := "json-tool-roundtrip", pyFile := "Lib/json/tool.py"
    pyFns := ["main"]
    statement := "python -m json.tool keeps the document: a value without floats on which json-roundtrip applies comes back from the text written, for every indent option and --compact."
    source := "json.tool docs: validate and pretty-print", status := .open
    prop := ``ToolRoundTrip
    notes := "Missing: json-roundtrip with the trailing newline, and toE/toJ for decoded values." },
  { id := "json-loads-bytes", pyFile := "Lib/json/__init__.py"
    pyFns := ["loads", "detect_encoding"]
    statement := "json.loads on the bytes of a str in any of the five encodings gives the result of json.loads on the str, when its first two characters are ASCII and not NUL and, in UTF-16, no high surrogate is followed by a low surrogate."
    source := "json.loads docstring", status := .open
    prop := ``LoadsBytes
    notes := "Missing: decode(encode(s)) == s for the three codecs. detect_encoding is json-detect-encoding." },
  { id := "json-roundtrip-float", pyFile := "Lib/json/encoder.py"
    pyFns := ["encoder_encode_float", "_match_number_unicode"]
    statement := "A finite float comes back through parse_float, whose argument is exactly its repr; with the default float, loads(dumps(x)) == x."
    source := "round trip; float.__repr__ round-trips", status := .open
    prop := ``RoundTripFloat
    notes := "Waits for lean/PyLean/Binary64: the grammar of float.__repr__ and float(repr(x)) == x." },
  { id := "json-dumps-accepted-float", pyFile := "Lib/json/encoder.py"
    pyFns := ["JSONEncoder.encode", "scan_once_unicode"]
    statement := "json-dumps-accepted for values with floats, NaN and Infinity included."
    source := "json docs; invariant", status := .open
    prop := ``DumpsAcceptedFloat
    notes := "Waits for lean/PyLean/Binary64: dec_enc needs the grammar of float.__repr__." }
]

end PyLean.JsonMod
