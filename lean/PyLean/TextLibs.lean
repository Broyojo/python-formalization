import PyLean.Registry
import PyLean.TextLibs.Diff
import PyLean.TextLibs.StructClose
import PyLean.TextLibs.BinasciiProps2
import PyLean.TextLibs.CsvProps
import PyLean.TextLibs.ReParseProps

/-!
Text and binary formats, CPython 3.14.7. `Modules/_struct.c` is modelled in
`TextLibs/StructModel.lean`, on the x86-64 LP64 little-endian build the difftest runs on,
with floats as exact bit patterns (`TextLibs/Bits.lean`). `lu_short`, `lu_longlong`,
`lp_longlong` and similar routines are replaced by native ones at start-up on this build,
so only the proofs reach them, not the difftest.

`Modules/binascii.c` and `Lib/base64.py` are in `TextLibs/BinasciiModel.lean` and
`TextLibs/BinasciiRest.lean`; `hexlify`'s `sep` argument is not modelled. `Modules/_csv.c` and
`Lib/csv.py` are in `TextLibs/CsvModel.lean`, whose `float()` covers ASCII text only.
`Lib/re/_parser.py` is in `TextLibs/ReParse.lean`, without `\\N{...}` and non-ASCII group names.
-/

namespace PyLean.TextLibs

open PyLean.Registry
open PyLean.TextLibs.Struct
open PyLean.TextLibs.Binascii
open PyLean.TextLibs.Csv
open PyLean.TextLibs.Re

/-- The integer routines `IntCodesRoundTrip` drives through `runPack` and `runUnpack`. -/
def structIntFns : List String :=
  ["get_pylong", "get_long", "get_ulong", "get_longlong", "get_ulonglong", "get_ssize_t",
   "get_size_t",
   "nu_byte", "nu_ubyte", "nu_short", "nu_ushort", "nu_int", "nu_uint", "nu_long", "nu_ulong",
   "nu_ssize_t", "nu_size_t", "nu_longlong", "nu_ulonglong", "nu_void_p",
   "np_byte", "np_ubyte", "np_short", "np_ushort", "np_int", "np_uint", "np_long", "np_ulong",
   "np_ssize_t", "np_size_t", "np_longlong", "np_ulonglong", "np_void_p",
   "bu_short", "bu_int", "bu_uint", "bu_longlong", "bu_ulonglong",
   "bp_int", "bp_uint", "bp_longlong", "bp_ulonglong",
   "lu_short", "lu_int", "lu_uint", "lu_longlong", "lu_ulonglong",
   "lp_int", "lp_uint", "lp_longlong", "lp_ulonglong"]

def entries : List Entry := [
  { id := "textlibs-struct-int-round-trip", pyFile := "Modules/_struct.c", pyFns := structIntFns
    statement := "For every integer entry of every format table, including the little-endian table before init_endian_tables runs, and every value in that entry's range, pack succeeds, gives exactly size bytes, and unpack returns the value."
    source := "docs: the format table's standard sizes and ranges", status := .proven
    prop := ``IntCodesRoundTrip, thm := some ``intCodesRoundTrip_proven
    notes := "Goes through the runPack/runUnpack dispatch, including the C sign extension. P reads back unsigned, so it is stated on 0..2**64-1; its negative range does not round trip, by design of nu_void_p." },
  { id := "textlibs-struct-endian-tables", pyFile := "Modules/_struct.c", pyFns := ["init_endian_tables"]
    statement := "init_endian_tables keeps every format, size and alignment, swaps in the native routines for F and D, and keeps the standard routines for f, d, ? and the 4-byte l, L."
    source := "comments at Modules/_struct.c:1521-1543", status := .proven
    prop := ``EndianTableSwap, thm := some ``endianTableSwap_proven },
  { id := "textlibs-struct-align", pyFile := "Modules/_struct.c", pyFns := ["align"]
    statement := "For every size <= PY_SSIZE_T_MAX and non-zero alignment, align returns the next multiple of the alignment, or fails only when that multiple would pass PY_SSIZE_T_MAX."
    source := "comment at Modules/_struct.c:1597", status := .proven
    prop := ``AlignNextMultiple, thm := some ``alignNextMultiple_proven },
  { id := "textlibs-struct-bool-nonzero", pyFile := "Modules/_struct.c", pyFns := ["nu_bool", "bu_bool"]
    statement := "The ? code reads every non-zero byte as True, in native and in standard mode."
    source := "docs: format characters, note on ?", status := .proven
    prop := ``BoolAnyNonzero, thm := some ``boolAnyNonzero_proven },
  { id := "textlibs-struct-s-pads", pyFile := "Modules/_struct.c", pyFns := ["s_pack_internal"]
    statement := "An s field of size n holds the first n bytes of the value, padded with NUL bytes."
    source := "docs: the s format character", status := .proven
    prop := ``PackSPads, thm := some ``packSPads_proven },
  { id := "textlibs-struct-unpack-length", pyFile := "Modules/_struct.c", pyFns := ["Struct_unpack_impl", "unpack_impl"]
    statement := "unpack raises struct.error with the source's message for every buffer whose length is not the struct size."
    source := "docstring: the buffer's size in bytes must be Struct.size", status := .proven
    prop := ``UnpackWrongLength, thm := some ``unpackWrongLength_proven },
  { id := "textlibs-struct-iter-zero-size", pyFile := "Modules/_struct.c", pyFns := ["Struct_iter_unpack_impl", "iter_unpack_impl"]
    statement := "iter_unpack raises struct.error for a zero-sized struct, for every buffer."
    source := "invariant: the loop would not advance; Modules/_struct.c:2129", status := .proven
    prop := ``IterUnpackZeroSize, thm := some ``iterUnpackZeroSize_proven },
  { id := "textlibs-struct-pack-count", pyFile := "Modules/_struct.c", pyFns := ["s_pack"]
    statement := "pack raises struct.error with the source's message for every wrong argument count, before converting any argument."
    source := "docs: the values must match the format exactly", status := .proven
    prop := ``PackWrongCount, thm := some ``packWrongCount_proven },
  { id := "textlibs-struct-le-complex-float-overflow", pyFile := "Modules/_struct.c"
    pyFns := ["np_float_complex", "bp_float_complex", "s_pack", "pack"]
    statement := "<F and >F accept the same values: byte order changes the bytes, not whether a value can be packed."
    source := "invariant: f, <f and >f all raise OverflowError", status := .refuted
    prop := ``StdComplexOrderAgree, thm := some ``stdComplexOrderAgree_refuted
    bug := some "textlibs-struct-le-complex-float-overflow"
    notes := "Duplicate of python/cpython#156865, fixed on main by #156868; 3.14.7 still has it." },
  { id := "textlibs-struct-bytes-format-nonascii-error", pyFile := "Modules/_struct.c"
    pyFns := ["cache_struct_converter", "Struct___init___impl", "pack"]
    statement := "pack(fmt, ...) and Struct(fmt).pack(...) give the same result for every format object."
    source := "docs: module functions are equivalent to the Struct methods", status := .refuted
    prop := ``ModuleMatchesStruct, thm := some ``moduleMatchesStruct_refuted
    bug := some "textlibs-struct-bytes-format-nonascii-error"
    notes := "3.14 only; main redesigned this in python/cpython#145850. Low value." },
  { id := "textlibs-struct-void-p-index-overflow", pyFile := "Modules/_struct.c", pyFns := ["np_void_p", "s_pack_internal"]
    statement := "An __index__ object packs with P exactly like the equal int: same bytes or same error."
    source := "invariant: every other integer code", status := .refuted
    prop := ``PIndexLikeInt, thm := some ``pIndexLikeInt_refuted
    bug := some "textlibs-struct-void-p-index-overflow"
    notes := "Reproduces on main too. Trivial on its own." },
  { id := "textlibs-struct-pack-into-0p-outside-field", pyFile := "Modules/_struct.c"
    pyFns := ["s_pack_internal", "s_pack_into", "pack_into"]
    statement := "pack_into changes no byte outside the calcsize(format) bytes at offset."
    source := "invariant", status := .refuted
    prop := ``PackIntoStaysInside, thm := some ``packIntoStaysInside_refuted
    bug := some "textlibs-struct-pack-into-0p-outside-field"
    notes := "Duplicate of python/cpython#158762, closed for flooding, not on the merits; main no longer has it." },
  { id := "textlibs-struct-half-round-trip", pyFile := "Modules/_struct.c"
    pyFns := ["unpack_halffloat", "pack_halffloat", "nu_halffloat", "np_halffloat"]
    statement := "For every non-NaN 16-bit pattern, packing the unpacked half float gives back the same two bytes."
    source := "invariant", status := .open
    prop := ``HalfRoundTrip
    notes := "CPython agrees on all 65536 patterns (scratch sweep). decide +kernel passes the first 1024 patterns but hits a deterministic timeout on 65536; this needs a symbolic proof, not a smaller range." },
  { id := "textlibs-struct-float-round-trip", pyFile := "Modules/_struct.c"
    pyFns := ["unpack_float", "lu_float", "lp_float"]
    statement := "For every non-NaN 32-bit pattern, packing the unpacked float gives back the same four bytes."
    source := "invariant", status := .open
    prop := ``FloatRoundTrip
    notes := "Needs a symbolic proof over encodeRounded, especially for subnormal floats." },
  { id := "textlibs-struct-prepare-two-passes", pyFile := "Modules/_struct.c"
    pyFns := ["prepare_s", "whichtable", "getentry"]
    statement := "For every format prepare_s accepts, its two passes agree: s_size is the first pass's size, s_len is the sum of the codes' repeats, and there is one code per counted item."
    source := "invariant: pack reads s_len arguments by walking the codes (Modules/_struct.c:2178-2183)", status := .proven
    prop := ``PrepareSAgree, thm := some ``prepareSAgree_proven },
  { id := "textlibs-struct-char-code", pyFile := "Modules/_struct.c", pyFns := ["nu_char", "np_char"]
    statement := "c round-trips every byte and rejects every value that is not a length-1 bytes object."
    source := "docs: the c format character", status := .proven
    prop := ``CharCode, thm := some ``charCode_proven },
  { id := "textlibs-struct-bool-code", pyFile := "Modules/_struct.c", pyFns := ["np_bool", "bp_bool", "nu_bool", "bu_bool"]
    statement := "? stores the truth value of any object in one byte and reads it back, in native and standard mode."
    source := "docs: format characters, note on ?", status := .proven
    prop := ``BoolCode, thm := some ``boolCode_proven },
  { id := "textlibs-struct-scalar-byte-order", pyFile := "Modules/_struct.c"
    pyFns := ["unpack_halffloat", "pack_halffloat", "unpack_float", "unpack_double", "nu_halffloat", "np_halffloat",
      "bu_halffloat", "lu_halffloat", "bp_halffloat", "lp_halffloat", "bu_float", "lu_float", "bp_float", "lp_float",
      "bu_double", "lu_double", "bp_double", "lp_double", "nu_double", "np_double"]
    statement := "For e, f and d, little-endian bytes are the reverse of big-endian bytes for every value (or both raise the same error), and unpacking a buffer little-endian equals unpacking its reverse big-endian."
    source := "docs: byte order is the only difference between < and >", status := .proven
    prop := ``ScalarByteOrder, thm := some ``scalarByteOrder_proven
    notes := "True on 3.14.7. On main <f quiets a signalling NaN and >f does not; see textlibs-struct-native-float-snan." },
  { id := "textlibs-struct-native-float-pack", pyFile := "Modules/_struct.c", pyFns := ["np_float"]
    statement := "Native f packs every value to the reverse of >f's bytes, or raises the same error."
    source := "docs: native order is little-endian on this build", status := .proven
    prop := ``NativeFloatPack, thm := some ``nativeFloatPack_proven },
  { id := "textlibs-struct-complex-byte-order", pyFile := "Modules/_struct.c"
    pyFns := ["bu_double_complex", "lu_double_complex", "bp_double_complex", "lp_double_complex", "nu_double_complex",
      "np_double_complex", "lu_float_complex", "lp_float_complex", "bu_float_complex", "bp_float_complex"]
    statement := "For D, and for F through the standard routines, the little-endian bytes are each part byte-reversed in place, for every value and every buffer of the right size."
    source := "docs: byte order is the only difference between < and >", status := .proven
    prop := ``ComplexByteOrder, thm := some ``complexByteOrder_proven
    notes := "lu_float_complex, lp_float_complex, lu_double_complex and lp_double_complex are replaced at start-up on this build, so only proofs reach them." },
  { id := "textlibs-struct-native-float-snan", pyFile := "Modules/_struct.c", pyFns := ["nu_float"]
    statement := "unpack('f', b) and unpack('<f', b) agree on every 4-byte buffer."
    source := "invariant: native and little-endian differ only in alignment on this build", status := .refuted
    prop := ``NativeFloatMatchesStd, thm := some ``nativeFloatMatchesStd_refuted
    bug := some "textlibs-struct-native-float-snan" },
  { id := "textlibs-struct-native-complex-snan", pyFile := "Modules/_struct.c", pyFns := ["nu_float_complex"]
    statement := "unpack('F', b) and unpack('>F', swapped b) agree on every 8-byte buffer."
    source := "invariant: byte order is the only difference", status := .refuted
    prop := ``NativeComplexMatchesBig, thm := some ``nativeComplexMatchesBig_refuted
    bug := some "textlibs-struct-native-float-snan" },
  { id := "textlibs-struct-unpack-from-offsets", pyFile := "Modules/_struct.c", pyFns := ["Struct_unpack_from_impl", "unpack_from_impl"]
    statement := "A negative offset counts from the end of the buffer, and offset 0 on an exact-size buffer is unpack."
    source := "docstring: a negative offset counts from the end of the buffer", status := .proven
    prop := ``UnpackFromOffsets, thm := some ``unpackFromOffsets_proven
    notes := "Hypothesis len < 2**63 is the type invariant of a Python buffer." },
  { id := "textlibs-struct-iter-length", pyFile := "Modules/_struct.c", pyFns := ["unpackiter_len", "unpackiter_iternext"]
    statement := "iter_unpack yields exactly len(buffer) / size tuples, which is the fresh iterator's __length_hint__."
    source := "docstring: the bytes length must be a multiple of the struct size", status := .proven
    prop := ``IterUnpackLength, thm := some ``iterUnpackLength_proven },
  { id := "textlibs-struct-accessors", pyFile := "Modules/_struct.c", pyFns := ["s_get_format", "s_get_size", "s_sizeof", "calcsize_impl"]
    statement := "For every accepted str format, Struct(fmt).format == fmt, .size and calcsize(fmt) are the size prepare_s computed, and __sizeof__ counts one formatcode per code plus the sentinel."
    source := "docs: Struct.format, Struct.size", status := .proven
    prop := ``Accessors, thm := some ``accessors_proven },
  { id := "textlibs-struct-uninitialized", pyFile := "Modules/_struct.c", pyFns := ["s_new"]
    statement := "Before __init__, .size is -1 and every method raises RuntimeError."
    source := "invariant: ENSURE_STRUCT_IS_READY, Modules/_struct.c:1914-1921", status := .proven
    prop := ``UninitStruct, thm := some ``uninitStruct_proven },
  { id := "textlibs-struct-range-error", pyFile := "Modules/_struct.c", pyFns := ["_range_error"]
    statement := "_range_error's message states the exact range of the entry, for every integer entry that uses it."
    source := "invariant", status := .proven
    prop := ``RangeErrorBounds, thm := some ``rangeErrorBounds_proven },
  { id := "textlibs-struct-repr", pyFile := "Modules/_struct.c", pyFns := ["s_repr"]
    statement := "repr(Struct(fmt)) of a format without control characters is Struct('fmt')."
    source := "invariant: repr round-trips the format", status := .proven
    prop := ``ReprPlain, thm := some ``reprPlain_proven },
  { id := "textlibs-binascii-base64-round-trip", pyFile := "Modules/binascii.c"
    pyFns := ["binascii_a2b_base64_impl", "binascii_b2a_base64_impl"]
    statement := "a2b_base64(b2a_base64(d, newline=False), strict_mode=s) == d for every bytes value d and both strict modes."
    source := "RFC 4648 and the module's purpose: encoding then decoding returns the data", status := .proven
    prop := ``Base64RoundTrip, thm := some ``base64RoundTrip_proven
    notes := "The 32-bit wrap of leftchar is modelled and shown harmless: the encoder only reads low bytes." },
  { id := "textlibs-binascii-base64-lenient-filter", pyFile := "Modules/binascii.c", pyFns := ["binascii_a2b_base64_impl"]
    statement := "With strict_mode=False, removing every byte that is neither in the alphabet nor '=' changes nothing, including which error is raised and its message."
    source := "base64.b64decode docstring: non-alphabet characters are discarded prior to the padding check", status := .proven
    prop := ``LenientIgnoresNonAlphabet, thm := some ``lenientIgnoresNonAlphabet_proven },
  { id := "textlibs-binascii-base64-strict-implies-lenient", pyFile := "Modules/binascii.c", pyFns := ["binascii_a2b_base64_impl"]
    statement := "Whatever strict_mode=True accepts, strict_mode=False accepts with the same result."
    source := "docs: strict mode only disallows more input", status := .proven
    prop := ``StrictImpliesLenient, thm := some ``strictImpliesLenient_proven },
  { id := "textlibs-binascii-base64-length", pyFile := "Modules/binascii.c", pyFns := ["binascii_b2a_base64_impl"]
    statement := "len(b2a_base64(d, newline=False)) == 4 * ceil(len(d) / 3) for every bytes value d."
    source := "RFC 4648 section 4", status := .proven
    prop := ``B2aLength, thm := some ``b2aLength_proven },
  { id := "textlibs-binascii-hex-round-trip", pyFile := "Modules/binascii.c"
    pyFns := ["binascii_b2a_hex_impl", "binascii_hexlify_impl", "binascii_a2b_hex_impl", "binascii_unhexlify_impl"]
    statement := "unhexlify(hexlify(d)) == d for every bytes value d."
    source := "docs: a2b_hex is the inverse of b2a_hex", status := .proven
    prop := ``HexRoundTrip, thm := some ``hexRoundTrip_proven
    notes := "hexlify's sep and bytes_per_sep arguments are not modelled." },
  { id := "textlibs-base64-round-trip", pyFile := "Lib/base64.py"
    pyFns := ["b64encode", "b64decode", "_bytes_from_decode_data"]
    statement := "b64decode(b64encode(d), validate=v) == d for every bytes value d and both modes."
    source := "docs: b64decode decodes what b64encode produces", status := .proven
    prop := ``B64ModuleRoundTrip, thm := some ``b64ModuleRoundTrip_proven
    notes := "Stated without altchars. The str branch of _bytes_from_decode_data is covered by the difftest only." },
  { id := "textlibs-binascii-ascii-buffer", pyFile := "Modules/binascii.c", pyFns := ["ascii_buffer_converter"]
    statement := "An ASCII str and the equal bytes convert alike; any other str raises ValueError."
    source := "docs: a2b functions accept ASCII-only unicode strings", status := .proven
    prop := ``AsciiBuffer, thm := some ``asciiBuffer_proven },
  { id := "textlibs-binascii-crc-incremental", pyFile := "Modules/binascii.c", pyFns := ["binascii_crc_hqx_impl"]
    statement := "crc_hqx(a + b, c) == crc_hqx(b, crc_hqx(a, c)) for all bytes a, b and every int c."
    source := "docstring: compute CRC-CCITT incrementally", status := .proven
    prop := ``CrcIncremental, thm := some ``crcIncremental_proven },
  { id := "textlibs-binascii-crc-table", pyFile := "Modules/binascii.c", pyFns := ["binascii_crc_hqx_impl"]
    statement := "crctab_hqx has 256 entries, each the bitwise CRC of its index for the CCITT polynomial 0x1021."
    source := "docstring: CRC-CCITT", status := .proven
    prop := ``CrcTableIsCcitt, thm := some ``crcTableIsCcitt_proven
    notes := "The table is copied mechanically from the C source." },
  { id := "textlibs-binascii-to-hex", pyFile := "Modules/binascii.c", pyFns := ["to_hex"]
    statement := "to_hex writes two hex digits that decode back to the byte, for every byte."
    source := "invariant", status := .proven
    prop := ``ToHexInverse, thm := some ``toHexInverse_proven },
  { id := "textlibs-binascii-a2b-qp-plain", pyFile := "Modules/binascii.c", pyFns := ["binascii_a2b_qp_impl"]
    statement := "a2b_qp leaves bytes without '=' unchanged, for header=False."
    source := "RFC 2045 rule 2: literal representation", status := .proven
    prop := ``A2bQpPlain, thm := some ``a2bQpPlain_proven },
  { id := "textlibs-binascii-qp-line-length", pyFile := "Modules/binascii.c", pyFns := ["binascii_b2a_qp_impl"]
    statement := "Every line b2a_qp writes has at most MAXLINESIZE (76) characters, not counting line ends."
    source := "RFC 2045 section 6.7 rule 5; MAXLINESIZE at Modules/binascii.c:958", status := .refuted
    prop := ``QpLineLimit, thm := some ``qpLineLimit_refuted
    bug := some "textlibs-binascii-qp-line-length"
    notes := "74 'a', a space and a newline give a 77-character line. The first pass counts the same bytes, so the buffer is big enough." },
  { id := "textlibs-base64-standard-round-trip", pyFile := "Lib/base64.py"
    pyFns := ["standard_b64encode", "standard_b64decode"]
    statement := "standard_b64decode(standard_b64encode(d)) == d for every bytes value d."
    source := "docstrings", status := .proven
    prop := ``StandardRoundTrip, thm := some ``standardRoundTrip_proven },
  { id := "textlibs-base64-input-check", pyFile := "Lib/base64.py", pyFns := ["_input_type_check"]
    statement := "_input_type_check accepts exactly one-dimensional views of single-byte formats."
    source := "the checks' messages", status := .proven
    prop := ``InputTypeCheck, thm := some ``inputTypeCheck_proven },
  { id := "textlibs-base64-main-flags", pyFile := "Lib/base64.py", pyFns := ["main"]
    statement := "main runs the function of the last -e, -d or -u flag, unless -h came first."
    source := "the usage text", status := .proven
    prop := ``MainLastFlagWins, thm := some ``mainLastFlagWins_proven
    notes := "Only the flag loop: file handling is not modelled, and the difftest stubs out encode and decode." },
  { id := "textlibs-re-digit-limit-parse", pyFile := "Lib/re/_parser.py"
    pyFns := ["_parse", "parse"]
    statement := "For every allowed sys.set_int_max_str_digits value, a str pattern parsed with no flags reports a bad pattern as PatternError or OverflowError, and never leaks ValueError."
    source := "docs: re.compile raises PatternError; Lib/re/_parser.py:671", status := .refuted
    prop := ``ParseNoValueError, thm := some ``parseNoValueError_refuted
    bug := some "textlibs-re-int-digit-limit"
    notes := "Counterexample at the lowest allowed limit, 640, with 641 digits, because the kernel cannot evaluate the parser on 4301. The YAML reproducer shows the default limit on CPython. The parser model agrees with CPython on whole trees, widths and exact error messages." },
  { id := "textlibs-re-digit-limit-template", pyFile := "Lib/re/_parser.py", pyFns := ["parse_template"]
    statement := "For every allowed sys.set_int_max_str_digits value, a replacement template reports a bad group reference as PatternError, and never leaks ValueError."
    source := "docs: re.sub", status := .refuted
    prop := ``TemplateNoValueError, thm := some ``templateNoValueError_refuted
    bug := some "textlibs-re-int-digit-limit" },
  { id := "textlibs-re-parse-plain", pyFile := "Lib/re/_parser.py"
    pyFns := ["State.__init__", "Tokenizer.__init__", "Tokenizer.__next", "Tokenizer.get", "_parse_sub", "_parse", "parse"]
    statement := "For every str pattern with no special character, parse returns its literal characters, one group, and UNICODE."
    source := "docs: re syntax, ordinary characters", status := .proven
    prop := ``ParsePlain, thm := some ``parsePlain_proven },
  { id := "textlibs-re-group-lifecycle", pyFile := "Lib/re/_parser.py"
    pyFns := ["State.groups", "State.opengroup", "State.closegroup", "State.checkgroup"]
    statement := "opengroup returns the next group number and grows groups by one, a new group cannot be referred to, and closegroup makes it referable."
    source := "the message at Lib/re/_parser.py:436", status := .proven
    prop := ``GroupLifecycle, thm := some ``groupLifecycle_proven },
  { id := "textlibs-re-lookbehind-groups", pyFile := "Lib/re/_parser.py", pyFns := ["State.checklookbehindgroup"]
    statement := "Outside a lookbehind any group may be referred to; inside one, an open group or one opened in the same lookbehind is refused."
    source := "the messages at Lib/re/_parser.py:106-109", status := .proven
    prop := ``LookbehindLaw, thm := some ``lookbehindLaw_proven },
  { id := "textlibs-re-seek", pyFile := "Lib/re/_parser.py", pyFns := ["Tokenizer.seek"]
    statement := "seek(i) puts tell() at i when there is a token there."
    source := "invariant", status := .proven
    prop := ``SeekTell, thm := some ``seekTell_proven },
  { id := "textlibs-re-error-position", pyFile := "Lib/re/_parser.py", pyFns := ["Tokenizer.error"]
    statement := "Tokenizer.error reports the position tell() - offset."
    source := "Lib/re/_parser.py:302", status := .proven
    prop := ``ErrorPosition, thm := some ``errorPosition_proven },
  { id := "textlibs-re-match", pyFile := "Lib/re/_parser.py", pyFns := ["Tokenizer.match"]
    statement := "match(c) leaves the tokenizer alone and returns False unless the next token is c."
    source := "Lib/re/_parser.py:256-260", status := .proven
    prop := ``MatchLaw, thm := some ``matchLaw_proven },
  { id := "textlibs-re-getwhile", pyFile := "Lib/re/_parser.py", pyFns := ["Tokenizer.getwhile"]
    statement := "getwhile(n, set) reads at most n characters, all in set."
    source := "Lib/re/_parser.py:265-273", status := .proven
    prop := ``GetwhileBound, thm := some ``getwhileBound_proven },
  { id := "textlibs-re-getuntil", pyFile := "Lib/re/_parser.py", pyFns := ["Tokenizer.getuntil"]
    statement := "getuntil(term) on plain text returns what comes before the terminator and leaves the tokenizer after it."
    source := "Lib/re/_parser.py:274-289", status := .proven
    prop := ``GetuntilLaw, thm := some ``getuntilLaw_proven },
  { id := "textlibs-re-group-name", pyFile := "Lib/re/_parser.py", pyFns := ["Tokenizer.checkgroupname"]
    statement := "checkgroupname accepts exactly the identifiers."
    source := "docs: group names must be valid identifiers", status := .proven
    prop := ``GroupNameLaw, thm := some ``groupNameLaw_proven
    notes := "ASCII names: non-ASCII str.isidentifier is not modelled." },
  { id := "textlibs-re-width-ordered", pyFile := "Lib/re/_parser.py", pyFns := ["SubPattern.getwidth"]
    statement := "For every tree of the shape the parser produces, getwidth returns lo <= hi."
    source := "invariant: the lookbehind check at Lib/re/_compiler.py:159 compares them", status := .proven
    prop := ``WidthOrdered, thm := some ``widthOrdered_proven },
  { id := "textlibs-re-prefix-factor", pyFile := "Lib/re/_parser.py", pyFns := ["_parse_sub"]
    statement := "Moving a common prefix out of a branch keeps every alternative: each is still the prefix followed by what stays in the branch."
    source := "comment at Lib/re/_parser.py:472", status := .proven
    prop := ``PrefixFactor, thm := some ``prefixFactor_proven },
  { id := "textlibs-re-branch-set", pyFile := "Lib/re/_parser.py", pyFns := ["_parse_sub"]
    statement := "A branch of single characters and sets becomes one set that holds all of them."
    source := "comment at Lib/re/_parser.py:491", status := .proven
    prop := ``BranchSetLaw, thm := some ``branchSetLaw_proven },
  { id := "textlibs-re-flags", pyFile := "Lib/re/_parser.py", pyFns := ["_parse_flags"]
    statement := "An inline flag group never turns a flag both on and off or turns off a global flag, and the refused combinations raise the source's messages."
    source := "the messages at Lib/re/_parser.py:893-944", status := .proven
    prop := ``FlagLaws, thm := some ``flagLaws_proven },
  { id := "textlibs-re-template-plain", pyFile := "Lib/re/_parser.py", pyFns := ["parse_template"]
    statement := "A replacement with no backslash is that literal text, for every length and every pattern."
    source := "docs: re.sub", status := .proven
    prop := ``TemplatePlain, thm := some ``templatePlain_proven },
  { id := "textlibs-re-tell", pyFile := "Lib/re/_parser.py", pyFns := ["Tokenizer.tell", "Tokenizer.pos", "Tokenizer.__next"]
    statement := "After reading a token, tell() is the position of that token."
    source := "invariant: error positions point at the current token", status := .proven
    prop := ``TellAfterAdv, thm := some ``tellAfterAdv_proven },
  { id := "textlibs-re-fix-flags", pyFile := "Lib/re/_parser.py", pyFns := ["fix_flags"]
    statement := "A str pattern rejects LOCALE, and without ASCII it gets UNICODE."
    source := "docs: re.ASCII, re.LOCALE", status := .proven
    prop := ``FixFlagsStr, thm := some ``fixFlagsStr_proven },
  { id := "textlibs-re-uniq", pyFile := "Lib/re/_parser.py", pyFns := ["_uniq"]
    statement := "_uniq keeps exactly the same items."
    source := "invariant", status := .proven
    prop := ``UniqMembers, thm := some ``uniqMembers_proven },
  { id := "textlibs-re-message", pyFile := "Lib/re/_constants.py", pyFns := ["PatternError.__init__"]
    statement := "A pattern without a newline gets the plain position suffix, with no line or column."
    source := "Lib/re/_constants.py:41-50", status := .proven
    prop := ``MessagePlain, thm := some ``messagePlain_proven },
  { id := "textlibs-re-escape-twins", pyFile := "Lib/re/_parser.py", pyFns := ["_escape", "_class_escape"]
    statement := "_escape and _class_escape agree on every single-character ASCII escape, except those that mean something else outside a set."
    source := "the implementation disagreeing with itself", status := .proven
    prop := ``EscapeTwins, thm := some ``escapeTwins_proven }
]

end PyLean.TextLibs
