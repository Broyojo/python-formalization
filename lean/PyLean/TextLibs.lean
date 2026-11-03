import PyLean.Registry
import PyLean.TextLibs.Diff
import PyLean.TextLibs.StructFail
import PyLean.TextLibs.BinasciiEq3
import PyLean.TextLibs.CsvRoundTrip
import PyLean.TextLibs.ReParseProps
import PyLean.TextLibs.ReMisc
import PyLean.TextLibs.PathProps
import PyLean.TextLibs.ShlexProps
import PyLean.TextLibs.TextwrapProps
import PyLean.TextLibs.QuopriProps
import PyLean.TextLibs.HtmlProps
import PyLean.TextLibs.DifflibHunks
import PyLean.TextLibs.CsvSniffProps
import PyLean.TextLibs.EtreeProps
import PyLean.TextLibs.EtreePathProps
import PyLean.TextLibs.EtreeWriters
import PyLean.TextLibs.EtreeAttrib
import PyLean.TextLibs.EtreeRemove
import PyLean.TextLibs.EtreeCopy
import PyLean.TextLibs.ZoneinfoBefore
import PyLean.TextLibs.SimpleQueueGet
import PyLean.TextLibs.UrlQuery
import PyLean.TextLibs.UrlBrackets
import PyLean.TextLibs.UrlTwins
import PyLean.TextLibs.UrlLegacy
import PyLean.TextLibs.UrlSpecBytes
import PyLean.TextLibs.TomlErr
import PyLean.TextLibs.TomlStr
import PyLean.TextLibs.TomlKey
import PyLean.TextLibs.TomlNum
import PyLean.TextLibs.TomlDate
import PyLean.TextLibs.TomlTable
import PyLean.TextLibs.TomlLoad
import PyLean.TextLibs.TomlArr
import PyLean.TextLibs.TomlDoc
import PyLean.TextLibs.TomlMulti
import PyLean.TextLibs.TomlPending
import PyLean.TextLibs.EmailQuote
import PyLean.TextLibs.TomlScen
import PyLean.TextLibs.TomlLoads
import PyLean.TextLibs.TomlInline
import PyLean.TextLibs.EmailEw2
import PyLean.TextLibs.PlistRefute

/-!
Text and binary formats, CPython 3.15.2. `Modules/_struct.c` is modelled in
`TextLibs/StructModel.lean`, on the x86-64 LP64 little-endian build the difftest runs on,
with floats as exact bit patterns (`TextLibs/Bits.lean`). `lu_short`, `lu_longlong`,
`lp_longlong` and similar routines are replaced by native ones at start-up on this build,
so only the proofs reach them, not the difftest.

`Modules/binascii.c` and `Lib/base64.py` are in `TextLibs/BinasciiModel.lean` and
`TextLibs/BinasciiRest.lean`. `Modules/_csv.c` and
`Lib/csv.py` are in `TextLibs/CsvModel.lean`, over fallible and re-entrant objects; `Sniffer` is not
modelled.
`Lib/re/_parser.py` is in `TextLibs/ReParse.lean`, without `\\N{...}` and non-ASCII group names.
`Lib/urllib/parse.py` is in `TextLibs/UrlModel.lean`, with `unicodedata.normalize` and
`ipaddress.ip_address` as parameters.
`Lib/tomllib/_parser.py` and `Lib/tomllib/_re.py` are in `TextLibs/TomlModel.lean`, with
`parse_float`, `MAX_KEY_PARTS`, `sys.get_int_max_str_digits()`, `cached_tz`'s cache and the frames
left below the recursion limit as parameters.
The binary side of `Lib/plistlib.py` (reader, writer, `load`/`loads`/`dump`/`dumps` dispatch) is in
`TextLibs/PlistModel.lean` and `TextLibs/PlistWrite.lean`, with the frames left as a parameter,
`dict_type=dict`, and the XML parser and writer as parameters.
-/

namespace PyLean.TextLibs

open PyLean.Registry
open PyLean.TextLibs.Struct
open PyLean.TextLibs.Binascii
open PyLean.TextLibs.Csv
open PyLean.TextLibs.Re
open PyLean.TextLibs.Path
open PyLean.TextLibs.Textwrap
open PyLean.TextLibs.Shlex
open PyLean.TextLibs.Quopri
open PyLean.TextLibs.Html
open PyLean.TextLibs.Difflib
open PyLean.TextLibs.Url
open PyLean.TextLibs.Toml

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
    source := "comments at Modules/_struct.c:1528-1546", status := .proven
    prop := ``EndianTableSwap, thm := some ``endianTableSwap_proven },
  { id := "textlibs-struct-align", pyFile := "Modules/_struct.c", pyFns := ["align"]
    statement := "For every size <= PY_SSIZE_T_MAX and non-zero alignment, align returns the next multiple of the alignment, or fails only when that multiple would pass PY_SSIZE_T_MAX."
    source := "comment at Modules/_struct.c:1616", status := .proven
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
    source := "invariant: the loop would not advance; Modules/_struct.c:2293", status := .proven
    prop := ``IterUnpackZeroSize, thm := some ``iterUnpackZeroSize_proven },
  { id := "textlibs-struct-pack-count", pyFile := "Modules/_struct.c", pyFns := ["Struct_pack_impl"]
    statement := "pack raises struct.error with the source's message for every wrong argument count, before converting any argument."
    source := "docs: the values must match the format exactly", status := .proven
    prop := ``PackWrongCount, thm := some ``packWrongCount_proven },
  { id := "textlibs-struct-le-complex-float-overflow", pyFile := "Modules/_struct.c"
    pyFns := ["np_float_complex", "bp_float_complex", "Struct_pack_impl", "pack_impl"]
    statement := "<F and >F accept the same values: byte order changes the bytes, not whether a value can be packed."
    source := "invariant: f, <f and >f all raise OverflowError", status := .refuted
    prop := ``StdComplexOrderAgree, thm := some ``stdComplexOrderAgree_refuted
    bug := some "textlibs-struct-le-complex-float-overflow"
    notes := "Duplicate of python/cpython#156865, fixed on main by #156868; 3.15.2 still has it." },
  { id := "textlibs-struct-bytes-format-nonascii-error", pyFile := "Modules/_struct.c"
    pyFns := ["cache_struct_converter", "set_format", "pack_impl"]
    statement := "pack(fmt, ...) and Struct(fmt).pack(...) give the same result for every hashable format object."
    source := "docs: module functions are equivalent to the Struct methods", status := .proven
    prop := ``ModuleMatchesStruct, thm := some ``moduleMatchesStruct_proven
    notes := "A str key is encoded and bytes decoded with surrogateescape in both routes, so they agree." },
  { id := "textlibs-struct-void-p-index-overflow", pyFile := "Modules/_struct.c", pyFns := ["np_void_p", "s_pack_internal"]
    statement := "An __index__ object packs with P exactly like the equal int: same bytes or same error."
    source := "invariant: every other integer code", status := .refuted
    prop := ``PIndexLikeInt, thm := some ``pIndexLikeInt_refuted
    bug := some "textlibs-struct-void-p-index-overflow"
    notes := "Reproduces on main too. Trivial on its own." },
  { id := "textlibs-struct-pack-into-0p-outside-field", pyFile := "Modules/_struct.c"
    pyFns := []
    statement := "pack_into changes no byte outside the calcsize(format) bytes at offset."
    source := "invariant", status := .open
    prop := ``PackIntoStaysInside
    notes := "`packP` writes the count of a p field only when the field has room. Open: the proof needs that every pack routine returns exactly e.size bytes, which is stated for the integers only." },
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
    source := "invariant: pack reads s_len arguments by walking the codes (Modules/_struct.c:2342-2347)", status := .proven
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
    notes := "lu_float, lp_float, lu_double and lp_double are replaced at start-up on this build, so only proofs reach them. As a statement about formats, <f quiets a signalling NaN and >f does not; see textlibs-struct-native-float-snan." },
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
    statement := "unpack('f', b) and unpack('>f', reversed b) agree on every 4-byte buffer."
    source := "invariant: byte order is the only difference", status := .refuted
    prop := ``NativeFloatMatchesBig, thm := some ``nativeFloatMatchesBig_refuted
    bug := some "textlibs-struct-native-float-snan" },
  { id := "textlibs-struct-little-is-native", pyFile := "Modules/_struct.c", pyFns := ["init_endian_tables"]
    statement := "unpack('f', b) and unpack('<f', b) agree on every buffer: the native routine is swapped into the little-endian table."
    source := "invariant: native and little-endian differ only in alignment on this build", status := .proven
    prop := ``NativeFloatMatchesStd, thm := some ``nativeFloatMatchesStd_proven },
  { id := "textlibs-struct-z-codes", pyFile := "Modules/_struct.c", pyFns := ["format_equal", "getentry", "align"]
    statement := "Zf and Zd have the entries of F and D in each table, and a Z with anything else is a bad character."
    source := "docs: Zf and Zd are the complex codes", status := .proven
    prop := ``ZCodes, thm := some ``zCodes_proven },
  { id := "textlibs-struct-life", pyFile := "Modules/_struct.c", pyFns := ["s_new", "s_init", "Struct_impl", "set_format", "same_format", "Struct___init___impl"]
    statement := "Struct(f) is set_format once; __init__ with an equal format does nothing; with another it warns and changes the format; a subclass with __init__ gets a warning for a bad format in __new__."
    source := "Modules/_struct.c:1868-2002", status := .proven
    prop := ``LifeLaw, thm := some ``lifeLaw_proven },
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
  { id := "textlibs-struct-accessors", pyFile := "Modules/_struct.c", pyFns := ["Struct___sizeof___impl", "calcsize_impl"]
    statement := "For every accepted str format, Struct(fmt).format == fmt, .size and calcsize(fmt) are the size prepare_s computed, and __sizeof__ counts one formatcode per code plus the sentinel."
    source := "docs: Struct.format, Struct.size", status := .proven
    prop := ``Accessors, thm := some ``accessors_proven },
  { id := "textlibs-struct-uninitialized", pyFile := "Modules/_struct.c", pyFns := ["s_new"]
    statement := "Before __init__, .size is -1 and every method raises RuntimeError."
    source := "invariant: ENSURE_STRUCT_IS_READY, Modules/_struct.c:2083-2090", status := .proven
    prop := ``UninitStruct, thm := some ``uninitStruct_proven },
  { id := "textlibs-struct-get-pylong", pyFile := "Modules/_struct.c", pyFns := ["get_pylong"]
    statement := "get_pylong gives the result of __index__, including what it raises, and struct.error for an object without it."
    source := "Modules/_struct.c:112-134", status := .proven
    prop := ``GetPylongLaw, thm := some ``getPylongLaw_proven },
  { id := "textlibs-struct-index-raises", pyFile := "Modules/_struct.c"
    pyFns := ["get_long", "get_ulong", "get_longlong", "get_ulonglong", "get_ssize_t", "get_size_t"]
    statement := "An exception from __index__ other than OverflowError comes out of every integer format unchanged."
    source := "Modules/_struct.c:144-151", status := .proven
    prop := ``IndexRaises, thm := some ``indexRaises_proven },
  { id := "textlibs-struct-index-overflow", pyFile := "Modules/_struct.c", pyFns := ["np_int"]
    statement := "An OverflowError from __index__ becomes the format's range error."
    source := "Modules/_struct.c:576-579", status := .proven
    prop := ``IndexOverflow, thm := some ``indexOverflow_proven },
  { id := "textlibs-struct-bool-raises", pyFile := "Modules/_struct.c", pyFns := ["np_bool", "bp_bool"]
    statement := "A raising __bool__ raises out of ?, in both format tables."
    source := "Modules/_struct.c:745-747", status := .proven
    prop := ``BoolRaises, thm := some ``boolRaises_proven },
  { id := "textlibs-struct-float-replaced", pyFile := "Modules/_struct.c"
    pyFns := ["pack_halffloat", "np_float", "np_double", "bp_float", "bp_double", "lp_float", "lp_double"]
    statement := "A __float__ that raises does not get through: every failure of PyFloat_AsDouble becomes struct.error."
    source := "Modules/_struct.c:281-286", status := .proven
    prop := ``FloatFailureReplaced, thm := some ``floatFailureReplaced_proven },
  { id := "textlibs-struct-float-order", pyFile := "Modules/_struct.c", pyFns := ["pack_halffloat", "np_float", "np_double"]
    statement := "__float__ wins over __index__, and without __float__ the value of __index__ is used."
    source := "PyFloat_AsDouble, Objects/floatobject.c", status := .proven
    prop := ``FloatOrder, thm := some ``floatOrder_proven },
  { id := "textlibs-struct-complex-order", pyFile := "Modules/_struct.c"
    pyFns := ["np_float_complex", "np_double_complex", "bp_float_complex", "bp_double_complex", "lp_float_complex", "lp_double_complex"]
    statement := "__complex__ wins and its failure becomes struct.error; without it the object is real, with imaginary part zero."
    source := "PyComplex_AsCComplex, Objects/complexobject.c", status := .proven
    prop := ``ComplexOrder, thm := some ``complexOrder_proven },
  { id := "textlibs-struct-buffers", pyFile := "Modules/_struct.c", pyFns := ["Struct_pack_into_impl", "Struct_unpack_impl"]
    statement := "y* lets a failing __buffer__ through; the rwbuffer Py_buffer of pack_into replaces it with TypeError and refuses bytes."
    source := "Modules/clinic/_struct.c.h, the Py_buffer conversions", status := .proven
    prop := ``BufferLaws, thm := some ``bufferLaws_proven },
  { id := "textlibs-struct-pack-into-order", pyFile := "Modules/_struct.c", pyFns := ["Struct_pack_into_impl"]
    statement := "pack_into converts the buffer, then the offset, and only then compares the item count, with the s_len a __init__ run by __index__ left."
    source := "Modules/clinic/_struct.c.h and Struct_pack_into_impl", status := .proven
    prop := ``PackIntoOrder, thm := some ``packIntoOrder_proven },
  { id := "textlibs-struct-offset-laws", pyFile := "Modules/_struct.c", pyFns := ["Struct_pack_into_impl", "Struct_unpack_from_impl"]
    statement := "Too large an offset is OverflowError for pack_into and for unpack_from, and an exception from __index__ comes out of both."
    source := "the Py_ssize_t conversions of Modules/clinic/_struct.c.h", status := .proven
    prop := ``OffsetLaws, thm := some ``offsetLaws_proven },
  { id := "textlibs-struct-module-order", pyFile := "Modules/_struct.c"
    pyFns := ["unpack_impl", "unpack_from_impl", "iter_unpack_impl", "pack_impl", "pack_into_impl"]
    statement := "The module functions report a bad format ahead of a bad buffer and need a format at all; otherwise they are the Struct methods."
    source := "Modules/_struct.c:2709-2809", status := .proven
    prop := ``ModuleOrder, thm := some ``moduleOrder_proven },
  { id := "textlibs-struct-unpack-buffer", pyFile := "Modules/_struct.c", pyFns := ["Struct_unpack_impl", "Struct_unpack_from_impl"]
    statement := "unpack and unpack_from raise what the buffer conversion raises, before looking at the length."
    source := "the clinic conversions of Struct.unpack", status := .proven
    prop := ``UnpackBufferFirst, thm := some ``unpackBufferFirst_proven },
  { id := "textlibs-struct-iter-order", pyFile := "Modules/_struct.c", pyFns := ["Struct_iter_unpack_impl"]
    statement := "iter_unpack refuses a zero-sized format first, then a failing buffer, then a length that is not a multiple."
    source := "Modules/_struct.c:2293-2314", status := .proven
    prop := ``IterUnpackOrder, thm := some ``iterUnpackOrder_proven },
  { id := "textlibs-struct-iter-drive", pyFile := "Modules/_struct.c", pyFns := ["unpackiter_iternext"]
    statement := "With the Struct left alone, the iterator object yields the tuples of the list model, and its read stays in the buffer."
    source := "docs: iter_unpack", status := .proven
    prop := ``IterDriveAgrees, thm := some ``iterDriveAgrees_proven },
  { id := "textlibs-struct-iter-len", pyFile := "Modules/_struct.c", pyFns := ["unpackiter_len"]
    statement := "The iterator's __length_hint__ is the remaining length over s_size."
    source := "Modules/_struct.c:2220", status := .proven
    prop := ``IterLenAgrees, thm := some ``iterLenAgrees_proven },
  { id := "textlibs-struct-reinit-pack", pyFile := "Modules/_struct.c", pyFns := ["Struct_pack_impl", "s_pack_internal"]
    statement := "No conversion can free the format codes pack is walking."
    source := "undisputed: Python code must not reach freed memory", status := .refuted
    prop := ``PackNoUnsafe, thm := some ``packNoUnsafe_refuted
    bug := some "textlibs-struct-reinit-memory-safety"
    notes := "__index__ calls s.__init__, which frees s_codes during s_pack_internal." },
  { id := "textlibs-struct-reinit-pack-into", pyFile := "Modules/_struct.c", pyFns := ["Struct_pack_into_impl", "s_pack_internal"]
    statement := "pack_into reads only the arguments it was given."
    source := "undisputed: Python code must not reach out-of-bounds memory", status := .refuted
    prop := ``PackIntoNoUnsafe, thm := some ``packIntoNoUnsafe_refuted
    bug := some "textlibs-struct-reinit-memory-safety"
    notes := "An __index__ of a packed value reinitializes the Struct, which frees s_codes during s_pack_internal. The offset can no longer do it: textlibs-struct-pack-into-order has the count checked after the offset is converted." },
  { id := "textlibs-struct-reinit-iter", pyFile := "Modules/_struct.c", pyFns := ["unpackiter_iternext"]
    statement := "iter_unpack reads only the buffer it was given."
    source := "undisputed: Python code must not reach out-of-bounds memory", status := .refuted
    prop := ``IterNoOverRead, thm := some ``iterNoOverRead_refuted
    bug := some "textlibs-struct-reinit-memory-safety"
    notes := "A larger format installed between next() calls: the bound is only an assert." },
  { id := "textlibs-struct-reinit-iter-len", pyFile := "Modules/_struct.c", pyFns := ["unpackiter_len"]
    statement := "__length_hint__ does not divide by zero."
    source := "undisputed: Python code must not crash the interpreter", status := .refuted
    prop := ``IterLenNoCrash, thm := some ``iterLenNoCrash_refuted
    bug := some "textlibs-struct-reinit-memory-safety"
    notes := "A zero-sized format installed after the iterator was made: SIGFPE." },
  { id := "textlibs-struct-range-error", pyFile := "Modules/_struct.c", pyFns := ["_range_error"]
    statement := "_range_error's message states the exact range of the entry, for every integer entry that uses it."
    source := "invariant", status := .proven
    prop := ``RangeErrorBounds, thm := some ``rangeErrorBounds_proven },
  { id := "textlibs-struct-repr", pyFile := "Modules/_struct.c", pyFns := ["s_repr"]
    statement := "repr(Struct(fmt)) of a format without control characters is Struct('fmt')."
    source := "invariant: repr round-trips the format", status := .proven
    prop := ``ReprPlain, thm := some ``reprPlain_proven },
  { id := "textlibs-binascii-base64-round-trip", pyFile := "Modules/binascii.c"
    pyFns := ["binascii_a2b_base64_impl", "binascii_b2a_base64_impl", "base64_encode_trio", "base64_encode_fast", "base64_decode_quad", "base64_decode_fast"]
    statement := "a2b_base64(b2a_base64(d, newline=False), strict_mode=s) == d for every bytes value d and both strict modes."
    source := "RFC 4648 and the module's purpose: encoding then decoding returns the data", status := .proven
    prop := ``Base64RoundTripC, thm := some ``base64RoundTripC_proven
    notes := "Both fast paths are in the model: BinasciiEq.lean has the C loops equal to the bit-at-a-time specification at the default options, and the theorem goes through that." },
  { id := "textlibs-binascii-base64-lenient-filter", pyFile := "Modules/binascii.c", pyFns := ["binascii_a2b_base64_impl"]
    statement := "With strict_mode=False, removing every byte that is neither in the alphabet nor '=' changes nothing, including which error is raised and its message."
    source := "base64.b64decode docstring: non-alphabet characters are discarded prior to the padding check", status := .proven
    prop := ``LenientIgnoresC, thm := some ``lenientIgnoresC_proven },
  { id := "textlibs-binascii-base64-strict-implies-lenient", pyFile := "Modules/binascii.c", pyFns := ["binascii_a2b_base64_impl"]
    statement := "Whatever strict_mode=True accepts, strict_mode=False accepts with the same result."
    source := "docs: strict mode only disallows more input", status := .proven
    prop := ``StrictImpliesLenientC, thm := some ``strictImpliesLenientC_proven },
  { id := "textlibs-binascii-base64-length", pyFile := "Modules/binascii.c", pyFns := ["binascii_b2a_base64_impl"]
    statement := "len(b2a_base64(d, newline=False)) == 4 * ceil(len(d) / 3) for every bytes value d."
    source := "RFC 4648 section 4", status := .proven
    prop := ``B2aLengthC, thm := some ``b2aLengthC_proven },
  { id := "textlibs-binascii-hex-round-trip", pyFile := "Modules/binascii.c"
    pyFns := ["binascii_b2a_hex_impl", "binascii_hexlify_impl", "binascii_a2b_hex_impl", "binascii_unhexlify_impl"]
    statement := "unhexlify(hexlify(d), ignorechars=g) == d for every bytes value d and every g."
    source := "docs: a2b_hex is the inverse of b2a_hex", status := .proven
    prop := ``HexRoundTripC, thm := some ``hexRoundTripC_proven
    notes := "The separator arguments are textlibs-binascii-hex-sep." },
  { id := "textlibs-base64-round-trip", pyFile := "Lib/base64.py"
    pyFns := ["b64encode", "b64decode", "_bytes_from_decode_data"]
    statement := "b64decode(b64encode(d), validate=v) == d for every bytes value d and both modes."
    source := "docs: b64decode decodes what b64encode produces", status := .proven
    prop := ``B64ModuleRoundTripC, thm := some ``b64ModuleRoundTripC_proven
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
    source := "RFC 2045 section 6.7 rule 5; MAXLINESIZE at Modules/binascii.c:2368", status := .refuted
    prop := ``QpLineLimit, thm := some ``qpLineLimit_refuted
    bug := some "textlibs-binascii-qp-line-length"
    notes := "74 'a', a space and a newline give a 77-character line. The first pass counts the same bytes, so the buffer is big enough." },
  { id := "textlibs-base64-standard-round-trip", pyFile := "Lib/base64.py"
    pyFns := ["standard_b64encode", "standard_b64decode"]
    statement := "standard_b64decode(standard_b64encode(d)) == d for every bytes value d."
    source := "docstrings", status := .proven
    prop := ``StandardRoundTripC, thm := some ``standardRoundTripC_proven },
  { id := "textlibs-base64-input-check", pyFile := "Lib/base64.py", pyFns := ["_input_type_check"]
    statement := "_input_type_check accepts exactly one-dimensional views of single-byte formats."
    source := "the checks' messages", status := .proven
    prop := ``InputTypeCheck, thm := some ``inputTypeCheck_proven },
  { id := "textlibs-base64-main-flags", pyFile := "Lib/base64.py", pyFns := []
    statement := "main runs the function of the last -e, -d or -u flag, unless -h came first."
    source := "the usage text", status := .proven
    prop := ``MainLastFlagWins, thm := some ``mainLastFlagWins_proven
    notes := "Only the flag loop. This does not cover the row for main, whose getopt errors and file handling are not modelled." },
  { id := "textlibs-binascii-hex-sep", pyFile := "Modules/binascii.c", pyFns := ["binascii_b2a_hex_impl", "binascii_hexlify_impl"]
    statement := "hexlify with a separator: taking the separators out gives plain hexadecimal, (n-1)/|group| are inserted, and the sign of group picks the end the groups count from."
    source := "docs: hexlify, sep and bytes_per_sep", status := .proven
    prop := ``HexSepLaw, thm := some ``hexSepLaw_proven },
  { id := "textlibs-binascii-hex-no-sep", pyFile := "Modules/binascii.c", pyFns := ["binascii_b2a_hex_impl", "binascii_hexlify_impl"]
    statement := "No separator goes in without sep, for bytes_per_sep 0, or for a group at least as long as the data."
    source := "Python/pystrhex.c:150-168", status := .proven
    prop := ``HexNoSep, thm := some ``hexNoSep_proven },
  { id := "textlibs-binascii-hex-sep-checks", pyFile := "Modules/binascii.c", pyFns := ["binascii_b2a_hex_impl", "binascii_hexlify_impl"]
    statement := "What sep may be, in check order: length first, which may raise, then type; a non-ASCII bytes or Latin-1 str sep passes when the result is bytes."
    source := "Python/pystrhex.c:123-149", status := .proven
    prop := ``HexSepChecks, thm := some ``hexSepChecks_proven },
  { id := "textlibs-binascii-uu-round-trip", pyFile := "Modules/binascii.c", pyFns := ["binascii_a2b_uu_impl", "binascii_b2a_uu_impl"]
    statement := "a2b_uu(b2a_uu(d, backtick=b)) == d for all the data b2a_uu accepts."
    source := "docs: a2b_uu, b2a_uu", status := .proven
    prop := ``UuRoundTrip, thm := some ``uuRoundTrip_proven },
  { id := "textlibs-binascii-uu-limit", pyFile := "Modules/binascii.c", pyFns := ["binascii_b2a_uu_impl"]
    statement := "b2a_uu refuses more than 45 bytes."
    source := "docs: b2a_uu", status := .proven
    prop := ``UuLimit, thm := some ``uuLimit_proven },
  { id := "textlibs-binascii-buffers", pyFile := "Modules/binascii.c", pyFns := ["ascii_buffer_converter"]
    statement := "ascii_buffer_converter replaces a failing buffer with TypeError, where y* lets it through."
    source := "Modules/binascii.c:448-453", status := .proven
    prop := ``BufferConversions, thm := some ``bufferConversions_proven },
  { id := "textlibs-binascii-flag-order", pyFile := "Modules/binascii.c"
    pyFns := ["binascii_b2a_base64_impl", "binascii_a2b_base64_impl", "binascii_b2a_uu_impl"]
    statement := "A raising __bool__ on a keyword passes through, after the data has been converted."
    source := "the clinic conversions of binascii", status := .proven
    prop := ``FlagOrder, thm := some ``flagOrder_proven },
  { id := "textlibs-base64-decode-data", pyFile := "Lib/base64.py", pyFns := ["_bytes_from_decode_data"]
    statement := "_bytes_from_decode_data replaces only a TypeError from memoryview."
    source := "Lib/base64.py:41-44", status := .proven
    prop := ``DecodeDataFails, thm := some ``decodeDataFails_proven },
  { id := "textlibs-base64-b16-round-trip", pyFile := "Lib/base64.py", pyFns := ["b16encode", "b16decode"]
    statement := "b16decode(b16encode(d)) == d, with only upper case digits, so casefold=False accepts it."
    source := "docs: b16encode, b16decode", status := .proven
    prop := ``B16RoundTripC, thm := some ``b16RoundTripC_proven },
  { id := "textlibs-base64-urlsafe-round-trip", pyFile := "Lib/base64.py", pyFns := ["urlsafe_b64encode", "urlsafe_b64decode"]
    statement := "urlsafe_b64decode(urlsafe_b64encode(d), padded=q) == d, for both values of q: the decoder defaults to padded=False and the encoder pads."
    source := "docs: urlsafe_b64encode", status := .proven
    prop := ``UrlsafeRoundTripC, thm := some ``urlsafeRoundTripC_proven },
  { id := "textlibs-base64-b85-round-trip", pyFile := "Lib/base64.py", pyFns := ["b85encode", "b85decode"]
    statement := "b85decode(b85encode(d)) == d, including a cut last group."
    source := "docs: b85encode, b85decode", status := .proven
    prop := ``B85RoundTripC, thm := some ``b85RoundTripC_proven },
  { id := "textlibs-base64-z85-round-trip", pyFile := "Lib/base64.py", pyFns := ["z85encode", "z85decode"]
    statement := "z85decode(z85encode(d)) == d."
    source := "docs: z85encode, z85decode", status := .proven
    prop := ``Z85RoundTripC, thm := some ``z85RoundTripC_proven },
  { id := "textlibs-base64-a85-round-trip", pyFile := "Lib/base64.py", pyFns := ["a85encode", "a85decode"]
    statement := "a85decode(a85encode(d, foldspaces=f), foldspaces=f) == d, through the z and y folds and a cut last group."
    source := "docs: a85encode, a85decode", status := .proven
    prop := ``A85RoundTripC, thm := some ``a85RoundTripC_proven },
  { id := "textlibs-binascii-base32-round-trip", pyFile := "Modules/binascii.c"
    pyFns := ["binascii_a2b_base32_impl", "binascii_b2a_base32_impl", "base32_encode_quint", "base32_encode_fast",
      "base32_decode_octa", "base32_decode_fast", "get_reverse_table"]
    statement := "a2b_base32(b2a_base32(d, alphabet=a), alphabet=a) == d for all bytes d and every alphabet of 32 distinct bytes without '=', through both fast paths and all four padding lengths."
    source := "the implementation disagreeing with itself: round trip", status := .proven
    prop := ``B32AlphabetRoundTrip, thm := some ``b32AlphabetRoundTrip_proven },
  { id := "textlibs-binascii-base85-round-trip", pyFile := "Modules/binascii.c"
    pyFns := ["binascii_a2b_base85_impl", "binascii_b2a_base85_impl", "get_reverse_table"]
    statement := "a2b_base85(b2a_base85(d, alphabet=a), alphabet=a) == d for all bytes d and every alphabet of 85 distinct bytes, including a cut last group."
    source := "the implementation disagreeing with itself: round trip", status := .proven
    prop := ``B85AlphabetRoundTrip, thm := some ``b85AlphabetRoundTrip_proven },
  { id := "textlibs-binascii-ascii85-round-trip", pyFile := "Modules/binascii.c"
    pyFns := ["binascii_a2b_ascii85_impl", "binascii_b2a_ascii85_impl"]
    statement := "a2b_ascii85(b2a_ascii85(d, foldspaces=f), foldspaces=f, ignorechars=g) == d, through the z and y folds and a cut last group."
    source := "the implementation disagreeing with itself: round trip", status := .proven
    prop := ``A85RoundTripC, thm := some ``a85RoundTripC_proven },
  { id := "textlibs-binascii-reverse-tables", pyFile := "Modules/binascii.c", pyFns := ["_Py_ALIGNED_DEF"]
    statement := "The four static reverse tables, copied from the source, are entry by entry what get_reverse_table builds from their alphabets."
    source := "Modules/binascii.c:81-99, 192-230, 251-269", status := .proven
    prop := ``ReverseTables, thm := some ``reverseTables_proven },
  { id := "textlibs-binascii-hex-ignorechars", pyFile := "Modules/binascii.c"
    pyFns := ["binascii_a2b_hex_impl", "binascii_unhexlify_impl", "ignorechar"]
    statement := "unhexlify(s, ignorechars=g) is unhexlify of s without the non-digit bytes of g, failures and their messages included; a digit named in g stays a digit."
    source := "the docs of ignorechars and Modules/binascii.c:2310-2343", status := .proven
    prop := ``HexIgnoreLaw, thm := some ``hexIgnoreLaw_proven },
  { id := "textlibs-binascii-wraplines", pyFile := "Modules/binascii.c", pyFns := ["wraplines"]
    statement := "wraplines joins lines of exactly width characters, and one last line of at most width, with single newlines, and adds nothing else."
    source := "the comment at Modules/binascii.c:457-458", status := .proven
    prop := ``WraplinesLaw, thm := some ``wraplinesLaw_proven },
  { id := "textlibs-base64-a85-wrap-round-trip", pyFile := "Lib/base64.py", pyFns := []
    statement := "The Ascii85 round trip holds with wrapcol and adobe."
    source := "docs: a85encode, a85decode", status := .open
    prop := ``A85WrapRoundTripC
    notes := "Needs the loop shown to skip the newlines wraplines inserts, and the framing shown to survive them." },
  { id := "textlibs-base64-b32-round-trip", pyFile := "Lib/base64.py"
    pyFns := ["b32encode", "b32decode", "b32hexencode", "b32hexdecode"]
    statement := "b32decode(b32encode(d)) == d and b32hexdecode(b32hexencode(d)) == d, for every length, so through all four padding lengths."
    source := "docs: b32encode, b32decode", status := .proven
    prop := ``B32RoundTripC, thm := some ``b32RoundTripC_proven },
  { id := "textlibs-base64-b32-option-law", pyFile := "Lib/base64.py", pyFns := ["b32decode"]
    statement := "casefold and map01 only rewrite the input before decoding, map01 first, and a map01 that is not one byte is refused by bytes.maketrans."
    source := "docs: b32decode", status := .proven
    prop := ``B32OptionLawC, thm := some ``b32OptionLawC_proven },
  { id := "textlibs-base64-encodebytes-round-trip", pyFile := "Lib/base64.py", pyFns := ["encodebytes", "decodebytes"]
    statement := "decodebytes(encodebytes(d)) == d."
    source := "docs: decodebytes", status := .proven
    prop := ``DecodebytesRoundTripC, thm := some ``decodebytesRoundTripC_proven },
  { id := "textlibs-base64-encodebytes-line-length", pyFile := "Lib/base64.py", pyFns := ["encodebytes", "wraplines"]
    statement := "Past 57 bytes, encodebytes starts with exactly 76 characters and a newline, the encoding of the first 57 bytes."
    source := "docs: encodebytes (a newline after every 76 bytes of output)", status := .proven
    prop := ``EncodebytesLineLengthC, thm := some ``encodebytesLineLengthC_proven },
  { id := "textlibs-base64-encode-file-law", pyFile := "Lib/base64.py", pyFns := ["encode"]
    statement := "encode over a file with short reads and scripted failures writes a prefix of encodebytes(data), all of it unless the failure is one the file raised."
    source := "docs: encode", status := .proven
    prop := ``EncodeFileLaw, thm := some ``encodeFileLaw_proven
    notes := "Hypothesis: read returns nothing only at end of file; textlibs-base64-encode-empty-read has the other case." },
  { id := "textlibs-base64-encode-file-agrees", pyFile := "Lib/base64.py", pyFns := ["encode"]
    statement := "With no failing call, encode writes exactly encodebytes(data), however short the reads."
    source := "twin: encode and encodebytes", status := .proven
    prop := ``EncodeFileAgreesC, thm := some ``encodeFileAgreesC_proven },
  { id := "textlibs-base64-encode-empty-read", pyFile := "Lib/base64.py", pyFns := ["encode"]
    statement := "A read returning nothing before end of file ends encode with no error and nothing written."
    source := "Lib/base64.py:417 reads until an empty result", status := .proven
    prop := ``EncodeEmptyReadStops, thm := some ``encodeEmptyReadStops_proven },
  { id := "textlibs-base64-decode-file-round-trip", pyFile := "Lib/base64.py", pyFns := ["decode"]
    statement := "decode over the lines readline finds in encodebytes(d) writes d."
    source := "docs: decode", status := .proven
    prop := ``DecodeFileRoundTripC, thm := some ``decodeFileRoundTripC_proven },
  { id := "textlibs-base64-decode-file-stops", pyFile := "Lib/base64.py", pyFns := ["decode"]
    statement := "A failing readline or a line that does not decode ends decode at once, with nothing more written."
    source := "invariant: failures pass through", status := .proven
    prop := ``DecodeFileStops, thm := some ``decodeFileStops_proven },
  { id := "textlibs-base64-decode-agrees-decodebytes", pyFile := "Lib/base64.py", pyFns := ["decode"]
    statement := "decode accepts every input decodebytes accepts."
    source := "twin: decode and decodebytes", status := .refuted
    prop := ``DecodeAgreesDecodebytes, thm := some ``decodeAgreesDecodebytes_refuted
    bug := some "textlibs-base64-decode-per-line"
    notes := "b'YW\\nJj\\n': a group split across two lines." },
  { id := "textlibs-re-possessive-is-atomic", pyFile := "Modules/_sre/sre_lib.h", pyFns := []
    statement := "x{m,n}+ is equivalent to (?>x{m,n})."
    source := "docs: re, x{m,n}+", status := .refuted
    prop := ``PossessiveIsAtomic, thm := some ``possessiveIsAtomic_refuted
    bug := some "textlibs-re-possessive-min-count-not-atomic"
    notes := "(?:a+){2}+ on 'aa'. No function credited: sre_lib.h is one function row family, and this runs part of it." },
  { id := "textlibs-re-possessive-star-is-atomic", pyFile := "Modules/_sre/sre_lib.h", pyFns := []
    statement := "x*+, x++ and x?+ are equivalent to (?>x*), (?>x+) and (?>x?)."
    source := "docs: re, x*+", status := .open
    prop := ``PossessiveStarIsAtomic
    notes := "The two forms run different engine code. Needs textlibs-re-sem-agrees-no-self-test, or a direct simulation of possMore against MAX_UNTIL under an atomic group." },
  { id := "textlibs-re-sem-agrees-documented", pyFile := "Modules/_sre/sre_lib.h", pyFns := []
    statement := "re.match and re.fullmatch give what the declarative backtracking semantics gives, with possessive repeats as documented."
    source := "the module's documented backtracking behaviour", status := .refuted
    prop := ``SemAgreesDocumented, thm := some ``semAgreesDocumented_refuted
    bug := some "textlibs-re-possessive-min-count-not-atomic"
    notes := "Same counterexample as textlibs-re-possessive-is-atomic, through the semantics." },
  { id := "textlibs-re-sem-agrees-per-iteration", pyFile := "Modules/_sre/sre_lib.h", pyFns := []
    statement := "The same, with each of the first m iterations of a possessive repeat atomic, as re runs them."
    source := "the module's documented backtracking behaviour", status := .refuted
    prop := ``SemAgreesPerIteration, thm := some ``semAgreesPerIteration_refuted
    bug := some "textlibs-re-conditional-stale-end-mark"
    notes := "(()(?:(?(1)b))??) on 'b' with fullmatch." },
  { id := "textlibs-re-sem-agrees-no-self-test", pyFile := "Modules/_sre/sre_lib.h", pyFns := []
    statement := "With no conditional testing an open group, re gives what the semantics gives: the same end, group spans and lastindex."
    source := "the module's documented backtracking behaviour", status := .open
    prop := ``SemAgreesNoSelfTest
    notes := "Difftest 150000/150000 (re.sem, seeds 71-73). Needs a simulation of the compiled code against semSeq, with an invariant relating SSt to SemSt that survives LASTMARK_RESTORE and MARK_POP." },
  { id := "textlibs-re-endpos-before-pos", pyFile := "Modules/_sre/sre.c", pyFns := []
    statement := "Pattern.match finds no match when endpos is less than pos."
    source := "docs: Pattern.search, endpos", status := .refuted
    prop := ``EndposBeforePos, thm := some ``endposBeforePos_refuted
    bug := some "textlibs-re-match-endpos-before-pos"
    notes := "Duplicate of #160316, fixed upstream on 2026-10-31." },
  { id := "textlibs-re-endpos-before-pos-search", pyFile := "Modules/_sre/sre_lib.h", pyFns := ["SRE(search)"]
    statement := "Pattern.search finds no match when endpos is less than pos, for every compiled pattern."
    source := "docs: Pattern.search, endpos", status := .proven
    prop := ``EndposBeforePosSearch, thm := some ``endposBeforePosSearch_proven },
  { id := "textlibs-re-backref-matches-literal", pyFile := "Modules/_sre/sre_lib.h", pyFns := []
    statement := "Under IGNORECASE, (x)\\1 matches wherever x followed by x as literals matches."
    source := "twin: backreference and literal", status := .refuted
    prop := ``BackrefMatchesLiteral, thm := some ``backrefMatchesLiteral_refuted
    bug := some "textlibs-re-backref-extra-cases"
    notes := "Duplicate of #156513 (open)." },
  { id := "textlibs-re-bitmap-law", pyFile := "Lib/re/_compiler.py", pyFns := ["_mk_bitmap"]
    statement := "Bit i of the words _mk_bitmap makes, read as SRE(charset) reads CHARSET, is bit i of the charmap."
    source := "the engine reads back what the compiler packs", status := .proven
    prop := ``BitmapLaw, thm := some ``bitmapLaw_proven },
  { id := "textlibs-re-bytes-to-codes-law", pyFile := "Lib/re/_compiler.py", pyFns := ["_bytes_to_codes"]
    statement := "Byte i of the words _bytes_to_codes makes, read as SRE(charset) reads the block map of BIGCHARSET, is byte i."
    source := "the engine reads back what the compiler packs", status := .proven
    prop := ``BytesToCodesLaw, thm := some ``bytesToCodesLaw_proven },
  { id := "textlibs-re-overlap-table-law", pyFile := "Lib/re/_compiler.py", pyFns := ["_generate_overlap_table"]
    statement := "Entry i of the overlap table is the length of the longest proper border of prefix[:i+1], for every prefix."
    source := "the KMP failure function the search relies on", status := .proven
    prop := ``OverlapTableLaw, thm := some ``overlapTableLaw_proven },
  { id := "textlibs-re-simple-width", pyFile := "Lib/re/_compiler.py", pyFns := ["_simple"]
    statement := "A pattern _simple accepts has width exactly 1."
    source := "REPEAT_ONE steps back one character at a time", status := .proven
    prop := ``SimpleWidth, thm := some ``simpleWidth_proven },
  { id := "textlibs-re-search-prefix-law", pyFile := "Modules/_sre/sre_lib.h", pyFns := []
    statement := "The KMP scan of SRE(search) finds what trying each start finds: the same match in the same state, or nothing, for every prefix of two or more characters and every text."
    source := "an optimization preserves the search it replaces", status := .proven
    prop := ``SearchPrefixLaw, thm := some ``searchPrefixLaw_proven
    notes := "Assumes the INFO block's shape (textlibs-re-compiled-prefix-block shows _compile_info writes it) and that SRE(match) never sets must_advance, which it only reads." },
  { id := "textlibs-re-compiled-prefix-block", pyFile := "Lib/re/_compiler.py", pyFns := ["_compile_info"]
    statement := "With a literal prefix of two or more characters, _compile_info writes the prefix and then its overlap table where SRE(search) reads them."
    source := "the engine reads back what the compiler writes", status := .proven
    prop := ``CompiledPrefixBlock, thm := some ``compiledPrefixBlock_proven },
  { id := "textlibs-re-literal-prefix-sound", pyFile := "Lib/re/_compiler.py", pyFns := ["_get_literal_prefix", "_get_iscased"]
    statement := "The declarative semantics matches only where the text starts with the literal prefix, through nested groups and flag changes."
    source := "an optimization preserves the search it replaces", status := .proven
    prop := ``LiteralPrefixSound, thm := some ``literalPrefixSound_proven
    notes := "Excludes IGNORECASE|LOCALE, where _compile_info writes no prefix." },
  { id := "textlibs-re-charset-preserved", pyFile := "Lib/re/_compiler.py", pyFns := ["_optimize_charset", "_compile_charset"]
    statement := "SRE(charset) on the compiled set answers what the unoptimized set says, for every set and character, through the literal, range, bitmap and BIGCHARSET forms and the [\\s\\S] shortcuts."
    source := "an optimization preserves the set it replaces", status := .proven
    prop := ``CharsetPreserved, thm := some ``charsetPreserved_proven
    notes := "Without IGNORECASE; textlibs-re-charset-preserved-ignorecase has the other case. NEGATE first is the parser's invariant." },
  { id := "textlibs-re-charset-preserved-ignorecase", pyFile := "Lib/re/_compiler.py", pyFns := []
    statement := "The same under IGNORECASE, with the character lower-cased when the set is cased."
    source := "an optimization preserves the set it replaces", status := .open
    prop := ``CharsetPreservedIgnorecase
    notes := "Difftest agrees (re.sem), and categories in cased sets agree on all code points. Needs the fix-table steps of literalPass and rangeMark proved like the case-free ones." },
  { id := "textlibs-re-findall-is-finditer", pyFile := "Modules/_sre/sre.c"
    pyFns := []
    statement := "findall is finditer with each match read as the whole match, the group, or the tuple of groups, with '' for a group that did not take part. For every pattern."
    source := "twin: findall and finditer", status := .proven
    prop := ``FindallIsFinditer, thm := some ``findallIsFinditer_proven
    notes := "Relative law: it assumes scanLoop succeeds, and scanLoop itself is stated nowhere, so a scanLoop that always fails passes. No row is credited until textlibs-re-sem-agrees-no-self-test settles it." },
  { id := "textlibs-re-split-is-finditer", pyFile := "Modules/_sre/sre.c", pyFns := []
    statement := "split cuts at the spans finditer finds and keeps the groups, including for patterns that match the empty string."
    source := "twin: split and finditer", status := .proven
    prop := ``SplitIsFinditer, thm := some ``splitIsFinditer_proven
    notes := "maxsplit 0; a positive maxsplit stops the same loop early. Relative law: it assumes scanLoop succeeds, and scanLoop itself is stated nowhere, so a scanLoop that always fails passes. No row is credited until textlibs-re-sem-agrees-no-self-test settles it." },
  { id := "textlibs-re-sub-is-finditer", pyFile := "Modules/_sre/sre.c", pyFns := []
    statement := "sub with a string repl rebuilds the subject from what finditer finds, with a literal or an expanded template at each match; a template that fails fails the call."
    source := "twin: sub and finditer", status := .proven
    prop := ``SubIsFinditer, thm := some ``subIsFinditer_proven
    notes := "count 0. textlibs-re-sub-call-is-finditer has the callable path. Relative law: it assumes scanLoop succeeds, and scanLoop itself is stated nowhere, so a scanLoop that always fails passes. No row is credited until textlibs-re-sem-agrees-no-self-test settles it." },
  { id := "textlibs-re-sub-call-is-finditer", pyFile := "Modules/_sre/sre.c", pyFns := []
    statement := "A callable repl is called once per match in order, for any callable: a call that raises ends sub with that exception and no later call runs, and a result of the wrong type surfaces only at the join."
    source := "docs: re.sub with a function", status := .proven
    prop := ``SubCallIsFinditer, thm := some ``subCallIsFinditer_proven
    notes := "Relative law: it assumes scanLoop succeeds, and scanLoop itself is stated nowhere, so a scanLoop that always fails passes. No row is credited until textlibs-re-sem-agrees-no-self-test settles it." },
  { id := "textlibs-re-group-index-range", pyFile := "Modules/_sre/sre.c", pyFns := ["match_getindex"]
    statement := "An integer group index is valid exactly when it is in range, however large; the failure is IndexError."
    source := "docs: Match.group", status := .proven
    prop := ``GroupIndexRange, thm := some ``groupIndexRange_proven },
  { id := "textlibs-re-match-methods-agree", pyFile := "Modules/_sre/sre.c"
    pyFns := ["match_getslice", "match_getslice_by_index", "match_group", "_sre_SRE_Match_start_impl", "_sre_SRE_Match_end_impl", "_sre_SRE_Match_span_impl", "match_regs", "_sre_SRE_Match_groups_impl"]
    statement := "span, start, end, regs, group and groups say the same thing about a group and fail the same way, for every index object."
    source := "twin: the Match methods", status := .proven
    prop := ``MatchMethodsAgree, thm := some ``matchMethodsAgree_proven },
  { id := "textlibs-re-groupdict-agrees", pyFile := "Modules/_sre/sre.c", pyFns := ["_sre_SRE_Match_groupdict_impl"]
    statement := "groupdict()[name] is group(name)."
    source := "docs: Match.groupdict", status := .proven
    prop := ``GroupdictAgrees, thm := some ``groupdictAgrees_proven },
  { id := "textlibs-re-scanner-agrees-compile", pyFile := "Lib/re/__init__.py", pyFns := ["Scanner.__init__", "Scanner.scan"]
    statement := "What a phrase matches under re.compile is a token of re.Scanner."
    source := "twin: Scanner and compile", status := .refuted
    prop := ``ScannerAgreesCompile, thm := some ``scannerAgreesCompile_refuted
    bug := some "textlibs-re-scanner-drops-flags"
    notes := "\\w+ on 'é'. The counterexample runs Scanner.__init__ and the first step of Scanner.scan." },
  { id := "textlibs-csv-sniff-usable", pyFile := "Lib/csv.py", pyFns := ["Sniffer.sniff", "Sniffer._guess_delimiter"]
    statement := "What sniff returns has a delimiter different from its quotechar, so that reader accepts it."
    source := "docs: Sniffer.sniff returns a Dialect subclass", status := .refuted
    prop := ``SniffUsable, thm := some ``sniffUsable_refuted
    bug := some "textlibs-csv-sniffer-unusable-dialect"
    notes := "sniff('\\\"'). Fixed on main by a rewrite of Sniffer." },
  { id := "textlibs-csv-sniff-respects-delimiters", pyFile := "Lib/csv.py"
    pyFns := ["Sniffer.sniff", "Sniffer._guess_quote_and_delimiter", "Sniffer._guess_delimiter"]
    statement := "sniff(sample, delimiters) returns a delimiter from delimiters, through both guessers and the preferred fallback."
    source := "docs: Sniffer.sniff", status := .proven
    prop := ``SniffRespectsDelimiters, thm := some ``sniffRespectsDelimiters_proven },
  { id := "textlibs-re-combine-flags", pyFile := "Lib/re/_compiler.py", pyFns := ["_combine_flags"]
    statement := "Every bit of _combine_flags: del_flags clears, add_flags sets, and a type flag in add_flags first clears the old type flags."
    source := "docs: re, inline flag groups", status := .proven
    prop := ``CombineFlagsLaw, thm := some ``combineFlagsLaw_proven },
  { id := "textlibs-re-ascii-case", pyFile := "Modules/_sre/sre.c"
    pyFns := ["sre_lower_ascii", "_sre_ascii_iscased_impl", "_sre_ascii_tolower_impl"]
    statement := "A code point is ASCII-cased exactly when a case mapping moves it, and the mappings undo each other."
    source := "twin: iscased and the case mappings", status := .proven
    prop := ``AsciiCaseLaw, thm := some ``asciiCaseLaw_proven },
  { id := "textlibs-re-char-loc-ignore", pyFile := "Modules/_sre/sre.c", pyFns := ["char_loc_ignore"]
    statement := "In the C locale, a letter of either case matches itself and its other case, and nothing else."
    source := "docs: re.LOCALE with IGNORECASE", status := .proven
    prop := ``CharLocIgnoreLaw, thm := some ``charLocIgnoreLaw_proven
    notes := "C locale only. Other locales are out of the model, as the file's header says." },
  { id := "textlibs-re-category-negation", pyFile := "Modules/_sre/sre.c", pyFns := ["sre_category"]
    statement := "Under any flags, a category and its negation answer opposite ways for every character."
    source := "the [\\s\\S] shortcut of _optimize_charset relies on it", status := .proven
    prop := ``CategoryNegation, thm := some ``categoryNegation_proven },
  { id := "textlibs-re-compile-law", pyFile := "Lib/re/__init__.py", pyFns := ["_compile"]
    statement := "_compile: a compiled pattern with flags is ValueError, one without goes through, anything but a string or a pattern is TypeError, and a string compiles under its own kind."
    source := "docs: re.compile", status := .proven
    prop := ``ReCompileLaw, thm := some ``reCompileLaw_proven
    notes := "The caches are not modelled: they only return an earlier result. An unhashable pattern raises at the cache lookup first, which the model's `other` does not separate." },
  { id := "textlibs-re-escape-round-trip", pyFile := "Lib/re/__init__.py", pyFns := []
    statement := "re.escape(s) parses to the literal characters of s, with or without VERBOSE."
    source := "docs: re.escape", status := .open
    prop := ``EscapeRoundTrip
    notes := "100000 random strings and every code point below U+0300 agree on CPython. Needs parseSub walked over the escape branch of the tokenizer." },
  { id := "textlibs-path-p-splitext", pyFile := "Lib/posixpath.py", pyFns := ["splitext"]
    statement := "root + ext == p, an extension starts with a dot, and it holds no separator."
    source := "docs: os.path.splitext", status := .proven
    prop := ``SplitextLaw, thm := some ``splitextLaw_proven
    notes := "Stated on genericpath._splitext, which both splitext functions call." },
  { id := "textlibs-path-n-splitext", pyFile := "Lib/ntpath.py", pyFns := ["splitext"]
    statement := "The same for ntpath, with both separators."
    source := "docs: os.path.splitext", status := .proven
    prop := ``SplitextLaw, thm := some ``splitextLaw_proven },
  { id := "textlibs-path-p-split", pyFile := "Lib/posixpath.py", pyFns := ["split"]
    statement := "The tail of split has no slash, and the path is the head, some slashes, and the tail."
    source := "docs: os.path.split", status := .proven
    prop := ``PosixSplitLaw, thm := some ``posixSplitLaw_proven },
  { id := "textlibs-path-p-join", pyFile := "Lib/posixpath.py", pyFns := ["join"]
    statement := "join of two values of a kind: an absolute second part replaces the first, and otherwise one slash goes between them unless the first ends in one."
    source := "docs: os.path.join", status := .proven
    prop := ``JoinLaw, thm := some ``joinLaw_proven },
  { id := "textlibs-path-p-join-mix", pyFile := "Lib/posixpath.py", pyFns := ["join"]
    statement := "Mixing str and bytes through an os.PathLike gives the same error as without one."
    source := "twin: join with and without PathLike", status := .refuted
    prop := ``JoinMixMessage, thm := some ``joinMixMessage_refuted
    bug := some "textlibs-path-join-pathlike-error" },
  { id := "textlibs-path-p-join-fspath-error", pyFile := "Lib/posixpath.py", pyFns := ["join"]
    statement := "An exception from __fspath__ reaches the caller of join."
    source := "invariant: exceptions are not rewritten", status := .refuted
    prop := ``JoinKeepsFspathError, thm := some ``joinKeepsFspathError_refuted
    bug := some "textlibs-path-join-pathlike-error" },
  { id := "textlibs-path-p-join-other-errors", pyFile := "Lib/posixpath.py", pyFns := ["join"]
    statement := "Exceptions from __fspath__ other than TypeError and AttributeError reach the caller, and later arguments are not read."
    source := "Lib/posixpath.py:85", status := .proven
    prop := ``JoinPassesOtherErrors, thm := some ``joinPassesOtherErrors_proven },
  { id := "textlibs-path-p-normpath-twin", pyFile := "Lib/posixpath.py", pyFns := []
    statement := "C _Py_normpath_and_size and the Python fallback of posixpath.normpath agree on every path."
    source := "twin: C and Python", status := .open
    prop := ``PosixNormpathTwin
    notes := "Both are modelled and agree with CPython on every difftest case. Needs an invariant relating the C output buffer to the fallback's component list." },
  { id := "textlibs-path-p-normpath-idempotent", pyFile := "Lib/posixpath.py", pyFns := []
    statement := "posixpath.normpath is idempotent."
    source := "invariant", status := .open
    prop := ``PosixNormpathIdempotent
    notes := "Needs splitOn and intercalate shown inverse on the normal form." },
  { id := "textlibs-path-n-splitroot", pyFile := "Lib/ntpath.py", pyFns := ["splitdrive"]
    statement := "The three parts of splitroot are the path, the root is at most one separator, and a drive letter, a lone separator and neither are told apart."
    source := "docs: os.path.splitroot", status := .proven
    prop := ``NtSplitrootLaw, thm := some ``ntSplitrootLaw_proven },
  { id := "textlibs-path-n-join-absolute", pyFile := "Lib/ntpath.py", pyFns := ["join"]
    statement := "ntpath.join with a second part that has a drive and a root gives that part, whatever came first."
    source := "docs: os.path.join", status := .proven
    prop := ``NtJoinAbsolute, thm := some ``ntJoinAbsolute_proven },
  { id := "textlibs-path-n-normpath-relative", pyFile := "Lib/ntpath.py", pyFns := []
    statement := "ntpath.normpath keeps a path with no drive and no root that way."
    source := "docs: os.path.normpath", status := .refuted
    prop := ``NtNormpathKeepsRelative, thm := some ``ntNormpathKeepsRelative_refuted
    bug := some "textlibs-path-ntpath-normpath-drive"
    notes := "Duplicate of #100162 (open). normpath is in a try/except row the fallback sits in; no row credited." },
  { id := "textlibs-shlex-join-round-trip", pyFile := "Lib/shlex.py"
    pyFns := ["shlex.read_token", "shlex.__next__", "split", "join", "quote"]
    statement := "shlex.split(shlex.join(args)) == args, for every list of strings."
    source := "docs: shlex.join", status := .proven
    prop := ``JoinRoundTrip, thm := some ``joinRoundTrip_proven
    notes := "Walks the state machine over what quote writes: safe words, quoted text, the five-character form of a quote, and empty strings." },
  { id := "textlibs-shlex-quote-type", pyFile := "Lib/shlex.py", pyFns := ["quote"]
    statement := "quote raises TypeError for anything but a string."
    source := "the check at Lib/shlex.py:326", status := .refuted
    prop := ``QuoteRejectsNonStr, thm := some ``quoteRejectsNonStr_refuted
    bug := some "textlibs-shlex-quote-false-objects" },
  { id := "textlibs-shlex-stream-failure", pyFile := "Lib/shlex.py", pyFns := ["shlex.read_token"]
    statement := "A stream that raises stops the lexer with that exception."
    source := "invariant: failures pass through", status := .proven
    prop := ``StreamFailurePasses, thm := some ``streamFailurePasses_proven },
  { id := "textlibs-shlex-open-quote", pyFile := "Lib/shlex.py", pyFns := ["shlex.read_token"]
    statement := "An open quote at the end of the text raises ValueError, whatever was read."
    source := "Lib/shlex.py:192-196", status := .proven
    prop := ``OpenQuoteRaises, thm := some ``openQuoteRaises_proven },
  { id := "textlibs-csv-round-trip", pyFile := "Modules/_csv.c"
    pyFns := ["join_reset", "join_append_data", "join_append", "join_append_lineterminator", "csv_writerow_lock_held",
      "csv_writerow", "parse_add_char", "parse_process_char"]
    statement := "For every accepted dialect with QUOTE_MINIMAL or QUOTE_ALL, reading back the text writerow wrote gives the row."
    source := "the module's purpose: reader reads what writer wrote", status := .refuted
    prop := ``CsvRoundTrip, thm := some ``csvRoundTrip_refuted
    bug := some "textlibs-csv-skipinitialspace-round-trip"
    notes := "skipinitialspace=True, field ' a'. The counterexample runs the plain-character path of join_append_data and the START_FIELD, IN_FIELD and EAT_CRNL states of parse_process_char." },
  { id := "textlibs-csv-round-trip-no-skip", pyFile := "Modules/_csv.c"
    pyFns := ["join_append_data", "join_append", "join_append_lineterminator", "csv_writerow_lock_held", "csv_writerow",
      "parse_save_field", "parse_add_char", "parse_process_char", "parse_reset", "Reader_iternext_lock_held",
      "Reader_iternext"]
    statement := "With skipinitialspace off, QUOTE_MINIMAL or QUOTE_ALL, a newline line terminator and fields within the limit, reading back what writerow wrote gives the row."
    source := "the module's purpose: reader reads what writer wrote; docs: the reader recognises only \\r and \\n", status := .proven
    prop := ``CsvRoundTripNoSkip, thm := some ``csvRoundTripNoSkip_proven
    notes := "Runs through the unquoted, escaped and quoted states of the reader and the escape and doublequote logic of the writer. Each excluded case is on record: textlibs-csv-round-trip for skipinitialspace, textlibs-csv-num-fields for 2^31 fields." },
  { id := "textlibs-csv-round-trip-any-terminator", pyFile := "Modules/_csv.c"
    pyFns := ["parse_process_char", "join_append_lineterminator"]
    statement := "The round trip holds for any line terminator."
    source := "the assumption of textlibs-csv-round-trip-no-skip", status := .refuted
    prop := ``CsvRoundTripAnyTerminator, thm := some ``csvRoundTripAnyTerminator_refuted
    bug := some "textlibs-csv-round-trip-documented-limits"
    notes := "lineterminator='x': the reader takes the terminator as field text. Documented, so this records the assumption and is not for filing." },
  { id := "textlibs-csv-round-trip-over-limit", pyFile := "Modules/_csv.c", pyFns := ["parse_add_char"]
    statement := "The round trip holds for fields over the field size limit."
    source := "the assumption of textlibs-csv-round-trip-no-skip", status := .refuted
    prop := ``CsvRoundTripOverLimit, thm := some ``csvRoundTripOverLimit_refuted
    bug := some "textlibs-csv-round-trip-documented-limits"
    notes := "The writer has no limit and the reader raises csv.Error. Documented, so this records the assumption and is not for filing." },
  { id := "textlibs-csv-round-trip-any-quoting", pyFile := "Modules/_csv.c", pyFns := []
    statement := "The round trip holds for every quoting style."
    source := "the assumption of textlibs-csv-round-trip-no-skip", status := .open
    prop := ``CsvRoundTripAnyQuoting
    notes := "Held for all six styles in 300000 random dialects and rows on CPython. The proof covers QUOTE_MINIMAL and QUOTE_ALL; the others need the float and None paths of parse_save_field shown not to fire on what the writer quotes." },
  { id := "textlibs-csv-round-trip-not-code-points", pyFile := "Modules/_csv.c", pyFns := []
    statement := "The round trip holds for values that are not code points."
    source := "the assumption of textlibs-csv-round-trip-no-skip", status := .open
    prop := ``CsvRoundTripNotCodePoints
    notes := "False in the model at the EOL and NOT_SET sentinels, which no str can hold: the assumption is the type invariant of str. There is no Python reproducer, so it is recorded here rather than refuted." },
  { id := "textlibs-csv-writerow-resets", pyFile := "Modules/_csv.c", pyFns := ["join_reset"]
    statement := "Whatever a failed row left in the record buffer, the next writerow starts clean."
    source := "Modules/_csv.c:1346", status := .proven
    prop := ``WriterowResets, thm := some ``writerowResets_proven },
  { id := "textlibs-csv-set-char", pyFile := "Modules/_csv.c", pyFns := ["_set_char"]
    statement := "_set_char accepts exactly a missing argument, as the default, or a str or str subclass of length one."
    source := "the checks' messages", status := .proven
    prop := ``SetCharLaw, thm := some ``setCharLaw_proven },
  { id := "textlibs-csv-set-char-or-none", pyFile := "Modules/_csv.c", pyFns := ["_set_char_or_none"]
    statement := "_set_char_or_none accepts exactly what _set_char does, and None as NOT_SET."
    source := "the checks' messages", status := .proven
    prop := ``SetCharOrNoneLaw, thm := some ``setCharOrNoneLaw_proven },
  { id := "textlibs-csv-set-str", pyFile := "Modules/_csv.c", pyFns := ["_set_str"]
    statement := "_set_str accepts exactly a missing argument, as the default, or a str or str subclass."
    source := "the checks' messages", status := .proven
    prop := ``SetStrLaw, thm := some ``setStrLaw_proven },
  { id := "textlibs-csv-set-int", pyFile := "Modules/_csv.c", pyFns := ["_set_int"]
    statement := "_set_int accepts exactly a missing argument, as the default, or an exact int that fits a C int; a bool is refused, and an int out of range is OverflowError."
    source := "the checks' messages", status := .proven
    prop := ``SetIntLaw, thm := some ``setIntLaw_proven },
  { id := "textlibs-csv-dialect-valid", pyFile := "Modules/_csv.c"
    pyFns := ["dialect_check_quoting", "dialect_check_char", "dialect_check_chars"]
    statement := "Every accepted dialect has a known quoting style, a quote character unless quoting is off, no newline or line terminator character as a special character, no space as escape or quote character under skipinitialspace, and pairwise different special characters."
    source := "docs: dialect parameters; the checks' messages", status := .proven
    prop := ``DialectValid, thm := some ``dialectValid_proven },
  { id := "textlibs-csv-dialect-stores", pyFile := "Modules/_csv.c", pyFns := ["_set_bool"]
    statement := "An accepted dialect stores each converted argument, or the default for a missing one; boolean attributes are the argument's truth value."
    source := "docs: dialect parameters", status := .proven
    prop := ``DialectStores, thm := some ``dialectStores_proven },
  { id := "textlibs-csv-dialect-bool-raises", pyFile := "Modules/_csv.c", pyFns := ["_set_bool"]
    statement := "A raising __bool__ on a boolean parameter raises out of the dialect, in conversion order."
    source := "Modules/_csv.c:223-225", status := .proven
    prop := ``DialectBoolRaises, thm := some ``dialectBoolRaises_proven },
  { id := "textlibs-csv-dialect-rebuild", pyFile := "Modules/_csv.c"
    pyFns := ["get_char_or_None", "Dialect_get_lineterminator", "Dialect_get_delimiter", "Dialect_get_escapechar",
      "Dialect_get_quotechar", "Dialect_get_quoting"]
    statement := "Rebuilding a dialect from the attributes its getters return gives the same settings."
    source := "docs: Dialect attributes; DIALECT_GETATTR", status := .proven
    prop := ``DialectRebuild, thm := some ``dialectRebuild_proven },
  { id := "textlibs-csv-dialect-reuse", pyFile := "Modules/_csv.c", pyFns := ["dialect_new", "_call_dialect"]
    statement := "A Dialect passed with no overrides, by value or by registered name, is the same object back; any other object gives a new dialect."
    source := "comment at Modules/_csv.c:475", status := .proven
    prop := ``DialectReuse, thm := some ``dialectReuse_proven
    notes := "Identity is a constructor of DRes, not equality of contents." },
  { id := "textlibs-csv-getattr-cleared", pyFile := "Modules/_csv.c", pyFns := ["dialect_new"]
    statement := "An AttributeError from a dialect attribute is cleared, so an object without the attributes gives the default dialect; any other exception comes out of dialect_new."
    source := "DIALECT_GETATTR, Modules/_csv.c", status := .proven
    prop := ``GetattrCleared, thm := some ``getattrCleared_proven },
  { id := "textlibs-csv-dialect-keywords", pyFile := "Modules/_csv.c", pyFns := ["dialect_new"]
    statement := "A keyword beats the attribute, and with one present an object is not reused, even a Dialect: the new one is built from the keywords and the old object's attributes."
    source := "DIALECT_GETATTR and the reuse test, Modules/_csv.c", status := .proven
    prop := ``DialectKeywords, thm := some ``dialectKeywords_proven },
  { id := "textlibs-csv-dialect-arg-errors", pyFile := "Modules/_csv.c", pyFns := ["dialect_new"]
    statement := "PyArg_ParseTupleAndKeywords fails first, for too many arguments and for a keyword that names no parameter."
    source := "Modules/_csv.c:449-460", status := .proven
    prop := ``DialectArgErrors, thm := some ``dialectArgErrors_proven },
  { id := "textlibs-csv-dialect-unknown-name", pyFile := "Modules/_csv.c", pyFns := ["dialect_new", "get_dialect_from_registry"]
    statement := "A name that is not registered is csv.Error, whatever keywords come with it."
    source := "docs: csv.Error", status := .proven
    prop := ``DialectUnknownName, thm := some ``dialectUnknownName_proven },
  { id := "textlibs-csv-dialect-new-valid", pyFile := "Modules/_csv.c", pyFns := ["dialect_new"]
    statement := "What dialect_new builds, by any route, came through dialectBuild, so textlibs-csv-dialect-valid applies to it; the stored line terminator is that of the arguments."
    source := "Modules/_csv.c:527-560", status := .proven
    prop := ``DialectNewValid, thm := some ``dialectNewValid_proven },
  { id := "textlibs-csv-subclass-attrs", pyFile := "Modules/_csv.c", pyFns := ["dialect_new"]
    statement := "An attribute of a Dialect subclass shadows the C field for DIALECT_GETATTR; one that raises AttributeError is cleared."
    source := "DIALECT_GETATTR, Modules/_csv.c", status := .proven
    prop := ``SubclassAttrs, thm := some ``subclassAttrs_proven },
  { id := "textlibs-csv-lineterminator-stored", pyFile := "Modules/_csv.c", pyFns := ["Dialect_get_lineterminator"]
    statement := "The getter returns the object in the slot, which is the argument itself, so a str subclass stays one; an empty slot gives NULL."
    source := "Modules/_csv.c:182-187", status := .proven
    prop := ``LineterminatorStored, thm := some ``lineterminatorStored_proven
    notes := "Identity is the constructor LtRes.stored, not equality of contents." },
  { id := "textlibs-csv-lineterminator-not-null", pyFile := "Modules/_csv.c", pyFns := ["Dialect_get_lineterminator"]
    statement := "The lineterminator getter never returns NULL with no exception set."
    source := "invariant: the C API result rule", status := .refuted
    prop := ``LineterminatorNotNull, thm := some ``lineterminatorNotNull_refuted
    bug := some "textlibs-csv-lineterminator-null"
    notes := "A half-built instance, reached from a subclass __del__ when dialect_new fails." },
  { id := "textlibs-csv-call-dialect", pyFile := "Modules/_csv.c", pyFns := ["_call_dialect"]
    statement := "type_call runs tp_init on what dialect_new returned: a reused subclass instance runs its own __init__, which can raise; keywords make a new instance, which skips it; no instance and no keywords give the default."
    source := "Objects/typeobject.c:2522-2524", status := .proven
    prop := ``CallDialectLaw, thm := some ``callDialectLaw_proven
    notes := "The first clause is the behaviour of bugs/textlibs-csv-dialect-subclass-reinit.yaml, stated rather than refuted." },
  { id := "textlibs-csv-reuse-never-fails", pyFile := "Modules/_csv.c", pyFns := ["_call_dialect"]
    statement := "_call_dialect on a reusable instance hands it back and cannot fail."
    source := "the \"Can we reuse this instance?\" branch of dialect_new", status := .refuted
    prop := ``ReuseNeverFails, thm := some ``reuseNeverFails_refuted
    bug := some "textlibs-csv-dialect-subclass-reinit" },
  { id := "textlibs-csv-no-pickle", pyFile := "Modules/_csv.c", pyFns := ["Dialect_reduce"]
    statement := "__reduce__ and __reduce_ex__ raise TypeError with the short name of the instance's own class, unless that class defines the method."
    source := "docs: dialect_reduce_doc", status := .proven
    prop := ``DialectNoPickle, thm := some ``dialectNoPickle_proven },
  { id := "textlibs-csv-register-sees-callbacks", pyFile := "Modules/_csv.c", pyFns := ["csv_register_dialect"]
    statement := "PyDict_SetItem at :1635 works on the registry as callbacks left it, not as it was at :1632, for any callbacks; a failed _call_dialect keeps their effects and adds nothing."
    source := "Modules/_csv.c:1632-1635", status := .proven
    prop := ``RegisterSeesCallbacks, thm := some ``registerSeesCallbacks_proven },
  { id := "textlibs-csv-subclass-key", pyFile := "Modules/_csv.c", pyFns := ["csv_register_dialect", "_csv_list_dialects_impl"]
    statement := "A str subclass stays the key with its own __hash__ and __eq__: list_dialects returns the object, and a key that compares unequal is listed and not found by its text."
    source := "PyDict_SetItem", status := .proven
    prop := ``SubclassKeyKept, thm := some ``subclassKeyKept_proven },
  { id := "textlibs-csv-list-dialects", pyFile := "Modules/_csv.c", pyFns := ["_csv_list_dialects_impl"]
    statement := "list_dialects is the keys in dict order: a new name comes last, a name set again keeps its place, and a removed name is gone."
    source := "docs: list_dialects", status := .proven
    prop := ``ListDialectsLaw, thm := some ``listDialectsLaw_proven },
  { id := "textlibs-csv-reader-resets", pyFile := "Modules/_csv.c", pyFns := ["parse_reset"]
    statement := "parse_reset clears fields, the NULL of the re-entrancy crash, the state, the field and unquoted_field, so the next __next__ cannot depend on what the last one left."
    source := "Modules/_csv.c:913-923", status := .proven
    prop := ``ReaderResets, thm := some ``readerResets_proven },
  { id := "textlibs-csv-registry", pyFile := "Modules/_csv.c", pyFns := ["csv_register_dialect"]
    statement := "A registered dialect can be read back by name, and it is the object _call_dialect made."
    source := "docs: register_dialect, get_dialect", status := .proven
    prop := ``RegistryLaw, thm := some ``registryLaw_proven },
  { id := "textlibs-csv-register-checks", pyFile := "Modules/_csv.c", pyFns := ["csv_register_dialect"]
    statement := "register_dialect refuses a non-string name before looking at the dialect, and a failing __hash__ leaves the dialect unregistered."
    source := "Modules/_csv.c:1627-1638", status := .proven
    prop := ``RegisterNameChecks, thm := some ``registerNameChecks_proven },
  { id := "textlibs-csv-get-dialect", pyFile := "Modules/_csv.c"
    pyFns := ["get_dialect_from_registry", "_csv_get_dialect_impl"]
    statement := "get_dialect for every name object: failures of __hash__ and __eq__, no match, and an equal key."
    source := "docs: get_dialect; Modules/_csv.c:166-168", status := .proven
    prop := ``GetDialectLaw, thm := some ``getDialectLaw_proven },
  { id := "textlibs-csv-unregister", pyFile := "Modules/_csv.c", pyFns := ["_csv_unregister_dialect_impl", "_csv_list_dialects_impl"]
    statement := "unregister_dialect does not hash on an empty registry; otherwise a raising __hash__ raises, an unknown name is csv.Error, and a removed name leaves list_dialects."
    source := "docs: unregister_dialect", status := .proven
    prop := ``UnregisterLaw, thm := some ``unregisterLaw_proven },
  { id := "textlibs-csv-field-limit", pyFile := "Modules/_csv.c", pyFns := ["_csv_field_size_limit_impl"]
    statement := "field_size_limit for every argument: the old limit for no argument or an int that fits, OverflowError for one that does not, TypeError for anything else, bool included."
    source := "docs: field_size_limit", status := .proven
    prop := ``FieldLimit, thm := some ``fieldLimit_proven },
  { id := "textlibs-csv-add-char-limit", pyFile := "Modules/_csv.c", pyFns := ["parse_add_char"]
    statement := "parse_add_char raises exactly at the field limit, and otherwise appends one character."
    source := "docs: field_size_limit", status := .proven
    prop := ``AddCharLimit, thm := some ``addCharLimit_proven },
  { id := "textlibs-csv-save-field", pyFile := "Modules/_csv.c", pyFns := ["parse_save_field"]
    statement := "What parse_save_field appends for every quoting style, with float() through PyFloat_FromString."
    source := "docs: QUOTE_NONNUMERIC, QUOTE_NOTNULL, QUOTE_STRINGS", status := .proven
    prop := ``SaveFieldLaw, thm := some ``saveFieldLaw_proven },
  { id := "textlibs-csv-eat-crnl", pyFile := "Modules/_csv.c", pyFns := ["parse_process_char"]
    statement := "After a newline ends a record, a further newline is ignored, the end of the line finishes the record, and any other character raises csv.Error."
    source := "the error message at Modules/_csv.c:901-903", status := .proven
    prop := ``EatCrnl, thm := some ``eatCrnl_proven },
  { id := "textlibs-csv-iter-raises", pyFile := "Modules/_csv.c"
    pyFns := ["Reader_iternext_lock_held", "Reader_iternext", "parse_reset"]
    statement := "An exception from the input iterator passes through, and the next __next__ starts a fresh record from the next line."
    source := "Modules/_csv.c:942-957", status := .proven
    prop := ``IterRaisePasses, thm := some ``iterRaisePasses_proven },
  { id := "textlibs-csv-eof", pyFile := "Modules/_csv.c", pyFns := ["Reader_iternext_lock_held"]
    statement := "End of input: StopIteration with nothing open, csv.Error in strict mode with a field or quote open, and the open field as a row otherwise."
    source := "docs: strict", status := .proven
    prop := ``EofLaw, thm := some ``eofLaw_proven },
  { id := "textlibs-csv-not-str-line", pyFile := "Modules/_csv.c", pyFns := ["Reader_iternext_lock_held"]
    statement := "An item that is not a string raises csv.Error naming its type, without counting a line."
    source := "the error message at Modules/_csv.c:959-963", status := .proven
    prop := ``NotStrLine, thm := some ``notStrLine_proven },
  { id := "textlibs-csv-parse-failure", pyFile := "Modules/_csv.c", pyFns := ["Reader_iternext_lock_held"]
    statement := "A parse failure raises and keeps the state C left, with the line counted."
    source := "Modules/_csv.c:974-984", status := .proven
    prop := ``ParseFailureKeeps, thm := some ``parseFailureKeeps_proven },
  { id := "textlibs-csv-already-advanced", pyFile := "Modules/_csv.c", pyFns := ["Reader_iternext_lock_held"]
    statement := "If the input iterator advances the reader through a whole row and then returns a line, the outer call raises csv.Error."
    source := "the guard at Modules/_csv.c:968-973", status := .proven
    prop := ``AlreadyAdvanced, thm := some ``alreadyAdvanced_proven },
  { id := "textlibs-csv-reader-no-crash", pyFile := "Modules/_csv.c"
    pyFns := ["Reader_iternext_lock_held", "Reader_iternext", "parse_reset", "parse_save_field"]
    statement := "No input iterator crashes the reader."
    source := "undisputed: Python code must not crash the interpreter", status := .refuted
    prop := ``ReaderNoCrash, thm := some ``readerNoCrash_refuted
    bug := some "textlibs-csv-reader-reentrant-null-fields"
    notes := "The iterator re-enters the reader, which ends the input with a quoted field open, and then ends the outer call too. Duplicate of python/cpython#157379." },
  { id := "textlibs-csv-crash-needs-quote", pyFile := "Modules/_csv.c", pyFns := ["Reader_iternext_lock_held"]
    statement := "With fields NULL, the end of input is safe unless a quoted field is open."
    source := "narrowing of textlibs-csv-reader-no-crash", status := .proven
    prop := ``CrashNeedsOpenQuote, thm := some ``crashNeedsOpenQuote_proven },
  { id := "textlibs-csv-limit-live", pyFile := "Modules/_csv.c", pyFns := ["_csv_field_size_limit_impl", "parse_add_char"]
    statement := "field_size_limit called from the input iterator applies to the line it returns."
    source := "Modules/_csv.c:716", status := .proven
    prop := ``LimitIsLive, thm := some ``limitIsLive_proven },
  { id := "textlibs-csv-writer-iter-fails", pyFile := "Modules/_csv.c", pyFns := ["csv_writerow_lock_held", "csv_writerow", "csv_writerows"]
    statement := "writerow turns a TypeError from iter() into csv.Error and passes other exceptions; writerows passes all of them; the writer is untouched."
    source := "Modules/_csv.c:1334-1342, 1459-1462", status := .proven
    prop := ``WriterIterFails, thm := some ``writerIterFails_proven },
  { id := "textlibs-csv-write-result", pyFile := "Modules/_csv.c", pyFns := ["csv_writerow_lock_held", "csv_writerow", "join_append_lineterminator"]
    statement := "write is called once with the record and its terminator, and writerow returns what it returned or raises what it raised."
    source := "docs: writerow returns the return value of the call to write", status := .proven
    prop := ``WriteResult, thm := some ``writeResult_proven },
  { id := "textlibs-csv-field-raises", pyFile := "Modules/_csv.c", pyFns := ["csv_writerow_lock_held"]
    statement := "A row iterator that raises ends writerow with that exception, with no call to write."
    source := "Modules/_csv.c:1395-1397", status := .proven
    prop := ``FieldRaises, thm := some ``fieldRaises_proven },
  { id := "textlibs-csv-str-raises", pyFile := "Modules/_csv.c", pyFns := ["csv_writerow_lock_held"]
    statement := "A field whose str() raises ends writerow with that exception."
    source := "Modules/_csv.c:1381-1386", status := .proven
    prop := ``StrRaises, thm := some ``strRaises_proven },
  { id := "textlibs-csv-writerows-stop", pyFile := "Modules/_csv.c", pyFns := ["csv_writerows"]
    statement := "writerows stops at the first row that fails, with that exception."
    source := "Modules/_csv.c:1464-1469", status := .proven
    prop := ``WritesStopAtFailure, thm := some ``writesStopAtFailure_proven },
  { id := "textlibs-csv-writerows-result", pyFile := "Modules/_csv.c", pyFns := ["csv_writerows"]
    statement := "writerows returns None, whatever write returned."
    source := "Modules/_csv.c:1476", status := .proven
    prop := ``WriterowsResult, thm := some ``writerowsResult_proven },
  { id := "textlibs-csv-num-fields", pyFile := "Modules/_csv.c", pyFns := ["join_append"]
    statement := "Once a field has been appended, the field count stays positive, so every later field gets its delimiter."
    source := "undisputed: a row's fields are separated by delimiters", status := .refuted
    prop := ``NumFieldsPositive, thm := some ``numFieldsPositive_refuted
    bug := some "textlibs-csv-num-fields-int-overflow"
    notes := "num_fields is a C int. At INT_MAX the next field wraps it, and no delimiter is written for the next 2^31 fields." },
  { id := "textlibs-csv-join-delimiter", pyFile := "Modules/_csv.c", pyFns := ["join_append"]
    statement := "Below INT_MAX the field count is exact, and a field after the first starts with one delimiter."
    source := "narrowing of textlibs-csv-num-fields", status := .proven
    prop := ``JoinDelimiter, thm := some ``joinDelimiter_proven },
  { id := "textlibs-csv-reader-order", pyFile := "Modules/_csv.c", pyFns := ["csv_reader", "_call_dialect"]
    statement := "csv.reader fails in order: iter() of the input, then the dialect; a new reader starts on the input's iterator."
    source := "docs: csv.reader", status := .proven
    prop := ``CsvReaderOrder, thm := some ``csvReaderOrder_proven },
  { id := "textlibs-csv-writer-order", pyFile := "Modules/_csv.c", pyFns := ["csv_writer"]
    statement := "csv.writer needs a callable write attribute; AttributeError and a non-callable are the same TypeError, other exceptions pass through, and both come before the dialect."
    source := "docs: csv.writer", status := .proven
    prop := ``CsvWriterOrder, thm := some ``csvWriterOrder_proven },
  { id := "textlibs-csv-dialect-validate", pyFile := "Lib/csv.py", pyFns := ["Dialect.__init__", "Dialect._validate"]
    statement := "csv.Dialect accepts what _csv.Dialect accepts, reporting TypeError as csv.Error and passing other exceptions."
    source := "Lib/csv.py:109-114", status := .proven
    prop := ``DialectValidate, thm := some ``dialectValidate_proven },
  { id := "textlibs-csv-dictwriter-order", pyFile := "Lib/csv.py", pyFns := ["DictWriter._dict_to_list"]
    statement := "DictWriter yields the fields in fieldnames order, with restval for missing keys."
    source := "docs: DictWriter", status := .proven
    prop := ``DictToListOrder, thm := some ``dictToListOrder_proven },
  { id := "textlibs-csv-dictwriter-extra", pyFile := "Lib/csv.py", pyFns := ["DictWriter._dict_to_list", "DictWriter.writerow"]
    statement := "With extrasaction='raise', a key outside fieldnames raises ValueError and nothing reaches the writer."
    source := "docs: DictWriter", status := .proven
    prop := ``DictExtraRaises, thm := some ``dictExtraRaises_proven },
  { id := "textlibs-csv-dictwriter-row", pyFile := "Lib/csv.py", pyFns := ["DictWriter._dict_to_list", "DictWriter.writerow"]
    statement := "A dict that passes the check is written as the row of its values."
    source := "docs: DictWriter", status := .proven
    prop := ``DictWriterowIsRow, thm := some ``dictWriterowIsRow_proven },
  { id := "textlibs-csv-dictwriter-writerows", pyFile := "Lib/csv.py", pyFns := ["DictWriter.writerows"]
    statement := "DictWriter.writerows raises at the first dict with an extra key, in its place: the dicts before it are written and later ones are not looked at."
    source := "Lib/csv.py:225-226: map is lazy", status := .proven
    prop := ``MapStepsStop, thm := some ``mapStepsStop_proven },
  { id := "textlibs-csv-writeheader", pyFile := "Lib/csv.py", pyFns := ["DictWriter.writeheader"]
    statement := "writeheader writes the field names as one row, repeated names included."
    source := "docs: writeheader", status := .proven
    prop := ``WriteheaderLaw, thm := some ``writeheaderLaw_proven },
  { id := "textlibs-csv-extrasaction", pyFile := "Lib/csv.py", pyFns := ["DictWriter.__init__"]
    statement := "extrasaction is case-insensitive, and only raise and ignore are accepted."
    source := "Lib/csv.py:203-206", status := .proven
    prop := ``ExtrasactionLaw, thm := some ``extrasactionLaw_proven },
  { id := "textlibs-csv-dictrow", pyFile := "Lib/csv.py", pyFns := ["DictReader.__next__"]
    statement := "With distinct names, a row of the same length is their dict, and a longer one keeps the extras under restkey."
    source := "docs: DictReader", status := .proven
    prop := ``DictRowLaw, thm := some ``dictRowLaw_proven },
  { id := "textlibs-csv-dictreader-header", pyFile := "Lib/csv.py", pyFns := ["DictReader.fieldnames", "DictReader.__next__"]
    statement := "With no field names given, the first row becomes the names and the dict of the second comes out."
    source := "docs: DictReader", status := .proven
    prop := ``DictReaderHeader, thm := some ``dictReaderHeader_proven },
  { id := "textlibs-csv-dictreader-blank", pyFile := "Lib/csv.py", pyFns := ["DictReader.__next__"]
    statement := "Blank rows do not reach the caller, and a failure while skipping them passes through."
    source := "Lib/csv.py:178-182", status := .proven
    prop := ``DictReaderSkipsBlank, thm := some ``dictReaderSkipsBlank_proven },
  { id := "textlibs-csv-dictreader-init", pyFile := "Lib/csv.py", pyFns := ["DictReader.__init__"]
    statement := "DictReader passes its dialect and keywords to csv.reader, and every failure of csv.reader comes out of the constructor."
    source := "Lib/csv.py:150", status := .proven
    prop := ``DictReaderInit, thm := some ``dictReaderInit_proven },
  { id := "textlibs-re-digit-limit-parse", pyFile := "Lib/re/_parser.py"
    pyFns := ["_parse", "parse"]
    statement := "For every allowed sys.set_int_max_str_digits value, a str pattern parsed with no flags reports a bad pattern as PatternError or OverflowError, and never leaks ValueError."
    source := "docs: re.compile raises PatternError; Lib/re/_parser.py:670", status := .refuted
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
    source := "comment at Lib/re/_parser.py:471", status := .proven
    prop := ``PrefixFactor, thm := some ``prefixFactor_proven },
  { id := "textlibs-re-branch-set", pyFile := "Lib/re/_parser.py", pyFns := ["_parse_sub"]
    statement := "A branch of single characters and sets becomes one set that holds all of them."
    source := "comment at Lib/re/_parser.py:490", status := .proven
    prop := ``BranchSetLaw, thm := some ``branchSetLaw_proven },
  { id := "textlibs-re-flags", pyFile := "Lib/re/_parser.py", pyFns := ["_parse_flags"]
    statement := "An inline flag group never turns a flag both on and off or turns off a global flag, and the refused combinations raise the source's messages."
    source := "the messages at Lib/re/_parser.py:892-943", status := .proven
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
    prop := ``EscapeTwins, thm := some ``escapeTwins_proven },
  { id := "textlibs-textwrap-terminates", pyFile := "Lib/textwrap.py", pyFns := ["TextWrapper._wrap_chunks", "TextWrapper._handle_long_word"]
    statement := "For a positive width, _wrap_chunks returns."
    source := "invariant: no hang", status := .refuted
    prop := ``WrapTerminates, thm := some ``wrapTerminates_refuted
    bug := some "textlibs-textwrap-indent-hang" },
  { id := "textlibs-textwrap-succeeds", pyFile := "Lib/textwrap.py", pyFns := ["TextWrapper._wrap_chunks", "TextWrapper._handle_long_word"]
    statement := "With indents of at most width, _wrap_chunks returns exactly when its two checks pass."
    source := "narrows textlibs-textwrap-terminates", status := .proven
    prop := ``WrapSucceeds, thm := some ``wrapSucceeds_proven },
  { id := "textlibs-textwrap-errors", pyFile := "Lib/textwrap.py", pyFns := ["TextWrapper._wrap_chunks"]
    statement := "The width check comes first and the placeholder check second, each with its message."
    source := "Lib/textwrap.py:252-260", status := .proven
    prop := ``WrapErrors, thm := some ``wrapErrors_proven },
  { id := "textlibs-textwrap-width", pyFile := "Lib/textwrap.py", pyFns := ["TextWrapper._wrap_chunks"]
    statement := "With break_long_words on, every line is at most width."
    source := "docstring of TextWrapper.wrap", status := .refuted
    prop := ``WrapWidthLaw, thm := some ``wrapWidthLaw_refuted
    bug := some "textlibs-textwrap-indent-over-width" },
  { id := "textlibs-textwrap-width-narrow", pyFile := "Lib/textwrap.py", pyFns := ["TextWrapper._wrap_chunks", "TextWrapper._handle_long_word"]
    statement := "With break_long_words on and indents shorter than width, every line is at most width, including with max_lines."
    source := "narrows textlibs-textwrap-width", status := .proven
    prop := ``WrapWidthNarrow, thm := some ``wrapWidthNarrow_proven },
  { id := "textlibs-textwrap-keeps-text", pyFile := "Lib/textwrap.py", pyFns := ["TextWrapper._wrap_chunks", "TextWrapper._handle_long_word"]
    statement := "Without max_lines the lines hold all the text of the chunks, or all but its whitespace under drop_whitespace."
    source := "docstring of _wrap_chunks", status := .proven
    prop := ``WrapKeepsText, thm := some ``wrapKeepsText_proven },
  { id := "textlibs-textwrap-max-lines", pyFile := "Lib/textwrap.py", pyFns := ["TextWrapper._wrap_chunks"]
    statement := "With max_lines there are at most max(max_lines, 1) lines, and text that was cut leaves the stripped placeholder at the end."
    source := "docs: TextWrapper.max_lines", status := .proven
    prop := ``WrapMaxLines, thm := some ``wrapMaxLines_proven },
  { id := "textlibs-textwrap-no-break", pyFile := "Lib/textwrap.py", pyFns := ["TextWrapper._wrap_chunks", "TextWrapper._handle_long_word"]
    statement := "With break_long_words off, the lines are runs of the chunks, and only a single chunk exceeds width."
    source := "docstring of _wrap_chunks", status := .proven
    prop := ``WrapNoBreak, thm := some ``wrapNoBreak_proven },
  { id := "textlibs-textwrap-greedy", pyFile := "Lib/textwrap.py", pyFns := ["TextWrapper._wrap_chunks", "TextWrapper._handle_long_word"]
    statement := "With break_long_words and drop_whitespace off, each line ends only because the next chunk would not fit."
    source := "docstring of _wrap_chunks", status := .proven
    prop := ``WrapGreedy, thm := some ``wrapGreedy_proven
    notes := "Both switches are off so that the partition is exact; the same lines of code run with them on." },
  { id := "textlibs-textwrap-fitting-text", pyFile := "Lib/textwrap.py", pyFns := ["TextWrapper._wrap_chunks"]
    statement := "Text that fits in width passes, whatever the placeholder."
    source := "docs: shorten", status := .refuted
    prop := ``FittingTextPasses, thm := some ``fittingTextPasses_refuted
    bug := some "textlibs-textwrap-placeholder-check-first" },
  { id := "textlibs-binascii-qp-round-trip", pyFile := "Modules/binascii.c", pyFns := ["binascii_a2b_qp_impl", "binascii_b2a_qp_impl"]
    statement := "a2b_qp(b2a_qp(d)) == d for all bytes and both of quotetabs and header, given istext=False or no CRLF in d."
    source := "the implementation disagreeing with itself: round trip", status := .proven
    prop := ``QpRoundTripNarrow, thm := some ``qpRoundTripNarrow_proven },
  { id := "textlibs-binascii-qp-round-trip-broad", pyFile := "Modules/binascii.c", pyFns := ["binascii_a2b_qp_impl", "binascii_b2a_qp_impl"]
    statement := "a2b_qp(b2a_qp(d)) == d for all bytes."
    source := "the implementation disagreeing with itself: round trip", status := .refuted
    prop := ``QpRoundTrip, thm := some ``qpRoundTrip_refuted
    bug := some "textlibs-quopri-mixed-line-ends" },
  { id := "textlibs-quopri-file-round-trip", pyFile := "Lib/quopri.py", pyFns := ["encode", "decode", "encodestring", "decodestring"]
    statement := "encode then decode on files gives one write each and the data back, for all bytes and flags, with no CRLF in the data."
    source := "the implementation disagreeing with itself: round trip", status := .proven
    prop := ``FileRoundTrip, thm := some ``fileRoundTrip_proven },
  { id := "textlibs-quopri-file-failures", pyFile := "Lib/quopri.py", pyFns := ["encode", "decode"]
    statement := "A read that raises passes through with nothing written; a write that raises passes through after that write."
    source := "invariant", status := .proven
    prop := ``FileFailures, thm := some ``fileFailures_proven },
  { id := "textlibs-quopri-quote-set-twin", pyFile := "Lib/quopri.py", pyFns := ["needsquoting"]
    statement := "In the middle of a line, needsquoting and b2a_qp quote the same bytes."
    source := "the implementation disagreeing with itself: C and Python twins", status := .proven
    prop := ``QuoteSetTwin, thm := some ``quoteSetTwin_proven },
  { id := "textlibs-quopri-quote-decodes", pyFile := "Lib/quopri.py", pyFns := ["quote", "ishex", "unhex"]
    statement := "The pure-Python decoder undoes quote, for every byte."
    source := "the implementation disagreeing with itself: round trip", status := .proven
    prop := ``QuoteDecodes, thm := some ``quoteDecodes_proven },
  { id := "textlibs-quopri-encode-twin", pyFile := "Lib/quopri.py", pyFns := ["encode", "encodestring", "needsquoting", "quote"]
    statement := "The two bodies of encodestring agree."
    source := "the implementation disagreeing with itself: C and Python twins", status := .refuted
    prop := ``EncodeTwin, thm := some ``encodeTwin_refuted
    bug := some "textlibs-quopri-twins-disagree" },
  { id := "textlibs-quopri-decode-twin", pyFile := "Lib/quopri.py", pyFns := ["decode", "decodestring"]
    statement := "The two bodies of decodestring agree."
    source := "the implementation disagreeing with itself: C and Python twins", status := .refuted
    prop := ``DecodeTwin, thm := some ``decodeTwin_refuted
    bug := some "textlibs-quopri-twins-disagree" },
  { id := "textlibs-quopri-py-round-trip", pyFile := "Lib/quopri.py", pyFns := ["encode", "decode", "quote"]
    statement := "The pure-Python body round-trips."
    source := "the implementation disagreeing with itself: round trip", status := .refuted
    prop := ``PyRoundTrip, thm := some ``pyRoundTrip_refuted
    bug := some "textlibs-quopri-py-soft-break-escape" },
  { id := "textlibs-html-round-trip", pyFile := "Lib/html/__init__.py", pyFns := ["escape", "unescape", "_replace_charref"]
    statement := "unescape(escape(s, quote)) == s for every string, on the real entity table."
    source := "the implementation disagreeing with itself: round trip", status := .proven
    prop := ``UnescapeEscape, thm := some ``unescapeEscape_proven },
  { id := "textlibs-html-fast-path", pyFile := "Lib/html/__init__.py", pyFns := ["unescape"]
    statement := "The test for '&' before the regex agrees with the regex."
    source := "the implementation disagreeing with itself: fast and slow path", status := .proven
    prop := ``UnescapeFastPath, thm := some ``unescapeFastPath_proven },
  { id := "textlibs-html-escape-safe", pyFile := "Lib/html/__init__.py", pyFns := ["escape"]
    statement := "The output of escape holds no < or >, and with quote no quotes."
    source := "docstring of escape", status := .proven
    prop := ``EscapeSafe, thm := some ``escapeSafe_proven },
  { id := "textlibs-html-total", pyFile := "Lib/html/__init__.py", pyFns := ["unescape", "_replace_charref"]
    statement := "unescape never raises on a str."
    source := "invariant: no internal error leaking", status := .refuted
    prop := ``UnescapeTotal, thm := some ``unescapeTotal_refuted
    bug := some "textlibs-html-unescape-digit-limit" },
  { id := "textlibs-html-total-narrow", pyFile := "Lib/html/__init__.py", pyFns := ["unescape", "_replace_charref"]
    statement := "With no run of more than 4300 decimal digits, unescape does not raise."
    source := "narrows textlibs-html-total", status := .proven
    prop := ``UnescapeTotalNarrow, thm := some ``unescapeTotalNarrow_proven },
  { id := "textlibs-html-numeric-twin", pyFile := "Lib/html/__init__.py", pyFns := ["_replace_charref"]
    statement := "A decimal and a hexadecimal reference with the same value give the same result."
    source := "the implementation disagreeing with itself", status := .refuted
    prop := ``NumericTwin, thm := some ``numericTwin_refuted
    bug := some "textlibs-html-unescape-digit-limit" },
  { id := "textlibs-html-numeric-twin-narrow", pyFile := "Lib/html/__init__.py", pyFns := ["_replace_charref"]
    statement := "With at most 4300 decimal digits, decimal and hexadecimal references of one value agree."
    source := "narrows textlibs-html-numeric-twin", status := .proven
    prop := ``NumericTwinNarrow, thm := some ``numericTwinNarrow_proven },
  { id := "textlibs-html-numeric-valid", pyFile := "Lib/html/__init__.py", pyFns := ["_replace_charref"]
    statement := "A numeric reference gives nothing or one scalar value, never a surrogate, for every number."
    source := "docs: the HTML 5 rules", status := .proven
    prop := ``NumericValid, thm := some ``numericValid_proven },
  { id := "textlibs-html-named-longest", pyFile := "Lib/html/__init__.py", pyFns := ["_replace_charref"]
    statement := "A named reference is the whole name, else the longest proper prefix of two or more characters in the table, else unchanged."
    source := "comment at Lib/html/__init__.py:110", status := .proven
    prop := ``NamedLongest, thm := some ``namedLongest_proven },
  { id := "textlibs-difflib-find-longest", pyFile := "Lib/difflib.py", pyFns := ["SequenceMatcher.find_longest_match", "SequenceMatcher.__chain_b"]
    statement := "For any lawful elements, with no junk and nothing popular, the result is a longest match in the box under __eq__, the earliest in a of those, the earliest in b of those, for every box in range."
    source := "docstring of find_longest_match", status := .proven
    prop := ``FindLongestDocO, thm := some ``findLongestDocO_proven },
  { id := "textlibs-difflib-blocks", pyFile := "Lib/difflib.py", pyFns := ["SequenceMatcher.get_matching_blocks", "SequenceMatcher.find_longest_match", "SequenceMatcher.__chain_b"]
    statement := "For any lawful elements and any isjunk, the blocks are real matches under __eq__, in order in both sequences, do not touch, and end with the sentinel."
    source := "docstring of get_matching_blocks", status := .proven
    prop := ``BlocksLawO, thm := some ``blocksLawO_proven },
  { id := "textlibs-difflib-opcodes", pyFile := "Lib/difflib.py", pyFns := ["SequenceMatcher.get_opcodes"]
    statement := "For any lawful elements and any isjunk, the opcodes run from 0 to the ends of both sequences with no gap, and each tag means what it says."
    source := "docstring of get_opcodes", status := .proven
    prop := ``OpcodesLawO, thm := some ``opcodesLawO_proven },
  { id := "textlibs-difflib-grouped", pyFile := "Lib/difflib.py", pyFns := ["SequenceMatcher.get_grouped_opcodes"]
    statement := "On a new matcher over lawful elements, every change is in a group, in order, and no equal in a group exceeds 2n."
    source := "docstring of get_grouped_opcodes", status := .proven
    prop := ``GroupedLawO, thm := some ``groupedLawO_proven },
  { id := "textlibs-difflib-grouped-cache", pyFile := "Lib/difflib.py", pyFns := ["SequenceMatcher.get_grouped_opcodes", "SequenceMatcher.get_opcodes"]
    statement := "get_grouped_opcodes does not change what get_opcodes returns."
    source := "docstring of get_opcodes", status := .refuted
    prop := ``GroupedKeepsOpcodes, thm := some ``groupedKeepsOpcodes_refuted
    bug := some "textlibs-difflib-grouped-opcodes-mutates-cache" },
  { id := "textlibs-difflib-ratio-bound", pyFile := "Lib/difflib.py", pyFns := ["SequenceMatcher.ratio", "SequenceMatcher.real_quick_ratio"]
    statement := "For lawful elements, the matches of ratio number at most the shorter length, which real_quick_ratio uses."
    source := "docstring of real_quick_ratio", status := .proven
    prop := ``RatioBoundO, thm := some ``ratioBoundO_proven
    notes := "Counts of matches, not the float, which the difftest compares." },
  { id := "textlibs-difflib-quick-bound", pyFile := "Lib/difflib.py", pyFns := ["SequenceMatcher.quick_ratio"]
    statement := "For lawful elements, the matches of quick_ratio are at least those of ratio."
    source := "docstring of quick_ratio", status := .proven
    prop := ``QuickBoundO, thm := some ``quickBoundO_proven
    notes := "Counts of matches, not the float, which the difftest compares." },
  { id := "textlibs-difflib-set-seqs", pyFile := "Lib/difflib.py", pyFns := ["SequenceMatcher.__init__", "SequenceMatcher.set_seqs", "SequenceMatcher.set_seq1", "SequenceMatcher.set_seq2"]
    statement := "For any elements at all, set_seqs with new objects leaves what __init__ would on those sequences, or raises what it would."
    source := "the implementation disagreeing with itself", status := .proven
    prop := ``SetSeqsFreshO, thm := some ``setSeqsFreshO_proven },
  { id := "textlibs-difflib-chain-hash-fail", pyFile := "Lib/difflib.py", pyFns := ["SequenceMatcher.__chain_b", "SequenceMatcher.set_seq2"]
    statement := "When __hash__ of an element of b raises after lawful elements, the exception comes out, and b is set, the caches cleared, bjunk and bpopular the old ones, and b2j has exactly the indices before it."
    source := "Lib/difflib.py:278-283: b2j is assigned before its loop", status := .proven
    prop := ``ChainHashFail, thm := some ``chainHashFail_proven },
  { id := "textlibs-difflib-longest-eq-fail", pyFile := "Lib/difflib.py", pyFns := ["SequenceMatcher.find_longest_match"]
    statement := "What == raises in the first extension loop comes out of find_longest_match."
    source := "invariant: failures pass through", status := .proven
    prop := ``LongestEqFail, thm := some ``longestEqFail_proven },
  { id := "textlibs-difflib-longest-hash-fail", pyFile := "Lib/difflib.py", pyFns := ["SequenceMatcher.find_longest_match"]
    statement := "The first element of the box in a whose __hash__ raises decides the exception of find_longest_match, whatever follows it."
    source := "invariant: failures pass through, in order", status := .proven
    prop := ``LongestHashFail, thm := some ``longestHashFail_proven },
  { id := "textlibs-difflib-get-opcodes-empty-cache", pyFile := "Lib/difflib.py", pyFns := ["SequenceMatcher.get_opcodes"]
    statement := "A second get_opcodes after one that raised raises the same exception."
    source := "the docstring of get_opcodes, and get_matching_blocks, which does", status := .refuted
    prop := ``OpcodesFailAgain, thm := some ``opcodesFailAgain_refuted
    bug := some "textlibs-difflib-get-opcodes-empty-cache"
    notes := "self.opcodes = answer = [] runs ahead of get_matching_blocks, so the second call returns []." },
  { id := "textlibs-difflib-restore", pyFile := "Lib/difflib.py"
    pyFns := ["restore", "ndiff", "Differ.compare", "Differ._dump", "Differ._plain_replace", "Differ._fancy_replace", "Differ._fancy_helper", "Differ._qformat"]
    statement := "restore(ndiff(a, b), 1) == a and restore(ndiff(a, b), 2) == b, for all lists of str and any linejunk and charjunk, when ndiff runs to its end."
    source := "docstring of restore", status := .proven
    prop := ``RestoreRoundTrip, thm := some ``restoreRoundTrip_proven
    notes := "Holds whatever synch pair _fancy_replace picks, so the ratios and the cutoff are checked by the difftest, on exact doubles, not by this theorem." },
  { id := "textlibs-difflib-detects", pyFile := "Lib/difflib.py", pyFns := ["unified_diff", "context_diff"]
    statement := "unified_diff and context_diff yield something for any two different lists of str, for every n."
    source := "docstrings of unified_diff and context_diff", status := .proven
    prop := ``DiffDetects, thm := some ``diffDetects_proven },
  { id := "textlibs-difflib-same-lines", pyFile := "Lib/difflib.py", pyFns := []
    statement := "unified_diff yields nothing for two equal lists of str, popular lines included."
    source := "docstring of unified_diff", status := .open
    prop := ``SameLinesNoDiff
    notes := "Holds on CPython. A proof has to show that every box on the diagonal keeps to it, which FindLongestDocO does not give when lines are popular." },
  { id := "textlibs-difflib-twins-refuse", pyFile := "Lib/difflib.py", pyFns := ["unified_diff", "context_diff", "_check_types"]
    statement := "unified_diff raises whenever context_diff raises."
    source := "the comment in _check_types, and the twin", status := .refuted
    prop := ``DiffTwinsRefuse, thm := some ``diffTwinsRefuse_refuted
    bug := some "textlibs-difflib-unified-diff-nonstr-lines"
    notes := "A bytes line after a str first line. The f-strings of 3.15 format it, and '- ' + line raises." },
  { id := "textlibs-difflib-is-line-junk", pyFile := "Lib/difflib.py", pyFns := ["IS_LINE_JUNK"]
    statement := "IS_LINE_JUNK(line) with no pat holds exactly when, white space aside, the line is empty or a single '#'."
    source := "docstring of IS_LINE_JUNK", status := .proven
    prop := ``IsLineJunkDoc, thm := some ``isLineJunkDoc_proven },
  { id := "textlibs-difflib-hunk-sides", pyFile := "Lib/difflib.py", pyFns := ["unified_diff"]
    statement := "Each hunk of unified_diff, for any two lists of str and any n: its context and removed lines are a[i1:i2], and its context and added lines b[j1:j2], from the first and last opcodes of the group."
    source := "docstring of unified_diff: a diff is a patch", status := .proven
    prop := ``HunkSides, thm := some ``hunkSides_proven
    notes := "With textlibs-difflib-grouped, no change is left out of a hunk. The range text of the @@ line is checked by the difftest." },
  { id := "textlibs-difflib-context-sides", pyFile := "Lib/difflib.py", pyFns := ["context_diff"]
    statement := "The two sides of a hunk of context_diff, without their prefixes, are the slices of a and b the group covers."
    source := "docstring of context_diff", status := .proven
    prop := ``ContextSides, thm := some ``contextSides_proven },
  { id := "textlibs-etree-slice-store-list", pyFile := "Modules/_elementtree.c"
    pyFns := ["element_ass_subscr"]
    statement := "e[s] = xs, for a list or tuple xs of Elements and every slice with int/None parts, leaves the children l[s] = xs leaves in a list and raises what it raises."
    source := "the implementation disagreeing with itself (the pure-Python twin stores through list)", status := .refuted
    prop := ``Etree.SetSliceCIsList, thm := some ``Etree.setSliceCIsList_refuted
    bug := some "textlibs-etree-slice-backward-dup"
    notes := "e[5:2] = [X] on a0..a6 gives a0 a1 a2 a2 a3 X a5 a6: a2 sits in two slots with one reference, a4 is dropped." },
  { id := "textlibs-etree-slice-store-forward", pyFile := "Modules/_elementtree.c"
    pyFns := ["element_ass_subscr"]
    statement := "The same holds for every slice that is not a backward step-1 slice: the resize, the shift loops, the replace loop and the extended-slice size check agree with list_ass_subscript."
    source := "narrows textlibs-etree-slice-store-list", status := .proven
    prop := ``Etree.SetSliceCForwardIsList, thm := some ``Etree.setSliceCForwardIsList_proven },
  { id := "textlibs-etree-slice-del", pyFile := "Modules/_elementtree.c"
    pyFns := ["element_ass_subscr", "Element.__delitem__"]
    statement := "del e[s] leaves the same children and raises the same exception in the C accelerator and the Python twin, for every slice with int/None parts, step 1 included."
    source := "the implementation disagreeing with itself (C and Python twins)", status := .proven
    prop := ``Etree.DelSliceCIsList, thm := some ``Etree.delSliceCIsList_proven
    notes := "C runs the extended-slice compaction loop for step 1 as well; with step 1 every num_moved is 0." },
  { id := "textlibs-etree-item-twins", pyFile := "Modules/_elementtree.c"
    pyFns := ["element_subscr", "element_getitem", "element_ass_subscr", "element_setitem",
      "Element.__getitem__", "Element.__setitem__", "Element.__delitem__"]
    statement := "e[i], del e[i] and e[i] = x for an Element x give the same value or children and the same exception class in both twins, for every int i."
    source := "the implementation disagreeing with itself (C and Python twins)", status := .proven
    prop := ``Etree.ItemTwins, thm := some ``Etree.itemTwins_proven
    notes := "Messages differ: C says 'child index out of range', the twin 'list index out of range'." },
  { id := "textlibs-etree-item-store-order", pyFile := "Lib/xml/etree/ElementTree.py"
    pyFns := ["Element.__setitem__", "Element._assert_is_element", "element_ass_subscr", "element_setitem"]
    statement := "e[i] = x raises the same exception class in both twins for every int i and every object x."
    source := "the implementation disagreeing with itself (C and Python twins)", status := .refuted
    prop := ``Etree.ItemStoreTwins, thm := some ``Etree.itemStoreTwins_refuted
    bug := some "textlibs-etree-py-twin-setitem"
    notes := "C checks the index before the type, the twin the type before the index." },
  { id := "textlibs-etree-slice-read-twins", pyFile := "Modules/_elementtree.c"
    pyFns := ["element_subscr", "Element.__getitem__"]
    statement := "e[s] gives the same children or the same exception in both twins for every slice with int/None parts."
    source := "the implementation disagreeing with itself (C and Python twins)", status := .proven
    prop := ``Etree.GetSliceTwins, thm := some ``Etree.getSliceTwins_proven },
  { id := "textlibs-etree-slice-store-twins", pyFile := "Lib/xml/etree/ElementTree.py"
    pyFns := ["Element.__setitem__", "element_ass_subscr"]
    statement := "e[s] = value leaves the same children in both twins for every slice and every iterable value."
    source := "the implementation disagreeing with itself (C and Python twins)", status := .refuted
    prop := ``Etree.SetSliceTwins, thm := some ``Etree.setSliceTwins_refuted
    bug := some "textlibs-etree-py-twin-setitem"
    notes := "The twin's type-check loop exhausts a generator before list.__setitem__ iterates it again, so nothing is inserted." },
  { id := "textlibs-etree-slice-store-twins-seq", pyFile := "Lib/xml/etree/ElementTree.py"
    pyFns := ["Element.__setitem__", "element_ass_subscr"]
    statement := "For a list or tuple of Elements and a slice that is not a backward step-1 slice, both twins leave the same children and raise the same exception."
    source := "narrows textlibs-etree-slice-store-twins", status := .proven
    prop := ``Etree.SetSliceTwinsSeq, thm := some ``Etree.setSliceTwinsSeq_proven },
  { id := "textlibs-elementpath-no-keyerror", pyFile := "Lib/xml/etree/ElementPath.py"
    pyFns := ["iterfind", "xpath_tokenizer"]
    statement := "For every str path and namespaces dict, iterfind returns an iterator or raises SyntaxError."
    source := "invariant: no internal error leaking; ElementPath rejects other invalid paths with SyntaxError", status := .refuted
    prop := ``Etree.ElementPathNoKeyError, thm := some ``Etree.elementPathNoKeyError_refuted
    bug := some "textlibs-etree-elementpath-errors"
    notes := "findall(')') raises KeyError: ')' from the ops table; so does any step starting with (, ), (), ::, :, @, =, != or a quoted string." },
  { id := "textlibs-elementpath-no-none-step", pyFile := "Lib/xml/etree/ElementPath.py"
    pyFns := ["iterfind", "xpath_tokenizer", "prepare_child", "prepare_predicate"]
    statement := "No path leaves None in the compiled selector list."
    source := "invariant: no internal error leaking", status := .refuted
    prop := ``Etree.ElementPathNoNoneStep, thm := some ``Etree.elementPathNoNoneStep_refuted
    bug := some "textlibs-etree-elementpath-errors"
    notes := "a[ : prepare_predicate returns None at :236 and iterfind calls it, TypeError: 'NoneType' object is not callable; the broken selector list is cached." },
  { id := "textlibs-elementpath-iterable", pyFile := "Lib/xml/etree/ElementPath.py"
    pyFns := ["iterfind"]
    statement := "iterfind returns an iterator for every path it does not reject."
    source := "docs: Element.iterfind 'Returns an iterable yielding all matching elements in document order'", status := .refuted
    prop := ``Etree.ElementPathIterable, thm := some ``Etree.elementPathIterable_refuted
    bug := some "textlibs-etree-elementpath-errors"
    notes := "iterfind is a plain function; its bare return at :387 gives None for a path with no tokens ('', '!')." },
  { id := "textlibs-elementpath-plain-tag-twins", pyFile := "Lib/xml/etree/ElementPath.py"
    pyFns := ["iterfind", "xpath_tokenizer", "prepare_child", "_is_wildcard_tag", "find", "findall", "findtext"]
    statement := "For every tree and every nonempty tag name of characters other than whitespace and /[]()@!=.*:{}'\", findall, find and findtext without namespaces give the same result through the C fast path and through ElementPath."
    source := "the implementation disagreeing with itself (C fast path against ElementPath)", status := .proven
    prop := ``Etree.PlainTagTwins, thm := some ``Etree.plainTagTwins_proven },
  { id := "textlibs-etree-find-fast-path", pyFile := "Modules/_elementtree.c"
    pyFns := ["checkpath", "_elementtree_Element_find_impl", "_elementtree_Element_findtext_impl",
      "_elementtree_Element_findall_impl"]
    statement := "The same theorem, from the C side: checkpath is false on such names and the fast path's children scan equals the compiled child step."
    source := "the implementation disagreeing with itself (C fast path against ElementPath)", status := .proven
    prop := ``Etree.PlainTagTwins, thm := some ``Etree.plainTagTwins_proven
    notes := "Outside plain names the two routes differ: 'a:b', 'a b' and '(a)' match a literal tag in C and raise or match nothing in ElementPath." },
  { id := "textlibs-etree-writers-twins", pyFile := "Modules/_elementtree.c"
    pyFns := ["_elementtree_Element_append_impl", "_elementtree_Element_extend_impl",
      "_elementtree_Element_insert_impl", "element_add_subelement"]
    statement := "For Element arguments, append and insert leave the same children and raise the same exception in C and in the Python twin for every int index, and extend of a list or tuple leaves the same children and raises the same exception class."
    source := "the implementation disagreeing with itself (C and Python twins)", status := .proven
    prop := ``Etree.WritersTwins, thm := some ``Etree.writersTwins_proven
    notes := "insert's clamp and shift loop are proven equal to list.insert's ins1Pos and insAt." },
  { id := "textlibs-etree-writers-twins-py", pyFile := "Lib/xml/etree/ElementTree.py"
    pyFns := ["Element.append", "Element.extend", "Element.insert"]
    statement := "The same theorem, credited to the Python twin's methods."
    source := "the implementation disagreeing with itself (C and Python twins)", status := .proven
    prop := ``Etree.WritersTwins, thm := some ``Etree.writersTwins_proven },
  { id := "textlibs-etree-writers-refuse", pyFile := "Lib/xml/etree/ElementTree.py"
    pyFns := ["Element.append", "Element.insert", "Element._assert_is_element"]
    statement := "append(x) and insert(i, x) with x not an Element raise TypeError and leave the children unchanged, in both twins, for every index that fits Py_ssize_t; the messages are Clinic's and _assert_is_element's."
    source := "_assert_is_element, ElementTree.py:248-252; Clinic's subclass_of check on Element.append/insert", status := .proven
    prop := ``Etree.WritersRefuse, thm := some ``Etree.writersRefuse_proven
    notes := "Smoke-tested on 3.15.2: append(5), insert(0, 5), insert(-7, 'x'), append(Element) in both twins." },
  { id := "textlibs-etree-extend-iter-twins", pyFile := "Modules/_elementtree.c"
    pyFns := ["_elementtree_Element_extend_impl", "Element.extend"]
    statement := "extend leaves the same children in both twins for every iterable."
    source := "the implementation disagreeing with itself (C and Python twins)", status := .refuted
    prop := ``Etree.ExtendTwins, thm := some ``Etree.extendTwins_refuted
    bug := some "textlibs-etree-py-twin-setitem"
    notes := "An iterator that yields two Elements and raises: C materialises it first and appends nothing, the twin has appended both." },
  { id := "textlibs-etree-attrib-no-bad-call", pyFile := "Modules/_elementtree.c"
    pyFns := ["_elementtree_Element_get_impl", "_elementtree_Element_set_impl", "_elementtree_Element_keys_impl",
      "_elementtree_Element_items_impl", "element_get_attrib"]
    statement := "While the attrib slot holds NULL, a dict or a frozendict, Element.get, set, keys and items never raise SystemError."
    source := "invariant: no internal error leaking", status := .proven
    prop := ``Etree.NoBadCall, thm := some ``Etree.noBadCall_proven },
  { id := "textlibs-etree-attrib-invariant", pyFile := "Modules/_elementtree.c"
    pyFns := ["element_attrib_setter", "element_attrib_getter"]
    statement := "Element(tag, attrib), the attrib setter and getter, and set keep the attrib slot NULL, a dict or a frozendict."
    source := "invariant: 3.15's setter and Element() refuse other objects", status := .proven
    prop := ``Etree.AttribInvariant, thm := some ``Etree.attribInvariant_proven
    notes := "element_init is not credited: its keyword-attribute path (get_attrib_from_keywords) is not modelled." },
  { id := "textlibs-etree-copy-shallow", pyFile := "Modules/_elementtree.c"
    pyFns := ["_elementtree_Element___copy___impl", "Element.__copy__", "Element.makeelement"]
    statement := "copy.copy of an element, in either twin, has the original's tag, text, tail and children (the same elements, in order) and shows the original's attributes; the Python twin's copy keeps the class."
    source := "copy module docs: a shallow copy; ElementTree.py:189-194; _elementtree.c:763-797", status := .proven
    prop := ``Etree.CopyShallow, thm := some ``Etree.copyShallow_proven
    notes := "Smoke-tested on 3.15.2: 5k elements per twin, subclasses included. That the C copy shares the attrib dict and drops the class is refuted separately (textlibs-etree-copy-shares-attrib)." },
  { id := "textlibs-etree-fast-path-sound", pyFile := "Modules/_elementtree.c"
    pyFns := ["checkpath", "_elementtree_Element_findall_impl"]
    statement := "Whenever checkpath finds no XPath character, the C fast path of findall gives what ElementPath (the Python twin) gives."
    source := "the implementation disagreeing with itself (C fast path against the twin)", status := .refuted
    prop := ``Etree.FastPathSound, thm := some ``Etree.fastPathSound_refuted
    bug := some "textlibs-etree-elementpath-errors"
    notes := "Counterexample findall('a(b)'): C finds the child, Python raises KeyError. Tags are str in the model; checkpath's bytes and other-type branches are not modelled." },
  { id := "textlibs-etree-attrib-dict", pyFile := "Modules/_elementtree.c"
    pyFns := ["element_get_attrib", "_elementtree_Element_get_impl", "_elementtree_Element_set_impl",
      "_elementtree_Element_keys_impl", "_elementtree_Element_items_impl", "element_attrib_getter",
      "element_attrib_setter"]
    statement := "For str keys and values on an element whose attrib is NULL, a dict or a frozendict: after a successful set(k, v), get(k) is v, get of another key is unchanged, and keys()/items() list the attributes with k set to v in insertion order; set succeeds unless the attrib is a frozendict, where it raises TypeError and changes nothing; the attrib getter returns the stored object and a second call returns the same; items() lists what the getter returns; the setter stores exactly the dict or frozendict it is given."
    source := "docs: Element.get/set/keys/items and attrib; dict semantics", status := .proven
    prop := ``Etree.AttribDict, thm := some ``Etree.attribDict_proven
    notes := "Smoke-tested on 3.15.2 with 20k random elements, frozendict attribs included. Keys are str: a key whose __hash__ or __eq__ raises is out of scope." },
  { id := "textlibs-etree-setstate-attrib", pyFile := "Modules/_elementtree.c"
    pyFns := ["_elementtree_Element___setstate___impl", "element_setstate_from_Python",
      "element_setstate_from_attributes"]
    statement := "Element.__setstate__ keeps the attrib slot NULL, a dict or a frozendict."
    source := "invariant: the setter and Element() enforce it", status := .refuted
    prop := ``Etree.SetstateKeepsAttrib, thm := some ``Etree.setstateKeepsAttrib_refuted
    bug := some "textlibs-etree-setstate-attrib-systemerror" },
  { id := "textlibs-etree-setstate-entry", pyFile := "Modules/_elementtree.c"
    pyFns := ["_elementtree_Element___setstate___impl"]
    statement := "Element.__setstate__ of anything but an exact dict raises TypeError and leaves the element unchanged; a dict holding only tag and attrib stores that attrib."
    source := "_elementtree.c:1176-1188; the pickle protocol", status := .proven
    prop := ``Etree.SetstateEntry, thm := some ``Etree.setstateEntry_proven },
  { id := "textlibs-etree-remove-twins", pyFile := "Modules/_elementtree.c"
    pyFns := ["_elementtree_Element_remove_impl"]
    statement := "For every child __eq__, however it raises or changes the children in place, Element.remove of an Element leaves the same children and raises the same exception class in C and in the Python twin (list.remove)."
    source := "the implementation disagreeing with itself (C and Python twins)", status := .proven
    prop := ``Etree.RemoveTwins, thm := some ``Etree.removeTwins_proven
    notes := "C's post-loop check (extra NULL or i >= length) does what list_ass_slice's clipping does in list.remove. clear() inside __eq__ is out of scope: the twin rebinds _children." },
  { id := "textlibs-etree-remove-twins-py", pyFile := "Lib/xml/etree/ElementTree.py"
    pyFns := ["Element.remove"]
    statement := "The same theorem, credited to the Python twin's remove, which turns every ValueError (one raised by __eq__ included) into ValueError('x not in self')."
    source := "the implementation disagreeing with itself (C and Python twins)", status := .proven
    prop := ``Etree.RemoveTwins, thm := some ``Etree.removeTwins_proven },
  { id := "textlibs-etree-remove-twins-all", pyFile := "Lib/xml/etree/ElementTree.py"
    pyFns := ["Element.remove", "_elementtree_Element_remove_impl"]
    statement := "Element.remove leaves the same children in both twins for every argument, Element or not."
    source := "the implementation disagreeing with itself (C and Python twins)", status := .refuted
    prop := ``Etree.RemoveTwinsAll, thm := some ``Etree.removeTwinsAll_refuted
    bug := some "textlibs-etree-py-twin-setitem"
    notes := "e.remove(5) with a child whose __eq__ is true: C's Clinic refuses 5, the twin's list.remove removes the child before its iselement check runs." },
  { id := "textlibs-etree-copy-independent", pyFile := "Modules/_elementtree.c"
    pyFns := ["_elementtree_Element___copy___impl", "create_new_element"]
    statement := "Setting an attribute on copy.copy(e) leaves e's attributes unchanged."
    source := "the implementation disagreeing with itself (the Python twin's __copy__ makes a new dict)", status := .refuted
    prop := ``Etree.CopyIndependentC, thm := some ``Etree.copyIndependentC_refuted
    bug := some "textlibs-etree-copy-shares-attrib" },
  { id := "textlibs-etree-copy-class", pyFile := "Modules/_elementtree.c"
    pyFns := ["_elementtree_Element___copy___impl", "create_new_element"]
    statement := "copy.copy(e) has e's class."
    source := "the implementation disagreeing with itself (the Python twin uses self.__class__)", status := .refuted
    prop := ``Etree.CopyKeepsClassC, thm := some ``Etree.copyKeepsClassC_refuted
    bug := some "textlibs-etree-copy-shares-attrib" },
  { id := "textlibs-etree-copy-independent-py", pyFile := "Lib/xml/etree/ElementTree.py"
    pyFns := ["Element.__copy__", "Element.makeelement"]
    statement := "In the twin, setting an attribute on copy.copy(e) leaves e's attributes unchanged, and the copy has e's class."
    source := "docs: copy.copy makes a new object", status := .proven
    prop := ``Etree.CopyIndependentPy, thm := some ``Etree.copyIndependentPy_proven
    notes := "The class half is CopyKeepsClassPy, proven by rfl from makeelement's self.__class__." },
  { id := "textlibs-zoneinfo-before-twins", pyFile := "Lib/zoneinfo/_zoneinfo.py", pyFns := []
    statement := "For every TZif type table and transition list (indices validated), C and Python pick the same local-time type before the first transition."
    source := "the implementation disagreeing with itself (C and Python twins)", status := .refuted
    prop := ``Zoneinfo.BeforeTwins, thm := some ``Zoneinfo.beforeTwins_refuted
    bug := some "textlibs-zoneinfo-before-first-transition"
    notes := "Models only the ttinfo_before block of ZoneInfo._load_file and its C twin in load_data (Modules/_zoneinfo.c:1170-1182); credits no row." },
  { id := "textlibs-zoneinfo-before-twins-narrow", pyFile := "Lib/zoneinfo/_zoneinfo.py", pyFns := []
    statement := "They agree when some type is not DST or the first transition names type 0."
    source := "narrows textlibs-zoneinfo-before-twins", status := .proven
    prop := ``Zoneinfo.BeforeTwinsNarrow, thm := some ``Zoneinfo.beforeTwinsNarrow_proven },
  { id := "textlibs-simplequeue-get-twins", pyFile := "Modules/_queuemodule.c", pyFns := []
    statement := "On a non-empty SimpleQueue, whenever the Python twin's get returns the waiting item, so does C's."
    source := "the implementation disagreeing with itself (C and Python twins)", status := .refuted
    prop := ``SQ.GetTwins, thm := some ``SQ.getTwins_refuted
    bug := some "textlibs-simplequeue-get-timeout"
    notes := "Models the non-empty path only (no waiting), so it credits no row." },
  { id := "textlibs-simplequeue-get-tiny-negative", pyFile := "Modules/_queuemodule.c", pyFns := []
    statement := "On a non-empty SimpleQueue, C and the twin give the same result for every finite blocking timeout."
    source := "the implementation disagreeing with itself (C and Python twins)", status := .refuted
    prop := ``SQ.GetTwinsTinyNegative, thm := some ``SQ.getTwinsTinyNegative_refuted
    bug := some "textlibs-simplequeue-get-timeout" },
  { id := "textlibs-simplequeue-get-finite", pyFile := "Modules/_queuemodule.c", pyFns := []
    statement := "They agree for None and for finite timeouts within PyTime_t that are non-negative or at most -1 ns."
    source := "narrows textlibs-simplequeue-get-tiny-negative", status := .proven
    prop := ``SQ.GetTwinsFinite, thm := some ``SQ.getTwinsFinite_proven },
  { id := "textlibs-urllib-quote-from-bytes-paths", pyFile := "Lib/urllib/parse.py"
    pyFns := ["quote_from_bytes", "_byte_quoter_factory", "_Quoter.__init__", "_Quoter.__missing__"]
    statement := "For every bytes or bytearray and every str or bytes safe, quote_from_bytes's three paths (all bytes safe: bs.decode(); below 200,000 bytes; chunks of isqrt(len)) all return each byte as itself when it is always safe or in safe's ASCII part, and as %XX otherwise; any other first argument raises TypeError."
    source := "the implementation disagreeing with itself (fast, plain and chunked paths); quote's docstring", status := .proven
    prop := ``Url.QuoteFromBytesPaths, thm := some ``Url.quoteFromBytesPaths_proven
    notes := "_byte_quoter_factory's lru_cache and the _Quoter dict only memoize __missing__, so quoteByte stands for _Quoter(safe).__getitem__." },
  { id := "textlibs-urllib-quote-bytes-round-trip", pyFile := "Lib/urllib/parse.py"
    pyFns := ["quote_from_bytes", "unquote_to_bytes", "_unquote_impl"]
    statement := "unquote_to_bytes(quote_from_bytes(b, safe)) == b for every bytes b and every safe without '%'."
    source := "round trip; docstrings of quote_from_bytes and unquote_to_bytes", status := .proven
    prop := ``Url.QuoteBytesRoundTrip, thm := some ``Url.quoteBytesRoundTrip_proven
    notes := "unquote_to_bytes gets a str, so it runs the UTF-8 encode and the split on b'%'; _unquote_impl is shown equal to a left-to-right scan (joinBits_split)." },
  { id := "textlibs-urllib-quote-round-trip", pyFile := "Lib/urllib/parse.py"
    pyFns := ["quote", "unquote", "_generate_unquoted_parts", "_unquote_impl"]
    statement := "For every str the encoding (None, utf-8, ascii, latin-1) can write, every str or bytes safe and all error handlers, quote %-escapes exactly the bytes of s.encode(encoding) that are neither always safe nor in safe, and when safe has no '%', unquote(quote(s, safe, encoding, errors), encoding, errors2) == s."
    source := "round trip; docstrings of quote and unquote", status := .proven
    prop := ``Url.QuoteStrRoundTrip, thm := some ``Url.quoteStrRoundTrip_proven
    notes := "Uses the UTF-8, ASCII and Latin-1 codecs of PyLean.UnicodeObj; namereplace is out of scope for ascii/latin-1." },
  { id := "textlibs-urllib-quote-plus-round-trip", pyFile := "Lib/urllib/parse.py"
    pyFns := ["quote_plus", "unquote_plus"]
    statement := "For every str the encoding can write, every safe and all error handlers, quote_plus is quote(s, safe) without spaces and quote(s, safe + ' ') with spaces turned to '+', and when safe has neither '%' nor '+', unquote_plus(quote_plus(s, ...), encoding, errors2) == s."
    source := "round trip; docstrings of quote_plus and unquote_plus", status := .proven
    prop := ``Url.QuotePlusRoundTrip, thm := some ``Url.quotePlusRoundTrip_proven },
  { id := "textlibs-urllib-qsl-round-trip", pyFile := "Lib/urllib/parse.py"
    pyFns := ["urlencode", "parse_qsl"]
    statement := "parse_qsl(urlencode(pairs), keep_blank_values=True) == pairs for every list of str pairs without surrogates (as 2-tuples or as a mapping), and for every list of bytes pairs read back from urlencode(pairs).encode('ascii')."
    source := "round trip; docs of urlencode and parse_qsl", status := .proven
    prop := ``Url.QslRoundTrip, thm := some ``Url.qslRoundTrip_proven },
  { id := "textlibs-urllib-split-round-trip", pyFile := "Lib/urllib/parse.py"
    pyFns := ["urlsplit", "_urlsplit", "_splitnetloc", "urlunsplit", "_urlunsplit", "_SplitResultBase.geturl",
      "_coerce_args", "_noop"]
    statement := "For every str URL accepted by urlsplit(url, missing_as_none=True), urlunsplit of the result (keep_empty unspecified or true) and geturl() give back the URL with leading C0/space stripped, tab/CR/LF removed and the scheme lower-cased; the scheme is None only when the URL does not start with an RFC 3986 scheme and ':'; the netloc has no '/', '?', '#', the path no '?', '#', the query no '#'."
    source := "docs of urlunsplit (keep_empty 'allows rebuilding a URL that was parsed with option missing_as_none=True') and urlsplit", status := .proven
    prop := ``Url.SplitRoundTrip, thm := some ``Url.splitRoundTrip_proven
    notes := "allow_fragments=True; the general statement is refuted by textlibs-urllib-split-round-trip-all. unicodedata.normalize and ipaddress.ip_address are quantified oracles." },
  { id := "textlibs-urllib-split-round-trip-all", pyFile := "Lib/urllib/parse.py"
    pyFns := ["urlsplit", "_urlsplit", "_splitnetloc", "urlunsplit", "_urlunsplit", "_SplitResultBase.geturl"]
    statement := "The round trip of textlibs-urllib-split-round-trip holds for every value of allow_fragments."
    source := "docs of urlunsplit (keep_empty) and SplitResult.geturl", status := .refuted
    prop := ``Url.SplitRoundTripAll, thm := some ``Url.splitRoundTripAll_refuted
    bug := some "textlibs-urllib-nofrag-slash"
    notes := "urlsplit('http://h#x', allow_fragments=False) has path '#x' after the netloc, and _urlunsplit inserts '/'." },
  { id := "textlibs-urllib-parse-round-trip", pyFile := "Lib/urllib/parse.py"
    pyFns := ["urlparse", "_urlparse", "_splitparams", "urlunparse", "_ParseResultBase.geturl"]
    statement := "For every str URL accepted by urlparse(url, missing_as_none=True), urlunparse of the result and geturl() give back the URL normalized as for urlsplit, and urlparse's fields are urlsplit's with the path split into path and params."
    source := "docs of urlunparse (keep_empty) and urlparse ('similar to urlsplit(), but additionally splits the path component on path and params')", status := .proven
    prop := ``Url.ParseRoundTrip, thm := some ``Url.parseRoundTrip_proven },
  { id := "textlibs-urllib-defrag-round-trip", pyFile := "Lib/urllib/parse.py"
    pyFns := ["urldefrag", "_DefragResultBase.geturl"]
    statement := "For every str URL accepted by urldefrag(url, missing_as_none=True): without '#' it returns (url, None) and geturl() is url; with '#' the url part has no '#', the fragment is a string, and geturl() is the URL normalized as for urlsplit."
    source := "docs of urldefrag and geturl()", status := .proven
    prop := ``Url.DefragRoundTrip, thm := some ``Url.defragRoundTrip_proven },
  { id := "textlibs-urllib-bracketed-host", pyFile := "Lib/urllib/parse.py"
    pyFns := ["_check_bracketed_netloc", "_check_bracketed_host", "_NetlocResultMixinStr._hostinfo"]
    statement := "Whenever urlsplit (any allow_fragments, any missing_as_none) accepts a str URL whose netloc contains '[', the hostname _hostinfo reads from it passes _check_bracketed_host: an IPv6 address (per ip_address) or an IPvFuture literal."
    source := "the implementation disagreeing with itself: comment at Lib/urllib/parse.py:528-529, the check must mirror _hostinfo", status := .proven
    prop := ``Url.BracketedHostValid, thm := some ``Url.bracketedHostValid_proven },
  { id := "textlibs-urllib-userinfo-brackets", pyFile := "Lib/urllib/parse.py"
    pyFns := ["_check_bracketed_netloc", "_check_bracketed_host"]
    statement := "urlsplit accepts every URL whose ASCII netloc has matched '[' ']' only in the userinfo, before the last '@'."
    source := "comment at Lib/urllib/parse.py:528-529; python/cpython#105704 and #77523", status := .refuted
    prop := ``Url.BracketsOnlyInUserinfo, thm := some ``Url.bracketsOnlyInUserinfo_refuted
    bug := some "textlibs-urllib-userinfo-brackets"
    notes := "Duplicate of the open #77523; refuted with the oracle ip_address('example.com') raising, as CPython does." },
  { id := "textlibs-urllib-netloc-twin", pyFile := "Lib/urllib/parse.py"
    pyFns := ["_NetlocResultMixinBytes._userinfo", "_NetlocResultMixinBytes._hostinfo", "_NetlocResultMixinStr._userinfo",
      "_NetlocResultMixinStr._hostinfo", "_NetlocResultMixinBase.username", "_NetlocResultMixinBase.password",
      "_NetlocResultMixinBase.hostname"]
    statement := "For every netloc that is a bytes value (code points below 256) or None, the bytes result classes (splitting bytes with b'@', b':', b'[', b']') give the same username, password and port as the str classes, and for an ASCII netloc the same hostname (bytes.lower() against str.lower())."
    source := "the implementation disagreeing with itself: the twin mixins at Lib/urllib/parse.py:212-277", status := .proven
    prop := ``Url.NetlocTwin, thm := some ``Url.netlocTwin_proven
    notes := "The bytes mixin is modelled on List UInt8 with its own partition/rpartition (UrlModel.bpart, brpart); the twin needs the injectivity of the byte conversion." },
  { id := "textlibs-urllib-netloc-attrs", pyFile := "Lib/urllib/parse.py"
    pyFns := ["_NetlocResultMixinStr._userinfo", "_NetlocResultMixinStr._hostinfo", "_NetlocResultMixinBase.username",
      "_NetlocResultMixinBase.password", "_NetlocResultMixinBase.hostname"]
    statement := "For every str result and netloc: username/password come from the text before the last '@' (cut at its first ':', None without '@' or ':'); _hostinfo reads the text after the last '@' (host before the first ':', or between the first '[' and the next ']', port after the ':' that follows, empty port None); hostname is None for an empty host and otherwise lower-cases the part before the first '%' and keeps the zone."
    source := "docs of urlsplit (username, password, hostname attributes; the zone comment at Lib/urllib/parse.py:191-192); RFC 3986 section 3.2", status := .proven
    prop := ``Url.NetlocAttrSpec, thm := some ``Url.netlocAttrSpec_proven },
  { id := "textlibs-urllib-port", pyFile := "Lib/urllib/parse.py"
    pyFns := ["_NetlocResultMixinBase.port"]
    statement := "For every str or bytes result (a bytes netloc below 256): a port is in 0-65535, every error is ValueError, a netloc host:digits (no '@', '[', ':' in the host, at most 4300 ASCII digits) gives int(digits) or the range error, and a netloc without '@', '[', ':' has no port."
    source := "docs of urlsplit ('Port number as integer, if present'; invalid port raises ValueError)", status := .proven
    prop := ``Url.PortSpec, thm := some ``Url.portSpec_proven },
  { id := "textlibs-urllib-bytes-twin", pyFile := "Lib/urllib/parse.py"
    pyFns := ["_decode_args", "_encode_result", "_ResultMixinStr.encode", "_ResultMixinBytes.decode"]
    statement := "For every ASCII bytes URL, every allow_fragments and missing_as_none, urlsplit(b) == urlsplit(b.decode()).encode('ascii') (errors included, _keep_empty kept), and urlsplit(b).decode('ascii') == urlsplit(b.decode())."
    source := "the implementation disagreeing with itself (bytes path against str path); docs 'Parsing ASCII Encoded Bytes'", status := .proven
    prop := ``Url.BytesTwin, thm := some ``Url.bytesTwin_proven },
  { id := "textlibs-urllib-nfkc-check", pyFile := "Lib/urllib/parse.py"
    pyFns := ["_checknetloc"]
    statement := "For every URL whose netloc has no brackets and every NFKC oracle, urlsplit accepts it exactly when the netloc is ASCII, or its NFKC form without '@:#?' is unchanged or contains none of '/?#@:'."
    source := "docs of urlsplit (characters that decompose under NFKC into / ? # @ : raise ValueError)", status := .proven
    prop := ``Url.NfkcCheck, thm := some ``Url.nfkcCheck_proven
    notes := "unicodedata.normalize('NFKC', _) is the quantified oracle nfkc." },
  { id := "textlibs-urllib-legacy-split", pyFile := "Lib/urllib/parse.py"
    pyFns := ["_splituser", "_splitpasswd", "_splitquery", "_splittag", "_splitvalue", "_splitattr", "_splitport",
      "_splitnport"]
    statement := "For every str, _splituser/_splitquery/_splittag cut at the last '@'/'?'/'#', _splitpasswd/_splitvalue at the first ':'/'=', _splitattr at every ';', losing nothing; _splitport cuts at the last ':' exactly when only ASCII digits follow (None for none) and otherwise returns (host, None); _splitnport returns (host, defport) without ':' or with an empty port, (host, int(port)) for ASCII digits (ValueError beyond the 4300-digit int limit), and (host, None) otherwise."
    source := "docstrings of the helpers (e.g. splituser('user[:passwd]@host[:port]') --> 'user[:passwd]', 'host[:port]'; _splitnport's three return rules); docs of the int/str digit limit", status := .proven
    prop := ``Url.LegacySplit, thm := some ``Url.legacySplit_proven },
  { id := "textlibs-urllib-type-host-split", pyFile := "Lib/urllib/parse.py"
    pyFns := ["_splittype", "_splithost"]
    statement := "For every str: _splittype returns the lower-cased text before the first ':' when it is non-empty and has no '/', and (None, url) otherwise; _splithost returns, for a URL starting '//', the text up to the next '/', '#' or '?' and the rest (with '/' put before a rest starting '#' or '?'), and (None, url) otherwise."
    source := "docstrings (splittype('type:opaquestring') --> 'type', 'opaquestring'; splithost('//host[:port]/path') --> 'host[:port]', '/path') and the regular expressions at Lib/urllib/parse.py:1248, :1269", status := .proven
    prop := ``Url.TypeHostSplit, thm := some ``Url.typeHostSplit_proven },
  { id := "textlibs-urllib-quote-spec", pyFile := "Lib/urllib/parse.py"
    pyFns := ["quote", "quote_plus", "quote_from_bytes", "_Quoter.__init__", "_Quoter.__missing__", "_byte_quoter_factory"]
    statement := "For every bytes/bytearray and str-or-bytes safe, quote_from_bytes (all three paths), quote and quote_plus write a byte as itself when it is one of the 66 always-safe characters or in safe's ASCII part, and otherwise as '%' and two upper-case hex digits; quote_plus on bytes adds b' ' to safe and turns spaces into '+'; quote on bytes refuses encoding, then errors, with TypeError; on a non-empty str, a character the encoding cannot write raises UnicodeEncodeError under errors None/'strict', and errors='ignore' drops it for ascii/latin-1."
    source := "docstrings of quote, quote_plus, quote_from_bytes; RFC 3986 section 2.1 (uppercase hex digits)", status := .proven
    prop := ``Url.QuoteSpec, thm := some ``Url.quoteSpec_proven
    notes := "_ALWAYS_SAFE and the hex digits are written out as literals (UrlSpecQuote.alwaysSafeSet, hexUpper); _byte_quoter_factory's lru_cache and the _Quoter dict only memoize __missing__." },
  { id := "textlibs-urllib-unquote-spec", pyFile := "Lib/urllib/parse.py"
    pyFns := ["unquote", "unquote_to_bytes", "_unquote_impl", "_generate_unquoted_parts"]
    statement := "For every input, %XX escapes are read left to right (a '%' without two hex digits kept literally); unquote on an ASCII str is the input without '%' and otherwise the scanned bytes decoded with encoding/errors; a non-ASCII character is kept between the unquoted text on its two sides; unquote on bytes decodes the scanned bytes and refuses encoding=None; unquote_to_bytes scans bytes and the UTF-8 of a str, raises UnicodeEncodeError on a lone surrogate, AttributeError on None, and TypeError on a bytearray with '%'."
    source := "docstrings of unquote and unquote_to_bytes; docs of unquote; the comment at Lib/urllib/parse.py:796-797", status := .proven
    prop := ``Url.UnquoteSpec, thm := some ``Url.unquoteSpec_proven },
  { id := "textlibs-urllib-brackets", pyFile := "Lib/urllib/parse.py"
    pyFns := ["_check_bracketed_netloc", "_check_bracketed_host"]
    statement := "_check_bracketed_host accepts exactly an IPvFuture literal per the regex of :548 (starting v/V) or an IPv6 address per ip_address (otherwise), and raises 'IPvFuture address is invalid', 'An IPv4 address cannot be in brackets' or ip_address's error; _check_bracketed_netloc accepts exactly a host part after the last '@' that starts with '[' when it has one, has only a ':' port after the ']', and holds an accepted host, and raises 'Invalid IPv6 URL' for data before '[' or between ']' and ':'."
    source := "comments at Lib/urllib/parse.py:528-529, :544-545 (RFC 3986 IP-literal); docs of urlsplit (invalid IPv6/IPvFuture brackets raise ValueError)", status := .proven
    prop := ``Url.BracketSpec, thm := some ``Url.bracketSpec_proven
    notes := "ipaddress.ip_address is the quantified oracle ipk." },
  { id := "textlibs-urllib-splitparams", pyFile := "Lib/urllib/parse.py"
    pyFns := ["_splitparams"]
    statement := "For every path and both values of missing_as_none, _splitparams cuts at the first ';' after the last '/' (None or '' without one), at the first ';' when there is no '/', and returns url[:-1], url with neither."
    source := "docs of urlparse (parameters of the last path element); RFC 2396 section 3.3", status := .proven
    prop := ``Url.SplitparamsSpec, thm := some ``Url.splitparamsSpec_proven },
  { id := "textlibs-urllib-split-spec", pyFile := "Lib/urllib/parse.py"
    pyFns := ["urlsplit", "_urlsplit", "urlparse", "_urlparse", "urldefrag"]
    statement := "For every str URL, scheme default (None or str), allow_fragments and missing_as_none: urlsplit, urlparse and (for a URL with '#') urldefrag succeed exactly when the netloc is accepted (no netloc, or both brackets or neither, an accepted bracketed host, not the NFKC rejection) and then return their documented fields (scheme lower-cased or the stripped default, params split for uses_params schemes, '' for missing parts unless missing_as_none); one kind of bracket raises 'Invalid IPv6 URL' and every other refusal is the failing check's ValueError; urldefrag returns (url, None or '') without '#'."
    source := "docs of urlsplit (ValueError for invalid brackets and NFKC netlocs; scheme default; missing_as_none), urlparse and urldefrag", status := .proven
    prop := ``Url.UrlsplitSpec, thm := some ``Url.urlsplitSpec_proven
    notes := "unicodedata.normalize and ipaddress.ip_address are quantified oracles; the bracket and NFKC checks are pinned by textlibs-urllib-brackets and textlibs-urllib-nfkc-check." },
  { id := "textlibs-urllib-unsplit-spec", pyFile := "Lib/urllib/parse.py"
    pyFns := ["urlunsplit", "urlunparse", "_urlunsplit"]
    statement := "For every str components and every keep_empty and _keep_empty: keep_empty=True on a missing_as_none=False result raises 'Cannot distinguish ...'; a true keep_empty joins every non-None component, a false one first drops false components (keeping '' as netloc for uses_netloc schemes with an empty or '/'-path); _urlunsplit writes 'scheme:', '//netloc' with '/' before a relative path, '//' before a '//'-path without netloc, '?query', '#fragment', and urlsplit reads '////p' back as netloc '' and path '//p'."
    source := "docstrings of urlunsplit and urlunparse; docs of keep_empty; RFC 3986 section 3.3", status := .proven
    prop := ``Url.UnsplitSpec, thm := some ``Url.unsplitSpec_proven },
  { id := "textlibs-urllib-defrag-geturl", pyFile := "Lib/urllib/parse.py"
    pyFns := ["_DefragResultBase.geturl"]
    statement := "For every DefragResult or DefragResultBytes and every _keep_empty, geturl() is url + '#' + fragment when the fragment is non-empty, or empty and not None with _keep_empty true, and url otherwise."
    source := "docs of DefragResult.geturl() and urldefrag", status := .proven
    prop := ``Url.DefragGeturlSpec, thm := some ``Url.defragGeturlSpec_proven },
  { id := "textlibs-urllib-coerce", pyFile := "Lib/urllib/parse.py"
    pyFns := ["_coerce_args", "_decode_args"]
    statement := "For every argument list, _coerce_args raises TypeError('Cannot mix str and non-str arguments') when a true str and a true non-str are present; otherwise returns str arguments unchanged, or decodes bytes arguments with ASCII (UnicodeDecodeError for a byte from 128); through urlsplit, non-ASCII bytes raise UnicodeDecodeError and a str URL with a bytes scheme raises the TypeError."
    source := "docs ('Attempting to mix str data with bytes or bytearray ... will raise TypeError, while ... non-ASCII byte values will trigger UnicodeDecodeError')", status := .proven
    prop := ``Url.CoerceSpec, thm := some ``Url.coerceSpec_proven },
  { id := "textlibs-urllib-result-codec", pyFile := "Lib/urllib/parse.py"
    pyFns := ["_ResultMixinStr.encode", "_ResultMixinBytes.decode"]
    statement := "For every result and codec (utf-8, ascii, latin-1): when the codec can write every field, encode (any handler) encodes each non-None field and copies _keep_empty, and decode with the same codec (any handler) gives the result back; encode(errors='strict') raises UnicodeEncodeError on a character the codec cannot write; decode('ascii') raises UnicodeDecodeError on a byte from 128."
    source := "docs of the result objects' encode() and decode(); round trip", status := .proven
    prop := ``Url.ResCodecSpec, thm := some ``Url.resCodecSpec_proven },
  { id := "textlibs-urllib-qsl-spec", pyFile := "Lib/urllib/parse.py"
    pyFns := ["parse_qsl"]
    statement := "For every query and option of parse_qsl: a separator that is not a non-empty str or bytes raises ValueError; None gives []; max_num_fields below the field count raises 'Max number of fields exceeded' and otherwise changes nothing; with a one-character separator fields compose (a + sep + b), and one field gives the unquoted name/value around its first '=' (dropped when the value is empty without keep_blank_values), or without '=' raises ValueError under strict_parsing, gives (field, '') under keep_blank_values, and is dropped otherwise."
    source := "docstring of parse_qsl (keep_blank_values, strict_parsing, max_num_fields, separator)", status := .proven
    prop := ``Url.QslSpec, thm := some ``Url.qslSpec_proven },
  { id := "textlibs-urllib-urlencode-spec", pyFile := "Lib/urllib/parse.py"
    pyFns := ["urlencode"]
    statement := "For every query and option of urlencode: an object without len and a sequence whose first element is not a tuple raise TypeError('not a valid non-string sequence or mapping object'); a mapping encodes as its items; keys and values go through quote_via (quote_plus or quote), bytes without encoding/errors, other objects as str(v); without doseq pairs give quote_via(k) + '=' + quote_via(v) joined by '&'; with doseq the result is that of the pairs expanded one per element (a key whose value is an empty sequence is still quoted, and its error raised)."
    source := "docstring of urlencode (doseq; 'encoding and errors only if a component is a str')", status := .proven
    prop := ``Url.UrlencodeSpec, thm := some ``Url.urlencodeSpec_proven },
  { id := "textlibs-urllib-parse-bytes-twin", pyFile := "Lib/urllib/parse.py"
    pyFns := ["urlparse", "urldefrag"]
    statement := "For every ASCII bytes URL, every allow_fragments and missing_as_none, urlparse and urldefrag on it give what they give on the decoded str as a bytes result (same fields, _keep_empty kept), errors included."
    source := "the implementation disagreeing with itself (bytes path against str path); docs 'Parsing ASCII Encoded Bytes'", status := .proven
    prop := ``Url.ParseBytesTwin, thm := some ``Url.parseBytesTwin_proven },
  { id := "textlibs-toml-decode-error-coords", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["TOMLDecodeError.__init__"]
    statement := "TOMLDecodeError(msg, doc, pos) with str msg and doc and int pos: for 0 <= pos <= len(doc), lineno and colno are the 1-based line and column of pos (counted from the last newline before pos) and str(e) is 'msg (at line L, column C)' or 'msg (at end of document)' when pos == len(doc); for every int pos it does not raise; any other call warns (DeprecationWarning, raised when warnings are errors) and passes the non-default arguments in order to ValueError.__init__."
    source := "docs of TOMLDecodeError (lineno: 'The line corresponding to pos', colno: 'The column corresponding to pos'; free-form arguments deprecated)", status := .proven
    prop := ``Toml.TdeCoords, thm := some ``Toml.tdeCoords_proven },
  { id := "textlibs-toml-basic-str", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["parse_value", "parse_one_line_basic_str", "parse_basic_str", "parse_basic_str_escape",
      "parse_hex_char", "is_unicode_scalar_value"]
    statement := "For every list of characters each written as itself (not '\"', '\\' or a control character other than tab) or with any escape TOML 1.1 allows for it (\\b \\t \\n \\f \\r \\e \\\" \\\\, \\xHH below 256, \\uHHHH and \\UHHHHHHHH for Unicode scalar values, either case), parse_value on the quoted text, with at least six frames left below it, returns that str and the position after the closing quote; a \\u or \\U escape of a surrogate or of a value above U+10FFFF raises TOMLDecodeError 'Escaped character is not a Unicode scalar value'; a raw control character other than tab raises 'Illegal character'."
    source := "docs ('parsing TOML 1.1.0'); TOML 1.1 spec, String", status := .proven
    prop := ``Toml.BasicStrRoundTrip, thm := some ``Toml.basicStrRoundTrip_proven },
  { id := "textlibs-toml-literal-str", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["parse_value", "parse_literal_str", "skip_until"]
    statement := "For every str without \"'\" and without control characters other than tab, parse_value on its single-quoted form (with at least three frames left below it) returns it unchanged; a control character other than tab before the closing quote raises TOMLDecodeError 'Found invalid character' at that character; with no closing quote it raises 'Expected \"'\"' at the end of the document."
    source := "docs ('parsing TOML 1.1.0'); TOML 1.1 spec, literal strings", status := .proven
    prop := ``Toml.LiteralStrSpec, thm := some ``Toml.literalStrSpec_proven }
,
  { id := "textlibs-toml-keys", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["parse_key", "parse_key_part", "skip_chars", "parse_one_line_basic_str", "parse_literal_str"]
    statement := "For every dotted key whose parts are each bare (non-empty, A-Za-z0-9_-), literal or basic (any escapes), with spaces or tabs around the dots and after it, and followed by text that does not continue it, parse_key returns the tuple of parts and the position after the trailing whitespace when the key has at most MAX_KEY_PARTS parts or only one, and raises RecursionError 'TOML key has more than the allowed N parts' otherwise."
    source := "docs ('parsing TOML 1.1.0'); TOML 1.1 spec, Keys; comment at _parser.py:32-36 on MAX_KEY_PARTS", status := .proven
    prop := ``Toml.KeySpec, thm := some ``Toml.keySpec_proven
    notes := "A one-part key is never checked against MAX_KEY_PARTS (the check is in the loop), so MAX_KEY_PARTS = 0 still accepts 'a = 1'." }
,
  { id := "textlibs-toml-numbers", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["parse_value", "make_safe_parse_float", "match_to_number"]
    statement := "For every number token TOML 1.1 allows (decimal integer without leading zero, 0x/0o/0b integer with leading zeros and either case, float with fraction and/or exponent, inf/nan with optional sign; single underscores between digits), followed by nothing, whitespace, a newline, ',', ']', '}' or '#', parse_value, with the frames match_to_number and parse_float need left below it, returns the position after it and: a decimal integer's signed value, or int()'s ValueError when it has more digits (not counting underscores) than sys.get_int_max_str_digits() allows; a prefixed integer's value with no limit; for floats, what parse_float returns when called with exactly the token's text, its exception, or ValueError 'parse_float must not return dicts or lists' when it returns a dict or list and is not float."
    source := "docs of load/loads (parse_float 'will be called with the string of every TOML float'; 'must not return a dict or a list, else a ValueError is raised'; Integers: int max str digits); TOML 1.1 spec, Integer and Float", status := .proven
    prop := ``Toml.NumberSpec, thm := some ``Toml.numberSpec_proven
    notes := "RE_NUMBER, RE_DATETIME and RE_LOCALTIME are hand-written matchers; the theorem shows the date patterns never match a number token. parse_float is modelled as a function of its argument." }
,
  { id := "textlibs-toml-datetimes", pyFile := "Lib/tomllib/_re.py"
    pyFns := ["match_to_datetime", "cached_tz", "match_to_localtime"]
    statement := "For every YYYY-MM-DD (month 01-12, day 01-31), optionally followed by T, t or a space, HH:MM with optional :SS and optional fraction, and an optional Z/z or +-HH:MM offset, followed by what may end a value, parse_value (with at least two frames left below it) returns datetime.date, or datetime.datetime with seconds defaulting to 0, microseconds the first six fraction digits (truncated, zero-padded) and tzinfo None, UTC or the signed offset, when the date exists (year >= 1, day within the month), and raises TOMLDecodeError 'Invalid date or datetime' at the token otherwise; every HH:MM[:SS[.frac]] local time gives the corresponding datetime.time."
    source := "docs conversion table (offset/local date-time, local date, local time); TOML 1.1 spec, Offset Date-Time ('additional precision must be truncated, not rounded'), seconds optional in 1.1", status := .proven
    prop := ``Toml.DatetimeSpec, thm := some ``Toml.datetimeSpec_proven
    notes := "Also exercises parse_value's date branches. datetime.date/datetime/time and timezone are modelled by their range checks; lru_cache of cached_tz only memoizes, and timezone(timedelta(0)) is timezone.utc, so an offset is a number of minutes." }
,
  { id := "textlibs-toml-table-rules", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["loads", "create_dict_rule", "create_list_rule", "Flags.__init__", "Flags.set", "Flags.is_",
      "Flags.unset_all", "NestedDict.__init__", "NestedDict.get_or_create_nest", "NestedDict.append_nest_to_list",
      "Output.__init__"]
    statement := "For every dotted header key K (bare, literal or basic parts, at most MAX_KEY_PARTS - 1 of them), bare key x and at least ten frames left when loads is called: loads('[K]\\n[K]') raises TOMLDecodeError 'Cannot declare K twice'; loads('[[K]]\\n[[K]]') gives K = [{}, {}]; loads('[K]\\n[[K]]') raises 'Cannot overwrite a value'; loads('[[K]]\\n[K]') raises 'Cannot declare K twice'; loads('[K.x]\\n[K]') gives K = {x = {}}; loads('[[K]]\\n[K.x]\\n[[K]]\\n[K.x]') gives K = [{x = {}}, {x = {}}]; each error at the position after the second key."
    source := "docs ('parsing TOML 1.1.0'); TOML 1.1 spec, Table ('you cannot define a table more than once', super-tables after sub-tables are valid) and Array of Tables", status := .proven
    prop := ``Toml.TableRules, thm := some ``Toml.tableRules_proven
    notes := "The last document needs unset_all (the old element's flags are dropped) and get_or_create_nest's walk into the last element of a list. Pending flags, recursive flags and the errors of the rules are in the entries below." }
,
  { id := "textlibs-toml-load", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["load"]
    statement := "For every text of Unicode scalar values, load() of a binary file holding its UTF-8 encoding equals loads() of the text called one frame deeper (and raises RecursionError with no frame left); bytes that are not valid UTF-8 raise the decoder's UnicodeDecodeError; a file opened in text mode (read() returns str) and an AttributeError from a decode() method both raise TypeError 'File must be opened in binary mode, ...'; an exception from fp.read() propagates."
    source := "docs of load ('The first argument should be a readable and binary file object'); load against loads", status := .proven
    prop := ``Toml.LoadSpec, thm := some ``Toml.loadSpec_proven
    notes := "Uses the UTF-8 decoder of PyLean.UnicodeObj and its round trip (utf8RoundTrip_proven)." }
,
  { id := "textlibs-toml-arrays-inline-tables", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["parse_array", "parse_inline_table", "skip_comment", "skip_comments_and_array_ws",
      "parse_key_value_pair", "parse_value"]
    statement := "For every value built from basic strings and booleans by arrays and inline tables (distinct one-part keys, bare, literal or basic; spaces or tabs around '='), with any whitespace, newlines and comments after '[' or '{', around each ',' and before ']' or '}', and an optional trailing comma, parse_value (with the fuel loads gives it) returns the nested lists and dicts in order and the position after the value, when at least 3 * depth + 10 frames are left below it (each array level takes two frames, each inline table three)."
    source := "docs ('parsing TOML 1.1.0'; What's New: newlines and trailing commas in inline tables); TOML 1.1 spec, Array and Inline Table", status := .proven
    prop := ``Toml.ArrayTableSpec, thm := some ``Toml.arrayTableSpec_proven
    notes := "skip_comments_and_array_ws is shown to skip exactly a run of whitespace, newlines and comments (skipCaw_fill); inline tables run Flags.is_, Flags.set and get_or_create_nest(access_lists=False) on their local state." }
,
  { id := "textlibs-toml-document", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["loads", "key_value_rule", "parse_key_value_pair"]
    statement := "For every document of 'key = value' lines joined by newlines (one-part keys written bare, literal or basic, all distinct; spaces or tabs around '='; values built from basic strings and booleans by arrays and inline tables, with comments and newlines inside them), loads, called with at least four frames left and 3 * depth + 14 for every value, returns the dict of the pairs in insertion order."
    source := "docs ('parsing TOML 1.1.0'; Tables/dicts: 'loads dictionary entries in the order they appear'); TOML 1.1 spec, Key/Value Pair", status := .proven
    prop := ``Toml.DocRoundTrip, thm := some ``Toml.docRoundTrip_proven }
,
  { id := "textlibs-toml-multiline-basic", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["parse_multiline_str", "parse_basic_str_escape_multiline", "parse_basic_str", "parse_basic_str_escape"]
    statement := "For every list of pieces of a multi-line basic string (characters written raw, newlines included, or with any escape basic strings allow; line-ending backslashes, which drop the newline and the whitespace after them; one or two raw quotes followed by another piece), optionally preceded by a newline right after the opening triple quote (trimmed) and followed by up to two quotes before the closing triple quote (kept), parse_value, with at least six frames left below it, returns the text and the position after the closing quotes."
    source := "docs ('parsing TOML 1.1.0'); TOML 1.1 spec, multi-line basic strings ('A newline immediately following the opening delimiter will be trimmed', line ending backslash, 1 or 2 quotes next to the delimiters)", status := .proven
    prop := ``Toml.MultilineBasicSpec, thm := some ``Toml.multilineBasicSpec_proven
    notes := "The literal branch of parse_multiline_str (triple apostrophes) is textlibs-toml-multiline-literal." }
,
  { id := "textlibs-toml-dotted-then-header", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["Flags.add_pending", "Flags.finalize_pending", "key_value_rule"]
    statement := "For every dotted key K (bare, literal or basic parts, at most MAX_KEY_PARTS - 1 of them), bare key x and at least twelve frames left, loads('K.x=true\\n[K]') raises TOMLDecodeError 'Cannot declare K twice' at the position after the header's key: the tables a dotted key defines are recorded as pending and become explicit at the next header."
    source := "TOML 1.1 spec, Table ('Since tables cannot be defined more than once, redefining such tables using a [table] header is not allowed'); comment at _parser.py:427-429", status := .proven
    prop := ``Toml.DottedThenHeader, thm := some ``Toml.dottedThenHeader_proven }
,
  -- Lib/email/_header_value_parser.py: TextLibs/EmailBase.lean (tree, str, value),
  -- EmailLex.lean, EmailAddr.lean, EmailMime.lean, EmailHeaders.lean (the get_*/parse_*
  -- parsers, with _ew.decode as a parameter); properties in EmailUnstruct.lean, EmailRefute.lean.
  { id := "textlibs-email-unstructured", pyFile := "Lib/email/_header_value_parser.py"
    pyFns := ["get_unstructured", "get_fws", "TokenList.__str__", "TokenList.value",
      "WhiteSpaceTerminal.value", "ValueTerminal.value"]
    statement := "For every header value, get_unstructured returns (never raises, never loops: at most one iteration per character) whatever _ew.decode returns, if it raises only ValueError or KeyError; and when _ew.decode rejects every encoded word, str() of the result is the value and .value is the value with each run of whitespace that starts with a space or tab (plus the str.isspace characters after it) replaced by one space."
    source := "module docstring (:35-49: whitespace tokens have value ' ', str() does not collapse whitespace runs); comment at :1182-1187 (the =? split must not loop); invariant: no exception", status := .proven
    prop := ``PyLean.TextLibs.Email.UnstructuredSpec, thm := some ``PyLean.TextLibs.Email.unstructuredSpec_proven
    notes := "_ew.decode (Lib/email/_encoded_words.py) is a parameter. The termination part needs the regex rfc2047_matcher (hand-written as rfcSearch): a word starting with =? that it matches has a ?= after the =?, so get_encoded_word did not raise its plain HeaderParseError there. Encoded words that decode are not covered by the str/value part." }
,
  { id := "textlibs-email-msgid-no-fold-literal-space", pyFile := "Lib/email/_header_value_parser.py"
    pyFns := ["parse_message_id", "get_msg_id", "get_no_fold_literal", "_get_ptext_to_endchars"]
    statement := "For every header value, parse_message_id returns a token list and raises nothing (it turns the HeaderParseError of get_msg_id into a defect)."
    source := "Lib/email/headerregistry.py:169-174 ('The parser should not, insofar as practical, raise any errors'); :2182-2189", status := .refuted
    prop := ``PyLean.TextLibs.Email.MessageIdNoRaise, thm := some ``PyLean.TextLibs.Email.messageIdNoRaise_refuted
    bug := some "textlibs-email-msgid-no-fold-literal-space"
    notes := "'<a@[ x]>': get_no_fold_literal calls get_dtext on ' x]>', and _get_ptext_to_endchars reads the unbound pos for a value starting with a space (messageId_unbound). The gh-134152 fix covered only the empty value." }
,
  { id := "textlibs-email-msgids-no-fold-literal-space", pyFile := "Lib/email/_header_value_parser.py"
    pyFns := ["parse_message_ids"]
    statement := "For every header value, parse_message_ids returns a token list and raises nothing (it turns the HeaderParseError of get_msg_id into a defect and keeps the rest as an InvalidMessageID)."
    source := "Lib/email/headerregistry.py:169-174; :2213-2221", status := .refuted
    prop := ``PyLean.TextLibs.Email.MessageIdsNoRaise, thm := some ``PyLean.TextLibs.Email.messageIdsNoRaise_refuted
    bug := some "textlibs-email-msgid-no-fold-literal-space"
    notes := "The same '<a@[ x]>' raises UnboundLocalError from parse_message_ids (References, In-Reply-To)." }
,
  { id := "textlibs-email-param-extended-marker-at-end", pyFile := "Lib/email/_header_value_parser.py"
    pyFns := ["parse_content_type_header", "parse_mime_parameters", "get_parameter"]
    statement := "For every header value, parse_content_type_header returns a token list and raises nothing (parse_mime_parameters keeps an unparsable parameter as an invalid one)."
    source := "Lib/email/headerregistry.py:169-174; :2650-2671", status := .refuted
    prop := ``PyLean.TextLibs.Email.ContentHeadersNoRaise, thm := some ``PyLean.TextLibs.Email.contentHeadersNoRaise_refuted
    bug := some "textlibs-email-param-extended-marker-at-end"
    notes := "'text/plain; a*' raises IndexError at :2525 (contentType_star). Duplicate of python/cpython#151857 (open)." }
,
  { id := "textlibs-email-disposition-extended-marker-at-end", pyFile := "Lib/email/_header_value_parser.py"
    pyFns := ["parse_content_disposition_header"]
    statement := "For every header value, parse_content_disposition_header returns a token list and raises nothing."
    source := "Lib/email/headerregistry.py:169-174; :2785-2786 (parameters go to parse_mime_parameters)", status := .refuted
    prop := ``PyLean.TextLibs.Email.ContentDispositionNoRaise, thm := some ``PyLean.TextLibs.Email.contentDispositionNoRaise_refuted
    bug := some "textlibs-email-param-extended-marker-at-end"
    notes := "'attachment; filename*' raises IndexError at :2525 (contentDisposition_star). Duplicate of python/cpython#151857 (open)." }
,
  { id := "textlibs-email-section-nondecimal-digit", pyFile := "Lib/email/_header_value_parser.py"
    pyFns := ["get_section"]
    statement := "For every value, get_section returns a Section or raises HeaderParseError, the only exception get_parameter catches around it."
    source := "invariant: the caller's try/except at :2513-2518", status := .refuted
    prop := ``PyLean.TextLibs.Email.SectionOnlyHpe, thm := some ``PyLean.TextLibs.Email.sectionOnlyHpe_refuted
    bug := some "textlibs-email-section-nondecimal-digit"
    notes := "'*²': isdigit() accepts '²' and int() rejects it (section_superscript; contentType_superscript shows the ValueError leaving parse_content_type_header). int() is modelled for str.isdigit strings with the max-str-digits limit (pyInt). Duplicate of python/cpython#87112 (open)." }
,
  { id := "textlibs-email-mime-version-nondecimal-digit", pyFile := "Lib/email/_header_value_parser.py"
    pyFns := ["parse_mime_version"]
    statement := "For every header value, parse_mime_version returns a MIMEVersion token list and raises nothing (non-numbers become defects)."
    source := "Lib/email/headerregistry.py:169-174; the defect branches at :2253-2256, :2284-2287", status := .refuted
    prop := ``PyLean.TextLibs.Email.MimeVersionNoRaise, thm := some ``PyLean.TextLibs.Email.mimeVersionNoRaise_refuted
    bug := some "textlibs-email-mime-version-nondecimal-digit"
    notes := "'²' raises ValueError from int() (mimeVersion_superscript). Duplicate of python/cpython#158708 (closed in a batch, not on the merits)." }
,
  { id := "textlibs-email-display-name-only-cfws", pyFile := "Lib/email/_header_value_parser.py"
    pyFns := ["DisplayName.display_name"]
    statement := "For every value get_display_name parses, display_name of the resulting DisplayName is a string (raises nothing)."
    source := "Lib/email/headerregistry.py:169-174 and :343-347 (address headers read display_name of every group and mailbox)", status := .refuted
    prop := ``PyLean.TextLibs.Email.DisplayNameTotal, thm := some ``PyLean.TextLibs.Email.displayNameTotal_refuted
    bug := some "textlibs-email-display-name-only-cfws"
    notes := "'(c)': the phrase is one CFWS token; display_name pops it and reads res[-1] of an empty list (displayName_comment). Duplicate of python/cpython#151857 (open)." }
,
  { id := "textlibs-email-display-name-value-only-cfws", pyFile := "Lib/email/_header_value_parser.py"
    pyFns := ["DisplayName.value"]
    statement := "For every value get_display_name parses, value of the resulting DisplayName is a string (raises nothing)."
    source := "Lib/email/headerregistry.py:169-174; DisplayName.value :604-624", status := .refuted
    prop := ``PyLean.TextLibs.Email.DisplayNameValueTotal, thm := some ``PyLean.TextLibs.Email.displayNameValueTotal_refuted
    bug := some "textlibs-email-display-name-only-cfws"
    notes := "'(c)': the phrase has a defect, so value takes the quoting branch and calls display_name, which raises IndexError." }
,
  { id := "textlibs-email-quoted-string-reparse", pyFile := "Lib/email/_header_value_parser.py"
    pyFns := ["get_quoted_string", "get_bare_quoted_string", "BareQuotedString.__str__", "quote_string",
      "make_quoted_pairs"]
    statement := "For every value get_quoted_string parses (and every _ew.decode that raises only ValueError/KeyError), parsing str() of the result again gives a whole quoted string with the same value."
    source := "module docstring :46-49 (str() is 'a canonical representation of the RFC-compliant form ... including minimal use of quoted pair quoting')", status := .refuted
    prop := ``PyLean.TextLibs.Email.QuotedStringCanonical, thm := some ``PyLean.TextLibs.Email.quotedStringCanonical_refuted
    bug := some "textlibs-email-quoted-string-reparse"
    notes := "'\"\\\\=?utf-8?q?a?=\"' has value '=?utf-8?q?a?=' (the quoted pair hides the encoded word); str() drops the backslash and the reparse decodes it to 'a' (quotedString_reparse), with _ew.decode answering as CPython's does on that word." }
,
  { id := "textlibs-email-quoting-round-trip", pyFile := "Lib/email/_header_value_parser.py"
    pyFns := ["make_quoted_pairs", "make_parenthesis_pairs", "quote_string", "get_bare_quoted_string",
      "get_qcontent", "_get_ptext_to_endchars", "get_comment", "get_qp_ctext", "get_fws",
      "BareQuotedString.__str__", "BareQuotedString.value", "Comment.__str__", "Comment.quote",
      "Comment.content"]
    statement := "For every text s and rest r: get_bare_quoted_string(quote_string(s) + r) returns r and a bare quoted string whose value is s and whose str() is quote_string(s), when _ew.decode rejects every encoded word; get_comment('(' + make_parenthesis_pairs(s) + ')' + r) returns r and a comment whose content is s and whose str() is '(' + make_parenthesis_pairs(s) + ')'. Fuel above len(s) + 1 suffices."
    source := "docstrings of make_quoted_pairs and make_parenthesis_pairs (:100-108), _get_ptext_to_endchars (:1037-1043: quoted pairs are unquoted), get_bare_quoted_string (:1244-1250: whitespace preserved); module docstring :51-52 (Comment.content)", status := .proven
    prop := ``PyLean.TextLibs.Email.QuotingRoundTrip, thm := some ``PyLean.TextLibs.Email.quotingRoundTrip_proven
    notes := "s is any text, whitespace included (runs of spaces become fws tokens, the rest qcontent/ctext runs). With an encoded word that decodes, the quoted-string half fails: textlibs-email-quoted-string-reparse." }
,
  { id := "textlibs-email-ptext-had-qp", pyFile := "Lib/email/_header_value_parser.py"
    pyFns := ["_get_ptext_to_endchars"]
    statement := "Whenever _get_ptext_to_endchars returns fewer characters than it consumed (it dropped the backslash of a quoted pair), its had_qp flag is True."
    source := "docstring :1037-1043 ('a flag that is True iff there were any quoted printables decoded')", status := .refuted
    prop := ``PyLean.TextLibs.Email.PtextQpFlag, thm := some ``PyLean.TextLibs.Email.ptextQpFlag_refuted
    bug := some "textlibs-email-ptext-had-qp"
    notes := "'a\\b' gives ('ab', '', False) (ptext_qp_unset)." },
  { id := "textlibs-toml-nesting", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["parse_value", "parse_array", "skip_comments_and_array_ws", "parse_key_value_pair", "key_value_rule", "loads"]
    statement := "For every bare key x and every m, loads('x = ' + '[' * (m + 1) + ']' * (m + 1)), called with fr frames left (sys.getrecursionlimit() minus the frames on the stack), returns {x: m + 1 nested empty lists} exactly when 2m + 7 <= fr, and raises RecursionError('maximum recursion depth exceeded') otherwise: each array level takes two frames (parse_value, parse_array)."
    source := "docs of tomllib, 'Nesting limit' ('the nesting level is mainly limited by Python's recursion limit'); the recursion check of _Py_EnterRecursivePy", status := .proven
    prop := ``Toml.NestingDepthLimit, thm := some ``Toml.nestingDepthLimit_proven
    notes := "The model counts every Python frame (need in TomlModel.lean); the difftest sets the recursion limit per case and checks deep documents near the threshold. Call sites are taken as specialized (CALL_ALLOC_AND_ENTER_INIT)." },
  { id := "textlibs-toml-nesting-unbounded", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["parse_value", "parse_array"]
    statement := "With at least sixteen frames left (enough for every flat document of this shape), loads('x = ' + '[' * (m + 1) + ']' * (m + 1)) returns the nested lists for every m."
    source := "the unbounded reading of ArrayTableSpec, which the docs rule out", status := .refuted
    prop := ``Toml.NestingUnbounded, thm := some ``Toml.nestingUnbounded_refuted
    bug := some "textlibs-toml-nesting-recursion-limit"
    notes := "Documented limitation, not for filing: seventeen nested arrays with sixteen frames left raise RecursionError." },
  { id := "textlibs-toml-escape-errors", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["parse_basic_str_escape", "parse_hex_char", "skip_chars"]
    statement := "In both modes, '\\' followed by a character that is not an escape letter (nor, multi-line, a space, tab or newline) raises TOMLDecodeError 'Unescaped '\\' in a string' at pos + 2; '\\x', '\\u', '\\U' not followed by 2, 4, 8 hex digits raise 'Invalid hex value' at pos + 2; multi-line, '\\' then spaces or tabs then a character other than a newline raises 'Unescaped '\\' in a string' at that character, and spaces or tabs up to the end of the document end the escape there with nothing; a '\\' that is the last character raises 'Unescaped '\\' in a string' at pos + 2, one past the end."
    source := "TOML 1.1 spec, String ('All other escape sequences ... TOML should produce an error'; line ending backslash)", status := .proven
    prop := ``Toml.EscapeErrors, thm := some ``Toml.escapeErrors_proven },
  { id := "textlibs-toml-key-errors", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["parse_key_part", "parse_key_value_pair", "parse_key"]
    statement := "parse_key_part at the end of the document or at a character that cannot start a key raises TOMLDecodeError 'Invalid initial character for a key part' there; parse_key_value_pair on any dotted key KeySpec reads (at most MAX_KEY_PARTS parts) whose trailing whitespace is followed by anything but '=' (the end of the document included) raises 'Expected '=' after a key in a key/value pair' there, with at least eight frames left."
    source := "TOML 1.1 spec, Keys and Key/Value Pair", status := .proven
    prop := ``Toml.KeyErrors, thm := some ``Toml.keyErrors_proven },
  { id := "textlibs-toml-invalid-value", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["parse_value"]
    statement := "parse_value at the end of the document, or at a character that starts no value (not a digit, '\"', ''', '[', '{', '+', '-', 'i' or 'n'; 't' and 'f' when not followed by the rest of true or false), raises TOMLDecodeError 'Invalid value' there, with at least one frame left."
    source := "TOML 1.1 spec, Key/Value Pair ('Unspecified values are invalid')", status := .proven
    prop := ``Toml.InvalidValue, thm := some ``Toml.invalidValue_proven },
  { id := "textlibs-toml-unterminated-string", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["parse_basic_str", "parse_one_line_basic_str", "parse_value"]
    statement := "'\"' followed by characters and escapes TOML 1.1 allows up to the end of the document raises TOMLDecodeError 'Unterminated string' at the end, with at least six frames left below parse_value."
    source := "TOML 1.1 spec, String", status := .proven
    prop := ``Toml.UnterminatedString, thm := some ``Toml.unterminatedString_proven },
  { id := "textlibs-toml-pending-dotted", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["Flags.add_pending", "key_value_rule", "Flags.is_", "NestedDict.get_or_create_nest", "loads"]
    statement := "For all bare keys a, b != c and booleans X, Y, and at least sixteen frames left: loads('a.b=X\\na.c=Y') gives {a: {b: X, c: Y}} (the table a is only marked pending; marking it at once would make the second line raise 'Cannot redefine namespace')."
    source := "TOML 1.1 spec, Keys ('Dotted keys create and define a table for each key part before the last one'); comment at _parser.py:427-429", status := .proven
    prop := ``Toml.PendingDotted, thm := some ``Toml.pendingDotted_proven },
  { id := "textlibs-toml-unset-all-scope", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["Flags.unset_all", "create_list_rule", "create_dict_rule", "Flags.is_", "Flags.set", "NestedDict.append_nest_to_list"]
    statement := "For all bare keys a != b and at least ten frames left, loads('[a]\\n[[b]]\\n[a]') raises TOMLDecodeError 'Cannot declare ('a',) twice' after the last a: starting the array b drops only the flags under b."
    source := "TOML 1.1 spec, Table ('you cannot define a table more than once')", status := .proven
    prop := ``Toml.UnsetAllScope, thm := some ``Toml.unsetAllScope_proven },
  { id := "textlibs-toml-nested-aot", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["NestedDict.append_nest_to_list", "NestedDict.get_or_create_nest", "create_list_rule"]
    statement := "For all bare keys a, b and at least ten frames left, loads('[[a]]\\n[[a.b]]') gives {a: [{b: [{}]}]}: the sub-array goes into the last element of a."
    source := "TOML 1.1 spec, Array of Tables ('Any reference to an array of tables points to the most recently defined table element of the array')", status := .proven
    prop := ``Toml.NestedArrayTables, thm := some ``Toml.nestedArrayTables_proven },
  { id := "textlibs-toml-frozen", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["Flags.set", "Flags.is_", "create_dict_rule", "create_list_rule", "key_value_rule"]
    statement := "For all bare keys a, b, boolean X and at least eighteen frames left: loads('a={}\\n[a.b]') raises 'Cannot declare ('a', 'b') twice' (a's recursive FROZEN flag answers for a.b); loads('a=[]\\n[[a]]') raises 'Cannot mutate immutable namespace ('a',)'; loads('a={}\\na.b=X') raises 'Cannot mutate immutable namespace ('a',)'; each after the second key (after X for the last)."
    source := "TOML 1.1 spec, Inline Table ('fully self-contained'; 'Keys and sub-tables cannot be added outside the braces') and Array", status := .proven
    prop := ``Toml.FrozenRules, thm := some ``Toml.frozenRules_proven },
  { id := "textlibs-toml-overwrite", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["NestedDict.get_or_create_nest", "create_dict_rule", "key_value_rule"]
    statement := "For all bare keys a, b, booleans X, Y and at least sixteen frames left: loads('a=X\\n[a.b]') and loads('a=X\\n[a]') raise TOMLDecodeError 'Cannot overwrite a value' after the header's key (get_or_create_nest's KeyError: no table behind a); loads('a=X\\na=Y') raises it after Y."
    source := "TOML 1.1 spec, Keys ('Defining a key multiple times is invalid') and Table", status := .proven
    prop := ``Toml.OverwriteRules, thm := some ``Toml.overwriteRules_proven },
  { id := "textlibs-toml-header-relative", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["key_value_rule", "loads"]
    statement := "For all bare keys t, k, boolean X and at least sixteen frames left, loads('[t]\\nk=X') gives {t: {k: X}}."
    source := "TOML 1.1 spec, Table ('Under that, and until the next table or EOF are the key/values of that table')", status := .proven
    prop := ``Toml.HeaderRelative, thm := some ``Toml.headerRelative_proven },
  { id := "textlibs-toml-redefine-namespace", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["key_value_rule", "Flags.is_"]
    statement := "For all bare keys a, b, c, boolean X and at least sixteen frames left, loads('[a.b]\\n[a]\\nb.c=X') raises TOMLDecodeError 'Cannot redefine namespace ('a', 'b')' after X."
    source := "TOML 1.1 spec, Table ('using dotted keys to redefine tables already defined in [table] form is not allowed')", status := .proven
    prop := ``Toml.RedefineNamespace, thm := some ``Toml.redefineNamespace_proven },
  { id := "textlibs-toml-header-unclosed", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["create_dict_rule", "create_list_rule"]
    statement := "For every dotted key K (bare, literal or basic parts, at most MAX_KEY_PARTS) followed by text that does not continue it, and at least ten frames left: loads('[' + K + rest) raises 'Expected ']' at the end of a table declaration' after K when rest does not start with ']'; loads('[[' + K + rest) raises 'Expected ']]' at the end of an array declaration' after K when rest does not start with ']]'."
    source := "TOML 1.1 spec, Table and Array of Tables (header syntax)", status := .proven
    prop := ``Toml.HeaderUnclosed, thm := some ``Toml.headerUnclosed_proven },
  { id := "textlibs-toml-finalize-clears", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["Flags.finalize_pending", "Flags.add_pending", "Flags.unset_all", "create_list_rule", "create_dict_rule",
      "NestedDict.get_or_create_nest"]
    statement := "For all bare keys t, a, b, boolean X and at least sixteen frames left, loads('[[t]]\\na.b=X\\n[[t]]\\n[t.a]') gives {t: [{a: {b: X}}, {a: {}}]}: the second [[t]] turns the pending t.a into a flag, clears the pending set and drops the flags under t (without the clear, [t.a] would raise 'Cannot declare')."
    source := "TOML 1.1 spec, Array of Tables (each [[t]] starts a new table)", status := .proven
    prop := ``Toml.FinalizeClears, thm := some ``Toml.finalizeClears_proven },
  { id := "textlibs-toml-finalize-not-recursive", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["Flags.finalize_pending", "Flags.set", "Flags.is_", "create_dict_rule", "key_value_rule",
      "NestedDict.get_or_create_nest"]
    statement := "For all bare keys a, b, c, d, x with x != a, c != d, boolean X and at least sixteen frames left, loads('a.b.c=X\\n[x]\\n[a.b.d]') gives {a: {b: {c: X, d: {}}}, x: {}}: finalize_pending marks a and a.b one by one (recursive=False); marked recursively, [a.b.d] would raise 'Cannot declare'."
    source := "TOML 1.1 spec, Table (a dotted key defines its tables; an undefined sub-table may still be declared)", status := .proven
    prop := ``Toml.FinalizeNotRecursive, thm := some ``Toml.finalizeNotRecursive_proven },
  { id := "textlibs-toml-kv-rule-more", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["key_value_rule", "NestedDict.get_or_create_nest", "Flags.set", "Flags.is_"]
    statement := "For all bare keys t, a, b, booleans X, Y and at least eighteen frames left: loads('a=X\\na.b=Y') raises 'Cannot overwrite a value' after Y (get_or_create_nest's KeyError caught in key_value_rule); loads('[t]\\na={}\\na.b=Y') raises 'Cannot mutate immutable namespace ('t', 'a')' after Y (FROZEN set and checked on header + key)."
    source := "TOML 1.1 spec, Keys ('Defining a key multiple times is invalid') and Inline Table ('Keys and sub-tables cannot be added outside the braces')", status := .proven
    prop := ``Toml.KvRuleMore, thm := some ``Toml.kvRuleMore_proven },
  { id := "textlibs-toml-top-level-comments", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["loads", "skip_comment", "skip_until", "create_dict_rule", "parse_key_part"]
    statement := "After any run of blank and comment lines, with at least ten frames left (3 * depth + 14 per value): a key = value line, spaces or tabs and a comment running to the end gives the one-entry dict; a header [K], spaces or tabs and such a comment gives {K: {}}; a '[' that is the last character raises 'Invalid initial character for a key part' one past it."
    source := "TOML 1.1 spec, Comment ('Comments may be placed after a key/value pair'); _parser.py:192-195", status := .proven
    prop := ``Toml.TopLevelComments, thm := some ``Toml.topLevelComments_proven },
  { id := "textlibs-toml-multiline-basic-errors", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["parse_basic_str", "parse_multiline_str", "parse_value"]
    statement := "With at least six frames left: '\"\"\"', an optional newline, characters, then a control character other than tab and newline raises 'Illegal character' there; '\"\"\"', an optional newline and characters up to the end of the document raise 'Unterminated string' at the end."
    source := "TOML 1.1 spec, String (multi-line basic strings: control characters other than tab, line feed and carriage return must be escaped)", status := .proven
    prop := ``Toml.MultilineBasicErrors, thm := some ``Toml.multilineBasicErrors_proven },
  { id := "textlibs-toml-inline-dotted", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["parse_inline_table", "NestedDict.get_or_create_nest", "Flags.is_", "Flags.set"]
    statement := "For all bare keys a, b != c, values v, w of ArrayTableSpec and fillers around ',' and before '}', with 3 * depth + 16 frames left: {a.b=v, a.c=w} gives {a: {b: v, c: w}} and the position after '}'."
    source := "TOML 1.1 spec, Inline Table (dotted keys inside braces)", status := .proven
    prop := ``Toml.InlineDotted, thm := some ``Toml.inlineDotted_proven },
  { id := "textlibs-toml-escape-eof-pos", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["parse_basic_str_escape", "parse_basic_str", "loads"]
    statement := "Every TOMLDecodeError(msg, doc, pos) that loads raises has pos <= len(doc) (doc after CRLF normalisation)."
    source := "docs of TOMLDecodeError ('pos: The index of doc where parsing failed')", status := .refuted
    prop := ``Toml.DecodeErrorPosInDoc, thm := some ``Toml.decodeErrorPosInDoc_refuted
    bug := some "textlibs-toml-escape-eof-pos"
    notes := "'a = \"\\' (length 6) raises at pos 7. Duplicate of python/cpython#158566 and hukkin/tomli#312, both open." }
,
  { id := "textlibs-toml-loads-input", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["loads"]
    statement := "For every text without CR and every choice of which newlines are written as CRLF, loads gives exactly what it gives on the LF text (same dict or same error at the same position); a CR not followed by a newline is kept, so loads('\\r' + t) raises 'Invalid statement' at 0 (at least four frames left); an argument whose replace raises AttributeError or TypeError raises TypeError('Expected str object, not '<qualname>'') (at least one frame left)."
    source := "TOML 1.1 spec ('Newline means LF (0x0A) or CRLF (0x0D 0x0A)'); comment at _parser.py:154-155; docs of loads", status := .proven
    prop := ``Toml.LoadsInput, thm := some ``Toml.loadsInput_proven },
  { id := "textlibs-toml-comments", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["skip_comment", "skip_until"]
    statement := "skip_comment at '#' followed by characters allowed in comments returns the position of the newline that ends them, or the end of the document when none does (skip_until with error_on_eof=False); a control character other than tab before the newline or the end raises TOMLDecodeError 'Found invalid character' there; at anything but '#' it returns its argument."
    source := "TOML 1.1 spec, Comment ('Control characters other than tab ... are not permitted in comments')", status := .proven
    prop := ``Toml.CommentRules, thm := some ``Toml.commentRules_proven },
  { id := "textlibs-toml-top-level", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["loads", "skip_comment", "key_value_rule"]
    statement := "For every run L of blank and comment lines, with at least four frames left and 3 * depth + 14 per value: loads(L + D) for a DocRoundTrip document D gives D's dict (comment-only documents give {}); L, spaces or tabs, then a character that starts no statement raises 'Invalid statement' there; L, one key = value line, spaces or tabs, then a character other than a newline, '#', CR or '\"' raises 'Expected newline or end of document after a statement' there."
    source := "TOML 1.1 spec ('A hash symbol marks the rest of the line as a comment'; 'There must be a newline (or EOF) after a key/value pair')", status := .proven
    prop := ``Toml.TopLevel, thm := some ``Toml.topLevel_proven },
  { id := "textlibs-toml-unclosed-array", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["parse_array", "parse_value", "skip_comments_and_array_ws"]
    statement := "'[', filler, a value of ArrayTableSpec, filler, then anything but ']', ',' or '\"' (the end of the document included) raises TOMLDecodeError 'Unclosed array' there, with 3 * depth + 13 frames left below parse_value."
    source := "TOML 1.1 spec, Array", status := .proven
    prop := ``Toml.UnclosedArray, thm := some ``Toml.unclosedArray_proven },
  { id := "textlibs-toml-inline-table-rules", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["parse_inline_table", "parse_key_value_pair", "Flags.is_", "Flags.set", "NestedDict.get_or_create_nest"]
    statement := "With fillers around each ',' and entries K=v: for one-part keys k, k' with the same value and v not a table or array, {k=v, k'=w} raises 'Duplicate inline table key 'k'' after w; for a bare x, {k=v, k.x=w} raises 'Cannot overwrite a value' after w when v is not a table or array and 'Cannot mutate immutable namespace (k, x)' when it is; {k=v followed by anything but '}' or ',' raises 'Unclosed inline table' there."
    source := "TOML 1.1 spec, Inline Table ('fully self-contained'; keys may be dotted; a key may not be defined twice)", status := .proven
    prop := ``Toml.InlineTableRules, thm := some ``Toml.inlineTableRules_proven
    notes := "access_lists=False is not observable here: every list in an inline table is a value, which is frozen before a dotted key can reach it." },
  { id := "textlibs-toml-multiline-literal", pyFile := "Lib/tomllib/_parser.py"
    pyFns := ["parse_multiline_str", "parse_value", "skip_until"]
    statement := "With at least three frames left: for every text without ''' that does not end with ' (one or two ' inside are kept) and has no control characters other than tab and newline, an optional newline after the opening ''' (trimmed) and one or two ''' before the closing ''' (kept), parse_value returns the text and the position after the quotes; without a closing ''' it raises 'Expected \"'''\"' at the end of the document; a control character other than tab or newline before the closing quotes raises 'Found invalid character' there."
    source := "TOML 1.1 spec, String (multi-line literal strings; 1 or 2 single quotes next to the delimiters)", status := .proven
    prop := ``Toml.MultilineLiteralSpec, thm := some ``Toml.multilineLiteralSpec_proven }
,
  { id := "textlibs-email-dtext-qp-defect", pyFile := "Lib/email/_header_value_parser.py"
    pyFns := ["get_dtext"]
    statement := "Whenever get_dtext returns a token whose text is shorter than the text it consumed (a quoted pair was unquoted), the token carries an ObsoleteHeaderDefect."
    source := "get_dtext docstring :1582-1591 ('If there were quoted-printables, an ObsoleteHeaderDefect is added to the returned token's defect list')", status := .refuted
    prop := ``PyLean.TextLibs.Email.DtextQpDefect, thm := some ``PyLean.TextLibs.Email.dtextQpDefect_refuted
    bug := some "textlibs-email-ptext-had-qp"
    notes := "'a\\b': get_dtext returns ValueTerminal('ab', 'ptext') with no defect (dtext_qp), because had_qp is only set for an escaped backslash." }
,
  { id := "textlibs-email-comment-spec", pyFile := "Lib/email/_header_value_parser.py"
    pyFns := ["get_comment", "get_qp_ctext", "Comment.__str__", "Comment.quote", "Comment.content",
      "make_parenthesis_pairs", "_get_ptext_to_endchars", "get_fws"]
    statement := "With r frames left (py_recursion_remaining), for every canonical comment body b (text escaped with make_parenthesis_pairs, with nested comments in canonical form, depth levels of nesting) and rest, when 2 * depth + 6 <= r: get_comment('(' + b + ')' + rest) returns rest and a comment whose str() is '(' + b + ')', whose content is b with its top-level text unescaped, and whose elements are WhiteSpaceTerminals or nested comments, and str() and content called with r frames return; a comment the value ends inside gets 'end of header inside comment' and its ')' in str() (with 6 frames); a non-empty value not starting with '(' raises HeaderParseError(\"expected '(' but found '<value>'\") (with 1 frame)."
    source := "get_comment docstring :1287-1291 (ccontent = ctext / quoted-pair / comment; nested comments handled here); get_qp_ctext docstring :1197-1206 (a WhiteSpaceTerminal); Comment.content (module docstring :51-52); :1292-1294, :1305-1308; Python/ceval_macros.h:426-429 (one frame per Python call)", status := .proven
    prop := ``PyLean.TextLibs.Email.CommentSpec, thm := some ``PyLean.TextLibs.Email.commentSpec_proven
    notes := "The recursion limit is modelled for these functions (EmailFrames.lean: commentN, commentStrN, contentN, the deepest chain of Python calls, checked exactly against CPython by the emailfr difftest). get_comment needs one frame per level, str() and content two; the bound 2 * depth + 6 is sufficient, and the unbounded reading is refuted (textlibs-email-nested-comment-recursion)." }
,
  { id := "textlibs-email-nested-comment-recursion", pyFile := "Lib/email/_header_value_parser.py"
    pyFns := ["get_comment", "Comment.__str__", "Comment.quote"]
    statement := "Given the frames any comment without nesting needs (six), get_comment returns for every nesting depth of a canonical comment, and so does str() of the comment it returns."
    source := "Doc/library/email.parser.rst:62-68 (non-compliant input is reported through defects); Lib/email/headerregistry.py:169-174", status := .refuted
    prop := ``PyLean.TextLibs.Email.CommentNestingUnbounded, thm := some ``PyLean.TextLibs.Email.commentNestingUnbounded_refuted
    bug := some "textlibs-email-nested-comment-recursion"
    notes := "'(' * 7 + ')' * 7 with 8 frames: get_comment parses (it needs 8), str() raises RecursionError (it needs 13); with 7 frames get_comment raises (comment_depth7). At the default limit this is depth about 500 for str() and 1000 for get_comment, as the bug record measures." }
,
  { id := "textlibs-email-unstructured-encoded-words", pyFile := "Lib/email/_header_value_parser.py"
    pyFns := ["get_unstructured", "get_encoded_word", "EWWhiteSpaceTerminal.__str__", "TokenList.__str__"]
    statement := "For every list of encoded words =?tok?= that _ew.decode decodes (no ?= inside tok) separated by runs of whitespace, get_unstructured returns a token list with no defects whose elements are the EncodedWords with an EWWhiteSpaceTerminal between each two, and whose str() is the decoded texts run together."
    source := "RFC 2047 section 6.2 ('linear-white-space that separates a pair of adjacent encoded-words is ignored'); :1168-1180", status := .proven
    prop := ``PyLean.TextLibs.Email.UnstructuredEncodedWords, thm := some ``PyLean.TextLibs.Email.unstructuredEncodedWords_proven
    notes := "_ew.decode is any function that accepts these words; the decoded texts are arbitrary. Pins get_encoded_word's split at the closing ?= and the rest it returns, the EncodedWord token, and the EWWhiteSpaceTerminal replacement of :1175-1178." }
,
  { id := "textlibs-email-encoded-word-spec", pyFile := "Lib/email/_header_value_parser.py"
    pyFns := ["get_encoded_word"]
    statement := "For every word =?cs?e?txt?= (no ? in cs or txt, e not ? or =, txt starting with an =XX escape or not with =) followed by any rest y, get_encoded_word hands _ew.decode exactly the word (re-splitting when the first ?= is the ? before an =XX escape) and returns y; when the word decodes, the EncodedWord's str() is the decoded text and its defects are 'whitespace inside encoded word' (when the token holds two words), decode's defects, and 'missing trailing whitespace after encoded-word' (when y does not start with a space or tab); when decode raises ValueError/KeyError it raises _InvalidEwError(\"encoded word format invalid: '<value>'\"); another exception propagates."
    source := "RFC 2047 section 2 (encoded-word syntax); :1080-1127 (the =XX re-split :1093-1099 and its comment, the defects :1100-1102, :1112, :1124-1126)", status := .proven
    prop := ``PyLean.TextLibs.Email.EncodedWordSpec, thm := some ``PyLean.TextLibs.Email.encodedWordSpec_proven
    notes := "Every Q-encoded word whose text starts with an escape takes the re-split, e.g. '=?utf-8?q?=C3=A9?='." }
,
  { id := "textlibs-email-unstructured-word-then-ew", pyFile := "Lib/email/_header_value_parser.py"
    pyFns := ["get_unstructured"]
    statement := "For every word p (no space or tab, no =?) followed by an encoded word =?cs?e?txt?= that _ew.decode decodes (e in qQbB; no ?, space, tab or newline in cs and txt), get_unstructured gives str() = p + decoded text and, with no whitespace between them, elements ValueTerminal, EncodedWord and the defect 'missing whitespace before encoded word'; with whitespace sep between them, str() = p + sep + decoded text, elements ValueTerminal, WhiteSpaceTerminal, EncodedWord and no defect."
    source := ":1168-1180 (missing whitespace defect and have_ws; the EWWhiteSpaceTerminal only after an encoded word), :1182-1189 (split at =? inside a word)", status := .proven
    prop := ``PyLean.TextLibs.Email.UnstructuredWordThenEw, thm := some ``PyLean.TextLibs.Email.unstructuredWordThenEw_proven
    notes := "With UnstructuredEncodedWords this pins both branches of the unstructured[-2] == 'encoded-word' test." }
,
  { id := "textlibs-plist-loads-binary-invalid-only", pyFile := "Lib/plistlib.py"
    pyFns := ["loads", "load", "_BinaryPlistParser.parse", "_BinaryPlistParser._read_object",
      "_BinaryPlistParser._get_size", "_BinaryPlistParser._read", "_BinaryPlistParser._read_ints",
      "_BinaryPlistParser._read_refs", "InvalidFileException.__init__"]
    statement := "With len(data) + 8 frames left, loads(data) with fmt=FMT_BINARY (or fmt=None when data does not look like XML) returns or raises InvalidFileException('Invalid file'), for every bytes object data: whatever its trailer, offset sizes, reference sizes (0 or more than 8 included), offsets past the end, counts, tokens and references (cyclic ones included), every struct.error, IndexError, OverflowError, ValueError (UnicodeDecodeError included) and unhashable-key TypeError inside is turned into InvalidFileException, and no RecursionError escapes."
    source := "Doc/library/plistlib.rst ('The parser raises InvalidFileException when the file cannot be parsed'); :508-510 (except by class), :635-639", status := .proven
    prop := ``Plist.LoadsBinaryInvalidOnly, thm := some ``Plist.loadsBinaryInvalidOnly_proven
    notes := "The frame bound is what the object cache buys: a container is stored in self._objects before its elements are read (:619, :634), so nested calls visit each slot at most once and the depth is at most the number of objects. Without it the statement is refuted (textlibs-plist-loads-nesting-depth). The except clause is modelled by class membership (excMro), so UnicodeDecodeError and InvalidFileException are caught as ValueErrors and RecursionError is not. dict_type is dict (scope limit)." }
,
  { id := "textlibs-plist-loads-nesting-depth", pyFile := "Lib/plistlib.py"
    pyFns := ["_BinaryPlistParser._read_object", "_BinaryPlistParser.parse"]
    statement := "With 16 frames left (more than any binary plist without nested containers needs), loads(data, fmt=FMT_BINARY) returns or raises InvalidFileException for every data."
    source := "the unbounded reading of LoadsBinaryInvalidOnly, which test_deep_nesting rules out", status := .refuted
    prop := ``Plist.LoadsBinaryAnyDepth, thm := some ``Plist.loadsBinaryAnyDepth_refuted
    bug := some "textlibs-plist-deep-nesting-recursion"
    notes := "Documented limitation, not for filing: eleven nested one-element arrays around a string raise RecursionError with 16 frames (they need 17). Lib/test/test_plistlib.py:1070-1082 accepts RecursionError." }
,
  { id := "textlibs-plist-binary-round-trip", pyFile := "Lib/plistlib.py"
    pyFns := ["dumps", "dump", "loads", "load", "_BinaryPlistWriter.write", "_BinaryPlistWriter._flatten",
      "_BinaryPlistWriter._getrefnum", "_BinaryPlistWriter._write_size", "_BinaryPlistWriter._write_object",
      "_BinaryPlistParser.parse", "_BinaryPlistParser._read_object", "_BinaryPlistParser._get_size",
      "_BinaryPlistParser._read", "_BinaryPlistParser._read_ints", "_BinaryPlistParser._read_refs"]
    statement := "For every object graph (shared and cyclic lists, tuples, dicts and frozendicts; None, bools, ints, floats, strs, bytes, bytearrays, UIDs; no datetimes) that dumps(value, fmt=FMT_BINARY, sort_keys=..., skipkeys=...) writes to b (shorter than 2**63 bytes), loads(b) with len(b) + 8 frames returns a graph related to the value: the roots are related, and related objects match: equal ints (the whole -2**63..2**64-1 range the writer accepts), bools, strs (ASCII and UTF-16, astral characters included), bytes, UID data and None, floats with the same bits or equal (==), a list for each list or tuple with related elements, and a dict for each dict or frozendict with exactly the str-keyed items the writer keeps, in the order it writes them, keys and values related."
    source := "Doc/library/plistlib.rst (load reads what dump writes; supported value types); invariant: round trip", status := .proven
    prop := ``Plist.BinaryRoundTrip, thm := some ``Plist.binaryRoundTrip_proven
    notes := "Proved by composing the writer (_flatten numbers every reachable object, the tables map objects back to their number, _write_object writes canonical bytes: PlistWriteInv, PlistWriteObj, PlistLayout) with the reader on any canonical table (PlistReadAll, readObj_tab, with the object cache keeping cycles and sharing). Dict keys are the dict's type invariant (pairwise different strs). Exact float bits are refuted (textlibs-plist-binary-float-bits, the 0.0/-0.0 sharing); datetimes are refuted (textlibs-plist-binary-datetime). The XML writer and parser are parameters." }
,
  { id := "textlibs-plist-binary-float-bits", pyFile := "Lib/plistlib.py"
    pyFns := ["_BinaryPlistWriter._flatten", "_BinaryPlistWriter._getrefnum"]
    statement := "The binary round trip keeps the bits of every float: loads(dumps([x, y], fmt=FMT_BINARY)) is a list of two floats with the bits of x and y."
    source := "invariant: the binary format stores IEEE doubles exactly; the XML twin keeps -0.0", status := .refuted
    prop := ``Plist.BinaryFloatBits, thm := some ``Plist.binaryFloatBits_refuted
    bug := some "textlibs-plist-binary-negative-zero"
    notes := "[0.0, -0.0]: _flatten finds (float, -0.0) equal to the (float, 0.0) already in _objtable, so both elements refer to one object and loads gives [0.0, 0.0]. BinaryRoundTrip proves the narrowed form (same bits or equal)." }
,
  { id := "textlibs-plist-binary-datetime", pyFile := "Lib/plistlib.py"
    pyFns := ["_BinaryPlistWriter._write_object", "_BinaryPlistParser._read_object"]
    statement := "Every naive datetime in datetime.min..datetime.max written alone with dumps(fmt=FMT_BINARY) is read back by loads as the same datetime."
    source := "Doc/library/plistlib.rst (datetime.datetime is a supported value); invariant: round trip", status := .refuted
    prop := ``Plist.BinaryDateRoundTrip, thm := some ``Plist.binaryDateRoundTrip_refuted
    bug := some "textlibs-plist-binary-datetime-max"
    notes := "datetime.max: total_seconds() rounds to 252423993600.0, and datetime(2001, 1, 1) + timedelta(seconds=f) overflows, so loads raises InvalidFileException. The reader's timedelta(seconds=float) is modelled exactly (accum, the leftover rounding, microseconds_to_delta_ex) and checked by the difftest." }
,
  { id := "textlibs-plist-count-to-size", pyFile := "Lib/plistlib.py"
    pyFns := ["_count_to_size"]
    statement := "For every count below 2**64, _count_to_size(count) is 1, 2, 4 or 8 and is the smallest of them whose bytes hold count."
    source := "invariant: the reference and offset sizes of the binary format (:683-687, :700-701)", status := .proven
    prop := ``Plist.CountToSizeMinimal, thm := some ``Plist.countToSizeMinimal_proven }
]

end PyLean.TextLibs
