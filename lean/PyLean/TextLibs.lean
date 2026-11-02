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
import PyLean.TextLibs.DifflibObjLaws
import PyLean.TextLibs.CsvSniffProps

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
    notes := "self.opcodes = answer = [] runs ahead of get_matching_blocks, so the second call returns []." }
]

end PyLean.TextLibs
