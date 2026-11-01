import PyLean.Registry
import PyLean.BytesObj.Bytes.ByteArrayProps4

/-! Registry entries for bytes (Objects/bytesobject.c, Objects/bytes_methods.c) and
bytearray (Objects/bytearrayobject.c). -/

namespace PyLean.BytesObj.Bytes

open PyLean.Registry

def entries : List Entry := [
  { id := "bytesobj-bytes-class-shortcut", pyFile := "Objects/bytes_methods.c"
    pyFns := ["_Py_bytes_isspace", "_Py_bytes_isalpha", "_Py_bytes_isalnum", "_Py_bytes_isdigit",
      "bytearray_isspace", "bytearray_isalpha", "bytearray_isalnum", "bytearray_isdigit"]
    statement := "For every byte string and every ctype class: isspace, isalpha, isalnum, isdigit are true exactly for a non-empty string of class members; the one-byte shortcut agrees with the loop."
    source := "docstrings _Py_isspace__doc__ etc., bytes_methods.c:5-9", status := .proven
    prop := ``ClassShortcut, thm := some ``classShortcut_proven },
  { id := "bytesobj-bytes-cased", pyFile := "Objects/bytes_methods.c"
    pyFns := ["_Py_bytes_islower", "_Py_bytes_isupper", "bytearray_islower", "bytearray_isupper"]
    statement := "islower (isupper) is true exactly when no byte is uppercase (lowercase) and some byte is lowercase (uppercase), for every length; the one-byte shortcut agrees."
    source := "docstrings, bytes_methods.c:125-129, :159-163", status := .proven
    prop := ``CasedSpec, thm := some ``casedSpec_proven },
  { id := "bytesobj-bytes-title", pyFile := "Objects/bytes_methods.c"
    pyFns := ["_Py_bytes_istitle", "_Py_bytes_title", "bytearray_istitle", "bytearray_title"]
    statement := "For every byte string, b.title().istitle() holds exactly when b has a cased byte, and title keeps the length."
    source := "docstrings, bytes_methods.c:193-199, :277-281", status := .proven
    prop := ``TitleIstitle, thm := some ``titleIstitle_proven },
  { id := "bytesobj-bytes-case-maps", pyFile := "Objects/bytes_methods.c"
    pyFns := ["_Py_bytes_lower", "_Py_bytes_upper", "_Py_bytes_capitalize", "_Py_bytes_swapcase",
      "bytearray_lower", "bytearray_upper", "bytearray_capitalize", "bytearray_swapcase"]
    statement := "For every byte string: swapcase is an involution, lower and upper keep the length and absorb each other, and capitalize is upper(b[:1]) + lower(b[1:])."
    source := "docstrings, bytes_methods.c:245-326", status := .proven
    prop := ``CaseMaps, thm := some ``caseMaps_proven },
  { id := "bytesobj-bytes-isascii", pyFile := "Objects/bytes_methods.c"
    pyFns := ["_Py_bytes_isascii", "bytearray_isascii"]
    statement := "isascii is true exactly for byte strings with no byte above 127, the empty one included."
    source := "docstring, bytes_methods.c:724-728", status := .proven
    prop := ``IsAsciiSpec, thm := some ``isAsciiSpec_proven },
  { id := "bytesobj-bytes-maketrans", pyFile := "Objects/bytes_methods.c"
    pyFns := ["_Py_bytes_maketrans", "bytes_maketrans_impl", "bytearray_maketrans_impl"]
    statement := "maketrans raises ValueError exactly on a length mismatch; otherwise the table has 256 entries and fixes every byte not in frm."
    source := "docstring, bytes_methods.c:348-354", status := .proven
    prop := ``MaketransSpec, thm := some ``maketransSpec_proven },
  { id := "bytesobj-bytes-find-byte-arg", pyFile := "Objects/bytes_methods.c"
    pyFns := ["parse_args_finds_byte", "find_internal", "_Py_bytes_find", "_Py_bytes_index", "_Py_bytes_rfind",
      "_Py_bytes_rindex", "_Py_bytes_count"]
    statement := "An int argument of find, rfind, index, rindex, count means the one-byte string for every byte value and all bounds; ints outside range(256), of any size, raise ValueError; index is find with ValueError for -1; a non-buffer, non-index raises TypeError."
    source := "Doc/library/stdtypes.rst bytes.find ('The subsequence to search for may be any bytes-like object or an integer in the range 0 to 255')", status := .proven
    prop := ``FindByteArg, thm := some ``findByteArg_proven },
  { id := "bytesobj-bytes-contains", pyFile := "Objects/bytes_methods.c"
    pyFns := ["_Py_bytes_contains", "bytes_contains", "bytearray_contains"]
    statement := "x in b: an int in range(256) is byte membership and equals bytes([x]) in b; other ints raise ValueError; b'' is in every b."
    source := "Doc/library/stdtypes.rst common sequence 'x in s', bytes note", status := .proven
    prop := ``ContainsSpec, thm := some ``containsSpec_proven },
  { id := "bytesobj-bytes-tailmatch-tuple", pyFile := "Objects/bytes_methods.c"
    pyFns := ["tailmatch", "_Py_bytes_tailmatch", "_Py_bytes_startswith", "_Py_bytes_endswith"]
    statement := "startswith/endswith with a tuple is 'any item matches', stopping at the first match so that a later invalid item is not looked at; a non-buffer argument gets the method's own TypeError."
    source := "Doc/library/stdtypes.rst bytes.startswith", status := .proven
    prop := ``TailmatchTuple, thm := some ``tailmatchTuple_proven },
  { id := "bytesobj-bytes-capi", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_get_empty", "_PyBytes_FromSize", "PyBytes_FromStringAndSize", "PyBytes_FromString",
      "PyBytes_FromFormatV", "PyBytes_FromFormat", "PyBytes_Size", "PyBytes_AsString", "PyBytes_AsStringAndSize",
      "bytes_length"]
    statement := "PyBytes_FromFormat copies a format with no conversion; PyBytes_Size, PyBytes_AsString and PyBytes_AsStringAndSize report TypeError for non-bytes; without a length pointer an embedded NUL is ValueError; PyBytes_FromStringAndSize copies and refuses a negative size; PyBytes_FromString stops at the first NUL."
    source := "Doc/c-api/bytes.rst", status := .proven
    prop := ``CApiSpec, thm := some ``cApiSpec_proven
    notes := "The difftest calls the real functions through ctypes.pythonapi, including conversions in PyBytes_FromFormat." },
  { id := "bytesobj-bytes-hash-cache", pyFile := "Objects/bytesobject.c"
    pyFns := ["set_ob_shash", "get_ob_shash", "bytes_hash", "bytes_subtype_new", "bytes_alloc", "_PyBytes_Resize"]
    statement := "For any Py_HashBuffer that never returns -1: hash(b) is the hash of the contents whether or not the cache was filled, a second call hits the cache, a subclass copy keeps the cache, and a resize that changes the size invalidates it."
    source := "invariant of ob_shash, Include/cpython/bytesobject.h; bytesobject.c:3206-3216", status := .proven
    prop := ``BytesHashCache, thm := some ``bytesHashCache_proven
    notes := "Generic over the hash function: Py_HashBuffer lives in Python/pyhash.c and has a random seed." },
  { id := "bytesobj-bytes-format-field", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FormatEx", "bytes_mod", "bytearray_mod", "bytearray_mod_lock_held"]
    statement := "For every flag set, sign, width and length: the writes of a field produce exactly the alloc bytes reserved (the assert at bytesobject.c:1052), so the writer's buffer is neither overrun nor left with a gap."
    source := "bytesobject.c:1052 (assert); invariant", status := .proven
    prop := ``FieldAllocExact, thm := some ``fieldAllocExact_proven },
  { id := "bytesobj-bytes-format-fast-slow", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FormatEx", "formatlong"]
    statement := "%d %i %u %o %x of an exact int with no width, precision or sign flag: the fast path gives the same text as formatlong and the field writer, for every int, including the digit-limit error."
    source := "fast path against slow path of the same conversion, bytesobject.c:864-909", status := .proven
    prop := ``FastSlowLong, thm := some ``fastSlowLong_proven
    notes := "Hypothesis: the text is below INT_MAX bytes, the guard the slow path has and the fast path has not. X has no fast path." },
  { id := "bytesobj-bytes-format-literal", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FormatEx", "bytes_mod"]
    statement := "For every format without % whose size an object can have: the bytes are copied, an empty tuple or a mapping is accepted, and any other right operand raises TypeError('not all arguments converted during bytes formatting')."
    source := "Doc/library/stdtypes.rst, printf-style bytes formatting", status := .proven
    prop := ``FormatLiteral, thm := some ``formatLiteral_proven },
  { id := "bytesobj-bytes-format-converters", pyFile := "Objects/bytesobject.c"
    pyFns := ["byte_converter", "format_obj"]
    statement := "%c accepts an int exactly in range(256) and a bytes or bytearray exactly of length 1; %b gives the contents of bytes, bytearray, __bytes__ results and buffers."
    source := "Doc/library/stdtypes.rst, printf-style bytes formatting table", status := .proven
    prop := ``ConvertersSpec, thm := some ``convertersSpec_proven },
  { id := "bytesobj-bytes-format-long-types", pyFile := "Objects/bytesobject.c"
    pyFns := ["formatlong", "getnextarg"]
    statement := "bool and __index__ objects format as their integer value; %o %x %X refuse a float with TypeError; a bytes argument is a TypeError; getnextarg stops at the end of the tuple with 'not enough arguments for format string'."
    source := "Doc/library/stdtypes.rst, printf-style bytes formatting", status := .proven
    prop := ``FormatLongTypes, thm := some ``formatLongTypes_proven },
  { id := "bytesobj-bytes-format-bad-conv", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FormatEx"]
    statement := "A byte that is no conversion raises ValueError: refuted, because a byte above 127 is a negative c and PyErr_Format('%c') raises OverflowError instead."
    source := "the ValueError of the default case, bytesobject.c:949-955", status := .refuted
    prop := ``BadConvIsValueError, thm := some ``badConvIsValueError_refuted
    bug := some "bytesobj-bytes-format-nonascii-conversion" },
  { id := "bytesobj-bytes-format-bad-conv-ascii", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FormatEx"]
    statement := "Every ASCII byte that is no conversion raises ValueError."
    source := "narrowing of bytesobj-bytes-format-bad-conv", status := .proven
    prop := ``BadConvAsciiIsValueError, thm := some ``badConvAsciiIsValueError_proven },
  { id := "bytesobj-bytes-format-float-error", pyFile := "Objects/bytesobject.c"
    pyFns := ["formatfloat"]
    statement := "%f reports the failure of PyFloat_AsDouble: refuted, every failure becomes TypeError('float argument required'), also OverflowError for an int too large."
    source := "twin: formatfloat in Objects/unicodeobject.c returns the original error", status := .refuted
    prop := ``FloatErrorPreserved, thm := some ``floatErrorPreserved_refuted
    bug := some "bytesobj-bytes-format-float-error-masked" },
  { id := "bytesobj-bytes-format-float-type", pyFile := "Objects/bytesobject.c"
    pyFns := ["formatfloat"]
    statement := "A non-number argument of a float conversion raises TypeError('float argument required, not ...')."
    source := "narrowing of bytesobj-bytes-format-float-error", status := .proven
    prop := ``FloatArgType, thm := some ``floatArgType_proven },
  { id := "bytesobj-bytes-format-star-min", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FormatEx"]
    statement := "A negative * width gives a field at least that wide when it succeeds: refuted at PY_SSIZE_T_MIN, whose negation wraps and drops the width."
    source := "Doc/library/stdtypes.rst, printf-style formatting: '*' width; invariant: no signed overflow", status := .refuted
    prop := ``NegStarWidth, thm := some ``negStarWidth_refuted
    bug := some "bytesobj-bytes-format-star-width-min" },
  { id := "bytesobj-bytes-format-star-other", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FormatEx"]
    statement := "For every other negative width the negation is exact and positive."
    source := "narrowing of bytesobj-bytes-format-star-min", status := .proven
    prop := ``NegWrapExact, thm := some ``negWrapExact_proven },
  { id := "bytesobj-bytes-escape-roundtrip", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_DecodeEscape2", "PyBytes_DecodeEscape", "PyBytes_Repr", "bytes_repr", "bytes_str",
      "bytearray_repr", "bytearray_repr_lock_held", "bytearray_str"]
    statement := "For every byte string and either quote: decoding the body of the literal repr writes, for bytes and for bytearray, gives back the bytes with no invalid escape, so repr is an inverse of escape_decode."
    source := "repr of bytes is a literal, Doc/library/functions.rst repr", status := .proven
    prop := ``ReprDecodeRoundTrip, thm := some ``reprDecodeRoundTrip_proven
    notes := "bytearray's repr escapes ' even inside double quotes, which bytes's does not: bytearray(b\"'\") shows bytearray(b\"\\'\"). The text differs, the value does not; not filed." },
  { id := "bytesobj-bytes-escape-warning", pyFile := "Objects/bytesobject.c"
    pyFns := ["PyBytes_DecodeEscape", "_PyBytes_DecodeEscape2"]
    statement := "An invalid escape keeps the backslash, reports the first bad byte through the warning, and a clean input gives no warning."
    source := "Doc/whatsnew/3.12, invalid escape sequences", status := .proven
    prop := ``EscapeWarning, thm := some ``escapeWarning_proven },
  { id := "bytesobj-bytes-repr-size", pyFile := "Objects/bytesobject.c"
    pyFns := ["PyBytes_Repr"]
    statement := "The sizing loop of PyBytes_Repr and the squotes extra give exactly the length the writing loop produces, for every byte string and both smartquotes settings."
    source := "invariant: PyUnicode_New(newsize) must hold the writes, bytesobject.c:1382", status := .proven
    prop := ``ReprSizeExact, thm := some ``reprSizeExact_proven },
  { id := "bytesobj-bytes-private-find", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_Find", "_PyBytes_ReverseFind"]
    statement := "_PyBytes_Find is stringlib_find for every haystack, needle and offset >= 0: searching one byte less and comparing the last alignment by hand changes nothing."
    source := "comment bytesobject.c:1315", status := .proven
    prop := ``PrivateFindAgrees, thm := some ``privateFindAgrees_proven },
  { id := "bytesobj-bytes-concat", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_concat", "PyBytes_Concat", "PyBytes_ConcatAndDel"]
    statement := "a + b for bytes-like operands is the concatenation, a TypeError naming both types otherwise, and the in-place and new-object branches of PyBytes_Concat give the same result for every operand."
    source := "fast path against slow path, bytesobject.c:3160-3195", status := .proven
    prop := ``ConcatSpec, thm := some ``concatSpec_proven },
  { id := "bytesobj-bytes-repeat-fill", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_Repeat", "bytearray_repeat", "bytearray_repeat_lock_held"]
    statement := "_PyBytes_Repeat, the doubling copy or memset, produces n copies of the source for every source and n >= 1."
    source := "invariant", status := .proven
    prop := ``RepeatFill, thm := some ``repeatFill_proven },
  { id := "bytesobj-bytes-repeat", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_repeat"]
    statement := "b * n: n <= 0 is empty, n = 1 is b, otherwise n copies, with OverflowError exactly for len(b) > maxsize // n."
    source := "Doc/library/stdtypes.rst common sequence s * n", status := .proven
    prop := ``BytesRepeatSpec, thm := some ``bytesRepeatSpec_proven },
  { id := "bytesobj-bytes-richcompare-twins", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_compare_eq", "bytes_richcompare", "bytearray_richcompare"]
    statement := "bytes_richcompare, with its first-byte shortcuts, and bytearray_richcompare agree on every pair of byte strings and every operator; == is list equality and != its negation."
    source := "twins: both implement the comparison of sequences of ints", status := .proven
    prop := ``RichcompareTwins, thm := some ``richcompareTwins_proven },
  { id := "bytesobj-bytes-subscript-twins", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_item", "bytes_subscript", "bytearray_getitem", "bytearray_getitem_lock_held", "bytearray_subscript",
      "bytearray_subscript_lock_held"]
    statement := "bytes[slice] and bytearray[slice] hold the same bytes for every slice, in spite of the extra full-slice shortcut of bytes; an index reads the byte at the position and raises IndexError outside."
    source := "twins; Doc/library/stdtypes.rst common sequence operations", status := .proven
    prop := ``SubscriptTwins, thm := some ``subscriptTwins_proven },
  { id := "bytesobj-bytes-buffer", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_buffer_getbuffer", "bytes___bytes___impl", "bytes_getnewargs", "bytearray_getbuffer",
      "bytearray_getbuffer_lock_held", "bytearray_releasebuffer"]
    statement := "A view of bytes is read-only and exposes the contents; a view of bytearray is writable and raises ob_exports by one for as long as it lives; bytes(b) and __getnewargs__ give the contents."
    source := "Doc/library/stdtypes.rst memoryview.readonly; PEP 3118", status := .proven
    prop := ``BufferSpec, thm := some ``bufferSpec_proven },
  { id := "bytesobj-bytes-join", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_join_impl", "PyBytes_Join", "bytearray_join_impl"]
    statement := "sep.join(items) is the items with sep between them for list, tuple and generator arguments; the first item that is no buffer gives a TypeError naming its position."
    source := "docstring, bytesobject.c:1880-1892", status := .proven
    prop := ``JoinSpec, thm := some ``joinSpec_proven },
  { id := "bytesobj-bytes-translate-twins", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_translate_impl", "bytearray_translate_impl"]
    statement := "bytes.translate and bytearray.translate agree on every input, the no-delete fast loop equals the general loop, and with no table the result is the bytes outside delete."
    source := "twins; fast path against slow path, bytesobject.c:2227-2269", status := .proven
    prop := ``TranslateTwins, thm := some ``translateTwins_proven },
  { id := "bytesobj-bytes-strip-twins", pyFile := "Objects/bytesobject.c"
    pyFns := ["do_xstrip", "do_strip", "do_argstrip", "bytes_lstrip_impl", "bytes_rstrip_impl", "bytearray_strip_impl_helper",
      "bytearray_lstrip_impl", "bytearray_rstrip_impl"]
    statement := "bytes.strip and bytearray.strip strip the same bytes for every byte string and direction, with None (Py_ISSPACE against the six-byte string) and with an explicit set."
    source := "twins", status := .proven
    prop := ``StripTwins, thm := some ``stripTwins_proven },
  { id := "bytesobj-bytes-remove-affix", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_removeprefix_impl", "bytes_removesuffix_impl", "bytearray_removeprefix_impl", "bytearray_removesuffix_impl"]
    statement := "With a non-empty matching affix, the affix and the result rebuild the original; otherwise the original comes back."
    source := "docstrings, bytesobject.c:2332-2336, :2369-2373", status := .proven
    prop := ``RemoveAffix, thm := some ``removeAffix_proven },
  { id := "bytesobj-bytes-decode", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_decode_impl", "bytearray_decode_impl"]
    statement := "For every byte string, s.decode('latin-1') is the code points of the bytes and bytes(text, 'latin-1') inverts it; 'ascii' accepts exactly the strings below 128."
    source := "Doc/library/codecs.rst", status := .proven
    prop := ``DecodeRoundTrip, thm := some ``decodeRoundTrip_proven
    notes := "Two codecs stand for the codec registry, which is out of this module's scope; decode itself only forwards." },
  { id := "bytesobj-bytes-fromhex-roundtrip", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FromHex", "bytes_fromhex_impl", "bytes_hex_impl", "bytearray_fromhex_impl", "bytearray_hex_impl"]
    statement := "bytes.fromhex(b.hex()) == b for every byte string."
    source := "docstrings, bytesobject.c:2502-2505, :2640-2651", status := .proven
    prop := ``FromHexRoundTrip, thm := some ``fromHexRoundTrip_proven },
  { id := "bytesobj-bytes-fromhex-tail", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FromHex"]
    statement := "fromhex of a view does not depend on what follows it in memory: refuted, the digit after the view is read."
    source := "invariant: a function reads only the buffer it was given", status := .refuted
    prop := ``FromHexIgnoresTail, thm := some ``fromHexIgnoresTail_refuted
    bug := some "bytesobj-bytes-fromhex-reads-past-view" },
  { id := "bytesobj-bytes-fromhex-terminated", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FromHex"]
    statement := "For a NUL-terminated argument the odd digit is reported: one hex digit in bytes or bytearray raises ValueError."
    source := "narrowing of bytesobj-bytes-fromhex-tail", status := .proven
    prop := ``FromHexTerminated, thm := some ``fromHexTerminated_proven },
  { id := "bytesobj-bytes-hex-sep", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_hex_impl", "bytearray_hex_impl"]
    statement := "hex(sep, k): dropping the separators gives the plain hex digits, whether the groups count from the left or the right, for every number of chunks."
    source := "docstring, bytesobject.c:2636-2651", status := .proven
    prop := ``HexSepFilter, thm := some ``hexSepFilter_proven },
  { id := "bytesobj-bytes-new", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_new_impl", "_PyBytes_FromBuffer", "_PyBytes_FromList", "_PyBytes_FromTuple", "_PyBytes_FromIterator",
      "PyBytes_FromObject"]
    statement := "bytes(x): a list, a tuple and a generator of ints in range(256) give those bytes (three C loops); an int n >= 0 gives n zero bytes and a negative one ValueError; a str without an encoding is TypeError; a buffer gives its contents; a bad item stops with ValueError."
    source := "docstring, bytesobject.c:3089-3100", status := .proven
    prop := ``BytesNewSpec, thm := some ``bytesNewSpec_proven },
  { id := "bytesobj-bytes-iter", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_iter", "striter_next", "striter_len", "striter_reduce", "striter_setstate"]
    statement := "iter(b) yields the bytes in order and then stops for good; __length_hint__ counts what is left; __setstate__ clamps into [0, len]; rebuilding from __reduce__ restores the iterator."
    source := "iterator protocol; pickling round trip", status := .proven
    prop := ``BytesIterSpec, thm := some ``bytesIterSpec_proven
    notes := "bytes clamps a negative state to 0 and bytearray to -1, which means exhausted, as the list iterator does; recorded in the two models, not filed." },
  { id := "bytesobj-bytes-writer", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytesWriter_Init", "_PyBytesWriter_AsString", "_PyBytesWriter_GetSize", "_PyBytesWriter_Resize",
      "_PyBytesWriter_Prepare", "_PyBytesWriter_Alloc", "_PyBytesWriter_Finish", "_PyBytesWriter_WriteBytes"]
    statement := "From any state with 0 <= min_size <= allocated: a successful Prepare raises min_size by exactly the request and keeps min_size <= allocated; Alloc establishes it; WriteBytes advances by the data's length."
    source := "invariant: _PyBytesWriter_CheckConsistency, bytesobject.c:3495-3528", status := .proven
    prop := ``WriterInvariant, thm := some ``writerInvariant_proven },
  { id := "bytesobj-bytearray-resize-wf", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_resize_lock_held", "PyByteArray_Resize", "bytearray_resize_impl", "PyByteArray_Size", "PyByteArray_AsString",
      "bytearray_length", "bytearray_alloc", "bytearray_sizeof_impl"]
    statement := "For every object with a valid layout and every request, a successful resize gives the requested size and a valid layout (data and terminator inside ob_alloc), keeps the common bytes and the export count."
    source := "invariant: bytearray_resize_lock_held; __alloc__ and __sizeof__ expose ob_alloc, which the difftest compares", status := .proven
    prop := ``ResizeWF, thm := some ``resizeWF_proven },
  { id := "bytesobj-bytearray-export-rule", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["_canresize", "bytearray_resize_lock_held"]
    statement := "A resize to the same size always works; any other resize of an object with exports raises BufferError('Existing exports of data: object cannot be re-sized'), after the ValueError for a negative size; with no exports a size that fits in memory succeeds."
    source := "Doc/c-api/bytearray.rst; bytearrayobject.c:104-113", status := .proven
    prop := ``ExportRule, thm := some ``exportRule_proven },
  { id := "bytesobj-bytearray-init-initialised", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray___init___impl"]
    statement := "After any b.__init__(items) on a fresh object, also a failed one, every byte is a value: refuted by the list fast path."
    source := "invariant: Python code cannot read uninitialized memory", status := .refuted
    prop := ``InitInitialised, thm := some ``initInitialised_refuted
    bug := some "bytesobj-bytearray-init-uninitialized" },
  { id := "bytesobj-bytearray-extend-initialised", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_extend_impl", "bytearray_setslice"]
    statement := "Whatever the __buffer__ of extend's argument does to self, the result has no uninitialized byte: refuted, lo is computed before PyObject_GetBuffer and not clamped after it."
    source := "invariant: Python code cannot read uninitialized memory", status := .refuted
    prop := ``ExtendInitialised, thm := some ``extendInitialised_refuted
    bug := some "bytesobj-bytearray-extend-buffer-shrink" },
  { id := "bytesobj-bytearray-alloc-failure", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["PyByteArray_FromStringAndSize", "bytearray_dealloc"]
    statement := "An allocation failure in PyByteArray_FromStringAndSize is only a MemoryError: refuted, bytearray_dealloc reads ob_exports before it is set."
    source := "invariant: no read of uninitialized memory", status := .refuted
    prop := ``AllocFailureSilent, thm := some ``allocFailureSilent_refuted
    bug := some "bytesobj-bytearray-alloc-failure-exports" },
  { id := "bytesobj-bytearray-init-iterator", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray___init___impl"]
    statement := "One append of the iterator loop of __init__ keeps a valid buffer layout: refuted, its capacity test ignores ob_start - ob_bytes, which an iterator can move."
    source := "invariant: every write stays inside the allocation", status := .refuted
    prop := ``InitLoopKeepsLayout, thm := some ``initLoopKeepsLayout_refuted
    bug := some "bytesobj-bytearray-init-iterator-ignores-start" },
  { id := "bytesobj-bytearray-init-fresh-layout", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray___init___impl"]
    statement := "With ob_start == ob_bytes the same step keeps the layout, so the offset is the whole cause."
    source := "narrowing of bytesobj-bytearray-init-iterator", status := .proven
    prop := ``InitLoopFreshLayout, thm := some ``initLoopFreshLayout_proven },
  { id := "bytesobj-bytearray-setslice", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_setslice_linear", "bytearray_setslice"]
    statement := "For every object and valid range, a successful splice leaves data[:lo] + bytes + data[hi:], through the three branches (advance ob_start, memmove down, grow and memmove up)."
    source := "Doc/library/stdtypes.rst s[i:j] = t", status := .proven
    prop := ``SetsliceSpec, thm := some ``setsliceSpec_proven },
  { id := "bytesobj-bytearray-slice-agrees-list", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_ass_subscript_lock_held", "bytearray_ass_subscript"]
    statement := "b[s] = v succeeds only where list[s] = v does, with the same contents: refuted by an empty value on an extended slice, which deletes."
    source := "Doc/library/stdtypes.rst note: 'If k is not equal to 1, t must have the same length as the slice it is replacing'", status := .refuted
    prop := ``SliceAssignAgreesList, thm := some ``sliceAssignAgreesList_refuted
    bug := some "sequences-array-extended-slice-empty-deletes" },
  { id := "bytesobj-bytearray-slice-nonempty", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_ass_subscript_lock_held", "bytearray_ass_subscript"]
    statement := "With a non-empty value, every successful b[s] = v leaves the contents list[s] = v leaves, for all slices with int parts, extended ones included."
    source := "narrowing of bytesobj-bytearray-slice-agrees-list", status := .proven
    prop := ``SliceAssignAgreesNonempty, thm := some ``sliceAssignAgreesNonempty_proven },
  { id := "bytesobj-bytearray-slice-delete", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_ass_subscript_lock_held", "bytearray_ass_subscript"]
    statement := "Every successful del b[s] leaves the contents del list[s] leaves, for all slices with int parts."
    source := "same operation on two mutable sequences", status := .proven
    prop := ``SliceDeleteAgrees, thm := some ``sliceDeleteAgrees_proven
    notes := "bytearray refuses (BufferError) an extended deletion of an empty slice while exports exist, where del b[3:3] is accepted: _canresize comes before the slicelen == 0 return at bytearrayobject.c:831-836. Modelled; not filed." },
  { id := "bytesobj-bytearray-item", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["_getbytevalue", "bytearray_setitem", "bytearray_setitem_lock_held", "bytearray_ass_subscript_lock_held"]
    statement := "b[i] = v for a byte value sets one position; del b[i] removes it; a value outside range(256) raises ValueError, also before the IndexError of a bad index, so a value checked first cannot be overtaken by a resize."
    source := "Doc/library/stdtypes.rst; GH-91153 comment, bytearrayobject.c:690-691", status := .proven
    prop := ``ItemSpec, thm := some ``itemSpec_proven },
  { id := "bytesobj-bytearray-mutators", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_append_impl", "bytearray_insert_impl", "bytearray_pop_impl", "bytearray_remove_impl",
      "bytearray_reverse_impl", "bytearray_clear_impl"]
    statement := "append, insert, pop act on the contents as the list methods do, reverse is an involution, clear empties, and an item outside range(256) raises ValueError first."
    source := "Doc/library/stdtypes.rst mutable sequence operations", status := .proven
    prop := ``MutatorsSpec, thm := some ``mutatorsSpec_proven },
  { id := "bytesobj-bytearray-concat", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["PyByteArray_Concat", "bytearray_iconcat", "bytearray_iconcat_lock_held", "bytearray_irepeat",
      "bytearray_irepeat_lock_held", "bytearray_extend_impl", "bytearray_copy_impl"]
    statement := "a + b and a += b append the bytes of a buffer; a *= n repeats in place, refusing with exports exactly when the size changes; extend with a plain iterable appends the items; copy has the contents."
    source := "Doc/library/stdtypes.rst common and mutable sequence operations", status := .proven
    prop := ``ConcatSpec2, thm := some ``concatSpec2_proven },
  { id := "bytesobj-bytearray-init", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray___init___impl", "PyByteArray_FromObject", "_PyByteArray_FromBufferObject"]
    statement := "bytearray(x) has the bytes of a buffer, n zeros for an int, nothing with no argument; argument errors match bytes(); a non-empty object with exports refuses __init__."
    source := "docstring, bytearrayobject.c:2836-2848", status := .proven
    prop := ``InitSpec, thm := some ``initSpec_proven },
  { id := "bytesobj-bytearray-iter", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_iter", "bytearrayiter_next", "bytearrayiter_length_hint", "bytearrayiter_reduce", "bytearrayiter_setstate"]
    statement := "The iterator reads the current contents at its index, stops when past the end and then stays stopped whatever happens to the object; the length hint is never negative; __setstate__ clamps above."
    source := "iterator protocol; list iterator, Objects/listobject.c", status := .proven
    prop := ``BaIterSpec, thm := some ``baIterSpec_proven },
  { id := "bytesobj-bytearray-reduce", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["_common_reduce", "bytearray_reduce_impl", "bytearray_reduce_ex_impl"]
    statement := "__reduce_ex__ gives constructor arguments that rebuild the bytes for every protocol: no argument for an empty object, (text, 'latin-1') below protocol 3, (bytes,) from 3 on."
    source := "pickling round trip", status := .proven
    prop := ``ReduceSpec, thm := some ``reduceSpec_proven },
  { id := "bytesobj-bytearray-read-wrappers", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["_bytearray_with_buffer", "bytearray_find_impl", "bytearray_count_impl", "bytearray_index_impl", "bytearray_rfind_impl",
      "bytearray_rindex_impl", "bytearray_startswith_impl", "bytearray_endswith_impl", "bytearray_split_impl", "bytearray_rsplit_impl",
      "bytearray_partition_impl", "bytearray_rpartition_impl", "bytearray_replace_impl", "bytearray_splitlines_impl",
      "bytearray_center", "bytearray_ljust", "bytearray_rjust", "bytearray_zfill", "bytearray_expandtabs", "bytearray_strip_impl"]
    statement := "The read-only bytearray methods run the bytes code on the contents and leave ob_exports as it was; while they run ob_exports is raised, so any callback that tries to resize gets BufferError."
    source := "comment bytearrayobject.c:97; GH-143195 comment, :2627", status := .proven
    prop := ``ReadWrappers, thm := some ``readWrappers_proven
    notes := "The search, split, partition, pad and strip results are compared for bytes and bytearray by difftest/strsearch_diff.py; the entries strsearch-* prove their content." }
]

end PyLean.BytesObj.Bytes
