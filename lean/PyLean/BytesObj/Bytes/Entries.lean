import PyLean.Registry
import PyLean.BytesObj.Bytes.Specs4
import PyLean.BytesObj.Bytes.HeapProps3

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
    source := "docstring, bytes_methods.c:722-726", status := .proven
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
    pyFns := ["_Py_bytes_contains", "bytes_contains"]
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
      "PyBytes_FromFormatV", "bytes_fromformat", "PyBytes_FromFormat", "PyBytes_Size", "PyBytes_AsString", "PyBytes_AsStringAndSize",
      "bytes_length"]
    statement := "PyBytes_FromFormat copies a format with no conversion; PyBytes_Size, PyBytes_AsString and PyBytes_AsStringAndSize report TypeError for non-bytes; without a length pointer an embedded NUL is ValueError; PyBytes_FromStringAndSize copies and refuses a negative size; PyBytes_FromString stops at the first NUL."
    source := "Doc/c-api/bytes.rst", status := .proven
    prop := ``CApiSpec, thm := some ``cApiSpec_proven
    notes := "The difftest calls the real functions through ctypes.pythonapi, including conversions in PyBytes_FromFormat." },
  { id := "bytesobj-bytes-hash-cache", pyFile := "Objects/bytesobject.c"
    pyFns := ["set_ob_shash", "bytes_hash", "bytes_subtype_new", "bytes_alloc", "_PyBytes_Resize"]
    statement := "For any Py_HashBuffer that never returns -1: hash(b) is the hash of the contents whether or not the cache was filled, a second call hits the cache, a subclass copy keeps the cache, and a resize that changes the size invalidates it."
    source := "invariant of ob_shash, Include/cpython/bytesobject.h; bytesobject.c:3404-3414", status := .proven
    prop := ``BytesHashCache, thm := some ``bytesHashCache_proven
    notes := "Generic over the hash function: Py_HashBuffer lives in Python/pyhash.c and has a random seed." },
  { id := "bytesobj-bytes-format-field", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FormatEx", "bytes_mod"]
    statement := "For every flag set, sign, width and length: the writes of a field produce exactly the alloc bytes reserved (the assert at bytesobject.c:1136), so the writer's buffer is neither overrun nor left with a gap."
    source := "bytesobject.c:1136 (assert); invariant", status := .proven
    prop := ``FieldAllocExact, thm := some ``fieldAllocExact_proven },
  { id := "bytesobj-bytes-format-fast-slow", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FormatEx", "formatlong"]
    statement := "%d %i %u %o %x of an exact int with no width, precision or sign flag: the fast path gives the same text as formatlong and the field writer, for every int, including the digit-limit error."
    source := "fast path against slow path of the same conversion, bytesobject.c:924-968", status := .proven
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
    statement := "bool and __index__ objects format as their integer value; %o %x %X refuse a float, and %d a bytes, with TypeError through FORMAT_ERROR; getnextarg stops at the end of the tuple, and a * cannot take a single argument."
    source := "Doc/library/stdtypes.rst, printf-style bytes formatting", status := .proven
    prop := ``FormatLongTypes, thm := some ``formatLongTypes_proven },
  { id := "bytesobj-bytes-format-bad-conv", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FormatEx"]
    statement := "A byte that is no conversion raises the ValueError of the default case, with both positions, for a byte above 127 too."
    source := "the default case, bytesobject.c:1007-1038", status := .proven
    prop := ``BadConvIsValueError, thm := some ``badConvIsValueError_proven },
  { id := "bytesobj-bytes-format-float-error", pyFile := "Objects/bytesobject.c"
    pyFns := ["formatfloat"]
    statement := "%f keeps the exception of PyFloat_AsDouble, and replaces a TypeError by the format's message."
    source := "twin: formatfloat in Objects/unicode_format.c; bytesobject.c:441-449", status := .proven
    prop := ``FloatErrorPreserved, thm := some ``floatErrorPreserved_proven },
  { id := "bytesobj-bytes-format-float-type", pyFile := "Objects/bytesobject.c"
    pyFns := ["formatfloat"]
    statement := "A bytes argument of a float conversion raises the TypeError through FORMAT_ERROR; 2**1024 keeps its OverflowError."
    source := "narrowing of bytesobj-bytes-format-float-error", status := .proven
    prop := ``FloatArgType, thm := some ``floatArgType_proven },
  { id := "bytesobj-bytes-format-star-min", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FormatEx"]
    statement := "A negative * width is a left-justified field of that absolute width; PY_SSIZE_T_MIN and a width outside Py_ssize_t are the OverflowError."
    source := "Doc/library/stdtypes.rst, printf-style formatting: '*' width; bytesobject.c:771-804", status := .proven
    prop := ``NegStarWidth, thm := some ``negStarWidth_proven },
  { id := "bytesobj-bytes-escape-roundtrip", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_DecodeEscape2", "PyBytes_DecodeEscape", "PyBytes_Repr", "bytes_repr", "bytes_str", "bytearray_repr", "bytearray_repr_lock_held"]
    statement := "For every byte string and either quote: decoding the body of the literal repr writes, for bytes and for bytearray, gives back the bytes with no invalid escape, so repr is an inverse of escape_decode."
    source := "repr of bytes is a literal, Doc/library/functions.rst repr", status := .proven
    prop := ``ReprDecodeRoundTrip, thm := some ``reprDecodeRoundTrip_proven
    notes := "On 3.15.2 bytearray's repr quotes as bytes's does: repr(bytearray(b\"'\")) is bytearray(b\"'\")." },
  { id := "bytesobj-bytes-escape-warning", pyFile := "Objects/bytesobject.c"
    pyFns := ["PyBytes_DecodeEscape", "_PyBytes_DecodeEscape2"]
    statement := "An invalid escape keeps the backslash, reports the first bad byte through the warning, and a clean input gives no warning."
    source := "Doc/whatsnew/3.12, invalid escape sequences", status := .proven
    prop := ``EscapeWarning, thm := some ``escapeWarning_proven },
  { id := "bytesobj-bytes-repr-size", pyFile := "Objects/bytesobject.c"
    pyFns := ["PyBytes_Repr", "_Py_bytes_repr"]
    statement := "The sizing loop of PyBytes_Repr and the squotes extra give exactly the length the writing loop produces, for every byte string and both smartquotes settings."
    source := "invariant: PyUnicode_New(newsize) must hold the writes, bytesobject.c:1473", status := .proven
    prop := ``ReprSizeExact, thm := some ``reprSizeExact_proven },
  { id := "bytesobj-bytes-private-find", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_Find", "_PyBytes_ReverseFind"]
    statement := "_PyBytes_Find is stringlib_find for every haystack, needle and offset >= 0: searching one byte less and comparing the last alignment by hand changes nothing."
    source := "comment bytesobject.c:1400", status := .proven
    prop := ``PrivateFindAgrees, thm := some ``privateFindAgrees_proven },
  { id := "bytesobj-bytes-concat", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_Concat", "PyBytes_Concat", "PyBytes_ConcatAndDel"]
    statement := "a + b for bytes-like operands is the concatenation, a TypeError naming both types otherwise, and the in-place and new-object branches of PyBytes_Concat give the same result for every operand."
    source := "fast path against slow path, bytesobject.c:3285-3320", status := .proven
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
    pyFns := ["bytes_compare_eq", "bytes_richcompare"]
    statement := "bytes_richcompare, with its first-byte shortcuts, and bytearray_richcompare agree on every pair of byte strings and every operator; == is list equality and != its negation."
    source := "twins: both implement the comparison of sequences of ints", status := .proven
    prop := ``RichcompareTwins, thm := some ``richcompareTwins_proven },
  { id := "bytesobj-bytes-subscript-twins", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_item", "bytes_subscript", "bytearray_getitem", "bytearray_getitem_lock_held"]
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
    pyFns := ["bytes_join_impl", "PyBytes_Join"]
    statement := "sep.join(items) is the items with sep between them for list, tuple and generator arguments; the first item that is no buffer gives a TypeError naming its position."
    source := "docstring, bytesobject.c:1973-1985", status := .proven
    prop := ``JoinSpec, thm := some ``joinSpec_proven },
  { id := "bytesobj-bytes-translate-twins", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_translate_impl"]
    statement := "bytes.translate and bytearray.translate agree on every input, the no-delete fast loop equals the general loop, and with no table the result is the bytes outside delete."
    source := "twins; fast path against slow path, bytesobject.c:2326-2372", status := .proven
    prop := ``TranslateTwins, thm := some ``translateTwins_proven },
  { id := "bytesobj-bytes-strip-twins", pyFile := "Objects/bytesobject.c"
    pyFns := ["do_xstrip", "do_strip", "do_argstrip", "bytes_lstrip_impl", "bytes_rstrip_impl"]
    statement := "bytes.strip and bytearray.strip strip the same bytes for every byte string and direction, with None (Py_ISSPACE against the six-byte string) and with an explicit set."
    source := "twins", status := .proven
    prop := ``StripTwins, thm := some ``stripTwins_proven },
  { id := "bytesobj-bytes-remove-affix", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_removeprefix_impl", "bytes_removesuffix_impl", "bytearray_removeprefix_impl", "bytearray_removesuffix_impl"]
    statement := "With a non-empty matching affix, the affix and the result rebuild the original; otherwise the original comes back."
    source := "docstrings, bytesobject.c:2437-2441, :2475-2479", status := .proven
    prop := ``RemoveAffix, thm := some ``removeAffix_proven },
  { id := "bytesobj-bytes-decode", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_decode_impl"]
    statement := "For every byte string, s.decode('latin-1') is the code points of the bytes and bytes(text, 'latin-1') inverts it; 'ascii' accepts exactly the strings below 128."
    source := "Doc/library/codecs.rst", status := .proven
    prop := ``DecodeRoundTrip, thm := some ``decodeRoundTrip_proven
    notes := "Two codecs stand for the codec registry, which is out of this module's scope; decode itself only forwards." },
  { id := "bytesobj-bytes-fromhex-roundtrip", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FromHex", "bytes_fromhex_impl", "bytes_hex_impl"]
    statement := "bytes.fromhex(b.hex()) == b for every byte string."
    source := "docstrings, bytesobject.c:2611-2614, :2752-2763", status := .proven
    prop := ``FromHexRoundTrip, thm := some ``fromHexRoundTrip_proven },
  { id := "bytesobj-bytes-fromhex-tail", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FromHex"]
    statement := "fromhex of a view does not depend on what follows it in memory: the parser tests end before every read."
    source := "invariant: a function reads only the buffer it was given", status := .proven
    prop := ``FromHexIgnoresTail, thm := some ``fromHexIgnoresTail_proven },
  { id := "bytesobj-bytes-fromhex-terminated", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FromHex"]
    statement := "For a NUL-terminated argument the odd digit is reported: one hex digit in bytes or bytearray raises ValueError."
    source := "bytesobject.c:2703-2707", status := .proven
    prop := ``FromHexTerminated, thm := some ``fromHexTerminated_proven },
  { id := "bytesobj-bytes-hex-sep", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_hex_impl"]
    statement := "hex(sep, k): dropping the separators gives the plain hex digits, whether the groups count from the left or the right, for every number of chunks."
    source := "docstring, bytesobject.c:2749-2763", status := .proven
    prop := ``HexSepFilter, thm := some ``hexSepFilter_proven },
  { id := "bytesobj-bytes-new", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_new_impl", "_PyBytes_FromBuffer", "_PyBytes_FromTuple", "_PyBytes_FromIterator", "PyBytes_FromObject"]
    statement := "bytes(x): a list, a tuple and a generator of ints in range(256) give those bytes (three C loops); an int n >= 0 gives n zero bytes and a negative one ValueError; a str without an encoding is TypeError; a buffer gives its contents; a bad item stops with ValueError."
    source := "docstring, bytesobject.c:3201-3212", status := .proven
    prop := ``BytesNewSpec, thm := some ``bytesNewSpec_proven },
  { id := "bytesobj-bytes-iter", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_iter", "striter_next", "striter_len", "striter_reduce", "striter_setstate"]
    statement := "iter(b) yields the bytes in order and then stops for good; __length_hint__ counts what is left; __setstate__ clamps into [0, len]; rebuilding from __reduce__ restores the iterator."
    source := "iterator protocol; pickling round trip", status := .proven
    prop := ``BytesIterSpec, thm := some ``bytesIterSpec_proven
    notes := "bytes clamps a negative state to 0 and bytearray to -1, which means exhausted, as the list iterator does; recorded in the two models, not filed." },
  { id := "bytesobj-bytes-writer", pyFile := "Objects/bytesobject.c"
    pyFns := ["byteswriter_allocated", "byteswriter_resize", "byteswriter_create", "PyBytesWriter_Create",
      "_PyBytesWriter_CreateByteArray", "PyBytesWriter_Resize", "PyBytesWriter_Grow", "PyBytesWriter_WriteBytes",
      "PyBytesWriter_GrowAndUpdatePointer", "_PyBytesWriter_ResizeAndUpdatePointer", "_PyBytesWriter_ResizeToAllocated"]
    statement := "A successful Create, Resize or Grow leaves size where it was asked to be with room for it, from any writer with 0 <= size <= allocated; WriteBytes appends the data too."
    source := "invariant: every *res++ of a caller stays inside the buffer; byteswriter_check_consistency, bytesobject.c:3696-3718", status := .proven
    prop := ``WriterInvariant, thm := some ``writerInvariant_proven },
  { id := "bytesobj-bytes-writer-finish", pyFile := "Objects/bytesobject.c"
    pyFns := ["PyBytesWriter_FinishWithSize", "PyBytesWriter_Finish", "PyBytesWriter_FinishWithPointer"]
    statement := "Finishing refuses a negative size and one above size, succeeds at any size up to that of a writer as Create left it, for bytes and bytearray, and gives back what the caller wrote."
    source := "bytesobject.c:3864-3937", status := .proven
    prop := ``WriterFinish, thm := some ``writerFinish_proven },
  { id := "bytesobj-bytes-writer-growth", pyFile := "Objects/bytesobject.c"
    pyFns := ["byteswriter_resize", "byteswriter_create", "PyBytesWriter_Create", "PyBytesWriter_Resize", "PyBytesWriter_Grow"]
    statement := "A writer does not fail below 2^46 bytes from any state, for bytes or bytearray, and refuses a negative size, a shrink past 0 and a grow past PY_SSIZE_T_MAX."
    source := "bytesobject.c:3730-3835, :3958-4023", status := .proven
    prop := ``WriterGrowth, thm := some ``writerGrowth_proven },
  { id := "bytesobj-bytes-writer-format", pyFile := "Objects/bytesobject.c"
    pyFns := ["PyBytesWriter_Format"]
    statement := "PyBytesWriter_Format adds what bytes_fromformat writes, and on an error leaves the size where it was and adds nothing."
    source := "bytesobject.c:4063-4085", status := .proven
    prop := ``WriterFormatRules, thm := some ``writerFormatRules_proven },
  { id := "bytesobj-bytes-resize-rules", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_ResizeKeepOnError", "bytes_resize_inplace", "_PyBytes_Resize"]
    statement := "A negative size is refused, the same size and size 0 cannot fail, and otherwise resizing fails as _PyBytes_FromSize does."
    source := "bytesobject.c:3358-3484", status := .proven
    prop := ``BytesResizeRules, thm := some ``bytesResizeRules_proven },
  { id := "bytesobj-bytes-mul-specialized", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_repeat"]
    statement := "A specialized b * n behaves as the generic one: refuted for an int outside Py_ssize_t, whose OverflowError has another message."
    source := "twin: sequence_repeat against seq_int_multiply; PEP 659", status := .refuted
    prop := ``SpecializedRepeatAgrees, thm := some ``specializedRepeatAgrees_refuted
    bug := some "bytesobj-seq-repeat-specialized-overflow-message" },
  { id := "bytesobj-bytes-mul-specialized-range", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_repeat"]
    statement := "For a count in Py_ssize_t the specialized * is the generic one."
    source := "narrowing of bytesobj-bytes-mul-specialized", status := .proven
    prop := ``SpecializedRepeatInRange, thm := some ``specializedRepeatInRange_proven },
  { id := "bytesobj-bytes-iteritem", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_iteritem"]
    statement := "bytes_iteritem gives what striter_next gives at each index, and stops at the end."
    source := "twin: the two iteration paths of a for loop", status := .proven
    prop := ``IterItemAgrees, thm := some ``iterItemAgrees_proven },
  { id := "bytesobj-bytearray-take-bytes", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_take_bytes_impl"]
    statement := "take_bytes(n) gives the first bytes and leaves the rest in a valid layout, with the refusals for a count out of range, an export, a non-integer and an int too large."
    source := "Doc/library/stdtypes.rst, bytearray.take_bytes; bytearrayobject.c:1614-1688", status := .proven
    prop := ``TakeBytesSpec, thm := some ``takeBytesSpec_proven },
  { id := "bytesobj-bytearray-resize-wf", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_resize_lock_held", "bytearray_reinit_from_bytes", "PyByteArray_Resize", "bytearray_resize_impl", "PyByteArray_AsString",
      "bytearray_length", "bytearray_alloc", "bytearray_sizeof_impl"]
    statement := "For every object with a valid layout and every request, a successful resize gives the requested size and a valid layout (data and terminator inside ob_alloc), keeps the common bytes and the export count."
    source := "invariant: bytearray_resize_lock_held; __alloc__ and __sizeof__ expose ob_alloc, which the difftest compares", status := .proven
    prop := ``ResizeWF, thm := some ``resizeWF_proven },
  { id := "bytesobj-bytearray-export-rule", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["_canresize", "bytearray_resize_lock_held"]
    statement := "A resize to the same size always works; any other resize of an object with exports raises BufferError('Existing exports of data: object cannot be re-sized'), after the ValueError for a negative size; with no exports a size that fits in memory succeeds."
    source := "Doc/c-api/bytearray.rst; bytearrayobject.c:127-136", status := .proven
    prop := ``ExportRule, thm := some ``exportRule_proven },
  { id := "bytesobj-bytearray-init-initialised", pyFile := "Objects/bytearrayobject.c"
    pyFns := []
    statement := "After any b.__init__(items) on a fresh object, also a failed one, every byte is a value; a refused int leaves the object empty, with the exception of the refusal."
    source := "invariant: Python code cannot read uninitialized memory; bytearrayobject.c:1119-1124", status := .proven
    prop := ``InitInitialised, thm := some ``initInitialised_proven },
  { id := "bytesobj-bytearray-extend-initialised", pyFile := "Objects/bytearrayobject.c"
    pyFns := []
    statement := "Whatever the __buffer__ of extend's argument does to self, the bytes go in at the old end clamped to the new one, so no gap is left."
    source := "invariant: Python code cannot read uninitialized memory; gh-153578", status := .proven
    prop := ``ExtendInitialised, thm := some ``extendInitialised_proven },
  { id := "bytesobj-bytearray-alloc-failure", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["PyByteArray_FromStringAndSize", "bytearray_dealloc"]
    statement := "A new bytearray has no exports, so bytearray_dealloc reports nothing; a success has the size asked for in a bytes object of that size; the failures are OverflowError above PyByteArray_SIZE_MAX and MemoryError."
    source := "invariant: no read of uninitialized memory; bytearrayobject.c:184-189", status := .proven
    prop := ``AllocFailureSilent, thm := some ``allocFailureSilent_proven },
  { id := "bytesobj-bytearray-shrink-failure", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_setslice_linear", "bytearray_resize_storage"]
    statement := "A failed del b[:k] leaves a valid layout: refuted, the failure path subtracts the shrink from an ob_start that bytearray_resize_storage already reset."
    source := "invariant: every access stays inside the allocation; comment at bytearrayobject.c:639-647", status := .refuted
    prop := ``ShrinkFailureKeepsLayout, thm := some ``shrinkFailureKeepsLayout_refuted
    bug := some "bytesobj-bytearray-shrink-failure-start" },
  { id := "bytesobj-bytearray-resize-failure", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_resize_lock_held", "bytearray_resize_storage"]
    statement := "A failed resize keeps the contents and a valid layout, with the offset at 0 once the storage step has started."
    source := "bytearrayobject.c:236-258", status := .proven
    prop := ``ResizeFailureLayout, thm := some ``resizeFailureLayout_proven },
  { id := "bytesobj-bytearray-alloc-sizeof", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_alloc", "bytearray_sizeof_impl"]
    statement := "__alloc__ counts the bytes object when there is storage and __sizeof__ adds the object size."
    source := "bytearrayobject.c:2605-2612 and :2813-2820", status := .proven
    prop := ``AllocSizeofSpec, thm := some ``allocSizeofSpec_proven },
  { id := "bytesobj-bytearray-init-iterator", pyFile := "Objects/bytearrayobject.c"
    pyFns := []
    statement := "One append of the iterator loop of __init__ keeps a valid buffer layout: refuted, its capacity test ignores ob_start - ob_bytes, which an iterator can move."
    source := "invariant: every write stays inside the allocation", status := .refuted
    prop := ``InitLoopKeepsLayout, thm := some ``initLoopKeepsLayout_refuted
    bug := some "bytesobj-bytearray-init-iterator-ignores-start" },
  { id := "bytesobj-bytearray-init-fresh-layout", pyFile := "Objects/bytearrayobject.c"
    pyFns := []
    statement := "With ob_start == ob_bytes the same step keeps the layout, so the offset is the whole cause."
    source := "narrowing of bytesobj-bytearray-init-iterator", status := .proven
    prop := ``InitLoopFreshLayout, thm := some ``initLoopFreshLayout_proven },
  { id := "bytesobj-bytearray-setslice", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_setslice_linear"]
    statement := "For every object and valid range, a successful splice leaves data[:lo] + bytes + data[hi:], through the three branches (advance ob_start, memmove down, grow and memmove up)."
    source := "Doc/library/stdtypes.rst s[i:j] = t", status := .proven
    prop := ``SetsliceSpec, thm := some ``setsliceSpec_proven },
  { id := "bytesobj-bytearray-slice-agrees-list", pyFile := "Objects/bytearrayobject.c"
    pyFns := []
    statement := "b[s] = v succeeds only where list[s] = v does, with the same contents: refuted by an empty value on an extended slice, which deletes."
    source := "Doc/library/stdtypes.rst note: 'If k is not equal to 1, t must have the same length as the slice it is replacing'", status := .refuted
    prop := ``SliceAssignAgreesList, thm := some ``sliceAssignAgreesList_refuted
    bug := some "sequences-array-extended-slice-empty-deletes" },
  { id := "bytesobj-bytearray-slice-nonempty", pyFile := "Objects/bytearrayobject.c"
    pyFns := []
    statement := "With a non-empty value, every successful b[s] = v leaves the contents list[s] = v leaves, for all slices with int parts, extended ones included."
    source := "narrowing of bytesobj-bytearray-slice-agrees-list", status := .proven
    prop := ``SliceAssignAgreesNonempty, thm := some ``sliceAssignAgreesNonempty_proven },
  { id := "bytesobj-bytearray-slice-delete", pyFile := "Objects/bytearrayobject.c"
    pyFns := []
    statement := "Every successful del b[s] leaves the contents del list[s] leaves, for all slices with int parts."
    source := "same operation on two mutable sequences", status := .proven
    prop := ``SliceDeleteAgrees, thm := some ``sliceDeleteAgrees_proven
    notes := "bytearray refuses (BufferError) an extended deletion of an empty slice while exports exist, where del b[3:3] is accepted: _canresize comes before the slicelen == 0 return at bytearrayobject.c:887-892. Modelled; not filed." },
  { id := "bytesobj-bytearray-item", pyFile := "Objects/bytearrayobject.c"
    pyFns := []
    statement := "b[i] = v for a byte value sets one position; del b[i] removes it; a value outside range(256) raises ValueError, also before the IndexError of a bad index, so a value checked first cannot be overtaken by a resize."
    source := "Doc/library/stdtypes.rst; GH-91153 comment, bytearrayobject.c:746-747", status := .proven
    prop := ``ItemSpec, thm := some ``itemSpec_proven },
  { id := "bytesobj-bytearray-mutators", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_pop_impl", "bytearray_reverse_impl", "bytearray_clear_impl", "bytearray_append_impl",
      "bytearray_insert_impl"]
    statement := "append, insert, pop act on the contents as the list methods do, reverse is an involution, clear empties, and an item outside range(256) raises ValueError first."
    source := "Doc/library/stdtypes.rst mutable sequence operations", status := .proven
    prop := ``MutatorsSpec, thm := some ``mutatorsSpec_proven },
  { id := "bytesobj-bytearray-concat", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_irepeat", "bytearray_irepeat_lock_held", "bytearray_copy_impl"]
    statement := "a + b and a += b append the bytes of a buffer; a *= n repeats in place, refusing with exports exactly when the size changes; extend with a plain iterable appends the items; copy has the contents."
    source := "Doc/library/stdtypes.rst common and mutable sequence operations", status := .proven
    prop := ``ConcatSpec2, thm := some ``concatSpec2_proven },
  { id := "bytesobj-bytearray-init", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_new", "PyByteArray_FromObject", "_PyByteArray_FromBufferObject"]
    statement := "bytearray(x) has the bytes of a buffer, n zeros for an int, nothing with no argument; argument errors match bytes(); a non-empty object with exports refuses __init__."
    source := "docstring, bytearrayobject.c:2954-2966", status := .proven
    prop := ``InitSpec, thm := some ``initSpec_proven },
  { id := "bytesobj-bytearray-iter", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_iter", "bytearrayiter_next", "bytearrayiter_length_hint", "bytearrayiter_setstate"]
    statement := "The iterator reads the current contents at its index, stops when past the end and then stays stopped whatever happens to the object; the length hint is never negative; __setstate__ clamps above."
    source := "iterator protocol; list iterator, Objects/listobject.c", status := .proven
    prop := ``BaIterSpec, thm := some ``baIterSpec_proven },
  { id := "bytesobj-bytearray-reduce", pyFile := "Objects/bytearrayobject.c"
    pyFns := []
    statement := "__reduce_ex__ gives constructor arguments that rebuild the bytes for every protocol: no argument for an empty object, (text, 'latin-1') below protocol 3, (bytes,) from 3 on."
    source := "pickling round trip", status := .proven
    prop := ``ReduceSpec, thm := some ``reduceSpec_proven },
  { id := "bytesobj-bytearray-read-wrappers", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_zfill", "bytearray_expandtabs"]
    statement := "center, ljust, rjust, zfill, replace, expandtabs and splitlines raise no export: the callbacks of their arguments (__index__ of width, count and tabsize, __buffer__ of old and new) run first and may resize the bytearray, and the result is the bytes method on the contents as they left them; replace releases its buffers after the copy."
    source := "twin: the bytes methods of stringlib/transmogrify.h; clinic/bytearrayobject.c.h:858-891, stringlib/clinic/transmogrify.h.h", status := .proven
    prop := ``ReadAfterArgs, thm := some ``readAfterArgs_proven
    notes := "Corrected: an earlier statement said these methods raise ob_exports, which 3.15.2 contradicts (a width.__index__ or old.__buffer__ that resizes self succeeds). Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-copy-twin", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["_bytearray_with_buffer", "bytearray_contains", "bytearray_startswith_impl", "bytearray_endswith_impl",
      "bytearray_split_impl", "bytearray_rsplit_impl", "bytearray_hex_impl", "bytearray_richcompare"]
    statement := "With arguments that run no Python code, x in b, startswith/endswith of one buffer, split and rsplit, hex() and comparison give what the bytes methods give on the contents (_Py_bytes_contains, _Py_bytes_tailmatch, bytes.split, bytes.hex, the byte-string comparison) and leave the object as it was."
    source := "twin: bytes and bytearray share bytes_methods.c, stringlib/split.h and pystrhex.c", status := .proven
    prop := ``CopyTwinBytes, thm := some ``copyTwinBytes_proven
    notes := "Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-remove", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_remove_impl"]
    statement := "remove(c) removes the first occurrence as list.remove does, raises ValueError('value not found in bytearray') when there is none, and with exports refuses a removal with BufferError; for every object below 2^45 bytes."
    source := "Doc/library/stdtypes.rst mutable sequence s.remove(x)", status := .proven
    prop := ``RemoveSpec, thm := some ``removeSpec_proven },
  { id := "bytesobj-bytearray-search-live", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["_bytearray_with_buffer", "bytearray_find_impl", "bytearray_rfind_impl", "bytearray_index_impl",
      "bytearray_rindex_impl", "bytearray_count_impl", "bytearray_startswith_impl", "bytearray_endswith_impl",
      "bytearray_contains"]
    statement := "For every heap and every argument, whatever the __index__ of sub, start and end and the __buffer__ and __release_buffer__ of sub (or of each item of a startswith tuple) do to the bytearray, the search reads through the pointer taken before them exactly the bytes the object holds at that moment: ob_exports keeps the size and the storage, so no read is stale or of freed memory."
    source := "invariant: no read of freed or stale memory; comment bytearrayobject.c:120, gh-142560", status := .proven
    prop := ``SearchReadsLive, thm := some ``searchReadsLive_proven
    notes := "Callbacks are statements on self (in-place writes, resizes, front deletions, taking and releasing views), each through the model of that method; see Heap.lean. Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-search-twin", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["_bytearray_with_buffer", "bytearray_find_impl", "bytearray_rfind_impl", "bytearray_index_impl",
      "bytearray_rindex_impl", "bytearray_count_impl"]
    statement := "With an argument and bounds that run no Python code, bytearray.find, rfind, index, rindex and count are the bytes methods on the contents, and leave the object as it was (ob_exports back where it was)."
    source := "twin: bytes and bytearray share _Py_bytes_find etc. (bytes_methods.c)", status := .proven
    prop := ``SearchTwinBytes, thm := some ``searchTwinBytes_proven
    notes := "Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-strip-release", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_strip_impl_helper", "bytearray_strip_impl"]
    statement := "strip copies the bytes its loops scanned: copying after the argument's __release_buffer__ gives what copying before it gives. Refuted: an in-place write there gives bytearray(b' a ').strip(B()) == bytearray(b' '), and self.clear() there makes the copy read freed memory."
    source := "invariant: no read of freed memory; Doc/library/stdtypes.rst bytearray.strip", status := .refuted
    prop := ``StripCopiesScanned, thm := some ``stripCopiesScanned_refuted
    bug := some "bytesobj-bytearray-strip-release-uaf"
    notes := "Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-strip-norel", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_strip_impl_helper", "bytearray_strip_impl", "bytearray_lstrip_impl", "bytearray_rstrip_impl"]
    statement := "When the argument's release runs no Python code (None, a C buffer, self, or a class whose __release_buffer__ does nothing), strip, lstrip and rstrip are the strip of the contents as the argument's __buffer__ left them, with the six whitespace bytes for None."
    source := "narrowing of bytesobj-bytearray-strip-release; Doc/library/stdtypes.rst bytearray.strip", status := .proven
    prop := ``StripNoRelAgrees, thm := some ``stripNoRelAgrees_proven
    notes := "Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-split-live", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_split_impl", "bytearray_rsplit_impl"]
    statement := "For every heap, separator and maxsplit: with ob_exports raised before sbuf and slen are read, the separator's __buffer__ and __release_buffer__ cannot resize the bytearray, so splitting through sbuf reads the live contents."
    source := "invariant: no stale read; comment bytearrayobject.c:1875", status := .proven
    prop := ``SplitReadsLive, thm := some ``splitReadsLive_proven
    notes := "Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-hex-live", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_hex_impl"]
    statement := "For every heap, separator and bytes_per_sep: argbuf is read before ob_exports is raised, and the separator's __len__ (gh-143195) runs with it raised, so the hexlify loop reads the live contents."
    source := "invariant: no read of freed memory; gh-143195 comment, bytearrayobject.c:2740-2742", status := .proven
    prop := ``HexReadsLive, thm := some ``hexReadsLive_proven
    notes := "Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-rich-live", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_richcompare"]
    statement := "For every heap, operand and operator: self is exported before the other operand's __buffer__ runs, so the memcmp reads the live contents of self."
    source := "invariant: no stale read", status := .proven
    prop := ``RichReadsLive, thm := some ``richReadsLive_proven
    notes := "Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-item-after-index", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["_getbytevalue", "bytearray_subscript_lock_held", "bytearray_subscript", "bytearray_ass_subscript_lock_held",
      "bytearray_ass_subscript", "bytearray_setitem_lock_held", "bytearray_setitem", "bytearray_append_impl",
      "bytearray_remove_impl", "bytearray_insert_impl", "bytearray_take_bytes_impl"]
    statement := "For every heap and every __index__ callback: b[k], b[i] = x, the sq_ass_item b[i] = x, append, remove, insert and take_bytes run the conversion first and then the method on the object as the callback left it, so the position is checked against the size after the callback (GH-91153); an exception of the value's __index__ comes before the IndexError of the position."
    source := "GH-91153 comments, bytearrayobject.c:746-747, :800-801, :1629", status := .proven
    prop := ``ItemAfterIndex, thm := some ``itemAfterIndex_proven
    notes := "The slice branches of subscript and assignment (__index__ of slice parts, a value converted with PyByteArray_FromObject and the slice unpacked again) are modelled and compared by the difftest family bare; their contents are those of bytesobj-bytearray-slice-*. Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-partition-after-sep", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_partition_impl", "bytearray_rpartition_impl", "_PyByteArray_FromBufferObject"]
    statement := "partition and rpartition copy the separator (its __buffer__, then its __release_buffer__) before reading self: the result is the partition of the contents as both callbacks left them; for a C bytes-like separator it is bytes.partition and bytes.rpartition on the contents."
    source := "twin: bytes.partition; bytearrayobject.c:1926-1935", status := .proven
    prop := ``PartitionAfterSep, thm := some ``partitionAfterSep_proven
    notes := "Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-translate-after-args", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_translate_impl"]
    statement := "translate reads self after the table's __buffer__ and before its __release_buffer__: with a table class of 256 bytes the result is the table applied to the contents as __buffer__ left them; with C arguments it is the pure translate of the contents."
    source := "twin: bytes.translate; bytearrayobject.c:1724-1795", status := .proven
    prop := ``TranslateAfterArgs, thm := some ``translateAfterArgs_proven
    notes := "Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-delegates", pyFile := "Objects/bytearrayobject.c"
    pyFns := []
    statement := "For every bytearray, each is* predicate returns the bytes helper's answer on its contents, and each case map returns a new bytearray holding the helper's result (below 2^46 bytes, where the allocation cannot fail); neither changes the object."
    source := "twin: stringlib/ctype.h delegates to the _Py_bytes_* helpers of bytes_methods.c", status := .proven
    prop := ``DelegatesSpec, thm := some ``delegatesSpec_proven
    notes := "Credits no row: it holds for any helper; bytesobj-bytearray-isalnum and the twelve entries after it pin each method." },
  { id := "bytesobj-bytearray-affix", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_removeprefix_impl", "bytearray_removesuffix_impl"]
    statement := "removeprefix/removesuffix of bytearray, which lack the prefix_len > 0 test of bytes, agree with the bytes bodies for every contents and affix; with a prefix class the contents read are those __buffer__ left, and __release_buffer__ runs after."
    source := "twin: bytes_removeprefix_impl, bytesobject.c; bytearrayobject.c:1525-1576", status := .proven
    prop := ``AffixSpec, thm := some ``affixSpec_proven
    notes := "Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-maketrans", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_maketrans_impl"]
    statement := "bytearray.maketrans(frm, to) is _Py_bytes_maketrans of the two buffers as their __buffer__ gave them, both released after."
    source := "bytearrayobject.c:1817-1822", status := .proven
    prop := ``BaMaketransSpec, thm := some ``baMaketransSpec_proven },
  { id := "bytesobj-bytearray-getitem-raw", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_getitem_lock_held", "bytearray_getitem"]
    statement := "sq_item of a bytearray whose bytes are all written is list indexing: the byte at an index in range(len), IndexError('bytearray index out of range') for every other index."
    source := "Doc/library/stdtypes.rst common sequence s[i]", status := .proven
    prop := ``GetItemRawSpec, thm := some ``getItemRawSpec_proven },
  { id := "bytesobj-bytearray-repeat", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_repeat_lock_held", "bytearray_repeat"]
    statement := "b * n: n <= 0 gives an empty bytearray, MemoryError exactly when len(b) > PyByteArray_SIZE_MAX // n, and otherwise (below 2^46 bytes) a new bytearray without exports holding n copies of b."
    source := "Doc/library/stdtypes.rst common sequence s * n; bytearrayobject.c:439-469", status := .proven
    prop := ``BaRepeatSpec, thm := some ``baRepeatSpec_proven },
  { id := "bytesobj-bytearray-iadd-self", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_iconcat_lock_held", "bytearray_iconcat", "bytearray_setslice"]
    statement := "b += x is b.extend(x) for every bytes-like x. Refuted: b += b raises BufferError, because bytearray_iconcat_lock_held exports b as its own argument and then resizes it, where b.extend(b) copies first."
    source := "Doc/library/stdtypes.rst mutable sequence operations: s += t extends s with the contents of t", status := .refuted
    prop := ``IAddIsExtend, thm := some ``iAddIsExtend_refuted
    bug := some "bytesobj-bytearray-iadd-self"
    notes := "Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-iadd-extend-obj", pyFile := "Objects/bytearrayobject.c"
    pyFns := []
    statement := "For a C bytes-like object that is not self, b += x and b.extend(x) give the same result and contents."
    source := "narrowing of bytesobj-bytearray-iadd-self", status := .open
    prop := ``IAddExtendObj
    notes := "Open: the proof has to follow the growth branch of bytearray_setslice_linear (resize, empty memmove, copy) against the resize and copy of iconcat; the difftest family bare compares both. Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-init-steal", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray___init___impl"]
    statement := "bytearray.__init__(s, encoding) leaves the same object whether the codec's result is uniquely referenced (installed as the storage) or not (appended with iconcat). Refuted: a Python codec that resizes self has its bytes dropped (and leaked) on the first path and kept on the second; one that keeps memoryview(self) gets its storage replaced under the export on the first and BufferError on the second."
    source := "invariant: uniqueness of a bytes object is not visible to Python code; exported storage is not replaced (Doc/c-api/bytearray.rst)", status := .refuted
    prop := ``InitPathsAgree, thm := some ``initPathsAgree_refuted
    bug := some "bytesobj-bytearray-init-codec-steal"
    notes := "Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-isalnum", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_isalnum"]
    statement := "For every bytearray, isalnum() is true exactly when it is non-empty and every byte is an ASCII letter or digit ([0-9A-Za-z]); the object is not changed."
    source := "Doc/library/stdtypes.rst bytearray.isalnum; bytearrayobject.c:2098-2106", status := .proven
    prop := ``BaIsalnumSpec, thm := some ``baIsalnumSpec_proven },
  { id := "bytesobj-bytearray-isalpha", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_isalpha"]
    statement := "For every bytearray, isalpha() is true exactly when it is non-empty and every byte is an ASCII letter."
    source := "Doc/library/stdtypes.rst bytearray.isalpha; bytearrayobject.c:2108-2116", status := .proven
    prop := ``BaIsalphaSpec, thm := some ``baIsalphaSpec_proven },
  { id := "bytesobj-bytearray-isascii", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_isascii"]
    statement := "For every bytearray, isascii() is true exactly when every byte is below 128, the empty object included."
    source := "Doc/library/stdtypes.rst bytearray.isascii; bytearrayobject.c:2118-2126", status := .proven
    prop := ``BaIsasciiSpec, thm := some ``baIsasciiSpec_proven },
  { id := "bytesobj-bytearray-isdigit", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_isdigit"]
    statement := "For every bytearray, isdigit() is true exactly when it is non-empty and every byte is an ASCII digit."
    source := "Doc/library/stdtypes.rst bytearray.isdigit; bytearrayobject.c:2128-2136", status := .proven
    prop := ``BaIsdigitSpec, thm := some ``baIsdigitSpec_proven },
  { id := "bytesobj-bytearray-islower", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_islower"]
    statement := "For every bytearray, islower() is true exactly when there is no ASCII capital and at least one ASCII small letter."
    source := "Doc/library/stdtypes.rst bytearray.islower; bytearrayobject.c:2138-2146", status := .proven
    prop := ``BaIslowerSpec, thm := some ``baIslowerSpec_proven },
  { id := "bytesobj-bytearray-isspace", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_isspace"]
    statement := "For every bytearray, isspace() is true exactly when it is non-empty and every byte is one of \\t\\n\\v\\f\\r and space."
    source := "Doc/library/stdtypes.rst bytearray.isspace; bytearrayobject.c:2148-2156", status := .proven
    prop := ``BaIsspaceSpec, thm := some ``baIsspaceSpec_proven },
  { id := "bytesobj-bytearray-istitle", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_istitle"]
    statement := "For every bytearray, istitle() is true exactly when there is an ASCII letter, every capital follows a byte that is not a letter and every small letter follows a letter."
    source := "Doc/library/stdtypes.rst bytearray.istitle; bytearrayobject.c:2158-2166", status := .proven
    prop := ``BaIstitleSpec, thm := some ``baIstitleSpec_proven },
  { id := "bytesobj-bytearray-isupper", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_isupper"]
    statement := "For every bytearray, isupper() is true exactly when there is no ASCII small letter and at least one ASCII capital."
    source := "Doc/library/stdtypes.rst bytearray.isupper; bytearrayobject.c:2168-2176", status := .proven
    prop := ``BaIsupperSpec, thm := some ``baIsupperSpec_proven },
  { id := "bytesobj-bytearray-capitalize", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_capitalize"]
    statement := "capitalize() gives a new bytearray whose first byte is upper-cased and the rest lower-cased (ASCII only), below 2^46 bytes; MemoryError where the copy cannot be allocated; the object is not changed."
    source := "Doc/library/stdtypes.rst bytearray.capitalize; bytearrayobject.c:2203-2211", status := .proven
    prop := ``BaCapitalizeSpec, thm := some ``baCapitalizeSpec_proven },
  { id := "bytesobj-bytearray-swapcase", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_swapcase"]
    statement := "swapcase() gives a new bytearray with ASCII small letters and capitals exchanged, every other byte kept; MemoryError where the copy cannot be allocated."
    source := "Doc/library/stdtypes.rst bytearray.swapcase; bytearrayobject.c:2485-2493", status := .proven
    prop := ``BaSwapcaseSpec, thm := some ``baSwapcaseSpec_proven },
  { id := "bytesobj-bytearray-title", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_title"]
    statement := "title() gives a new bytearray in which a small letter after a non-letter becomes a capital and a capital after a letter becomes small, every other byte kept; MemoryError where the copy cannot be allocated."
    source := "Doc/library/stdtypes.rst bytearray.title; bytearrayobject.c:2495-2503", status := .proven
    prop := ``BaTitleSpec, thm := some ``baTitleSpec_proven },
  { id := "bytesobj-bytearray-upper", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_upper"]
    statement := "upper() gives a new bytearray in which each byte 97-122 is 32 less and every other byte kept; MemoryError where the copy cannot be allocated."
    source := "Doc/library/stdtypes.rst bytearray.upper; bytearrayobject.c:2505-2513", status := .proven
    prop := ``BaUpperSpec, thm := some ``baUpperSpec_proven },
  { id := "bytesobj-bytearray-lower", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_lower"]
    statement := "lower() gives a new bytearray in which each byte 65-90 is 32 more and every other byte kept; MemoryError where the copy cannot be allocated."
    source := "Doc/library/stdtypes.rst bytearray.lower; bytearrayobject.c:2515-2523", status := .proven
    prop := ``BaLowerSpec, thm := some ``baLowerSpec_proven },
  { id := "bytesobj-bytearray-just-fill", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_center", "bytearray_ljust", "bytearray_rjust"]
    statement := "center, ljust and rjust convert width first (its __index__ may change the object), then fillchar, which must be a bytes (a subclass by its stored size) or bytearray of length 1, else TypeError with the clinic's message (self measured after width's callback); the result is the bytes method on the contents as width's callback left them."
    source := "stringlib/clinic/transmogrify.h.h:116-139, :184-207, :252-275; Python/getargs.c:663-670", status := .proven
    prop := ``BaJustSpec, thm := some ``baJustSpec_proven
    notes := "Scope: callbacks act on self only." },
  { id := "bytesobj-bytearray-replace-count", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_replace_impl"]
    statement := "replace takes the buffer of old, then of new, then converts count (whose __index__ may change the object), reads the object only then, and releases both buffers after, also when count raises; the result is bytes.replace on the contents as the three callbacks left them."
    source := "clinic/bytearrayobject.c.h:858-891; bytearrayobject.c:1842-1850", status := .proven
    prop := ``BaReplaceSpec, thm := some ``baReplaceSpec_proven
    notes := "Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-splitlines-keepends", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_splitlines_impl"]
    statement := "splitlines runs PyObject_IsTrue(keepends) before reading the object: a __bool__ that changes the object is seen, one that raises is the result, self is true when not empty; the result is bytes.splitlines on the contents then, and with keepends the lines join back to them."
    source := "clinic/bytearrayobject.c.h:1657-1674; bytearrayobject.c:2674-2682", status := .proven
    prop := ``BaSplitlinesSpec, thm := some ``baSplitlinesSpec_proven
    notes := "Scope: callbacks act on self only." },
  { id := "bytesobj-bytearray-tailmatch", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_startswith_impl", "bytearray_endswith_impl"]
    statement := "With arguments that run no Python code, startswith and endswith of a tuple are bytes's tuple loop on the contents (true at the first match, the first non-buffer item's TypeError unreplaced when no earlier item matched), and one non-buffer object gets the method's own TypeError message."
    source := "twin: _Py_bytes_tailmatch, bytes_methods.c:675-706", status := .proven
    prop := ``BaTailmatchSpec, thm := some ``baTailmatchSpec_proven },
  { id := "bytesobj-bytearray-rich-bytes", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_richcompare"]
    statement := "bytearray comparison with an object that runs no Python code is bytes comparison of the two byte strings (== is equality of the contents), and NotImplemented without the buffer protocol; the object is left as it was."
    source := "twin: bytes_richcompare; bytearrayobject.c:1222-1275", status := .proven
    prop := ``BaRichSpec, thm := some ``baRichSpec_proven },
  { id := "bytesobj-bytearray-append", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_append_impl"]
    statement := "append converts the item first (its exception passes out); with exports then present it raises BufferError, otherwise it appends the byte as list.append does."
    source := "Doc/library/stdtypes.rst s.append(x); bytearrayobject.c:2189-2201", status := .proven
    prop := ``BaAppendSpec, thm := some ``baAppendSpec_proven },
  { id := "bytesobj-bytearray-insert", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_insert_impl"]
    statement := "insert converts index, then item (each exception passing out); with exports then present it raises BufferError, otherwise it inserts as list.insert does."
    source := "Doc/library/stdtypes.rst s.insert(i, x); bytearrayobject.c:2074-2096", status := .proven
    prop := ``BaInsertSpec, thm := some ``baInsertSpec_proven },
  { id := "bytesobj-bytearray-pop", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_pop_impl"]
    statement := "pop raises IndexError on an empty object and outside the range (a negative index counted from the end), BufferError with exports, and otherwise returns and removes the byte; the clinic converts index first, -1 when absent."
    source := "Doc/library/stdtypes.rst s.pop([i]); bytearrayobject.c:2359-2388", status := .proven
    prop := ``BaPopSpec, thm := some ``baPopSpec_proven },
  { id := "bytesobj-bytearray-from-size", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["PyByteArray_FromStringAndSize", "bytearray_reinit_from_bytes"]
    statement := "PyByteArray_FromStringAndSize raises SystemError for a negative size and succeeds below 2^46 bytes with the bytes copied (or unwritten for NULL), no exports, ob_start == ob_bytes and ob_alloc the size."
    source := "Doc/c-api/bytearray.rst PyByteArray_FromStringAndSize; bytearrayobject.c:55-67, :168-206", status := .proven
    prop := ``BaFromStringAndSizeSpec, thm := some ``baFromStringAndSizeSpec_proven },
  { id := "bytesobj-bytearray-copy", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_copy_impl"]
    statement := "copy() of every bytearray below 2^46 bytes succeeds with a new object holding the contents and no exports, the empty object included."
    source := "Doc/library/stdtypes.rst s.copy(); bytearrayobject.c:1382-1388", status := .proven
    prop := ``BaCopySpec, thm := some ``baCopySpec_proven },
  { id := "bytesobj-bytearray-clear", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_clear_impl"]
    statement := "clear() leaves an empty object alone, raises BufferError on a non-empty one with exports, and otherwise empties it onto the empty bytes."
    source := "Doc/library/stdtypes.rst s.clear(); bytearrayobject.c:1366-1373", status := .proven
    prop := ``BaClearSpec, thm := some ``baClearSpec_proven },
  { id := "bytesobj-bytearray-irepeat", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_irepeat_lock_held", "bytearray_irepeat"]
    statement := "b *= n: n == 1 returns b untouched; n <= 0 empties it; MemoryError exactly when len(b) > PyByteArray_SIZE_MAX // n; BufferError with exports whenever the size changes; otherwise b holds n copies of its old contents."
    source := "Doc/library/stdtypes.rst s *= n; bytearrayobject.c:471-506", status := .proven
    prop := ``BaIRepeatSpec, thm := some ``baIRepeatSpec_proven },
  { id := "bytesobj-bytearray-resize-strategy", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_resize_lock_held", "PyByteArray_Resize", "bytearray_reinit_from_bytes"]
    statement := "A resize without exports keeps the first bytes and sets ob_alloc by the strategy: quick exit inside the buffer down to half, exact size below half, n + n//8 + (3 or 6) up to 1.125 times, exact beyond; 0 installs the empty bytes; an overallocation above PyByteArray_SIZE_MAX is MemoryError; bytearray(10).append(1) leaves __alloc__() at 51."
    source := "observable through __alloc__(); bytearrayobject.c:294-342", status := .proven
    prop := ``BaResizeStrategy, thm := some ``baResizeStrategy_proven },
  { id := "bytesobj-bytearray-setslice-linear-ok", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_setslice_linear"]
    statement := "For 0 <= lo <= hi <= len, a splice that keeps the size succeeds even with exports, one that changes it raises BufferError with exports, and without exports every splice below 2^45 bytes succeeds through each branch with data[:lo] + bytes + data[hi:]."
    source := "Doc/library/stdtypes.rst s[i:j] = t; bytearrayobject.c:601-684", status := .proven
    prop := ``BaSetsliceLinearOk, thm := some ``baSetsliceLinearOk_proven },
  { id := "bytesobj-bytearray-subscript-slice", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_subscript_lock_held", "bytearray_subscript"]
    statement := "b[start:stop:step] with __index__ parts runs the step's, then the start's, then the stop's (a zero step raising before the others), and is bytes's slice of the contents as they left them."
    source := "PySlice_Unpack, Objects/sliceobject.c:219-262; bytearrayobject.c:550-581", status := .proven
    prop := ``BaSubscriptSlice, thm := some ``baSubscriptSlice_proven
    notes := "Scope: callbacks act on self only." },
  { id := "bytesobj-bytearray-ass-subscript-index", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_ass_subscript_lock_held", "bytearray_ass_subscript"]
    statement := "b[k] = v and del b[k] with an __index__ key run the key's callback, then the value's, and check the position against the size both left; a key that is neither an index nor a slice is the TypeError."
    source := "GH-91153 comments, bytearrayobject.c:791-827", status := .proven
    prop := ``BaAssSubIndex, thm := some ``baAssSubIndex_proven
    notes := "The index branch; the slice branch is bytesobj-bytearray-ass-subscript-slice. Scope: callbacks act on self only." },
  { id := "bytesobj-bytearray-buffer-export", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_getbuffer_lock_held", "bytearray_getbuffer", "bytearray_releasebuffer"]
    statement := "A NULL view is the BufferError of getbuffer; PyBUF_READ and PyBUF_WRITE are refused by PyBuffer_FillInfo with SystemError; any other request exports the contents writable and raises ob_exports by one; while it is held every resize to another size is refused, and after the release every resize does what it did before."
    source := "Doc/c-api/buffer.rst; bytearrayobject.c:69-106, Objects/abstract.c:774-810", status := .proven
    prop := ``BaBufferExport, thm := some ``baBufferExport_proven },
  { id := "bytesobj-bytearray-alloc-report", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_alloc", "bytearray_sizeof_impl"]
    statement := "__alloc__() is ob_alloc + 33 with storage and 0 without, __sizeof__() the type's basic size (64) plus that; bytearray() reports 0, bytearray(n) reports n + 33, bytearray(10).append(1) reports 51."
    source := "Doc/library/stdtypes.rst bytearray; bytearrayobject.c:2605-2613, :2813-2823", status := .proven
    prop := ``BaAllocReport, thm := some ``baAllocReport_proven },
  { id := "bytesobj-bytearray-resize-method", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_resize_impl"]
    statement := "resize(n) converts n first; a negative n is ValueError, the same size changes nothing, another size raises BufferError with exports, and otherwise the first bytes are kept and the new ones are zero."
    source := "Doc/library/stdtypes.rst bytearray.resize; bytearrayobject.c:1588-1602", status := .proven
    prop := ``BaResizeMethodSpec, thm := some ``baResizeMethodSpec_proven },
  { id := "bytesobj-bytearray-reverse-loop", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_reverse_impl"]
    statement := "The head/tail swap loop of reverse() leaves the contents reversed for every object, the odd middle byte in place."
    source := "Doc/library/stdtypes.rst s.reverse(); bytearrayobject.c:2033-2050", status := .proven
    prop := ``BaReverseSpec, thm := some ``baReverseSpec_proven },
  { id := "bytesobj-bytearray-iter-full", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_iter", "bytearrayiter_next", "bytearrayiter_length_hint", "bytearrayiter_setstate"]
    statement := "list(iter(b)) is list(b); on an unchanged object the length hint is the number of items still to come; __setstate__ takes only an int (TypeError, or OverflowError outside Py_ssize_t), ignores an exhausted iterator, and otherwise sets the index clamped to [-1, len], after which the iterator yields b[k:]."
    source := "iterator protocol; bytearrayobject.c:3042-3132, :3179-3195", status := .proven
    prop := ``BaIterFull, thm := some ``baIterFull_proven },
  { id := "bytesobj-bytearray-ass-subscript-slice", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_ass_subscript_lock_held", "bytearray_ass_subscript"]
    statement := "del b[s] and b[s] = bytearray(...) with __index__ slice parts unpack once and splice as the pure assignment does; a bytes value is copied with PyByteArray_FromObject and the function called again, so every part's __index__ runs twice; a number or str value is the TypeError after one unpacking."
    source := "bytearrayobject.c:828-940; PySlice_Unpack, Objects/sliceobject.c:219-262", status := .proven
    prop := ``BaAssSubSlice, thm := some ``baAssSubSlice_proven
    notes := "Scope: callbacks act on self only. Together with bytesobj-bytearray-ass-subscript-index, which has the index branch." },
  { id := "bytesobj-bytearray-setslice-values", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_setslice"]
    statement := "bytearray_setslice deletes for NULL, copies self first, refuses a value without the buffer protocol with TypeError, runs a value's __buffer__ before clamping both bounds to the size it left (gh-153578), splices with bytearray_setslice_linear and releases the buffer after."
    source := "gh-153578; bytearrayobject.c:686-738", status := .proven
    prop := ``BaSetsliceSpec, thm := some ``baSetsliceSpec_proven
    notes := "Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-init-paths", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray___init___impl"]
    statement := "__init__ with exports raises BufferError and changes nothing; otherwise it empties the object and then gives nothing, n zero bytes for an int n > 0, ValueError for a negative count, OverflowError outside Py_ssize_t, a buffer's bytes, and a list of ints in range(256) through the fast path."
    source := "docstring, bytearrayobject.c:2954-2966; bytearrayobject.c:982-1128", status := .proven
    prop := ``BaInitESpec, thm := some ``baInitESpec_proven
    notes := "The iterator loop (:1142-1172) is in bytesobj-bytearray-init-iterator; the str branch in bytesobj-bytearray-init-steal." },
  { id := "bytesobj-bytearray-buffer-flags", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_getbuffer_lock_held", "bytearray_getbuffer"]
    statement := "No flag of inspect.BufferFlags makes a bytearray buffer request fail with SystemError. Refuted: PyBuffer_FillInfo answers PyBUF_READ and PyBUF_WRITE with PyErr_BadInternalCall, so bytearray().__buffer__(inspect.BufferFlags.READ) raises SystemError, where memoryview accepts the flag."
    source := "Doc/library/inspect.rst:1877-1901 (flags that can be passed to __buffer__); invariant: no internal error from a documented call", status := .refuted
    prop := ``BufferFlagsNoSystemError, thm := some ``bufferFlagsNoSystemError_refuted
    bug := some "bytesobj-bytearray-buffer-flags-systemerror" },
  { id := "bytesobj-bytearray-hex-sep", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_hex_impl"]
    statement := "hex(sep, n) with a separator that runs no Python code: a one-byte bytes or one-character str below 128 gives bytes.hex of the contents with it, grouped by n; another length is ValueError('sep must be length 1.'), a non-ASCII one ValueError('sep must be ASCII.'), an object without a length the TypeError of len(); the object is left as it was."
    source := "twin: bytes.hex; Doc/library/stdtypes.rst bytes.hex; Python/pystrhex.c:118-150", status := .proven
    prop := ``BaHexSepSpec, thm := some ``baHexSepSpec_proven },
  { id := "bytesobj-bytearray-ass-extended", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_ass_subscript_lock_held", "bytearray_ass_subscript"]
    statement := "The extended-slice branch: a value of the slice's non-zero length is stored and succeeds even with exports; another non-zero length is the ValueError naming both sizes; an empty value deletes, which with exports is BufferError even for an empty slice, and without exports an empty slice changes nothing."
    source := "bytearrayobject.c:880-939", status := .proven
    prop := ``BaAssExtendedSpec, thm := some ``baAssExtendedSpec_proven },
  { id := "bytesobj-bytearray-ass-extended-ok", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_ass_subscript_lock_held", "bytearray_ass_subscript"]
    statement := "b[s] = v for an extended slice and a non-empty value of the slice's length succeeds on every object and slice, with the contents list[s] = v leaves; any other non-zero length raises the ValueError."
    source := "Doc/library/stdtypes.rst s[i:j:k] = t; bytearrayobject.c:924-937", status := .proven
    prop := ``BaAssSliceExtOk, thm := some ``baAssSliceExtOk_proven },
  { id := "bytesobj-bytearray-ass-extended-del", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_ass_subscript_lock_held", "bytearray_ass_subscript"]
    statement := "del b[s] for an extended slice of an object without exports succeeds for every slice (the compaction loop, the tail move and the shrink stay in bounds) and leaves what del list[s] leaves."
    source := "Doc/library/stdtypes.rst del s[i:j:k]; bytearrayobject.c:881-922", status := .proven
    prop := ``BaAssSliceDelOk, thm := some ``baAssSliceDelOk_proven },
  { id := "bytesobj-bytearray-ass-values", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_ass_subscript_lock_held", "bytearray_ass_subscript"]
    statement := "b[s] = v for a list of ints, a class with __buffer__ (its __buffer__ then __release_buffer__) and self: the slice is unpacked once, the value copied with PyByteArray_FromObject, and the slice unpacked again for the assignment of the copy."
    source := "bytearrayobject.c:828-862", status := .proven
    prop := ``BaAssSubValues, thm := some ``baAssSubValues_proven
    notes := "Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-init-more", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray___init___impl"]
    statement := "__init__: encoding or errors without a string argument are the TypeErrors; the list fast path's bad value empties the object and raises ValueError; a list of non-int items falls back to the iterator loop; a tuple takes the fast path; a generator's items are all appended in order; a class with __buffer__ gives its bytes, or BufferError when its callback took a view, with __release_buffer__ run after."
    source := "docstring, bytearrayobject.c:2954-2966; bytearrayobject.c:1003-1181", status := .proven
    prop := ``BaInitPaths, thm := some ``baInitPaths_proven
    notes := "Scope: callbacks act on self only; a Python __buffer__ returns memoryview(bytes(...))." },
  { id := "bytesobj-bytearray-resize-storage", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_resize_storage"]
    statement := "On the physical buffer, the memmoves of bytearray_resize_storage leave ob_start == ob_bytes with the old contents there when _PyBytes_ResizeKeepOnError fails (also for a shrink), and the bytes the resize keeps at the start when it succeeds."
    source := "invariant: a failed resize keeps the contents; bytearrayobject.c:227-260", status := .proven
    prop := ``BaResizeStorageSpec, thm := some ``baResizeStorageSpec_proven },
  { id := "bytesobj-bytearray-resize-left-mirror", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_resize_storage", "bytearray_resize_lock_held"]
    statement := "baResizeLeft, what a failed resize leaves, is the state the mirrored failure path of bytearray_resize_storage leaves whenever the storage step is reached and fails."
    source := "bytearrayobject.c:227-260, :302-336", status := .proven
    prop := ``BaResizeLeftMirror, thm := some ``baResizeLeftMirror_proven },
  { id := "bytesobj-bytearray-dealloc", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_dealloc"]
    statement := "bytearray_dealloc prints the SystemError exactly when exports remain; from a fresh object every sequence of Python statements leaves one export per view Python holds, so an object Python drops prints nothing."
    source := "invariant: views are the only exports Python code holds; bytearrayobject.c:1277-1288", status := .proven
    prop := ``BaDeallocSpec, thm := some ``baDeallocSpec_proven },
  { id := "bytesobj-bytearray-tp-new", pyFile := "Objects/bytearrayobject.c"
    pyFns := ["bytearray_new"]
    statement := "bytearray.__new__ ignores its arguments and gives an empty object on the empty bytes, with no storage and no exports, for any type; a failed allocation is MemoryError."
    source := "bytearrayobject.c:959-971", status := .proven
    prop := ``BaTpNewSpec, thm := some ``baTpNewSpec_proven },
  { id := "bytesobj-bytearray-size-null", pyFile := "Objects/bytearrayobject.c"
    pyFns := []
    statement := "PyByteArray_Size(NULL) gives an error, as the documentation's 'after checking for a NULL pointer' says. Refuted: the body only asserts, and a release build dereferences NULL."
    source := "Doc/c-api/bytearray.rst:76-78", status := .refuted
    prop := ``SizeChecksNull, thm := some ``sizeChecksNull_refuted
    bug := some "bytesobj-bytearray-size-null-doc" },
  { id := "bytesobj-bytes-class-tables", pyFile := "Objects/bytes_methods.c"
    pyFns := ["_Py_bytes_isspace", "_Py_bytes_isalpha", "_Py_bytes_isalnum", "_Py_bytes_isdigit"]
    statement := "isspace, isalpha, isdigit and isalnum are 'non-empty and every byte in the class', for the exact byte ranges of pyctype.c."
    source := "docstrings, bytes_methods.c:5-9; Python/pyctype.c", status := .proven
    prop := ``ClassTables, thm := some ``classTables_proven },
  { id := "bytesobj-bytes-case-laws", pyFile := "Objects/bytes_methods.c"
    pyFns := ["_Py_bytes_lower", "_Py_bytes_upper", "_Py_bytes_title", "_Py_bytes_swapcase", "_Py_bytes_islower", "_Py_bytes_isupper"]
    statement := "lower leaves no uppercase byte and is islower exactly when the input has a cased byte, likewise upper; swapcase exchanges isupper and islower; title changes only the case of letters; a string with no cased byte is left alone."
    source := "docstrings, bytes_methods.c:245-326", status := .proven
    prop := ``CaseLaws, thm := some ``caseLaws_proven },
  { id := "bytesobj-bytes-maketrans-hit", pyFile := "Objects/bytes_methods.c"
    pyFns := ["_Py_bytes_maketrans"]
    statement := "maketrans sends each byte of frm to the byte of to at the place of its last occurrence."
    source := "docstring, bytes_methods.c:348-354", status := .proven
    prop := ``MaketransHit, thm := some ``maketransHit_proven },
  { id := "bytesobj-bytes-find-extreme", pyFile := "Objects/bytes_methods.c"
    pyFns := ["parse_args_finds_byte", "find_internal", "_Py_bytes_find", "_Py_bytes_index", "_Py_bytes_rfind", "_Py_bytes_rindex"]
    statement := "find gives the least and rfind the greatest index at which sub occurs within the normalised bounds, or -1 when there is none; index and rindex give the same answer and raise instead of -1."
    source := "docstring of bytes.find; the reading of the bounds given in python/cpython#68431", status := .proven
    prop := ``BytesFindExtreme, thm := some ``bytesFindExtreme_proven },
  { id := "bytesobj-bytes-count-spec", pyFile := "Objects/bytes_methods.c"
    pyFns := ["parse_args_finds_byte", "_Py_bytes_count"]
    statement := "count of a non-empty sub is the number of rounds of the loop that repeats find from the end of the previous match; count of the empty string is the number of positions in the bounds."
    source := "docstring of bytes.count: 'non-overlapping occurrences'", status := .proven
    prop := ``BytesCountSpec, thm := some ``bytesCountSpec_proven },
  { id := "bytesobj-bytes-contains-sub", pyFile := "Objects/bytes_methods.c"
    pyFns := ["_Py_bytes_contains"]
    statement := "p in b for a bytes-like p is exactly 'p occurs in b', at any place and any length."
    source := "Doc/library/stdtypes.rst common sequence 'x in s', bytes note", status := .proven
    prop := ``ContainsSub, thm := some ``containsSub_proven },
  { id := "bytesobj-bytes-tailmatch-spec", pyFile := "Objects/bytes_methods.c"
    pyFns := ["tailmatch"]
    statement := "startswith holds exactly when the normalised bounds leave room for p and p occurs at their start; endswith the same at their end."
    source := "Doc/library/stdtypes.rst bytes.startswith, bytes.endswith", status := .proven
    prop := ``TailmatchSpec, thm := some ``tailmatchSpec_proven },
  { id := "bytesobj-bytes-rich-lex", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_richcompare"]
    statement := "<, <=, > and >= of bytes are the sign of the first difference as unsigned bytes, a proper prefix coming first; the order is antisymmetric and zero exactly on equal strings."
    source := "Doc/reference/expressions.rst, sequence comparison", status := .proven
    prop := ``RichLex, thm := some ``richLex_proven },
  { id := "bytesobj-bytes-subscript-spec", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_item", "bytes_subscript"]
    statement := "b[i] counts a negative index from the end and raises outside; b[s] holds the elements of range(*s.indices(len(b))), in order and in bounds, for every slice with a non-zero step."
    source := "Doc/library/stdtypes.rst common sequence operations", status := .proven
    prop := ``SubscriptSpec, thm := some ``subscriptSpec_proven },
  { id := "bytesobj-bytes-hex-groups", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_hex_impl"]
    statement := "hex(sep, n) puts sep between groups of |n| bytes counted from the left for n < 0 and from the right for n > 0, the odd group at the far end, and adds no separator with n = 0 or |n| at least the length."
    source := "docstring, bytesobject.c:2749-2763", status := .proven
    prop := ``HexGroups, thm := some ``hexGroups_proven },
  { id := "bytesobj-bytes-fromhex-spec", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FromHex", "bytes_fromhex_impl"]
    statement := "fromhex of bytes, bytearray or ASCII str follows a position-by-position grammar: skip ASCII whitespace, two digits make a byte, the first offending position is reported, a lone last digit is the odd-count error; a non-ASCII str is refused at its first non-ASCII position."
    source := "docstring, bytesobject.c:2611-2614", status := .proven
    prop := ``FromHexSpec, thm := some ``fromHexSpec_proven },
  { id := "bytesobj-bytes-repr-spec", pyFile := "Objects/bytesobject.c"
    pyFns := ["PyBytes_Repr", "_Py_bytes_repr", "bytearray_repr", "bytearray_repr_lock_held"]
    statement := "repr(b) uses \" only in smart mode for a body with ' and no \", its text is printable ASCII, printable bytes other than the quote and the backslash stand for themselves, and the quote appears only escaped."
    source := "Doc/library/functions.rst repr; Doc/library/stdtypes.rst bytes literals", status := .proven
    prop := ``ReprSpec, thm := some ``reprSpec_proven },
  { id := "bytesobj-bytes-strip-spec", pyFile := "Objects/bytesobject.c"
    pyFns := ["do_xstrip", "do_strip", "do_argstrip"]
    statement := "strip removes only members of the set, only from the sides asked for, and a stripped side of the result is not a member; the result is a piece of the input."
    source := "Doc/library/stdtypes.rst bytes.strip", status := .proven
    prop := ``BytesStripSpec, thm := some ``bytesStripSpec_proven },
  { id := "bytesobj-bytes-translate-spec", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_translate_impl"]
    statement := "translate keeps the bytes outside delete and sends each through the table; no table keeps them; a table of another length raises ValueError."
    source := "Doc/library/stdtypes.rst bytes.translate", status := .proven
    prop := ``TranslateSpec, thm := some ``translateSpec_proven },
  { id := "bytesobj-bytes-concat-value", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_Concat", "PyBytes_Concat"]
    statement := "PyBytes_Concat gives the concatenation on both the in-place and the new-object path."
    source := "Doc/c-api/bytes.rst PyBytes_Concat", status := .proven
    prop := ``ConcatValue, thm := some ``concatValue_proven },
  { id := "bytesobj-bytes-join-intercalate", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_join_impl", "PyBytes_Join"]
    statement := "The write loop of join is the items with sep between them and nowhere else."
    source := "docstring, bytesobject.c:1973-1985", status := .proven
    prop := ``JoinIntercalate, thm := some ``joinIntercalate_proven },
  { id := "bytesobj-bytes-removesuffix-miss", pyFile := "Objects/bytesobject.c"
    pyFns := ["bytes_removesuffix_impl"]
    statement := "A suffix that does not match leaves the bytes alone."
    source := "docstring, bytesobject.c:2475-2479", status := .proven
    prop := ``RemoveSuffixMiss, thm := some ``removeSuffixMiss_proven },
  { id := "bytesobj-bytes-contains-index-error", pyFile := "Objects/bytes_methods.c"
    pyFns := ["_Py_bytes_contains"]
    statement := "x in b reports what x.__index__ raised, as b.find(x) does: refuted, the exception is cleared and the buffer protocol's TypeError takes its place."
    source := "twin: parse_args_finds_byte keeps the error, bytes_methods.c:418-421", status := .refuted
    prop := ``ContainsKeepsIndexError, thm := some ``containsKeepsIndexError_refuted
    bug := some "bytesobj-bytes-contains-index-error-masked" },
  { id := "bytesobj-bytes-index-raises", pyFile := "Objects/bytes_methods.c"
    pyFns := ["parse_args_finds_byte", "_Py_bytes_contains", "byte_converter", "formatlong", "bytes_new_impl"]
    statement := "An exception from __index__ passes through find, index, count, the item conversions and the conversions of %; bytes(x) and bytearray(x) fall through on TypeError only; %c passes it on as well, and %d and its kin replace a TypeError by the format's message; in loses it."
    source := "the error paths at bytes_methods.c:418-421, :604-610, bytesobject.c:2931-2938, bytearrayobject.c:1058-1063", status := .proven
    prop := ``IndexRaisesRules, thm := some ``indexRaisesRules_proven },
  { id := "bytesobj-bytearray-index-raises", pyFile := "Objects/bytearrayobject.c"
    pyFns := []
    statement := "An exception from the item's __index__ is what append, insert, remove and item assignment raise, before any change to the object."
    source := "error paths of _getbytevalue, bytearrayobject.c:31-34", status := .proven
    prop := ``MutatorsIndexRaises, thm := some ``mutatorsIndexRaises_proven },
  { id := "bytesobj-bytes-iter-raises", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FromIterator", "PyBytes_FromObject", "PyBytes_Join"]
    statement := "bytes(it) and extend check items as they come, so a failing iterator's exception comes after good items and a bad item comes before it; join runs the iterator to its end first, so its exception wins over any item; extend writes nothing."
    source := "the loops at bytesobject.c:3080-3108, bytearrayobject.c:2286-2324; PySequence_Fast", status := .proven
    prop := ``IterRaisesRules, thm := some ``iterRaisesRules_proven },
  { id := "bytesobj-bytes-hint-rules", pyFile := "Objects/bytesobject.c"
    pyFns := ["_PyBytes_FromIterator", "PyBytes_Join"]
    statement := "__length_hint__ runs before the first item: a TypeError from it is ignored, another exception wins over a bad item, a negative value is ValueError, and a good value does not change the result."
    source := "PyObject_LengthHint, Objects/abstract.c:95-152; bytesobject.c:3068-3070", status := .proven
    prop := ``HintRules, thm := some ``hintRules_proven },
  { id := "bytesobj-bytes-call-raises", pyFile := "Objects/bytesobject.c"
    pyFns := ["PyBytes_FromObject", "PyBytes_Join", "bytes_new_impl", "format_obj"]
    statement := "__iter__ raising: each caller keeps a non-TypeError and turns a TypeError into its own message. __bytes__ raising: bytes(x) and %b pass it on, and bytearray(x) never calls it."
    source := "bytesobject.c:3148-3163, :2910-2914, :577-584; bytearrayobject.c:1131-1138, :2262-2269", status := .proven
    prop := ``CallRaisesRules, thm := some ``callRaisesRules_proven }
]

end PyLean.BytesObj.Bytes
