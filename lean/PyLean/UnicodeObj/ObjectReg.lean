import PyLean.Registry
import PyLean.UnicodeObj.ObjectKinds
import PyLean.UnicodeObj.ObjectWriterProps
import PyLean.UnicodeObj.ObjectFromFormatTwin
import PyLean.UnicodeObj.ObjectFromFormatWriter
import PyLean.UnicodeObj.ObjectIterProps
import PyLean.UnicodeObj.ObjectInternProps
import PyLean.UnicodeObj.ObjectJoinProps
import PyLean.UnicodeObj.ObjectAscii
import PyLean.UnicodeObj.ObjectChunksUtf8
import PyLean.UnicodeObj.ObjectEscapeErrors

/-! Registry entries of the object slice. -/

namespace PyLean.UnicodeObj

open PyLean.Registry

def objectEntries : List Entry := [
  { id := "unicodeobj-escape-warns", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_DecodeUnicodeEscapeInternal2", "_PyUnicode_DecodeUnicodeEscapeStateful", "PyUnicode_DecodeUnicodeEscape"]
    statement := "The first invalid escape after any encoder text is what the decoder reports, with its position, whatever follows and whatever a handler does; it is a DeprecationWarning, an exception only if warnings are errors, and it never changes the text or replaces a failure of the decode."
    source := "unicodeobject.c:6733-6741, 6833-6840 and 6892-6913"
    status := .proven, prop := ``UnicodeEscapeWarns, thm := some ``unicodeEscapeWarns_proven },
  { id := "unicodeobj-escape-clean", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_DecodeUnicodeEscapeStateful", "PyUnicode_AsUnicodeEscapeString"]
    statement := "Text from s.encode('unicode_escape') decodes back with no warning, even when warnings are errors, for any handler."
    source := "implementation against itself: the encoder against the warning of the decoder"
    status := .proven, prop := ``UnicodeEscapeClean, thm := some ``unicodeEscapeClean_proven },
  { id := "unicodeobj-escape-fails-at", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_DecodeUnicodeEscapeInternal2"]
    statement := "A strict unicode_escape decode raises at the first escape that fails, with that escape's span and reason measured in the whole input."
    source := "invariant: exact error positions"
    status := .proven, prop := ``UnicodeEscapeFailsAt, thm := some ``unicodeEscapeFailsAt_proven },
  { id := "unicodeobj-escape-failures", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_DecodeUnicodeEscapeInternal2"]
    statement := "Each form of unicode_escape that cannot be read fails with its own reason and span: truncated \\x, \\u and \\U, a backslash at the end, a malformed or unknown \\N, and a value above U+10FFFF."
    source := "unicodeobject.c:6696-6831"
    status := .proven, prop := ``UnicodeEscapeFailures, thm := some ``unicodeEscapeFailures_proven },
  { id := "unicodeobj-raw-escape-fails-at", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_DecodeRawUnicodeEscapeStateful", "PyUnicode_DecodeRawUnicodeEscape"]
    statement := "A strict raw_unicode_escape decode raises at the first escape that fails, with that escape's span and reason measured in the whole input."
    source := "invariant: exact error positions"
    status := .proven, prop := ``RawEscapeFailsAt, thm := some ``rawEscapeFailsAt_proven },
  { id := "unicodeobj-raw-escape-failures", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_DecodeRawUnicodeEscapeStateful"]
    statement := "In raw_unicode_escape a backslash at the very end is itself, before anything but u or U it is itself and that byte, and truncated \\u and \\U and a value above U+10FFFF fail with their own reasons."
    source := "unicodeobject.c:6971-7025"
    status := .proven, prop := ``RawEscapeFailures, thm := some ``rawEscapeFailures_proven },
  { id := "unicodeobj-escape-printable", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_AsUnicodeEscapeString"]
    statement := "Every byte of s.encode('unicode_escape') is printable ASCII, for every string."
    source := "Doc/library/codecs.rst: unicode_escape is ASCII-encoded source text"
    status := .proven, prop := ``UnicodeEscapePrintable, thm := some ``unicodeEscapePrintable_proven },
  { id := "unicodeobj-raw-escape-encode-spec", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_AsRawUnicodeEscapeString"]
    statement := "raw_unicode_escape copies Latin-1 text unchanged, and writes every other character as printable ASCII."
    source := "unicodeobject.c:7081-7127"
    status := .proven, prop := ``RawEscapeEncodeSpec, thm := some ``rawEscapeEncodeSpec_proven },
  { id := "unicodeobj-codec-utf8-chunks", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_decode_utf8_impl"]
    statement := "Decoding UTF-8 in two chunks through consumed gives what decoding at once gives, wherever the input is cut, for every standard handler, surrogatepass and the truncated surrogate case included."
    source := "the contract of incremental decoding, Doc/library/codecs.rst; unicodeobject.c:5227-5234"
    status := .proven, prop := ``Utf8Chunks, thm := some ``utf8Chunks_proven },
  { id := "unicodeobj-codec-utf16-chunks", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_DecodeUTF16Stateful"]
    statement := "Decoding UTF-16 with a fixed byte order in two chunks gives what decoding at once gives, wherever the input is cut, a surrogate pair included, for every standard handler."
    source := "the contract of incremental decoding, Doc/library/codecs.rst"
    status := .proven, prop := ``Utf16Chunks, thm := some ``utf16Chunks_proven },
  { id := "unicodeobj-codec-utf32-chunks", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_DecodeUTF32Stateful"]
    statement := "Decoding UTF-32 with a fixed byte order in two chunks gives what decoding at once gives, wherever the input is cut, for every standard handler."
    source := "the contract of incremental decoding, Doc/library/codecs.rst"
    status := .proven, prop := ``Utf32Chunks, thm := some ``utf32Chunks_proven },
  { id := "unicodeobj-codec-raw-escape-chunks", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "Decoding raw_unicode_escape in two chunks gives what decoding at once gives, wherever the input is cut, for every standard handler."
    source := "the contract of incremental decoding, Doc/library/codecs.rst"
    status := .proven, prop := ``RawEscapeChunks, thm := some ``rawEscapeChunks_proven },
  { id := "unicodeobj-codec-unicode-escape-chunks-narrow", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "Decoding unicode_escape in two chunks gives what decoding at once gives, for every standard handler and name table, unless the cut is inside an octal escape and the next chunk starts with a digit for it. That one case is unicodeobj-codec-unicode-escape-chunks."
    source := "the contract of incremental decoding, Doc/library/codecs.rst; narrowed from the refuted entry"
    status := .proven, prop := ``UnicodeEscapeChunksNarrow, thm := some ``unicodeEscapeChunksNarrow_proven },
  { id := "unicodeobj-utf8-std-is-callback", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_decode_utf8_impl"]
    statement := "The ignore, replace and surrogateescape handlers written out inside the UTF-8 decoder do what the registered handlers of those names do through the Python path, for every input and every handler."
    source := "implementation against itself: inline handlers against Python/codecs.c, unicodeobject.c:5252-5277"
    status := .proven, prop := ``Utf8StdIsCallback, thm := some ``utf8StdIsCallback_proven },
  { id := "unicodeobj-ascii-decode-spec", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_DecodeASCII"]
    statement := "The replace, surrogateescape and ignore handlers written out inside the ASCII decoder and its fast paths give what the generic handler path gives, for every handler, and the kind of the result is canonical."
    source := "implementation against itself: inline handlers against Python/codecs.c, unicodeobject.c:7504-7538"
    status := .proven, prop := ``AsciiDecodeSpec, thm := some ``asciiDecodeSpec_proven },
  { id := "unicodeobj-writer-decode-any-handler", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_DecodeUTF8Writer"]
    statement := "_PyUnicode_DecodeUTF8Writer, with any handler, adds what the UTF-8 decoder behind bytes.decode gives (the stateful one when consumed is passed), and a success keeps the capacity what the text needs when it was so before. When the decoder raises, it returns the same exception and does not put writer->pos back. Either way the writer ends with the old text followed by exactly what the loop of unicode_decode_utf8_impl, run on the whole input without the ASCII fast path, had written when it stopped (for b'a\\xff' with the strict handler on a new writer the a stays). Followed by the put back of pos that PyUnicodeWriter_WriteUTF8 and PyUnicodeWriter_DecodeUTF8Stateful do, it is decodeWriterX, the model unicodeobj-writer-decode-stateful-any-handler is built on, where none of the text is kept."
    source := "implementation against itself: the writer entry against unicode_decode_utf8_impl; Objects/unicodeobject.c:5404-5441, 5302-5305; Objects/unicode_writer.c:504-508, 526-531"
    status := .proven, prop := ``WriterDecodeRawX, thm := some ``writerDecodeRawX_proven
    notes := "The earlier statement credited this function with keeping none of the text on failure. That is done by its two public callers; unicodeobj-writer-decode-stateful-any-handler states it for PyUnicodeWriter_DecodeUTF8Stateful." },
  { id := "unicodeobj-writer-decode-stateful-any-handler", pyFile := "Objects/unicode_writer.c"
    pyFns := ["PyUnicodeWriter_DecodeUTF8Stateful"]
    statement := "PyUnicodeWriter_DecodeUTF8Stateful, for any size and handler, gives the text of the decoder and sets *consumed, and on a failure rolls the text back and sets *consumed to 0."
    source := "Doc/c-api/unicode.rst: PyUnicodeWriter_DecodeUTF8Stateful"
    status := .proven, prop := ``WriterDecodeStatefulX, thm := some ``writerDecodeStatefulX_proven },
  { id := "unicodeobj-decode-utf8-spec", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_decode_utf8", "PyUnicode_DecodeUTF8Stateful", "PyUnicode_DecodeUTF8"]
    statement := "The empty, one byte and ASCII fast paths and the guess of maxchr from the first byte change nothing: the result is what the plain loop gives, for every handler, and its kind is canonical."
    source := "implementation against itself: fast paths against the loop; invariant: _PyUnicode_CheckConsistency"
    status := .proven, prop := ``DecodeUtf8Spec, thm := some ``decodeUtf8Spec_proven },
  { id := "unicodeobj-join-spec", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_JoinArray"]
    statement := "sep.join(items) is the items with the separator between them, of the canonical kind, for every list of strings that fits; one exact str is returned itself, and one item of a subclass ignores the separator."
    source := "Doc/library/stdtypes.rst: str.join; invariant: _PyUnicode_CheckConsistency"
    status := .proven, prop := ``JoinSpec, thm := some ``joinSpec_proven },
  { id := "unicodeobj-join-errors", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_JoinArray"]
    statement := "With two or more items the separator is checked first, the first item that is not a str is named by its index, and a result too long for Py_ssize_t raises OverflowError."
    source := "invariant: no wraparound; unicodeobject.c:10085-10133"
    status := .proven, prop := ``JoinErrors, thm := some ``joinErrors_proven },
  { id := "unicodeobj-join-sequence", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_Join"]
    statement := "An iterator gives what a list of its items gives, the first exception from next is raised as it is, a TypeError from __iter__ becomes 'can only join an iterable', and any other exception from __iter__ is kept."
    source := "implementation against itself: list against iterator; Objects/abstract.c:2104-2129"
    status := .proven, prop := ``JoinSequence, thm := some ``joinSequence_proven },
  { id := "unicodeobj-join-memcpy-safe", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_JoinArray"]
    statement := "When join takes the memcpy path, the separator and every item have the byte width of the result."
    source := "invariant: the memcpy of kind * len bytes at unicodeobject.c:10164-10174"
    status := .proven, prop := ``JoinMemcpySafe, thm := some ``joinMemcpySafe_proven },
  { id := "unicodeobj-intern-start-world", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "The interning tables at the start of a program satisfy the invariant the interning theorems assume."
    source := "invariant of the interned tables: it holds at the start"
    status := .proven, prop := ``StartWorldOK, thm := some ``startWorldOK_proven },
  { id := "unicodeobj-intern-scripts-keep-invariant", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "From the start of a program, through any script of new objects and interning calls, the tables satisfy that invariant."
    source := "invariant of the interned tables: it holds at every reachable state"
    status := .proven, prop := ``ScriptsKeepWOK, thm := some ``scriptsKeepWOK_proven },
  { id := "unicodeobj-intern-canonical", pyFile := "Objects/unicodeobject.c"
    pyFns := ["intern_common"]
    statement := "For every two exact strings of equal text, in any state, the second intern returns the object of the first. Objects are compared by id."
    source := "Doc/library/sys.rst: sys.intern; invariant of the interned tables"
    status := .proven, prop := ``InternCanonical, thm := some ``internCanonical_proven },
  { id := "unicodeobj-intern-spec", pyFile := "Objects/unicodeobject.c"
    pyFns := ["intern_common", "immortalize_interned"]
    statement := "Interning keeps the tables consistent and every object's text, returns an object of the same text, leaves non-str objects and instances of subclasses alone, and gives an interned result for an exact str, not mortal if immortality was asked for."
    source := "invariant of the interned tables; unicodeobject.c:14306-14310"
    status := .proven, prop := ``InternSpec, thm := some ``internSpec_proven },
  { id := "unicodeobj-intern-idempotent", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "Interning what interning returned changes nothing."
    source := "invariant: idempotence"
    status := .proven, prop := ``InternIdempotent, thm := some ``internIdempotent_proven },
  { id := "unicodeobj-intern-mortality", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_InternMortal", "_PyUnicode_InternImmortal", "PyUnicode_InternInPlace", "PyUnicode_InternImmortal"]
    statement := "PyUnicode_InternInPlace makes a new interned string mortal and leaves what the dict holds, PyUnicode_InternImmortal makes it immortal and promotes what the dict holds."
    source := "implementation against itself: the two entry points; InternalDocs/string_interning.md"
    status := .proven, prop := ``InternMortality, thm := some ``internMortality_proven },
  { id := "unicodeobj-intern-from-string", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_InternFromString"]
    statement := "PyUnicode_InternFromString raises what the strict decode raises, and otherwise gives an interned string of the decoded text, the same object each time."
    source := "implementation against itself: the C string path against intern_common"
    status := .proven, prop := ``InternFromStringSpec, thm := some ``internFromStringSpec_proven },
  { id := "unicodeobj-unicode-char-spec", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_char"]
    statement := "unicode_char gives the character in its canonical kind for every code point, and SystemError for every Py_UCS4 above U+10FFFF."
    source := "unicodeobject.c:1838-1841; invariant: the maximum character of a str"
    status := .proven, prop := ``UnicodeCharSpec, thm := some ``unicodeCharSpec_proven },
  { id := "unicodeobj-iter-drains", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicodeiter_next", "unicode_ascii_iter_next", "unicode_char", "unicode_iter"]
    statement := "list(iter(s)) is the characters of s, each a one-character string of the canonical kind, for both iterator types and for a subclass of str, and the iterator ends."
    source := "invariant: iteration over a str; Doc/library/stdtypes.rst"
    status := .proven, prop := ``IterDrains, thm := some ``iterDrains_proven },
  { id := "unicodeobj-iter-ascii-twin", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_ascii_iter_next"]
    statement := "The ASCII iterator and the general one give the same item and the same state on ASCII strings, at every state."
    source := "implementation against itself: fast path against general path"
    status := .proven, prop := ``AsciiIterTwin, thm := some ``asciiIterTwin_proven },
  { id := "unicodeobj-iter-hint-exact", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicodeiter_len"]
    statement := "__length_hint__ is the number of items still to come, after any script of next and __setstate__, including past the end."
    source := "invariant: the length hint of a str iterator is exact"
    status := .proven, prop := ``IterHintExact, thm := some ``iterHintExact_proven },
  { id := "unicodeobj-iter-setstate", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicodeiter_setstate"]
    statement := "__setstate__ moves to where s[v:] starts, for every Py_ssize_t, leaves an exhausted iterator exhausted, and raises OverflowError or TypeError otherwise, for an exhausted iterator too."
    source := "invariant: the clamp at unicodeobject.c:14718-14723"
    status := .proven, prop := ``IterSetstateSpec, thm := some ``iterSetstateSpec_proven },
  { id := "unicodeobj-iter-reduce-round-trip", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicodeiter_reduce"]
    statement := "Rebuilding from __reduce__ gives the items the iterator has left after the lookup of iter, whatever that lookup does to the iterator, and a failed lookup raises."
    source := "invariant: pickle round trip; issue 101765, reading the iterator after the lookup"
    status := .proven, prop := ``IterReduceRoundTrip, thm := some ``iterReduceRoundTrip_proven },
  { id := "unicodeobj-fromformat-no-negative-copy", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "No format and no arguments of the right types reach a copy with a negative count."
    source := "invariant: no crash; assert(0 <= how_many) at unicodeobject.c:1393"
    status := .refuted, prop := ``FromFormatNoNegativeCopy, thm := some ``fromFormatNoNegativeCopy_refuted
    bug := some "unicodeobj-fromformat-negative-precision" },
  { id := "unicodeobj-fromformat-negative-star-omitted", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "A negative '*' precision is an omitted precision, as in C, for every conversion."
    source := "implementation against itself: %d against %s; C11 7.21.6.1"
    status := .refuted, prop := ``FromFormatNegativeStarOmitted, thm := some ``fromFormatNegativeStarOmitted_refuted
    bug := some "unicodeobj-fromformat-negative-precision" },
  { id := "unicodeobj-fromformat-int-star-omitted", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "The integer conversions read a negative '*' precision as omitted, with any flags, width and size."
    source := "implementation against itself: the sentinel -2 against -1; C11 7.21.6.1"
    status := .proven, prop := ``FromFormatIntStarOmitted, thm := some ``fromFormatIntStarOmitted_proven },
  { id := "unicodeobj-fromformat-write-str-negative-copy", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "unicode_fromformat_write_str does the bad copy exactly when the precision is below -1, for every string, width and flag."
    source := "invariant: no crash"
    status := .proven, prop := ``WriteStrNegativeCopy, thm := some ``writeStrNegativeCopy_proven },
  { id := "unicodeobj-fromformat-parser-precision-range", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "The parser gives a precision of -1 or more, or the sentinel -2 of a negative '*': digits and a bare '.' cannot produce a precision below -1."
    source := "invariant: the range of a parsed precision"
    status := .proven, prop := ``ParserPrecisionRange, thm := some ``parserPrecisionRange_proven },
  { id := "unicodeobj-fromformat-canonical", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "Every str PyUnicode_FromFormat returns has the canonical kind, for every format and all arguments, including when a precision makes the text narrower than the string it came from."
    source := "invariant: _PyUnicode_CheckConsistency"
    status := .proven, prop := ``FromFormatCanonical, thm := some ``fromFormatCanonical_proven },
  { id := "unicodeobj-fromformat-v-twins", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "%V is %U when it has an object, and %s or %ls when it does not, with any flags, width and precision."
    source := "implementation against itself; Doc/c-api/unicode.rst"
    status := .proven, prop := ``FromFormatVTwins, thm := some ``fromFormatVTwins_proven },
  { id := "unicodeobj-fromformat-int-matches-percent", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "PyUnicode_FromFormat and Python's % lay an integer out the same way, for every value of the C type, every width and precision, and the flags - and 0 in any combination."
    source := "implementation against itself: two layouts of an integer"
    status := .proven, prop := ``IntMatchesPercent, thm := some ``intMatchesPercent_proven },
  { id := "unicodeobj-fromformat-escape", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "Doubling the % of an ASCII string and formatting it with no arguments gives the string back, with the canonical kind."
    source := "invariant: round trip through %%"
    status := .proven, prop := ``FromFormatEscape, thm := some ``fromFormatEscape_proven },
  { id := "unicodeobj-writer-format-appends", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicodeWriter_Format", "_PyUnicodeWriter_FormatV"]
    statement := "PyUnicodeWriter_Format is PyUnicode_FromFormat appended to what the writer holds: same exception, same text, for every writer, or no text on failure."
    source := "implementation against itself: the writer path against the object path"
    status := .proven, prop := ``WriterFormatAppends, thm := some ``writerFormatAppends_proven },
  { id := "unicodeobj-writer-format-unobservable", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "After a failed PyUnicodeWriter_Format, Finish behaves as if it had not been called."
    source := "Doc/c-api/unicode.rst: On error, set an exception, leave the writer unchanged"
    status := .refuted, prop := ``WriterFormatUnobservable, thm := some ``writerFormatUnobservable_refuted
    bug := some "unicodeobj-writer-rollback-noncanonical" },
  { id := "unicodeobj-writer-text", pyFile := "Objects/unicode_writer.c"
    pyFns := ["PyUnicodeWriter_WriteStr", "PyUnicodeWriter_WriteRepr", "PyUnicodeWriter_WriteASCII", "PyUnicodeWriter_WriteWideChar", "find_maxchar_surrogates", "PyUnicodeWriter_WriteUTF8"]
    statement := "For every script of writer operations, the text is what the successful ones wrote, in order: WriteStr is str(), WriteRepr is repr(), a decode is bytes.decode, each raises what they raise, and a failed operation leaves no characters."
    source := "implementation against itself: the exact-str and exact-int fast paths and the writer's decoder against the object-level functions; Doc/c-api/unicode.rst"
    status := .proven, prop := ``WriterText, thm := some ``writerText_proven },
  { id := "unicodeobj-writer-consumed", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "PyUnicodeWriter_DecodeUTF8Stateful writes the text and reports the *consumed of PyUnicode_DecodeUTF8Stateful, for every built-in handler."
    source := "implementation against itself: the writer path against the stateful decoder; Doc/c-api/unicode.rst"
    status := .proven, prop := ``WriterConsumed, thm := some ``writerConsumed_proven },
  { id := "unicodeobj-writer-finish-one-byte", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_Result"]
    statement := "A one-byte buffer holding at most one character finishes with the canonical kind, whatever the writer has been through."
    source := "invariant: _PyUnicode_CheckConsistency; the LATIN1 singleton of _PyUnicode_Result"
    status := .proven, prop := ``WriterFinishOneByte, thm := some ``writerFinishOneByte_proven },
  { id := "unicodeobj-writer-consumed-failure", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "When the stateful decoder raises, PyUnicodeWriter_DecodeUTF8Stateful raises the same exception, keeps no text, and sets *consumed to 0, for every built-in handler."
    source := "implementation against itself: the writer path against the stateful decoder; unicode_writer.c:530-535"
    status := .proven, prop := ``WriterConsumedFailure, thm := some ``writerConsumedFailure_proven },
  { id := "unicodeobj-writer-cap-value", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "writer->maxchar stays the limit of a kind through every operation, failed ones included."
    source := "invariant: _PyUnicodeWriter_Update"
    status := .proven, prop := ``WriterCapValue, thm := some ``writerCapValue_proven },
  { id := "unicodeobj-writer-finish-canonical", pyFile := "Objects/unicode_writer.c"
    pyFns := ["PyUnicodeWriter_Finish", "_PyUnicode_Result"]
    statement := "Unless a decode fails, the str that PyUnicodeWriter_Finish returns has the canonical kind, for every script from any PyUnicodeWriter_Create."
    source := "invariant: _PyUnicode_CheckConsistency"
    status := .proven, prop := ``WriterFinishCanonical, thm := some ``writerFinishCanonical_proven },
  { id := "unicodeobj-writer-always-canonical", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "The str that PyUnicodeWriter_Finish returns has the canonical kind for every script, failed decodes included."
    source := "invariant: _PyUnicode_CheckConsistency"
    status := .refuted, prop := ``WriterAlwaysCanonical, thm := some ``writerAlwaysCanonical_refuted
    bug := some "unicodeobj-writer-rollback-noncanonical" },
  { id := "unicodeobj-writer-failure-keeps-state", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "An operation other than a decode leaves the writer unchanged when it fails."
    source := "Doc/c-api/unicode.rst: On error, set an exception, leave the writer unchanged"
    status := .proven, prop := ``WriterFailureKeepsState, thm := some ``writerFailureKeepsState_proven },
  { id := "unicodeobj-writer-failure-unobservable", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "After any failed operation, Finish and every later write behave as if it had not been made."
    source := "Doc/c-api/unicode.rst: On error, set an exception, leave the writer unchanged"
    status := .refuted, prop := ``WriterFailureUnobservable, thm := some ``writerFailureUnobservable_refuted
    bug := some "unicodeobj-writer-rollback-noncanonical" },
  { id := "unicodeobj-writer-paths-agree", pyFile := "Objects/unicode_writer.c"
    pyFns := ["PyUnicodeWriter_WriteChar", "_PyUnicodeWriter_WriteChar", "PyUnicodeWriter_WriteUCS4"]
    statement := "WriteStr, WriteUCS4, WriteWideChar, WriteSubstring of all of it, WriteChar for each character, and WriteUTF8 or DecodeUTF8Stateful of its encoding leave the same writer, from every writer."
    source := "implementation against itself: six ways to write one string"
    status := .proven, prop := ``WriterPathsAgree, thm := some ``writerPathsAgree_proven },
  { id := "unicodeobj-writer-substring-slice", pyFile := "Objects/unicode_writer.c"
    pyFns := ["PyUnicodeWriter_WriteSubstring", "_PyUnicodeWriter_WriteSubstring"]
    statement := "WriteSubstring(s, a, b) is WriteStr(s[a:b]) for every in-range slice and every writer, whichever way the kind check goes."
    source := "implementation against itself: the scan skipped when the whole string's kind fits"
    status := .proven, prop := ``WriterSubstringIsSlice, thm := some ``writerSubstringIsSlice_proven },
  { id := "unicodeobj-object-isascii-kind", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "PyUnicode_IS_ASCII, a flag of the representation, holds exactly when every character is below 128."
    source := "invariant: PEP 393 canonical kind"
    status := .proven, prop := ``IsAsciiKind, thm := some ``isAsciiKind_proven },
  { id := "unicodeobj-object-concat-kind", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "str + str allocates the canonical kind of the result, from the operands' kinds alone."
    source := "invariant: PEP 393 canonical kind (_PyUnicode_CheckConsistency)"
    status := .proven, prop := ``ConcatKind, thm := some ``concatKind_proven },
  { id := "unicodeobj-object-slice-kind", pyFile := "Objects/unicodeobject.c"
    pyFns := ["kind_maxchar_limit"]
    statement := "An extended slice allocates the canonical kind of its result, despite the early break of its max_char loop."
    source := "invariant: PEP 393 canonical kind (_PyUnicode_CheckConsistency)"
    status := .proven, prop := ``SliceKind, thm := some ``sliceKind_proven },
  { id := "unicodeobj-object-repeat-length", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "s * n has n * len(s) characters, and OverflowError is raised exactly when that exceeds PY_SSIZE_T_MAX."
    source := "invariant: no silent wraparound"
    status := .proven, prop := ``RepeatLength, thm := some ``repeatLength_proven },
  { id := "unicodeobj-object-compare-order", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "unicode_compare is antisymmetric and is 0 exactly on equal strings."
    source := "invariant: total order on code points"
    status := .proven, prop := ``CompareOrder, thm := some ``compareOrder_proven
    notes := "The twelve kind pairs and memcmp paths are modelled by their result; difftested through ==, < and sorted." }
]

end PyLean.UnicodeObj
