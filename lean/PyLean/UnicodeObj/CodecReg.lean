import PyLean.Registry
import PyLean.UnicodeObj.CodecProps

/-! Registry entries of the codecs slice. -/

namespace PyLean.UnicodeObj

open PyLean.Registry

def codecEntries : List Entry := [
  { id := "unicodeobj-codec-utf8-rejects-forbidden", pyFile := "Objects/stringlib/codecs.h"
    pyFns := ["unicode_decode_utf8_impl"]
    statement := "The UTF-8 decoder rejects C0, C1 and F5..FF as lead bytes, overlong three- and four-byte forms, encoded surrogates and sequences above U+10FFFF, whatever follows."
    source := "The Unicode Standard, Table 3-7; RFC 3629; comments in codecs.h:150-158"
    status := .proven, prop := ``Utf8RejectsForbidden, thm := some ``utf8RejectsForbidden_proven },
  { id := "unicodeobj-codec-utf8-strict-iff-wf", pyFile := "Objects/stringlib/codecs.h"
    pyFns := ["unicode_decode_utf8_impl"]
    statement := "The strict UTF-8 decoder accepts exactly the well-formed sequences of Table 3-7."
    source := "The Unicode Standard, Table 3-7"
    status := .open, prop := ``Utf8StrictIffWellFormed
    notes := "Needs an induction over utf8DecodeLoop and utf8Wf together." },
  { id := "unicodeobj-codec-utf8-round-trip", pyFile := "Objects/stringlib/codecs.h"
    pyFns := ["unicode_encode_utf8", "unicode_decode_utf8", "unicode_decode_utf8_impl",
      "PyUnicode_DecodeUTF8", "PyUnicode_DecodeUTF8Stateful", "PyUnicode_AsUTF8String",
      "_PyUnicode_AsUTF8String"]
    statement := "The strict UTF-8 encoder succeeds on every string of scalar values, and decoding its output gives the string back."
    source := "invariant: round trip; The Unicode Standard, Table 3-7"
    status := .proven, prop := ``Utf8RoundTrip, thm := some ``utf8RoundTrip_proven },
  { id := "unicodeobj-codec-utf16-round-trip", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_DecodeUTF16Stateful", "PyUnicode_DecodeUTF16", "_PyUnicode_EncodeUTF16",
      "PyUnicode_AsUTF16String"]
    statement := "Encoding to UTF-16 and decoding with the same byteorder gives every string of scalar values back, surrogate pairs included, for little-endian, big-endian and BOM."
    source := "invariant: round trip"
    status := .proven, prop := ``Utf16RoundTrip, thm := some ``utf16RoundTrip_proven
    notes := "The model is a little-endian build. The aligned long reads and unrolled loops are modelled by the scalar path; the difftest checks them." },
  { id := "unicodeobj-codec-utf32-round-trip", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_DecodeUTF32Stateful", "PyUnicode_DecodeUTF32", "_PyUnicode_EncodeUTF32",
      "PyUnicode_AsUTF32String"]
    statement := "Encoding to UTF-32 and decoding with the same byteorder gives every string of scalar values back, for little-endian, big-endian and BOM."
    source := "invariant: round trip"
    status := .proven, prop := ``Utf32RoundTrip, thm := some ``utf32RoundTrip_proven },
  { id := "unicodeobj-codec-decode-handler-advances", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_decode_call_errorhandler_writer", "make_decode_exception"]
    statement := "Every standard error handler returns a position past start on a decode error, so no decoder loop can repeat forever."
    source := "invariant: no hang"
    status := .proven, prop := ``DecodeHandlerAdvances, thm := some ``decodeHandlerAdvances_proven
    notes := "User-registered handlers can return any position; they are not modelled." },
  { id := "unicodeobj-codec-encode-handler-advances", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_encode_call_errorhandler", "make_encode_exception", "raise_encode_exception"]
    statement := "Every standard error handler returns a position past start on an encode error."
    source := "invariant: no hang"
    status := .proven, prop := ``EncodeHandlerAdvances, thm := some ``encodeHandlerAdvances_proven },
  { id := "unicodeobj-codec-unicode-escape-round-trip", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_AsUnicodeEscapeString", "_PyUnicode_DecodeUnicodeEscapeInternal2",
      "_PyUnicode_DecodeUnicodeEscapeStateful", "PyUnicode_DecodeUnicodeEscape"]
    statement := "s.encode('unicode_escape') decodes back to s for every string, lone surrogates included, one-shot or stateful, and all of it is consumed."
    source := "invariant: round trip"
    status := .proven, prop := ``UnicodeEscapeRoundTrip, thm := some ``unicodeEscapeRoundTrip_proven
    notes := "The DeprecationWarning for invalid escapes has no effect on the result and is not modelled. \\N names come from a parameter." },
  { id := "unicodeobj-codec-unicode-escape-chunks", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_DecodeUnicodeEscapeInternal2"]
    statement := "Decoding unicode_escape in two chunks gives what decoding at once gives, wherever the input is cut."
    source := "the contract of incremental decoding, Doc/library/codecs.rst; the same decoder's handling of \\x, \\u, \\U and \\N"
    status := .refuted, prop := ``UnicodeEscapeChunks, thm := some ``unicodeEscapeChunks_refuted
    bug := some "unicodeobj-codec-unicode-escape-octal-chunks" },
  { id := "unicodeobj-codec-raw-escape-round-trip", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_AsRawUnicodeEscapeString", "_PyUnicode_DecodeRawUnicodeEscapeStateful",
      "PyUnicode_DecodeRawUnicodeEscape"]
    statement := "s.encode('raw_unicode_escape') decodes back to s for every string with no backslash."
    source := "Doc/library/codecs.rst: existing backslashes are not escaped"
    status := .proven, prop := ``RawEscapeRoundTrip, thm := some ``rawEscapeRoundTrip_proven },
  { id := "unicodeobj-codec-latin1-round-trip", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_DecodeLatin1", "_PyUnicode_AsLatin1String", "PyUnicode_AsLatin1String"]
    statement := "Decoding any bytes as Latin-1 and encoding gives them back, under every error handler."
    source := "invariant: Latin-1 is the first 256 ordinals"
    status := .proven, prop := ``Latin1RoundTrip, thm := some ``latin1RoundTrip_proven },
  { id := "unicodeobj-codec-ucs1-strict-error", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_encode_ucs1", "_PyUnicode_AsASCIIString", "PyUnicode_AsASCIIString"]
    statement := "The strict ASCII and Latin-1 encoders report exactly the span from the first unencodable character to the end of the unencodable run."
    source := "invariant: exact error positions"
    status := .proven, prop := ``Ucs1StrictError, thm := some ``ucs1StrictError_proven },
  { id := "unicodeobj-codec-ascii-strict", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_DecodeASCII"]
    statement := "ASCII decoding accepts every all-ASCII input unchanged and otherwise raises at the first byte at or above 128."
    source := "invariant: exact error positions"
    status := .proven, prop := ``AsciiStrict, thm := some ``asciiStrict_proven },
  { id := "unicodeobj-codec-utf7-direct", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_EncodeUTF7", "PyUnicode_DecodeUTF7Stateful", "PyUnicode_DecodeUTF7"]
    statement := "A string of the characters the encoder leaves direct passes through UTF-7 unchanged in both directions."
    source := "RFC 2152"
    status := .proven, prop := ``Utf7Direct, thm := some ``utf7Direct_proven },
  { id := "unicodeobj-codec-utf7-round-trip", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_EncodeUTF7", "PyUnicode_DecodeUTF7Stateful"]
    statement := "Encoding to UTF-7 and decoding gives back every string of scalar values."
    source := "invariant: round trip"
    status := .open, prop := ``Utf7RoundTrip
    notes := "Held on 200000 random strings. Needs an invariant linking the encoder's and the decoder's base-64 state." },
  { id := "unicodeobj-codec-charmap-decode-string", pyFile := "Objects/unicodeobject.c"
    pyFns := ["charmap_decode_string", "PyUnicode_DecodeCharmap"]
    statement := "Charmap decoding by a str table maps each byte through the table when no byte is undefined."
    source := "invariant"
    status := .proven, prop := ``CharmapDecodeString, thm := some ``charmapDecodeString_proven },
  { id := "unicodeobj-codec-charmap-decode-mapping", pyFile := "Objects/unicodeobject.c"
    pyFns := ["charmap_decode_mapping", "PyUnicode_DecodeCharmap"]
    statement := "Charmap decoding by a mapping that gives each byte an int in range maps each byte through it."
    source := "invariant"
    status := .proven, prop := ``CharmapDecodeMapping, thm := some ``charmapDecodeMapping_proven },
  { id := "unicodeobj-codec-charmap-encode-mapping", pyFile := "Objects/unicodeobject.c"
    pyFns := ["charmapencode_lookup", "charmapencode_output", "_PyUnicode_EncodeCharmap",
      "PyUnicode_AsCharmapString"]
    statement := "Charmap encoding by a mapping that gives each character a byte maps each character through it."
    source := "invariant"
    status := .proven, prop := ``CharmapEncodeMapping, thm := some ``charmapEncodeMapping_proven },
  { id := "unicodeobj-codec-charmap-build-fffe", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_BuildEncodingMap", "encoding_map_lookup", "EncodingMap_size_impl"]
    statement := "PyUnicode_BuildEncodingMap never gives U+FFFE a byte, in either of its two results."
    source := "the decoder and the trie branch both treat U+FFFE as undefined"
    status := .refuted, prop := ``BuildMapsNoFFFE, thm := some ``buildMapsNoFFFE_refuted
    bug := some "unicodeobj-codec-charmap-build-fffe"
    notes := "No stdlib codec is affected." },
  { id := "unicodeobj-codec-replacements-ascii", pyFile := "Objects/unicodeobject.c"
    pyFns := ["backslashreplace", "xmlcharrefreplace"]
    statement := "The replacements of backslashreplace and xmlcharrefreplace are ASCII for every character."
    source := "invariant: the ASCII encoder writes them to its output unchecked"
    status := .proven, prop := ``ReplacementsAscii, thm := some ``replacementsAscii_proven },
  { id := "unicodeobj-codec-error-handler-names", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_Py_GetErrorHandler"]
    statement := "_Py_GetErrorHandler classifies each of its seven names to its handler and sends namereplace to the registry."
    source := "invariant"
    status := .proven, prop := ``ErrorHandlerNames, thm := some ``errorHandlerNames_proven },
  { id := "unicodeobj-codec-normalize-case", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_Py_normalize_encoding", "PyUnicode_Decode", "PyUnicode_AsEncodedString"]
    statement := "Encoding names are case-insensitive for the fast dispatch of PyUnicode_Decode and PyUnicode_AsEncodedString, for every name of bytes."
    source := "Doc/library/codecs.rst"
    status := .proven, prop := ``NormalizeCase, thm := some ``normalizeCase_proven }
,
  { id := "unicodeobj-codec-surrogateescape-round-trip", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_decode_utf8_impl"]
    statement := "surrogateescape round-trips every byte string through decode and encode."
    source := "PEP 383"
    status := .open, prop := ``SurrogateEscapeRoundTrip
    notes := "Not attempted." }
]

end PyLean.UnicodeObj
