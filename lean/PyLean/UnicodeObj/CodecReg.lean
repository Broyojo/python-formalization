import PyLean.Registry
import PyLean.UnicodeObj.CodecProps
import PyLean.UnicodeObj.CodecCallbackProps

/-! Registry entries of the codecs slice. -/

namespace PyLean.UnicodeObj

open PyLean.Registry

def codecEntries : List Entry := [
  { id := "unicodeobj-codec-utf8-rejects-forbidden", pyFile := "Objects/stringlib/codecs.h"
    pyFns := []
    statement := "The UTF-8 decoder rejects C0, C1 and F5..FF as lead bytes, overlong three- and four-byte forms, encoded surrogates and sequences above U+10FFFF, whatever follows."
    source := "The Unicode Standard, Table 3-7; RFC 3629; comments in codecs.h:150-158"
    status := .proven, prop := ``Utf8RejectsForbidden, thm := some ``utf8RejectsForbidden_proven },
  { id := "unicodeobj-codec-utf8-strict-iff-wf", pyFile := "Objects/stringlib/codecs.h"
    pyFns := []
    statement := "The strict UTF-8 decoder accepts exactly the well-formed sequences of Table 3-7."
    source := "The Unicode Standard, Table 3-7"
    status := .open, prop := ``Utf8StrictIffWellFormed
    notes := "Needs an induction over utf8DecodeLoop and utf8Wf together." },
  { id := "unicodeobj-codec-utf8-round-trip", pyFile := "Objects/stringlib/codecs.h"
    pyFns := []
    statement := "The strict UTF-8 encoder succeeds on every string of scalar values, and decoding its output gives the string back."
    source := "invariant: round trip; The Unicode Standard, Table 3-7"
    status := .proven, prop := ``Utf8RoundTrip, thm := some ``utf8RoundTrip_proven },
  { id := "unicodeobj-codec-utf16-round-trip", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "Encoding to UTF-16 and decoding with the same byteorder gives every string of scalar values back, surrogate pairs included, for little-endian, big-endian and BOM."
    source := "invariant: round trip"
    status := .proven, prop := ``Utf16RoundTrip, thm := some ``utf16RoundTrip_proven
    notes := "The model is a little-endian build. The aligned long reads and unrolled loops are modelled by the scalar path; the difftest checks them." },
  { id := "unicodeobj-codec-utf32-round-trip", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "Encoding to UTF-32 and decoding with the same byteorder gives every string of scalar values back, for little-endian, big-endian and BOM."
    source := "invariant: round trip"
    status := .proven, prop := ``Utf32RoundTrip, thm := some ``utf32RoundTrip_proven },
  { id := "unicodeobj-codec-decode-handler-advances", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "Every standard error handler returns a position past start on a decode error, so no decoder loop can repeat forever."
    source := "invariant: no hang"
    status := .proven, prop := ``DecodeHandlerAdvances, thm := some ``decodeHandlerAdvances_proven
    notes := "User-registered handlers can return any position; they are not modelled." },
  { id := "unicodeobj-codec-encode-handler-advances", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "Every standard error handler returns a position past start on an encode error."
    source := "invariant: no hang"
    status := .proven, prop := ``EncodeHandlerAdvances, thm := some ``encodeHandlerAdvances_proven },
  { id := "unicodeobj-codec-unicode-escape-round-trip", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "s.encode('unicode_escape') decodes back to s for every string, lone surrogates included, one-shot or stateful, and all of it is consumed."
    source := "invariant: round trip"
    status := .proven, prop := ``UnicodeEscapeRoundTrip, thm := some ``unicodeEscapeRoundTrip_proven
    notes := "The DeprecationWarning for invalid escapes has no effect on the result and is not modelled. \\N names come from a parameter." },
  { id := "unicodeobj-codec-unicode-escape-chunks", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "Decoding unicode_escape in two chunks gives what decoding at once gives, wherever the input is cut."
    source := "the contract of incremental decoding, Doc/library/codecs.rst; the same decoder's handling of \\x, \\u, \\U and \\N"
    status := .refuted, prop := ``UnicodeEscapeChunks, thm := some ``unicodeEscapeChunks_refuted
    bug := some "unicodeobj-codec-unicode-escape-octal-chunks" },
  { id := "unicodeobj-codec-raw-escape-round-trip", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "s.encode('raw_unicode_escape') decodes back to s for every string with no backslash."
    source := "Doc/library/codecs.rst: existing backslashes are not escaped"
    status := .proven, prop := ``RawEscapeRoundTrip, thm := some ``rawEscapeRoundTrip_proven },
  { id := "unicodeobj-codec-latin1-round-trip", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "Decoding any bytes as Latin-1 and encoding gives them back, under every error handler."
    source := "invariant: Latin-1 is the first 256 ordinals"
    status := .proven, prop := ``Latin1RoundTrip, thm := some ``latin1RoundTrip_proven },
  { id := "unicodeobj-codec-ucs1-strict-error", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_encode_ucs1", "raise_encode_exception"]
    statement := "The strict ASCII and Latin-1 encoders report exactly the span from the first unencodable character to the end of the unencodable run."
    source := "invariant: exact error positions"
    status := .proven, prop := ``Ucs1StrictError, thm := some ``ucs1StrictError_proven },
  { id := "unicodeobj-codec-ascii-strict", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "ASCII decoding accepts every all-ASCII input unchanged and otherwise raises at the first byte at or above 128."
    source := "invariant: exact error positions"
    status := .proven, prop := ``AsciiStrict, thm := some ``asciiStrict_proven },
  { id := "unicodeobj-codec-utf7-direct", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "A string of the characters the encoder leaves direct passes through UTF-7 unchanged in both directions."
    source := "RFC 2152"
    status := .proven, prop := ``Utf7Direct, thm := some ``utf7Direct_proven },
  { id := "unicodeobj-codec-utf7-round-trip", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "Encoding to UTF-7 and decoding gives back every string of scalar values."
    source := "invariant: round trip"
    status := .open, prop := ``Utf7RoundTrip
    notes := "Held on 200000 random strings. Needs an invariant linking the encoder's and the decoder's base-64 state." },
  { id := "unicodeobj-codec-charmap-decode-string", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "Charmap decoding by a str table maps each byte through the table when no byte is undefined."
    source := "invariant"
    status := .proven, prop := ``CharmapDecodeString, thm := some ``charmapDecodeString_proven },
  { id := "unicodeobj-codec-charmap-decode-mapping", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "Charmap decoding by a mapping that gives each byte an int in range maps each byte through it."
    source := "invariant"
    status := .proven, prop := ``CharmapDecodeMapping, thm := some ``charmapDecodeMapping_proven },
  { id := "unicodeobj-codec-charmap-encode-mapping", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "Charmap encoding by a mapping that gives each character a byte maps each character through it."
    source := "invariant"
    status := .proven, prop := ``CharmapEncodeMapping, thm := some ``charmapEncodeMapping_proven },
  { id := "unicodeobj-codec-charmap-build-fffe", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "PyUnicode_BuildEncodingMap never gives U+FFFE a byte, in either of its two results."
    source := "the decoder and the trie branch both treat U+FFFE as undefined"
    status := .refuted, prop := ``BuildMapsNoFFFE, thm := some ``buildMapsNoFFFE_refuted
    bug := some "unicodeobj-codec-charmap-build-fffe"
    notes := "No stdlib codec is affected." },
  { id := "unicodeobj-codec-replacements-ascii", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "The replacements of backslashreplace and xmlcharrefreplace are ASCII for every character."
    source := "invariant: the ASCII encoder writes them to its output unchecked"
    status := .proven, prop := ``ReplacementsAscii, thm := some ``replacementsAscii_proven },
  { id := "unicodeobj-codec-normalize-case", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_Py_normalize_encoding"]
    statement := "Encoding names are case-insensitive for the fast dispatch of PyUnicode_Decode and PyUnicode_AsEncodedString, for every name of bytes."
    source := "Doc/library/codecs.rst"
    status := .proven, prop := ``NormalizeCase, thm := some ``normalizeCase_proven }
,
  { id := "unicodeobj-codec-surrogateescape-round-trip", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "surrogateescape round-trips every byte string through decode and encode."
    source := "PEP 383"
    status := .open, prop := ``SurrogateEscapeRoundTrip
    notes := "Not attempted." },
  { id := "unicodeobj-codec-callback-decode-position", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_decode_call_errorhandler_writer", "make_decode_exception"]
    statement := "A decode handler can return any position. What reaches the decoder is inside the object as the handler left it, and a negative one counts from that object's end, for every handler, stateful or not."
    source := "invariant: no out-of-bounds read; codecs.register_error docs"
    status := .proven, prop := ``DecodeCallbackPosition, thm := some ``decodeCallbackPosition_proven }
,
  { id := "unicodeobj-codec-callback-encode-position", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_encode_call_errorhandler", "make_encode_exception"]
    statement := "The same for an encode handler, whose object cannot change."
    source := "invariant: no out-of-bounds read; codecs.register_error docs"
    status := .proven, prop := ``EncodeCallbackPosition, thm := some ``encodeCallbackPosition_proven }
,
  { id := "unicodeobj-codec-wide-std-callback", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_DecodeUTF16Stateful", "PyUnicode_DecodeUTF32Stateful", "unicode_decode_call_errorhandler_writer"]
    statement := "A standard handler reached through the callback path, which is the only path C has for UTF-16 and UTF-32, gives what the ErrHandler shortcut gives, and that shortcut is the decoder the round trips are proved over."
    source := "invariant: a handler's name does not change what it does"
    status := .proven, prop := ``WideStdIsCallback, thm := some ``wideStdIsCallback_proven }
,
  { id := "unicodeobj-codec-ascii-constant-handler", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_decode_call_errorhandler_writer"]
    statement := "With a handler that writes a fixed text and resumes after the error, ASCII decoding keeps every byte under 128 and calls the handler once per other byte, for every input."
    source := "codecs.register_error docs"
    status := .proven, prop := ``AsciiConstantHandler, thm := some ``asciiConstantHandler_proven }
,
  { id := "unicodeobj-codec-ucs1-inline-callback", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_encode_ucs1", "unicode_encode_call_errorhandler"]
    statement := "The inline replace, ignore, backslashreplace and xmlcharrefreplace of the ASCII and Latin-1 encoders give what the same handlers give through the callback path, for every string."
    source := "invariant: fast path vs generic path"
    status := .proven, prop := ``Ucs1InlineMatchesCallback, thm := some ``ucs1InlineMatchesCallback_proven }
,
  { id := "unicodeobj-codec-surrogateescape-error-span", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_encode_ucs1"]
    statement := "The inline surrogateescape of the ASCII and Latin-1 encoders also matches the callback path, error span included."
    source := "invariant: fast path vs generic path"
    status := .refuted, prop := ``Ucs1SurrogateEscapeMatchesCallback, thm := some ``ucs1SurrogateEscapeMatchesCallback_refuted
    bug := some "unicodeobj-codec-surrogateescape-error-span" }
]

end PyLean.UnicodeObj
