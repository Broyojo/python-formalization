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
  { id := "unicodeobj-codec-surrogateescape-round-trip", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_decode_utf8_impl"]
    statement := "surrogateescape round-trips every byte string through decode and encode."
    source := "PEP 383"
    status := .open, prop := ``SurrogateEscapeRoundTrip
    notes := "Not attempted." }
]

end PyLean.UnicodeObj
