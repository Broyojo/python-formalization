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
    pyFns := ["unicode_encode_utf8"]
    statement := "Encoding then decoding gives back every string with no surrogate."
    source := "invariant: round trip"
    status := .open, prop := ``Utf8RoundTrip
    notes := "A kernel sweep over the code points exhausts the 8 GB limit; this needs a proof over the bit arithmetic of utf8EncodeChar and utf8Step." },
  { id := "unicodeobj-codec-surrogateescape-round-trip", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_decode_utf8_impl"]
    statement := "surrogateescape round-trips every byte string through decode and encode."
    source := "PEP 383"
    status := .open, prop := ``SurrogateEscapeRoundTrip
    notes := "Not attempted." }
]

end PyLean.UnicodeObj
