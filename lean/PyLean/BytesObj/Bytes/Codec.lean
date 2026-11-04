import PyLean.BytesObj.Bytes.Obj
import PyLean.UnicodeObj.CodecProps

/-!
The codec calls of `bytes.decode` and `bytes(str, encoding, errors)`: `PyUnicode_Decode`
(Objects/unicodeobject.c:3570-3657) and `PyUnicode_AsEncodedString` (:3828-3925), on the codec
models of `lean/PyLean/UnicodeObj/` (`utf8Decode`, `asciiDecode`, `latin1Decode`, `utf8Encode`,
`ucs1Encode`).

Scope: the shortcut codecs utf-8, ascii and latin-1 (`_Py_normalize_encoding` and the name tests
of :3592-3630 and :3849-3887), and the error handlers `_Py_GetErrorHandler` knows. Every other
encoding, utf-16 and utf-32 included, and every other handler name, goes through the codec registry
(`_PyCodec_DecodeText`, `_PyCodec_EncodeText`), which is out of scope: `none`. The
`unicode_check_encoding_errors` checks run only in development mode (:531-536) and are not modelled.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-- The handler `errors` names; NULL is `strict`. `none`: a name `_Py_GetErrorHandler` does not
know (`_Py_ERROR_OTHER`), looked up in the registry when an error occurs. -/
def errHandlerOf (errors : Option String) : Option UnicodeObj.ErrHandler :=
  match errors with
  | none => some .strict
  | some e => UnicodeObj.getErrorHandler e

/-- The codec an encoding name reaches; NULL is utf-8 (:3587-3589, :3844-3846). -/
def shortcutOfName (encoding : Option String) : UnicodeObj.Shortcut :=
  match encoding with
  | none => .utf8
  | some e => UnicodeObj.shortcutOf (asc e)

/-- `PyUnicode_Decode(s, size, encoding, errors)`, unicodeobject.c:3570-3657: an empty input is the
empty string before the encoding is looked at (:3583-3585); then the shortcuts. Latin-1 ignores
`errors` (`PyUnicode_DecodeLatin1`, :7136-7142). -/
def unicodeDecode (s : Seq) (encoding errors : Option String) : Option (Py Seq) :=
  if s.length = 0 then some (.ok [])
  else
    match shortcutOfName encoding, errHandlerOf errors with
    | .latin1, _ => some (.ok (UnicodeObj.latin1Decode s))
    | .utf8, some h => some (UnicodeObj.utf8Decode s h)
    | .ascii, some h => some (UnicodeObj.asciiDecode s h)
    | _, _ => none

/-- `PyUnicode_AsEncodedString(unicode, encoding, errors)`, unicodeobject.c:3828-3925:
`_PyUnicode_AsUTF8String`, `_PyUnicode_AsASCIIString`, `_PyUnicode_AsLatin1String`. The
`namereplace` handler (the only user of `nameOf`) is not one `_Py_GetErrorHandler` knows. -/
def unicodeEncode (s : Seq) (encoding errors : Option String) : Option (Py Seq) :=
  match shortcutOfName encoding, errHandlerOf errors with
  | .utf8, some h => some (UnicodeObj.utf8Encode s h)
  | .ascii, some h => some (UnicodeObj.ucs1Encode s 128 h (fun _ => none))
  | .latin1, some h => some (UnicodeObj.ucs1Encode s 256 h (fun _ => none))
  | _, _ => none

end PyLean.BytesObj.Bytes
