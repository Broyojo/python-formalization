import PyLean.UnicodeObj.CodecsRegistry
import PyLean.BytesObj.Bytes.Escape

/-!
The `_codecs` functions of `Modules/_codecsmodule.c` (CPython 3.15.2) that do more than call
into `Objects/unicodeobject.c`: the registry wrappers, `escape_encode` and `escape_decode`, and
`_normalize_encoding`.
-/

namespace PyLean.UnicodeObj.Codecs

open PyLean PyLean.UnicodeObj

/-- The clinic `str` converter (Modules/clinic/_codecsmodule.c.h): `PyUnicode_AsUTF8AndSize`,
then "embedded null character" when `strlen` stops short. -/
def strArg (s : Str) : Py (List Nat) :=
  match utf8Encode s .strict with
  | .error e => .error e
  | .ok u => if u.contains 0 then .error (.valueError "embedded null character") else .ok u

/-- `_codecs_register`, _codecsmodule.c:64-72. -/
def codecsRegister (W : World) (st : Reg) (f : Val) : Reg × Py Val :=
  match register W st f with
  | (st', .ok ()) => (st', .ok .none)
  | (st', .error e) => (st', .error e)

/-- `_codecs_unregister`, _codecsmodule.c:84-93; `PyCodec_Unregister` cannot fail here. -/
def codecsUnregister (st : Reg) (f : Val) : Reg × Py Val := (unregister st f, .ok .none)

/-- `_codecs_lookup_impl`, _codecsmodule.c:104-109, behind its `str` converter. -/
def codecsLookup (W : World) (st : Reg) (encoding : Str) : Reg × Py Val :=
  match strArg encoding with
  | .error e => (st, .error e)
  | .ok enc => pyCodecLookup W st enc

/-- The `encoding` and `errors` arguments of `_codecs.encode`/`decode`: `str` or omitted
(`c_default="NULL"`). -/
def optStrArg (s : Option Str) : Py (Option (List Nat)) :=
  match s with
  | none => .ok none
  | some s => (strArg s).map some

/-- `_codecs_encode_impl`, _codecsmodule.c:126-136: no encoding means
`PyUnicode_GetDefaultEncoding()`, "utf-8". -/
def codecsEncode (W : World) (st : Reg) (obj : Val) (encoding errors : Option Str) : Reg × NPy Val :=
  match optStrArg encoding, optStrArg errors with
  | .error e, _ => (st, .error ⟨e, []⟩)
  | _, .error e => (st, .error ⟨e, []⟩)
  | .ok enc, .ok err =>
    pyCodecEncode W st obj (enc.getD (lit "utf-8")) (err.map fun e => (utf8Decode e .strict).toOption.getD [])

/-- `_codecs_decode_impl`, _codecsmodule.c:153-163. -/
def codecsDecode (W : World) (st : Reg) (obj : Val) (encoding errors : Option Str) : Reg × NPy Val :=
  match optStrArg encoding, optStrArg errors with
  | .error e, _ => (st, .error ⟨e, []⟩)
  | _, .error e => (st, .error ⟨e, []⟩)
  | .ok enc, .ok err =>
    pyCodecDecode W st obj (enc.getD (lit "utf-8")) (err.map fun e => (utf8Decode e .strict).toOption.getD [])

/-- `_codecs_register_error_impl`, _codecsmodule.c:971-979. -/
def codecsRegisterError (W : World) (st : Reg) (name : String) (h : Val) : Reg × Py Val :=
  match registerError W st name h with
  | (st', .ok ()) => (st', .ok .none)
  | (st', .error e) => (st', .error e)

/-- `_codecs__unregister_error_impl`, _codecsmodule.c:998-1003, returning a `bool`. -/
def codecsUnregisterError (st : Reg) (name : String) : Reg × Py Bool := unregisterError st name

/-- `_codecs_lookup_error_impl`, _codecsmodule.c:1016-1021. -/
def codecsLookupError (st : Reg) (name : String) : Py Val := lookupError st (some name)

/-! ## escape_encode and escape_decode, _codecsmodule.c:165-250 -/

/-- `codec_tuple`, _codecsmodule.c:167-174. -/
def codecTuple {α : Type} (decoded : Py α) (len : Nat) : Py (α × Nat) :=
  match decoded with
  | .error e => .error e
  | .ok v => .ok (v, len)

/-- One byte of `_codecs_escape_encode_impl`, _codecsmodule.c:220-246. `c` is a C `char`,
signed: from 0x80 on it is negative, so `c < ' '` holds and `c & 0xf0` still gives the high
nibble. -/
def escapeByte (c : Nat) : List Nat :=
  if c = 39 ∨ c = 92 then [92, c]
  else if c = 9 then [92, 116]
  else if c = 10 then [92, 110]
  else if c = 13 then [92, 114]
  else if c < 32 ∨ c ≥ 0x7f then [92, 120, hexLower ((c &&& 0xf0) >>> 4), hexLower (c &&& 0xf)]
  else [c]

/-- `_codecs_escape_encode_impl`, _codecsmodule.c:201-250. -/
def escapeEncode (data : Bytes) : Py (Bytes × Nat) :=
  if data.length > ssizeMaxN / 4 then .error (.overflowError "string is too large to encode")
  else codecTuple (.ok (data.flatMap escapeByte)) data.length

/-- `_codecs_escape_decode_impl`, _codecsmodule.c:184-192: `PyBytes_DecodeEscape`
(bytesobject.c:1284-1320, modelled in `BytesObj`), with the length of the input. The
`DeprecationWarning` text for an invalid escape is dropped. -/
def escapeDecode (data : Bytes) (errors : Option String) : Py (Bytes × Nat) :=
  codecTuple ((BytesObj.Bytes.bytesDecodeEscape data errors).map (·.1)) data.length

/-! ## _normalize_encoding, _codecsmodule.c:1023-1062 -/

/-- The loop of `_Py_normalize_encoding`, unicodeobject.c:3539-3564, on a buffer that cannot
fill (`lower_len` is the length plus one): a NUL ends the C string. `l` is the output so far,
reversed. -/
def normKeep (toLower : Bool) : List Nat → Bool → List Nat → List Nat
  | [], _, l => l.reverse
  | c :: cs, punct, l =>
    if c = 0 then l.reverse
    else if pyIsAlnum c || c == 46 then
      let l := if punct && !l.isEmpty then 95 :: l else l
      normKeep toLower cs false ((if toLower then cLower c else c) :: l)
    else normKeep toLower cs true l

/-- `_codecs__normalize_encoding_impl`, _codecsmodule.c:1033-1062: `PyUnicode_AsUTF8AndSize`,
`_Py_normalize_encoding(cstr, normalized, len + 1, 0)`, then `PyUnicode_FromString`. -/
def normalizeEncodingC (encoding : Str) : Py Str :=
  match utf8Encode encoding .strict with
  | .error e => .error e
  | .ok cstr =>
    if cstr.length > ssizeMaxN then .error (.overflowError "encoding is too large")
    else utf8Decode (normKeep false cstr false []) .strict

end PyLean.UnicodeObj.Codecs

namespace PyLean.UnicodeObj.Codecs

open PyLean PyLean.UnicodeObj

/-- `str.encode` with a name that misses the shortcuts: `_PyCodec_EncodeText`, then the
result checks of `PyUnicode_AsEncodedString`, unicodeobject.c:3888-3925 (a `bytearray` is
copied to `bytes` after a `RuntimeWarning`, which the model does not show). -/
def strEncodeRegistry (W : World) (st : Reg) (s : Str) (enc : List Nat) (errors : Option Str) :
    Reg × NPy Val :=
  match encodeText W st (.str s) enc errors with
  | (st', .error e) => (st', .error e)
  | (st', .ok v) =>
    match v with
    | .bytes _ => (st', .ok v)
    | .bytearray b => (st', .ok (.bytes b))
    | _ => (st', .error ⟨.typeError s!"'{toLeanString (trunc400 ((utf8Decode enc .strict).toOption.getD []))}' encoder returned '{v.tpName}' instead of 'bytes'; use codecs.encode() to encode to arbitrary types", []⟩)

/-- `bytes.decode` of non-empty bytes with a name that misses the shortcuts:
`_PyCodec_DecodeText` on a `memoryview` of the bytes, then the check of `PyUnicode_Decode`,
unicodeobject.c:3631-3650. -/
def bytesDecodeRegistry (W : World) (st : Reg) (view : Val) (enc : List Nat) (errors : Option Str) :
    Reg × NPy Val :=
  match decodeText W st view enc errors with
  | (st', .error e) => (st', .error e)
  | (st', .ok v) =>
    match v with
    | .str _ => (st', .ok v)
    | _ => (st', .error ⟨.typeError s!"'{toLeanString (trunc400 ((utf8Decode enc .strict).toOption.getD []))}' decoder returned '{v.tpName}' instead of 'str'; use codecs.decode() to decode to arbitrary types", []⟩)

end PyLean.UnicodeObj.Codecs
