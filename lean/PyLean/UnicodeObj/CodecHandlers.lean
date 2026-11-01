import PyLean.UnicodeObj.TextTable

/-!
The standard error handlers of Python/codecs.c, as every codec sees them through
`unicode_decode_call_errorhandler_writer` (unicodeobject.c:4538-4635) and
`unicode_encode_call_errorhandler` (:7321-7374).

Only the eight registered handlers are modelled. A user callback could return any
position; the built-in ones always return a position past `start`, so the codec loops
terminate. `namereplace` looks names up in the Unicode name database, which the model
takes as the parameter `nameOf`, supplied by the difftest from `unicodedata.name`.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- `Py_UNICODE_IS_SURROGATE`. -/
def isSurrogate (c : Nat) : Bool := decide (0xD800 ≤ c) && decide (c ≤ 0xDFFF)

/-- An error handler, as `_Py_GetErrorHandler` classifies it. -/
inductive ErrHandler where
  | strict | ignore | replace | surrogateescape | backslashreplace | surrogatepass
  | xmlcharrefreplace | namereplace
  deriving Repr, DecidableEq

/-- `ENC_UTF8`..`ENC_UTF32BE` with `*bytelength`, or `ENC_UNKNOWN`:
`get_standard_encoding_impl`, Python/codecs.c:1157-1205, already applied to the name. -/
inductive EncCode where
  | utf8 | utf16le | utf16be | utf32le | utf32be | unknown
  deriving Repr, DecidableEq

def EncCode.bytelength : EncCode → Nat
  | .utf8 => 3
  | .utf16le | .utf16be => 2
  | .utf32le | .utf32be => 4
  | .unknown => 0

/-- `UnicodeDecodeError.__str__`, Objects/exceptions.c. -/
def decodeError (encoding : String) (input : Bytes) (start stop : Nat) (reason : String) : PyExc :=
  if stop = start + 1 then
    .named "UnicodeDecodeError"
      s!"'{encoding}' codec can't decode byte 0x{toLeanString (hexDigits 2 (input.getD start 0))} in position {start}: {reason}"
  else
    .named "UnicodeDecodeError"
      s!"'{encoding}' codec can't decode bytes in position {start}-{stop - 1}: {reason}"

/-- `\xHH`, `\uHHHH` or `\UHHHHHHHH`: `codec_handler_write_unicode_hex`, and the
character of a `UnicodeEncodeError` message. -/
def escapeEncodeChar (c : Nat) : Str :=
  if c ≤ 0xff then [92, 120] ++ hexDigits 2 c
  else if c ≤ 0xffff then [92, 117] ++ hexDigits 4 c
  else [92, 85] ++ hexDigits 8 c

/-- `UnicodeEncodeError.__str__`, Objects/exceptions.c. -/
def encodeError (encoding : String) (input : Str) (start stop : Nat) (reason : String) : PyExc :=
  if stop = start + 1 then
    .named "UnicodeEncodeError"
      s!"'{encoding}' codec can't encode character '{toLeanString (escapeEncodeChar (input.getD start 0))}' in position {start}: {reason}"
  else
    .named "UnicodeEncodeError"
      s!"'{encoding}' codec can't encode characters in position {start}-{stop - 1}: {reason}"

/-- `wrong_exception_type`, Python/codecs.c. -/
def wrongExceptionType (name : String) : PyExc :=
  .typeError s!"don't know how to handle {name} in error callback"

/-- The code unit a `surrogatepass` decode reads at `p`, Python/codecs.c:1345-1381. -/
def surrogatePassRead (code : EncCode) (p : List Nat) : Nat :=
  match code, p with
  | .utf8, a :: b :: c :: _ =>
    if a &&& 0xf0 == 0xe0 && b &&& 0xc0 == 0x80 && c &&& 0xc0 == 0x80 then
      ((a &&& 0x0f) <<< 12) + ((b &&& 0x3f) <<< 6) + (c &&& 0x3f)
    else 0
  | .utf16le, a :: b :: _ => b * 256 + a
  | .utf16be, a :: b :: _ => a * 256 + b
  | .utf32le, a :: b :: c :: d :: _ => d * 16777216 + c * 65536 + b * 256 + a
  | .utf32be, a :: b :: c :: d :: _ => a * 16777216 + b * 65536 + c * 256 + d
  | _, _ => 0

/-- The leading bytes at or above 128, at most 4: the loop of
`_PyCodec_SurrogateEscapeUnicodeDecodeError`, Python/codecs.c:1467-1490. -/
def escapeRun : Nat → List Nat → List Nat
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, b :: bs => if b < 128 then [] else b :: escapeRun n bs

/-- Calling a standard handler on a `UnicodeDecodeError`: the replacement and `newpos`. -/
def decodeHandlerCall (h : ErrHandler) (enc : String) (code : EncCode) (input : Bytes)
    (start stop : Nat) (reason : String) : Py (Str × Nat) :=
  let bad := decodeError enc input start stop reason
  let slice := (input.drop start).take (stop - start)
  match h with
  | .strict => .error bad
  | .ignore => .ok ([], stop)
  | .replace => .ok ([0xfffd], stop)
  | .backslashreplace => .ok (slice.flatMap fun b => [92, 120] ++ hexDigits 2 b, stop)
  | .surrogateescape =>
    let run := escapeRun 4 slice
    if run.isEmpty then .error bad else .ok (run.map (· + 0xdc00), start + run.length)
  | .surrogatepass =>
    if code == .unknown then .error bad
    else
      let ch := if input.length - start ≥ code.bytelength
        then surrogatePassRead code (input.drop start) else 0
      if isSurrogate ch then .ok ([ch], start + code.bytelength) else .error bad
  | .xmlcharrefreplace | .namereplace => .error (wrongExceptionType "UnicodeDecodeError")

/-- A replacement from an encode handler: `bytes` or `str`. -/
inductive EncRep where
  | bytes (b : List Nat)
  | str (s : Str)
  deriving Repr, DecidableEq

/-- The decimal digits of `n`, written in front of `acc`. -/
def decChars : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let a := (48 + n % 10) :: acc
    if n / 10 = 0 then a else decChars fuel (n / 10) a

/-- `&#NNN;`, `PyCodec_XMLCharRefReplaceErrors`, Python/codecs.c:903-950. -/
def xmlRef (c : Nat) : List Nat := [38, 35] ++ decChars (c + 1) c [] ++ [59]

/-- The bytes of one surrogate, `_PyCodec_SurrogatePassUnicodeEncodeError`. -/
def surrogatePassBytes (code : EncCode) (ch : Nat) : List Nat :=
  match code with
  | .utf8 => [0xe0 ||| (ch >>> 12), 0x80 ||| ((ch >>> 6) &&& 0x3f), 0x80 ||| (ch &&& 0x3f)]
  | .utf16le => [ch % 256, ch / 256 % 256]
  | .utf16be => [ch / 256 % 256, ch % 256]
  | .utf32le => [ch % 256, ch / 256 % 256, ch / 65536 % 256, ch / 16777216 % 256]
  | .utf32be => [ch / 16777216 % 256, ch / 65536 % 256, ch / 256 % 256, ch % 256]
  | .unknown => []

/-- Calling a standard handler on a `UnicodeEncodeError`: the replacement and `newpos`. -/
def encodeHandlerCall (h : ErrHandler) (nameOf : Nat → Option Str) (enc : String) (code : EncCode)
    (input : Str) (start stop : Nat) (reason : String) : Py (EncRep × Nat) :=
  let bad := encodeError enc input start stop reason
  let run := (input.drop start).take (stop - start)
  match h with
  | .strict => .error bad
  | .ignore => .ok (.str [], stop)
  | .replace => .ok (.str (List.replicate run.length 63), stop)
  | .backslashreplace => .ok (.str (run.flatMap escapeEncodeChar), stop)
  | .xmlcharrefreplace => .ok (.str (run.flatMap xmlRef), stop)
  | .namereplace =>
    .ok (.str (run.flatMap fun c =>
      match nameOf c with
      | some n => [92, 78, 123] ++ n ++ [125]
      | none => escapeEncodeChar c), stop)
  | .surrogatepass =>
    if code == .unknown || !run.all isSurrogate then .error bad
    else .ok (.bytes (run.flatMap (surrogatePassBytes code)), stop)
  | .surrogateescape =>
    if run.all fun c => decide (0xdc80 ≤ c) && decide (c ≤ 0xdcff)
    then .ok (.bytes (run.map (· - 0xdc00)), stop)
    else .error bad

end PyLean.UnicodeObj
