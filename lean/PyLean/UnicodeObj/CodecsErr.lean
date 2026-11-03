import PyLean.UnicodeObj.CodecProps

/-!
The standard error handlers of `Python/codecs.c` (CPython 3.15.2), called directly on an
exception object, as `codecs.lookup_error(name)(exc)` does. User code can build the object
with any class and leave its attributes in any state, so every check and every early return
of the handlers is mirrored, together with the accessors of `Objects/exceptions.c` they go
through (`_PyUnicodeError_GetParams` and the clamping of `start` and `end`).

The model of the same handlers as the codec loops see them, on exceptions the codecs build
themselves, is `CodecHandlers.lean`. `CodecsErrProps.lean` proves the two agree.

Scope:
* Classes are type names. `PyObject_TypeCheck` walks `tp_mro`, which no metaclass can
  override, and is taken as the oracle `Hier.sub`, constrained only by what CPython
  guarantees (`HierOk`).
* The `encoding`, `object` and `reason` slots are `_Py_T_OBJECT` members: NULL after
  `del exc.object` or before `__init__`, otherwise any object. `start` and `end` are
  `Py_T_PYSSIZET` members, so they always hold a `Py_ssize_t`.
* `namereplace` gets names from `unicodedata`'s C API, the parameter `getname`, which is
  `ucnhash_capi->getname(c, buffer, 256, 1)`; `capi` is what `_PyUnicode_GetNameCAPI`
  returns, an error when the capsule cannot be imported.
* A failed allocation (`MemoryError`) is not modelled.
-/

namespace PyLean.UnicodeObj.Codecs

open PyLean PyLean.UnicodeObj

/-! ## Classes -/

/-- `issubclass` between types as `PyObject_TypeCheck` sees it: `sub c b` when `b` is in the
MRO of `c`. -/
structure Hier where
  sub : String → String → Bool

/-- The builtin bases on the way from the three error classes, and from `IndexError`, to
`BaseException`, Objects/exceptions.c (`SimpleExtendsException(PyExc_ValueError, UnicodeError,
...)`, `SimpleExtendsException(PyExc_LookupError, IndexError, ...)` and the
`ComplexExtendsException(PyExc_UnicodeError, ...)` definitions). -/
def builtinBase : String → Option String
  | "UnicodeEncodeError" | "UnicodeDecodeError" | "UnicodeTranslateError" => some "UnicodeError"
  | "UnicodeError" => some "ValueError"
  | "ValueError" => some "Exception"
  | "IndexError" => some "LookupError"
  | "LookupError" => some "Exception"
  | "Exception" => some "BaseException"
  | _ => none

/-- What CPython guarantees of the MRO relation: reflexive, transitive, the builtin bases, and
no class below two of the three error classes: each is its own solid base, so
`class X(UnicodeEncodeError, UnicodeDecodeError)` fails with "multiple bases have instance
lay-out conflict" (typeobject.c, `best_base`). -/
def HierOk (H : Hier) : Prop :=
  (∀ c, H.sub c c = true) ∧
  (∀ a b c, H.sub a b = true → H.sub b c = true → H.sub a c = true) ∧
  (∀ c b, builtinBase c = some b → H.sub c b = true) ∧
  (∀ c, ¬ (H.sub c "UnicodeEncodeError" = true ∧ H.sub c "UnicodeDecodeError" = true)) ∧
  (∀ c, ¬ (H.sub c "UnicodeEncodeError" = true ∧ H.sub c "UnicodeTranslateError" = true)) ∧
  (∀ c, ¬ (H.sub c "UnicodeDecodeError" = true ∧ H.sub c "UnicodeTranslateError" = true))

/-- `_PyIsUnicodeEncodeError`, codecs.c:673-674. -/
def Hier.isEnc (H : Hier) (c : String) : Bool := H.sub c "UnicodeEncodeError"
/-- `_PyIsUnicodeDecodeError`, codecs.c:675-676. -/
def Hier.isDec (H : Hier) (c : String) : Bool := H.sub c "UnicodeDecodeError"
/-- `_PyIsUnicodeTranslateError`, codecs.c:677-678. -/
def Hier.isTr (H : Hier) (c : String) : Bool := H.sub c "UnicodeTranslateError"

/-! ## The exception object -/

/-- An object slot of a `PyUnicodeErrorObject`: NULL, a `str` (or subclass, by
`PyUnicode_Check`), a `bytes` (or subclass, by `PyBytes_Check`), or anything else. -/
inductive Slot where
  | null
  | str (s : Str)
  | bytes (b : Bytes)
  | other
  deriving Repr, DecidableEq

/-- The object handed to a handler. `cls` is its type and `tpName` how `%T` prints that type.
The other fields are read only when `cls` is below one of the three error classes, which is
when the object is a `PyUnicodeErrorObject`. -/
structure ExcObj where
  cls : String
  tpName : String
  encoding : Slot
  object : Slot
  start : Int
  stop : Int
  deriving Repr

/-- How a handler fails: a new exception, or `PyErr_SetObject(PyExceptionInstance_Class(exc),
exc)`, which raises the handler's argument itself. -/
inductive HErr where
  | exc (e : PyExc)
  | reraise
  deriving Repr, DecidableEq

abbrev HPy (α : Type) := Except HErr α

def raiseT {α : Type} (msg : String) : HPy α := .error (.exc (.typeError msg))

/-- The replacement a handler returns. -/
inductive Rep where
  | str (s : Str)
  | bytes (b : Bytes)
  deriving Repr, DecidableEq

/-- `PY_SSIZE_T_MAX`. -/
def ssizeMaxN : Nat := 2 ^ 63 - 1

/-! ## Accessors, Objects/exceptions.c -/

/-- `check_unicode_error_attribute` then `as_unicode_error_attribute`,
exceptions.c:3065-3098: the slot as a `str` (`asBytes = false`) or a `bytes`. -/
def asAttr (slot : Slot) (name : String) (asBytes : Bool) : HPy (List Nat) :=
  match slot with
  | .null => raiseT s!"UnicodeError '{name}' attribute is not set"
  | v =>
    let content : Option (List Nat) :=
      match asBytes, v with
      | true, .bytes b => some b
      | false, .str s => some s
      | _, _ => none
    match content with
    | some c => .ok c
    | none => raiseT s!"UnicodeError '{name}' attribute must be a {if asBytes then "bytes" else "string"}"

/-- `check_unicode_error_type`, exceptions.c:3127-3137. -/
def checkType (H : Hier) (e : ExcObj) (expect : String) : HPy Unit :=
  if H.sub e.cls "UnicodeError" then .ok ()
  else raiseT s!"expecting a {expect} object, got {e.tpName}"

/-- `unicode_error_adjust_start`, exceptions.c:3242-3253. -/
def adjustStart (start : Int) (n : Nat) : Int :=
  let start := if start < 0 then 0 else start
  if start ≥ n then (if n = 0 then 0 else (n : Int) - 1) else start

/-- `unicode_error_adjust_end`, exceptions.c:3283-3294. -/
def adjustEnd (stop : Int) (n : Nat) : Int :=
  let stop := if stop < 1 then 1 else stop
  if stop > n then n else stop

/-- `unicode_error_adjust_len`, exceptions.c:3329-3337. -/
def adjustLen (start stop : Int) : Int :=
  let r := stop - start
  if r < 0 then 0 else r

/-- The output parameters of `_PyUnicodeError_GetParams`. -/
structure Params where
  obj : List Nat
  objlen : Nat
  start : Nat
  stop : Nat
  slen : Nat
  deriving Repr

/-- `_PyUnicodeError_GetParams`, exceptions.c:3382-3431. The clipped values are never
negative (exceptions.c:3256-3351), so they are kept as `Nat`. -/
def getParams (e : ExcObj) (asBytes : Bool) : HPy Params := do
  let r ← asAttr e.object "object" asBytes
  let n := r.length
  let s := adjustStart e.start n
  let t := adjustEnd e.stop n
  pure ⟨r, n, s.toNat, t.toNat, (adjustLen s t).toNat⟩

/-- `PyUnicodeEncodeError_GetEncoding` and `PyUnicodeDecodeError_GetEncoding`,
exceptions.c:3437-3450, through `unicode_error_get_encoding_impl` (:3149-3155). -/
def getEncoding (H : Hier) (e : ExcObj) (expect : String) : HPy Str := do
  checkType H e expect
  asAttr e.encoding "encoding" false

/-- `PyUnicodeDecodeError_GetEnd`, exceptions.c:3573-3578, through
`unicode_error_get_end_impl` (:3555-3562). -/
def decodeGetEnd (H : Hier) (e : ExcObj) : HPy Nat := do
  checkType H e "UnicodeDecodeError"
  let p ← getParams e true
  pure p.stop

/-! ## Helpers, codecs.c:665-772 -/

/-- `wrong_exception_type`, codecs.c:665-670. -/
def wrongType {α : Type} (e : ExcObj) : HPy α :=
  raiseT s!"don't know how to handle {e.tpName} in error callback"

/-- `codec_handler_unicode_hex_width`, codecs.c:687-702. -/
def hexWidth (ch : Nat) : Nat :=
  if ch ≥ 0x10000 then 1 + 1 + 8
  else if ch ≥ 0x100 then 1 + 1 + 4
  else 1 + 1 + 2

/-- `Py_hexdigits[(ch >> k) & 0xf]`, codecs.c:28. -/
def hexAt (ch k : Nat) : Nat := hexLower ((ch >>> k) &&& 0xf)

/-- `codec_handler_write_unicode_hex`, codecs.c:709-732: what it writes. -/
def writeUnicodeHex (ch : Nat) : List Nat :=
  [92] ++
  (if ch ≥ 0x10000 then [85, hexAt ch 28, hexAt ch 24, hexAt ch 20, hexAt ch 16, hexAt ch 12, hexAt ch 8]
   else if ch ≥ 0x100 then [117, hexAt ch 12, hexAt ch 8]
   else [120]) ++
  [hexAt ch 4, hexAt ch 0]

/-- `n_decimal_digits_for_codepoint`, codecs.c:739-751. Past 10^7 the source has
`Py_UNREACHABLE()`, which a `str` (code points up to 0x10FFFF) never reaches; the model
returns 0 there. -/
def nDecimalDigits (ch : Nat) : Nat :=
  if ch < 10 then 1
  else if ch < 100 then 2
  else if ch < 1000 then 3
  else if ch < 10000 then 4
  else if ch < 100000 then 5
  else if ch < 1000000 then 6
  else if ch < 10000000 then 7
  else 0

/-- The digit loop of codecs.c:946-950: `k` digits written from the last one back, each
`'0' + ch % 10`; `acc` holds those already written. -/
def decFill : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | k + 1, ch, acc => decFill k (ch / 10) ((48 + ch % 10) :: acc)

/-- `codec_handler_unicode_replacement_character`, codecs.c:758-772. -/
def replacementChars (count : Nat) : Str := List.replicate count 0xfffd

/-- The code points (or bytes) at `start <= i < end`. -/
def slice (l : List Nat) (start stop : Nat) : List Nat := (l.drop start).take (stop - start)

/-- The guard against an oversized replacement, codecs.c:915-919, :982-986, :1249-1253:
when `slen > PY_SSIZE_T_MAX / width` the range is cut to that many characters. -/
def guardRange (width : Nat) (p : Params) : Nat × Nat :=
  if p.slen > ssizeMaxN / width then
    let stop := min (p.start + ssizeMaxN / width) p.objlen
    (stop, stop - p.start)
  else (p.stop, p.slen)

/-- A handler body: the size it allocates, what it writes, and the position it returns. -/
structure Body where
  alloc : Nat
  out : Rep
  pos : Nat
  deriving Repr

def Body.result (b : Body) : Rep × Nat := (b.out, b.pos)

/-! ## strict and ignore, codecs.c:775-816 -/

/-- `PyCodec_StrictErrors`, codecs.c:777-786. -/
def strictErrors (H : Hier) (e : ExcObj) : HPy (Rep × Nat) :=
  if H.sub e.cls "BaseException" then .error .reraise
  else raiseT "codec must pass exception instance"

/-- `_PyCodec_IgnoreError`, codecs.c:791-801. -/
def ignoreError (e : ExcObj) (asBytes : Bool) : HPy Body := do
  let p ← getParams e asBytes
  pure ⟨0, .str [], p.stop⟩

/-- `PyCodec_IgnoreErrors`, codecs.c:804-816. -/
def ignoreErrors (H : Hier) (e : ExcObj) : HPy Body :=
  if H.isEnc e.cls || H.isTr e.cls then ignoreError e false
  else if H.isDec e.cls then ignoreError e true
  else wrongType e

/-! ## replace, codecs.c:819-889 -/

/-- `_PyCodec_ReplaceUnicodeEncodeError`, codecs.c:821-839. -/
def replaceEncode (e : ExcObj) : HPy Body := do
  let p ← getParams e false
  pure ⟨p.slen, .str (List.replicate p.slen 63), p.stop⟩

/-- `_PyCodec_ReplaceUnicodeDecodeError`, codecs.c:842-854. -/
def replaceDecode (H : Hier) (e : ExcObj) : HPy Body := do
  let stop ← decodeGetEnd H e
  pure ⟨1, .str (replacementChars 1), stop⟩

/-- `_PyCodec_ReplaceUnicodeTranslateError`, codecs.c:857-871. -/
def replaceTranslate (e : ExcObj) : HPy Body := do
  let p ← getParams e false
  pure ⟨p.slen, .str (replacementChars p.slen), p.stop⟩

/-- `PyCodec_ReplaceErrors`, codecs.c:874-889. -/
def replaceErrors (H : Hier) (e : ExcObj) : HPy Body :=
  if H.isEnc e.cls then replaceEncode e
  else if H.isDec e.cls then replaceDecode H e
  else if H.isTr e.cls then replaceTranslate e
  else wrongType e

/-! ## xmlcharrefreplace, codecs.c:892-959 -/

/-- One `&#DIGITS;` block, codecs.c:944-953. -/
def xmlBlock (ch : Nat) : List Nat := [38, 35] ++ decFill (nDecimalDigits ch) ch [] ++ [59]

/-- `PyCodec_XMLCharRefReplaceErrors`, codecs.c:894-959: the size loop (:921-928), then the
write loop (:938-954). -/
def xmlCharRefReplaceErrors (H : Hier) (e : ExcObj) : HPy Body := do
  if !H.isEnc e.cls then wrongType e
  else
    let p ← getParams e false
    let (stop, _) := guardRange (2 + 7 + 1) p
    let chars := slice p.obj p.start stop
    let ressize := chars.foldl (fun acc ch => acc + (2 + nDecimalDigits ch + 1)) 0
    pure ⟨ressize, .str (chars.flatMap xmlBlock), stop⟩

/-! ## backslashreplace, codecs.c:962-1065 -/

/-- `_PyCodec_BackslashReplaceUnicodeEncodeError`, codecs.c:964-1006. -/
def backslashEncode (e : ExcObj) : HPy Body := do
  let p ← getParams e false
  let (stop, _) := guardRange (1 + 1 + 8) p
  let chars := slice p.obj p.start stop
  let ressize := chars.foldl (fun acc c => acc + hexWidth c) 0
  pure ⟨ressize, .str (chars.flatMap writeUnicodeHex), stop⟩

/-- One `\xhh` for a byte, codecs.c:1030-1034. -/
def byteHex (ch : Nat) : List Nat := [92, 120, hexLower ((ch >>> 4) &&& 0xf), hexLower (ch &&& 0xf)]

/-- `_PyCodec_BackslashReplaceUnicodeDecodeError`, codecs.c:1009-1039. -/
def backslashDecode (e : ExcObj) : HPy Body := do
  let p ← getParams e true
  pure ⟨4 * p.slen, .str ((slice p.obj p.start p.stop).flatMap byteHex), p.stop⟩

/-- `PyCodec_BackslashReplaceErrors`, codecs.c:1050-1065; a translate error goes to the
encode body (:1042-1047). -/
def backslashReplaceErrors (H : Hier) (e : ExcObj) : HPy Body :=
  if H.isEnc e.cls then backslashEncode e
  else if H.isDec e.cls then backslashDecode e
  else if H.isTr e.cls then backslashEncode e
  else wrongType e

/-! ## namereplace, codecs.c:1068-1137 -/

/-- The size of one replacement, codecs.c:1095-1103. -/
def nameSize (getname : Nat → Option Str) (c : Nat) : Nat :=
  match getname c with
  | some n => 1 + 1 + 1 + n.length + 1
  | none => hexWidth c

/-- The size loop, codecs.c:1093-1108, over the characters from `imax` on: it stops at
`end`, or before a character whose replacement would take `ressize` past
`PY_SSIZE_T_MAX`. Returns the final `imax` and `ressize`. -/
def nameSizeLoop (getname : Nat → Option Str) : List Nat → Nat → Nat → Nat × Nat
  | [], imax, ressize => (imax, ressize)
  | c :: cs, imax, ressize =>
    let replsize := nameSize getname c
    if ressize > ssizeMaxN - replsize then (imax, ressize)
    else nameSizeLoop getname cs (imax + 1) (ressize + replsize)

/-- One replacement as the write loop writes it, codecs.c:1119-1129. -/
def nameBlock (getname : Nat → Option Str) (c : Nat) : List Nat :=
  match getname c with
  | some n => [92, 78, 123] ++ n ++ [125]
  | none => writeUnicodeHex c

/-- `PyCodec_NameReplaceErrors`, codecs.c:1070-1137. -/
def nameReplaceErrors (H : Hier) (capi : Except PyExc (Nat → Option Str)) (e : ExcObj) :
    HPy Body := do
  if !H.isEnc e.cls then wrongType e
  else
    let getname ← match capi with
      | .ok g => (pure g : HPy _)
      | .error x => .error (.exc x)
    let p ← getParams e false
    let (imax, ressize) := nameSizeLoop getname (slice p.obj p.start p.stop) p.start 0
    pure ⟨ressize, .str ((slice p.obj p.start imax).flatMap (nameBlock getname)), imax⟩

/-! ## surrogatepass, codecs.c:1140-1410 -/

/-- `Py_TOLOWER` on a byte: ASCII only. -/
def cLower (c : Nat) : Nat := if 65 ≤ c ∧ c ≤ 90 then c + 32 else c

/-- `p[i]` of a C string whose bytes are `l`, terminated by its NUL: `none` for a read past the
NUL, outside the string. -/
def cAt (l : List Nat) (i : Nat) : Option Nat :=
  if i < l.length then l[i]? else if i = l.length then some 0 else none

/-- The tail of `get_standard_encoding_impl` after `utf16`/`utf32`, codecs.c:1161-1178 and
:1181-1198, with `encoding` at offset `o`: `bare` is the byte order of the bare name on a
little-endian build (`WORDS_BIGENDIAN` unset). Each read goes through `cAt`, in the order of the
`&&` chains. -/
def stdTail (le be bare : EncCode) (enc : List Nat) (o : Nat) : Option EncCode := do
  let c0 ← cAt enc o
  if c0 = 0 then return bare
  let o := if c0 = 45 ∨ c0 = 95 then o + 1 else o
  let d0 ← cAt enc o
  if d0 = 0 then return .unknown
  let d1 ← cAt enc (o + 1)
  if cLower d1 ≠ 101 then return .unknown
  let d2 ← cAt enc (o + 2)
  if d2 ≠ 0 then return .unknown
  if cLower d0 = 98 then return be
  if cLower d0 = 108 then return le
  return .unknown

/-- `get_standard_encoding_impl`, codecs.c:1147-1206, on the bytes of a C string, with every
read checked (`none` is a read past the terminating NUL). `*bytelength` is
`EncCode.bytelength` of the code returned. -/
def stdImplM (enc : List Nat) : Option EncCode := do
  let a ← cAt enc 0
  let utf ← if cLower a ≠ 117 then pure false else do
    let b ← cAt enc 1
    if cLower b ≠ 116 then pure false else do
      let c ← cAt enc 2
      pure (cLower c = 102)
  if utf then
    let x ← cAt enc 3
    let o := if x = 45 ∨ x = 95 then 4 else 3
    let y0 ← cAt enc o
    let is8 ← if y0 ≠ 56 then pure false else do
      let y1 ← cAt enc (o + 1)
      pure (y1 = 0)
    if is8 then return .utf8
    let is16 ← if y0 ≠ 49 then pure false else do
      let y1 ← cAt enc (o + 1)
      pure (y1 = 54)
    if is16 then stdTail .utf16le .utf16be .utf16le enc (o + 2)
    else
      let is32 ← if y0 ≠ 51 then pure false else do
        let y1 ← cAt enc (o + 1)
        pure (y1 = 50)
      if is32 then stdTail .utf32le .utf32be .utf32le enc (o + 2)
      else return .unknown
  else if enc = lit "cp65001" then return .utf8
  else return .unknown

/-- The code `get_standard_encoding_impl` returns. `stdImpl_safe` shows that no read falls past
the NUL, so the default is never taken. -/
def stdEncodingImpl (enc : List Nat) : EncCode := (stdImplM enc).getD .unknown

/-- `get_standard_encoding`, codecs.c:1209-1218: `PyUnicode_AsUTF8` (which fails on a lone
surrogate with the UTF-8 encoder's error), then the C string, which ends at the first NUL. -/
def stdEncoding (enc : Str) : HPy EncCode :=
  match utf8Encode enc .strict with
  | .error x => .error (.exc x)
  | .ok u => .ok (stdEncodingImpl (u.takeWhile (· ≠ 0)))

/-- The standard encoding the `encoding` attribute names: `PyUnicode*Error_GetEncoding` then
`get_standard_encoding`, codecs.c:1226-1235 and :1317-1326. -/
def encCodeOf (H : Hier) (e : ExcObj) (expect : String) : HPy EncCode := do
  let enc ← getEncoding H e expect
  stdEncoding enc

/-- The bytes of one surrogate, codecs.c:1270-1301. `(unsigned char)x` is `x % 256`. -/
def passBytes (code : EncCode) (ch : Nat) : List Nat :=
  match code with
  | .utf8 => [(0xe0 ||| (ch >>> 12)) % 256, (0x80 ||| ((ch >>> 6) &&& 0x3f)) % 256,
              (0x80 ||| (ch &&& 0x3f)) % 256]
  | .utf16le => [ch % 256, (ch >>> 8) % 256]
  | .utf16be => [(ch >>> 8) % 256, ch % 256]
  | .utf32le => [ch % 256, (ch >>> 8) % 256, (ch >>> 16) % 256, (ch >>> 24) % 256]
  | .utf32be => [(ch >>> 24) % 256, (ch >>> 16) % 256, (ch >>> 8) % 256, ch % 256]
  | .unknown => []

/-- The write loop of codecs.c:1262-1302: fails with the original exception at the first
character that is not a surrogate. -/
def passWrite (code : EncCode) : List Nat → HPy (List Nat)
  | [] => .ok []
  | ch :: cs =>
    if !isSurrogate ch then .error .reraise
    else do
      let rest ← passWrite code cs
      pure (passBytes code ch ++ rest)

/-- `_PyCodec_SurrogatePassUnicodeEncodeError`, codecs.c:1223-1311. -/
def surrogatePassEncode (H : Hier) (e : ExcObj) : HPy Body := do
  let code ← encCodeOf H e "UnicodeEncodeError"
  if code = .unknown then .error .reraise
  else
    let p ← getParams e false
    let (stop, slen) := guardRange code.bytelength p
    let out ← passWrite code (slice p.obj p.start stop)
    pure ⟨code.bytelength * slen, .bytes out, stop⟩

/-- The code unit read at `p`, codecs.c:1346-1377: 0 when fewer than `bytelength` bytes are
left or the UTF-8 bytes are not a three-byte form. -/
def passRead (code : EncCode) (p : List Nat) : Nat :=
  let b (i : Nat) := p.getD i 0
  match code with
  | .utf8 =>
    if b 0 &&& 0xf0 = 0xe0 ∧ b 1 &&& 0xc0 = 0x80 ∧ b 2 &&& 0xc0 = 0x80 then
      ((b 0 &&& 0x0f) <<< 12) + ((b 1 &&& 0x3f) <<< 6) + (b 2 &&& 0x3f)
    else 0
  | .utf16le => b 1 <<< 8 ||| b 0
  | .utf16be => b 0 <<< 8 ||| b 1
  | .utf32le => (b 3 <<< 24) ||| (b 2 <<< 16) ||| (b 1 <<< 8) ||| b 0
  | .utf32be => (b 0 <<< 24) ||| (b 1 <<< 16) ||| (b 2 <<< 8) ||| b 3
  | .unknown => 0

/-- `_PyCodec_SurrogatePassUnicodeDecodeError`, codecs.c:1314-1392. -/
def surrogatePassDecode (H : Hier) (e : ExcObj) : HPy Body := do
  let code ← encCodeOf H e "UnicodeDecodeError"
  if code = .unknown then .error .reraise
  else
    let p ← getParams e true
    let ch := if p.objlen - p.start ≥ code.bytelength then passRead code (p.obj.drop p.start) else 0
    if !isSurrogate ch then .error .reraise
    else pure ⟨1, .str [ch], p.start + code.bytelength⟩

/-- `PyCodec_SurrogatePassErrors`, codecs.c:1397-1410. -/
def surrogatePassErrors (H : Hier) (e : ExcObj) : HPy Body :=
  if H.isEnc e.cls then surrogatePassEncode H e
  else if H.isDec e.cls then surrogatePassDecode H e
  else wrongType e

/-! ## surrogateescape, codecs.c:1413-1503 -/

/-- The write loop of codecs.c:1434-1444. -/
def escWrite : List Nat → HPy (List Nat)
  | [] => .ok []
  | ch :: cs =>
    if ch < 0xdc80 ∨ ch > 0xdcff then .error .reraise
    else do
      let rest ← escWrite cs
      pure ((ch - 0xdc00) :: rest)

/-- `_PyCodec_SurrogateEscapeUnicodeEncodeError`, codecs.c:1415-1448. -/
def surrogateEscapeEncode (e : ExcObj) : HPy Body := do
  let p ← getParams e false
  let out ← escWrite (slice p.obj p.start p.stop)
  pure ⟨p.slen, .bytes out, p.stop⟩

/-- The loop of codecs.c:1466-1473: at most `limit` bytes, stopping at an ASCII one. -/
def escConsume : Nat → List Nat → List Nat
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, b :: bs => if b < 128 then [] else (0xdc00 + b) :: escConsume k bs

/-- `_PyCodec_SurrogateEscapeUnicodeDecodeError`, codecs.c:1451-1487. The characters go to the
stack array `Py_UCS2 ch[4]` (:1463), whose size is `alloc` here. -/
def surrogateEscapeDecode (e : ExcObj) : HPy Body := do
  let p ← getParams e true
  let chs := escConsume (min 4 p.slen) (p.obj.drop p.start)
  if chs.length = 0 then .error .reraise
  else pure ⟨4, .str chs, p.start + chs.length⟩

/-- `PyCodec_SurrogateEscapeErrors`, codecs.c:1490-1503. -/
def surrogateEscapeErrors (H : Hier) (e : ExcObj) : HPy Body :=
  if H.isEnc e.cls then surrogateEscapeEncode e
  else if H.isDec e.cls then surrogateEscapeDecode e
  else wrongType e

/-! ## The registered functions, codecs.c:1506-1561 and :1565-1651 -/

/-- What `codecs.lookup_error(name)(exc)` runs for a builtin name: the `*_errors` wrappers
(codecs.c:1508-1561), registered under these names by `_PyCodec_InitRegistry`
(:1567-1651), each returning `Py_BuildValue("(Nn)", res, pos)`. -/
def callBuiltin (H : Hier) (capi : Except PyExc (Nat → Option Str)) (h : ErrHandler) (e : ExcObj) :
    HPy (Rep × Nat) :=
  match h with
  | .strict => strictErrors H e
  | .ignore => Body.result <$> ignoreErrors H e
  | .replace => Body.result <$> replaceErrors H e
  | .xmlcharrefreplace => Body.result <$> xmlCharRefReplaceErrors H e
  | .backslashreplace => Body.result <$> backslashReplaceErrors H e
  | .namereplace => Body.result <$> nameReplaceErrors H capi e
  | .surrogatepass => Body.result <$> surrogatePassErrors H e
  | .surrogateescape => Body.result <$> surrogateEscapeErrors H e

/-- The bodies that allocate a buffer and fill it: everything but `strict`. -/
def bodyOf (H : Hier) (capi : Except PyExc (Nat → Option Str)) (h : ErrHandler) (e : ExcObj) :
    HPy Body :=
  match h with
  | .strict => .error .reraise
  | .ignore => ignoreErrors H e
  | .replace => replaceErrors H e
  | .xmlcharrefreplace => xmlCharRefReplaceErrors H e
  | .backslashreplace => backslashReplaceErrors H e
  | .namereplace => nameReplaceErrors H capi e
  | .surrogatepass => surrogatePassErrors H e
  | .surrogateescape => surrogateEscapeErrors H e

end PyLean.UnicodeObj.Codecs
