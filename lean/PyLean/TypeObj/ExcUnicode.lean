import PyLean.TypeObj.ExcCore

/-!
The Unicode errors: `Objects/exceptions.c:3065-4043`. Attribute checks, the clipping of
`start` and `end`, `_PyUnicodeError_GetParams`, `__init__`, `__str__`, and the C API.

`PyUnicode_GET_LENGTH` counts code points, which is `String.toList.length`. A Lean `String`
cannot hold a lone surrogate, so the difftest keeps to valid text.
-/

namespace PyLean.TypeObj

/-- The bytes of a `bytes` object (`PyBytes_Check`). -/
def bytesOf (w : World) (v : Val) : Option (List Nat) :=
  if isSubtype w (typeOf w v) B.bytes then
    match payloadOf w v with
    | some (.bytes b) => some b
    | _ => none
  else none

/-- `PyObject_GetBuffer(object, &view, PyBUF_SIMPLE)` for the buffer types of this model. -/
def bufferOf (w : World) (v : Val) : M (List Nat) :=
  match payloadOf w v with
  | some (.bytes b) => pure b
  | _ => typeErr s!"a bytes-like object is required, not '{trunc 200 (typeName w v)}'"

/-- `check_unicode_error_attribute`, `Objects/exceptions.c:3065`. -/
def checkUnicodeErrorAttribute (attr : Option Val) (name : String) (asBytes : Bool) : M Unit := do
  let w ← getW
  match attr with
  | none => typeErr s!"UnicodeError '{name}' attribute is not set"
  | some a =>
    let ok := if asBytes then (bytesOf w a).isSome else (strOf w a).isSome
    unless ok do
      typeErr s!"UnicodeError '{name}' attribute must be a {if asBytes then "bytes" else "string"}"

/-- `as_unicode_error_attribute`, `Objects/exceptions.c:3094`. -/
def asUnicodeErrorAttribute (attr : Option Val) (name : String) (asBytes : Bool) : M Val := do
  checkUnicodeErrorAttribute attr name asBytes
  match attr with
  | some a => pure a
  | none => gap%

/-- `check_unicode_error_type`, `Objects/exceptions.c:3128`. -/
def checkUnicodeErrorType (self : Val) (expectType : String) : M Unit := do
  let w ← getW
  unless isSubtype w (typeOf w self) B.UnicodeError do
    typeErr s!"expecting a {expectType} object, got {typeFQN w (typeOf w self)}"

/-- `unicode_error_get_encoding_impl`, `Objects/exceptions.c:3150`. -/
def unicodeErrorGetEncodingImpl (self : Val) : M Val := do
  let w ← getW
  asUnicodeErrorAttribute (memGet (excDataOf w self) "encoding") "encoding" false

/-- `unicode_error_get_object_impl`, `Objects/exceptions.c:3163`. -/
def unicodeErrorGetObjectImpl (self : Val) (asBytes : Bool) : M Val := do
  let w ← getW
  asUnicodeErrorAttribute (memGet (excDataOf w self) "object") "object" asBytes

/-- `unicode_error_get_reason_impl`, `Objects/exceptions.c:3175`. -/
def unicodeErrorGetReasonImpl (self : Val) : M Val := do
  let w ← getW
  asUnicodeErrorAttribute (memGet (excDataOf w self) "reason") "reason" false

/-- `unicode_error_set_reason_impl`, `Objects/exceptions.c:3189`. -/
def unicodeErrorSetReasonImpl (self : Val) (reason : String) : M Unit :=
  excUpdate self (memSet "reason" (some (.str reason)))

/-- `unicode_error_set_start_impl`, `Objects/exceptions.c:3208`. -/
def unicodeErrorSetStartImpl (self : Val) (start : Int) : M Unit :=
  excUpdate self (memSet "start" (some (.int start)))

/-- `unicode_error_set_end_impl`, `Objects/exceptions.c:3223`. -/
def unicodeErrorSetEndImpl (self : Val) (e : Int) : M Unit :=
  excUpdate self (memSet "end" (some (.int e)))

/-- `unicode_error_adjust_start`, `Objects/exceptions.c:3243`. -/
def unicodeErrorAdjustStart (start objlen : Int) : Int :=
  let s := if start < 0 then 0 else start
  if s >= objlen then (if objlen == 0 then 0 else objlen - 1) else s

/-- `unicode_error_adjust_end`, `Objects/exceptions.c:3284`. -/
def unicodeErrorAdjustEnd (e objlen : Int) : Int :=
  let e' := if e < 1 then 1 else e
  if e' > objlen then objlen else e'

/-- `unicode_error_adjust_len`, `Objects/exceptions.c:3330`. -/
def unicodeErrorAdjustLen (start e : Int) : Int :=
  let r := e - start
  if r < 0 then 0 else r

/-- `assert_adjusted_unicode_error_start`, `Objects/exceptions.c:3259`. -/
def adjustedStartOk (start objlen : Int) : Prop := 0 ≤ start ∧ start ≤ max 0 (objlen - 1)

/-- `assert_adjusted_unicode_error_end`, `Objects/exceptions.c:3304`. -/
def adjustedEndOk (e objlen : Int) : Prop := min 1 objlen ≤ e ∧ e ≤ max (min 1 objlen) objlen

/-- `assert_adjusted_unicode_error_len`, `Objects/exceptions.c:3343`. -/
def adjustedLenOk (r objlen : Int) : Prop := 0 ≤ r ∧ r ≤ objlen

/-- A `Py_ssize_t` member; zero until set. -/
def ssizeMember (d : ExcData) (n : Name) : Int :=
  match memGet d n with
  | some (.int i) => i
  | _ => 0

/-- The length of the `object` attribute as `_PyUnicodeError_GetParams` reads it. -/
def unicodeObjectLen (w : World) (v : Val) (asBytes : Bool) : Int :=
  if asBytes then ((bytesOf w v).getD []).length
  else ((strOf w v).getD "").toList.length

/-- The output parameters of `_PyUnicodeError_GetParams`. -/
structure UParams where
  obj : Val
  objlen : Int
  start : Int
  «end» : Int
  slen : Int

/-- `_PyUnicodeError_GetParams`, `Objects/exceptions.c:3383`. -/
def unicodeErrorGetParams (self : Val) (asBytes : Bool) : M UParams := do
  let w ← getW
  let d := excDataOf w self
  let r ← asUnicodeErrorAttribute (memGet d "object") "object" asBytes
  let w ← getW
  let n := unicodeObjectLen w r asBytes
  let s := unicodeErrorAdjustStart (ssizeMember d "start") n
  let e := unicodeErrorAdjustEnd (ssizeMember d "end") n
  pure { obj := r, objlen := n, start := s, «end» := e, slen := unicodeErrorAdjustLen s e }

/-! ## `__init__` -/

/-- `UnicodeEncodeError_init`, `Objects/exceptions.c:3716`. -/
def unicodeEncodeErrorInit (rt : Rt) (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  baseExceptionInit self args kw
  argCount none 5 5 args.length
  let get (i : Nat) : Val := args.getD i .none
  argU none 1 (get 0)
  argU none 2 (get 1)
  let s ← argN rt (get 2)
  let e ← argN rt (get 3)
  argU none 5 (get 4)
  excUpdate self (memSet "encoding" (some (get 0)))
  excUpdate self (memSet "object" (some (get 1)))
  excUpdate self (memSet "start" (some (.int s)))
  excUpdate self (memSet "end" (some (.int e)))
  excUpdate self (memSet "reason" (some (get 4)))

/-- `UnicodeDecodeError_init`, `Objects/exceptions.c:3823`. -/
def unicodeDecodeErrorInit (rt : Rt) (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  baseExceptionInit self args kw
  argCount none 5 5 args.length
  let get (i : Nat) : Val := args.getD i .none
  argU none 1 (get 0)
  let s ← argN rt (get 2)
  let e ← argN rt (get 3)
  argU none 5 (get 4)
  let w ← getW
  let obj ← if (bytesOf w (get 1)).isSome then pure (get 1)
    else
      let b ← bufferOf w (get 1)
      alloc B.bytes (.bytes b)
  excUpdate self (memSet "encoding" (some (get 0)))
  excUpdate self (memSet "object" (some obj))
  excUpdate self (memSet "start" (some (.int s)))
  excUpdate self (memSet "end" (some (.int e)))
  excUpdate self (memSet "reason" (some (get 4)))

/-- `UnicodeTranslateError_init`, `Objects/exceptions.c:3945`. -/
def unicodeTranslateErrorInit (rt : Rt) (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  baseExceptionInit self args kw
  argCount none 4 4 args.length
  let get (i : Nat) : Val := args.getD i .none
  argU none 1 (get 0)
  let s ← argN rt (get 1)
  let e ← argN rt (get 2)
  argU none 4 (get 3)
  excUpdate self (memSet "object" (some (get 0)))
  excUpdate self (memSet "start" (some (.int s)))
  excUpdate self (memSet "end" (some (.int e)))
  excUpdate self (memSet "reason" (some (get 3)))

/-! ## `__str__` -/

/-- `%0Nx`: lowercase hex, padded to `width`. -/
def hexPad (width v : Nat) : String :=
  let ds := Nat.toDigits 16 v
  String.ofList (List.replicate (width - ds.length) '0' ++ ds)

/-- `end - 1` on `Py_ssize_t`: `Py_ssize_t` arithmetic on `Int`, wrapped as the
two's-complement machine does. Reaching the wrap is undefined behaviour in C. -/
def ssizeWrap (i : Int) : Int :=
  if i < PyLean.ssizeMin then i + 2 ^ 64 else i

/-- `(start >= 0 && start < len) && (end >= 0 && end <= len) && end == start + 1`: the test
that guards every `__str__` read of the object, `Objects/exceptions.c:3770`, `:3893`, `:3992`. -/
def unicodeStrSingle (start e len : Int) : Bool :=
  decide (0 ≤ start) && decide (start < len) && decide (0 ≤ e) && decide (e ≤ len) &&
    decide (e = start + 1)

/-- The bad character at `start`: `PyUnicode_ReadChar`. -/
def charAt (s : String) (i : Int) : Nat := ((s.toList.getD i.toNat 'x').toNat)

/-- `'\\x%02x'` and friends: the escape of one character in the error message. -/
def badCharEscape (c : Nat) : String :=
  if c ≤ 0xff then "\\x" ++ hexPad 2 c
  else if c ≤ 0xffff then "\\u" ++ hexPad 4 c
  else "\\U" ++ hexPad 8 c

/-- `UnicodeEncodeError_str`, `Objects/exceptions.c:3741`. -/
def unicodeEncodeErrorStr (rt : Rt) (self : Val) : M Val := do
  let w ← getW
  let d := excDataOf w self
  match memGet d "object" with
  | none => pure (.str "")
  | some _ =>
    let reason ← strOrNull rt (memGet d "reason")
    let encoding ← strOrNull rt (memGet d "encoding")
    let w ← getW
    let d := excDataOf w self
    checkUnicodeErrorAttribute (memGet d "object") "object" false
    let obj := (strOf w (orNoneU (memGet d "object"))).getD ""
    let len : Int := obj.toList.length
    let (start, e) := (ssizeMember d "start", ssizeMember d "end")
    if unicodeStrSingle start e len then
      let esc := badCharEscape (charAt obj start)
      pure (.str s!"'{encoding}' codec can't encode character '{esc}' in position {start}: {reason}")
    else
      pure (.str s!"'{encoding}' codec can't encode characters in position {start}-{ssizeWrap (e - 1)}: {reason}")
where
  orNoneU (v : Option Val) : Val := v.getD .none

/-- `UnicodeDecodeError_str`, `Objects/exceptions.c:3864`. -/
def unicodeDecodeErrorStr (rt : Rt) (self : Val) : M Val := do
  let w ← getW
  let d := excDataOf w self
  match memGet d "object" with
  | none => pure (.str "")
  | some _ =>
    let reason ← strOrNull rt (memGet d "reason")
    let encoding ← strOrNull rt (memGet d "encoding")
    let w ← getW
    let d := excDataOf w self
    checkUnicodeErrorAttribute (memGet d "object") "object" true
    let obj := (bytesOf w ((memGet d "object").getD .none)).getD []
    let len : Int := obj.length
    let (start, e) := (ssizeMember d "start", ssizeMember d "end")
    if unicodeStrSingle start e len then
      let b := obj.getD start.toNat 0
      pure (.str s!"'{encoding}' codec can't decode byte 0x{hexPad 2 b} in position {start}: {reason}")
    else
      pure (.str s!"'{encoding}' codec can't decode bytes in position {start}-{ssizeWrap (e - 1)}: {reason}")

/-- `UnicodeTranslateError_str`, `Objects/exceptions.c:3968`. -/
def unicodeTranslateErrorStr (rt : Rt) (self : Val) : M Val := do
  let w ← getW
  let d := excDataOf w self
  match memGet d "object" with
  | none => pure (.str "")
  | some _ =>
    let reason ← strOrNull rt (memGet d "reason")
    let w ← getW
    let d := excDataOf w self
    checkUnicodeErrorAttribute (memGet d "object") "object" false
    let obj := (strOf w ((memGet d "object").getD .none)).getD ""
    let len : Int := obj.toList.length
    let (start, e) := (ssizeMember d "start", ssizeMember d "end")
    if unicodeStrSingle start e len then
      let esc := badCharEscape (charAt obj start)
      pure (.str s!"can't translate character '{esc}' in position {start}: {reason}")
    else
      pure (.str s!"can't translate characters in position {start}-{ssizeWrap (e - 1)}: {reason}")

/-! ## The C API, `Objects/exceptions.c:3437-3664`

Each public function is `check_unicode_error_type` followed by one shared helper. They differ
only in the name for the error message and in `as_bytes`, so `UKind` carries both. -/

/-- Which of `PyUnicodeEncodeError_*`, `PyUnicodeDecodeError_*`, `PyUnicodeTranslateError_*`. -/
inductive UKind where
  | encode | decode | translate
  deriving DecidableEq

/-- `Py_UNICODE_ENCODE_ERROR_NAME` and friends, `Objects/exceptions.c:3108`. -/
def UKind.name : UKind → String
  | .encode => "UnicodeEncodeError"
  | .decode => "UnicodeDecodeError"
  | .translate => "UnicodeTranslateError"

/-- The `as_bytes` each family passes. -/
def UKind.asBytes : UKind → Bool
  | .decode => true
  | _ => false

/-- `PyUnicode{Encode,Decode}Error_GetEncoding`, `Objects/exceptions.c:3438`, `:3446`. -/
def pyUnicodeErrorGetEncoding (k : UKind) (self : Val) : M Val := do
  checkUnicodeErrorType self k.name
  unicodeErrorGetEncodingImpl self

/-- `PyUnicode*Error_GetObject`, `Objects/exceptions.c:3456-3476`. -/
def pyUnicodeErrorGetObject (k : UKind) (self : Val) : M Val := do
  checkUnicodeErrorType self k.name
  unicodeErrorGetObjectImpl self k.asBytes

/-- `unicode_error_get_start_impl` and `PyUnicode*Error_GetStart`,
`Objects/exceptions.c:3488-3518`. -/
def pyUnicodeErrorGetStart (k : UKind) (self : Val) : M Int := do
  checkUnicodeErrorType self k.name
  UParams.start <$> unicodeErrorGetParams self k.asBytes

/-- `PyUnicode*Error_SetStart`, `Objects/exceptions.c:3524-3544`. -/
def pyUnicodeErrorSetStart (k : UKind) (self : Val) (start : Int) : M Unit := do
  checkUnicodeErrorType self k.name
  unicodeErrorSetStartImpl self start

/-- `unicode_error_get_end_impl` and `PyUnicode*Error_GetEnd`,
`Objects/exceptions.c:3556-3586`. -/
def pyUnicodeErrorGetEnd (k : UKind) (self : Val) : M Int := do
  checkUnicodeErrorType self k.name
  UParams.«end» <$> unicodeErrorGetParams self k.asBytes

/-- `PyUnicode*Error_SetEnd`, `Objects/exceptions.c:3592-3612`. -/
def pyUnicodeErrorSetEnd (k : UKind) (self : Val) (e : Int) : M Unit := do
  checkUnicodeErrorType self k.name
  unicodeErrorSetEndImpl self e

/-- `PyUnicode*Error_GetReason`, `Objects/exceptions.c:3618-3638`. -/
def pyUnicodeErrorGetReason (k : UKind) (self : Val) : M Val := do
  checkUnicodeErrorType self k.name
  unicodeErrorGetReasonImpl self

/-- `PyUnicode*Error_SetReason`, `Objects/exceptions.c:3644-3664`. -/
def pyUnicodeErrorSetReason (k : UKind) (self : Val) (reason : String) : M Unit := do
  checkUnicodeErrorType self k.name
  unicodeErrorSetReasonImpl self reason

/-- `PyUnicodeDecodeError_Create`, `Objects/exceptions.c:3931`. -/
def pyUnicodeDecodeErrorCreate (rt : Rt) (encoding : String) (object : List Nat)
    (start e : Int) (reason : String) : M Val := do
  let o ← alloc B.bytes (.bytes object)
  rt.call (.obj B.UnicodeDecodeError) [.str encoding, o, .int start, .int e, .str reason] []

/-- `_PyUnicodeTranslateError_Create`, `Objects/exceptions.c:4037`. -/
def pyUnicodeTranslateErrorCreate (rt : Rt) (object : Val) (start e : Int) (reason : String) :
    M Val :=
  rt.call (.obj B.UnicodeTranslateError) [object, .int start, .int e, .str reason] []

end PyLean.TypeObj
