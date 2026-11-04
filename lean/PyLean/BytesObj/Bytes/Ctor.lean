import PyLean.BytesObj.Bytes.Basic
import PyLean.BytesObj.Bytes.Codec

/-!
The `bytes` constructor: `bytes_new_impl`, `PyBytes_FromObject` and its helpers,
Objects/bytesobject.c:2872-3164.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-- One item of the three loops `_PyBytes_FromList`, `_PyBytes_FromTuple`,
`_PyBytes_FromIterator`, bytesobject.c:3000-3009, :3044-3052, :3093-3103. -/
def byteItem (item : Obj) : Py Nat := do
  let value ← asSsizeClamp item
  if value < 0 ∨ value ≥ 256 then throw (.valueError "bytes must be in range(0, 256)")
  return value.toNat

/-- The shared loop body: items in order, stopping at the first error.
`_PyBytes_FromList`, bytesobject.c:2984-3027; `_PyBytes_FromTuple`, :3029-3060;
`_PyBytes_FromIterator`, :3068-3128 (for a generator, without a length hint). -/
def bytesFromItems : List Obj → Py Seq
  | [] => .ok []
  | item :: rest => do
    let v ← byteItem item
    let tail ← bytesFromItems rest
    return v :: tail

/-- `PyBytes_FromObject`, bytesobject.c:3124-3164. -/
def bytesFromObject (x : Obj) : Py Seq :=
  match x with
  | .bytes s => .ok s
  | _ =>
    match x.buffer? with
    | some b => .ok b   -- _PyBytes_FromBuffer, :2958-2982
    | none =>
      let cannot : PyExc := .typeError s!"cannot convert '{x.typeName}' object to bytes"
      match x with
      | .str _ => .error cannot
      | .list items | .tuple items => bytesFromItems items
      | _ => do
        let items ← getIterOr cannot x
        -- `_PyBytes_FromIterator`, bytesobject.c:3068-3074: the hint, then the allocation.
        let size ← lengthHint x 64
        let _ ← writerCreate size false
        let vals ← bytesFromItems items
        iterFinish x
        return vals

/-- `PyNumber_AsSsize_t(x, PyExc_OverflowError)` on an index object of value `v`,
Objects/abstract.c:1468-1510: the message names the object's type. -/
def countOf (x : Obj) (v : Int) : Py Int :=
  if ssizeMin ≤ v ∧ v ≤ ssizeMax then .ok v
  else .error (.overflowError s!"cannot fit '{x.typeName}' into an index-sized integer")

/-- `bytes_new_impl`, bytesobject.c:2872-2956, for `type = bytes`. -/
def bytesNew (x : Option Obj) (encoding errors : Option String) : Py Seq :=
  match x with
  | none =>
    if encoding.isSome then .error (.typeError "encoding without a string argument")
    else if errors.isSome then .error (.typeError "errors without a string argument")
    else bytesFromStringAndSize none 0
  | some x =>
    match encoding with
    | some enc =>
      match x with
      | .str cs =>
        -- PyUnicode_AsEncodedString(x, encoding, errors), :2896; `.modelFuel` is the codec
        -- registry, outside the model
        (unicodeEncode cs (some enc) errors).getD (.error .modelFuel)
      | _ => .error (.typeError "encoding without a string argument")
    | none =>
      if errors.isSome then
        match x with
        | .str _ => .error (.typeError "string argument without an encoding")
        | _ => .error (.typeError "errors without a string argument")
      else
        match x with
        | .dunderRaises e => .error e
        | .dunder r =>
          match r with
          | .bytes s => .ok s
          | _ => .error (bytesDunderWrong x r)
        | .bytes s => .ok s  -- bytes.__bytes__
        | .str _ => .error (.typeError "string argument without an encoding")
        | _ =>
          match x.index? with
          | some (.ok v) =>
            match countOf x v with
            | .error e => .error e
            | .ok size =>
              if size < 0 then .error (.valueError "negative count")
              else bytesFromSize size
          | some (.error e) => if isTypeError e then bytesFromObject x else .error e
          | none => bytesFromObject x

/-- `bytes.__bytes__`, bytesobject.c:1828-1838 (copy for a subclass) and
`bytes_getnewargs`, :2775-2780: both are the contents. -/
def bytesBytes (s : Seq) : Seq := s

/-- `bytes___bytes___impl(self)`, bytesobject.c:1828-1838, with the class of `self` by name: an exact
bytes is returned as it is (:1832-1834), an instance of a subclass is copied into an exact bytes by
`PyBytes_FromStringAndSize` (:1835-1837). `(class, contents)`; identity is out of scope. -/
def bytesDunderBytes (cls : String) (s : Seq) : String × Seq :=
  if cls = "bytes" then (cls, s) else ("bytes", s)

/-- `bytes_new_impl(type, ...)`, bytesobject.c:2872-2956, with `type` by name: the result of the
arms for `bytes`, then, for a subtype, `bytes_subtype_new(type, bytes)` (:2951-2953, :3182-3199),
which copies the contents (and the cached hash) into an instance of `type`. -/
def bytesNewType (type : String) (x : Option Obj) (encoding errors : Option String) :
    Py (String × Seq) :=
  match bytesNew x encoding errors with
  | .error e => .error e
  | .ok b =>
    if type ≠ "bytes" then .ok (type, (bytesSubtypeNew { data := b }).data) else .ok ("bytes", b)

/-- `bytes_fromhex_impl(type, string)`, bytesobject.c:2617-2626: `_PyBytes_FromHex`, then for a
subclass `type(result)` (:2621-2623), which for a subclass that keeps `bytes.__new__` and
`object.__init__` is `bytes_new_impl(type, result)`. A subclass with its own `__new__` or `__init__`
is out of scope (classes by identity). -/
def bytesFromHexType (type : String) (o : Obj) : Py (String × Seq) :=
  match bytesFromHex o with
  | .error e => .error e
  | .ok r => if type ≠ "bytes" then bytesNewType type (some (.bytes r)) none none else .ok ("bytes", r)

/-- `bytes.decode(encoding, errors)`, bytesobject.c:2573-2579: `PyUnicode_FromEncodedObject(self,
encoding, errors)`, which for a bytes is `PyUnicode_Decode`, after its own empty-input shortcut
(Objects/unicodeobject.c:3479-3489).
`.modelFuel` is the codec registry, outside the model. Also `bytearray.decode`,
bytearrayobject.c:2589-2597. -/
def bytesDecode (s : Seq) (encoding errors : Option String) : Py Seq :=
  (unicodeDecode s encoding errors).getD (.error .modelFuel)

end PyLean.BytesObj.Bytes
