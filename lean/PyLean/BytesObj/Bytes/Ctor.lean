import PyLean.BytesObj.Bytes.Basic

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
`_PyBytes_FromIterator`, :3062-3122 (for a generator, without a length hint). -/
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
      | .str cs => encodeStr cs enc
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

/-- `bytes.decode(encoding, errors)`, bytesobject.c:2573-2579, and
`bytearray.decode`, bytearrayobject.c:2589-2597. -/
def bytesDecode (s : Seq) (encoding : String) : Py Seq := decodeBytes s encoding

end PyLean.BytesObj.Bytes
