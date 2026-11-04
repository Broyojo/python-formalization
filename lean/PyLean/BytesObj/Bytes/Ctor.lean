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

/-- What an item's `__index__` does to the list that holds it, before it returns. -/
inductive ListAct where
  | keep
  | append (v : Int)
  | clear
  | popLast

/-- An item of a list given to `bytes()`: a plain object, or one whose `__index__` first acts on the
list and then returns `r` (or raises, or returns a non-int: the `TypeError` in `r`). -/
inductive LItem where
  | plain (o : Obj)
  | mut (r : Py Int) (act : ListAct)

instance : Inhabited LItem := ⟨.plain .none⟩

/-- The list after `act`; an appended value is a plain int. -/
def ListAct.apply : ListAct → List LItem → List LItem
  | .keep, xs => xs
  | .append v, xs => xs ++ [.plain (.int v)]
  | .clear, _ => []
  | .popLast, xs => xs.dropLast

/-- `PyNumber_AsSsize_t(item, NULL)` on an item of the list `xs` (bytesobject.c:3000): the clipped
value, and the list as `__index__` left it. -/
def lItemIndex (item : LItem) (xs : List LItem) : Py Int × List LItem :=
  match item with
  | .plain o => (asSsizeClamp o, xs)
  | .mut r act => (r.map clampSsize, act.apply xs)

/-- The loop of `_PyBytes_FromList`, bytesobject.c:2995-3021: `i < PyList_GET_SIZE(x)` and
`_PyList_GetItemRef(x, i)` read the list as the previous `__index__` left it (:2995-2996); the range
check (:3005-3009); past `size`, `_PyBytesWriter_ResizeAndUpdatePointer(writer, size + 1, str)` and
`_PyBytesWriter_ResizeToAllocated` (:3011-3019). The model is the GIL build, where
`_PyList_GetItemRef` of an index below the size cannot fail; under `Py_GIL_DISABLED` it can return
NULL without an exception set (listobject.c:375-388), a lead that is not verified here. -/
def fromListLoop : Nat → List LItem → Nat → Writer → Int → Seq → Py (Seq × Writer)
  | 0, _, _, _, _, _ => .error .modelFuel
  | fuel + 1, xs, i, w, size, out =>
    if i < xs.length then
      match lItemIndex (xs.getD i default) xs with
      | (.error e, _) => .error e
      | (.ok value, xs) =>
        if value < 0 ∨ value ≥ 256 then .error (.valueError "bytes must be in range(0, 256)")
        else if (i : Int) ≥ size then
          match writerResize w (size + 1) with
          | .error e => .error e
          | .ok w =>
            let w := writerResizeToAllocated w
            fromListLoop fuel xs (i + 1) w w.size (out ++ [value.toNat])
        else fromListLoop fuel xs (i + 1) w size (out ++ [value.toNat])
    else .ok (out, w)

/-- `_PyBytes_FromList(x)`, bytesobject.c:2984-3026: `PyBytesWriter_Create(size)`,
`_PyBytesWriter_ResizeToAllocated` (:2987-2992), the loop, `PyBytesWriter_FinishWithPointer`. Every
`__index__` appends at most one plain item, so `2 * len + 1` rounds bound the loop. -/
def bytesFromList (xs : List LItem) : Py Seq := do
  let w ← writerCreate xs.length false
  let w := writerResizeToAllocated w
  let (out, w) ← fromListLoop (2 * xs.length + 1) xs 0 w w.size []
  writerFinish w out

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
      | .list items => bytesFromList (items.map .plain)
      | .tuple items => bytesFromItems items
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

/-- `bytes_fromhex_impl(type, string)`, bytesobject.c:2617-2626, for any result type `α`:
`_PyBytes_FromHex`, then, when `type` is not `bytes`, `PyObject_CallOneArg(type, result)`
(:2621-2623). `call` is that call: `none` for `bytes` itself (the result is `inj r`); `some f` for a
subclass, where `f r` runs the subclass's `__new__` and `__init__` and may raise or return any
object. It is called only after the parse succeeded. -/
def bytesFromHexT {α : Type} (inj : Seq → α) (call : Option (Seq → Py α)) (o : Obj) : Py α :=
  match bytesFromHex o with
  | .error e => .error e
  | .ok r =>
    match call with
    | none => .ok (inj r)
    | some f => f r

/-- `type(r)` for a subclass `T` that keeps `bytes.__new__` and `object.__init__`:
`bytes_new_impl(T, r)`, an instance of `T` with the contents of `r`. -/
def plainSubCall (T : String) (r : Seq) : Py (String × Seq) := bytesNewType T (some (.bytes r)) none none

/-- `T.fromhex(s)` for `bytes` (`T = "bytes"`) or a subclass `T` that keeps `bytes.__new__` and
`object.__init__`: `(class, contents)`. -/
def bytesFromHexType (type : String) (o : Obj) : Py (String × Seq) :=
  bytesFromHexT (fun r => ("bytes", r)) (if type ≠ "bytes" then some (plainSubCall type) else none) o

/-- `bytes_getnewargs(op)`, bytesobject.c:2775-2780: `Py_BuildValue("(y#)", ob_sval, size)`, a new
1-tuple holding a new exact bytes with the contents, whatever the class of `self`. -/
def bytesGetnewargs (s : Seq) : Obj := .tuple [.bytes s]

/-- `bytes.decode(encoding, errors)`, bytesobject.c:2573-2579: `PyUnicode_FromEncodedObject(self,
encoding, errors)`, which for a bytes is `PyUnicode_Decode`, after its own empty-input shortcut
(Objects/unicodeobject.c:3479-3489).
`.modelFuel` is the codec registry, outside the model. Also `bytearray.decode`,
bytearrayobject.c:2589-2597. -/
def bytesDecode (s : Seq) (encoding errors : Option String) : Py Seq :=
  (unicodeDecode s encoding errors).getD (.error .modelFuel)

end PyLean.BytesObj.Bytes
