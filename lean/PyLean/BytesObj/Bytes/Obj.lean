import PyLean.BytesObj.Bytes.Ctype
import PyLean.BytesObj.Exc
import PyLean.Fractions.Model
import PyLean.Sequences.Common
import PyLean.Binary64.Dtoa

/-!
The object universe of the bytes model, `repr`, and the numeric conversions the
C code calls.

* `Obj` lists every kind of argument the difftest passes to the C code. The
  class-based cases stand for tiny Python classes: `index v` has `__index__`,
  `dunder r` has `__bytes__` returning `r`, `plain` is `object()`, `iter xs` is a
  generator (no buffer, no `__len__`, no `__length_hint__`). The `...Raises` cases
  are the same classes whose method raises.
* C `char` is signed (x86-64 and macOS arm64 builds; the build `python3` runs on).
* `malloc(n)` fails for `n ≥ 2^47`, more than the user address space of an LP64
  system; below that memory is unbounded, and the difftest never asks for a size
  between `2^31` and `2^47`.
* A float is an IEEE binary64 value, `Binary64.F64` (its 64 bits). Its `repr`, its
  `%e %f %g` text, `PyLong_AsDouble` and `PyLong_FromDouble` are the exact models in
  `lean/PyLean/Binary64/` (`float_repr`, `PyOS_double_to_string`, `_Py_dg_dtoa`).
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-- ASCII text as byte values. -/
def asc (s : String) : Seq := s.toList.map Char.toNat

/-- `PyBytesObject_SIZE`, Include/internal/pycore_bytesobject.h: `offsetof(ob_sval) + 1` on LP64. -/
def bytesObjectSize : Int := 33

/-- `malloc` failure, see the module docstring. -/
def mallocFails (n : Int) : Bool := decide (n ≥ 2 ^ 47)

/-- `MemoryError()`. -/
abbrev memoryError : PyExc := Sequences.memoryError

/-- `BufferError(msg)`. -/
def bufferError (msg : String) : PyExc := .named "BufferError" msg

/-- `SystemError(msg)`. -/
def systemError (msg : String) : PyExc := .named "SystemError" msg

/-- `PyErr_BadInternalCall()` at `file:line`: `_PyErr_BadInternalCall`, Python/errors.c:1196-1202,
`"%s:%d: bad argument to internal function"` with `__FILE__` as the build passes it. -/
def badInternalCall (file : String) (line : Nat) : PyExc :=
  systemError s!"{file}:{line}: bad argument to internal function"

/-- `(signed char)b`: what `c = *fmt++` stores in an `int`. -/
def sgnChar (b : Nat) : Int := if b ≥ 128 then (b : Int) - 256 else b

/-! ## Objects -/

inductive Obj where
  | none
  | bool (b : Bool)
  | int (v : Int)
  | float (f : Binary64.F64)
  | str (cs : Seq)
  | bytes (s : Seq)
  | bytearray (s : Seq)
  /-- `memoryview` of contiguous format-`B` data: `s` is the view, `after` what
  follows it in the exporter's memory (`[]` is the end of the allocation). -/
  | memview (s after : Seq)
  | list (xs : List Obj)
  | tuple (xs : List Obj)
  /-- A `dict` with bytes keys. -/
  | dict (kv : List (Seq × Obj))
  | iter (xs : List Obj)
  /-- A generator that yields `xs`, then raises `e`; under PEP 479 a `StopIteration` raised in a
  generator reaches the caller as `RuntimeError('generator raised StopIteration')`. -/
  | iterRaises (xs : List Obj) (e : PyExc)
  /-- A C iterator, `map(f, ...)`, that gives `xs` and then has `f` raise `e`; a `StopIteration` from
  `f` passes through `map_next` and ends the iteration. -/
  | mapRaises (xs : List Obj) (e : PyExc)
  /-- An iterator with a `__length_hint__`: `xs`, then the hint's value or exception. -/
  | iterHint (xs : List Obj) (hint : Py Int)
  /-- A class whose `__iter__` raises `e`. -/
  | iterCallRaises (e : PyExc)
  | index (v : Int)
  /-- A class whose `__index__` raises `e`, or returns a non-int (the `TypeError`). -/
  | indexRaises (e : PyExc)
  | dunder (r : Obj)
  /-- A class whose `__bytes__` raises `e`. -/
  | dunderRaises (e : PyExc)
  | plain
  deriving Inhabited

/-- `Py_TYPE(o)->tp_name`. -/
def Obj.typeName : Obj → String
  | .none => "NoneType"
  | .bool _ => "bool"
  | .int _ => "int"
  | .float _ => "float"
  | .str _ => "str"
  | .bytes _ => "bytes"
  | .bytearray _ => "bytearray"
  | .memview _ _ => "memoryview"
  | .list _ => "list"
  | .tuple _ => "tuple"
  | .dict _ => "dict"
  | .iter _ | .iterRaises _ _ => "generator"
  | .mapRaises _ _ => "map"
  | .iterHint _ _ => "BHint"
  | .iterCallRaises _ => "BIterCall"
  | .index _ => "BIdx"
  | .indexRaises _ => "BIdxRaises"
  | .dunder _ => "BDun"
  | .dunderRaises _ => "BDunRaises"
  | .plain => "object"

/-- `PyObject_CheckBuffer` / the contents of the buffer (`PyBUF_SIMPLE`). -/
def Obj.buffer? : Obj → Option Seq
  | .bytes s | .bytearray s | .memview s _ => some s
  | _ => Option.none

/-- `_PyNumber_Index` on an object with `nb_index` (`_PyIndex_Check`): `none` when it
has none. Failure is part of the result, because the callers treat it differently. -/
def Obj.index? : Obj → Option (Py Int)
  | .bool b => some (.ok (if b then 1 else 0))
  | .int v | .index v => some (.ok v)
  | .indexRaises e => some (.error e)
  | _ => Option.none

/-- `PyErr_ExceptionMatches(PyExc_TypeError)`. -/
def isTypeError (e : PyExc) : Bool := excMatches e "TypeError"

/-- `PyLong_Check`. -/
def Obj.longValue? : Obj → Option Int
  | .bool b => some (if b then 1 else 0)
  | .int v => some v
  | _ => Option.none

/-- `PyNumber_Check`. -/
def Obj.isNumber : Obj → Bool
  | .bool _ | .int _ | .float _ | .index _ | .indexRaises _ => true
  | _ => false

/-- `"%T.__bytes__() must return a bytes, not %T"`, bytesobject.c:585-587 and :2916-2918. -/
def bytesDunderWrong (x r : Obj) : PyExc :=
  .typeError s!"{x.typeName}.__bytes__() must return a bytes, not {r.typeName}"

/-- `"a bytes-like object is required, not '%.100s'"`, `PyObject_GetBuffer`,
Objects/abstract.c:440-444. -/
def notBytesLike (o : Obj) : PyExc :=
  .typeError s!"a bytes-like object is required, not '{o.typeName}'"

/-- `PyObject_GetBuffer(o, PyBUF_SIMPLE)`. -/
def getBuffer (o : Obj) : Py Seq :=
  match o.buffer? with
  | some s => .ok s
  | none => .error (notBytesLike o)

/-- `"'%.200s' object cannot be interpreted as an integer"`, `_PyNumber_Index`. -/
def notInteger (o : Obj) : PyExc :=
  .typeError s!"'{o.typeName}' object cannot be interpreted as an integer"

/-- `PyNumber_AsSsize_t(o, NULL)`: saturates. -/
def asSsizeClamp (o : Obj) : Py Int :=
  match o.index? with
  | some (.ok v) => .ok (clampSsize v)
  | some (.error e) => .error e
  | none => .error (notInteger o)

/-! ## `repr` of bytes, bytesobject.c:1428-1507 -/

/-- `"%s object is too large to make repr"`, bytesobject.c:1504-1505. -/
def reprOverflow (classname : String) : PyExc :=
  .overflowError s!"{classname} object is too large to make repr"

/-- The sizing loop of `_Py_bytes_repr`, bytesobject.c:1445-1461:
`(newsize, squotes, dquotes)`. -/
def reprScan (classname : String) : Seq → Int → Int → Int → Py (Int × Int × Int)
  | [], n, sq, dq => .ok (n, sq, dq)
  | c :: rest, n, sq, dq =>
    let (incr, sq, dq) : Int × Int × Int :=
      if c = 39 then (1, sq + 1, dq)
      else if c = 34 then (1, sq, dq + 1)
      else if c = 92 ∨ c = 9 ∨ c = 10 ∨ c = 13 then (2, sq, dq)
      else if c < 32 ∨ c ≥ 127 then (4, sq, dq)
      else (1, sq, dq)
    if n > ssizeMax - incr then .error (reprOverflow classname)
    else reprScan classname rest (n + incr) sq dq

/-- `Py_hexdigits[d]`, lower case. -/
def hexDigit (d : Nat) : Nat := if d < 10 then 48 + d else 87 + d

/-- The writing loop of `_Py_bytes_repr`, one byte, bytesobject.c:1479-1497. -/
def reprByte (quote c : Nat) : Seq :=
  if c = quote ∨ c = 92 then [92, c]
  else if c = 9 then [92, 116]
  else if c = 10 then [92, 110]
  else if c = 13 then [92, 114]
  else if c < 32 ∨ c ≥ 127 then [92, 120, hexDigit (c / 16), hexDigit (c % 16)]
  else [c]

/-- The body of a bytes literal. -/
def reprBody (quote : Nat) (s : Seq) : Seq := s.flatMap (reprByte quote)

/-- `_Py_bytes_repr(data, length, smartquotes, classname)`, bytesobject.c:1435-1507. -/
def bytesReprAs (classname : String) (s : Seq) (smart : Bool) : Py Seq := do
  let (newsize, squotes, dquotes) ← reprScan classname s 3 0 0
  let quote : Nat := if smart ∧ squotes ≠ 0 ∧ dquotes = 0 then 34 else 39
  if squotes ≠ 0 ∧ quote = 39 then
    if newsize > ssizeMax - squotes then
      throw (reprOverflow classname)
  return [98, quote] ++ reprBody quote s ++ [quote]

/-- `PyBytes_Repr(obj, smartquotes)`, bytesobject.c:1428-1433. -/
def bytesRepr (s : Seq) (smart : Bool) : Py Seq := bytesReprAs "bytes" s smart

/-! ## `repr` of bytearray, bytearrayobject.c:1185-1198 -/

/-- `bytearray_repr_lock_held`, bytearrayobject.c:1184-1198. -/
def bytearrayRepr (className : String) (s : Seq) : Py Seq := do
  let r ← bytesReprAs "bytearray" s true
  return asc className ++ asc "(" ++ r ++ asc ")"

/-! ## `ascii()` -/

/-- `len` lower-case hex digits of `v`. -/
def hexN : Nat → Nat → Seq
  | 0, _ => []
  | n + 1, v => hexN n (v / 16) ++ [hexDigit (v % 16)]

/-- One code point of `ascii(s)`: `unicode_repr` followed by the backslashreplace
of `PyObject_ASCII`; both write the same `\x`, `\u`, `\U` forms. -/
def asciiChar (quote c : Nat) : Seq :=
  if c = quote ∨ c = 92 then [92, c]
  else if c = 9 then [92, 116]
  else if c = 10 then [92, 110]
  else if c = 13 then [92, 114]
  else if c < 32 ∨ c = 127 then [92, 120] ++ hexN 2 c
  else if c < 127 then [c]
  else if c ≤ 0xff then [92, 120] ++ hexN 2 c
  else if c ≤ 0xffff then [92, 117] ++ hexN 4 c
  else [92, 85] ++ hexN 8 c

/-- `ascii(s)` for a `str`: `'` unless the text has `'` and no `"`. -/
def asciiStr (s : Seq) : Seq :=
  let quote : Nat := if s.contains 39 ∧ !s.contains 34 then 34 else 39
  [quote] ++ s.flatMap (asciiChar quote) ++ [quote]

/-- `str(i)`/`repr(i)` for an int, with the digit limit (`Fractions.strInt`). -/
def intRepr (i : Int) : Py Seq := do
  let cs ← Fractions.strInt i
  return cs.map Char.toNat

def sepBy (sep : Seq) : List Seq → Seq
  | [] => []
  | [x] => x
  | x :: rest => x ++ sep ++ sepBy sep rest

/-- `PyObject_ASCII(o)` (an address-bearing default `repr` is out of scope: the
difftest does not format one with `%a`). `fuel` bounds the nesting. -/
def asciiObj : Nat → Obj → Py Seq
  | 0, _ => .error .modelFuel
  | _ + 1, .none => .ok (asc "None")
  | _ + 1, .bool b => .ok (asc (if b then "True" else "False"))
  | _ + 1, .int v => intRepr v
  | _ + 1, .float f =>
    match Binary64.float_repr f with
    | some r => .ok r
    | none => .error memoryError
  | _ + 1, .str cs => .ok (asciiStr cs)
  | _ + 1, .bytes s => bytesRepr s true
  | _ + 1, .bytearray s => bytearrayRepr "bytearray" s
  | fuel + 1, .list xs => do
    let parts ← xs.attach.mapM (fun ⟨x, _⟩ => asciiObj fuel x)
    return asc "[" ++ sepBy (asc ", ") parts ++ asc "]"
  | fuel + 1, .tuple xs => do
    let parts ← xs.attach.mapM (fun ⟨x, _⟩ => asciiObj fuel x)
    match parts with
    | [p] => return asc "(" ++ p ++ asc ",)"
    | _ => return asc "(" ++ sepBy (asc ", ") parts ++ asc ")"
  | fuel + 1, .dict kv => do
    let parts ← kv.attach.mapM (fun ⟨(k, v), _⟩ => do
      let ks ← bytesRepr k true
      let vs ← asciiObj fuel v
      return ks ++ asc ": " ++ vs)
    return asc "{" ++ sepBy (asc ", ") parts ++ asc "}"
  | _ + 1, o => .ok (asc s!"<{o.typeName} object>")

/-! ## Conversions to double -/

/-- `PyFloat_AsDouble(o)`, Objects/floatobject.c:250-303: a float is its value; an int or
an object with `__index__` goes through `PyNumber_Index` and `PyLong_AsDouble`
(`Binary64.PyLong_AsDouble`: round half-even, `OverflowError` at `2^1024`). -/
def asDouble (o : Obj) : Py Binary64.F64 :=
  match o with
  | .float f => .ok f
  | .bool _ | .int _ | .index _ | .indexRaises _ =>
    match o.index? with
    | some (.ok v) => Binary64.PyLong_AsDouble v
    | some (.error e) => .error e
    | none => .error (.typeError "unreachable")
  | _ => .error (.typeError s!"must be real number, not {o.typeName}")

/-- Decimal digits of `n`. -/
def digitsOf (n : Nat) : Seq := (Nat.toDigits 10 n).map Char.toNat

/-! ## `int` to text -/

/-- `n` in `base` (8 or 16), lower case. -/
def digitsBase (base : Nat) (n : Nat) : Seq :=
  (Nat.toDigits base n).map Char.toNat

/-- `PyNumber_ToBase(val, base)`, Objects/abstract.c:1661-1675 and
`_PyLong_Format`: the base prefix, after the sign; the digit limit applies to
base 10 only. -/
def numberToBase (val : Int) (base : Nat) : Py Seq :=
  if base = 10 then intRepr val
  else
    let sign : Seq := if val < 0 then [45] else []
    let pre : Seq := if base = 8 then asc "0o" else asc "0x"
    .ok (sign ++ pre ++ digitsBase base val.natAbs)

/-- `PyNumber_Long(o)`, for a number. -/
def numberLong (o : Obj) : Py Int :=
  match o with
  | .float f => Binary64.PyLong_FromDouble f
  | _ =>
    match o.index? with
    | some (.ok v) => .ok v
    | some (.error e) => .error e
    | none => .error (.typeError "int() argument must be a string, a bytes-like object or a real number")

/-! ## Encoders and decoders used by `bytes()`, `decode` -/

/-- The text of a codec error (position only; the difftest compares the class). -/
def codecErrMsg (name : String) (i : Nat) : String := s!"~{name} {i}"

/-- `str.encode` for the two encodings whose result is a plain byte map:
`latin-1` and `ascii`, strict error handling. -/
def encodeStr (cs : Seq) (encoding : String) : Py Seq :=
  let name := encoding
  let limit := if name = "latin-1" then 256 else 128
  match cs.findIdx? (· ≥ limit) with
  | none => .ok cs
  | some i => .error (.named "UnicodeEncodeError" (codecErrMsg name i))

/-- `bytes.decode` for `latin-1` and `ascii`, strict error handling. -/
def decodeBytes (s : Seq) (encoding : String) : Py Seq :=
  let name := encoding
  let limit := if name = "latin-1" then 256 else 128
  match s.findIdx? (· ≥ limit) with
  | none => .ok s
  | some i => .error (.named "UnicodeDecodeError" (codecErrMsg name i))

end PyLean.BytesObj.Bytes
