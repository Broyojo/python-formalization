import PyLean.BytesObj.Bytes.Ctype
import PyLean.Fractions.Model
import PyLean.Sequences.Common

/-!
The object universe of the bytes model, `repr`, and the numeric conversions the
C code calls.

* `Obj` lists every kind of argument the difftest passes to the C code. The
  class-based cases stand for tiny Python classes: `index v` has `__index__`,
  `dunder r` has `__bytes__` returning `r`, `plain` is `object()`, `iter xs` is a
  generator (no buffer, no `__len__`, no `__length_hint__`).
* C `char` is signed (x86-64 and macOS arm64 builds; the build `python3` runs on).
* `malloc(n)` fails for `n ≥ 2^47`, more than the user address space of an LP64
  system; below that memory is unbounded, and the difftest never asks for a size
  between `2^31` and `2^47`.
* A float is its exact value (sign and fraction): `PyOS_double_to_string` for the
  `%e %f %g` modes is correct rounding (half-even on the exact value) of that
  value, so it is a function of the fraction. `repr` of a float (shortest
  round-trip) is out of scope and is carried by the value.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-- ASCII text as byte values. -/
def asc (s : String) : Seq := s.toList.map Char.toNat

/-- `PyBytesObject_SIZE`, bytesobject.c:34: `offsetof(ob_sval) + 1` on LP64. -/
def bytesObjectSize : Int := 33

/-- `malloc` failure, see the module docstring. -/
def mallocFails (n : Int) : Bool := decide (n ≥ 2 ^ 47)

/-- `MemoryError()`. -/
abbrev memoryError : PyExc := Sequences.memoryError

/-- `BufferError(msg)`. -/
def bufferError (msg : String) : PyExc := .named "BufferError" msg

/-- `SystemError(msg)`. -/
def systemError (msg : String) : PyExc := .named "SystemError" msg

/-- `PyErr_BadInternalCall()`. -/
def badInternalCall (f : String) : PyExc := systemError s!"{f}: bad internal call"

/-- `(signed char)b`: what `c = *fmt++` stores in an `int`. -/
def sgnChar (b : Nat) : Int := if b ≥ 128 then (b : Int) - 256 else b

/-! ## Floats -/

/-- An IEEE double by value. `kind`: 0 finite, 1 infinity, 2 NaN. -/
structure Flt where
  neg : Bool
  kind : Nat
  num : Nat
  den : Nat
  repr : String
  deriving Repr, Inhabited, DecidableEq

/-! ## Objects -/

inductive Obj where
  | none
  | bool (b : Bool)
  | int (v : Int)
  | float (f : Flt)
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
  | index (v : Int)
  | dunder (r : Obj)
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
  | .iter _ => "generator"
  | .index _ => "Idx"
  | .dunder _ => "Dun"
  | .plain => "object"

/-- `PyObject_CheckBuffer` / the contents of the buffer (`PyBUF_SIMPLE`). -/
def Obj.buffer? : Obj → Option Seq
  | .bytes s | .bytearray s | .memview s _ => some s
  | _ => Option.none

/-- The value of an object with `nb_index` (`_PyIndex_Check`). -/
def Obj.index? : Obj → Option Int
  | .bool b => some (if b then 1 else 0)
  | .int v | .index v => some v
  | _ => Option.none

/-- `PyLong_Check`. -/
def Obj.longValue? : Obj → Option Int
  | .bool b => some (if b then 1 else 0)
  | .int v => some v
  | _ => Option.none

/-- `PyNumber_Check`. -/
def Obj.isNumber : Obj → Bool
  | .bool _ | .int _ | .float _ | .index _ => true
  | _ => false

/-- `"a bytes-like object is required, not '%.100s'"`, `PyObject_GetBuffer`,
Objects/abstract.c:430-434. -/
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
  | some v => .ok (clampSsize v)
  | none => .error (notInteger o)

/-! ## `repr` of bytes, bytesobject.c:1344-1416 -/

/-- The sizing loop of `PyBytes_Repr`, bytesobject.c:1358-1372:
`(newsize, squotes, dquotes)`. -/
def reprScan : Seq → Int → Int → Int → Py (Int × Int × Int)
  | [], n, sq, dq => .ok (n, sq, dq)
  | c :: rest, n, sq, dq =>
    let (incr, sq, dq) : Int × Int × Int :=
      if c = 39 then (1, sq + 1, dq)
      else if c = 34 then (1, sq, dq + 1)
      else if c = 92 ∨ c = 9 ∨ c = 10 ∨ c = 13 then (2, sq, dq)
      else if c < 32 ∨ c ≥ 127 then (4, sq, dq)
      else (1, sq, dq)
    if n > ssizeMax - incr then .error (.overflowError "bytes object is too large to make repr")
    else reprScan rest (n + incr) sq dq

/-- `Py_hexdigits[d]`, lower case. -/
def hexDigit (d : Nat) : Nat := if d < 10 then 48 + d else 87 + d

/-- The writing loop of `PyBytes_Repr`, one byte, bytesobject.c:1390-1406. -/
def reprByte (quote c : Nat) : Seq :=
  if c = quote ∨ c = 92 then [92, c]
  else if c = 9 then [92, 116]
  else if c = 10 then [92, 110]
  else if c = 13 then [92, 114]
  else if c < 32 ∨ c ≥ 127 then [92, 120, hexDigit (c / 16), hexDigit (c % 16)]
  else [c]

/-- The body of a bytes literal. -/
def reprBody (quote : Nat) (s : Seq) : Seq := s.flatMap (reprByte quote)

/-- `PyBytes_Repr(obj, smartquotes)`, bytesobject.c:1344-1416. -/
def bytesRepr (s : Seq) (smart : Bool) : Py Seq := do
  let (newsize, squotes, dquotes) ← reprScan s 3 0 0
  let quote : Nat := if smart ∧ squotes ≠ 0 ∧ dquotes = 0 then 34 else 39
  if squotes ≠ 0 ∧ quote = 39 then
    if newsize > ssizeMax - squotes then
      throw (.overflowError "bytes object is too large to make repr")
  return [98, quote] ++ reprBody quote s ++ [quote]

/-! ## `repr` of bytearray, bytearrayobject.c:1092-1178 -/

/-- The quote choice, bytearrayobject.c:1126-1135. -/
def baQuote : Seq → Nat → Nat
  | [], q => q
  | c :: rest, q => if c = 34 then 39 else if c = 39 then baQuote rest 34 else baQuote rest q

/-- One byte of `bytearray_repr_lock_held`, bytearrayobject.c:1149-1167. Unlike
`PyBytes_Repr`, `'` is escaped whatever the quote is, and `c == 0` has its own
branch with the same result as the general `\xHH` one. -/
def baReprByte (c : Nat) : Seq :=
  if c = 39 ∨ c = 92 then [92, c]
  else if c = 9 then [92, 116]
  else if c = 10 then [92, 110]
  else if c = 13 then [92, 114]
  else if c = 0 then [92, 120, 48, 48]
  else if c < 32 ∨ c ≥ 127 then [92, 120, hexDigit (c / 16), hexDigit (c % 16)]
  else [c]

/-- `bytearray_repr_lock_held`, bytearrayobject.c:1092-1178. -/
def bytearrayRepr (className : String) (s : Seq) : Py Seq :=
  let newsize : Int := className.length
  if (s.length : Int) > Int.tdiv (ssizeMax - 6 - newsize) 4 then
    .error (.overflowError "bytearray object is too large to make repr")
  else
    let quote := baQuote s 39
    .ok (asc className ++ asc "(b" ++ [quote] ++ s.flatMap baReprByte ++ [quote] ++ asc ")")

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
  | _ + 1, .float f => .ok (asc f.repr)
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

/-- Half-even rounding of `n / d`. -/
def roundDiv (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if 2 * r > d then q + 1
  else if 2 * r = d then (if q % 2 = 1 then q + 1 else q)
  else q

/-- `n` rounded half-even to 53 significant bits, as `PyLong_AsDouble` does. -/
def round53 (n : Nat) : Nat :=
  let bl := bitLength n
  if bl ≤ 53 then n else
    let sh := bl - 53
    roundDiv n (2 ^ sh) * 2 ^ sh

/-- `PyFloat_AsDouble` on an int (`PyLong_AsDouble`): `OverflowError` when the
rounded value reaches `2^1024`. -/
def intToFlt (v : Int) : Py Flt :=
  let m := round53 v.natAbs
  if m ≥ 2 ^ 1024 then .error (.overflowError "int too large to convert to float")
  else .ok ⟨decide (v < 0), 0, m, 1, ""⟩

/-- `PyFloat_AsDouble(o)`, Objects/floatobject.c:257-313. -/
def asDouble (o : Obj) : Py Flt :=
  match o with
  | .float f => .ok f
  | .bool _ | .int _ | .index _ =>
    match o.index? with
    | some v => intToFlt v
    | none => .error (.typeError "unreachable")
  | _ => .error (.typeError s!"must be real number, not {o.typeName}")

/-! ## `PyOS_double_to_string` for `e`, `f`, `g` -/

/-- `x * 10^k` rounded half-even, for `x = num / den`. -/
def scaled (num den : Nat) (k : Int) : Nat :=
  if k ≥ 0 then roundDiv (num * 10 ^ k.toNat) den
  else roundDiv num (den * 10 ^ (-k).toNat)

def negLogLoop : Nat → Nat → Nat → Nat → Nat
  | 0, k, _, _ => k
  | fuel + 1, k, num, den =>
    if num * 10 ^ k ≥ den then k else negLogLoop fuel (k + 1) num den

/-- `⌊log10 x⌋` for `x = num / den > 0`. -/
def floorLog10 (num den : Nat) : Int :=
  if num ≥ den then ((Nat.toDigits 10 (num / den)).length : Int) - 1
  else -(negLogLoop 400 1 num den : Nat)

def digitsOf (n : Nat) : Seq := (Nat.toDigits 10 n).map Char.toNat

/-- `digits` padded with zeros on the left to width `w`. -/
def padZeros (w : Nat) (ds : Seq) : Seq := List.replicate (w - ds.length) 48 ++ ds

/-- Trailing zeros removed. -/
def stripZeros (ds : Seq) : Seq := (ds.reverse.dropWhile (· == 48)).reverse

/-- `(digits, exponent)`: `x` rounded to `n ≥ 1` significant digits; exactly `n`
digits. The zero value has exponent 0. -/
def sigDigits (num den n : Nat) : Seq × Int :=
  if num = 0 then (List.replicate n 48, 0) else
    let e := floorLog10 num den
    let m := scaled num den ((n : Int) - 1 - e)
    if m ≥ 10 ^ n then (digitsOf (m / 10), e + 1) else (digitsOf m, e)

/-- `%+.02d`. -/
def expText (e : Int) : Seq :=
  [if e < 0 then 45 else 43] ++ padZeros 2 (digitsOf e.natAbs)

def fmtE (expChar : Nat) (num den prec : Nat) (alt : Bool) : Seq :=
  let (ds, e) := sigDigits num den (prec + 1)
  ds.take 1 ++ (if prec > 0 ∨ alt then [46] else []) ++ ds.drop 1 ++ [expChar] ++ expText e

def fmtF (num den prec : Nat) (alt : Bool) : Seq :=
  let ds := padZeros (prec + 1) (digitsOf (scaled num den prec))
  let n := ds.length - prec
  ds.take n ++ (if prec > 0 ∨ alt then [46] else []) ++ ds.drop n

def fmtG (expChar : Nat) (num den prec : Nat) (alt : Bool) : Seq :=
  let p := max prec 1
  let (ds, x) := sigDigits num den p
  let decpt : Int := x + 1
  if decpt ≤ -4 ∨ decpt > p then
    let body := if alt then ds else (let t := stripZeros ds; if t.isEmpty then [48] else t)
    body.take 1 ++ (if body.length > 1 ∨ alt then [46] else []) ++ body.drop 1 ++ [expChar] ++ expText x
  else if decpt ≤ 0 then
    let fr := if alt then ds else stripZeros ds
    asc "0." ++ List.replicate (-decpt).toNat 48 ++ fr
  else
    let n := decpt.toNat
    let fr := if alt then ds.drop n else stripZeros (ds.drop n)
    ds.take n ++ (if !fr.isEmpty ∨ alt then [46] else []) ++ fr

/-- `PyOS_double_to_string(x, type, prec, alt ? Py_DTSF_ALT : 0, NULL)`,
Python/pystrtod.c:1243-1336 with `format_float_short` (:932-1241), for type in
`eEfFgG` and `prec ≥ 0`. -/
def dtoa (x : Flt) (type : Nat) (prec : Nat) (alt : Bool) : Seq :=
  let up := type = 69 ∨ type = 70 ∨ type = 71
  if x.kind = 2 then asc (if up then "NAN" else "nan")
  else
    let sign := if x.neg then [45] else []
    if x.kind = 1 then sign ++ asc (if up then "INF" else "inf")
    else
      let e : Nat := if up then 69 else 101
      sign ++
      (if type = 101 ∨ type = 69 then fmtE e x.num x.den prec alt
       else if type = 102 ∨ type = 70 then fmtF x.num x.den prec alt
       else fmtG e x.num x.den prec alt)

/-! ## `int` to text -/

/-- `n` in `base` (8 or 16), lower case. -/
def digitsBase (base : Nat) (n : Nat) : Seq :=
  (Nat.toDigits base n).map Char.toNat

/-- `PyNumber_ToBase(val, base)`, Objects/abstract.c:2895-2914 and
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
  | .float f =>
    if f.kind = 2 then .error (.valueError "cannot convert float NaN to integer")
    else if f.kind = 1 then .error (.overflowError "cannot convert float infinity to integer")
    else
      let t : Int := (f.num / f.den : Nat)
      .ok (if f.neg then -t else t)
  | _ =>
    match o.index? with
    | some v => .ok v
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
