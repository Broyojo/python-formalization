import PyLean.Sequences.Common

/-!
Python values that `array.array` reads and writes (`Modules/arraymodule.c`,
CPython 3.15.2), with the conversions of `PyArg_Parse`.

* Floats are binary64 bit patterns, single floats binary32 and `e` items binary16
  bit patterns, and a complex is the pair of its parts' binary64 patterns, so that
  storing, loading, `tobytes` and `byteswap` are exact integer operations. The
  conversions (`int` to `double`, `double` to `float`, `PyFloat_Pack2`,
  `PyFloat_Unpack2`, `PyFloat_Unpack4`) and the comparisons are exact arithmetic on
  those patterns; `lean/PyLean/Binary64/` has no model of these.
  NaN conversion follows the hardware (the quiet bit is set, the payload is kept
  in its top bits), which C leaves unspecified.
* LP64: `short` 16, `int` and `wchar_t` 32 (signed), `long` and `long long` 64 bits.
-/

namespace PyLean.Sequences

open PyLean

/-- A Python object as seen by array code. `obj t i` is any other object of type
`t`; `i` is its `__index__`, if it has one. -/
inductive PyVal where
  | int (n : Int)
  | float (bits : Nat)
  | complex (re im : Nat)
  | str (cps : List Nat)
  | obj (tname : String) (index : Option Int)
  deriving Repr, DecidableEq, Inhabited

instance : Inhabited PyVal := ⟨.int 0⟩

def PyVal.typeName : PyVal → String
  | .int _ => "int"
  | .float _ => "float"
  | .complex _ _ => "complex"
  | .str _ => "str"
  | .obj t _ => t

/-- `_PyNumber_Index` (Objects/abstract.c:1410-1454). -/
def toIndex (v : PyVal) : Py Int :=
  match v with
  | .int n => .ok n
  | .obj _ (some n) => .ok n
  | v => .error (.typeError s!"'{v.typeName}' object cannot be interpreted as an integer")

def longMin : Int := -9223372036854775808
def longMax : Int := 9223372036854775807

/-- `PyLong_AsLong` (Objects/longobject.c:673-688), through `_PyNumber_Index`. -/
def asLongV (v : PyVal) : Py Int := do
  let n ← toIndex v
  if longMin ≤ n ∧ n ≤ longMax then return n
  throw (.overflowError "Python int too large to convert to C long")

/-! ### Floating-point bit patterns -/

def two52 : Nat := 4503599627370496
def two63 : Nat := 9223372036854775808

/-- Round `m / 2^s` to nearest, ties to even. -/
def roundShift (m s : Nat) : Nat :=
  if s = 0 then m
  else
    let q := m >>> s
    let r := m % 2 ^ s
    let half := 2 ^ (s - 1)
    if r > half ∨ (r = half ∧ q % 2 = 1) then q + 1 else q

/-- `PyLong_AsDouble` (Objects/longobject.c:3567-3588, `_PyLong_Frexp` rounds half
to even): the binary64 pattern of an int, or `none` on overflow. -/
def intToDouble (n : Int) : Option Nat :=
  if n = 0 then some 0
  else
    let sign : Nat := if n < 0 then two63 else 0
    let m := n.natAbs
    let L := bitLength m
    let (q, e) :=
      if L ≤ 53 then (m <<< (53 - L), L - 1)
      else
        let q := roundShift m (L - 53)
        if q = 2 * two52 then (two52, L) else (q, L - 1)
    if e ≥ 1024 then none else some (sign + ((e + 1023) <<< 52) + (q - two52))

/-- `PyFloat_AsDouble` (Objects/floatobject.c:247-299) on the values we model. -/
def asDouble (v : PyVal) : Py Nat :=
  let ofInt (n : Int) : Py Nat :=
    match intToDouble n with
    | some b => .ok b
    | none => .error (.overflowError "int too large to convert to float")
  match v with
  | .float b => .ok b
  | .int n => ofInt n
  | .obj _ (some n) => ofInt n
  | v => .error (.typeError s!"must be real number, not {v.typeName}")

/-- `PyComplex_AsCComplex` (Objects/complexobject.c:537-571) on the values we model:
a complex is itself, anything else is `PyFloat_AsDouble` with imaginary part 0. No
modelled object has `__complex__`. -/
def asComplex (v : PyVal) : Py (Nat × Nat) :=
  match v with
  | .complex re im => .ok (re, im)
  | v =>
    match asDouble v with
    | .ok b => .ok (b, 0)
    | .error e => .error e

/-- `(float)x`, round to nearest even, on bit patterns. -/
def doubleToFloat (bits : Nat) : Nat :=
  let s := if bits ≥ two63 then 2147483648 else 0
  let e := (bits % two63) >>> 52
  let f := bits % two52
  if e = 2047 then
    if f = 0 then s + 2139095040 else s + 2143289344 + (f >>> 29) % 4194304
  else if e = 0 then s
  else
    let m := two52 + f
    if e ≥ 897 then
      -- normal single: exp = e - 1023 >= -126
      let q := roundShift m 29
      let (q, e') := if q = 16777216 then (8388608, e + 1) else (q, e)
      if e' ≥ 1151 then s + 2139095040
      else s + ((e' - 896) <<< 23) + (q - 8388608)
    else
      s + roundShift m (29 + (897 - e))

/-- `(double)x` on bit patterns. -/
def floatToDouble (bits : Nat) : Nat :=
  let s := if bits ≥ 2147483648 then two63 else 0
  let e := (bits % 2147483648) >>> 23
  let f := bits % 8388608
  if e = 255 then
    if f = 0 then s + (2047 <<< 52) else s + (2047 <<< 52) + ((f ||| 4194304) <<< 29)
  else if e = 0 then
    if f = 0 then s
    else
      let L := bitLength f
      s + ((L + 873) <<< 52) + ((f <<< (53 - L)) - two52)
  else s + ((e + 896) <<< 52) + (f <<< 29)

/-- `PyFloat_Unpack4` (Objects/floatobject.c:2146-2201) on a binary32 pattern: `(double)x`,
except that a signalling NaN stays signalling (:2165-2177). -/
def unpack4 (bits : Nat) : Nat :=
  let y := floatToDouble bits
  if (bits % 2147483648) >>> 23 = 255 ∧ bits % 8388608 ≠ 0 ∧ bits % 8388608 < 4194304 then
    y - 2251799813685248
  else y

/-- `PyFloat_Unpack2` (Objects/floatobject.c:2090-2143), the binary64 pattern of a
binary16 pattern. A NaN keeps its 10 bits at the top of the fraction (:2118-2124). -/
def halfToDouble (h : Nat) : Nat :=
  let s := if h ≥ 32768 then two63 else 0
  let e := (h % 32768) >>> 10
  let f := h % 1024
  if e = 31 then s + (2047 <<< 52) + (f <<< 42)
  else if e = 0 then
    if f = 0 then s
    else
      let L := bitLength f
      s + ((L + 998) <<< 52) + ((f <<< (53 - L)) - two52)
  else s + ((e + 1008) <<< 52) + (f <<< 42)

/-- The error of `PyFloat_Pack2` (Objects/floatobject.c:1996-1999). -/
def packHalfErr : PyExc := .overflowError "float too large to pack with e format"

/-- `PyFloat_Pack2` (Objects/floatobject.c:1895-2000) on a binary64 pattern: the binary16
pattern, or `OverflowError`. `be = 0` is a zero, or a subnormal double, which `frexp` puts
far below `2**-25`, so both give a signed zero. `e` is the exponent `frexp` gives after
normalising to `[1, 2)`. In the gradual underflow branch `f * 2**(14 + e) * 1024` is
`m / 2**(28 - e)` for the 53-bit `m`; a carry to 1024 there is the smallest normal, as in
the source (`bits = 0`, `e = 1`). -/
def packHalf (bits : Nat) : Py Nat :=
  let s : Nat := if bits ≥ two63 then 32768 else 0
  let be := (bits % two63) >>> 52
  let f := bits % two52
  if be = 2047 then
    if f = 0 then .ok (s + 31744)
    else
      -- NaN: the top 10 bits of the fraction, or the quiet bit if those are 0
      let b := f >>> 42
      .ok (s + 31744 + (if b = 0 then 512 else b))
  else if be = 0 then .ok s
  else
    let e : Int := (be : Int) - 1023
    if e ≥ 16 then .error packHalfErr
    else if e < -25 then .ok s
    else if e < -14 then .ok (s + roundShift (two52 + f) (28 - e).toNat)
    else
      let q := roundShift f 42
      let (q, e') : Nat × Nat := if q = 1024 then (0, (e + 16).toNat) else (q, (e + 15).toNat)
      if e' = 31 then .error packHalfErr else .ok (s + (e' <<< 10) + q)

/-- A decoded binary64: NaN, infinity with a sign, or `m * 2^e`. -/
inductive DVal where
  | nan
  | inf (neg : Bool)
  | finite (m : Int) (e : Int)
  deriving Repr, DecidableEq

def decodeDouble (bits : Nat) : DVal :=
  let neg := bits ≥ two63
  let be := (bits % two63) >>> 52
  let f := bits % two52
  if be = 2047 then (if f = 0 then .inf neg else .nan)
  else
    let (m, e) : Nat × Int := if be = 0 then (f, -1074) else (two52 + f, (be : Int) - 1075)
    .finite (if neg then -(m : Int) else m) e

/-- Exact comparison of `a * 2^x` and `b * 2^y`. -/
def cmpScaled (a x b y : Int) : Ordering :=
  let e := min x y
  compare (a * 2 ^ (x - e).toNat) (b * 2 ^ (y - e).toNat)

/-- The order of two numbers, `none` if one is NaN (`float_richcompare`,
Objects/floatobject.c:372-596, compares int and float exactly). -/
def numOrder (a b : DVal) : Option Ordering :=
  match a, b with
  | .nan, _ | _, .nan => none
  | .inf x, .inf y => some (compare (if x then (0 : Int) else 1) (if y then 0 else 1))
  | .inf x, _ => some (if x then .lt else .gt)
  | _, .inf y => some (if y then .gt else .lt)
  | .finite m e, .finite n f => some (cmpScaled m e n f)

def PyVal.num : PyVal → Option DVal
  | .int n => some (.finite n 0)
  | .float b => some (decodeDouble b)
  | _ => none

/-- The parts of a number as `complex_richcompare` sees them
(Objects/complexobject.c:819-869, `Py_EQ` and `Py_NE` only): an int or float has imaginary part 0. -/
def PyVal.parts : PyVal → Option (DVal × DVal)
  | .complex re im => some (decodeDouble re, decodeDouble im)
  | v => v.num.map (fun x => (x, .finite 0 0))

def opSym : CmpOp → String
  | .lt => "<" | .le => "<=" | .eq => "==" | .ne => "!=" | .gt => ">" | .ge => ">="

/-- Does `op` hold for an ordering? (`Py_RETURN_RICHCOMPARE`.) -/
def opHolds (op : CmpOp) (o : Ordering) : Bool :=
  match op, o with
  | .lt, .lt | .le, .lt | .le, .eq | .eq, .eq | .ne, .lt | .ne, .gt | .gt, .gt | .ge, .gt | .ge, .eq => true
  | _, _ => false

/-- The code-point order of strings. -/
def strOrder : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => if x < y then .lt else if y < x then .gt else strOrder xs ys

/-- `a == b` as a truth value, for the objects stored in an array against any
object (`PyObject_RichCompareBool(a, b, Py_EQ)`; a fresh `float` is never
identical to anything, so NaN is unequal to itself; other objects are compared by
identity and differ from array items). -/
def pvEq (a b : PyVal) : Bool :=
  match a, b with
  | .str x, .str y => x == y
  | a, b =>
    match a.num, b.num with
    | some x, some y => numOrder x y == some .eq
    | _, _ =>
      match a.parts, b.parts with
      | some (r, i), some (r', i') => numOrder r r' == some .eq && numOrder i i' == some .eq
      | _, _ => false

/-- `PyObject_RichCompare(a, b, op)` on these values. A complex has no order. -/
def pvRich (op : CmpOp) (a b : PyVal) : Py Bool :=
  match a, b with
  | .str x, .str y => .ok (opHolds op (strOrder x y))
  | a, b =>
    match a.num, b.num with
    | some x, some y =>
      match numOrder x y with
      | some o => .ok (opHolds op o)
      | none => .ok (op == .ne)
    | _, _ =>
      match op with
      | .eq => .ok (pvEq a b)
      | .ne => .ok (!pvEq a b)
      | op => .error (.typeError
          s!"'{opSym op}' not supported between instances of '{a.typeName}' and '{b.typeName}'")

end PyLean.Sequences
