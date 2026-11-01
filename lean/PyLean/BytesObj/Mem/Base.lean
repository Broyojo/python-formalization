import PyLean.BytesObj.Exc
import PyLean.RangeSlice.Model

/-!
Vocabulary of the `memoryview` model (`Objects/memoryobject.c`, CPython 3.14.7, 64-bit
little-endian build): exceptions, native format characters, raw byte access and the
exact IEEE conversions behind the formats `f`, `d` and `e`.

* The address space is one byte store (`Mem`), a list of bytes; a C pointer is an `Int`
  offset into it. All exporters of a script live in the same store, so overlapping
  `memcpy`/`memmove` behave as in C.
* A Python `float` is its 64-bit IEEE pattern (`Nat`), so float paths are exact: no
  Lean `Float` appears anywhere. The narrowing conversions round to nearest, ties to
  even, as `cvtsd2ss`, `_PyLong_Frexp` and `PyFloat_Pack2` do.
* A C format string is a `List Char`; a position past the end reads NUL (`cc`).
-/

namespace PyLean.BytesObj.Mem

open PyLean

/-! ## Exceptions without a `PyExc` constructor -/

def bufferError (m : String) : PyExc := .named "BufferError" m
def notImplError (m : String) : PyExc := .named "NotImplementedError" m
def systemError (m : String) : PyExc := .named "SystemError" m
def runtimeError (m : String) : PyExc := .named "RuntimeError" m
def structError (m : String) : PyExc := .named "error" m
def memoryError : PyExc := .named "MemoryError" ""
/-- `PyUnicode_AsASCIIString` on a non-ASCII format; its text embeds the character. -/
def unicodeEncodeError : PyExc := .named "UnicodeEncodeError" "~'ascii' codec can't encode"

/-- `CHECK_RELEASED`, memoryobject.c:184-189. -/
def releasedError : PyExc := .valueError "operation forbidden on released memoryview object"
/-- `CHECK_RESTRICTED`, memoryobject.c:198-203. -/
def restrictedError : PyExc := .valueError "cannot create new view on restricted memoryview"

/-! ## C strings -/

/-- `s[i]` for a C string: a position past the end reads the terminating NUL. -/
def cc (s : List Char) (i : Nat) : Char := s.getD i '\x00'

/-- The string as Python prints it. A format has no embedded NUL by the time it is
printed. -/
def fmtText (s : List Char) : String := String.ofList s

/-! ## Native format characters -/

/-- The `switch` of `get_native_fmtchar`, memoryobject.c:1209-1221 (`-1`: unknown). -/
def fmtSize : Char → Int
  | 'c' | 'b' | 'B' => 1
  | 'h' | 'H' => 2
  | 'i' | 'I' => 4
  | 'l' | 'L' => 8
  | 'q' | 'Q' => 8
  | 'n' | 'N' => 8
  | 'f' => 4
  | 'd' => 8
  | 'e' => 2
  | '?' => 1
  | 'P' => 8
  | _ => -1

/-- `get_native_fmtchar`, memoryobject.c:1202-1229: `(char, size)`, or `none` for `-1`.
Skips one leading `@`, then requires `fmt[0]` known and `fmt[1] == '\0'`. -/
def getNativeFmtchar (fmt : List Char) : Option (Char × Int) :=
  let fmt := if cc fmt 0 = '@' then fmt.drop 1 else fmt
  let size := fmtSize (cc fmt 0)
  if size > 0 ∧ cc fmt 1 = '\x00' then some (cc fmt 0, size) else none

/-- The `switch` of `get_native_fmtstr`, memoryobject.c:1246-1265. -/
def nativeChar : Char → Bool
  | 'c' | 'b' | 'B' | 'h' | 'H' | 'i' | 'I' | 'l' | 'L' | 'q' | 'Q' | 'n' | 'N'
  | 'f' | 'd' | 'e' | '?' | 'P' => true
  | _ => false

/-- `get_native_fmtstr`, memoryobject.c:1231-1268. -/
def getNativeFmtstr (fmt : List Char) : Option (List Char) :=
  let at_ := cc fmt 0 = '@'
  let fmt := if at_ then fmt.drop 1 else fmt
  if cc fmt 0 = '\x00' ∨ cc fmt 1 ≠ '\x00' then none
  else if nativeChar (cc fmt 0) then some (if at_ then ['@', cc fmt 0] else [cc fmt 0])
  else none

/-- `IS_BYTE_FORMAT`, memoryobject.c:1200. -/
def isByteFormat (f : Char) : Bool := f == 'b' || f == 'B' || f == 'c'

/-! ## The byte store -/

abbrev Mem := List Nat

def rdByte (m : Mem) (p : Int) : Nat := m.getD p.toNat 0

/-- `n` bytes at `p`. -/
def rdBytes (m : Mem) (p : Int) : Nat → List Nat
  | 0 => []
  | n + 1 => rdByte m p :: rdBytes m (p + 1) n

/-- `memcpy(p, bs, len(bs))`. Writes outside the store are dropped; a well-formed view
never makes one. -/
def wrBytes (m : Mem) (p : Int) : List Nat → Mem
  | [] => m
  | b :: bs => wrBytes (m.set p.toNat b) (p + 1) bs

/-- Little-endian value of a byte list. -/
def decLE : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * decLE bs

/-- The `k` low bytes of `n`, little-endian. -/
def encLE (n : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => (n % 256) :: encLE (n / 256) k

/-- `(type)x` for an integer type of `k` bytes, then its bytes. -/
def encInt (v : Int) (k : Nat) : List Nat := encLE (v % (2 ^ (8 * k) : Int)).toNat k

/-- Two's complement value of the `k`-byte pattern `v`. -/
def sx (k : Nat) (v : Nat) : Int :=
  if v ≥ 2 ^ (8 * k - 1) then (v : Int) - 2 ^ (8 * k) else v

/-- Unsigned `k`-byte value at `p`. -/
def rdU (m : Mem) (p : Int) (k : Nat) : Nat := decLE (rdBytes m p k)
/-- Signed `k`-byte value at `p`. -/
def rdS (m : Mem) (p : Int) (k : Nat) : Int := sx k (rdU m p k)

/-! ## Exact float formats -/

def two63 : Nat := 2 ^ 63
def infBits : Nat := 0x7FF * 2 ^ 52

def dSign (d : Nat) : Nat := d / two63 % 2
def dExp (d : Nat) : Nat := d / 2 ^ 52 % 2 ^ 11
def dFrac (d : Nat) : Nat := d % 2 ^ 52
def dIsNaN (d : Nat) : Bool := dExp d == 2047 && dFrac d != 0
def dIsZero (d : Nat) : Bool := d % two63 == 0

/-- `x == y` on doubles: NaN differs from everything, `0.0 == -0.0`. -/
def dEq (a b : Nat) : Bool :=
  if dIsNaN a || dIsNaN b then false
  else if dIsZero a && dIsZero b then true
  else a == b

/-- `n / 2^sh`, rounded to nearest, ties to even. -/
def rshiftRound (n sh : Nat) : Nat :=
  if sh = 0 then n
  else
    let q := n / 2 ^ sh
    let r := n % 2 ^ sh
    if 2 * r > 2 ^ sh ∨ (2 * r = 2 ^ sh ∧ q % 2 = 1) then q + 1 else q

/-- The mantissa and binary exponent of a finite non-zero double: `|x| = M * 2^E`. -/
def dMant (d : Nat) : Nat × Int :=
  let e := dExp d
  let f := dFrac d
  if e = 0 then (f, -1074) else (f + 2 ^ 52, (e : Int) - 1075)

/-- `double` value of the 32-bit float pattern `x` (`dest = x` in `UNPACK_SINGLE(d, ptr,
float)`, memoryobject.c:1822): exact, a signalling NaN comes back quiet. -/
def widen32 (x : Nat) : Nat :=
  let s := x / 2 ^ 31 % 2
  let e := x / 2 ^ 23 % 2 ^ 8
  let f := x % 2 ^ 23
  let sgn := s * two63
  if e = 255 then
    if f = 0 then sgn + infBits
    else sgn + infBits + (f % 2 ^ 22 + 2 ^ 22) * 2 ^ 29
  else if e = 0 then
    if f = 0 then sgn
    else
      let l := Nat.log2 f
      sgn + (l + 874) * 2 ^ 52 + (f - 2 ^ l) * 2 ^ (52 - l)
  else sgn + (e + 896) * 2 ^ 52 + f * 2 ^ 29

/-- `(float)d`, `PACK_SINGLE(ptr, d, float)` (memoryobject.c:1973): to nearest, ties to
even; too large a value becomes an infinity, with no error. -/
def narrow32 (d : Nat) : Nat :=
  let sgn := dSign d * 2 ^ 31
  let inf := sgn + 255 * 2 ^ 23
  if dExp d = 2047 then
    if dFrac d = 0 then inf
    else
      let top := dFrac d / 2 ^ 29
      inf + (top % 2 ^ 22 + 2 ^ 22)
  else if dIsZero d then sgn
  else
    let (m, ee) := dMant d
    let l := Nat.log2 m
    let ex : Int := l + ee
    if ex > 127 then inf
    else if ex ≥ -126 then
      let m' := rshiftRound m (l - 23)
      if m' ≥ 2 ^ 24 then
        (if ex + 1 > 127 then inf else sgn + (ex + 128).toNat * 2 ^ 23)
      else sgn + (ex + 127).toNat * 2 ^ 23 + (m' - 2 ^ 23)
    else sgn + rshiftRound m (-(ee + 149)).toNat

/-- `PyFloat_Unpack2`, Objects/floatobject.c:2379-2433, on the 16-bit pattern `x`. -/
def unpack2 (x : Nat) : Nat :=
  let s := x / 2 ^ 15 % 2
  let e := x / 2 ^ 10 % 2 ^ 5
  let f := x % 2 ^ 10
  let sgn := s * two63
  if e = 31 then
    if f = 0 then sgn + infBits else sgn + infBits + f * 2 ^ 42
  else if e = 0 then
    if f = 0 then sgn
    else
      let l := Nat.log2 f
      sgn + (l + 999) * 2 ^ 52 + (f - 2 ^ l) * 2 ^ (52 - l)
  else sgn + (e + 1008) * 2 ^ 52 + f * 2 ^ 42

def pack2Overflow : PyExc := .overflowError "float too large to pack with 'e' format"

/-- `PyFloat_Pack2`, Objects/floatobject.c:1993-2085, as a 16-bit pattern. -/
def pack2 (d : Nat) : Py Nat :=
  let sgn := dSign d * 2 ^ 15
  if dIsZero d then .ok sgn
  else if dExp d = 2047 then
    if dFrac d = 0 then .ok (sgn + 31 * 2 ^ 10)
    else
      let bits := dFrac d / 2 ^ 42
      .ok (sgn + 31 * 2 ^ 10 + (if bits = 0 then 512 else bits))
  else
    let (m, ee) := dMant d
    let l := Nat.log2 m
    let ex : Int := l + ee
    if ex ≥ 16 then .error pack2Overflow
    else if ex < -25 then .ok sgn
    else if ex < -14 then .ok (sgn + rshiftRound m (-(ee + 24)).toNat)
    else
      let m' := rshiftRound m (l - 10)
      if m' ≥ 2 ^ 11 then
        (if ex + 1 ≥ 16 then .error pack2Overflow else .ok (sgn + (ex + 16).toNat * 2 ^ 10))
      else .ok (sgn + (ex + 15).toNat * 2 ^ 10 + (m' - 2 ^ 10))

/-- `PyLong_AsDouble`: to nearest, ties to even, `OverflowError` past `DBL_MAX`. -/
def longAsDouble (n : Int) : Py Nat :=
  let sgn := if n < 0 then two63 else 0
  let x := n.natAbs
  if x = 0 then .ok 0
  else
    let l := Nat.log2 x
    let m' := if l ≤ 52 then x * 2 ^ (52 - l) else rshiftRound x (l - 52)
    let (m', l') := if m' ≥ 2 ^ 53 then (2 ^ 52, l + 1) else (m', l)
    if l' > 1023 then .error (.overflowError "int too large to convert to float")
    else .ok (sgn + (l' + 1023) * 2 ^ 52 + (m' - 2 ^ 52))

/-- `x == n`, comparing a double with an int exactly (`float_richcompare`). -/
def dEqInt (d : Nat) (n : Int) : Bool :=
  if dExp d = 2047 then false
  else if dIsZero d then n == 0
  else
    let (m, ee) := dMant d
    let v : Int := if dSign d = 1 then -(m : Int) else m
    if ee ≥ 0 then v * 2 ^ ee.toNat == n else v == n * 2 ^ (-ee).toNat

/-! ## Python values -/

/-- A value `unpack_single` or the `struct` module produces. -/
inductive Item where
  | int (n : Int)
  | bool (b : Bool)
  /-- 64-bit IEEE pattern. -/
  | float (bits : Nat)
  | bytes (b : List Nat)
  deriving Repr, DecidableEq, Inhabited

/-- `v == w` for two unpacked values (`PyObject_RichCompareBool(v, w, Py_EQ)`). `bool`
is an `int`; `bytes` differs from every number. -/
def itemEq : Item → Item → Bool
  | .int a, .int b => a == b
  | .bool a, .bool b => a == b
  | .int a, .bool b | .bool b, .int a => a == (if b then 1 else 0)
  | .float a, .float b => dEq a b
  | .float a, .int b | .int b, .float a => dEqInt a b
  | .float a, .bool b | .bool b, .float a => dEqInt a (if b then 1 else 0)
  | .bytes a, .bytes b => a == b
  | _, _ => false

end PyLean.BytesObj.Mem
