import PyLean.MathInt.Model

/-!
Model of the `int` operations of `Objects/longobject.c` (CPython 3.15.2) that
the `math.integer` functions lean on: three-argument `pow` with a negative
exponent (`long_invmod`), `int.to_bytes` / `int.from_bytes`
(`_PyLong_AsByteArray` / `_PyLong_FromByteArray`, digit by digit with
`PyLong_SHIFT = 30`), `divmod` (`l_divmod`, including its single-digit fast
path and the `_pylong.int_divmod` twin of `Lib/_pylong.py`) and
`round(int, ndigits)` (`_PyLong_DivmodNear`).

Not modelled, and stated where used: the multiplication / schoolbook-division
kernels (`long_mul`, `x_divrem`, the windowed exponentiation of `long_pow`,
Burnikel-Ziegler `_divmod_pos`), whose results are taken as the exact
mathematical values.
-/

namespace PyLean.MathInt

open PyLean

/-! ## Three-argument `pow`, longobject.c:4909-5249 -/

/-- The loop of `long_invmod`, longobject.c:4918-4938: Python's
`while n: q, r = divmod(a, n); a, b, c, n = n, c, b - q*c, r`. -/
def invmodLoop : Nat → Int → Int → Int → Int → Py (Int × Int)
  | 0, _, _, _, _ => .error .modelFuel
  | fuel + 1, a, b, c, n =>
    if n = 0 then .ok (a, b)
    else
      let q := floorDiv a n
      let r := floorMod a n
      invmodLoop fuel n c (b - q * c) r

/-- `long_invmod(a, n)` for `n > 0`, longobject.c:4909-4967. -/
def invmod (a n : Int) : Py Int := do
  let (g, b) ← invmodLoop (n.toNat + 2) a 1 0 n
  if g ≠ 1 then throw (.valueError "base is not invertible for the given modulus")
  return b

/-- `a ** e % c` by square-and-multiply; stands in for the windowed loop of
`long_pow` (longobject.c:5116-5226), whose result is that value. -/
def modPowAux (c : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, base, e, acc =>
    if e = 0 then acc
    else modPowAux c fuel (base * base % c) (e / 2) (if e % 2 = 1 then acc * base % c else acc)

def modPow (a e c : Nat) : Nat := modPowAux c (e + 1) (a % c) e (1 % c)

/-- `pow(v, w, x)` for ints with `x` given, longobject.c:4970-5249. -/
def powMod (v w x : Int) : Py Int := do
  if x = 0 then throw (.valueError "pow() 3rd argument cannot be 0")
  let negativeOutput := x < 0
  let c : Int := x.natAbs
  if c = 1 then return 0
  let mut a := v
  let mut b := w
  if b < 0 then
    b := -b
    a ← invmod a c
  if a < 0 ∨ digitCount a.natAbs > digitCount c.natAbs then
    a := floorMod a c
  let z : Int := modPow a.toNat b.toNat c.toNat
  if negativeOutput ∧ z ≠ 0 then return z - c
  return z

/-! ## `int.to_bytes`, longobject.c:1109-1248 and :6395-6422 -/

def digitMask : Nat := 2 ^ 30 - 1

/-- The 30-bit digits of `n`, least significant first; `digitCount n` of them. -/
def digitsOf (n : Nat) : List Nat := go (digitCount n) n
where
  go : Nat → Nat → List Nat
    | 0, _ => []
    | k + 1, n => n % 2 ^ 30 :: go k (n / 2 ^ 30)

/-- State of `_PyLong_AsByteArray`: bytes written so far (least significant
first), `accum`, `accumbits`, `carry`. -/
structure ABState where
  out : List Nat
  accum : Nat
  accumbits : Nat
  carry : Nat
  deriving Repr, Inhabited

/-- "Store as many bytes as possible", longobject.c:1181-1190; `none` is the
jump to `Overflow`. -/
def storeBytes (n : Nat) : Nat → ABState → Option ABState
  | 0, st => some st
  | fuel + 1, st =>
    if st.accumbits ≥ 8 then
      if st.out.length ≥ n then none
      else storeBytes n fuel { st with out := st.out ++ [st.accum % 256],
                                       accumbits := st.accumbits - 8, accum := st.accum / 256 }
    else some st

/-- The digit loop of `_PyLong_AsByteArray`, longobject.c:1155-1191. -/
def asByteArrayLoop (n : Nat) (twos : Bool) : List Nat → ABState → Option ABState
  | [], st => some st
  | d :: ds, st =>
    let (d, carry) :=
      if twos then
        let t := (d ^^^ digitMask) + st.carry
        (t &&& digitMask, t >>> 30)
      else (d, st.carry)
    let accum := st.accum ||| (d <<< st.accumbits)
    let accumbits :=
      if ds = [] then st.accumbits + bitLength (if twos then d ^^^ digitMask else d)
      else st.accumbits + 30
    match storeBytes n (accumbits + 1) ⟨st.out, accum, accumbits, carry⟩ with
    | none => none
    | some st => asByteArrayLoop n twos ds st

/-- `_PyLong_AsByteArray(v, bytes, n, little_endian=1, is_signed, 1)`: the
bytes least significant first, longobject.c:1109-1248. -/
def asByteArray (v : Int) (n : Nat) (signed : Bool) : Py (List Nat) :=
  let overflow : Py (List Nat) := .error (.overflowError "int too big to convert")
  if v < 0 ∧ ¬signed then .error (.overflowError "can't convert negative int to unsigned")
  else
    let twos := decide (v < 0)
    match asByteArrayLoop n twos (digitsOf v.natAbs) ⟨[], 0, 0, if twos then 1 else 0⟩ with
    | none => overflow
    | some st =>
      let fill (out : List Nat) : Py (List Nat) :=
        .ok (out ++ List.replicate (n - out.length) (if twos then 255 else 0))
      if st.accumbits > 0 then
        if st.out.length ≥ n then overflow
        else
          let accum := if twos then st.accum ||| (255 <<< st.accumbits) else st.accum
          fill (st.out ++ [accum % 256])
      else if st.out.length = n ∧ signed then
        let signBitSet := decide (n > 0 ∧ st.out.getLastD 0 ≥ 128)
        if signBitSet = twos then .ok st.out else overflow
      else fill st.out

/-- `_PyBytesObject_SIZE` on LP64, pycore_bytesobject.h:74: the object header, the
hash and the terminating NUL. -/
def bytesObjectSize : Int := 33

/-- `int.to_bytes(length, byteorder, *, signed)`. Argument Clinic rejects a negative
`length` (`Py_ssize_t(allow_negative=False)`, clinic/longobject.c.h:332-349) before
`int_to_bytes_impl` (longobject.c:6394-6425) looks at `byteorder`, so a bad length
wins over a bad byteorder. `PyBytesWriter_Create(length)` reaches the limit check of
`_PyBytes_FromSize` (bytesobject.c:101-105) through `byteswriter_resize`. An ordinary
allocation failure (`MemoryError`) is out of scope, as everywhere in this project.
Bytes are `0..255`. -/
def toBytes (v : Int) (length : Int) (byteorder : String) (signed : Bool) : Py (List Nat) :=
  if length < ssizeMin ∨ length > ssizeMax then
    .error (.overflowError "Python int too large to convert to C ssize_t")
  else if length < 0 then .error (.valueError "length cannot be negative")
  else if byteorder ≠ "little" ∧ byteorder ≠ "big" then
    .error (.valueError "byteorder must be either 'little' or 'big'")
  else if length > ssizeMax - bytesObjectSize then
    .error (.overflowError "byte string is too large")
  else do
    let bs ← asByteArray v length.toNat signed
    return if byteorder = "little" then bs else bs.reverse

/-! ## `int.from_bytes`, longobject.c:1000-1107 and :6452-6503 -/

/-- Number of leading (most significant) bytes equal to `ins`, longobject.c:1034-1037;
`msbFirst` lists the bytes from the most significant one. -/
def countInsignificant (ins : Nat) : List Nat → Nat
  | [] => 0
  | b :: bs => if b ≠ ins then 0 else countInsignificant ins bs + 1

/-- The copy loop of `_PyLong_FromByteArray`, longobject.c:1057-1089, on the
significant bytes least significant first; returns the digits written. -/
def fromByteArrayLoop (signed : Bool) : List Nat → (carry accum accumbits : Nat) → List Nat
  | [], _, accum, accumbits => if accumbits ≠ 0 then [accum] else []
  | b :: bs, carry, accum, accumbits =>
    let (b, carry) :=
      if signed then
        let t := (255 ^^^ b) + carry
        (t &&& 255, t >>> 8)
      else (b, carry)
    let accum := accum ||| (b <<< accumbits)
    let accumbits := accumbits + 8
    if accumbits ≥ 30 then
      (accum &&& digitMask) :: fromByteArrayLoop signed bs carry (accum >>> 30) (accumbits - 30)
    else fromByteArrayLoop signed bs carry accum accumbits

/-- Value of a little-endian list of 30-bit digits. -/
def digitsValue : List Nat → Nat
  | [] => 0
  | d :: ds => d + 2 ^ 30 * digitsValue ds

/-- `_PyLong_FromByteArray(bytes, n, little_endian=1, is_signed)` on bytes
least significant first, longobject.c:1000-1107. -/
def fromByteArray (lsbFirst : List Nat) (signed : Bool) : Int :=
  let n := lsbFirst.length
  if n = 0 then 0
  else
    let isSigned := signed && decide (lsbFirst.getLastD 0 ≥ 128)
    let i := countInsignificant (if isSigned then 255 else 0) lsbFirst.reverse
    let nsig := n - i
    let nsig := if isSigned ∧ nsig < n then nsig + 1 else nsig
    let digits := fromByteArrayLoop isSigned (lsbFirst.take nsig) 1 0 0
    let mag : Int := digitsValue digits
    if isSigned then -mag else mag

/-- The three routes of `int_from_bytes_impl` to the bytes of its argument,
longobject.c:6471-6497. `exact` is `PyBytes_CheckExact`. `buffer` is anything else
with `PyObject_CheckBuffer`, including a `bytes` subclass: `PyObject_GetBuffer` with
`PyBUF_SIMPLE` can fail, and `__bytes__` is not consulted. `other` is
`PyObject_Bytes`, which runs `__bytes__` or iterates, and can fail. The payload is
what that step yields. -/
inductive BytesObj where
  | exact (bs : List Nat)
  | buffer (view : Py (List Nat))
  | other (bytes : Py (List Nat))

/-- `int_from_bytes_impl`, longobject.c:6452-6505, for the class whose constructor is
`ctor`. `byteorder` is checked before the object is touched. `ctor` is the call of
longobject.c:6499-6501 for a subclass (it returns an arbitrary object and can raise);
for `int` itself it is `Except.ok`. -/
def fromBytesImpl {α : Type} (ctor : Int → Py α) (obj : BytesObj) (byteorder : String)
    (signed : Bool) : Py α :=
  if byteorder ≠ "little" ∧ byteorder ≠ "big" then
    .error (.valueError "byteorder must be either 'little' or 'big'")
  else
    let lsb (bs : List Nat) := if byteorder = "little" then bs else bs.reverse
    match obj with
    | .exact bs => ctor (fromByteArray (lsb bs) signed)
    | .buffer view => do ctor (fromByteArray (lsb (← view)) signed)
    | .other bytes => do ctor (fromByteArray (lsb (← bytes)) signed)

/-- `int.from_bytes(bytes, byteorder, *, signed)` on an exact `bytes`. -/
def fromBytes (bs : List Nat) (byteorder : String) (signed : Bool) : Py Int :=
  fromBytesImpl .ok (.exact bs) byteorder signed

/-! ## `divmod`, longobject.c:4378-4558 and Lib/_pylong.py:511-541 -/

/-- `fast_floor_div` and `fast_mod`, longobject.c:4378-4418, for single-digit
nonzero `a`, `b` (`left = |a|`, `right = |b|`). -/
def fastDivmod (a b : Int) : Int × Int :=
  let left : Int := a.natAbs
  let right : Int := b.natAbs
  let same := decide (a < 0) = decide (b < 0)
  let div := if same then left.tdiv right else -1 - (left - 1).tdiv right
  let sign : Int := if b < 0 then -1 else 1
  let md := if same then left.tmod right else right - 1 - (left - 1).tmod right
  (div, md * sign)

/-- The `b > 0` branches of `_pylong.int_divmod(a, b)`, Lib/_pylong.py:537-541,
with `_divmod_pos` (Burnikel-Ziegler, :511-525) taken as exact Nat division. -/
def pylongDivmodPos (a b : Int) : Int × Int :=
  if a < 0 then
    let a' := -a - 1                     -- ~a
    let q : Int := (a'.toNat / b.toNat : Nat)
    let r : Int := (a'.toNat % b.toNat : Nat)
    (-q - 1, b + (-r - 1))               -- ~q, b + ~r
  else ((a.toNat / b.toNat : Nat), (a.toNat % b.toNat : Nat))

/-- `_pylong.int_divmod(a, b)` for `b != 0`, Lib/_pylong.py:528-541. -/
def pylongIntDivmod (a b : Int) : Int × Int :=
  if b < 0 then
    let (q, r) := pylongDivmodPos (-a) (-b)
    (q, -r)
  else pylongDivmodPos a b

/-- `divmod(v, w)` for ints, `l_divmod`, longobject.c:4482-4558.
`long_divrem` (:3217-3279) gives the truncated quotient and remainder. -/
def divmod (v w : Int) : Py (Int × Int) :=
  let sv := digitCount v.natAbs
  let sw := digitCount w.natAbs
  if sv = 1 ∧ sw = 1 then .ok (fastDivmod v w)
  else if sw > 300 ∧ (sv : Int) - sw > 150 then .ok (pylongIntDivmod v w)
  else if w = 0 then .error (.zeroDivisionError "division by zero")
  else
    let div := v.tdiv w
    let md := v.tmod w
    if (md < 0 ∧ w > 0) ∨ (md > 0 ∧ w < 0) then .ok (div - 1, md + w)
    else .ok (div, md)

/-! ## `round(int, ndigits)`, longobject.c:6118-6267 -/

/-- `_PyLong_DivmodNear(a, b)`, longobject.c:6118-6191. -/
def divmodNear (a b : Int) : Int × Int :=
  let quoIsNeg := decide (a < 0) ≠ decide (b < 0)
  let quo := a.tdiv b
  let rem := a.tmod b
  let twiceRem := if quoIsNeg then -(2 * rem) else 2 * rem
  let quoIsOdd := quo.natAbs % 2 = 1
  let fix := (if b < 0 then twiceRem < b else twiceRem > b) ∨ (twiceRem = b ∧ quoIsOdd)
  if fix then
    if quoIsNeg then (quo - 1, rem + b) else (quo + 1, rem - b)
  else (quo, rem)

/-- `round(self, ndigits)` for ints, `int___round___impl`, longobject.c:6207-6267. -/
def roundInt (self : Int) (ndigits : Option Int) : Int :=
  match ndigits with
  | none => self
  | some nd =>
    if nd ≥ 0 then self
    else
      let b : Int := 10 ^ (-nd).toNat
      self - (divmodNear self b).2

end PyLean.MathInt
