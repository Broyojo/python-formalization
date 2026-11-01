import PyLean.Core

/-!
# An exact model of IEEE 754 binary64

This is the shared foundation for every float property in the project. Nothing
here uses Lean's `Float`: a value of `F64` is one of the `2^64` bit patterns, and
every operation is defined as "compute the exact rational result, then round to
nearest, ties to even". All of it runs under `decide +kernel`, and all of it can
be reasoned about (see `PyLean/Binary64/Lemmas.lean`).

## API

Construction and inspection:
* `F64`, `F64.ofBits`, `F64.bits`: the type and its bit patterns.
* `F64.qnan`, `F64.inf s`, `F64.zero s`, `F64.ofInt n`, `F64.ofRat q`.
* `F64.isNaN`, `isInf`, `isFinite`, `isZero`, `sign`, `view`, `toRat`.
* `F64.neg`, `abs`, `copysign` touch only the sign bit, so they keep NaN payloads.

Arithmetic, all correctly rounded: `add sub mul div sqrt fma`, plus the exact
`fmod`.

Comparison: `eq lt le` (`ne gt ge` are derived), with IEEE NaN behaviour.

Integers and scaling: `truncInt floorInt ceilInt`, `trunc floor ceil roundAway`,
`frexp ldexp nextafter ulp`.

`Fmt`, `Fmt.view`, `Fmt.encode` and `roundPos` are the format-generic layer used
for binary32 and binary16 by `struct` packing.

NaN payloads: arithmetic always returns `F64.qnan`. Real hardware propagates an
operand's payload, and Python makes no promise about it, so difftests compare
NaN results only as "is a NaN".
-/

namespace PyLean.Binary64

/-! ## Binary interchange formats -/

/-- A binary interchange format. `p` counts the hidden bit, `emax` is the largest
exponent of a normal number, and `width` is the total number of bits. -/
structure Fmt where
  p : Nat
  emax : Nat
  width : Nat
  deriving DecidableEq, Repr

def binary64 : Fmt := ⟨53, 1023, 64⟩
def binary32 : Fmt := ⟨24, 127, 32⟩
def binary16 : Fmt := ⟨11, 15, 16⟩

/-- Exponent of the least significant bit of a subnormal (`-1074` for binary64). -/
def Fmt.etiny (f : Fmt) : Int := 2 - (f.p : Int) - f.emax

/-- Biased exponent of infinities and NaNs (`2047` for binary64). -/
def Fmt.bexpMax (f : Fmt) : Nat := 2 * f.emax + 1

/-- `⌊log₂ (n / d)⌋`, for `n, d > 0`. `Nat.log2` of each side leaves one candidate
too high at most, and the final test decides. -/
def floorLog2Q (n d : Nat) : Int :=
  let k : Int := (Nat.log2 n : Int) - (Nat.log2 d : Int)
  if d * 2 ^ k.toNat ≤ n * 2 ^ (-k).toNat then k else k - 1

/-- `(q, r, D)` with `n / d = (q + r / D) * 2 ^ e` and `0 ≤ r < D`. -/
def divPow2 (n d : Nat) (e : Int) : Nat × Nat × Nat :=
  let N := n * 2 ^ (-e).toNat
  let D := d * 2 ^ e.toNat
  (N / D, N % D, D)

/-- Round the positive rational `n / d` to the nearest number of format `f`, ties
to even, with gradual underflow. `none` means overflow; `some (m, e)` is the value
`m * 2 ^ e`, where either `2 ^ (p - 1) ≤ m < 2 ^ p`, or `e = etiny` and
`m < 2 ^ (p - 1)` (a subnormal or zero). -/
def roundPos (f : Fmt) (n d : Nat) : Option (Nat × Int) :=
  let k := floorLog2Q n d
  let e : Int := max (k - ((f.p - 1 : Nat) : Int)) f.etiny
  let (q, r, D) := divPow2 n d e
  let up : Bool := decide (D < 2 * r) || (decide (2 * r = D) && q % 2 == 1)
  let q' := if up then q + 1 else q
  let (m, e') : Nat × Int := if q' = 2 ^ f.p then (2 ^ (f.p - 1), e + 1) else (q', e)
  if (f.emax : Int) < e' + ((f.p - 1 : Nat) : Int) then none else some (m, e')

/-- Bit pattern of a rounded result. -/
def Fmt.encode (f : Fmt) (neg : Bool) (r : Option (Nat × Int)) : Nat :=
  let s := if neg then 2 ^ (f.width - 1) else 0
  match r with
  | none => s + f.bexpMax * 2 ^ (f.p - 1)
  | some (m, e) =>
    if m < 2 ^ (f.p - 1) then s + m
    else s + (e + ((f.p - 1 : Nat) : Int) + (f.emax : Int)).toNat * 2 ^ (f.p - 1)
      + (m - 2 ^ (f.p - 1))

/-- What a bit pattern means. A finite number is `±m * 2 ^ e`. -/
inductive View where
  | nan (neg : Bool) (payload : Nat)
  | inf (neg : Bool)
  | finite (neg : Bool) (m : Nat) (e : Int)
  deriving DecidableEq, Repr

def Fmt.view (f : Fmt) (b : Nat) : View :=
  let neg := 2 ^ (f.width - 1) ≤ b % 2 ^ f.width
  let ex := (b / 2 ^ (f.p - 1)) % (f.bexpMax + 1)
  let fr := b % 2 ^ (f.p - 1)
  if ex = f.bexpMax then
    if fr = 0 then .inf neg else .nan neg fr
  else if ex = 0 then .finite neg fr f.etiny
  else .finite neg (2 ^ (f.p - 1) + fr) ((ex : Int) + f.etiny - 1)

/-! ## The type -/

/-- An IEEE 754 binary64 datum: exactly one of the `2 ^ 64` bit patterns, so a
`∀ x : F64` ranges over signed zeros, subnormals, normals, infinities and every
NaN, and nothing else. -/
structure F64 where
  bits : Nat
  isLt : bits < 2 ^ 64
  deriving DecidableEq

instance : Inhabited F64 := ⟨⟨0, by decide⟩⟩

instance : Repr F64 := ⟨fun x _ => "F64.ofBits " ++ repr x.bits⟩

namespace F64

/-- The pattern `n`, reduced modulo `2 ^ 64`. -/
def ofBits (n : Nat) : F64 := ⟨n % 2 ^ 64, Nat.mod_lt _ (by decide)⟩

/-- The sign bit. -/
def sign (x : F64) : Bool := decide (2 ^ 63 ≤ x.bits)

/-- The 11-bit biased exponent. -/
def bexp (x : F64) : Nat := (x.bits / 2 ^ 52) % 2048

/-- The 52-bit fraction. -/
def frac (x : F64) : Nat := x.bits % 2 ^ 52

def view (x : F64) : View := binary64.view x.bits

def isNaN (x : F64) : Bool := x.bexp == 2047 && x.frac != 0
def isInf (x : F64) : Bool := x.bexp == 2047 && x.frac == 0
def isFinite (x : F64) : Bool := x.bexp != 2047
def isZero (x : F64) : Bool := x.bexp == 0 && x.frac == 0

/-- The significand as an integer, hidden bit included. -/
def mant (x : F64) : Nat := if x.bexp = 0 then x.frac else 2 ^ 52 + x.frac

/-- Exponent of the least significant bit. A finite `x` is `± mant x * 2 ^ lsbExp x`. -/
def lsbExp (x : F64) : Int := (max x.bexp 1 : Nat) - 1075

/-- The canonical quiet NaN, `float('nan')`. -/
def qnan : F64 := ofBits 0x7ff8000000000000

def inf (neg : Bool) : F64 := ofBits (if neg then 0xfff0000000000000 else 0x7ff0000000000000)
def zero (neg : Bool) : F64 := ofBits (if neg then 2 ^ 63 else 0)
def one : F64 := ofBits 0x3ff0000000000000

/-- `sys.float_info.max`. -/
def maxFinite : F64 := ofBits 0x7fefffffffffffff

/-- Flip the sign bit. -/
def neg (x : F64) : F64 :=
  ofBits (if 2 ^ 63 ≤ x.bits then x.bits - 2 ^ 63 else x.bits + 2 ^ 63)

/-- Clear the sign bit. -/
def abs (x : F64) : F64 := if x.sign then x.neg else x

/-- `x` with the sign of `y`. -/
def copysign (x y : F64) : F64 := if x.sign == y.sign then x else x.neg

end F64

/-- `m * 2 ^ e` as an exact rational. -/
def dyadic (m : Nat) (e : Int) : Rat :=
  match e with
  | .ofNat k => ((m * 2 ^ k : Nat) : Rat)
  | .negSucc k => mkRat m (2 ^ (k + 1))

namespace F64

/-- The exact value of a finite `x`, sign included (`-0.0` maps to `0`). Infinities
and NaNs map to `0`: test `isFinite` first. -/
def toRat (x : F64) : Rat :=
  if x.isFinite then
    let v := dyadic x.mant x.lsbExp
    if x.sign then -v else v
  else 0

/-- Round a rational to the nearest `F64`, ties to even. A nonzero rational keeps
its sign when it underflows to zero, and `0` becomes `+0.0`. -/
def ofRat (q : Rat) : F64 :=
  if q = 0 then zero false
  else
    let neg := q < 0
    ofBits (binary64.encode neg (roundPos binary64 q.num.natAbs q.den))

/-- `float(n)` with no overflow check: too large an int becomes an infinity. -/
def ofInt (n : Int) : F64 := ofRat n

/-! ## Arithmetic: the exact result, rounded -/

def add (x y : F64) : F64 :=
  if x.isNaN || y.isNaN then qnan
  else if x.isInf then (if y.isInf && x.sign != y.sign then qnan else x)
  else if y.isInf then y
  else
    let q := x.toRat + y.toRat
    if q = 0 then zero (x.sign && y.sign) else ofRat q

def sub (x y : F64) : F64 := add x y.neg

def mul (x y : F64) : F64 :=
  if x.isNaN || y.isNaN then qnan
  else
    let s := x.sign != y.sign
    if x.isInf then (if y.isZero then qnan else inf s)
    else if y.isInf then (if x.isZero then qnan else inf s)
    else
      let q := x.toRat * y.toRat
      if q = 0 then zero s else ofRat q

def div (x y : F64) : F64 :=
  if x.isNaN || y.isNaN then qnan
  else
    let s := x.sign != y.sign
    if x.isInf then (if y.isInf then qnan else inf s)
    else if y.isInf then zero s
    else if y.isZero then (if x.isZero then qnan else inf s)
    else
      let q := x.toRat / y.toRat
      if q = 0 then zero s else ofRat q

/-- `x * y + z` with a single rounding. -/
def fma (x y z : F64) : F64 :=
  if x.isNaN || y.isNaN || z.isNaN then qnan
  else
    let s := x.sign != y.sign
    if x.isInf || y.isInf then
      if x.isZero || y.isZero then qnan
      else if z.isInf && z.sign != s then qnan
      else inf s
    else if z.isInf then z
    else
      let q := x.toRat * y.toRat + z.toRat
      if q = 0 then zero (s && z.sign) else ofRat q

/-- The digit-by-digit integer square root: `r` keeps `r * r ≤ n`, and each step
decides bit `k` of the result. -/
def isqrtGo : Nat → Nat → Nat → Nat
  | 0, _, r => r
  | k + 1, n, r =>
    let c := r + 2 ^ k
    isqrtGo k n (if c * c ≤ n then c else r)

/-- `⌊√n⌋`. -/
def isqrt (n : Nat) : Nat := isqrtGo (n.log2 / 2 + 1) n 0

/-- Round `√(m * 2 ^ e)`. With at least 55 bits in `r`, every number strictly
between `r` and `r + 1` rounds like `r + 1/2`, so an inexact root can stand in for
the unknown irrational value. -/
def sqrtRound (m : Nat) (e : Int) : F64 :=
  let oddE : Bool := e % 2 == 1
  let m' := if oddE then 2 * m else m
  let e' := if oddE then e - 1 else e
  let n := m' * 2 ^ 220
  let r := isqrt n
  let eh : Int := e' / 2 - 110
  if r * r = n then ofRat (dyadic r eh) else ofRat (dyadic (2 * r + 1) (eh - 1))

def sqrt (x : F64) : F64 :=
  if x.isNaN then qnan
  else if x.isZero then x
  else if x.sign then qnan
  else if x.isInf then x
  else sqrtRound x.mant x.lsbExp

/-- C `fmod`: the exact `x - y * trunc (x / y)`, with the sign of `x`. -/
def fmod (x y : F64) : F64 :=
  if x.isNaN || y.isNaN || x.isInf || y.isZero then qnan
  else if y.isInf then x
  else
    let ax := if x.toRat < 0 then -x.toRat else x.toRat
    let ay := if y.toRat < 0 then -y.toRat else y.toRat
    let r := ax - ay * ((ax / ay).floor : Rat)
    if r = 0 then zero x.sign
    else ofRat (if x.sign then -r else r)

/-! ## Comparison -/

def eq (x y : F64) : Bool :=
  if x.isNaN || y.isNaN then false
  else if x.isInf || y.isInf then x.isInf && y.isInf && x.sign == y.sign
  else decide (x.toRat = y.toRat)

def lt (x y : F64) : Bool :=
  if x.isNaN || y.isNaN then false
  else if x.isInf then x.sign && !(y.isInf && y.sign)
  else if y.isInf then !y.sign
  else decide (x.toRat < y.toRat)

def le (x y : F64) : Bool := lt x y || eq x y
def ne (x y : F64) : Bool := !eq x y
def gt (x y : F64) : Bool := lt y x
def ge (x y : F64) : Bool := le y x

/-! ## Integers -/

/-- `⌊x⌋` for finite `x`. -/
def floorInt (x : F64) : Int := x.toRat.floor

/-- `⌈x⌉` for finite `x`. -/
def ceilInt (x : F64) : Int := x.toRat.ceil

/-- `x` rounded toward zero, for finite `x`. -/
def truncInt (x : F64) : Int := if x.sign then x.ceilInt else x.floorInt

/-- Round to an integer-valued float, keeping the sign on a zero result. -/
def ofIntS (neg : Bool) (n : Int) : F64 := if n = 0 then zero neg else ofInt n

def floor (x : F64) : F64 := if x.isNaN then qnan else if !x.isFinite || x.isZero then x else ofIntS x.sign x.floorInt
def ceil (x : F64) : F64 := if x.isNaN then qnan else if !x.isFinite || x.isZero then x else ofIntS x.sign x.ceilInt
def trunc (x : F64) : F64 := if x.isNaN then qnan else if !x.isFinite || x.isZero then x else ofIntS x.sign x.truncInt

/-- C `round`: nearest integer, halfway cases away from zero. -/
def roundAway (x : F64) : F64 :=
  if x.isNaN then qnan
  else if !x.isFinite || x.isZero then x
  else
    let a := if x.sign then -x.toRat else x.toRat
    let n : Int := (a + mkRat 1 2).floor
    ofIntS x.sign (if x.sign then -n else n)

/-- C `frexp`: `x = m * 2 ^ e` with `0.5 ≤ |m| < 1`. Zeros, infinities and NaNs
come back unchanged, with exponent `0`. -/
def frexp (x : F64) : F64 × Int :=
  if !x.isFinite || x.isZero then (x, 0)
  else
    let b := Nat.log2 x.mant + 1
    let v := mkRat x.mant (2 ^ b)
    (ofRat (if x.sign then -v else v), x.lsbExp + b)

/-- C `ldexp`: `x * 2 ^ n`, rounded. Past the guards the result is surely an
infinity or a zero, which keeps `2 ^ n` small. -/
def ldexp (x : F64) (n : Int) : F64 :=
  if !x.isFinite || x.isZero then x
  else if 2200 < n then inf x.sign
  else if n < -2200 then zero x.sign
  else
    let q := x.toRat * dyadic 1 n
    ofRat q

/-- `math.nextafter(x, y)`. -/
def nextafter (x y : F64) : F64 :=
  if x.isNaN || y.isNaN then qnan
  else if eq x y then y
  else if x.isZero then ofBits (if y.sign then 2 ^ 63 + 1 else 1)
  else if lt x y != x.sign then ofBits (x.bits + 1)
  else ofBits (x.bits - 1)

/-- `math.ulp(x)`: the gap between `|x|` and the next float above it. -/
def ulp (x : F64) : F64 :=
  if x.isNaN then qnan
  else if x.isInf then inf false
  else
    let a := x.abs
    if a.bits = 0x7fefffffffffffff then ofBits 0x7ca0000000000000
    else sub (ofBits (a.bits + 1)) a

end F64

end PyLean.Binary64
