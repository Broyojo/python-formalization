import PyLean.CoreLibs.Rand.Gen

/-!
Lean's `Float` as a `Flt`, for the difftest only (proofs cannot reduce `Float`).
Everything Python computes exactly is computed exactly here, on the IEEE bits:
`float(int)`, literals, `floor`, comparison with an `int`, `fmod`.
-/

namespace PyLean.CoreLibs.Rand.FloatInst

open PyLean

/-- `|x| = m * 2 ^ e` for finite `x`, with the sign. -/
def decode (x : Float) : Bool × Nat × Int :=
  let bits := x.toBits.toNat
  let neg := (bits >>> 63) == 1
  let ex := (bits >>> 52) &&& 0x7ff
  let frac := bits &&& (2 ^ 52 - 1)
  if ex == 0 then (neg, frac, -1074) else (neg, frac + 2 ^ 52, (ex : Int) - 1075)

/-- `x` is finite. -/
def finite (x : Float) : Bool := ((x.toBits.toNat >>> 52) &&& 0x7ff) != 0x7ff

/-- Bits of `q * 2 ^ e`, for `2^52 ≤ q < 2^53` in the normal range. -/
def encodeNormal (neg : Bool) (q : Nat) (e : Int) : Option Float :=
  let biased := e + 1075
  if biased ≥ 2047 then none
  else if biased ≤ 0 then some 0.0
  else
    let bits := (if neg then 2 ^ 63 else 0) + (biased.toNat <<< 52) + (q - 2 ^ 52)
    some (Float.ofBits bits.toUInt64)

/-- `m * 2 ^ e` rounded half-even to 53 bits, as `_PyLong_Frexp` and `strtod` do.
`none` on overflow. Results in the subnormal range are not needed here. -/
def roundNat (neg : Bool) (m : Nat) (e : Int) : Option Float :=
  if m = 0 then some (if neg then -0.0 else 0.0)
  else
    let b := Nat.log2 m + 1
    if b ≤ 53 then
      encodeNormal neg (m <<< (53 - b)) (e - ((53 - b : Nat) : Int))
    else
      let shift := b - 53
      let q := m >>> shift
      let r := m % 2 ^ shift
      let half := 2 ^ (shift - 1)
      let q := if r > half ∨ (r = half ∧ q % 2 = 1) then q + 1 else q
      if q = 2 ^ 53 then encodeNormal neg (2 ^ 52) (e + (shift : Int) + 1)
      else encodeNormal neg q (e + (shift : Int))

/-- A decimal literal, correctly rounded: `m * 10 ^ e` or `m / 10 ^ e`. -/
def ofDecimal (mantissa : Nat) (exponentSign : Bool) (decimalExponent : Nat) : Float :=
  if exponentSign then
    let d := 10 ^ decimalExponent
    let s := 64 + (Nat.log2 d + 1)
    let q := (mantissa <<< s) / d
    let r := (mantissa <<< s) % d
    (roundNat false (q * 2 + (if r = 0 then 0 else 1)) (-(s : Int) - 1)).getD 0.0
  else (roundNat false (mantissa * 10 ^ decimalExponent) 0).getD 0.0

/-- `floor(x)` for finite `x`. -/
def floorInt (x : Float) : Int :=
  let (neg, m, e) := decode x
  let v : Int := if neg then -(m : Int) else m
  if e ≥ 0 then v * (2 ^ e.toNat : Nat) else v / (2 ^ (-e).toNat : Nat)

/-- `x < n` for an `int` `n`, exactly. -/
def ltInt (x : Float) (n : Int) : Bool :=
  if x != x then false
  else if !finite x then x < 0.0
  else
    let (neg, m, e) := decode x
    let v : Int := if neg then -(m : Int) else m
    if e ≥ 0 then decide (v * (2 ^ e.toNat : Nat) < n) else decide (v < n * (2 ^ (-e).toNat : Nat))

/-- An exactly representable `m * 2 ^ e`, including the subnormal range. -/
def encodeExact (neg : Bool) (m : Nat) (e : Int) : Float :=
  if m = 0 then (if neg then -0.0 else 0.0)
  else
    let b := Nat.log2 m + 1
    if e + (b : Int) - 53 ≥ -1074 then (roundNat neg m e).getD 0.0
    else
      let frac := m <<< (e + 1074).toNat
      Float.ofBits ((if neg then 2 ^ 63 else 0) + frac).toUInt64

/-- C `fmod`. -/
def fmod (x y : Float) : Float :=
  if x != x || y != y || !finite x || y == 0.0 then 0.0 / 0.0
  else if !finite y then x
  else
    let (nx, mx, ex) := decode x
    let (_, my, ey) := decode y
    let e := min ex ey
    let a := mx <<< (ex - e).toNat
    let b := my <<< (ey - e).toNat
    encodeExact nx (a % b) e

/-- `DOUBLE_IS_ODD_INTEGER`. -/
def isOdd (x : Float) : Bool :=
  finite x && x == x.floor && (floorInt x) % 2 = 1

/-- `copysign(0.0, x)`. -/
def zeroLike (x : Float) : Float :=
  if (x.toBits.toNat >>> 63) == 1 then -0.0 else 0.0

/-- `lanczos_num_coeffs`, Modules/mathmodule.c:318-332. -/
def lanczosNum : List Float := [
  ofDecimal 23531376880410759688572007674451636754734846804940 true 39,
  ofDecimal 42919803642649098768957899047001988850926355848959 true 39,
  ofDecimal 35711959237355668049440185451547166705960488635843 true 39,
  ofDecimal 17921034426037209699919755754458931112671403265390 true 39,
  ofDecimal 60395425863520280050642916443072979210699388420708 true 40,
  ofDecimal 14397204073117216736632230727949123939715485786772 true 40,
  ofDecimal 24887455786205415651146038641322942321632125127801 true 41,
  ofDecimal 31426415585400194380614231628318205362874684987640 true 42,
  ofDecimal 28763706289353724412254090516208496135991145378768 true 43,
  ofDecimal 18605626539522349504029498971604569928220784236328 true 44,
  ofDecimal 80716720023658162106380029022722506138218516325024 true 46,
  ofDecimal 21082427775157934587250973392071336271166969580291 true 47,
  ofDecimal 25066282746310002701649081771338373386264310793408 true 49]

/-- `lanczos_den_coeffs`, Modules/mathmodule.c:335-337. -/
def lanczosDen : List Float :=
  [0.0, 39916800.0, 120543840.0, 150917976.0, 105258076.0, 45995730.0,
   13339535.0, 2637558.0, 357423.0, 32670.0, 1925.0, 66.0, 1.0]

/-- `lanczos_g`, Modules/mathmodule.c:316. -/
def lanczosG : Float := ofDecimal 6024680040776729583740234375 true 27

/-- `lanczos_sum`, Modules/mathmodule.c:351-379. -/
def lanczosSum (x : Float) : Float :=
  let pairs := lanczosNum.zip lanczosDen
  if x < 5.0 then
    let (n, d) := pairs.reverse.foldl (fun (acc : Float × Float) (c : Float × Float) =>
      (acc.1 * x + c.1, acc.2 * x + c.2)) (0.0, 0.0)
    n / d
  else
    let (n, d) := pairs.foldl (fun (acc : Float × Float) (c : Float × Float) =>
      (acc.1 / x + c.1, acc.2 / x + c.2)) (0.0, 0.0)
    n / d

/-- `m_lgamma` for finite `x > 0`, Modules/mathmodule.c:483-524. `Lib/random.py`
only calls it on `m + 1`, `n - m + 1`, `k + 1`, `n - k + 1`, all at least 1. -/
def lgamma (x : Float) : Float :=
  if x == x.floor && x ≤ 2.0 then 0.0
  else
    let absx := x.abs
    if absx < 1e-20 then -(Float.log absx)
    else
      let r := Float.log (lanczosSum absx) - lanczosG
      r + (absx - 0.5) * (Float.log (absx + lanczosG - 0.5) - 1.0)

instance : Flt Float where
  ofScientific := ofDecimal
  add := Float.add
  sub := Float.sub
  mul := Float.mul
  div := Float.div
  neg := Float.neg
  lt a b := a < b
  le a b := a ≤ b
  beq a b := a == b
  isNan x := x != x
  isInf x := x == x && !finite x
  sqrt := Float.sqrt
  log := Float.log
  log2 := Float.log2
  exp := Float.exp
  sin := Float.sin
  cos := Float.cos
  acos := Float.acos
  pow := Float.pow
  fabs := Float.abs
  fmod := fmod
  lgamma := lgamma
  floorInt := floorInt
  ofInt n := roundNat (n < 0) n.natAbs 0
  ltInt := ltInt
  isInteger x := finite x && x == x.floor
  isOddInteger := isOdd
  zeroLike := zeroLike

end PyLean.CoreLibs.Rand.FloatInst
