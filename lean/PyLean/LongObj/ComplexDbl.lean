import PyLean.LongObj.ComplexCore

/-!
Exact IEEE-754 binary64, as an instance of `CDouble`.

A double is its 64-bit pattern. Finite values are read exactly, as an integer
multiple of `2^-1074`, operated on with `Nat`, and rounded to nearest-even in
one place (`roundQ`), so `+ - * /` here are the IEEE operations. The kernel can
evaluate all of this, which is why a refutation over `Dbl` is a `decide`.

NaN handling copies x86-64 SSE, the platform the differential test runs on: an
operation with a NaN operand returns that operand (the first one, if both are),
and an invalid operation returns the default NaN, whose sign bit is set. The
sign of a NaN is visible only through `copysign`, on lines 103-137 and 230-239.

This is deliberately small, and exists only to run `complexobject.c`; it is not
a replacement for the `Binary64` model. It has no proof about rounding, so
universally quantified float properties stay open.
-/

namespace PyLean.LongObj.Cplx

/-- A binary64 value: its bit pattern, below `2^64`. -/
structure Dbl where
  bits : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Dbl

def expMask : Nat := 0x7ff
def fracMask : Nat := 2 ^ 52 - 1
def signBit : Nat := 2 ^ 63

def sign (x : Dbl) : Bool := x.bits ≥ signBit
def expo (x : Dbl) : Nat := (x.bits >>> 52) &&& expMask
def frac (x : Dbl) : Nat := x.bits &&& fracMask

def isNaN (x : Dbl) : Bool := x.expo == expMask && x.frac != 0
def isInf (x : Dbl) : Bool := x.expo == expMask && x.frac == 0

/-- The magnitude of a finite value, as a multiple of `2^-1074`. -/
def mag (x : Dbl) : Nat :=
  if x.expo == 0 then x.frac else (x.frac + 2 ^ 52) <<< (x.expo - 1)

def ofSign (neg : Bool) (mag : Nat) : Dbl := ⟨if neg then mag + signBit else mag⟩

def pinf : Dbl := ⟨expMask <<< 52⟩
def ninf : Dbl := ⟨(expMask <<< 52) + signBit⟩
/-- `Py_NAN`: the quiet NaN with a clear sign bit. -/
def qnan : Dbl := ⟨(expMask <<< 52) + 2 ^ 51⟩
/-- The x86 default NaN, produced by invalid operations. -/
def defaultNaN : Dbl := ⟨(expMask <<< 52) + 2 ^ 51 + signBit⟩

def infOf (neg : Bool) : Dbl := if neg then ninf else pinf
def zeroOf (neg : Bool) : Dbl := ofSign neg 0

/-- `|num/den|` rounded to binary64 with sign `neg`, ties to even.
`den` is positive; `num = 0` gives a zero of sign `neg`. -/
def roundQ (neg : Bool) (num den : Nat) : Dbl :=
  if num == 0 then zeroOf neg else
  let l : Int := (Nat.log2 num : Int) - (Nat.log2 den : Int)
  let scaled (e : Int) : Nat × Nat :=
    if e ≥ 0 then (num, den <<< e.toNat) else (num <<< (-e).toNat, den)
  let e₀ : Int := max (l - 53) (-1074)
  let (n₀, d₀) := scaled e₀
  let q₀ := n₀ / d₀
  let e₁ : Int := if q₀ ≥ 2 ^ 53 then e₀ + 1 else e₀
  let (n, d) := scaled e₁
  let q := n / d
  let r := n % d
  let up := 2 * r > d || (2 * r == d && q % 2 == 1)
  let q' := if up then q + 1 else q
  let (q', e') : Nat × Int := if q' == 2 ^ 53 then (2 ^ 52, e₁ + 1) else (q', e₁)
  if e' > 971 then infOf neg
  else if q' < 2 ^ 52 then ofSign neg q'
  else ofSign neg ((((e' + 1075).toNat) <<< 52) + (q' - 2 ^ 52))

/-- Signed magnitude of a finite value, in units of `2^-1074`. -/
def sval (x : Dbl) : Int := if x.sign then -(x.mag : Int) else x.mag

/-- IEEE addition. An exact zero sum takes the sign of the operands if they
agree and is positive otherwise. -/
def add (x y : Dbl) : Dbl :=
  if x.isNaN then x else if y.isNaN then y
  else if x.isInf then
    if y.isInf && x.sign != y.sign then defaultNaN else x
  else if y.isInf then y
  else
    let s := x.sval + y.sval
    if s == 0 then zeroOf (x.sign && y.sign)
    else roundQ (s < 0) s.natAbs (2 ^ 1074)

def neg (x : Dbl) : Dbl :=
  ⟨if x.sign then x.bits - signBit else x.bits + signBit⟩

def sub (x y : Dbl) : Dbl :=
  if x.isNaN then x else if y.isNaN then y else add x (neg y)

/-- IEEE multiplication. -/
def mul (x y : Dbl) : Dbl :=
  let s := x.sign != y.sign
  if x.isNaN then x else if y.isNaN then y
  else if x.isInf || y.isInf then
    if (!x.isInf && x.mag == 0) || (!y.isInf && y.mag == 0) then defaultNaN
    else infOf s
  else roundQ s (x.mag * y.mag) (2 ^ 2148)

/-- IEEE division. -/
def div (x y : Dbl) : Dbl :=
  let s := x.sign != y.sign
  if x.isNaN then x else if y.isNaN then y
  else if x.isInf then
    if y.isInf then defaultNaN else infOf s
  else if y.isInf then zeroOf s
  else if y.mag == 0 then
    if x.mag == 0 then defaultNaN else infOf s
  else roundQ s x.mag y.mag

/-- C `==`. -/
def beq' (x y : Dbl) : Bool :=
  if x.isNaN || y.isNaN then false
  else if x.isInf || y.isInf then x.bits == y.bits
  else x.sval == y.sval

/-- C `<`. -/
def blt (x y : Dbl) : Bool :=
  if x.isNaN || y.isNaN then false
  else if x.isInf then x.sign && !(y.isInf && y.sign)
  else if y.isInf then !y.sign
  else x.sval < y.sval

def copysign (x y : Dbl) : Dbl := if x.sign == y.sign then x else neg x

def fabs (x : Dbl) : Dbl := if x.sign then neg x else x

/-- `n` as a `Dbl` with sign `neg`. -/
def ofNat' (neg : Bool) (n : Nat) : Dbl := roundQ neg n 1

/-- C `floor`. -/
def floor (x : Dbl) : Dbl :=
  if x.isNaN || x.isInf || x.mag == 0 then x
  else
    let units := 2 ^ 1074
    let q := x.mag / units
    if x.mag % units == 0 then x
    else if x.sign then ofNat' true (q + 1)
    else if q == 0 then zeroOf false
    else ofNat' false q

/-- `(long)x`: truncation toward zero. -/
def toLong (x : Dbl) : Int :=
  let q : Int := x.mag / 2 ^ 1074
  if x.sign then -q else q

/-- `PyLong_AsDouble`, `Objects/longobject.c:3484-3513`: round to nearest-even,
and report overflow if the rounded value does not fit. -/
def ofInt (n : Int) : Option Dbl :=
  let r := ofNat' (n < 0) n.natAbs
  if r.isInf then none else some r

/-- `float == int`, exact, as `float_richcompare` (`Objects/floatobject.c:382-542`)
decides it. An infinity or NaN equals no int. -/
def eqInt (x : Dbl) (n : Int) : Bool :=
  if x.isNaN || x.isInf then false else x.sval == n * 2 ^ 1074

instance : CDouble Dbl where
  zero := ⟨0⟩
  one := ofNat' false 1
  hundred := ofNat' false 100
  inf := pinf
  nan := qnan
  add := add
  sub := sub
  mul := mul
  div := div
  neg := neg
  eq := beq'
  lt := blt
  isnan := isNaN
  isinf := isInf
  copysign := copysign
  fabs := fabs
  floor := floor
  toLong := toLong
  ofInt := ofInt
  eqInt := eqInt

/-! ## `strtod` -/

private def isDigit (c : Nat) : Bool := 48 ≤ c && c ≤ 57

/-- Leading digits of `s`, with the count. Structural on `s`, so no fuel. -/
def scanDigits : List Nat → Nat → Nat → Nat × Nat
  | c :: rest, acc, n =>
    if isDigit c then scanDigits rest (acc * 10 + (c - 48)) (n + 1) else (acc, n)
  | [], acc, n => (acc, n)

/-- The decimal value `digits × 10^e`, correctly rounded. Huge exponents are
clamped first: `log2 digits` bounds the magnitude from both sides, so anything
beyond the clamps is an overflow or an underflow to zero, as in `_Py_dg_strtod`.
Leading zeros do not count, since they do not change `digits`. -/
def decToDbl (neg : Bool) (digits : Nat) (e : Int) : Dbl :=
  let l : Int := Nat.log2 digits
  if digits == 0 then zeroOf neg
  else if e + l * 3 / 10 > 400 then infOf neg
  else if e + (l + 1) * 31 / 100 + 1 < -400 then zeroOf neg
  else if e ≥ 0 then roundQ neg (digits * 10 ^ e.toNat) 1
  else roundQ neg digits (10 ^ (-e).toNat)

private def lower (c : Nat) : Nat := if 65 ≤ c && c ≤ 90 then c + 32 else c

/-- `case_insensitive_match`, `Python/pystrtod.c:13-20`. -/
def ciPrefix : List Nat → List Nat → Bool
  | _, [] => true
  | [], _ :: _ => false
  | c :: s, w :: ws => lower c == w && ciPrefix s ws

private def lit (s : String) : List Nat := s.toList.map Char.toNat

/-- `_Py_parse_inf_or_nan`, `Python/pystrtod.c:28-58`. -/
def parseInfNan (p : List Nat) : Dbl × Nat :=
  let (negate, s, off) : Bool × List Nat × Nat :=
    match p with
    | 45 :: t => (true, t, 1)
    | 43 :: t => (false, t, 1)
    | _ => (false, p, 0)
  if ciPrefix s (lit "inf") then
    let n := if ciPrefix (s.drop 3) (lit "inity") then 8 else 3
    (infOf negate, off + n)
  else if ciPrefix s (lit "nan") then
    ((if negate then ⟨qnan.bits + signBit⟩ else qnan), off + 3)
  else (⟨0⟩, 0)

/-- `_Py_dg_strtod`, `Python/dtoa.c:1386`, through the end of parsing, with the
conversion done exactly. Returns the value and the characters consumed; `0`
means `se == s00`. -/
def dgStrtod (p : List Nat) : Dbl × Nat :=
  let (negS, s, off₀) : Bool × List Nat × Nat :=
    match p with
    | 45 :: t => (true, t, 1)
    | 43 :: t => (false, t, 1)
    | _ => (false, p, 0)
  let (ip, ni) := scanDigits s 0 0
  let rest := s.drop ni
  let (fp, nf, hasDot) : Nat × Nat × Bool :=
    match rest with
    | 46 :: t => let (f, n) := scanDigits t 0 0; (f, n, true)
    | _ => (0, 0, false)
  if ni + nf == 0 then (⟨0⟩, 0) else
  let consumed := off₀ + ni + (if hasDot then 1 + nf else 0)
  let afterMant := s.drop (ni + (if hasDot then 1 + nf else 0))
  let (e, expLen) : Int × Nat :=
    match afterMant with
    | c :: t =>
      if c == 101 || c == 69 then
        let (esign, t', sl) : Bool × List Nat × Nat :=
          match t with
          | 45 :: u => (true, u, 1)
          | 43 :: u => (false, u, 1)
          | _ => (false, t, 0)
        let (v, n) := scanDigits t' 0 0
        if n == 0 then (0, 0)
        else ((if esign then -(min v 2000000000 : Int) else (min v 2000000000 : Int)), 1 + sl + n)
      else (0, 0)
    | [] => (0, 0)
  let digits := ip * 10 ^ nf + fp
  (decToDbl negS digits (e - (nf : Int)), consumed + expLen)

/-- `_PyOS_ascii_strtod`, `Python/pystrtod.c:93-113`. -/
def asciiStrtod (p : List Nat) : Dbl × Nat :=
  let r := dgStrtod p
  if r.2 == 0 then parseInfNan p else r

/-! ## `repr` -/

private def natDigits (n : Nat) : List Nat := (toString n).toList.map (fun c => c.toNat - 48)

/-- `|x|` rounded to `p` significant decimal digits: the digit integer and the
decimal point position. `up` picks the upward neighbour instead of the nearest. -/
private def sigDigits (m : Nat) (p : Nat) (dir : Int) : Nat × Int :=
  -- value is m / 2^1074; find k with 10^(p-1) <= value*10^k < 10^p
  let num := m
  let den := 2 ^ 1074
  let lg := ((Nat.log2 m : Int) - 1074) * 30103 / 100000
  let k₀ : Int := (p : Int) - 1 - lg
  let frac (k : Int) : Nat × Nat :=
    if k ≥ 0 then (num * 10 ^ k.toNat, den) else (num, den * 10 ^ (-k).toNat)
  let fix (k : Int) : Int :=
    let (a, b) := frac k
    let q := a / b
    if q ≥ 10 ^ p then k - 1 else if q < 10 ^ (p - 1) then k + 1 else k
  let k := fix (fix (fix k₀))
  let (a, b) := frac k
  let q := a / b
  let r := a % b
  let q' :=
    if dir < 0 then q else if dir > 0 then (if r == 0 then q else q + 1)
    else if 2 * r > b || (2 * r == b && q % 2 == 1) then q + 1 else q
  (q', k)

/-- `q / 10^k` as a `Dbl`. -/
private def decOf (q : Nat) (k : Int) : Dbl :=
  if k ≥ 0 then roundQ false q (10 ^ k.toNat) else roundQ false (q * 10 ^ (-k).toNat) 1

/-- The shortest digits that read back as the positive finite `x`, closest to
`x` among those: David Gay's mode 0. Returns the digits and `decpt`. -/
def shortest (x : Dbl) : List Nat × Int :=
  let m := x.mag
  let target := (fabs x).bits
  let attempt (p : Nat) : Option (Nat × Int) :=
    let cand : List (Nat × Int) :=
      [sigDigits m p 0, sigDigits m p (-1), sigDigits m p 1]
    cand.find? (fun ck => (decOf ck.1 ck.2).bits == target)
  let rec go : Nat → Nat → Nat × Int
    | 0, p => sigDigits m p 0
    | fuel + 1, p =>
      match attempt p with
      | some r => r
      | none => go fuel (p + 1)
  let (q, k) := go 16 1
  let ds := natDigits q
  -- strip trailing zeros
  let trimmed := (ds.reverse.dropWhile (· == 0)).reverse
  (trimmed, (ds.length : Int) - k)

private def digitStr (ds : List Nat) : String :=
  String.ofList (ds.map (fun d => Char.ofNat (d + 48)))

/-- `PyOS_double_to_string(x, 'r', 0, flags, NULL)`, with `Py_DTSF_SIGN` when
`alwaysSign` and without `Py_DTSF_ADD_DOT_0`: `format_float_short`,
`Python/pystrtod.c`. -/
def dblToString (x : Dbl) (alwaysSign : Bool) : String :=
  if x.isNaN then (if alwaysSign then "+nan" else "nan") else
  let signStr := if x.sign then "-" else if alwaysSign then "+" else ""
  if x.isInf then signStr ++ "inf" else
  if x.mag == 0 then signStr ++ "0" else
  let (ds, decpt) := shortest x
  let n : Int := ds.length
  let useExp := decpt ≤ -4 || decpt > 16
  if useExp then
    let e := decpt - 1
    let first := digitStr (ds.take 1)
    let more := digitStr (ds.drop 1)
    let mant := if more.isEmpty then first else first ++ "." ++ more
    let ea := e.natAbs
    let es := (if ea < 10 then "0" else "") ++ toString ea
    signStr ++ mant ++ "e" ++ (if e < 0 then "-" else "+") ++ es
  else if decpt ≤ 0 then
    signStr ++ "0." ++ String.ofList (List.replicate (-decpt).toNat '0') ++ digitStr ds
  else if decpt ≥ n then
    signStr ++ digitStr ds ++ String.ofList (List.replicate (decpt - n).toNat '0')
  else
    signStr ++ digitStr (ds.take decpt.toNat) ++ "." ++ digitStr (ds.drop decpt.toNat)

/-! ## `_Py_HashDouble` for finite values and infinities -/

def hashModulus : Nat := 2 ^ 61 - 1

/-- `_Py_HashDouble`, `Python/pyhash.c:87-130`, for non-NaN `x`, by its closed
form (the loop computes the value modulo the prime `2^61 - 1`). The result is a
signed `Py_hash_t`. -/
def hashFinite (x : Dbl) : Int :=
  if x.isInf then (if x.sign then -314159 else 314159)
  else
    -- x = mag * 2^-1074; 2^-1074 == 2^(61 - 1074 % 61) modulo the prime
    let e := (61 - 1074 % 61) % 61
    let h : Nat := (x.mag % hashModulus) * 2 ^ e % hashModulus
    let s : Int := if x.sign then -(h : Int) else h
    if s == -1 then -2 else s

end Dbl

end PyLean.LongObj.Cplx
