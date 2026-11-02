import PyLean.Bytecode.State

/-!
Numbers for the concrete object model: exact reading of binary64 values, correct
rounding from rationals, `float.__repr__`, and numeric comparison across
`int`/`float`. Everything here is exact `Int`/`Nat` arithmetic on the bit pattern.
-/

namespace PyLean.Bytecode.Num

/-- `(negative, exponent field, mantissa field)`. -/
def fields (b : UInt64) : Bool × Nat × Nat :=
  (b >>> 63 != 0, ((b >>> 52) &&& 0x7FF).toNat, (b &&& 0xFFFFFFFFFFFFF).toNat)

def isNan (b : UInt64) : Bool :=
  let (_, e, m) := fields b
  e == 2047 && m != 0
def isInf (b : UInt64) : Bool :=
  let (_, e, m) := fields b
  e == 2047 && m == 0
def isFinite (b : UInt64) : Bool := let (_, e, _) := fields b; e != 2047

/-- A finite double as `num / 2 ^ den`. -/
def toRat (b : UInt64) : Int × Nat :=
  let (neg, e, m) := fields b
  let (mant, ex) : Nat × Int :=
    if e == 0 then (m, -1074) else (m + 2 ^ 52, (e : Int) - 1075)
  let n : Nat := if ex ≥ 0 then mant * 2 ^ ex.toNat else mant
  let d : Nat := if ex ≥ 0 then 0 else (-ex).toNat
  ((if neg then -(n : Int) else n), d)

/-- The bit pattern of `±(mant * 2^ex)` for `2^52 ≤ mant < 2^53`, with overflow to
infinity and gradual underflow already applied by `ofRat`. -/
def assemble (neg : Bool) (mant : Nat) (ex : Int) : UInt64 :=
  let sign : UInt64 := if neg then 0x8000000000000000 else 0
  let biased := ex + 1075
  if biased ≥ 2047 then sign ||| 0x7FF0000000000000
  else sign ||| (UInt64.ofNat (biased.toNat <<< 52)) ||| UInt64.ofNat (mant - 2 ^ 52)

/-- Round-half-even of `n / 2^k`. -/
def shiftRound (n k : Nat) : Nat :=
  let q := n >>> k
  if k = 0 then q else
    let r := n - (q <<< k)
    let half := 1 <<< (k - 1)
    if r > half || (r == half && q % 2 == 1) then q + 1 else q

/-- The double nearest to `n / d`, ties to even (`n, d > 0`). -/
def ofRatPos (neg : Bool) (n d : Nat) : UInt64 :=
  -- scale so that the integer quotient has at least 66 significant bits
  let lb := Nat.log2 n
  let ld := Nat.log2 d
  let scale : Int := 66 + (ld : Int) - (lb : Int)
  let (num, den) : Nat × Nat :=
    if scale ≥ 0 then (n <<< scale.toNat, d) else (n, d <<< (-scale).toNat)
  let q := num / den
  let sticky := if num % den == 0 then 0 else 1
  let q := (q <<< 1) ||| sticky
  -- value = q * 2^(-scale - 1)
  let bits := Nat.log2 q + 1
  let e := (bits : Int) - 53 - scale - 1
  if e < -1074 then
    -- subnormal range
    let k := (-1074 + scale + 1).toNat
    let m := shiftRound q k
    let sign : UInt64 := if neg then 0x8000000000000000 else 0
    sign ||| UInt64.ofNat m
  else
    let k := bits - 53
    let m := shiftRound q k
    if m == 2 ^ 53 then assemble neg (2 ^ 52) (e + 1) else assemble neg m e

/-- `(double)(n / d)` correctly rounded; `d ≠ 0`. -/
def ofRat (n : Int) (d : Nat) : UInt64 :=
  if n == 0 then 0 else ofRatPos (n < 0) n.natAbs d

def ofInt (i : Int) : UInt64 := ofRat i 1

/-- The nearest double overflowed. -/
def tooLarge (b : UInt64) : Bool := isInf b

/-- `10 ^ k` as a rational pair. -/
def pow10 (k : Int) : Nat × Nat :=
  if k ≥ 0 then (10 ^ k.toNat, 1) else (1, 10 ^ (-k).toNat)

/-- `v` rounded to `p` significant decimal digits (half-even on the exact value):
digits and the decimal exponent of the first digit. `v = n / 2^d > 0`. -/
def sigDigits (n d p : Nat) : Nat × Int :=
  -- find e with 10^e ≤ v < 10^(e+1)
  let approx : Int := ((Nat.log2 n : Int) - d) * 30103 / 100000
  let ge (e : Int) : Bool :=
    let (a, b) := pow10 e
    n * b ≥ a * 2 ^ d
  let rec fix : Nat → Int → Int
    | 0, e => e
    | k + 1, e =>
      if !ge e then fix k (e - 1)
      else if ge (e + 1) then fix k (e + 1)
      else e
  let e := fix 40 approx
  let (a, b) := pow10 (e - (p : Int) + 1)
  -- digits = round(v / 10^(e-p+1)) = round(n * b / (2^d * a))
  let num := n * b
  let den := 2 ^ d * a
  let q := num / den
  let r := num % den
  let q := if 2 * r > den || (2 * r == den && q % 2 == 1) then q + 1 else q
  if q == 10 ^ p then (10 ^ (p - 1), e + 1) else (q, e)

/-- Does `digits * 10^(e-p+1)` read back as `b`? -/
def readsBack (b : UInt64) (digits p : Nat) (e : Int) : Bool :=
  let (a, c) := pow10 (e - (p : Int) + 1)
  ofRat (digits * a) c == b

/-- `repr(float)`: the shortest digit string that round-trips, in the layout of
`float_repr_style = 'short'` (`format_float_short`, decpt in `(-4, 16]`). The nearest string of
`p` digits can miss when the rounding interval is uneven, at a power of two: `2.0 ** -24` is
`5.9604644775390625e-08`, whose nearest 16 digits end in `062` and fall outside the short lower
half of the interval, while `063` reads back. So both neighbours are tried before adding a digit. -/
def repr (b : UInt64) : String :=
  if isNan b then "nan"
  else
    let (neg, _, _) := fields b
    let sign := if neg then "-" else ""
    if isInf b then sign ++ "inf"
    else
      let (n, d) := toRat b
      if n == 0 then sign ++ "0.0"
      else
        let abs := n.natAbs
        let pos := b &&& 0x7FFFFFFFFFFFFFFF
        let rec search : Nat → Nat → Nat × Nat × Int
          | 0, p => let (q, e) := sigDigits abs d p; (q, p, e)
          | k + 1, p =>
            let (q, e) := sigDigits abs d p
            if readsBack pos q p e then (q, p, e)
            else if q + 1 < 10 ^ p && readsBack pos (q + 1) p e then (q + 1, p, e)
            else if 10 ^ (p - 1) < q && readsBack pos (q - 1) p e then (q - 1, p, e)
            else search k (p + 1)
        let (q, p, e) := search 16 1
        -- strip trailing zeros
        let rec strip : Nat → Nat → Nat → Nat × Nat
          | 0, q, p => (q, p)
          | k + 1, q, p => if q % 10 == 0 && p > 1 then strip k (q / 10) (p - 1) else (q, p)
        let (q, p) := strip 17 q p
        let ds := toString q
        let decpt := e + 1
        if -4 < decpt && decpt ≤ 16 then
          if decpt ≤ 0 then
            sign ++ "0." ++ String.ofList (List.replicate (-decpt).toNat '0') ++ ds
          else if decpt.toNat ≥ p then
            sign ++ ds ++ String.ofList (List.replicate (decpt.toNat - p) '0') ++ ".0"
          else
            let cs := ds.toList
            sign ++ String.ofList (cs.take decpt.toNat) ++ "." ++ String.ofList (cs.drop decpt.toNat)
        else
          let cs := ds.toList
          let mant := if p == 1 then ds
            else String.ofList (cs.take 1) ++ "." ++ String.ofList (cs.drop 1)
          let ex := decpt - 1
          let exs := toString ex.natAbs
          let exs := if exs.length < 2 then "0" ++ exs else exs
          sign ++ mant ++ "e" ++ (if ex < 0 then "-" else "+") ++ exs

/-- Three-way comparison of a finite double and an int; exact. -/
def cmpFloatInt (b : UInt64) (i : Int) : Ordering :=
  let (n, d) := toRat b
  compare n (i * (2 : Int) ^ d)

/-- `float.is_integer` and the value. -/
def toIntExact? (b : UInt64) : Option Int :=
  if !isFinite b then none
  else
    let (n, d) := toRat b
    let p : Int := (2 : Int) ^ d
    if n % p == 0 then some (n / p) else none

end PyLean.Bytecode.Num
