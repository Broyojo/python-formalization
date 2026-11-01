/-!
Exact emulation of the two IEEE-754 binary64 operations used by
`TextIOWrapper.tell()` (`Lib/_pyio.py:2357-2359`, `:2420`):
`len(input_chunk) / len(decoded_chars)` (int true division, correctly
rounded) and `int(ratio * chars_to_skip)` (float times int, rounded to
nearest-even, then truncated). Only non-negative finite values occur.
A double is `m * 2^e` with `m < 2^53`.
-/

namespace PyLean.PyIO

structure Dbl where
  m : Nat
  e : Int
  deriving Repr, DecidableEq, Inhabited

def two53 : Nat := 2 ^ 53
def two52 : Nat := 2 ^ 52

/-- `p * 2^(-e)` over `q`, for the scaling exponent `e`. -/
def scaled (p q : Nat) (e : Int) : Nat × Nat :=
  if e ≥ 0 then (p, q * 2 ^ e.toNat) else (p * 2 ^ (-e).toNat, q)

/-- Round `p / (q * 2^e)` to an integer, ties to even. -/
def roundScaled (p q : Nat) (e : Int) : Nat :=
  let (n, d) := scaled p q e
  let t := n / d
  let r := n % d
  if 2 * r > d then t + 1 else if 2 * r = d then (if t % 2 = 1 then t + 1 else t) else t

/-- The double nearest to `p / q` (`q > 0`), ties to even. -/
def roundRat (p q : Nat) : Dbl :=
  if p = 0 then ⟨0, 0⟩ else
  let e0 : Int := (Nat.log2 p : Int) - Nat.log2 q - 52
  -- choose e with 2^52 <= p / (q 2^e) < 2^53
  let fl (e : Int) : Nat := let (n, d) := scaled p q e; n / d
  let e := if fl e0 ≥ two53 then e0 + 1 else if fl e0 < two52 then e0 - 1 else e0
  let m := roundScaled p q e
  if m = two53 then ⟨two52, e + 1⟩ else ⟨m, e⟩

/-- `float(a) / float(b)` for ints (`long_true_divide` is correctly rounded). -/
def dDiv (a b : Nat) : Dbl := if b = 0 then ⟨0, 0⟩ else roundRat a b

/-- `x * c` for a double `x` and an int `c < 2^53`, correctly rounded. -/
def dMulNat (x : Dbl) (c : Nat) : Dbl :=
  if x.e ≥ 0 then roundRat (x.m * c * 2 ^ x.e.toNat) 1
  else roundRat (x.m * c) (2 ^ (-x.e).toNat)

/-- `int(x)` for `x >= 0`. -/
def dTrunc (x : Dbl) : Nat :=
  if x.e ≥ 0 then x.m * 2 ^ x.e.toNat else x.m / 2 ^ (-x.e).toNat

end PyLean.PyIO
