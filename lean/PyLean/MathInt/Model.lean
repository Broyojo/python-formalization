import PyLean.Core
import PyLean.MathInt.Tables

/-!
Model of the integer functions of `Modules/mathmodule.c` (CPython 3.14.7; the
same code lives in `Modules/mathintegermodule.c` on main): `isqrt`, `comb`,
`perm`, `factorial`, `gcd`, `lcm`, and `_PyLong_GCD` from
`Objects/longobject.c`.

Build assumptions (macOS arm64/x86-64, the interpreter we test against):
`long` and `long long` are 64 bits (`LONG_MAX = LLONG_MAX = 2^63 - 1`) and
`PyLong_SHIFT = 30`.

C unsigned arithmetic is modelled on `Nat` with explicit reduction
(`u64`, `u32`); signed `stwodigits` arithmetic on `Int`, with a check that
reports any `int64_t` overflow (undefined behaviour in C) as the outcome
`PyExc.named "CUndefinedBehavior"`, which is never a Python outcome.
-/

namespace PyLean.MathInt

open PyLean

/-! ## C integer helpers -/

/-- Reduction modulo `2^64`: the value of a `uint64_t` / `unsigned long long`
/ `unsigned long` expression. -/
def u64 (x : Nat) : Nat := x % 2 ^ 64
/-- Reduction modulo `2^32`: the value of a `uint32_t` expression. -/
def u32 (x : Nat) : Nat := x % 2 ^ 32

/-- `LONG_MAX` and `LLONG_MAX` on LP64. -/
def llongMax : Nat := 2 ^ 63 - 1

/-- `PyLong_SHIFT`. -/
def shiftBits : Nat := 30

/-- `_PyLong_DigitCount(v)` for `|v| = n`: number of 30-bit digits. -/
def digitCount (n : Nat) : Nat := (bitLength n + 29) / 30

/-- An `int64_t` (`stwodigits`) intermediate is in range. -/
def inI64 (x : Int) : Bool := -(2 ^ 63 : Int) ≤ x && x < 2 ^ 63

def ubError : PyExc := .named "CUndefinedBehavior" "~int64_t overflow"

/-- Python's `x // y` and `x % y` (floor division), with `y ≠ 0`. -/
def floorDiv (x y : Int) : Int := Int.fdiv x y
def floorMod (x y : Int) : Int := Int.fmod x y

/-! ## `math.isqrt`, mathmodule.c:1676-1821 -/

/-- `_approximate_isqrt`, mathmodule.c:1676-1681. The caller guarantees
`2^62 <= n < 2^64`; `u` is `uint32_t`. -/
def approxIsqrt (n : Nat) : Nat :=
  let u := isqrtTab.getD ((n >>> 56) - 64) 0
  let u := u32 (u32 (u <<< 7) + u32 (n >>> 41) / u)
  u32 (u32 (u <<< 15) + u32 ((n >>> 17) / u))

/-- The `c_bit_length` loop, mathmodule.c:1745-1748: starting from `k`,
increment while `c >> k > 0`. -/
def cBitLength (c : Nat) : Nat → Nat → Nat
  | 0, k => k
  | fuel + 1, k => if c >>> k > 0 then cBitLength c fuel (k + 1) else k

/-- The Newton loop of the slow path, mathmodule.c:1764-1791, run for
`s = iters - 1, ..., 0`. -/
def isqrtLoop (n c : Nat) : Nat → Nat → Nat → Nat
  | 0, _, a => a
  | s + 1, d, a =>
    let e := d
    let d := c >>> s
    let q := (n >>> (2 * c - d - e + 1)) / a
    let a := (a <<< (d - 1 - e)) + q
    isqrtLoop n c s d a

/-- `math.isqrt(n)` for an int `n`, mathmodule.c:1693-1821. -/
def isqrt (n : Int) : Py Nat :=
  if n < 0 then .error (.valueError "isqrt() argument must be nonnegative")
  else if n = 0 then .ok 0
  else
    let n := n.toNat
    let c := (bitLength n - 1) / 2
    if c ≤ 31 then
      -- fast path, :1723-1735
      let shift := 31 - c
      let m := n
      let u := approxIsqrt (u64 (m <<< (2 * shift))) >>> shift
      let u := if u * u > m then u - 1 else u
      .ok u
    else
      -- slow path, :1740-1820
      let cbl := cBitLength c 64 6
      let d := c >>> (cbl - 5)
      let b := n >>> (2 * c - 62)
      if b ≥ 2 ^ 64 then
        .error (.overflowError "int too big to convert")
      else
        let u := approxIsqrt b >>> (31 - d)
        let a := isqrtLoop n c (cbl - 6 + 1) d u
        .ok (if n < a * a then a - 1 else a)

/-! ## `math.comb` and `math.perm`, mathmodule.c:3557-3933 -/

/-- The loop `for (i = 1; i < k;) { result *= --n; result /= ++i; }`,
mathmodule.c:3603-3607 (`iscomb`), or without the division (:3630-3634).
`rem` counts the iterations left. -/
def smallLoop (iscomb : Bool) : Nat → Nat → Nat → Nat → Nat
  | 0, result, _, _ => result
  | rem + 1, result, n, i =>
    let n := u64 (n + 2 ^ 64 - 1)
    let result := u64 (result * n)
    let i := i + 1
    let result := if iscomb then result / i else result
    smallLoop iscomb rem result n i

/-- The fast paths of `perm_comb_small`, mathmodule.c:3563-3637: `some r` when
one of them applies. -/
def permCombFast (n k : Nat) (iscomb : Bool) : Option Nat :=
  if iscomb then
    if k < fastCombLimits1.length ∧ n ≤ fastCombLimits1.getD k 0 then
      let odd := u64 (u64 (reducedFactorialOddPart.getD n 0 * invertedFactorialOddPart.getD k 0)
        * invertedFactorialOddPart.getD (n - k) 0)
      let shift : Int := (factorialTrailingZeros.getD n 0 : Int)
        - factorialTrailingZeros.getD k 0 - factorialTrailingZeros.getD (n - k) 0
      some (u64 (odd <<< shift.toNat))
    else if k < fastCombLimits2.length ∧ n ≤ fastCombLimits2.getD k 0 then
      some (smallLoop true (k - 1) n n 1)
    else none
  else
    if k < fastPermLimits.length ∧ n ≤ fastPermLimits.getD k 0 then
      if n ≤ 127 then
        let odd := u64 (reducedFactorialOddPart.getD n 0 * invertedFactorialOddPart.getD (n - k) 0)
        let shift : Int := (factorialTrailingZeros.getD n 0 : Int)
          - factorialTrailingZeros.getD (n - k) 0
        some (u64 (odd <<< shift.toNat))
      else some (smallLoop false (k - 1) n n 1)
    else none

/-- `perm_comb_small(n, k, iscomb)`, mathmodule.c:3557-3669, for `n` and `k`
of type `unsigned long long`. `fuel` bounds the recursion depth. -/
def permCombSmall : Nat → Nat → Nat → Bool → Py Nat
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, n, k, iscomb =>
    match permCombFast n k iscomb with
    | some r => .ok r
    | none => do
      let j := k / 2
      let a ← permCombSmall fuel n j iscomb
      let b ← permCombSmall fuel (n - j) (k - j) iscomb
      let a := a * b
      if iscomb then
        let b ← permCombSmall fuel k j true
        return a / b
      else return a

/-- `perm_comb(n, k, iscomb)`, mathmodule.c:3676-3722, for a Python int `n`
and `unsigned long long k`. -/
def permComb : Nat → Nat → Nat → Bool → Py Nat
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, n, k, iscomb =>
    if k = 0 then .ok 1
    else if k = 1 then .ok n
    else do
      let j := k / 2
      let a ← permComb fuel n j iscomb
      let n := n - j
      let b ← permComb fuel n (k - j) iscomb
      let a := a * b
      if iscomb then
        let b ← permCombSmall (k + 1) k j true
        return a / b
      else return a

/-- `math.factorial(n)` is defined below; `math.perm(n)` calls it. -/
def llongMaxMsg (what : String) : String := s!"{what} must not exceed {llongMax}"

/-! ## `math.factorial`, mathmodule.c:1484-2054 -/

/-- `count_set_bits`, mathmodule.c:1484-1492. -/
def countSetBits : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n ≠ 0 then countSetBits fuel (n &&& (n - 1)) + 1 else 0

/-- The tight loop `for (total = start, j = start + 2; j < stop; j += 2) total *= j;`
on `unsigned long`, mathmodule.c:1917-1918. `rem` bounds the iterations. -/
def fppLoop (stop : Nat) : Nat → Nat → Nat → Nat
  | 0, total, _ => total
  | rem + 1, total, j => if j < stop then fppLoop stop rem (u64 (total * j)) (j + 2) else total

/-- `factorial_partial_product(start, stop, max_bits)`, mathmodule.c:1893-1941. -/
def factorialPartialProduct : Nat → Nat → Nat → Nat → Py Nat
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, start, stop, maxBits =>
    let numOperands := (stop - start) / 2
    if numOperands ≤ 64 ∧ u64 (numOperands * maxBits) ≤ 64 then
      .ok (fppLoop stop (stop - start) start (start + 2))
    else do
      let midpoint := (start + numOperands) ||| 1
      let left ← factorialPartialProduct fuel start midpoint (bitLength (midpoint - 2))
      let right ← factorialPartialProduct fuel midpoint stop maxBits
      return left * right

/-- The loop of `factorial_odd_part`, mathmodule.c:1958-1986, for
`i = iters - 1, ..., 0`, carrying `(upper, inner, outer)`. -/
def factorialOddPartLoop (n : Nat) : Nat → Nat → Nat → Nat → Py Nat
  | 0, _, _, outer => .ok outer
  | i + 1, upper, inner, outer =>
    let v := n >>> i
    if v ≤ 2 then factorialOddPartLoop n i upper inner outer
    else do
      let lower := upper
      let upper := (v + 1) ||| 1
      let part ← factorialPartialProduct (upper + 1) lower upper (bitLength (upper - 2))
      let inner := inner * part
      let outer := outer * inner
      factorialOddPartLoop n i upper inner outer

/-- `factorial_odd_part(n)`, mathmodule.c:1946-1993. -/
def factorialOddPart (n : Nat) : Py Nat :=
  factorialOddPartLoop n (bitLength n - 2 + 1) 3 1 1

/-- `math.factorial(x)` for an int `x`, mathmodule.c:2018-2054. -/
def factorial (x : Int) : Py Nat :=
  if x > llongMax then
    .error (.overflowError s!"factorial() argument should not exceed {llongMax}")
  else if x < 0 then
    .error (.valueError "factorial() not defined for negative values")
  else
    let x := x.toNat
    if x < smallFactorials.length then .ok (smallFactorials.getD x 0)
    else do
      let odd ← factorialOddPart x
      let twoValuation := x - countSetBits 64 x
      return odd <<< twoValuation

/-- `math.perm(n, k)`, mathmodule.c:3744-3815 (`k = None` is `factorial(n)`). -/
def perm (n : Int) (k : Option Int) : Py Nat :=
  match k with
  | none => factorial n
  | some k =>
    if n < 0 then .error (.valueError "n must be a non-negative integer")
    else if k < 0 then .error (.valueError "k must be a non-negative integer")
    else if n < k then .ok 0
    else if k > llongMax then .error (.overflowError (llongMaxMsg "k"))
    else
      let n := n.toNat
      let k := k.toNat
      if n ≤ llongMax ∧ k > 1 then permCombSmall (k + 1) n k false
      else permComb (k + 1) n k false

/-- `math.comb(n, k)`, mathmodule.c:3839-3933. -/
def comb (n k : Int) : Py Nat :=
  if n < 0 then .error (.valueError "n must be a non-negative integer")
  else if k < 0 then .error (.valueError "k must be a non-negative integer")
  else if n ≤ llongMax then
    if k > llongMax ∨ k > n then .ok 0
    else
      let ni := n.toNat
      let ki := min k.toNat (ni - k.toNat)
      if ki > 1 then permCombSmall (ki + 1) ni ki true
      else permComb (ki + 1) ni ki true
  else
    let temp := n - k
    if temp < 0 then .ok 0
    else
      let k := if temp < k then temp else k
      if k > llongMax then .error (.overflowError (llongMaxMsg "min(n - k, k)"))
      else permComb (k.toNat + 1) n.toNat k.toNat true

/-! ## `_PyLong_GCD`, longobject.c:5647-5851 -/

/-- Euclid's algorithm on C `long`s, longobject.c:5831-5836. -/
def euclid : Nat → Nat → Nat → Nat
  | 0, x, _ => x
  | fuel + 1, x, y => if y ≠ 0 then euclid fuel y (x % y) else x

/-- The `simple:` tail, longobject.c:5812-5843: `a` and `b` fit in a `long`. -/
def gcdSimple (a b : Int) : Nat := euclid (b.natAbs + 1) a.natAbs b.natAbs

/-- State of Lehmer's inner loop: `x, y, A, B, C, D` and the step count `k`. -/
structure LehmerState where
  x : Int
  y : Int
  A : Int
  B : Int
  C : Int
  D : Int
  k : Nat
  deriving Repr, Inhabited

/-- The inner loop of Lehmer's algorithm on `stwodigits`, longobject.c:5717-5728.
Every intermediate is checked to fit `int64_t`. -/
def lehmerInner : Nat → LehmerState → Py LehmerState
  | 0, _ => .error .modelFuel
  | fuel + 1, st =>
    let yc := st.y - st.C
    if !inI64 yc then .error ubError
    else if yc = 0 then .ok st
    else
      let num := st.x + (st.A - 1)
      let q := num.tdiv yc
      let qD := q * st.D
      let s := st.B + qD
      let qy := q * st.y
      let t := st.x - qy
      if !(inI64 num && inI64 qD && inI64 s && inI64 qy && inI64 t) then .error ubError
      else if s > t then .ok st
      else
        let qC := q * st.C
        let t' := st.A + qC
        if !(inI64 qC && inI64 t') then .error ubError
        else lehmerInner fuel ⟨st.y, t, st.D, st.C, s, t', st.k + 1⟩

/-- The outer loop of `_PyLong_GCD`, longobject.c:5683-5808, on `0 <= b <= a`.
The top `2*PyLong_SHIFT` bits that :5701-5707 assemble from three digits are
`a >> sh` and `b >> sh` with `sh = 30*(size_a-3) + nbits`. The digit loop at
:5777-5799 stores the low `size_a` digits of `A*a - B*b` and `D*b - C*a`,
i.e. their values modulo `2^(30*size_a)`. -/
def lehmerOuter : Nat → Nat → Nat → Py Nat
  | 0, _, _ => .error .modelFuel
  | fuel + 1, a, b =>
    let sa := digitCount a
    if sa ≤ 2 then .ok (gcdSimple a b)
    else
      let nbits := bitLength (a >>> (30 * (sa - 1)))
      let sb := digitCount b
      if sb = 0 then .ok a
      else
        let sh := 30 * (sa - 3) + nbits
        match lehmerInner (2 ^ 64) ⟨(a >>> sh : Nat), (b >>> sh : Nat), 1, 0, 0, 1, 0⟩ with
        | .error e => .error e
        | .ok st =>
          if st.k = 0 then lehmerOuter fuel b (a % b)
          else
            let (A, B, C, D) :=
              if st.k % 2 = 1 then (-st.B, -st.A, -st.D, -st.C) else (st.A, st.B, st.C, st.D)
            let m : Int := 2 ^ (30 * sa)
            let c := (A * a - B * b) % m
            let d := (D * b - C * a) % m
            lehmerOuter fuel c.toNat d.toNat

/-- `_PyLong_GCD(a, b)`, longobject.c:5647-5851. -/
def pyLongGCD (a b : Int) : Py Nat :=
  if digitCount a.natAbs ≤ 2 ∧ digitCount b.natAbs ≤ 2 then .ok (gcdSimple a b)
  else
    let a' := a.natAbs
    let b' := b.natAbs
    let (a', b') := if a' < b' then (b', a') else (a', b')
    lehmerOuter (a' + 1) a' b'

/-! ## `math.gcd` and `math.lcm`, mathmodule.c:718-840 -/

/-- The loop of `math_gcd_impl`, mathmodule.c:742-758. -/
def gcdLoop (res : Int) : List Int → Py Int
  | [] => .ok res
  | x :: xs =>
    if res = 1 then gcdLoop res xs
    else do
      let g ← pyLongGCD res x
      gcdLoop g xs

/-- `math.gcd(*integers)`, mathmodule.c:718-761 (all arguments exact ints). -/
def gcd (args : List Int) : Py Int :=
  match args with
  | [a, b] => do return ((← pyLongGCD a b) : Int)
  | [] => .ok 0
  | [a] => .ok (a.natAbs : Int)
  | a :: rest => gcdLoop a rest

/-- `long_lcm(a, b)`, mathmodule.c:765-789. -/
def longLcm (a b : Int) : Py Int :=
  if a = 0 ∨ b = 0 then .ok 0
  else do
    let g ← pyLongGCD a b
    let f := floorDiv a g
    let m := f * b
    return (m.natAbs : Int)

/-- The loop of `math_lcm_impl`, mathmodule.c:819-837. -/
def lcmLoop (res : Int) : List Int → Py Int
  | [] => .ok res
  | x :: xs =>
    if res = 0 then lcmLoop res xs
    else do
      let r ← longLcm res x
      lcmLoop r xs

/-- `math.lcm(*integers)`, mathmodule.c:801-840. -/
def lcm (args : List Int) : Py Int :=
  match args with
  | [] => .ok 1
  | [a] => .ok (a.natAbs : Int)
  | a :: rest => lcmLoop a rest

end PyLean.MathInt
