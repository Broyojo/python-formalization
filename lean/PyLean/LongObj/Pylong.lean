import PyLean.LongObj.FromString

/-!
`Lib/_pylong.py` (CPython 3.14.7), the Python half of the int/str conversions and
of fast division, and the knots with the C code that calls it and that it calls.

`decimal` is not modelled. The two functions that use it are mirrored over exact
numbers, for these reasons:

* `int_to_decimal` runs in `_unbounded_dec_context`, which traps `Inexact`
  (`_pylong.py:133-137`), so every `Decimal` is an exact integer with exponent 0.
* `_dec_str_to_int_inner` runs with `ROUND_DOWN` and no trap. Its `Decimal`s are
  modelled as their exact values, with explicit chopping. `n.adjusted()` of a zero
  with a non-zero exponent is not tracked; it would change only a working
  precision, and the correctness theorem holds for every precision.

The float estimates `w * 0.3010299956639812 + 1` and `lenS * _LOG_10_BASE_256` use
the exact value of the double constant and leave out the rounding of the product;
their results are only sizes of a recursion and are not otherwise observable.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-! ## `compute_powers` -/

/-- A `dict` from exponents, in insertion order. -/
abbrev PowDict (α : Type) := List (Nat × α)

def dGet {α : Type} (k : Nat) (d : PowDict α) : Option α := d.lookup k

/-- The first `while ws` loop of `compute_powers`, _pylong.py:61-73. `ws.pop()` may
return any element; the model takes the head. Returns `need`. -/
def cpWork (needHi : Bool) (moreThan : Nat) :
    Nat → List Nat → List Nat → List Nat → Py (List Nat)
  | 0, _, _, _ => .error .modelFuel
  | _ + 1, [], _, need => .ok need
  | f + 1, w :: ws, seen, need =>
    if w ∈ seen ∨ w ≤ moreThan then cpWork needHi moreThan f ws seen need
    else
      let lo := w >>> 1
      let hi := w - lo
      let which := if needHi then hi else lo
      let ws' := List.insert which ws
      let ws'' := if lo ≠ hi then List.insert (w - which) ws' else ws'
      cpWork needHi moreThan f ws'' (w :: seen) (List.insert which need)

/-- The second loop, _pylong.py:90-96. Returns `extra`. -/
def cpExtra (moreThan : Nat) : Nat → List Nat → List Nat → Py (List Nat)
  | 0, _, _ => .error .modelFuel
  | _ + 1, [], extra => .ok extra
  | f + 1, c :: cs, extra =>
    let w := (c :: cs).foldl max 0
    let cands := (c :: cs).erase w
    let lo := w >>> 1
    if lo > moreThan ∧ w - 1 ∉ cands ∧ lo ∉ cands then
      cpExtra moreThan f (List.insert lo cands) (List.insert lo extra)
    else cpExtra moreThan f cands extra

section
variable {α : Type} (mul : α → α → α) (pow : α → Nat → α) (base : α)

/-- The third loop, _pylong.py:100-124. `pow` is `**`. `-1 in d` is false at `n = 0`;
the model reads `d[0]` there, which is absent because `0` sorts first. -/
def cpBuild : List Nat → PowDict α → Py (PowDict α)
  | [], d => .ok d
  | n :: ns, d =>
    let lo := n >>> 1
    let hi := n - lo
    match dGet (n - 1) d with
    | some v => cpBuild ns (d ++ [(n, mul v base)])
    | none =>
      match dGet lo d with
      | some v =>
        let r := mul v v
        if hi ≠ lo then
          if 2 * lo + 1 = n then cpBuild ns (d ++ [(n, mul r base)])
          else .error (.assertionError "")
        else cpBuild ns (d ++ [(n, r)])
      | none => cpBuild ns (d ++ [(n, pow base n)])

/-- `compute_powers(w, base, more_than, need_hi=...)`, _pylong.py:57-131. -/
def computePowers (w moreThan : Nat) (needHi : Bool) : Py (PowDict α) := do
  let need ← cpWork needHi moreThan (4 * w + 4) [w] [] []
  let extra ← cpExtra moreThan ((need.map (· + 1)).sum + 1) need []
  if ¬ (needHi = true ∨ extra = []) then throw (.assertionError "")
  let keys := (need.foldr List.insert extra).mergeSort (· ≤ ·)
  let d ← cpBuild mul pow base keys []
  if ¬ need.all (fun k => (dGet k d).isSome) then throw (.assertionError "")
  let excess := d.filter (fun kv => kv.1 ∉ need)
  if excess ≠ [] ∧ ¬ needHi = true then throw (.assertionError "")
  return d.filter (fun kv => kv.1 ∈ need)

end

/-- `compute_powers` over the `int`s. -/
def computePowersNat (w : Nat) (base moreThan : Nat) (needHi : Bool) : Py (PowDict Nat) :=
  computePowers (· * ·) (· ^ ·) base w moreThan needHi

/-! ## int to decimal string -/

/-- `str.zfill(w)` on a string without a sign. -/
def zfill (s : List Char) (w : Nat) : List Char := List.replicate (w - s.length) '0' ++ s

/-- `inner` of `int_to_decimal`, _pylong.py:157-163. `D(n)` is `n`; see the module
note on exactness. The operands evaluate in the source order: `inner(lo, w2)`,
then `inner(hi, w - w2)`, then `w2pow[w2]`. -/
def itdecInner (w2pow : PowDict Nat) : Nat → Nat → Nat → Py Nat
  | 0, _, _ => .error .modelFuel
  | f + 1, n, w =>
    if w ≤ 200 then .ok n
    else do
      let w2 := w >>> 1
      let hi := n >>> w2
      let lo := n &&& ((1 <<< w2) - 1)
      let l ← itdecInner w2pow f lo w2
      let h ← itdecInner w2pow f hi (w - w2)
      match dGet w2 w2pow with
      | some p => return l + h * p
      | none => throw (.keyError (toString w2))

/-- `int_to_decimal(n)`, _pylong.py:139-176, as the integer the `Decimal` equals. -/
def intToDecimal (n : Int) : Py Int := do
  let nbits := bitLength n.natAbs
  let w2pow ← computePowersNat nbits 2 200 false
  let r ← itdecInner w2pow (nbits + 1) n.natAbs nbits
  return if n < 0 then -(r : Int) else r

/-- `inner` of `int_to_decimal_string`, _pylong.py:193-198. `strf` is `str`. -/
def itdsInner (strf : Int → Py (List Char)) (pow10 : PowDict Nat) :
    Nat → Nat → Nat → Py (List Char)
  | 0, _, _ => .error .modelFuel
  | f + 1, n, w =>
    if w ≤ 1000 then strf n
    else
      let w2 := w >>> 1
      match dGet w2 pow10 with
      | none => .error (.keyError (toString w2))
      | some p => do
        let a ← itdsInner strf pow10 f (n / p) (w - w2)
        let b ← itdsInner strf pow10 f (n % p) w2
        return a ++ zfill b w2

/-- `int(w * 0.3010299956639812 + 1)`, _pylong.py:207, with the exact value of the
double constant. -/
def decEstimate (w : Nat) : Nat := w * 5422874305198591 / 2 ^ 54 + 1

/-- The decimal digits of an integer with its sign, which is how `str` prints a
`Decimal` of exponent 0 and also what `str(int)` is specified to return. -/
def decStr (v : Int) : List Char :=
  (if v < 0 then ['-'] else []) ++ Nat.toDigits 10 v.natAbs

/-- `int_to_decimal_string(n)`, _pylong.py:178-221, for a build with `_decimal`. -/
def intToDecimalString (strf : Int → Py (List Char)) (n : Int) : Py (List Char) := do
  let w := bitLength n.natAbs
  if w > 450000 then
    let d ← intToDecimal n
    return decStr d
  let w := decEstimate w
  let pow10 ← computePowersNat w 5 1000 false
  let pow10 := pow10.map (fun kv => (kv.1, kv.2 <<< kv.1))
  let m := n.natAbs
  let sign := if n < 0 then ['-'] else []
  let s ← itdsInner strf pow10 (w + 1) m w
  let s := if s.head? = some '0' ∧ m ≠ 0 then s.dropWhile (· == '0') else s
  return sign ++ s

/-! ## str to int -/

/-- `s[a:b]` for `a <= b`. -/
def slice (s : List Nat) (a b : Nat) : List Nat := (s.drop a).take (b - a)

/-- `inner` of `_str_to_int_inner`, _pylong.py:238-244. `leaf` is `int`. -/
def stiInner (leaf : List Nat → Py Int) (w5pow : PowDict Nat) (s : List Nat) :
    Nat → Nat → Nat → Py Int
  | 0, _, _ => .error .modelFuel
  | f + 1, a, b =>
    if b - a ≤ 2048 then leaf (slice s a b)
    else do
      let mid := (a + b + 1) >>> 1
      let x ← stiInner leaf w5pow s f mid b
      let y ← stiInner leaf w5pow s f a mid
      match dGet (b - mid) w5pow with
      | some p => return x + y * (p : Int) * (2 ^ (b - mid) : Nat)
      | none => throw (.keyError (toString (b - mid)))

/-- `_str_to_int_inner(s)`, _pylong.py:223-247. -/
def strToIntInner (leaf : List Nat → Py Int) (s : List Nat) : Py Int := do
  let w5pow ← computePowersNat s.length 5 2048 false
  stiInner leaf w5pow s (s.length + 1) 0 s.length

/-- Number of decimal digits of `n`, one for zero: `n.adjusted() + 1`. -/
def decLen (n : Nat) : Nat := (Nat.toDigits 10 n).length

/-- `Decimal.adjusted()` of an integer. -/
def adjusted (n : Nat) : Nat := decLen n - 1

/-- Unary `+` under `ROUND_DOWN`: keep `prec` significant digits. -/
def chop (prec x : Nat) : Nat :=
  let d := decLen x - prec
  x / 10 ^ d * 10 ^ d

/-- `int.to_bytes(w)`, big-endian, for `n < 256^w`. -/
def toBytesBE (w n : Nat) : List Nat :=
  (List.range w).reverse.map (fun i => n / 256 ^ i % 256)

/-- `(p256, recip)` of one power: `recip` is the chopped reciprocal, held as an
integer scaled by `10^e`. -/
structure PowRec where
  p256 : Nat
  recip : Nat
  e : Nat

/-- `inner` of `_dec_str_to_int_inner`, _pylong.py:283-338. Returns the bytes that
`result` gains. `leaf` is `int(str(n))`. -/
def dsiInner (leaf : Nat → Py Nat) (pow256 : PowDict PowRec) (GUARD : Nat) :
    Nat → Nat → Nat → Py (List Nat)
  | 0, _, _ => .error .modelFuel
  | f + 1, n, w =>
    if w ≤ 100000 then do
      let v ← leaf n
      if v < 256 ^ w then return toBytesBE w v
      else throw (.overflowError "int too big to convert")
    else
      let w1 := w >>> 1
      let w2 := w - w1
      match dGet w2 pow256 with
      | none => .error (.keyError (toString w2))
      | some ⟨p, recip, e⟩ =>
        let prec := (adjusted n - adjusted p) + GUARD
        let hi0 := chop prec (chop prec n * chop prec recip) / 10 ^ e
        if hi0 * p > n then .error (.assertionError "")
        else
          let lo0 := n - hi0 * p
          let (hi, lo) :=
            if lo0 ≥ p then
              let lo1 := lo0 - p
              let hi1 := hi0 + 1
              if lo1 ≥ p then (hi1 + lo1 / p, lo1 % p) else (hi1, lo1)
            else (hi0, lo0)
        do
          let a ← dsiInner leaf pow256 GUARD f hi w1
          let b ← dsiInner leaf pow256 GUARD f lo w2
          return a ++ b

/-- `w` of `_dec_str_to_int_inner`, _pylong.py:353-356, with the exact value of
`_LOG_10_BASE_256`. -/
def byteEstimate (lenS : Nat) : Nat :=
  let num := lenS * 7480317065143153
  let i := num / 2 ^ 54
  i + 1 + (if (num - i * 2 ^ 54) * 10 > 9 * 2 ^ 54 then 1 else 0)

/-- `int.from_bytes(result)`: big-endian. -/
def fromBytesBE (l : List Nat) : Nat := l.foldl (fun acc b => acc * 256 + b) 0

/-- `_dec_str_to_int_inner(s, GUARD=...)`, _pylong.py:271-387, on a string of ASCII
digits. `leaf` is `int(str(n))`. -/
def decStrToIntInner (leaf : Nat → Py Nat) (s : List Nat) (GUARD : Nat := 8) : Py Nat := do
  let lenS := s.length
  let w := byteEstimate lenS
  if bitLength w ≥ 46 then
    throw (.valueError s!"cannot convert string of len {lenS} to int")
  let pow256 ← computePowersNat w 256 100000 true
  let pairs := pow256.map (fun kv =>
    -- `1 / 256**k` is exactly `5**(8k) / 10**(8k)`, _pylong.py:375-383.
    let k := kv.1
    (k, (⟨kv.2, chop (adjusted kv.2 + GUARD + 1) (5 ^ (8 * k)), 8 * k⟩ : PowRec)))
  let n := s.foldl (fun acc c => acc * 10 + (c - 48)) 0
  let bytes ← dsiInner leaf pairs GUARD (w + 1) n w
  return fromBytesBE bytes

/-- `str.rstrip()`. -/
def rstripU (s : List Nat) : List Nat :=
  (s.reverse.dropWhile (fun c => StrSearch.uniSpace c)).reverse

/-- `int_from_string(s)`, _pylong.py:389-400, for a build with `_decimal`. -/
def intFromString (leaf : List Nat → Py Int) (decLeaf : Nat → Py Nat) (s : List Nat) : Py Int := do
  let s := (rstripU s).filter (· ≠ uscore)
  if s.length ≥ 2000000 then
    let v ← decStrToIntInner decLeaf s
    return (v : Int)
  else strToIntInner leaf s

/-- The match of `re.match(r'\s*([+-]?)([0-9_]+)\s*', s)`, _pylong.py:405: the sign
group and the digits group. -/
def strToIntMatch (s : List Nat) : Option (List Nat × List Nat) :=
  let r0 := s.dropWhile (fun c => StrSearch.uniSpace c)
  let (sign, r1) :=
    match r0 with
    | 43 :: t => ([43], t)
    | 45 :: t => ([45], t)
    | t => ([], t)
  let g2 := r1.takeWhile (fun c => (48 ≤ c ∧ c ≤ 57) ∨ c = uscore)
  if g2 = [] then none else some (sign, g2)

/-- `str_to_int(s)`, _pylong.py:402-411. -/
def strToInt (leaf : List Nat → Py Int) (decLeaf : Nat → Py Nat) (s : List Nat) : Py Int :=
  match strToIntMatch s with
  | none => .error (.valueError "invalid literal for int() with base 10")
  | some (sign, g2) => do
    let v ← intFromString leaf decLeaf g2
    return if sign = [45] then -v else v

/-! ## Burnikel-Ziegler division -/

/-- `while r < 0: q -= 1; r += b`, _pylong.py:459-461. -/
def div3Loop (b : Int) : Nat → Int → Int → Py (Int × Int)
  | 0, _, _ => .error .modelFuel
  | f + 1, q, r => if r < 0 then div3Loop b f (q - 1) (r + b) else .ok (q, r)

mutual
  /-- `_div2n1n(a, b, n)`, _pylong.py:422-449, on non-negative ints. -/
  def div2n1n : Nat → Nat → Nat → Nat → Py (Nat × Nat)
    | 0, _, _, _ => .error .modelFuel
    | f + 1, a, b, n =>
      if (bitLength a : Int) - n ≤ 4000 then .ok (a / b, a % b)
      else
        let pad := n &&& 1
        let a' := if pad ≠ 0 then a <<< 1 else a
        let b' := if pad ≠ 0 then b <<< 1 else b
        let n' := if pad ≠ 0 then n + 1 else n
        let half := n' >>> 1
        let mask := (1 <<< half) - 1
        let b1 := b' >>> half
        let b2 := b' &&& mask
        do
          let (q1, r) ← div3n2n f (a' >>> n') ((a' >>> half) &&& mask) b' b1 b2 half
          let (q2, r) ← div3n2n f r (a' &&& mask) b' b1 b2 half
          let r := if pad ≠ 0 then r >>> 1 else r
          return ((q1 <<< half) ||| q2, r)

  /-- `_div3n2n(a12, a3, b, b1, b2, n)`, _pylong.py:452-462. -/
  def div3n2n : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Py (Nat × Nat)
    | 0, _, _, _, _, _, _ => .error .modelFuel
    | f + 1, a12, a3, b, b1, b2, n => do
      let (q, r) ←
        if a12 >>> n = b1 then pure ((1 <<< n) - 1, a12 - (b1 <<< n) + b1)
        else div2n1n f a12 b1 n
      let r' : Int := (((r <<< n) ||| a3 : Nat) : Int) - (q : Int) * (b2 : Int)
      let (q', r'') ← div3Loop b 4 q r'
      return (q'.toNat, r''.toNat)
end

/-- `inner` of `_int2digits`, _pylong.py:480-489: fills `a_digits[L:R]`. -/
def i2dInner (n : Nat) : Nat → Nat → Nat → Nat → Py (List Nat)
  | 0, _, _, _ => .error .modelFuel
  | f + 1, x, L, R =>
    if L + 1 = R then .ok [x]
    else do
      let mid := (L + R) >>> 1
      let shift := (mid - L) * n
      let upper := x >>> shift
      let lower := x ^^^ (upper <<< shift)
      let a ← i2dInner n f lower L mid
      let b ← i2dInner n f upper mid R
      return a ++ b

/-- `_int2digits(a, n)`, _pylong.py:465-493. -/
def int2digits (a n : Nat) : Py (List Nat) :=
  let len := (bitLength a + n - 1) / n
  if a ≠ 0 then i2dInner n (len + 1) a 0 len else .ok (List.replicate len 0)

/-- `inner` of `_digits2int`, _pylong.py:501-506. -/
def d2iInner (digits : List Nat) (n : Nat) : Nat → Nat → Nat → Py Nat
  | 0, _, _ => .error .modelFuel
  | f + 1, L, R =>
    if L + 1 = R then
      match digits[L]? with
      | some d => .ok d
      | none => .error (.indexError "list index out of range")
    else do
      let mid := (L + R) >>> 1
      let shift := (mid - L) * n
      let h ← d2iInner digits n f mid R
      let l ← d2iInner digits n f L mid
      return (h <<< shift) + l

/-- `_digits2int(digits, n)`, _pylong.py:496-508. -/
def digits2int (digits : List Nat) (n : Nat) : Py Nat :=
  if digits ≠ [] then d2iInner digits n (digits.length + 1) 0 digits.length else .ok 0

/-- The loop of `_divmod_pos`, _pylong.py:520-522, over `reversed(a_digits)`.
`q_digits` is in append order. -/
def dmLoop (b n fuel : Nat) : List Nat → Nat → List Nat → Py (List Nat × Nat)
  | [], r, qs => .ok (qs, r)
  | d :: ds, r, qs => do
    let (q, r') ← div2n1n fuel ((r <<< n) + d) b n
    dmLoop b n fuel ds r' (qs ++ [q])

/-- `_divmod_pos(a, b)`, _pylong.py:511-525. -/
def divmodPos (a b : Nat) : Py (Nat × Nat) := do
  let n := bitLength b
  let aDigits ← int2digits a n
  let (qs, r) ← dmLoop b n (2 * n + 2) aDigits.reverse 0 []
  let q ← digits2int qs.reverse n
  return (q, r)

/-! ## `consumer`, _pylong.py:706-722 -/

/-- `inner` of `consumer`: the set `need` that recursion needs. -/
def consumerInner (limit : Nat) (needHi : Bool) :
    Nat → Nat → List Nat × List Nat → List Nat × List Nat
  | 0, _, st => st
  | f + 1, w, (seen, need) =>
    if w ≤ limit then (seen, need)
    else if w ∈ seen then (seen, need)
    else
      let lo := w >>> 1
      let hi := w - lo
      let st := (w :: seen, List.insert (if needHi then hi else lo) need)
      consumerInner limit needHi f hi (consumerInner limit needHi f lo st)

/-! ## The knots with the C code -/

/-- `pylong_int_to_decimal_string(aa, ...)`, longobject.c:1952-2012, as `str(a)` with
fuel for the mutual recursion between C and `_pylong`: `int_to_decimal_string` calls
`str` on pieces. -/
def longStrF : Nat → Nat → Long → Py (List Char)
  | 0, _, _ => .error .modelFuel
  | f + 1, lim, x =>
    longToDecimalWith
      (fun y => intToDecimalString (fun n => longStrF f lim (Long.ofInt n)) y.toInt) lim x

/-- `long_to_decimal_string(aa)`, longobject.c:2243-2249. -/
def longToDecimalString (lim : Nat) (x : Long) : Py (List Char) := longStrF 3 lim x

/-- `_PyLong_Format(obj, base)`. -/
def pyLongFormat (lim : Nat) (x : Long) (base : Nat) : Py (List Char) :=
  if base = 10 then longToDecimalString lim x else longFormatBinary x base true

/-- `_PyLong_FormatWriter` and `_PyLong_FormatBytesWriter`. -/
def pyLongFormatW (lim : Nat) (x : Long) (base : Nat) (alternate : Bool) : Py (List Char) :=
  if base = 10 then longToDecimalString lim x else longFormatBinary x base alternate

/-- `int(str(n))` of `_dec_str_to_int_inner`, through `leaf`. -/
def decLeafOf (leaf : List Nat → Py Int) (n : Nat) : Py Nat := do
  let v ← leaf ((Nat.toDigits 10 n).map Char.toNat)
  return v.toNat

/-- `pylong_int_from_string(start, end, res)`, longobject.c:2576-2604. -/
def pylongHook (leaf : List Nat → Py Int) (body : List Nat) : Py (List Nat) := do
  let v ← intFromString leaf (decLeafOf leaf) body
  return digitsOf v.natAbs

/-- `int(s, base)` for a `str`, with fuel for the recursion through `_pylong`. -/
def intOfStrF : Nat → Nat → List Nat → Int → Py Long
  | 0, _, _, _ => .error .modelFuel
  | f + 1, lim, u, base =>
    pyLongFromUnicodeObject
      (pylongHook (fun s => do let v ← intOfStrF f lim s 10; return v.toInt)) lim u base

/-- The leaf `int(s)` used by `_pylong`, one level of recursion down from `fuel`. -/
def pylongLeaf (fuel lim : Nat) (s : List Nat) : Py Int := do
  let v ← intOfStrF fuel lim s 10
  return v.toInt

/-- `PyLong_FromUnicodeObject(u, base)`. -/
def intOfStr (lim : Nat) (u : List Nat) (base : Int) : Py Long := intOfStrF 3 lim u base

/-- `_PyLong_FromBytes(s, len, base)`. -/
def intOfBytes (lim : Nat) (s : List Nat) (base : Int) : Py Long :=
  pyLongFromBytes (pylongHook (pylongLeaf 2 lim)) lim s base

/-- `PyLong_FromString(str, pend, base)`. -/
def intOfCStr (lim : Nat) (s : List Nat) (base : Int) : Py Long × Option (List Nat) :=
  pyLongFromString (pylongHook (pylongLeaf 2 lim)) lim s base

end PyLean.LongObj
