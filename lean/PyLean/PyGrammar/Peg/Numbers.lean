import PyLean.PyGrammar.Lexer.State

/-!
`parsenumber`, `Parser/pegen.c:667-693`, with exact decimal-to-binary64 conversion.
Everything is over `Nat`: a binary64 is its 64-bit pattern, and
`PyOS_string_to_double` is correctly rounded (ties to even), which `roundToBits`
computes from the exact rational value.
-/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- `2^1024`-free binary64 infinity bit pattern. -/
def infBits : Nat := 0x7FF0000000000000

/-- The binary64 nearest to `num / den`, ties to even, for `num > 0`, `den > 0`;
values past the largest finite double become infinity, as `_Py_dg_strtod` reports
and `PyOS_string_to_double` passes through when `overflow_exception` is `NULL`. -/
def roundToBits (num den : Nat) : Nat :=
  -- `e` with `2^(e) ≤ num/den < 2^(e+2)`, from the bit lengths.
  let e : Int := (Nat.log2 num : Int) - (Nat.log2 den : Int) - 1
  -- Scale so that the quotient has at least 55 bits, keeping the exact remainder.
  let sh : Int := 54 - e
  let (n', d') : Nat × Nat :=
    if sh ≥ 0 then (num <<< sh.toNat, den) else (num, den <<< (-sh).toNat)
  let q := n' / d'
  let r := n' % d'
  -- `q` has 54 to 57 bits; its exponent:
  let bits := Nat.log2 q + 1
  -- value = q * 2^(-sh) (plus remainder); leading bit at position bits-1-sh
  let exp2 : Int := (bits : Int) - 1 - sh
  -- Number of low bits to drop: normal numbers keep 53, subnormals fewer.
  let keep : Int := if exp2 ≥ -1022 then 53 else 53 - (-1022 - exp2)
  if keep < 0 then 0
  else
    let drop := (bits : Int) - keep
    let dropN := drop.toNat
    let m := q >>> dropN
    let lost := q - (m <<< dropN)
    let half := 1 <<< (dropN - 1)
    let up :=
      if lost > half then true
      else if lost < half then false
      else if r > 0 then true
      else m % 2 == 1
    let m' := if up then m + 1 else m
    -- `m'` may have carried into a new bit.
    if exp2 ≥ -1022 then
      let (m2, e2) : Nat × Int :=
        if m' == 1 <<< 53 then (m' >>> 1, exp2 + 1) else (m', exp2)
      if e2 > 1023 then infBits
      else (((e2 + 1023).toNat) <<< 52) ||| (m2 - (1 <<< 52))
    else
      -- subnormal, or rounded up to the smallest normal: the encoding is the same
      m'

/-- `10 ^ n` without computing absurd powers: callers clamp `n` first. -/
def decimalToBits (mant : Nat) (exp10 : Int) (ndigits : Nat) : Nat :=
  if mant == 0 then 0
  else
    -- value ≥ 10^(ndigits-1+exp10) and < 10^(ndigits+exp10)
    let top : Int := (ndigits : Int) + exp10
    if top > 310 then infBits
    else if top < -330 then 0
    else if exp10 ≥ 0 then roundToBits (mant * 10 ^ exp10.toNat) 1
    else roundToBits mant (10 ^ (-exp10).toNat)

/-- Digits to value. -/
def digitsToNat (ds : List Nat) : Nat :=
  ds.foldl (fun a d => a * 10 + (d - 48)) 0

/-- `PyOS_string_to_double` on a Python float literal without underscores:
`[digits][.digits][(e|E)[+-]digits]`, as the tokenizer guarantees. -/
def stringToDouble (s : List Nat) : Nat :=
  let isD (c : Nat) := 48 ≤ c && c ≤ 57
  let intPart := s.takeWhile isD
  let rest := s.drop intPart.length
  let (frac, rest) :=
    match rest with
    | 46 :: r => (r.takeWhile isD, r.drop (r.takeWhile isD).length)
    | _ => ([], rest)
  let (neg, expDigits) :=
    match rest with
    | 101 :: 45 :: r | 69 :: 45 :: r => (true, r.takeWhile isD)
    | 101 :: 43 :: r | 69 :: 43 :: r => (false, r.takeWhile isD)
    | 101 :: r | 69 :: r => (false, r.takeWhile isD)
    | _ => (false, [])
  let exp : Nat := digitsToNat expDigits
  let all := intPart ++ frac
  let sig := all.dropWhile (· == 48)
  -- A huge exponent decides the result by itself once it exceeds every digit count.
  if exp > 100000 + all.length then
    if sig.isEmpty then 0 else if neg then 0 else infBits
  else
    let e : Int := (if neg then -(exp : Int) else exp) - frac.length
    decimalToBits (digitsToNat sig) e sig.length

/-- Value of a digit in any base up to 36, or `99`. -/
def digitVal (c : Nat) : Nat :=
  if 48 ≤ c && c ≤ 57 then c - 48
  else if 97 ≤ c && c ≤ 122 then c - 87
  else if 65 ≤ c && c ≤ 90 then c - 55
  else 99

/-- Result of `parsenumber`, or the `ValueError` message of the digit limit. -/
inductive NumResult where
  | ok (c : PyConst)
  | limit (msg : String)

/-- `_PY_LONG_DEFAULT_MAX_STR_DIGITS` -/
def maxStrDigits : Nat := 4300

/-- `_MAX_STR_DIGITS_ERROR_FMT_TO_INT` -/
def limitMessage (n : Nat) : String :=
  s!"Exceeds the limit ({maxStrDigits} digits) for integer string conversion: value has {n} "
    ++ "digits; use sys.set_int_max_str_digits() to increase the limit"

/-- `parsenumber_raw` after `parsenumber` removes underscores,
`Parser/pegen.c:622-690`. An integer literal is one `strtol` with base 0 consumes
entirely; its value is the same on both C paths, and only `PyLong_FromString`, reached
when `strtol` overflows, enforces the digit limit. -/
def parseNumber (raw : List Nat) : NumResult :=
  let s := raw.filter (· != 95)
  let imflag := match s.getLast? with
    | some c => c == 106 || c == 74
    | none => false
  let (base, ds) : Nat × List Nat :=
    match s with
    | 48 :: 120 :: r | 48 :: 88 :: r => (16, r)
    | 48 :: 111 :: r | 48 :: 79 :: r => (8, r)
    | 48 :: 98 :: r | 48 :: 66 :: r => (2, r)
    | _ => (10, s)
  let isInt := ds.all fun c => digitVal c < base
  if isInt then
    let v := ds.foldl (fun a d => a * base + digitVal d) 0
    if base == 10 && v ≥ 2 ^ 64 && ds.length > maxStrDigits then
      .limit (limitMessage ds.length)
    else .ok (.int v)
  else if imflag then
    .ok (.complex 0 (stringToDouble s))
  else
    .ok (.float (stringToDouble s))

end PyLean.PyGrammar.Peg
