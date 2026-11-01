import PyLean.PyGrammar.Lexer.State
import PyLean.PyGrammar.Peg.Numbers

/-!
`repr` of the constants an AST can hold, exactly and without `Float`.

* `str`: `unicode_repr`, `Objects/unicodeobject.c`.
* `bytes`: `PyBytes_Repr`, `Objects/bytesobject.c`.
* `float`: `float_repr`, shortest digits that round-trip, in the format of
  `PyOS_double_to_string(x, 'r', 0, Py_DTSF_ADD_DOT_0, NULL)`.
* `complex`: `complex_repr`, `Objects/complexobject.c`.
* `int`: decimal, with the 4300-digit limit of `int.__repr__`.
-/

namespace PyLean.PyGrammar.Unparse

open Lexer Peg

/-- Text of a Lean literal, as code points. -/
@[inline] def cp (s : String) : List Nat := s.toList.map Char.toNat

/-- Lower-case hex digit. -/
def hexDigit (d : Nat) : Nat := if d < 10 then 48 + d else 87 + d

/-- `n` as exactly `w` lower-case hex digits. -/
def hexN (n : Nat) : Nat → List Nat
  | 0 => []
  | w + 1 => hexN (n >>> 4) w ++ [hexDigit (n &&& 15)]

/-- `\xNN`, `\uNNNN` or `\UNNNNNNNN`. -/
def hexEscape (c : Nat) : List Nat :=
  if c < 0x100 then 92 :: 120 :: hexN c 2
  else if c < 0x10000 then 92 :: 117 :: hexN c 4
  else 92 :: 85 :: hexN c 8

/-- `str.isprintable` on one character. -/
@[inline] def printable (c : Nat) : Bool := isPrintable c

/-- `str.encode("unicode_escape")` of one character. -/
def unicodeEscape (c : Nat) : List Nat :=
  if c == 92 then [92, 92]
  else if c == 9 then [92, 116]
  else if c == 10 then [92, 110]
  else if c == 13 then [92, 114]
  else if c < 0x20 || c ≥ 0x7f then hexEscape c
  else [c]

/-- One character of `unicode_repr`, with quote `q`. -/
def reprEsc (q c : Nat) : List Nat :=
  if c == q || c == 92 then [92, c]
  else if c == 9 then [92, 116]
  else if c == 10 then [92, 110]
  else if c == 13 then [92, 114]
  else if c < 0x20 || c == 0x7f then hexEscape c
  else if c < 0x7f then [c]
  else if printable c then [c]
  else hexEscape c

/-- `unicode_repr`'s choice of quote. -/
def reprQuote (s : List Nat) : Nat := if s.contains 39 && !s.contains 34 then 34 else 39

/-- `unicode_repr` -/
def strRepr (s : List Nat) : List Nat :=
  reprQuote s :: s.flatMap (reprEsc (reprQuote s)) ++ [reprQuote s]

/-- `PyBytes_Repr` -/
def bytesRepr (s : List Nat) : List Nat :=
  let q : Nat := if s.contains 39 && !s.contains 34 then 34 else 39
  let esc (c : Nat) : List Nat :=
    if c == q || c == 92 then [92, c]
    else if c == 9 then [92, 116]
    else if c == 10 then [92, 110]
    else if c == 13 then [92, 114]
    else if c < 0x20 || c ≥ 0x7f then hexEscape c
    else [c]
  98 :: q :: s.flatMap esc ++ [q]

/-- Decode a binary64: `(negative, mantissa, exponent)` with value `m * 2^e`. `none` for
infinities and NaNs. -/
def decodeBits (b : Nat) : Option (Bool × Nat × Int) :=
  let neg := b >>> 63 == 1
  let ex := (b >>> 52) &&& 0x7FF
  let frac := b &&& 0xFFFFFFFFFFFFF
  if ex == 0x7FF then none
  else if ex == 0 then some (neg, frac, -1074)
  else some (neg, frac + (1 <<< 52), (ex : Int) - 1075)

/-- The positive rational `m * 2^e` as `(num, den)`. -/
def ratOf (m : Nat) (e : Int) : Nat × Nat :=
  if e ≥ 0 then (m <<< e.toNat, 1) else (m, 1 <<< (-e).toNat)

/-- `n * 10^k` as a rational. -/
def scaled (n : Nat) (k : Int) : Nat × Nat :=
  if k ≥ 0 then (n * 10 ^ k.toNat, 1) else (n, 10 ^ (-k).toNat)

/-- `floor(log10(num/den))`, found by a bounded walk from an estimate. -/
def floorLog10 (num den : Nat) : Int :=
  let est : Int := (((Nat.log2 num : Int) - (Nat.log2 den : Int)) * 30103) / 100000
  let ok (k : Int) : Bool :=
    -- 10^k ≤ num/den < 10^(k+1)
    if k ≥ 0 then den * 10 ^ k.toNat ≤ num && num < den * 10 ^ (k + 1).toNat
    else if k + 1 ≥ 0 then den ≤ num * 10 ^ (-k).toNat && num * 1 < den * 10 ^ (k + 1).toNat
    else den ≤ num * 10 ^ (-k).toNat && num * 10 ^ (-(k + 1)).toNat < den
  let cands : List Int := [est, est - 1, est + 1, est - 2, est + 2]
  (cands.find? ok).getD est

/-- Shortest decimal digits of the positive finite `bits`: `(digits, decpt)` with value
`0.d₁d₂… × 10^decpt`, as `_Py_dg_dtoa` mode 0 returns. Among `n`-digit decimals that read
back as `bits`, the one nearest the exact value is taken, for the smallest such `n`. -/
def shortestDigits (bits : Nat) (m : Nat) (e : Int) : List Nat × Int :=
  let (num, den) := ratOf m e
  let e10 := floorLog10 num den
  let rec go : Nat → Nat → List Nat × Int
    | 0, n =>
      let k : Int := e10 + 1 - n
      let q := if k ≥ 0 then num / (den * 10 ^ k.toNat) else (num * 10 ^ (-k).toNat) / den
      (Nat.toDigits 10 q |>.map Char.toNat, e10 + 1)
    | fuel + 1, n =>
      let k : Int := e10 + 1 - n
      let (qn, qd) : Nat × Nat :=
        if k ≥ 0 then (num, den * 10 ^ k.toNat) else (num * 10 ^ (-k).toNat, den)
      let lo := qn / qd
      let hi := lo + 1
      -- `|hi - v| - |v - lo|` decides the nearer one; ties go to even.
      let twice := 2 * (qn - lo * qd)
      let cands :=
        if twice < qd then [lo, hi]
        else if twice > qd then [hi, lo]
        else if lo % 2 == 0 then [lo, hi] else [hi, lo]
      let back (d : Nat) : Bool :=
        if d == 0 then false
        else
          let (a, b) := scaled d k
          roundToBits a b == bits
      match cands.find? back with
      | some d =>
        let ds := (Nat.toDigits 10 d).map Char.toNat
        -- `hi` may have one digit more than `n`, as with 9.5 → 10.
        let decpt : Int := (ds.length : Int) + k
        (((ds.reverse).dropWhile (· == 48)).reverse, decpt)
      | none => go fuel (n + 1)
  go 18 1

/-- `format_float_short` for mode `'r'`, `Python/pystrtod.c`. `addDot0` is
`Py_DTSF_ADD_DOT_0`. Digits `ds`, decimal point after `decpt` digits. -/
def formatShort (ds : List Nat) (decpt : Int) (addDot0 : Bool) : List Nat :=
  let n := (ds.length : Int)
  if decpt ≤ -4 || decpt > 16 then
    -- exponent form
    let e := decpt - 1
    let first := ds.take 1
    let rest := ds.drop 1
    let mant := if rest.isEmpty then first else first ++ 46 :: rest
    let sign : Nat := if e < 0 then 45 else 43
    let digits := (Nat.toDigits 10 e.natAbs).map Char.toNat
    let digits := if digits.length < 2 then 48 :: digits else digits
    mant ++ 101 :: sign :: digits
  else if decpt ≤ 0 then
    48 :: 46 :: (List.replicate (-decpt).toNat 48 ++ ds)
  else if decpt ≥ n then
    ds ++ List.replicate (decpt - n).toNat 48 ++ (if addDot0 then [46, 48] else [])
  else
    ds.take decpt.toNat ++ 46 :: ds.drop decpt.toNat

/-- `repr` of a binary64, with `Py_DTSF_ADD_DOT_0` as asked. -/
def floatStr (b : Nat) (addDot0 : Bool) : List Nat :=
  match decodeBits b with
  | none =>
    if b &&& 0xFFFFFFFFFFFFF != 0 then cp "nan"
    else if b >>> 63 == 1 then cp "-inf" else cp "inf"
  | some (neg, m, e) =>
    let body :=
      if m == 0 then (if addDot0 then cp "0.0" else cp "0")
      else
        let (ds, decpt) := shortestDigits (b &&& 0x7FFFFFFFFFFFFFFF) m e
        formatShort ds decpt addDot0
    if neg then 45 :: body else body

/-- `float.__repr__` -/
def floatRepr (b : Nat) : List Nat := floatStr b true

/-- `complex_repr`, `Objects/complexobject.c`. -/
def complexRepr (re im : Nat) : List Nat :=
  if re == 0 then floatStr im false ++ [106]
  else
    let r := floatStr re false
    let i := floatStr im false
    let i := match i with
      | 45 :: _ => i
      | _ => 43 :: i
    40 :: r ++ i ++ [106, 41]

/-- The `ValueError` of `int.__repr__` past the digit limit, `Objects/longobject.c`. -/
def intReprLimit : String :=
  "Exceeds the limit (4300 digits) for integer string conversion; "
    ++ "use sys.set_int_max_str_digits() to increase the limit"

/-- Whether `int.__repr__` is refused: more than 4300 decimal digits. -/
def intTooLong (v : Int) : Bool := v.natAbs ≥ 10 ^ 4300

/-- `int.__repr__`, for values within the limit. -/
def intRepr (v : Int) : List Nat := (toString v).toList.map Char.toNat

end PyLean.PyGrammar.Unparse
