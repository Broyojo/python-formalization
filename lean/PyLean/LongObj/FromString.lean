import PyLean.LongObj.Format
import PyLean.Datetime.IsoPy
import PyLean.StrSearch.Model

/-!
String to `int`, `Objects/longobject.c` (CPython 3.14.7).

A C string is a `List Nat` of bytes that may hold NUL bytes of its own; a `const
char *` into it is the suffix that starts there, and reading past the end reads
the terminating NUL (`hd`). So `end == s + len` becomes "the suffix is empty",
and an embedded NUL ends a scan exactly as in C.

`long_from_non_binary_base` allocates from a `double` estimate. The estimate is
not observable except through the rare reallocation at :2837-2853, so the digit
loop is modelled for an arbitrary capacity `size_z` and proven for all of them.
`fsizeZ` gives the capacity the tables produce; it uses the exact values of the
doubles in `log_base_BASE` and leaves out the rounding of the two `double`
operations, which only moves a capacity.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt PyLean.Datetime PyLean.StrSearch

/-! ## Character classes -/

/-- `_PyLong_DigitValue`, longobject.c:2475-2492. -/
def digitValueTable : List Nat :=
  [37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37,
   37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37,
   37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37,
   0,  1,  2,  3,  4,  5,  6,  7,  8,  9,  37, 37, 37, 37, 37, 37,
   37, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
   25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 37, 37, 37, 37, 37,
   37, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
   25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 37, 37, 37, 37, 37,
   37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37,
   37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37,
   37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37,
   37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37,
   37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37,
   37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37,
   37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37,
   37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37]

/-- `_PyLong_DigitValue[Py_CHARMASK(c)]`. -/
def digitValue (c : Nat) : Nat := digitValueTable.getD (c % 256) 37

/-- `Py_ISSPACE(c)`, pyctype.c (`PY_CTF_SPACE`): `\t\n\v\f\r` and space. -/
def cIsSpace (c : Nat) : Bool := byteSpace c

/-- `'_'`. -/
def uscore : Nat := 95

/-- `*p`: the byte at a pointer, the terminating NUL past the end. -/
def hd (p : List Nat) : Nat := p.headD 0

/-! ## `long_from_binary_base` -/

/-- The read loop of `long_from_binary_base`, longobject.c:2545-2566, over the
characters from the right. Returns the digits written, from `ob_digit[0]`. -/
def binLoop (bpc : Nat) : List Nat → Nat → Nat → Py (List Nat)
  | [], accum, bits =>
    if bits ≠ 0 then do
      let a ← chk32 accum
      return [a]
    else .ok []
  | c :: r, accum, bits =>
    if c = uscore then binLoop bpc r accum bits
    else do
      let k := digitValue c
      let a ← chk64 (accum ||| (k <<< bits))
      let bits' := bits + bpc
      if bits' ≥ 30 then do
        let rest ← binLoop bpc r (a >>> 30) (bits' - 30)
        return (a &&& MASK) :: rest
      else binLoop bpc r a bits'

/-- `for (bits_per_char = -1; n; ++bits_per_char) n >>= 1;`, longobject.c:2519-2522. -/
def bitsPerChar (base : Nat) : Nat := bitLength base - 1

/-- `long_from_binary_base(start, end, digits, base, res)`, longobject.c:2507-2571. -/
def longFromBinaryBase (body : List Nat) (digits base : Nat) : Py (List Nat) := do
  let bpc := bitsPerChar base
  if digits > (ssizeMax - (30 - 1)) / bpc then
    throw (.valueError "int string too large to convert")
  let n := (digits * bpc + 30 - 1) / 30
  longAlloc n
  let out ← binLoop bpc body.reverse 0 0
  if out.length ≤ n then return out ++ List.replicate (n - out.length) 0
  else throw cOverflow

/-! ## `long_from_non_binary_base` -/

/-- `log_base_BASE[base] * 2^60`, longobject.c:2720-2732: the doubles of the table
are all integer multiples of `2^-60`. -/
def logBaseBASE : List Nat :=
  [0, 0, 0, 60911245035895544, 0, 89233361091548256, 99341961856123776, 107888662023469680,
   0, 121822490071791088, 127664077911776496, 132948436894793776, 137772678676352016,
   142210550918205504, 146319378843697920, 150144606127443808, 0, 157084126965297312,
   160253206892019296, 163250899342006688, 166094794732004704, 168799907059365248,
   171379153715022016, 173843728551984768, 176203395496580256, 178466722183096512,
   180641267738433728, 182733735107686624, 184750095663926144, 186695691941798272,
   188575322947672032, 190393315476297536, 0, 193859681930689312, 195514843785525536,
   197122023115017952, 198683923712247552]

/-- `convwidth_base`, longobject.c:2733-2735. -/
def convwidthBase : List Nat :=
  [0, 0, 0, 18, 0, 12, 11, 10, 0, 9, 9, 8, 8, 8, 7, 7, 0, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6,
   6, 6, 6, 0, 5, 5, 5, 5]

/-- `convmultmax_base`, longobject.c:2736-2742. -/
def convmultmaxBase : List Nat :=
  [0, 0, 0, 387420489, 0, 244140625, 362797056, 282475249, 0, 387420489, 1000000000,
   214358881, 429981696, 815730721, 105413504, 170859375, 0, 410338673, 612220032, 893871739,
   64000000, 85766121, 113379904, 148035889, 191102976, 244140625, 308915776, 387420489,
   481890304, 594823321, 729000000, 887503681, 0, 39135393, 45435424, 52521875, 60466176]

/-- `(Py_ssize_t)((double)digits * log_base_BASE[base] + 1.0)`, longobject.c:2766,
:2774, without the rounding of the `double` operations (see the module note). -/
def fsizeZ (digits base : Nat) : Nat := digits * logBaseBASE.getD base 0 / 2 ^ 60 + 1

/-- Inner `for (i = 1; i < convwidth && p != end; ++p)`, longobject.c:2800-2808.
Returns `(i, c, p)`. -/
def grab (base convwidth : Nat) : List Nat → Nat → Nat → Py (Nat × Nat × List Nat)
  | [], i, c => .ok (i, c, [])
  | x :: r, i, c =>
    if i < convwidth then
      if x = uscore then grab base convwidth r i c
      else do
        let c' ← chk64 (c * base + digitValue x)
        grab base convwidth r (i + 1) c'
    else .ok (i, c, x :: r)

/-- `convmult = base; for ( ; i > 1; --i) convmult *= base;`, longobject.c:2815-2818. -/
def shortMult (base : Nat) : Nat → Nat → Py Nat
  | 0, m => .ok m
  | 1, m => .ok m
  | i + 2, m => do
    let m' ← chk64 (m * base)
    shortMult base (i + 1) m'

/-- `for (; pz < pzstop; ++pz)`, longobject.c:2824-2828. -/
def mulLoop (m : Nat) : List Nat → Nat → Py (List Nat × Nat)
  | [], c => .ok ([], c)
  | d :: ds, c => do
    let t ← chk64 (d * m)
    let c' ← chk64 (c + t)
    let (r, c'') ← mulLoop m ds (c' >>> 30)
    return ((c' &&& MASK) :: r, c'')

/-- `(digit)c` with `assert(c < PyLong_BASE)`, longobject.c:2831. -/
def chkDigit (c : Nat) : Py Nat := if c < 2 ^ 30 then .ok c else .error cOverflow

/-- The `while (p < end)` loop of `long_from_non_binary_base`,
longobject.c:2793-2855. `z` is the digits so far, `sizeZ` the allocated size. -/
def nbLoop (base convwidth convmultmax : Nat) :
    Nat → List Nat → List Nat → Nat → Py (List Nat)
  | 0, _, _, _ => .error .modelFuel
  | _ + 1, [], z, _ => .ok z
  | f + 1, x :: r, z, sizeZ =>
    if x = uscore then nbLoop base convwidth convmultmax f r z sizeZ
    else do
      let (i, c, p) ← grab base convwidth r 1 (digitValue x)
      let convmult ←
        if i ≠ convwidth then shortMult base i base else pure convmultmax
      let (z', c') ← mulLoop convmult z c
      if c' ≠ 0 then do
        let d ← chkDigit c'
        if z'.length < sizeZ then
          nbLoop base convwidth convmultmax f p (z' ++ [d]) sizeZ
        else do
          longAlloc (sizeZ + 1)
          nbLoop base convwidth convmultmax f p (z' ++ [d]) (sizeZ + 1)
      else nbLoop base convwidth convmultmax f p z' sizeZ

/-- `long_from_non_binary_base(start, end, digits, base, res)`,
longobject.c:2747-2858, with the allocation `sizeZ` as a parameter. -/
def longFromNonBinaryBaseAt (sizeZ : Nat) (body : List Nat) (base : Nat) : Py (List Nat) := do
  if sizeZ > maxLongDigits then
    throw (.overflowError "too many digits in integer")
  longAlloc sizeZ
  nbLoop base (convwidthBase.getD base 0) (convmultmaxBase.getD base 0)
    (body.length + 1) body [] sizeZ

/-! ## `long_from_string_base` -/

/-- `_MAX_STR_DIGITS_ERROR_FMT_TO_INT`, longobject.c:30. -/
def limitToIntMsg (lim digits : Nat) : String :=
  s!"Exceeds the limit ({lim} digits) for integer string conversion: value has {digits} digits; use sys.set_int_max_str_digits() to increase the limit"

/-- How the validating loop of `long_from_string_base` ended. -/
inductive Scan where
  /-- A double underscore: `*str = p - 1`, longobject.c:2903-2906. -/
  | dbl (q : List Nat)
  /-- The first character that is neither a digit nor `_`: `p`, with the count of
  digits, the previous character and the pointer `p - 1`. -/
  | stop (digits prev : Nat) (q p : List Nat)

/-- The `while` loop at longobject.c:2900-2912. -/
def scan (base : Nat) : List Nat → List Nat → Nat → Nat → Scan
  | q, [], prev, digits => .stop digits prev q []
  | q, c :: r, prev, digits =>
    if digitValue c < base ∨ c = uscore then
      if c = uscore then
        if prev = uscore then .dbl q
        else scan base (c :: r) r c digits
      else scan base (c :: r) r c (digits + 1)
    else .stop digits prev q (c :: r)

/-- `long_from_string_base(&str, base, &res)`, longobject.c:2880-2962. The first
component is the return value and `*res`: `none` is `-1`, a syntax error. The
second is the new `*str`. `pyl` is `pylong_int_from_string`. -/
def longFromStringBase (pyl : List Nat → Py (List Nat)) (lim : Nat) (start : List Nat)
    (base : Nat) : Option (Py (List Nat)) × List Nat :=
  if hd start = uscore then (none, start)
  else
    match scan base start start 0 0 with
    | .dbl q => (none, q)
    | .stop digits prev q e =>
      if prev = uscore then (none, q)
      else if start.length = e.length then (none, e)
      else
        let p := e.dropWhile (fun c => c ≠ 0 && cIsSpace c)
        if hd p ≠ 0 then (none, p)
        else
          let body := start.take (start.length - e.length)
          if base &&& (base - 1) = 0 then
            (some (longFromBinaryBase body digits base), p)
          else if digits > strDigitsThreshold ∧ lim > 0 ∧ digits > lim then
            (some (.error (.valueError (limitToIntMsg lim digits))), p)
          else if digits > 6000 ∧ base = 10 then
            (some (pyl body), p)
          else
            (some (longFromNonBinaryBaseAt (fsizeZ digits base) body base), p)

/-! ## Messages -/

/-- Up to and including the first NUL is what `strlen` measures. -/
def cStr (s : List Nat) : List Nat := s.takeWhile (· ≠ 0)

def hexChar (d : Nat) : Char := Nat.digitChar d

/-- `\xNN`, as `unicode_repr` and `PyBytes_Repr` print it. -/
def hexEsc (c : Nat) : List Char := ['\\', 'x', hexChar (c / 16), hexChar (c % 16)]

/-- The escaped body of a `repr` of ASCII-or-byte data with quote `q`. -/
def reprBody (q : Nat) : List Nat → List Char
  | [] => []
  | c :: r =>
    (if c = q ∨ c = 92 then ['\\', Char.ofNat c]
     else if c = 9 then ['\\', 't']
     else if c = 10 then ['\\', 'n']
     else if c = 13 then ['\\', 'r']
     else if c < 32 ∨ c ≥ 127 then hexEsc c
     else [Char.ofNat c]) ++ reprBody q r

/-- The quote `repr` picks: `"` when the data has `'` and no `"`. -/
def reprQuote (s : List Nat) : Nat := if s.contains 39 ∧ ¬ s.contains 34 then 34 else 39

/-- `repr(s)` of an ASCII `str`. -/
def reprStr (s : List Nat) : List Char :=
  let q := reprQuote s
  [Char.ofNat q] ++ reprBody q s ++ [Char.ofNat q]

/-- `repr(b)` of a `bytes`. -/
def reprBytes (s : List Nat) : List Char := 'b' :: reprStr s

/-- `"invalid literal for int() with base %d: %.200R"`. A non-ASCII `str` has a
`repr` that needs the Unicode printable table, which this model does not hold, so
the text is compared up to the object (`~`). -/
def invalidLiteral (base : Int) (repr : Option (List Char)) : PyExc :=
  match repr with
  | some r =>
    .valueError s!"invalid literal for int() with base {base}: {String.ofList (r.take 200)}"
  | none => .valueError s!"~invalid literal for int() with base {base}"

/-- All of `s` is ASCII, so `reprStr` applies. -/
def isAscii (s : List Nat) : Bool := s.all (· < 128)

/-- The `onError` label, longobject.c:3061-3075: a `str` is made from the first 200
bytes of `orig_str`, which can fail to decode. -/
def onError (orig : List Nat) (base : Int) : PyExc :=
  let cs := (cStr orig).take 200
  if isAscii cs then invalidLiteral base (some (reprStr cs))
  else if (ByteArray.validateUTF8 ⟨cs.map (·.toUInt8) |>.toArray⟩) then invalidLiteral base none
  else .named "UnicodeDecodeError" "~utf-8 codec can't decode"

/-! ## `PyLong_FromString` -/

def lower (c : Nat) : Nat := if 65 ≤ c ∧ c ≤ 90 then c + 32 else c

/-- `PyLong_FromString(str, pend, base)`, longobject.c:2973-3076. The second
component is what is stored to `*pend`: `none` when no path wrote it. -/
def pyLongFromString (pyl : List Nat → Py (List Nat)) (lim : Nat) (orig : List Nat)
    (base : Int) : Py Long × Option (List Nat) :=
  if (base ≠ 0 ∧ base < 2) ∨ base > 36 then
    (.error (.valueError "int() arg 2 must be >= 2 and <= 36"), none)
  else
    let s0 := orig.dropWhile (fun c => c ≠ 0 && cIsSpace c)
    let (neg, s1) :=
      if hd s0 = 43 then (false, s0.drop 1)
      else if hd s0 = 45 then (true, s0.drop 1)
      else (false, s0)
    let c0 := hd s1
    let c1 := hd (s1.drop 1)
    let (b, eif) : Nat × Bool :=
      if base = 0 then
        if c0 ≠ 48 then (10, false)
        else if lower c1 = 120 then (16, false)
        else if lower c1 = 111 then (8, false)
        else if lower c1 = 98 then (2, false)
        else (10, true)
      else (base.toNat, false)
    let s2 :=
      if c0 = 48 ∧ ((b = 16 ∧ lower c1 = 120) ∨ (b = 8 ∧ lower c1 = 111) ∨
          (b = 2 ∧ lower c1 = 98)) then
        let t := s1.drop 2
        if hd t = uscore then t.drop 1 else t
      else s1
    match longFromStringBase pyl lim s2 b with
    | (none, p) => (.error (onError orig b), some p)
    | (some (.error e), _) => (.error e, none)
    | (some (.ok z), p) =>
      if eif ∧ z ≠ [] then (.error (onError orig 0), some p)
      else
        let v : Long := ⟨false, normalize z⟩
        (.ok (if neg then v.flip else v), some p)

/-- `_PyLong_FromBytes(s, len, base)`, longobject.c:3084-3101. -/
def pyLongFromBytes (pyl : List Nat → Py (List Nat)) (lim : Nat) (s : List Nat) (base : Int) :
    Py Long :=
  let (r, e) := pyLongFromString pyl lim s base
  match e, r with
  | none, r => r
  | some [], .ok v => .ok v
  | some _, _ => .error (invalidLiteral base (some (reprBytes (s.take 200))))

/-- `_PyUnicode_TransformDecimalAndSpaceToASCII(unicode)`, unicodeobject.c:9614-9657,
over code points. On a character that is none of these, `'?'` ends the result. -/
def transformLoop : List Nat → List Nat
  | [] => []
  | c :: r =>
    if c < 127 then c :: transformLoop r
    else if uniSpace c then 32 :: transformLoop r
    else match decimalZeros.find? (fun z => z ≤ c && c < z + 10) with
      | some z => (48 + (c - z)) :: transformLoop r
      | none => [63]

def transformDecimalAndSpace (u : List Nat) : List Nat :=
  if u.all (· < 128) then u else transformLoop u

/-- `PyLong_FromUnicodeObject(u, base)`, longobject.c:3104-3130. -/
def pyLongFromUnicodeObject (pyl : List Nat → Py (List Nat)) (lim : Nat) (u : List Nat)
    (base : Int) : Py Long :=
  let asciidig := transformDecimalAndSpace u
  let (r, e) := pyLongFromString pyl lim asciidig base
  match e, r with
  | none, r => r
  | some [], .ok v => .ok v
  | some _, _ =>
    .error (invalidLiteral base (if isAscii u then some (reprStr u) else none))

end PyLean.LongObj
