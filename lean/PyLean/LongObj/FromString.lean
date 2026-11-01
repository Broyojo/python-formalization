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

/-- `convmult`, longobject.c:2810-2819: `convmultmax`, or recomputed when fewer than
`convwidth` digits were grabbed. -/
def convMult (base convwidth convmultmax i : Nat) : Py Nat :=
  if i ≠ convwidth then shortMult base i base else pure convmultmax

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
      let convmult ← convMult base convwidth convmultmax i
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

/-- The conversion chosen once a body is validated, longobject.c:2936-2961. -/
def convBody (pyl : List Nat → Py (List Nat)) (lim : Nat) (body : List Nat) (digits base : Nat) :
    Py (List Nat) :=
  if base &&& (base - 1) = 0 then longFromBinaryBase body digits base
  else if digits > strDigitsThreshold ∧ lim > 0 ∧ digits > lim then
    .error (.valueError (limitToIntMsg lim digits))
  else if digits > 6000 ∧ base = 10 then pyl body
  else longFromNonBinaryBaseAt (fsizeZ digits base) body base

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
          (some (convBody pyl lim body digits base), p)

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

/-- The sign, longobject.c:2989-2995. -/
def signOf (s0 : List Nat) : Bool × List Nat :=
  if hd s0 = 43 then (false, s0.drop 1)
  else if hd s0 = 45 then (true, s0.drop 1)
  else (false, s0)

/-- The radix letter of a base with a prefix. -/
def radixLetter (b : Nat) : Nat := if b = 16 then 120 else if b = 8 then 111 else 98

/-- Base detection, longobject.c:2996-3015: the base and `error_if_nonzero`. -/
def detectBase (base c0 c1 : Nat) : Nat × Bool :=
  if base = 0 then
    if c0 ≠ 48 then (10, false)
    else if lower c1 = 120 then (16, false)
    else if lower c1 = 111 then (8, false)
    else if lower c1 = 98 then (2, false)
    else (10, true)
  else (base, false)

/-- Skipping the radix prefix, longobject.c:3016-3025. -/
def skipPrefix (b : Nat) (s1 : List Nat) : List Nat :=
  let c0 := hd s1
  let c1 := hd (s1.drop 1)
  if c0 = 48 ∧ ((b = 16 ∧ lower c1 = 120) ∨ (b = 8 ∧ lower c1 = 111) ∨
      (b = 2 ∧ lower c1 = 98)) then
    let t := s1.drop 2
    if hd t = uscore then t.drop 1 else t
  else s1

/-- `PyLong_FromString(str, pend, base)`, longobject.c:2973-3076. The second
component is what is stored to `*pend`: `none` when no path wrote it. -/
def pyLongFromString (pyl : List Nat → Py (List Nat)) (lim : Nat) (orig : List Nat)
    (base : Int) : Py Long × Option (List Nat) :=
  if (base ≠ 0 ∧ base < 2) ∨ base > 36 then
    (.error (.valueError "int() arg 2 must be >= 2 and <= 36"), none)
  else
    let s0 := orig.dropWhile (fun c => c ≠ 0 && cIsSpace c)
    let (neg, s1) := signOf s0
    let (b, eif) := detectBase base.toNat (hd s1) (hd (s1.drop 1))
    let s2 := skipPrefix b s1
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

/-! ## Values of digit strings -/

/-- Horner value of the digit characters of `l` in base `b`, skipping underscores. -/
def hv (b acc : Nat) (l : List Nat) : Nat :=
  l.foldl (fun a c => if c = uscore then a else a * b + digitValue c) acc

/-- Number of digit characters. -/
def cnt : List Nat → Nat
  | [] => 0
  | c :: r => (if c = uscore then 0 else 1) + cnt r

def ValidBody (b : Nat) (l : List Nat) : Prop := ∀ c ∈ l, c = uscore ∨ digitValue c < b

theorem validBody_tail {b c : Nat} {r : List Nat} (h : ValidBody b (c :: r)) : ValidBody b r :=
  fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem hv_nil (b acc : Nat) : hv b acc [] = acc := rfl
theorem hv_cons (b acc c : Nat) (l : List Nat) :
    hv b acc (c :: l) = hv b (if c = uscore then acc else acc * b + digitValue c) l := rfl
theorem hv_append (b acc : Nat) (l₁ l₂ : List Nat) : hv b acc (l₁ ++ l₂) = hv b (hv b acc l₁) l₂ :=
  List.foldl_append ..

theorem cnt_append : ∀ a b : List Nat, cnt (a ++ b) = cnt a + cnt b
  | [], _ => by simp [cnt]
  | c :: a, b => by simp [cnt, cnt_append a b, Nat.add_assoc]

theorem cnt_reverse : ∀ a : List Nat, cnt a.reverse = cnt a
  | [] => rfl
  | c :: a => by simp [cnt, cnt_append, cnt_reverse a, Nat.add_comm]

theorem hv_add (b : Nat) : ∀ (l : List Nat) (A k c : Nat),
    hv b (A * b ^ k + c) l = A * b ^ (k + cnt l) + hv b c l
  | [], _, _, _ => by simp [hv_nil, cnt]
  | x :: l, A, k, c => by
    rw [hv_cons, hv_cons]
    by_cases hx : x = uscore
    · simp only [if_pos hx, cnt, Nat.zero_add]
      exact hv_add b l A k c
    · simp only [if_neg hx, cnt]
      have e : (A * b ^ k + c) * b + digitValue x = A * b ^ (k + 1) + (c * b + digitValue x) := by
        rw [Nat.add_mul, Nat.pow_succ, Nat.mul_assoc, Nat.add_assoc]
      rw [e, hv_add b l A (k + 1) _, show k + 1 + cnt l = k + (1 + cnt l) by omega]

/-- Value of the digits read from the right, as `long_from_binary_base` does. -/
def lsb (bpc : Nat) : List Nat → Nat
  | [] => 0
  | c :: r => if c = uscore then lsb bpc r else digitValue c + 2 ^ bpc * lsb bpc r

theorem hv_eq_lsb (bpc : Nat) (l : List Nat) : hv (2 ^ bpc) 0 l = lsb bpc l.reverse := by
  have key : ∀ R : List Nat, hv (2 ^ bpc) 0 R.reverse = lsb bpc R := by
    intro R
    induction R with
    | nil => rfl
    | cons c R ih =>
      rw [List.reverse_cons, hv_append, lsb, ← ih, hv_cons, hv_nil]
      by_cases hc : c = uscore
      · simp only [if_pos hc]
      · simp only [if_neg hc]
        rw [Nat.add_comm, Nat.mul_comm]
  simpa using key l.reverse

/-! ## `long_from_binary_base` -/

theorem binLoop_spec {bpc : Nat} (h1 : 1 ≤ bpc) (h5 : bpc ≤ 5) :
    ∀ (R : List Nat) (accum bits : Nat), ValidBody (2 ^ bpc) R → bits < 30 → accum < 2 ^ bits →
    ∃ out, binLoop bpc R accum bits = .ok out ∧ IsDigits out ∧
      val out = accum + 2 ^ bits * lsb bpc R ∧ out.length ≤ (bits + bpc * cnt R + 29) / 30
  | [], accum, bits, _, hb, ha => by
    by_cases h0 : bits = 0
    · subst h0
      have : accum = 0 := by simpa using ha
      subst this
      exact ⟨[], by simp [binLoop], isDigits_nil, by simp [lsb], by simp⟩
    · have hlt : accum < 2 ^ 30 :=
        Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega))
      have h32 : accum < 2 ^ 32 := by omega
      refine ⟨[accum], ?_, isDigits_cons.2 ⟨hlt, isDigits_nil⟩, by simp [lsb], ?_⟩
      · simp [binLoop, h0, chk32_ok h32, bindOk, pureOk]
      · simp only [cnt, Nat.mul_zero, List.length_singleton]
        omega
  | c :: r, accum, bits, hv', hb, ha => by
    have hr := validBody_tail hv'
    by_cases hc : c = uscore
    · obtain ⟨out, e, a, b, d⟩ := binLoop_spec h1 h5 r accum bits hr hb ha
      have el : lsb bpc (c :: r) = lsb bpc r := by simp [lsb, hc]
      have ec : cnt (c :: r) = cnt r := by simp [cnt, hc]
      rw [el, ec]
      refine ⟨out, ?_, a, b, d⟩
      rw [binLoop, if_pos hc]
      exact e
    · have hk : digitValue c < 2 ^ bpc := (hv' c (by simp)).resolve_left hc
      obtain ⟨k, hkd⟩ : ∃ k, digitValue c = k := ⟨_, rfl⟩
      rw [hkd] at hk
      obtain ⟨a, ha2⟩ : ∃ a, accum + 2 ^ bits * k = a := ⟨_, rfl⟩
      have hlt : a < 2 ^ (bits + bpc) := by
        rw [← ha2, Nat.pow_add]
        have : 2 ^ bits * (k + 1) ≤ 2 ^ bits * 2 ^ bpc := Nat.mul_le_mul_left _ hk
        rw [Nat.mul_add] at this
        omega
      have h64 : a < 2 ^ 64 :=
        Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega))
      have hor : accum ||| (k <<< bits) = a := by rw [or_shift_eq ha, ha2]
      have el : lsb bpc (c :: r) = k + 2 ^ bpc * lsb bpc r := by simp [lsb, hc, hkd]
      have ec : bpc * cnt (c :: r) = bpc * cnt r + bpc := by
        simp only [cnt, if_neg hc]
        rw [Nat.add_comm, Nat.mul_add, Nat.mul_one]
      rw [el, ec]
      obtain ⟨L, hL⟩ : ∃ L, lsb bpc r = L := ⟨_, rfl⟩
      rw [hL]
      have htarget : accum + 2 ^ bits * (k + 2 ^ bpc * L) = a + 2 ^ (bits + bpc) * L := by
        rw [Nat.mul_add, ← Nat.add_assoc, ha2, Nat.pow_add, Nat.mul_assoc]
      rw [htarget]
      by_cases hge : bits + bpc ≥ 30
      · have hq : a >>> 30 < 2 ^ (bits + bpc - 30) := by
          rw [shr30]
          apply Nat.div_lt_of_lt_mul
          rw [← Nat.pow_add, show 30 + (bits + bpc - 30) = bits + bpc by omega]
          exact hlt
        obtain ⟨out, e, h3, h4, h6⟩ :=
          binLoop_spec h1 h5 r (a >>> 30) (bits + bpc - 30) hr (by omega) hq
        refine ⟨(a &&& MASK) :: out, ?_, isDigits_cons.2 ⟨?_, h3⟩, ?_, ?_⟩
        · rw [binLoop, if_neg hc]
          simp only [hkd, hor, chk64_ok h64, bindOk, hge, ge_iff_le, if_true, e, pureOk]
        · rw [and30]; exact Nat.mod_lt _ (by decide)
        · rw [val_cons, h4, hL, and30, shr30, Nat.mul_add, ← Nat.add_assoc, Nat.mod_add_div,
            ← Nat.mul_assoc, ← Nat.pow_add, show 30 + (bits + bpc - 30) = bits + bpc by omega]
        · simp only [List.length_cons]
          omega
      · have hb2 : bits + bpc < 30 := by omega
        obtain ⟨out, e, h3, h4, h6⟩ := binLoop_spec h1 h5 r a (bits + bpc) hr hb2 hlt
        refine ⟨out, ?_, h3, ?_, ?_⟩
        · rw [binLoop, if_neg hc]
          simp only [hkd, hor, chk64_ok h64, bindOk, hge, ge_iff_le, if_false, e]
        · rw [h4, hL]
        · omega

theorem bitsPerChar_eq : ∀ b, b = 2 ∨ b = 4 ∨ b = 8 ∨ b = 16 ∨ b = 32 →
    1 ≤ bitsPerChar b ∧ bitsPerChar b ≤ 5 ∧ b = 2 ^ bitsPerChar b := by
  rintro b (rfl | rfl | rfl | rfl | rfl) <;> decide

/-- `long_from_binary_base` is exact on validated strings; no carry leaves its C type,
and the digits written fit the allocation. -/
theorem longFromBinaryBase_spec {body : List Nat} {base : Nat} (hbase : 1 ≤ bitsPerChar base ∧
    bitsPerChar base ≤ 5 ∧ base = 2 ^ bitsPerChar base) (hv' : ValidBody base body)
    (hd : cnt body ≤ (ssizeMax - (30 - 1)) / bitsPerChar base) :
    ∃ z, longFromBinaryBase body (cnt body) base = .ok z ∧ IsDigits z ∧ val z = hv base 0 body := by
  obtain ⟨h1, h5, hb⟩ := hbase
  obtain ⟨bpc, hbpc⟩ : ∃ bpc, bitsPerChar base = bpc := ⟨_, rfl⟩
  rw [hbpc] at h1 h5 hb hd
  have hR : ValidBody (2 ^ bpc) body.reverse := by
    intro c hc
    have := hv' c (List.mem_reverse.1 hc)
    rwa [hb] at this
  obtain ⟨out, e, hdig, hval, hlen⟩ := binLoop_spec h1 h5 body.reverse 0 0 hR (by decide) (by decide)
  rw [cnt_reverse] at hlen
  have hmul : cnt body * bpc + 29 ≤ ssizeMax := by
    have := Nat.mul_le_mul_right bpc hd
    have h2 := Nat.div_mul_le_self (ssizeMax - (30 - 1)) bpc
    have : ssizeMax ≥ 29 := by decide
    omega
  have hn : (cnt body * bpc + 30 - 1) / 30 ≤ maxLongDigits := by
    have : ssizeMax / 30 = maxLongDigits := by decide
    rw [← this]
    exact Nat.div_le_div_right (by omega)
  have hlen2 : out.length ≤ (cnt body * bpc + 30 - 1) / 30 := by
    rw [Nat.mul_comm]
    simpa using hlen
  refine ⟨out ++ List.replicate ((cnt body * bpc + 30 - 1) / 30 - out.length) 0, ?_, ?_, ?_⟩
  · unfold longFromBinaryBase
    rw [hbpc, if_neg (Nat.not_lt.2 hd)]
    simp only [longAlloc_ok hn, bindOk, e, if_pos hlen2, pureOk]
  · exact isDigits_append.2 ⟨hdig, isDigits_replicate_zero _⟩
  · rw [val_append, val_replicate_zero, Nat.mul_zero, Nat.add_zero, hval, hb, hv_eq_lsb]
    simp

/-! ## `long_from_non_binary_base` -/

theorem mulLoop_spec {m : Nat} (hm : m ≤ 2 ^ 30) : ∀ (z : List Nat) (c : Nat), IsDigits z →
    c < 2 ^ 30 → ∃ z' c', mulLoop m z c = .ok (z', c') ∧ z'.length = z.length ∧ IsDigits z' ∧
      c' < 2 ^ 30 ∧ val z' + 2 ^ (30 * z.length) * c' = val z * m + c
  | [], c, _, hc => ⟨[], c, rfl, rfl, isDigits_nil, hc, by simp⟩
  | d :: ds, c, hd, hc => by
    obtain ⟨hd0, hds⟩ := isDigits_cons.1 hd
    have ht : d * m ≤ (2 ^ 30 - 1) * 2 ^ 30 := Nat.mul_le_mul (by omega) hm
    obtain ⟨t, htd⟩ : ∃ t, d * m = t := ⟨_, rfl⟩
    obtain ⟨c1, hc1⟩ : ∃ c1, c + t = c1 := ⟨_, rfl⟩
    rw [htd] at ht
    have h64t : t < 2 ^ 64 := by omega
    have h64c : c1 < 2 ^ 64 := by omega
    have hq : c1 >>> 30 < 2 ^ 30 := by
      rw [shr30]
      apply Nat.div_lt_of_lt_mul
      omega
    obtain ⟨z', c', e, h1, h2, h3, h4⟩ := mulLoop_spec hm ds _ hds hq
    refine ⟨(c1 &&& MASK) :: z', c', ?_, by simp [h1], isDigits_cons.2 ⟨?_, h2⟩, h3, ?_⟩
    · simp only [mulLoop, htd, chk64_ok h64t, bindOk, hc1, chk64_ok h64c, e, pureOk]
    · rw [and30]; exact Nat.mod_lt _ (by decide)
    · obtain ⟨V, hV⟩ : ∃ V, val ds = V := ⟨_, rfl⟩
      rw [hV] at h4
      have hp : 2 ^ (30 * (ds.length + 1)) = 2 ^ 30 * 2 ^ (30 * ds.length) := by
        rw [show 30 * (ds.length + 1) = 30 + 30 * ds.length by omega, Nat.pow_add]
      rw [val_cons, val_cons, hV, List.length_cons, hp, and30, Nat.add_assoc, Nat.mul_assoc,
        ← Nat.mul_add, h4, shr30]
      have e2 : (d + 2 ^ 30 * V) * m = t + 2 ^ 30 * (V * m) := by
        rw [Nat.add_mul, htd, Nat.mul_assoc]
      rw [e2, Nat.mul_add]
      have := Nat.mod_add_div c1 (2 ^ 30)
      omega

theorem shortMult_spec {base : Nat} : ∀ (i k : Nat), base ^ (k + i + 1) < 2 ^ 64 → 1 ≤ base →
    shortMult base (i + 1) (base ^ (k + 1)) = .ok (base ^ (k + i + 1))
  | 0, k, _, _ => by simp [shortMult]
  | i + 1, k, h, hb => by
    have hle : base ^ (k + 1 + 1) ≤ base ^ (k + (i + 1) + 1) :=
      Nat.pow_le_pow_right hb (by omega)
    have h2 : base ^ (k + 1) * base < 2 ^ 64 := by
      have e : base ^ (k + 1) * base = base ^ (k + 1 + 1) := (Nat.pow_succ ..).symm
      rw [e]; omega
    have ih := shortMult_spec i (k + 1) (by
      rw [show k + 1 + i + 1 = k + (i + 1) + 1 by omega]; exact h) hb
    rw [show i + 1 + 1 = i + 2 from rfl, shortMult]
    simp only [chk64_ok h2, bindOk]
    rw [← Nat.pow_succ, ih, show k + 1 + i + 1 = k + (i + 1) + 1 by omega]

theorem grab_spec {base cw : Nat} (hb : 2 ≤ base) (hcw : base ^ cw ≤ 2 ^ 30) :
    ∀ (r : List Nat) (i c : Nat), ValidBody base r → 1 ≤ i → i ≤ cw → c < base ^ i →
    ∃ i' c' rest, grab base cw r i c = .ok (i', c', rest) ∧ i ≤ i' ∧ i' ≤ cw ∧ c' < base ^ i' ∧
      rest.length ≤ r.length ∧ ValidBody base rest ∧ cnt r = (i' - i) + cnt rest ∧
      ∀ Z, hv base (Z * base ^ i + c) r = hv base (Z * base ^ i' + c') rest
  | [], i, c, hv', _, h2, h3 =>
    ⟨i, c, [], rfl, Nat.le_refl _, h2, h3, Nat.le_refl _, hv', by simp [cnt], fun _ => rfl⟩
  | x :: r, i, c, hv', h1, h2, h3 => by
    have hr := validBody_tail hv'
    by_cases hi : i < cw
    · by_cases hx : x = uscore
      · obtain ⟨i', c', rest, e, a1, a2, a3, a4, a5, a6, a7⟩ :=
          grab_spec hb hcw r i c hr h1 h2 h3
        refine ⟨i', c', rest, ?_, a1, a2, a3, by simp; omega, a5, ?_, ?_⟩
        · rw [grab, if_pos hi, if_pos hx]; exact e
        · simp only [cnt, if_pos hx, Nat.zero_add]; exact a6
        · intro Z
          rw [hv_cons, if_pos hx]
          exact a7 Z
      · have hd : digitValue x < base := (hv' x (by simp)).resolve_left hx
        have hlt : c * base + digitValue x < base ^ (i + 1) := by
          rw [Nat.pow_succ]
          have : (c + 1) * base ≤ base ^ i * base := Nat.mul_le_mul_right _ h3
          rw [Nat.add_mul] at this
          omega
        have hle : base ^ (i + 1) ≤ base ^ cw := Nat.pow_le_pow_right (by omega) hi
        have h64 : c * base + digitValue x < 2 ^ 64 := by omega
        obtain ⟨i', c', rest, e, a1, a2, a3, a4, a5, a6, a7⟩ :=
          grab_spec hb hcw r (i + 1) _ hr (by omega) hi hlt
        refine ⟨i', c', rest, ?_, by omega, a2, a3, by simp; omega, a5, ?_, ?_⟩
        · rw [grab, if_pos hi, if_neg hx]
          simp only [chk64_ok h64, bindOk]
          exact e
        · simp only [cnt, if_neg hx]; omega
        · intro Z
          rw [hv_cons, if_neg hx, ← a7 Z]
          congr 1
          rw [Nat.add_mul, Nat.pow_succ, Nat.mul_assoc, Nat.add_assoc]
    · have hic : i = cw := by omega
      subst hic
      refine ⟨i, c, x :: r, ?_, Nat.le_refl _, Nat.le_refl _, h3, Nat.le_refl _, hv', by simp, ?_⟩
      · rw [grab, if_neg hi]
      · intro _; rfl

theorem conv_tables : ∀ b, b < 37 → 2 ≤ b → b &&& (b - 1) ≠ 0 →
    1 ≤ convwidthBase.getD b 0 ∧ b ^ convwidthBase.getD b 0 = convmultmaxBase.getD b 0 ∧
      convmultmaxBase.getD b 0 ≤ 2 ^ 30 := by decide

theorem nbLoop_spec {base cw m : Nat} (hb : 2 ≤ base) (hcw0 : 1 ≤ cw) (hm : base ^ cw = m)
    (hm2 : m ≤ 2 ^ 30) : ∀ (f : Nat) (p z : List Nat) (sz : Nat), p.length < f → ValidBody base p →
      IsDigits z → (z ≠ [] → 0 < val z) → z.length ≤ sz → z.length + cnt p ≤ maxLongDigits →
      ∃ z', nbLoop base cw m f p z sz = .ok z' ∧ IsDigits z' ∧ (z' ≠ [] → 0 < val z') ∧
        val z' = hv base (val z) p
  | 0, _, _, _, h, _, _, _, _, _ => by omega
  | f + 1, [], z, sz, _, _, hd, hz, _, _ => ⟨z, by simp [nbLoop], hd, hz, rfl⟩
  | f + 1, x :: r, z, sz, hf, hv', hd, hz, hs, hmax => by
    have hr := validBody_tail hv'
    by_cases hx : x = uscore
    · have hc : cnt (x :: r) = cnt r := by simp [cnt, hx]
      obtain ⟨z', e, a, b, c⟩ := nbLoop_spec hb hcw0 hm hm2 f r z sz (by simpa using hf) hr hd hz hs
        (by omega)
      refine ⟨z', ?_, a, b, ?_⟩
      · rw [nbLoop, if_pos hx]; exact e
      · rw [c, hv_cons, if_pos hx]
    · have hdv : digitValue x < base := (hv' x (by simp)).resolve_left hx
      have hbase1 : 1 ≤ base := by omega
      obtain ⟨i, c, rest, e1, a1, a2, a3, a4, a5, a6, a7⟩ :=
        grab_spec hb (by rw [hm]; exact hm2) r 1 (digitValue x) hr (by omega) hcw0 (by simpa using hdv)
      have hile : base ^ i ≤ m := by rw [← hm]; exact Nat.pow_le_pow_right hbase1 a2
      have hconv : convMult base cw m i = (.ok (base ^ i) : Py Nat) := by
        unfold convMult
        by_cases hi : i ≠ cw
        · rw [if_pos hi]
          obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
          have := shortMult_spec (base := base) j 0 (by
            rw [show 0 + j + 1 = j + 1 by omega]
            exact Nat.lt_of_le_of_lt hile (by omega)) hbase1
          simpa using this
        · have : i = cw := by omega
          subst this
          rw [if_neg hi, hm]
          rfl
      have hcC : c < 2 ^ 30 := Nat.lt_of_lt_of_le a3 (Nat.le_trans hile hm2)
      obtain ⟨z1, c2, e2, h1, h2, h3, h4⟩ := mulLoop_spec (Nat.le_trans hile hm2) z c hd hcC
      have hcnt : cnt (x :: r) = 1 + cnt r := by simp [cnt, hx]
      have hgoal : hv base (val z) (x :: r) = hv base (val z * base ^ i + c) rest := by
        rw [hv_cons, if_neg hx, ← a7 (val z)]
        simp
      have hrlen : rest.length < f := by simp at hf; omega
      by_cases hc2 : c2 ≠ 0
      · have hdig : chkDigit c2 = .ok c2 := if_pos h3
        have hval : val (z1 ++ [c2]) = val z * base ^ i + c := by
          rw [val_append, ← h4, h1]
          simp
        have hdz : IsDigits (z1 ++ [c2]) :=
          isDigits_append.2 ⟨h2, isDigits_cons.2 ⟨h3, isDigits_nil⟩⟩
        have hpos : (z1 ++ [c2]) ≠ [] → 0 < val (z1 ++ [c2]) := by
          intro _
          rw [val_append]
          have : 0 < 2 ^ (30 * z1.length) * val [c2] :=
            Nat.mul_pos (Nat.pow_pos (by decide)) (by simp; omega)
          omega
        have hlen : (z1 ++ [c2]).length = z.length + 1 := by simp [h1]
        by_cases hlt : z1.length < sz
        · obtain ⟨z', e3, b1, b2, b3⟩ := nbLoop_spec hb hcw0 hm hm2 f rest (z1 ++ [c2]) sz hrlen a5
            hdz hpos (by omega) (by omega)
          refine ⟨z', ?_, b1, b2, ?_⟩
          · rw [nbLoop, if_neg hx]
            simp only [e1, bindOk, hconv, e2, hc2, hdig, if_true, ne_eq, not_false_eq_true, hlt]
            exact e3
          · rw [b3, hval, hgoal]
        · have hsz : sz = z.length := by omega
          have halloc : longAlloc (sz + 1) = .ok () := longAlloc_ok (by omega)
          obtain ⟨z', e3, b1, b2, b3⟩ := nbLoop_spec hb hcw0 hm hm2 f rest (z1 ++ [c2]) (sz + 1)
            hrlen a5 hdz hpos (by omega) (by omega)
          refine ⟨z', ?_, b1, b2, ?_⟩
          · rw [nbLoop, if_neg hx]
            simp only [e1, bindOk, hconv, e2, hc2, hdig, if_true, ne_eq, not_false_eq_true, hlt,
              if_false, halloc]
            exact e3
          · rw [b3, hval, hgoal]
      · have hc0 : c2 = 0 := by omega
        subst hc0
        have hval : val z1 = val z * base ^ i + c := by
          simpa using h4
        have hpos : z1 ≠ [] → 0 < val z1 := by
          intro hne
          have hzne : z ≠ [] := by
            intro h0; apply hne; rw [h0] at h1; exact List.length_eq_zero_iff.1 h1
          have := hz hzne
          rw [hval]
          have : 0 < val z * base ^ i := Nat.mul_pos this (Nat.pow_pos (by omega))
          omega
        obtain ⟨z', e3, b1, b2, b3⟩ := nbLoop_spec hb hcw0 hm hm2 f rest z1 sz hrlen a5 h2 hpos
          (by omega) (by omega)
        refine ⟨z', ?_, b1, b2, ?_⟩
        · rw [nbLoop, if_neg hx]
          simp only [e1, bindOk, hconv, e2, ne_eq, not_true_eq_false, if_false]
          exact e3
        · rw [b3, hval, hgoal]

/-- `long_from_non_binary_base` is exact for every allocation `sizeZ`, which covers the
reallocation branch the source calls extremely rare. -/
theorem longFromNonBinaryBaseAt_spec {body : List Nat} {base sz : Nat} (hb : 2 ≤ base)
    (h36 : base < 37) (hnp : base &&& (base - 1) ≠ 0) (hv' : ValidBody base body)
    (hsz : sz ≤ maxLongDigits) (hc : cnt body ≤ maxLongDigits) :
    ∃ z, longFromNonBinaryBaseAt sz body base = .ok z ∧ IsDigits z ∧ (z ≠ [] → 0 < val z) ∧
      val z = hv base 0 body := by
  obtain ⟨t1, t2, t3⟩ := conv_tables base h36 hb hnp
  obtain ⟨z, e, a, b, c⟩ := nbLoop_spec hb t1 t2 t3 (body.length + 1) body [] sz (by omega) hv'
    isDigits_nil (fun h => absurd rfl h) (by simp) (by simpa using hc)
  refine ⟨z, ?_, a, b, by simpa using c⟩
  unfold longFromNonBinaryBaseAt
  rw [if_neg (Nat.not_lt.2 hsz)]
  simp only [longAlloc_ok hsz, bindOk]
  exact e

/-! ## The grammar of `int()`

"Optionally, the string can be preceded by `+` or `-` (with no space in between),
have leading zeros, be surrounded by whitespace, and have single underscores
interspersed between digits." (library/functions.rst, `int`). -/

/-- `digit (["_"] digit)*`. -/
inductive DigitPart (b : Nat) : List Nat → Prop
  | one {c : Nat} : digitValue c < b → DigitPart b [c]
  | cons {c : Nat} {r : List Nat} : digitValue c < b → DigitPart b r → DigitPart b (c :: r)
  | us {c : Nat} {r : List Nat} : digitValue c < b → DigitPart b r →
      DigitPart b (c :: uscore :: r)

/-- `0b`, `0B`, `0o`, `0O`, `0x`, `0X`, each with one optional underscore after it. -/
def IsRadixPrefix (b : Nat) (pre : List Nat) : Prop :=
  (b = 2 ∨ b = 8 ∨ b = 16) ∧ ∃ x, lower x = radixLetter b ∧ (pre = [48, x] ∨ pre = [48, x, uscore])

/-- How base `base` reads a prefix `pre` and digits `body`: `rb` is the radix. For base
0 "the actual base is 2, 8, 10, or 16 as determined by the prefix", and it "disallows
leading zeros", except that the value may still be zero. -/
inductive LitForm : Nat → List Nat → Nat → List Nat → Prop
  | plain {b : Nat} {body : List Nat} : b ≠ 0 → LitForm b [] b body
  | radix {b : Nat} {pre body : List Nat} : b ≠ 0 → IsRadixPrefix b pre → LitForm b pre b body
  | autoRadix {rb : Nat} {pre body : List Nat} : IsRadixPrefix rb pre → LitForm 0 pre rb body
  | autoDec {body : List Nat} : hd body ≠ 48 → LitForm 0 [] 10 body
  | autoZero {body : List Nat} : (∀ c ∈ body, c = uscore ∨ digitValue c = 0) →
      LitForm 0 [] 10 body

def Spaces (l : List Nat) : Prop := ∀ c ∈ l, cIsSpace c = true

/-- `s` is an integer literal for `base`: surrounding space, a sign, a prefix, digits. -/
def IsLit (base : Nat) (s : List Nat) (neg : Bool) (rb : Nat) (body : List Nat) : Prop :=
  ∃ ws1 sg pre ws2, s = ws1 ++ sg ++ pre ++ body ++ ws2 ∧ Spaces ws1 ∧ Spaces ws2 ∧
    ((sg = [] ∧ neg = false) ∨ (sg = [43] ∧ neg = false) ∨ (sg = [45] ∧ neg = true)) ∧
    LitForm base pre rb body ∧ DigitPart rb body

/-- The value of a literal. -/
def litValue (neg : Bool) (rb : Nat) (body : List Nat) : Int :=
  if neg then -(hv rb 0 body : Int) else hv rb 0 body

/-- `pylong_int_from_string` meets its contract on one validated decimal body. -/
def HookAt (pyl : List Nat → Py (List Nat)) (lim : Nat) (body : List Nat) : Prop :=
  cnt body > 6000 → (lim = 0 ∨ cnt body ≤ lim) → pyl body = .ok (digitsOf (hv 10 0 body))

/-- `pylong_int_from_string` meets its contract on validated bodies of bytes, of fewer
than `N` digits. -/
def HookOK (pyl : List Nat → Py (List Nat)) (lim N : Nat) : Prop :=
  ∀ body, DigitPart 10 body → (∀ c ∈ body, c < 256) → cnt body < N → HookAt pyl lim body

theorem space_dv : ∀ c, cIsSpace c = true → digitValue c = 37 := by
  intro c h
  have : (9 ≤ c ∧ c ≤ 13) ∨ c = 32 := by
    simpa [cIsSpace, StrSearch.byteSpace] using h
  rcases this with ⟨h1, h2⟩ | rfl
  · have : c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> decide
  · decide

theorem space_ne_zero {c : Nat} (h : cIsSpace c = true) : c ≠ 0 := by
  rintro rfl
  revert h
  decide

theorem uscore_dv : digitValue uscore = 37 := by decide

theorem lower_letter {c L : Nat} (h : lower c = L) (hL : L = 120 ∨ L = 111 ∨ L = 98) :
    digitValue c ≥ 10 ∧ c ≠ uscore ∧ cIsSpace c = false ∧ c ≠ 0 := by
  have hc : c = L ∨ c + 32 = L := by
    unfold lower at h
    split at h <;> omega
  rcases hL with rfl | rfl | rfl <;> rcases hc with rfl | hc
  all_goals first
    | decide
    | (have : c = 88 := by omega
       subst this; decide)
    | (have : c = 79 := by omega
       subst this; decide)
    | (have : c = 66 := by omega
       subst this; decide)

theorem radixLetter_eq {b : Nat} (h : b = 2 ∨ b = 8 ∨ b = 16) :
    radixLetter b = 120 ∨ radixLetter b = 111 ∨ radixLetter b = 98 := by
  rcases h with rfl | rfl | rfl <;> decide

theorem radix_dv_ge {b c : Nat} (h : b = 2 ∨ b = 8 ∨ b = 16) (hl : lower c = radixLetter b) :
    digitValue c ≥ b := by
  rcases h with rfl | rfl | rfl
  · have := (lower_letter hl (by decide)).1
    omega
  · have hc : c = 111 ∨ c + 32 = 111 := by
      have : lower c = 111 := hl
      unfold lower at this
      split at this <;> omega
    rcases hc with rfl | hc
    · decide
    · have : c = 79 := by omega
      subst this; decide
  · have hc : c = 120 ∨ c + 32 = 120 := by
      have : lower c = 120 := hl
      unfold lower at this
      split at this <;> omega
    rcases hc with rfl | hc
    · decide
    · have : c = 88 := by omega
      subst this; decide

theorem digitPart_ne_nil {b : Nat} {l : List Nat} (h : DigitPart b l) : l ≠ [] := by
  cases h <;> simp

theorem digitPart_head {b : Nat} {l : List Nat} (h : DigitPart b l) :
    ∃ c r, l = c :: r ∧ digitValue c < b := by
  cases h with
  | one h => exact ⟨_, _, rfl, h⟩
  | cons h _ => exact ⟨_, _, rfl, h⟩
  | us h _ => exact ⟨_, _, rfl, h⟩

theorem digitPart_valid {b : Nat} {l : List Nat} (h : DigitPart b l) : ValidBody b l := by
  induction h with
  | one h =>
    intro x hx
    simp only [List.mem_singleton] at hx
    subst hx; exact Or.inr h
  | cons h _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inr h
    · exact ih x hx
  | us h _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inr h
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inl rfl
      · exact ih x hx

/-- The character after the first of a literal, seen through the C terminator. -/
theorem second_char {b : Nat} {body ws : List Nat} (hb : b ≤ 36) (h : DigitPart b body)
    (hws : Spaces ws) : let c := hd ((body ++ ws).drop 1)
      c = 0 ∨ c = uscore ∨ digitValue c < b ∨ cIsSpace c = true := by
  intro c
  cases h with
  | one _ =>
    cases ws with
    | nil => exact Or.inl rfl
    | cons x ws => exact Or.inr (Or.inr (Or.inr (hws x (by simp))))
  | cons _ h2 =>
    obtain ⟨y, r, rfl, hy⟩ := digitPart_head h2
    exact Or.inr (Or.inr (Or.inl hy))
  | us _ _ => exact Or.inr (Or.inl rfl)

theorem scan_digitPart {b : Nat} (hb : b ≤ 36) {ws : List Nat} (hws : Spaces ws) {body : List Nat}
    (h : DigitPart b body) : ∀ q prev digits, ∃ q' last,
      scan b q (body ++ ws) prev digits = .stop (digits + cnt body) last q' ws ∧ last ≠ uscore := by
  have hstop : ∀ q prev digits, ∃ q', scan b q ws prev digits = .stop digits prev q' ws := by
    intro q prev digits
    cases ws with
    | nil => exact ⟨_, rfl⟩
    | cons x ws =>
      have h1 := hws x (by simp)
      have h2 := space_dv x h1
      have hne : ¬ x = uscore := by
        rintro rfl; revert h1; decide
      have hn : ¬ (digitValue x < b ∨ x = uscore) := by omega
      exact ⟨_, by rw [scan, if_neg hn]⟩
  induction h with
  | @one c hc =>
    intro q prev digits
    have hne : c ≠ uscore := by
      rintro rfl
      rw [uscore_dv] at hc
      omega
    obtain ⟨q', e⟩ := hstop (c :: ws) c (digits + 1)
    refine ⟨q', c, ?_, hne⟩
    simp only [List.singleton_append]
    rw [scan, if_pos (Or.inl hc), if_neg hne]
    simpa [cnt, hne] using e
  | @cons c r hc _ ih =>
    intro q prev digits
    have hne : c ≠ uscore := by
      rintro rfl
      rw [uscore_dv] at hc
      omega
    obtain ⟨q', last, e, hl⟩ := ih (c :: (r ++ ws)) c (digits + 1)
    refine ⟨q', last, ?_, hl⟩
    simp only [List.cons_append]
    rw [scan, if_pos (Or.inl hc), if_neg hne, e]
    simp only [cnt, if_neg hne]
    congr 1
    omega
  | @us c r hc _ ih =>
    intro q prev digits
    have hne : c ≠ uscore := by
      rintro rfl
      rw [uscore_dv] at hc
      omega
    obtain ⟨q', last, e, hl⟩ := ih (uscore :: (r ++ ws)) uscore (digits + 1)
    refine ⟨q', last, ?_, hl⟩
    simp only [List.cons_append]
    rw [scan, if_pos (Or.inl hc), if_neg hne, scan, if_pos (Or.inr rfl), if_pos rfl, if_neg hne, e]
    simp only [cnt, if_neg hne, if_true]
    congr 1
    omega

theorem dropWhile_spaces {ws : List Nat} (h : Spaces ws) :
    ws.dropWhile (fun c => c ≠ 0 && cIsSpace c) = [] := by
  induction ws with
  | nil => rfl
  | cons c ws ih =>
    have h1 := h c (by simp)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [List.dropWhile_cons, if_pos (by simp [h1, space_ne_zero h1])]
    exact h2

theorem longFromStringBase_lit (pyl : List Nat → Py (List Nat)) (lim : Nat) {b : Nat}
    (hb : b ≤ 36) {body ws : List Nat} (h : DigitPart b body) (hws : Spaces ws) :
    longFromStringBase pyl lim (body ++ ws) b = (some (convBody pyl lim body (cnt body) b), []) := by
  obtain ⟨c, r, hbody, hc⟩ := digitPart_head h
  have hne : c ≠ uscore := by
    rintro rfl
    rw [uscore_dv] at hc
    omega
  obtain ⟨q', last, e, hl⟩ := scan_digitPart hb hws h (body ++ ws) 0 0
  have hhd : hd (body ++ ws) ≠ uscore := by rw [hbody]; exact hne
  have hlen : ¬ (body ++ ws).length = ws.length := by
    rw [hbody]; simp; omega
  have htake : (body ++ ws).take ((body ++ ws).length - ws.length) = body := by
    simp
  unfold longFromStringBase
  rw [if_neg hhd, e]
  simp only [Nat.zero_add, if_neg hl, if_neg hlen, dropWhile_spaces hws, htake]
  simp only [hd, List.headD_nil, ne_eq, not_true_eq_false, if_false]

theorem normal_of_lit {z : List Nat} (hd' : IsDigits z)
    {V : Nat} (hv' : val z = V) (neg : Bool) :
    (if neg then (⟨false, normalize z⟩ : Long).flip else ⟨false, normalize z⟩) =
      Long.ofInt (if neg then -(V : Int) else V) := by
  have h1 : (⟨false, normalize z⟩ : Long) = Long.ofInt (V : Int) := by
    rw [Long.ofInt_natCast, digitsOf_normalize hd', hv']
  rw [h1]
  cases neg with
  | false => simp
  | true => simp [Long.ofInt_neg]

theorem hv_zero_acc {b : Nat} (hb : 1 ≤ b) : ∀ (l : List Nat) (acc : Nat), acc ≤ hv b acc l
  | [], _ => Nat.le_refl _
  | x :: l, acc => by
    rw [hv_cons]
    by_cases hx : x = uscore
    · rw [if_pos hx]
      exact hv_zero_acc hb l acc
    · rw [if_neg hx]
      have h := hv_zero_acc hb l (acc * b + digitValue x)
      have : acc ≤ acc * b := Nat.le_mul_of_pos_right _ (by omega)
      omega

theorem all_zero_of_hv {b : Nat} (hb : 1 ≤ b) : ∀ (l : List Nat) (acc : Nat), hv b acc l = 0 →
    ∀ c ∈ l, c = uscore ∨ digitValue c = 0
  | [], _, _, _, h => by simp at h
  | x :: l, acc, h0, c, hc => by
    rw [hv_cons] at h0
    by_cases hx : x = uscore
    · rw [if_pos hx] at h0
      rcases List.mem_cons.1 hc with rfl | hc
      · exact Or.inl hx
      · exact all_zero_of_hv hb l _ h0 c hc
    · rw [if_neg hx] at h0
      have h1 := hv_zero_acc hb l (acc * b + digitValue x)
      rw [h0] at h1
      rcases List.mem_cons.1 hc with rfl | hc
      · right; omega
      · exact all_zero_of_hv hb l _ h0 c hc

theorem hv_of_all_zero {b : Nat} : ∀ (l : List Nat), (∀ c ∈ l, c = uscore ∨ digitValue c = 0) →
    ∀ acc, hv b (acc * 1) l = acc * b ^ cnt l := by
  intro l h
  induction l with
  | nil => intro acc; simp [hv_nil, cnt]
  | cons x l ih =>
    intro acc
    have hl : ∀ c ∈ l, c = uscore ∨ digitValue c = 0 := fun c hc => h c (List.mem_cons_of_mem _ hc)
    rw [hv_cons]
    by_cases hx : x = uscore
    · simp only [if_pos hx, cnt, Nat.zero_add]
      exact ih hl acc
    · have hd0 : digitValue x = 0 := (h x (by simp)).resolve_left hx
      simp only [if_neg hx, hd0, Nat.add_zero, cnt]
      have := ih hl (acc * b)
      simp only [Nat.mul_one] at this ⊢
      rw [this, Nat.mul_assoc, ← Nat.pow_succ', Nat.add_comm]

/-! ### Soundness: every literal is read as its value -/

theorem not_letter {b c : Nat} (hb : b = 2 ∨ b = 8 ∨ b = 16)
    (hc : c = 0 ∨ c = uscore ∨ digitValue c < b ∨ cIsSpace c = true) :
    lower c ≠ radixLetter b := by
  intro h
  have hL := lower_letter h (radixLetter_eq hb)
  have hge := radix_dv_ge hb h
  rcases hc with rfl | rfl | h1 | h1
  · exact hL.2.2.2 rfl
  · exact hL.2.1 rfl
  · omega
  · rw [hL.2.2.1] at h1; simp at h1

theorem not_letter10 {c L : Nat} (hL : L = 120 ∨ L = 111 ∨ L = 98)
    (hc : c = 0 ∨ c = uscore ∨ digitValue c < 10 ∨ cIsSpace c = true) : lower c ≠ L := by
  intro h
  have h2 := lower_letter h hL
  rcases hc with rfl | rfl | h1 | h1
  · exact h2.2.2.2 rfl
  · exact h2.2.1 rfl
  · omega
  · rw [h2.2.2.1] at h1; simp at h1

theorem dv_ne {c : Nat} (h : digitValue c < 37) :
    c ≠ uscore ∧ c ≠ 43 ∧ c ≠ 45 ∧ cIsSpace c = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl; revert h; decide
  · rintro rfl; revert h; decide
  · rintro rfl; revert h; decide
  · cases hs : cIsSpace c with
    | false => rfl
    | true =>
      have := space_dv c hs
      omega

theorem skip_plain {b : Nat} {body ws : List Nat} (hb36 : b ≤ 36) (hne : ¬ b = 10 → True)
    (hdp : DigitPart b body) (hws : Spaces ws) : skipPrefix b (body ++ ws) = body ++ ws := by
  have h2 := second_char hb36 hdp hws
  unfold skipPrefix
  simp only
  rw [if_neg]
  rintro ⟨_, h3⟩
  rcases h3 with ⟨rfl, h3⟩ | ⟨rfl, h3⟩ | ⟨rfl, h3⟩
  · exact not_letter (Or.inr (Or.inr rfl)) h2 h3
  · exact not_letter (Or.inr (Or.inl rfl)) h2 h3
  · exact not_letter (Or.inl rfl) h2 h3

theorem skip_radix {b : Nat} {pre body ws : List Nat} (hb36 : b ≤ 36) (hp : IsRadixPrefix b pre)
    (hdp : DigitPart b body) : skipPrefix b (pre ++ body ++ ws) = body ++ ws := by
  obtain ⟨hb, x, hx, hpre⟩ := hp
  obtain ⟨c, r, rfl, hc⟩ := digitPart_head hdp
  have hne := (dv_ne (by omega : digitValue c < 37)).1
  have hcond : (48 : Nat) = 48 ∧ ((b = 16 ∧ lower x = 120) ∨ (b = 8 ∧ lower x = 111) ∨
      (b = 2 ∧ lower x = 98)) := by
    refine ⟨rfl, ?_⟩
    rcases hb with rfl | rfl | rfl
    · exact Or.inr (Or.inr ⟨rfl, hx⟩)
    · exact Or.inr (Or.inl ⟨rfl, hx⟩)
    · exact Or.inl ⟨rfl, hx⟩
  unfold skipPrefix
  rcases hpre with rfl | rfl
  · simp only [List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero, hd,
      List.headD_cons]
    rw [if_pos ⟨trivial, hcond.2⟩, if_neg hne]
  · simp only [List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero, hd,
      List.headD_cons]
    rw [if_pos ⟨trivial, hcond.2⟩, if_pos trivial]

theorem detect_lit {base rb : Nat} {pre body ws : List Nat} (hf : LitForm base pre rb body)
    (hdp : DigitPart rb body) (hws : Spaces ws) (hrb : rb ≤ 36) :
    ∃ eif, detectBase base (hd (pre ++ body ++ ws)) (hd ((pre ++ body ++ ws).drop 1)) = (rb, eif) ∧
      skipPrefix rb (pre ++ body ++ ws) = body ++ ws ∧
      (eif = true → rb = 10 ∧ ∀ c ∈ body, c = uscore ∨ digitValue c = 0) := by
  cases hf with
  | plain hb =>
    refine ⟨false, ?_, skip_plain hrb (fun _ => trivial) hdp hws, by simp⟩
    simp [detectBase, hb]
  | radix hb hp =>
    refine ⟨false, ?_, skip_radix hrb hp hdp, by simp⟩
    simp [detectBase, hb]
  | autoRadix hp =>
    refine ⟨false, ?_, skip_radix hrb hp hdp, by simp⟩
    obtain ⟨hb, x, hx, hpre⟩ := hp
    have hc : hd (pre ++ body ++ ws) = 48 ∧ hd ((pre ++ body ++ ws).drop 1) = x := by
      rcases hpre with rfl | rfl <;> simp [hd]
    rw [hc.1, hc.2]
    unfold detectBase
    rcases hb with rfl | rfl | rfl
    · have h1 : lower x = 98 := hx
      simp [h1]
    · have h1 : lower x = 111 := hx
      simp [h1]
    · have h1 : lower x = 120 := hx
      simp [h1]
  | autoDec h0 =>
    obtain ⟨c, r, rfl, hc⟩ := digitPart_head hdp
    have hh : hd ([] ++ (c :: r) ++ ws) = c := rfl
    refine ⟨false, ?_, ?_, by simp⟩
    · rw [hh]
      have : c ≠ 48 := h0
      simp [detectBase, this]
    · exact skip_plain hrb (fun _ => trivial) hdp hws
  | autoZero h0 =>
    obtain ⟨c, r, hbody, hc⟩ := digitPart_head hdp
    have hs2 := second_char hrb hdp hws
    by_cases h48 : c = 48
    · refine ⟨true, ?_, skip_plain hrb (fun _ => trivial) hdp hws, fun _ => ⟨rfl, h0⟩⟩
      have hh : hd (body ++ ws) = 48 := by rw [hbody, h48]; rfl
      have h1 : lower (hd ((body ++ ws).drop 1)) ≠ 120 := not_letter10 (Or.inl rfl) hs2
      have h2 : lower (hd ((body ++ ws).drop 1)) ≠ 111 := not_letter10 (Or.inr (Or.inl rfl)) hs2
      have h3 : lower (hd ((body ++ ws).drop 1)) ≠ 98 := not_letter10 (Or.inr (Or.inr rfl)) hs2
      simp only [List.nil_append, hh]
      unfold detectBase
      rw [if_pos rfl, if_neg (by simp), if_neg h1, if_neg h2, if_neg h3]
    · have hh : hd ([] ++ body ++ ws) = c := by rw [hbody]; rfl
      refine ⟨false, ?_, skip_plain hrb (fun _ => trivial) hdp hws, by simp⟩
      rw [hh]
      simp [detectBase, h48]

theorem litForm_range {base pre rb body} (hf : LitForm base pre rb body)
    (hb : base = 0 ∨ (2 ≤ base ∧ base ≤ 36)) : 2 ≤ rb ∧ rb ≤ 36 := by
  have hr : ∀ {b pre}, IsRadixPrefix b pre → 2 ≤ b ∧ b ≤ 36 := by
    rintro b pre ⟨h, _⟩
    omega
  cases hf with
  | plain h => omega
  | radix h hp => exact hr hp
  | autoRadix hp => exact hr hp
  | autoDec _ => omega
  | autoZero _ => omega

theorem binary_bases : ∀ b, b < 37 → 2 ≤ b → b &&& (b - 1) = 0 →
    b = 2 ∨ b = 4 ∨ b = 8 ∨ b = 16 ∨ b = 32 := by decide

theorem fsizeZ_le {digits base : Nat} (h : digits ≤ 2 ^ 58) (hb : base < 37) :
    fsizeZ digits base ≤ maxLongDigits := by
  have ht : ∀ b, b < 37 → logBaseBASE.getD b 0 ≤ 2 ^ 58 := by decide
  have hle := Nat.mul_le_mul h (ht base hb)
  unfold fsizeZ
  have : digits * logBaseBASE.getD base 0 / 2 ^ 60 ≤ 2 ^ 58 * 2 ^ 58 / 2 ^ 60 :=
    Nat.div_le_div_right hle
  have e : 2 ^ 58 * 2 ^ 58 / 2 ^ 60 + 1 ≤ maxLongDigits := by decide
  omega

/-- The limit test of `long_from_string_base`, longobject.c:2943-2946 and the
power-of-two exemption at :2936. -/
def limitHit (lim digits base : Nat) : Prop :=
  base &&& (base - 1) ≠ 0 ∧ digits > strDigitsThreshold ∧ lim > 0 ∧ digits > lim

instance (lim digits base : Nat) : Decidable (limitHit lim digits base) := by
  unfold limitHit; exact inferInstance

theorem convBody_spec {pyl : List Nat → Py (List Nat)} {lim rb : Nat} {body : List Nat}
    (hok : rb = 10 → HookAt pyl lim body) (hrb : 2 ≤ rb ∧ rb ≤ 36) (hdp : DigitPart rb body)
    (hs : cnt body ≤ 2 ^ 58) (hnl : ¬ limitHit lim (cnt body) rb) :
    ∃ z, convBody pyl lim body (cnt body) rb = .ok z ∧ IsDigits z ∧
      (rb &&& (rb - 1) ≠ 0 → z ≠ [] → 0 < val z) ∧ val z = hv rb 0 body := by
  have hvb := digitPart_valid hdp
  unfold convBody
  by_cases hbin : rb &&& (rb - 1) = 0
  · rw [if_pos hbin]
    have hb := bitsPerChar_eq rb (binary_bases rb (by omega) hrb.1 hbin)
    obtain ⟨z, e, a, b⟩ := longFromBinaryBase_spec hb hvb (by
      apply (Nat.le_div_iff_mul_le (by omega)).2
      have : cnt body * bitsPerChar rb ≤ 2 ^ 58 * 5 := Nat.mul_le_mul hs hb.2.1
      have h2 : (2 : Nat) ^ 58 * 5 ≤ ssizeMax - (30 - 1) := by decide
      omega)
    exact ⟨z, e, a, fun h => absurd hbin h, b⟩
  · rw [if_neg hbin]
    have hnl2 : ¬ (cnt body > strDigitsThreshold ∧ lim > 0 ∧ cnt body > lim) := by
      intro h
      exact hnl ⟨hbin, h⟩
    rw [if_neg hnl2]
    by_cases h6 : cnt body > 6000 ∧ rb = 10
    · rw [if_pos h6]
      obtain ⟨h60, rfl⟩ := h6
      have hlim : lim = 0 ∨ cnt body ≤ lim := by
        by_cases h0 : lim = 0
        · exact Or.inl h0
        · right
          apply Nat.le_of_not_lt
          intro h
          exact hnl2 ⟨by have : strDigitsThreshold = 640 := rfl; omega, by omega, h⟩
      rw [hok rfl h60 hlim]
      refine ⟨_, rfl, digitsOf_digits _, fun _ hz => ?_, val_digitsOf _⟩
      rw [val_digitsOf]
      have : hv 10 0 body ≠ 0 := fun h => hz (digitsOf_eq_nil.2 h)
      omega
    · rw [if_neg h6]
      have hmax : (2 : Nat) ^ 58 ≤ maxLongDigits := by decide
      obtain ⟨z, e, a, b, c⟩ := longFromNonBinaryBaseAt_spec (sz := fsizeZ (cnt body) rb) hrb.1
        (by omega) hbin hvb (fsizeZ_le hs (by omega)) (by omega)
      exact ⟨z, e, a, fun _ => b, c⟩

/-- `PyLong_FromString` on a literal: its value, or the digit limit, with `*pend` at the
end of the string. -/
theorem pyLongFromString_lit {pyl : List Nat → Py (List Nat)} {lim base rb : Nat} {neg : Bool}
    {s body : List Nat} (hok : rb = 10 → HookAt pyl lim body) (hbase : base = 0 ∨ (2 ≤ base ∧ base ≤ 36))
    (hl : IsLit base s neg rb body) (hs : cnt body ≤ 2 ^ 58) :
    pyLongFromString pyl lim s (base : Int) =
      if limitHit lim (cnt body) rb then
        (.error (.valueError (limitToIntMsg lim (cnt body))), none)
      else (.ok (Long.ofInt (litValue neg rb body)), some []) := by
  obtain ⟨ws1, sg, pre, ws2, rfl, h1, h2, h3, h4, h5⟩ := hl
  have hrb := litForm_range h4 hbase
  obtain ⟨eif, hdet, hskip, heif⟩ := detect_lit h4 h5 h2 hrb.2
  obtain ⟨U, hU⟩ : ∃ U, pre ++ body ++ ws2 = U := ⟨_, rfl⟩
  rw [hU] at hdet hskip
  have hhead : ∃ c r, U = c :: r ∧ digitValue c < 37 := by
    cases h4 with
    | plain _ =>
      obtain ⟨c, r, rfl, hc⟩ := digitPart_head h5
      exact ⟨c, r ++ ws2, by rw [← hU]; simp, by omega⟩
    | autoDec _ =>
      obtain ⟨c, r, rfl, hc⟩ := digitPart_head h5
      exact ⟨c, r ++ ws2, by rw [← hU]; simp, by omega⟩
    | autoZero _ =>
      obtain ⟨c, r, rfl, hc⟩ := digitPart_head h5
      exact ⟨c, r ++ ws2, by rw [← hU]; simp, by omega⟩
    | radix _ hp =>
      obtain ⟨_, x, _, hpre⟩ := hp
      rcases hpre with rfl | rfl
      · exact ⟨48, _, by rw [← hU]; simp; rfl, by decide⟩
      · exact ⟨48, _, by rw [← hU]; simp; rfl, by decide⟩
    | autoRadix hp =>
      obtain ⟨_, x, _, hpre⟩ := hp
      rcases hpre with rfl | rfl
      · exact ⟨48, _, by rw [← hU]; simp; rfl, by decide⟩
      · exact ⟨48, _, by rw [← hU]; simp; rfl, by decide⟩
  obtain ⟨c, r, hUc, hc⟩ := hhead
  obtain ⟨hc1, hc2, hc3, hc4⟩ := dv_ne hc
  have hfinal : ws1 ++ sg ++ pre ++ body ++ ws2 = ws1 ++ (sg ++ U) := by
    rw [← hU]; simp [List.append_assoc]
  rw [hfinal]
  have hdrop : (ws1 ++ (sg ++ U)).dropWhile (fun c => c ≠ 0 && cIsSpace c) = sg ++ U := by
    have key : ∀ w : List Nat, Spaces w → ∀ T : List Nat,
        T.dropWhile (fun c => c ≠ 0 && cIsSpace c) = T →
        (w ++ T).dropWhile (fun c => c ≠ 0 && cIsSpace c) = T := by
      intro w
      induction w with
      | nil => intro _ T h; exact h
      | cons x w ih =>
        intro hw T hT
        have hx := hw x (by simp)
        rw [List.cons_append, List.dropWhile_cons, if_pos (by simp [hx, space_ne_zero hx])]
        exact ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)) T hT
    apply key _ h1
    rcases h3 with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · rw [hUc, List.nil_append, List.dropWhile_cons, if_neg (by simp [hc4])]
    · simp [List.dropWhile_cons, show cIsSpace 43 = false by decide]
    · simp [List.dropWhile_cons, show cIsSpace 45 = false by decide]
  have hsign : signOf (sg ++ U) = (neg, U) := by
    rcases h3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hUc]
      simp [signOf, hd, hc2, hc3]
    · simp [signOf, hd]
    · simp [signOf, hd]
  have hrange : ¬ (((base : Int) ≠ 0 ∧ (base : Int) < 2) ∨ (base : Int) > 36) := by omega
  have htn : (base : Int).toNat = base := by simp
  have hlfsb := longFromStringBase_lit pyl lim hrb.2 h5 h2
  unfold pyLongFromString
  rw [if_neg hrange]
  simp only [hdrop, hsign, htn, hdet, hskip, hlfsb]
  by_cases hhit : limitHit lim (cnt body) rb
  · rw [if_pos hhit]
    have hconv : convBody pyl lim body (cnt body) rb =
        .error (.valueError (limitToIntMsg lim (cnt body))) := by
      unfold convBody
      rw [if_neg hhit.1, if_pos hhit.2]
    rw [hconv]
  · rw [if_neg hhit]
    obtain ⟨z, e, a, b, c⟩ := convBody_spec hok hrb h5 hs hhit
    rw [e]
    have hnot : ¬ (eif = true ∧ z ≠ []) := by
      rintro ⟨h6, h7⟩
      obtain ⟨hrb10, hz0⟩ := heif h6
      subst hrb10
      have hzero : hv 10 0 body = 0 := by
        have := hv_of_all_zero (b := 10) body hz0 0
        simpa using this
      have := b (by decide) h7
      omega
    simp only [hnot, ↓reduceIte, normal_of_lit a c neg]
    rfl

/-! ### Completeness: only literals are accepted -/

/-- Digits and underscores with no double underscore; `p` says the previous character
was an underscore. -/
def goodRun (b : Nat) : Bool → List Nat → Prop
  | _, [] => True
  | p, c :: r =>
    if c = uscore then p = false ∧ goodRun b true r else digitValue c < b ∧ goodRun b false r

def lastOr (prev : Nat) : List Nat → Nat
  | [] => prev
  | c :: r => lastOr c r

theorem scan_inv {b : Nat} : ∀ (S : List Nat) (q : List Nat) (prev digits d' p' : Nat)
    (q' e : List Nat), scan b q S prev digits = .stop d' p' q' e →
    ∃ body, S = body ++ e ∧ goodRun b (decide (prev = uscore)) body ∧ d' = digits + cnt body ∧
      p' = lastOr prev body
  | [], q, prev, digits, d', p', q', e, h => by
    rw [scan] at h
    injection h with h1 h2 h3 h4
    subst h1 h2 h4
    exact ⟨[], rfl, trivial, rfl, rfl⟩
  | c :: r, q, prev, digits, d', p', q', e, h => by
    rw [scan] at h
    by_cases h1 : digitValue c < b ∨ c = uscore
    · rw [if_pos h1] at h
      by_cases h2 : c = uscore
      · rw [if_pos h2] at h
        by_cases h3 : prev = uscore
        · rw [if_pos h3] at h
          cases h
        · rw [if_neg h3] at h
          obtain ⟨body, rfl, g, hd', hp⟩ := scan_inv r _ c digits d' p' q' e h
          refine ⟨c :: body, rfl, ?_, ?_, ?_⟩
          · simp only [goodRun, if_pos h2, decide_eq_false_iff_not, h3, not_false_eq_true,
              true_and]
            simpa [h2] using g
          · simp only [cnt, if_pos h2]; omega
          · exact hp
      · rw [if_neg h2] at h
        obtain ⟨body, rfl, g, hd', hp⟩ := scan_inv r _ c (digits + 1) d' p' q' e h
        have h4 : digitValue c < b := h1.resolve_right h2
        refine ⟨c :: body, rfl, ?_, ?_, ?_⟩
        · simp only [goodRun, if_neg h2]
          exact ⟨h4, by simpa [h2] using g⟩
        · simp only [cnt, if_neg h2]; omega
        · exact hp
    · rw [if_neg h1] at h
      injection h with h3 h4 h5 h6
      subst h3 h4 h6
      exact ⟨[], rfl, trivial, rfl, rfl⟩

theorem lastOr_uscore_of_nil (prev : Nat) : lastOr prev [] = prev := rfl

theorem spaces_of_dropWhile : ∀ {ws : List Nat},
    ws.dropWhile (fun c => c ≠ 0 && cIsSpace c) = [] → Spaces ws
  | [], _ => fun _ h => by simp at h
  | c :: ws, h => by
    rw [List.dropWhile_cons] at h
    by_cases hc : (decide (c ≠ 0) && cIsSpace c) = true
    · rw [if_pos hc] at h
      have h1 := spaces_of_dropWhile h
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · simp at hc; exact hc.2
      · exact h1 x hx
    · rw [if_neg hc] at h
      simp at h

theorem goodRun_true_to_false {b : Nat} {l : List Nat} (h : goodRun b true l) :
    goodRun b false l := by
  cases l with
  | nil => trivial
  | cons c r =>
    rw [goodRun] at h ⊢
    by_cases hc : c = uscore
    · rw [if_pos hc] at h
      exact absurd h.1 (by decide)
    · rw [if_neg hc] at h ⊢
      exact h

theorem lastOr_any {l : List Nat} (h : l ≠ []) (a b : Nat) : lastOr a l = lastOr b l := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem digitPart_of_good {b : Nat} : ∀ (l : List Nat), goodRun b false l → l ≠ [] →
    (∀ prev, lastOr prev l ≠ uscore) → hd l ≠ uscore → DigitPart b l
  | [], _, h, _, _ => absurd rfl h
  | [c], g, _, _, hh => by
    have hc : c ≠ uscore := hh
    rw [goodRun, if_neg hc] at g
    exact .one g.1
  | c :: x :: r, g, _, hl, hh => by
    have hc : c ≠ uscore := hh
    rw [goodRun, if_neg hc] at g
    obtain ⟨g1, g2⟩ := g
    by_cases hx : x = uscore
    · subst hx
      rw [goodRun, if_pos rfl] at g2
      obtain ⟨_, g3⟩ := g2
      have hr : r ≠ [] := by
        rintro rfl
        exact hl 0 rfl
      have hhead : hd r ≠ uscore := by
        cases r with
        | nil => exact absurd rfl hr
        | cons y s =>
          intro hy
          have hy' : y = uscore := hy
          rw [goodRun, if_pos hy'] at g3
          exact absurd g3.1 (by decide)
      have ih := digitPart_of_good r (goodRun_true_to_false g3) hr
        (fun prev => by rw [lastOr_any hr prev uscore]; exact hl 0) hhead
      exact .us g1 ih
    · have ih := digitPart_of_good (x :: r) g2 (by simp) (fun prev => hl prev) hx
      exact .cons g1 ih

/-- A body accepted by `long_from_string_base`, with the terminator at the end of the
string, is a digit part followed by white space. -/
theorem longFromStringBase_inv {pyl : List Nat → Py (List Nat)} {lim b : Nat} {S : List Nat}
    {r : Py (List Nat)} (h : longFromStringBase pyl lim S b = (some r, [])) :
    ∃ body ws, S = body ++ ws ∧ DigitPart b body ∧ Spaces ws ∧
      r = convBody pyl lim body (cnt body) b := by
  unfold longFromStringBase at h
  by_cases h1 : hd S = uscore
  · rw [if_pos h1] at h
    cases h
  · rw [if_neg h1] at h
    cases hs : scan b S S 0 0 with
    | dbl q =>
      rw [hs] at h
      cases h
    | stop digits prev q e =>
      rw [hs] at h
      dsimp only at h
      by_cases h2 : prev = uscore
      · rw [if_pos h2] at h
        cases h
      · rw [if_neg h2] at h
        by_cases h3 : S.length = e.length
        · rw [if_pos h3] at h
          cases h
        · rw [if_neg h3] at h
          obtain ⟨body, hS, g, hd', hp⟩ := scan_inv S S 0 0 digits prev q e hs
          have hne : body ≠ [] := by
            rintro rfl
            apply h3
            rw [hS]; simp
          have hgf : goodRun b false body := by
            simpa [show ¬ (0 : Nat) = uscore by decide] using g
          have hlast : ∀ p, lastOr p body ≠ uscore := by
            intro p
            rw [lastOr_any hne p 0, ← hp]
            exact h2
          have hhead : hd body ≠ uscore := by
            obtain ⟨c, t, rfl⟩ := List.exists_cons_of_ne_nil hne
            rw [hS] at h1
            exact h1
          have hdp := digitPart_of_good body hgf hne hlast hhead
          have hdig : digits = cnt body := by omega
          have htake : S.take (S.length - e.length) = body := by
            rw [hS]; simp
          rw [htake] at h
          by_cases h4 : hd (e.dropWhile (fun c => c ≠ 0 && cIsSpace c)) ≠ 0
          · rw [if_pos h4] at h
            cases h
          · rw [if_neg h4] at h
            injection h with h5 h6
            injection h5 with h5
            exact ⟨body, e, hS, hdp, spaces_of_dropWhile h6, by rw [← h5, hdig]⟩

theorem sign_inv {s0 s1 : List Nat} {neg : Bool} (h : signOf s0 = (neg, s1)) :
    ∃ sg, s0 = sg ++ s1 ∧
      ((sg = [] ∧ neg = false) ∨ (sg = [43] ∧ neg = false) ∨ (sg = [45] ∧ neg = true)) := by
  unfold signOf at h
  by_cases h1 : hd s0 = 43
  · rw [if_pos h1] at h
    injection h with h2 h3
    cases s0 with
    | nil => exact absurd h1 (by decide)
    | cons c r =>
      have hc : c = 43 := h1
      subst hc
      exact ⟨[43], by simpa using h3, Or.inr (Or.inl ⟨rfl, h2.symm⟩)⟩
  · rw [if_neg h1] at h
    by_cases h4 : hd s0 = 45
    · rw [if_pos h4] at h
      injection h with h2 h3
      cases s0 with
      | nil => exact absurd h4 (by decide)
      | cons c r =>
        have hc : c = 45 := h4
        subst hc
        exact ⟨[45], by simpa using h3, Or.inr (Or.inr ⟨rfl, h2.symm⟩)⟩
    · rw [if_neg h4] at h
      injection h with h2 h3
      exact ⟨[], by simpa using h3, Or.inl ⟨rfl, h2.symm⟩⟩

theorem skip_inv (b : Nat) (s1 : List Nat) :
    ∃ pre, s1 = pre ++ skipPrefix b s1 ∧
      ((hd s1 = 48 ∧ ((b = 16 ∧ lower (hd (s1.drop 1)) = 120) ∨
        (b = 8 ∧ lower (hd (s1.drop 1)) = 111) ∨ (b = 2 ∧ lower (hd (s1.drop 1)) = 98))) →
          IsRadixPrefix b pre) ∧
      (¬ (hd s1 = 48 ∧ ((b = 16 ∧ lower (hd (s1.drop 1)) = 120) ∨
        (b = 8 ∧ lower (hd (s1.drop 1)) = 111) ∨ (b = 2 ∧ lower (hd (s1.drop 1)) = 98))) →
          pre = []) := by
  unfold skipPrefix
  dsimp only
  by_cases hc : hd s1 = 48 ∧ ((b = 16 ∧ lower (hd (s1.drop 1)) = 120) ∨
      (b = 8 ∧ lower (hd (s1.drop 1)) = 111) ∨ (b = 2 ∧ lower (hd (s1.drop 1)) = 98))
  · rw [if_pos hc]
    obtain ⟨h1, h2⟩ := hc
    have hb : b = 2 ∨ b = 8 ∨ b = 16 := by
      rcases h2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    have hl : lower (hd (s1.drop 1)) = radixLetter b := by
      rcases h2 with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> exact h
    cases s1 with
    | nil => exact absurd h1 (by decide)
    | cons c u =>
      have hc48 : c = 48 := h1
      subst hc48
      cases u with
      | nil =>
        exfalso
        have := (lower_letter hl (radixLetter_eq hb)).2.2.2
        exact this rfl
      | cons x t =>
        have hx : lower x = radixLetter b := hl
        simp only [List.drop_succ_cons, List.drop_zero]
        by_cases hu : hd t = uscore
        · rw [if_pos hu]
          cases t with
          | nil => exact absurd hu (by decide)
          | cons y t' =>
            have hy : y = uscore := hu
            subst hy
            refine ⟨[48, x, uscore], rfl, fun _ => ⟨hb, x, hx, Or.inr rfl⟩, fun hn => ?_⟩
            exact absurd ⟨rfl, h2⟩ hn
        · rw [if_neg hu]
          refine ⟨[48, x], rfl, fun _ => ⟨hb, x, hx, Or.inl rfl⟩, fun hn => ?_⟩
          exact absurd ⟨rfl, h2⟩ hn
  · rw [if_neg hc]
    exact ⟨[], rfl, fun h => absurd h hc, fun _ => rfl⟩

theorem mem_takeWhile_prop {p : Nat → Bool} : ∀ {l : List Nat} {c : Nat}, c ∈ l.takeWhile p →
    p c = true
  | [], _, h => by simp at h
  | x :: l, c, h => by
    rw [List.takeWhile_cons] at h
    by_cases hx : p x = true
    · rw [if_pos hx] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact hx
      · exact mem_takeWhile_prop h
    · rw [if_neg hx] at h
      simp at h

theorem cnt_le_length : ∀ l : List Nat, cnt l ≤ l.length
  | [] => Nat.le_refl _
  | c :: r => by
    have := cnt_le_length r
    simp only [cnt, List.length_cons]
    split <;> omega

/-- Everything `PyLong_FromString` accepts through to the end of the string is a
literal of the grammar, and the result is its value. -/
theorem pyLongFromString_inv {pyl : List Nat → Py (List Nat)} {lim base : Nat} {s : List Nat}
    {v : Long} {N : Nat} (hok : HookOK pyl lim N) (hbase : base = 0 ∨ (2 ≤ base ∧ base ≤ 36))
    (hs : s.length ≤ 2 ^ 58) (hN : s.length < N) (hbytes : ∀ c ∈ s, c < 256)
    (h : pyLongFromString pyl lim s (base : Int) = (.ok v, some [])) :
    ∃ neg rb body, IsLit base s neg rb body ∧ v = Long.ofInt (litValue neg rb body) := by
  have hrange : ¬ (((base : Int) ≠ 0 ∧ (base : Int) < 2) ∨ (base : Int) > 36) := by omega
  have htn : (base : Int).toNat = base := by simp
  unfold pyLongFromString at h
  rw [if_neg hrange] at h
  obtain ⟨s0, hs0⟩ : ∃ s0, s.dropWhile (fun c => c ≠ 0 && cIsSpace c) = s0 := ⟨_, rfl⟩
  obtain ⟨neg, s1, hsg⟩ : ∃ neg s1, signOf s0 = (neg, s1) := ⟨_, _, rfl⟩
  obtain ⟨b, eif, hdt⟩ : ∃ b eif, detectBase base (hd s1) (hd (s1.drop 1)) = (b, eif) :=
    ⟨_, _, rfl⟩
  simp only [hs0, hsg, htn, hdt] at h
  obtain ⟨sg, hs01, hsgn⟩ := sign_inv hsg
  obtain ⟨pre, hs12, hpre1, hpre2⟩ := skip_inv b s1
  obtain ⟨S, hS⟩ : ∃ S, skipPrefix b s1 = S := ⟨_, rfl⟩
  rw [hS] at h hs12
  cases hlf : longFromStringBase pyl lim S b with
  | mk r p =>
    rw [hlf] at h
    cases r with
    | none => cases h
    | some r =>
      cases r with
      | error e => cases h
      | ok z =>
        dsimp only at h
        by_cases hez : eif = true ∧ z ≠ []
        · rw [if_pos hez] at h
          cases h
        · rw [if_neg hez] at h
          injection h with h1 h2
          injection h1 with h1
          injection h2 with h2
          subst h2
          obtain ⟨body, ws, hSd, hdp, hws, hconv⟩ := longFromStringBase_inv hlf
          have hrb : 2 ≤ b ∧ b ≤ 36 := by
            unfold detectBase at hdt
            split at hdt
            · repeat' split at hdt
              all_goals (injection hdt with h3 _; omega)
            · injection hdt with h3 _; omega
          have hsdec : s = s.takeWhile (fun c => c ≠ 0 && cIsSpace c) ++ s0 := by
            rw [← hs0, List.takeWhile_append_dropWhile]
          have hsfull : s = s.takeWhile (fun c => c ≠ 0 && cIsSpace c) ++
              (sg ++ (pre ++ (body ++ ws))) := by
            conv => lhs; rw [hsdec, hs01, hs12, hSd]
          have h4 : body.length ≤ s.length := by
            have : s.length = (s.takeWhile (fun c => c ≠ 0 && cIsSpace c)).length + sg.length +
                pre.length + body.length + ws.length := by
              conv => lhs; rw [hsfull]
              simp only [List.length_append]
              omega
            omega
          have h3 := cnt_le_length body
          have hcnt : cnt body ≤ 2 ^ 58 := by omega
          have hbody256 : ∀ c ∈ body, c < 256 := fun c hc => hbytes c (by
            rw [hsfull]
            simp [hc])
          have hat : b = 10 → HookAt pyl lim body := by
            rintro rfl
            exact hok body hdp hbody256 (by omega)
          have hnl : ¬ limitHit lim (cnt body) b := by
            intro hhit
            have : convBody pyl lim body (cnt body) b =
                .error (.valueError (limitToIntMsg lim (cnt body))) := by
              unfold convBody
              rw [if_neg hhit.1, if_pos hhit.2]
            rw [this] at hconv
            cases hconv
          obtain ⟨z', e', hdz, hpos, hvz⟩ := convBody_spec hat hrb hdp hcnt hnl
          rw [e'] at hconv
          injection hconv with hconv
          subst hconv
          have hform : LitForm base pre b body := by
            by_cases hb0 : base = 0
            · subst hb0
              unfold detectBase at hdt
              rw [if_pos rfl] at hdt
              by_cases hc0 : hd s1 ≠ 48
              · rw [if_pos hc0] at hdt
                injection hdt with h3 h4
                subst h3
                have hpn : pre = [] := hpre2 (fun h => hc0 h.1)
                subst hpn
                refine .autoDec ?_
                obtain ⟨c, t, rfl, _⟩ := digitPart_head hdp
                have : s1 = c :: (t ++ ws) := by simpa [hSd] using hs12
                rw [this] at hc0
                exact hc0
              · rw [if_neg hc0] at hdt
                have hc48 : hd s1 = 48 := by omega
                by_cases hl1 : lower (hd (s1.drop 1)) = 120
                · rw [if_pos hl1] at hdt
                  injection hdt with h3 h4
                  subst h3
                  exact .autoRadix (hpre1 ⟨hc48, Or.inl ⟨rfl, hl1⟩⟩)
                · rw [if_neg hl1] at hdt
                  by_cases hl2 : lower (hd (s1.drop 1)) = 111
                  · rw [if_pos hl2] at hdt
                    injection hdt with h3 h4
                    subst h3
                    exact .autoRadix (hpre1 ⟨hc48, Or.inr (Or.inl ⟨rfl, hl2⟩)⟩)
                  · rw [if_neg hl2] at hdt
                    by_cases hl3 : lower (hd (s1.drop 1)) = 98
                    · rw [if_pos hl3] at hdt
                      injection hdt with h3 h4
                      subst h3
                      exact .autoRadix (hpre1 ⟨hc48, Or.inr (Or.inr ⟨rfl, hl3⟩)⟩)
                    · rw [if_neg hl3] at hdt
                      injection hdt with h3 h4
                      subst h3
                      subst h4
                      have hpn : pre = [] := hpre2 (fun h => by
                        rcases h.2 with ⟨h5, _⟩ | ⟨h5, _⟩ | ⟨h5, _⟩ <;> omega)
                      subst hpn
                      have hz0 : z = [] := by
                        apply Classical.byContradiction
                        intro hne
                        exact hez ⟨rfl, hne⟩
                      subst hz0
                      refine .autoZero (all_zero_of_hv (b := 10) (by decide) body 0 ?_)
                      rw [← hvz]
                      rfl
            · unfold detectBase at hdt
              rw [if_neg hb0] at hdt
              injection hdt with h3 h4
              subst h3
              by_cases hcond : hd s1 = 48 ∧ ((base = 16 ∧ lower (hd (s1.drop 1)) = 120) ∨
                  (base = 8 ∧ lower (hd (s1.drop 1)) = 111) ∨
                  (base = 2 ∧ lower (hd (s1.drop 1)) = 98))
              · exact .radix hb0 (hpre1 hcond)
              · rw [hpre2 hcond]
                exact .plain hb0
          refine ⟨neg, b, body, ⟨s.takeWhile (fun c => c ≠ 0 && cIsSpace c), sg, pre, ws, ?_, ?_,
            hws, hsgn, hform, hdp⟩, ?_⟩
          · conv => lhs; rw [hsdec, hs01, hs12, hSd]
            simp [List.append_assoc]
          · intro c hc
            have := mem_takeWhile_prop hc
            simp at this
            exact this.2
          · rw [← h1]
            exact normal_of_lit hdz hvz neg

/-- `pend` stays unset only with an error. -/
theorem pyLongFromString_none {pyl : List Nat → Py (List Nat)} {lim : Nat} {s : List Nat}
    {base : Int} {v : Long} : pyLongFromString pyl lim s base ≠ (.ok v, none) := by
  intro h
  unfold pyLongFromString at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    all_goals first | cases h | (split at h <;> cases h)

/-- `_PyLong_FromBytes` on a literal. -/
theorem pyLongFromBytes_lit {pyl : List Nat → Py (List Nat)} {lim base rb : Nat} {neg : Bool}
    {s body : List Nat} (hok : rb = 10 → HookAt pyl lim body) (hbase : base = 0 ∨ (2 ≤ base ∧ base ≤ 36))
    (hl : IsLit base s neg rb body) (hs : cnt body ≤ 2 ^ 58) :
    pyLongFromBytes pyl lim s (base : Int) =
      if limitHit lim (cnt body) rb then .error (.valueError (limitToIntMsg lim (cnt body)))
      else .ok (Long.ofInt (litValue neg rb body)) := by
  unfold pyLongFromBytes
  rw [pyLongFromString_lit hok hbase hl hs]
  by_cases hhit : limitHit lim (cnt body) rb
  · simp only [if_pos hhit]
  · simp only [if_neg hhit]

/-- `_PyLong_FromBytes` accepts only literals. -/
theorem pyLongFromBytes_inv {pyl : List Nat → Py (List Nat)} {lim base : Nat} {s : List Nat}
    {v : Long} {N : Nat} (hok : HookOK pyl lim N) (hbase : base = 0 ∨ (2 ≤ base ∧ base ≤ 36))
    (hs : s.length ≤ 2 ^ 58) (hN : s.length < N) (hbytes : ∀ c ∈ s, c < 256)
    (h : pyLongFromBytes pyl lim s (base : Int) = .ok v) :
    ∃ neg rb body, IsLit base s neg rb body ∧ v = Long.ofInt (litValue neg rb body) := by
  unfold pyLongFromBytes at h
  cases hr : pyLongFromString pyl lim s (base : Int) with
  | mk r e =>
    rw [hr] at h
    dsimp only at h
    cases e with
    | none =>
      subst h
      exact absurd hr pyLongFromString_none
    | some p =>
      cases p with
      | nil =>
        cases r with
        | error e => cases h
        | ok w =>
          injection h with h
          subst h
          exact pyLongFromString_inv hok hbase hs hN hbytes hr
      | cons _ _ => cases h

/-- `PyLong_FromUnicodeObject` on a string whose transform is a literal. -/
theorem pyLongFromUnicodeObject_lit {pyl : List Nat → Py (List Nat)} {lim base rb : Nat}
    {neg : Bool} {u body : List Nat} (hok : rb = 10 → HookAt pyl lim body)
    (hbase : base = 0 ∨ (2 ≤ base ∧ base ≤ 36))
    (hl : IsLit base (transformDecimalAndSpace u) neg rb body) (hs : cnt body ≤ 2 ^ 58) :
    pyLongFromUnicodeObject pyl lim u (base : Int) =
      if limitHit lim (cnt body) rb then .error (.valueError (limitToIntMsg lim (cnt body)))
      else .ok (Long.ofInt (litValue neg rb body)) := by
  unfold pyLongFromUnicodeObject
  dsimp only
  rw [pyLongFromString_lit hok hbase hl hs]
  by_cases hhit : limitHit lim (cnt body) rb
  · simp only [if_pos hhit]
  · simp only [if_neg hhit]

/-- `PyLong_FromUnicodeObject` accepts only strings whose transform is a literal. -/
theorem pyLongFromUnicodeObject_inv {pyl : List Nat → Py (List Nat)} {lim base : Nat}
    {u : List Nat} {v : Long} {N : Nat} (hok : HookOK pyl lim N) (hbase : base = 0 ∨ (2 ≤ base ∧ base ≤ 36))
    (hs : (transformDecimalAndSpace u).length ≤ 2 ^ 58) (hN : (transformDecimalAndSpace u).length < N)
    (hbytes : ∀ c ∈ transformDecimalAndSpace u, c < 256)
    (h : pyLongFromUnicodeObject pyl lim u (base : Int) = .ok v) :
    ∃ neg rb body, IsLit base (transformDecimalAndSpace u) neg rb body ∧
      v = Long.ofInt (litValue neg rb body) := by
  unfold pyLongFromUnicodeObject at h
  dsimp only at h
  cases hr : pyLongFromString pyl lim (transformDecimalAndSpace u) (base : Int) with
  | mk r e =>
    rw [hr] at h
    dsimp only at h
    cases e with
    | none =>
      subst h
      exact absurd hr pyLongFromString_none
    | some p =>
      cases p with
      | nil =>
        cases r with
        | error e => cases h
        | ok w =>
          injection h with h
          subst h
          exact pyLongFromString_inv hok hbase hs hN hbytes hr
      | cons _ _ => cases h

/-! ### Printed numbers are literals -/

theorem dv_digitChar : ∀ d, d < 16 → digitValue (Nat.digitChar d).toNat = d := by decide

/-- The characters of `Nat.toDigits`, as code points. -/
def digitBytes (b n : Nat) : List Nat := (Nat.toDigits b n).map Char.toNat

theorem digitChar_ascii : ∀ d, d < 16 → (Nat.digitChar d).toNat < 128 := by decide

theorem digitBytes_ascii {b : Nat} (hb : b = 2 ∨ b = 8 ∨ b = 10 ∨ b = 16) (n : Nat) :
    ∀ c ∈ digitBytes b n, c < 128 := by
  have hb1 : 1 < b := by omega
  have hb16 : b ≤ 16 := by omega
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hlt : n < b
    · unfold digitBytes
      rw [Nat.toDigits_of_lt_base hlt]
      intro c hc
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
      subst hc
      exact digitChar_ascii n (by omega)
    · have hge : b ≤ n := by omega
      have e : digitBytes b n = digitBytes b (n / b) ++ [(Nat.digitChar (n % b)).toNat] := by
        unfold digitBytes
        rw [Nat.toDigits_of_base_le hb1 hge]
        simp
      rw [e]
      intro c hc
      rcases List.mem_append.1 hc with h | h
      · exact ih _ (Nat.div_lt_self (by omega) hb1) c h
      · simp only [List.mem_singleton] at h
        subst h
        exact digitChar_ascii _ (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hb16)

theorem digitBytes_spec {b : Nat} (hb : b = 2 ∨ b = 8 ∨ b = 10 ∨ b = 16) (n : Nat) :
    digitBytes b n ≠ [] ∧ (∀ c ∈ digitBytes b n, digitValue c < b) ∧ hv b 0 (digitBytes b n) = n := by
  have hb1 : 1 < b := by omega
  have hb16 : b ≤ 16 := by omega
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hlt : n < b
    · have hd := dv_digitChar n (by omega)
      unfold digitBytes
      rw [Nat.toDigits_of_lt_base hlt]
      refine ⟨by simp, ?_, ?_⟩
      · intro c hc
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
        subst hc
        rw [hd]; exact hlt
      · simp only [List.map_cons, List.map_nil, hv_cons, hv_nil]
        have hne : (Nat.digitChar n).toNat ≠ uscore := by
          intro h
          rw [h, uscore_dv] at hd
          omega
        rw [if_neg hne, hd]
        simp
    · have hge : b ≤ n := by omega
      have hdlt : n / b < n := Nat.div_lt_self (by omega) hb1
      obtain ⟨i1, i2, i3⟩ := ih _ hdlt
      have hml : n % b < b := Nat.mod_lt _ (by omega)
      have hd := dv_digitChar (n % b) (by omega)
      have hne : (Nat.digitChar (n % b)).toNat ≠ uscore := by
        intro h
        rw [h, uscore_dv] at hd
        omega
      have e : digitBytes b n = digitBytes b (n / b) ++ [(Nat.digitChar (n % b)).toNat] := by
        unfold digitBytes
        rw [Nat.toDigits_of_base_le hb1 hge]
        simp
      rw [e]
      refine ⟨by simp, ?_, ?_⟩
      · intro c hc
        rcases List.mem_append.1 hc with h | h
        · exact i2 c h
        · simp only [List.mem_singleton] at h
          subst h
          rw [hd]; exact hml
      · rw [hv_append, i3, hv_cons, hv_nil, if_neg hne, hd, Nat.mul_comm]
        exact Nat.div_add_mod n b

theorem digitPart_of_all {b : Nat} : ∀ l : List Nat, l ≠ [] → (∀ c ∈ l, digitValue c < b) →
    DigitPart b l
  | [], h, _ => absurd rfl h
  | [c], _, h => .one (h c (by simp))
  | c :: d :: l, _, h =>
    .cons (h c (by simp)) (digitPart_of_all (d :: l) (by simp)
      (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem cnt_of_digits {b : Nat} (hb : b ≤ 36) : ∀ l : List Nat, (∀ c ∈ l, digitValue c < b) →
    cnt l = l.length
  | [], _ => rfl
  | c :: l, h => by
    have hc : c ≠ uscore := (dv_ne (by have := h c (by simp); omega)).1
    simp only [cnt, if_neg hc, List.length_cons]
    rw [cnt_of_digits hb l (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    omega

theorem isLit_printed {base rb : Nat} {pre : List Nat} (neg : Bool) (V : Nat)
    (hrb : rb = 2 ∨ rb = 8 ∨ rb = 10 ∨ rb = 16) (hf : LitForm base pre rb (digitBytes rb V)) :
    IsLit base ((if neg then [45] else []) ++ pre ++ digitBytes rb V) neg rb (digitBytes rb V) := by
  obtain ⟨h1, h2, _⟩ := digitBytes_spec hrb V
  refine ⟨[], if neg then [45] else [], pre, [], by simp, fun _ h => by simp at h,
    fun _ h => by simp at h, ?_, hf, digitPart_of_all _ h1 h2⟩
  cases neg
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

theorem litValue_printed {rb : Nat} (hrb : rb = 2 ∨ rb = 8 ∨ rb = 10 ∨ rb = 16) (neg : Bool)
    (V : Nat) : litValue neg rb (digitBytes rb V) = if neg then -(V : Int) else V := by
  unfold litValue
  rw [(digitBytes_spec hrb V).2.2]

end PyLean.LongObj
