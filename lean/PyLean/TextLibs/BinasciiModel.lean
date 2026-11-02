import PyLean.Core

/-!
Model of the base64, base32, base16 and hex paths of `Modules/binascii.c` and
`Lib/base64.py`, CPython 3.15.2. Shifts and masks of the C loops are written with
`/` and `%` on naturals, which is what they compute there.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

/-- `binascii.Error`. -/
def err (m : String) : PyExc := .named "Error" m

/-- An argument: a `bytes`-like object, a `str` by code points, an object with no buffer, or one
whose `__buffer__` raises. -/
inductive Data where
  | bytes (b : List Nat)
  | str (cps : List Nat)
  | notBuffer (ty : String)
  | raises (ty : String) (e : PyExc)
  deriving Repr, DecidableEq, Inhabited

/-- `ascii_buffer_converter`, `Modules/binascii.c:428-455`. -/
def asciiBuffer : Data → Py (List Nat)
  | .bytes b => .ok b
  | .str s =>
    if s.all (· < 128) then .ok s
    else .error (.valueError "string argument should contain only ASCII characters")
  | .notBuffer t | .raises t _ =>
    .error (.typeError s!"argument should be bytes, buffer or ASCII string, not '{t}'")

/-- The `y*` of the encoding functions: a failing `__buffer__` passes through. -/
def bufData : Data → Py (List Nat)
  | .bytes b => .ok b
  | .str _ => .error (.typeError "a bytes-like object is required, not 'str'")
  | .notBuffer t => .error (.typeError s!"a bytes-like object is required, not '{t}'")
  | .raises _ e => .error e

/-- `table_b2a_base64`, `Modules/binascii.c:113-114`. -/
def b2aChar (v : Nat) : Nat :=
  if v < 26 then 65 + v
  else if v < 52 then 97 + (v - 26)
  else if v < 62 then 48 + (v - 52)
  else if v = 62 then 43
  else 47

/-- `table_a2b_base64`, `Modules/binascii.c:81-99`; `255` is its `-1`, and the `'='`
entry is never read because padding is handled first. -/
def a2bChar (c : Nat) : Nat :=
  if 65 ≤ c ∧ c ≤ 90 then c - 65
  else if 97 ≤ c ∧ c ≤ 122 then c - 97 + 26
  else if 48 ≤ c ∧ c ≤ 57 then c - 48 + 52
  else if c = 43 then 62
  else if c = 47 then 63
  else 255

/-- Decoder state of `binascii_a2b_base64_impl`. `out` is `bin_data` so far. -/
structure Dec where
  quad : Nat := 0
  pads : Nat := 0
  left : Nat := 0
  out : List Nat := []
  deriving Repr, DecidableEq, Inhabited

/-- The `switch (quad_pos)`, `Modules/binascii.c:875-897`. -/
def decStep (st : Dec) (v : Nat) : Dec :=
  match st.quad with
  | 0 => { st with quad := 1, left := v }
  | 1 => { st with quad := 2, out := st.out ++ [(st.left * 4 + v / 16) % 256], left := v % 16 }
  | 2 => { st with quad := 3, out := st.out ++ [(st.left * 16 + v / 4) % 256], left := v % 4 }
  | _ => { st with quad := 0, out := st.out ++ [(st.left * 64 + v) % 256], left := 0 }

/-- The slow loop of `binascii_a2b_base64_impl`, `Modules/binascii.c:811-898`, with default options and
the fast path left out, as a specification: `BinasciiEq.lean` has the C loop equal to it. -/
def a2bLoop (strict : Bool) : List Nat → (i : Nat) → Dec → Py Dec
  | [], _, st => .ok st
  | c :: cs, i, st =>
    if c = 61 then
      let pads := st.pads + 1
      let st' := { st with pads }
      if st.quad ≥ 2 ∧ st.quad + pads ≤ 4 then a2bLoop strict cs (i + 1) st'
      else if !strict then a2bLoop strict cs (i + 1) st'
      else if st.quad = 1 then .ok st'
      else .error (err (if st.quad = 0 ∧ st.out.isEmpty then "Leading padding not allowed"
                        else "Excess padding not allowed"))
    else
      let v := a2bChar c
      if v ≥ 64 then
        if strict then .error (err "Only base64 data is allowed")
        else a2bLoop strict cs (i + 1) st
      else if st.pads ≠ 0 ∧ strict then
        .error (err (if st.quad + st.pads = 4 then "Excess data after padding"
                     else "Discontinuous padding not allowed"))
      else a2bLoop strict cs (i + 1) (decStep { st with pads := 0 } v)

/-- `binascii_a2b_base64_impl`, `Modules/binascii.c:749-942`. -/
def a2bBase64Bytes (strict : Bool) (b : List Nat) : Py (List Nat) := do
  let st ← a2bLoop strict b 0 {}
  if st.quad = 1 then
    throw (err s!"Invalid base64-encoded string: number of data characters \
      ({st.out.length / 3 * 4 + 1}) cannot be 1 more than a multiple of 4")
  if st.quad ≠ 0 ∧ st.quad + st.pads < 4 then throw (err "Incorrect padding")
  return st.out

def a2bBase64 (strict : Bool) (d : Data) : Py (List Nat) := do
  a2bBase64Bytes strict (← asciiBuffer d)

/-- The bit-at-a-time drain of a specification of `binascii_b2a_base64_impl`, which writes three bytes at a time since 3.15. -/
def b2aDrain (left : Nat) : (fuel : Nat) → (bits : Nat) → List Nat × Nat
  | 0, bits => ([], bits)
  | fuel + 1, bits =>
    if bits ≥ 6 then
      let c := b2aChar (left / 2 ^ (bits - 6) % 64)
      let (r, bits') := b2aDrain left fuel (bits - 6)
      (c :: r, bits')
    else ([], bits)

/-- The byte loop of that specification. `leftchar` is 32-bit and wraps. -/
def b2aLoop : List Nat → (left bits : Nat) → List Nat × Nat × Nat
  | [], left, bits => ([], left, bits)
  | b :: bs, left, bits =>
    let left' := (left * 256 + b) % 2 ^ 32
    let (out, bits') := b2aDrain left' 3 (bits + 8)
    let (r, l2, b2) := b2aLoop bs left' bits'
    (out ++ r, l2, b2)

/-- `binascii_b2a_base64_impl`, `Modules/binascii.c:960-1049`. -/
def b2aBase64 (data : List Nat) (newline : Bool) : List Nat :=
  let (out, left, bits) := b2aLoop data 0 0
  let tail :=
    if bits = 2 then [b2aChar (left % 4 * 16), 61, 61]
    else if bits = 4 then [b2aChar (left % 16 * 4), 61]
    else []
  out ++ tail ++ (if newline then [10] else [])

/-- `_PyLong_DigitValue` for hex digits; `37` stands for its "not a digit" entry. -/
def digitValue (c : Nat) : Nat :=
  if 48 ≤ c ∧ c ≤ 57 then c - 48
  else if 97 ≤ c ∧ c ≤ 122 then c - 97 + 10
  else if 65 ≤ c ∧ c ≤ 90 then c - 65 + 10
  else 37

/-- Pairs of digits, a specification of `a2bHexIg` for an even number of digits and no `ignorechars`. -/
def a2bHexLoop : List Nat → Py (List Nat)
  | a :: b :: r =>
    let top := digitValue a
    let bot := digitValue b
    if top ≥ 16 ∨ bot ≥ 16 then .error (err "Non-hexadecimal digit found")
    else do return (top * 16 + bot) :: (← a2bHexLoop r)
  | _ => .ok []

/-- `binascii_a2b_hex_impl`, `Modules/binascii.c:2283-2350`. -/
def a2bHexBytes (b : List Nat) : Py (List Nat) :=
  if b.length % 2 ≠ 0 then .error (err "Odd-length string") else a2bHexLoop b

def a2bHex (d : Data) : Py (List Nat) := do a2bHexBytes (← asciiBuffer d)

def hexDigit (v : Nat) : Nat := if v < 10 then 48 + v else 97 + (v - 10)

/-- `_Py_strhex_bytes_with_sep` without a separator, `Modules/binascii.c:2241-2248`. -/
def b2aHex : List Nat → List Nat
  | [] => []
  | b :: r => hexDigit (b / 16) :: hexDigit (b % 16) :: b2aHex r

/-- The `sep` argument of `_Py_strhex_impl`. `seqlen` is an object with a length that is neither
`str` nor `bytes`, and `lenRaises` one whose `__len__` raises. -/
inductive SepArg where
  | absent
  | str (cps : List Nat)
  | bytes (b : List Nat)
  | seqlen (n : Nat)
  | lenRaises (e : PyExc)
  deriving Repr, DecidableEq, Inhabited

/-- The checks of `_Py_strhex_impl`, `Python/pystrhex.c:122-152`, with `return_bytes` set: the separator
byte. `PyUnicode_KIND` of a non-ASCII `str` of one character below 256 is `1BYTE`, so it passes. -/
def strhexSep : SepArg → Py (Option Nat)
  | .absent => .ok none
  | .lenRaises e => .error e
  | .str [c] =>
    if c < 256 then .ok (some c) else .error (.valueError "sep must be ASCII.")
  | .bytes [c] => .ok (some c)
  | .seqlen 1 => .error (.typeError "sep must be str or bytes.")
  | _ => .error (.valueError "sep must be length 1.")

/-- The negative `bytes_per_sep_group` loop, `Python/pystrhex.c:210-226`: groups count from the left. -/
def hexLeft (sep k : Nat) : (chunks : Nat) → List Nat → List Nat
  | 0, l => b2aHex l
  | c + 1, l => b2aHex (l.take k) ++ [sep] ++ hexLeft sep k c (l.drop k)

/-- The positive loop, `Python/pystrhex.c:227-244`, which fills from the end: groups count from the
right. -/
def hexRight (sep k : Nat) : (chunks : Nat) → List Nat → List Nat
  | 0, l => b2aHex l
  | c + 1, l =>
    hexRight sep k c (l.take (l.length - k)) ++ [sep] ++ b2aHex (l.drop (l.length - k))

/-- `_Py_strhex_impl`, `Python/pystrhex.c:116-254`, returning bytes. -/
def strhexBytes (data : List Nat) (sep : SepArg) (group : Int) : Py (List Nat) := do
  let sc ← strhexSep sep
  match sc with
  | none => return b2aHex data
  | some c =>
    let k := group.natAbs
    if group = 0 ∨ k ≥ data.length then return b2aHex data
    let chunks := (data.length - 1) / k
    if group < 0 then return hexLeft c k chunks data
    return hexRight c k chunks data

/-! ### `Lib/base64.py` -/

/-- `_bytes_from_decode_data`, `Lib/base64.py:32-44`: `memoryview(s)` failing with `TypeError` is
replaced, and any other exception passes through. -/
def bytesFromDecodeData : Data → Py (List Nat)
  | .bytes b => .ok b
  | .str s =>
    if s.all (· < 128) then .ok s
    else .error (.valueError "string argument should contain only ASCII characters")
  | .notBuffer t | .raises t (.typeError _) =>
    .error (.typeError s!"argument should be a bytes-like object or ASCII string, not '{t}'")
  | .raises _ e => .error e

/-- `memoryview(s).tobytes()`, for an argument that is not `bytes` already. -/
def toBytesView : Data → Py (List Nat)
  | .bytes b => .ok b
  | .str _ => .error (.typeError "memoryview: a bytes-like object is required, not 'str'")
  | .notBuffer t => .error (.typeError s!"memoryview: a bytes-like object is required, not '{t}'")
  | .raises _ e => .error e

/-- `bytes.translate` with the table `bytes.maketrans(frm, to)`; the last equal
`frm` byte wins, as when the table is filled in order. -/
def translate (frm to : List Nat) (s : List Nat) : List Nat :=
  s.map fun c => ((frm.zip to).reverse.find? (·.1 == c)).map (·.2) |>.getD c

/-- `bytes.upper`. -/
def upper (s : List Nat) : List Nat := s.map fun c => if 97 ≤ c ∧ c ≤ 122 then c - 32 else c

def plusSlash : List Nat := [43, 47]

/-- `b64encode` (a specification; `BinasciiC.lean` has the function of 3.15.2). -/
def b64encode (s : List Nat) (alt : Option (List Nat)) : Py (List Nat) :=
  let encoded := b2aBase64 s false
  match alt with
  | none => .ok encoded
  | some a =>
    if a.length ≠ 2 then .error (.assertionError "~repr(altchars)")
    else .ok (translate plusSlash a encoded)

/-- `b64decode` (a specification; `BinasciiC.lean` has the function of 3.15.2). -/
def b64decode (s : Data) (alt : Option Data) (validate : Bool) : Py (List Nat) := do
  let s ← bytesFromDecodeData s
  match alt with
  | none => a2bBase64 validate (.bytes s)
  | some a =>
    let a ← bytesFromDecodeData a
    if a.length ≠ 2 then throw (.assertionError "~repr(altchars)")
    a2bBase64 validate (.bytes (translate a plusSlash s))

def dashUnderscore : List Nat := [45, 95]

/-- `urlsafe_b64encode` (a specification; `BinasciiC.lean` has the function of 3.15.2). -/
def urlsafeEncode (s : List Nat) : List Nat := translate plusSlash dashUnderscore (b2aBase64 s false)

/-- `urlsafe_b64decode` (a specification; `BinasciiC.lean` has the function of 3.15.2). -/
def urlsafeDecode (s : Data) : Py (List Nat) := do
  let s ← bytesFromDecodeData s
  b64decode (.bytes (translate dashUnderscore plusSlash s)) none false

def b32alphabet : List Nat := "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567".toList.map Char.toNat
def b32hexalphabet : List Nat := "0123456789ABCDEFGHIJKLMNOPQRSTUV".toList.map Char.toNat

/-- `b32tab2[x]` (a specification; `BinasciiC.lean` has the function of 3.15.2). -/
def b32pair (alpha : List Nat) (x : Nat) : List Nat :=
  [alpha.getD (x / 32) 0, alpha.getD (x % 32) 0]

/-- The `for i in range(0, len(s), 5)` loop (a specification; `BinasciiC.lean` has the function of 3.15.2). -/
def b32Chunks (alpha : List Nat) : (fuel : Nat) → List Nat → List Nat
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, s =>
    let q := (s.take 5).foldl (fun x b => x * 256 + b) 0
    b32pair alpha (q / 2 ^ 30) ++ b32pair alpha (q / 2 ^ 20 % 1024) ++
      b32pair alpha (q / 2 ^ 10 % 1024) ++ b32pair alpha (q % 1024) ++
      b32Chunks alpha fuel (s.drop 5)

/-- `_b32encode` (a specification; `BinasciiC.lean` has the function of 3.15.2). -/
def b32encode (alpha s : List Nat) : List Nat :=
  let leftover := s.length % 5
  let s' := if leftover ≠ 0 then s ++ List.replicate (5 - leftover) 0 else s
  let encoded := b32Chunks alpha (s'.length) s'
  let n := match leftover with | 1 => 6 | 2 => 4 | 3 => 3 | 4 => 1 | _ => 0
  encoded.take (encoded.length - n) ++ List.replicate n 61

/-- `b32rev[c]`: the index of `c` in the alphabet. -/
def b32rev (alpha : List Nat) (c : Nat) : Option Nat := alpha.findIdx? (· == c)

/-- `acc.to_bytes(5)`. -/
def toBytes5 (acc : Nat) : List Nat :=
  [acc / 2 ^ 32 % 256, acc / 2 ^ 24 % 256, acc / 2 ^ 16 % 256, acc / 2 ^ 8 % 256, acc % 256]

/-- The inner `for c in quanta` loop (a specification; `BinasciiC.lean` has the function of 3.15.2). -/
def b32Quanta (alpha : List Nat) (acc : Nat) : List Nat → Py Nat
  | [] => .ok acc
  | c :: cs =>
    match b32rev alpha c with
    | none => .error (err "Non-base32 digit found")
    | some v => b32Quanta alpha (acc * 32 + v) cs

/-- The outer loop (a specification; `BinasciiC.lean` has the function of 3.15.2): the bytes and the last `acc`. -/
def b32DecLoop (alpha : List Nat) : (fuel : Nat) → List Nat → List Nat → Nat → Py (List Nat × Nat)
  | 0, _, dec, acc => .ok (dec, acc)
  | _ + 1, [], dec, acc => .ok (dec, acc)
  | fuel + 1, s, dec, _ => do
    let acc ← b32Quanta alpha 0 (s.take 8)
    b32DecLoop alpha fuel (s.drop 8) (dec ++ toBytes5 acc) acc

/-- `s.rstrip(b'=')`. -/
def rstripPad (s : List Nat) : List Nat := (s.reverse.dropWhile (· == 61)).reverse

/-- `_b32decode` (a specification; `BinasciiC.lean` has the function of 3.15.2). -/
def b32decode (alpha : List Nat) (s0 : Data) (casefold : Bool) (map01 : Option Data) :
    Py (List Nat) := do
  let s ← bytesFromDecodeData s0
  if s.length % 8 ≠ 0 then throw (err "Incorrect padding")
  let s ← match map01 with
    | none => pure s
    | some m =>
      let m ← bytesFromDecodeData m
      if m.length ≠ 1 then throw (.assertionError "~repr(map01)")
      pure (translate [48, 49] (79 :: m) s)
  let s := if casefold then upper s else s
  let l := s.length
  let s := rstripPad s
  let padchars := l - s.length
  let (decoded, acc) ← b32DecLoop alpha (s.length + 1) s [] 0
  if l % 8 ≠ 0 ∨ !([0, 1, 3, 4, 6].contains padchars) then throw (err "Incorrect padding")
  if padchars ≠ 0 ∧ !decoded.isEmpty then
    let acc := acc * 2 ^ (5 * padchars)
    let leftover := (43 - 5 * padchars) / 8
    return decoded.take (decoded.length - 5) ++ (toBytes5 acc).take leftover
  return decoded

/-- `b16encode` (a specification; `BinasciiC.lean` has the function of 3.15.2). -/
def b16encode (s : List Nat) : List Nat := upper (b2aHex s)

/-- `b16decode` (a specification; `BinasciiC.lean` has the function of 3.15.2). -/
def b16decode (s0 : Data) (casefold : Bool) : Py (List Nat) := do
  let s ← bytesFromDecodeData s0
  let s := if casefold then upper s else s
  if s.any (fun c => !(("0123456789ABCDEF".toList.map Char.toNat).contains c)) then
    throw (err "Non-base16 digit found")
  a2bHex (.bytes s)

end PyLean.TextLibs.Binascii
