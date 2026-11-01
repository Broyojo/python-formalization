import PyLean.Core

/-!
Model of the base64, base32, base16 and hex paths of `Modules/binascii.c` and
`Lib/base64.py`, CPython 3.14.7. Shifts and masks of the C loops are written with
`/` and `%` on naturals, which is what they compute there.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

/-- `binascii.Error`. -/
def err (m : String) : PyExc := .named "Error" m

/-- A `bytes`-like object or a `str`, by code points. -/
inductive Data where
  | bytes (b : List Nat)
  | str (cps : List Nat)
  deriving Repr, DecidableEq, Inhabited

/-- `ascii_buffer_converter`, `Modules/binascii.c:163-190`. -/
def asciiBuffer : Data → Py (List Nat)
  | .bytes b => .ok b
  | .str s =>
    if s.all (· < 128) then .ok s
    else .error (.valueError "string argument should contain only ASCII characters")

/-- `table_b2a_base64`, `Modules/binascii.c:104-105`. -/
def b2aChar (v : Nat) : Nat :=
  if v < 26 then 65 + v
  else if v < 52 then 97 + (v - 26)
  else if v < 62 then 48 + (v - 52)
  else if v = 62 then 43
  else 47

/-- `table_a2b_base64`, `Modules/binascii.c:78-97`; `255` is its `-1`, and the `'='`
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

/-- The `switch (quad_pos)`, `Modules/binascii.c:465-485`. -/
def decStep (st : Dec) (v : Nat) : Dec :=
  match st.quad with
  | 0 => { st with quad := 1, left := v }
  | 1 => { st with quad := 2, out := st.out ++ [(st.left * 4 + v / 16) % 256], left := v % 16 }
  | 2 => { st with quad := 3, out := st.out ++ [(st.left * 16 + v / 4) % 256], left := v % 4 }
  | _ => { st with quad := 0, out := st.out ++ [(st.left * 64 + v) % 256], left := 0 }

/-- The `for` loop of `binascii_a2b_base64_impl`, `Modules/binascii.c:407-486`. `i` is the
loop index, used only by the "Leading padding" test. -/
def a2bLoop (strict : Bool) : List Nat → (i : Nat) → Dec → Py Dec
  | [], _, st => .ok st
  | c :: cs, i, st =>
    if c = 61 then
      let pads := st.pads + 1
      let st' := { st with pads }
      if st.quad ≥ 2 ∧ st.quad + pads ≤ 4 then a2bLoop strict cs (i + 1) st'
      else if !strict then a2bLoop strict cs (i + 1) st'
      else if st.quad = 1 then .ok st'
      else .error (err (if st.quad = 0 ∧ i = 0 then "Leading padding not allowed"
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

/-- `binascii_a2b_base64_impl`, `Modules/binascii.c:385-517`. -/
def a2bBase64Bytes (strict : Bool) (b : List Nat) : Py (List Nat) := do
  let st ← a2bLoop strict b 0 {}
  if st.quad = 1 then
    throw (err s!"Invalid base64-encoded string: number of data characters \
      ({st.out.length / 3 * 4 + 1}) cannot be 1 more than a multiple of 4")
  if st.quad ≠ 0 ∧ st.quad + st.pads < 4 then throw (err "Incorrect padding")
  return st.out

def a2bBase64 (strict : Bool) (d : Data) : Py (List Nat) := do
  a2bBase64Bytes strict (← asciiBuffer d)

/-- The `while (leftbits >= 6)` of `binascii_b2a_base64_impl`, `Modules/binascii.c:575-579`. -/
def b2aDrain (left : Nat) : (fuel : Nat) → (bits : Nat) → List Nat × Nat
  | 0, bits => ([], bits)
  | fuel + 1, bits =>
    if bits ≥ 6 then
      let c := b2aChar (left / 2 ^ (bits - 6) % 64)
      let (r, bits') := b2aDrain left fuel (bits - 6)
      (c :: r, bits')
    else ([], bits)

/-- The byte loop, `Modules/binascii.c:569-580`. `leftchar` is 32-bit and wraps. -/
def b2aLoop : List Nat → (left bits : Nat) → List Nat × Nat × Nat
  | [], left, bits => ([], left, bits)
  | b :: bs, left, bits =>
    let left' := (left * 256 + b) % 2 ^ 32
    let (out, bits') := b2aDrain left' 3 (bits + 8)
    let (r, l2, b2) := b2aLoop bs left' bits'
    (out ++ r, l2, b2)

/-- `binascii_b2a_base64_impl`, `Modules/binascii.c:531-593`. -/
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

/-- The loop of `binascii_a2b_hex_impl`, `Modules/binascii.c:922-935`. -/
def a2bHexLoop : List Nat → Py (List Nat)
  | a :: b :: r =>
    let top := digitValue a
    let bot := digitValue b
    if top ≥ 16 ∨ bot ≥ 16 then .error (err "Non-hexadecimal digit found")
    else do return (top * 16 + bot) :: (← a2bHexLoop r)
  | _ => .ok []

/-- `binascii_a2b_hex_impl`, `Modules/binascii.c:888-941`. -/
def a2bHexBytes (b : List Nat) : Py (List Nat) :=
  if b.length % 2 ≠ 0 then .error (err "Odd-length string") else a2bHexLoop b

def a2bHex (d : Data) : Py (List Nat) := do a2bHexBytes (← asciiBuffer d)

def hexDigit (v : Nat) : Nat := if v < 10 then 48 + v else 97 + (v - 10)

/-- `_Py_strhex_bytes_with_sep` without a separator, `Modules/binascii.c:849-856`. -/
def b2aHex : List Nat → List Nat
  | [] => []
  | b :: r => hexDigit (b / 16) :: hexDigit (b % 16) :: b2aHex r

/-! ### `Lib/base64.py` -/

/-- `_bytes_from_decode_data`, `Lib/base64.py:31-43`. -/
def bytesFromDecodeData : Data → Py (List Nat)
  | .bytes b => .ok b
  | .str s =>
    if s.all (· < 128) then .ok s
    else .error (.valueError "string argument should contain only ASCII characters")

/-- `bytes.translate` with the table `bytes.maketrans(frm, to)`; the last equal
`frm` byte wins, as when the table is filled in order. -/
def translate (frm to : List Nat) (s : List Nat) : List Nat :=
  s.map fun c => ((frm.zip to).reverse.find? (·.1 == c)).map (·.2) |>.getD c

/-- `bytes.upper`. -/
def upper (s : List Nat) : List Nat := s.map fun c => if 97 ≤ c ∧ c ≤ 122 then c - 32 else c

def plusSlash : List Nat := [43, 47]

/-- `b64encode`, `Lib/base64.py:48-59`. -/
def b64encode (s : List Nat) (alt : Option (List Nat)) : Py (List Nat) :=
  let encoded := b2aBase64 s false
  match alt with
  | none => .ok encoded
  | some a =>
    if a.length ≠ 2 then .error (.assertionError "~repr(altchars)")
    else .ok (translate plusSlash a encoded)

/-- `b64decode`, `Lib/base64.py:62-85`. -/
def b64decode (s : Data) (alt : Option Data) (validate : Bool) : Py (List Nat) := do
  let s ← bytesFromDecodeData s
  match alt with
  | none => a2bBase64 validate (.bytes s)
  | some a =>
    let a ← bytesFromDecodeData a
    if a.length ≠ 2 then throw (.assertionError "~repr(altchars)")
    a2bBase64 validate (.bytes (translate a plusSlash s))

def dashUnderscore : List Nat := [45, 95]

/-- `urlsafe_b64encode`, `Lib/base64.py:109-116`. -/
def urlsafeEncode (s : List Nat) : List Nat := translate plusSlash dashUnderscore (b2aBase64 s false)

/-- `urlsafe_b64decode`, `Lib/base64.py:118-131`. -/
def urlsafeDecode (s : Data) : Py (List Nat) := do
  let s ← bytesFromDecodeData s
  b64decode (.bytes (translate dashUnderscore plusSlash s)) none false

def b32alphabet : List Nat := "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567".toList.map Char.toNat
def b32hexalphabet : List Nat := "0123456789ABCDEFGHIJKLMNOPQRSTUV".toList.map Char.toNat

/-- `b32tab2[x]`, `Lib/base64.py:167-168`. -/
def b32pair (alpha : List Nat) (x : Nat) : List Nat :=
  [alpha.getD (x / 32) 0, alpha.getD (x % 32) 0]

/-- The `for i in range(0, len(s), 5)` loop, `Lib/base64.py:180-186`. -/
def b32Chunks (alpha : List Nat) : (fuel : Nat) → List Nat → List Nat
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, s =>
    let q := (s.take 5).foldl (fun x b => x * 256 + b) 0
    b32pair alpha (q / 2 ^ 30) ++ b32pair alpha (q / 2 ^ 20 % 1024) ++
      b32pair alpha (q / 2 ^ 10 % 1024) ++ b32pair alpha (q % 1024) ++
      b32Chunks alpha fuel (s.drop 5)

/-- `_b32encode`, `Lib/base64.py:163-196`. -/
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

/-- The inner `for c in quanta` loop, `Lib/base64.py:227-231`. -/
def b32Quanta (alpha : List Nat) (acc : Nat) : List Nat → Py Nat
  | [] => .ok acc
  | c :: cs =>
    match b32rev alpha c with
    | none => .error (err "Non-base32 digit found")
    | some v => b32Quanta alpha (acc * 32 + v) cs

/-- The outer loop, `Lib/base64.py:224-232`: the bytes and the last `acc`. -/
def b32DecLoop (alpha : List Nat) : (fuel : Nat) → List Nat → List Nat → Nat → Py (List Nat × Nat)
  | 0, _, dec, acc => .ok (dec, acc)
  | _ + 1, [], dec, acc => .ok (dec, acc)
  | fuel + 1, s, dec, _ => do
    let acc ← b32Quanta alpha 0 (s.take 8)
    b32DecLoop alpha fuel (s.drop 8) (dec ++ toBytes5 acc) acc

/-- `s.rstrip(b'=')`. -/
def rstripPad (s : List Nat) : List Nat := (s.reverse.dropWhile (· == 61)).reverse

/-- `_b32decode`, `Lib/base64.py:198-241`. -/
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

/-- `b16encode`, `Lib/base64.py:267-270`. -/
def b16encode (s : List Nat) : List Nat := upper (b2aHex s)

/-- `b16decode`, `Lib/base64.py:273-288`. -/
def b16decode (s0 : Data) (casefold : Bool) : Py (List Nat) := do
  let s ← bytesFromDecodeData s0
  let s := if casefold then upper s else s
  if s.any (fun c => !(("0123456789ABCDEF".toList.map Char.toNat).contains c)) then
    throw (err "Non-base16 digit found")
  a2bHex (.bytes s)

end PyLean.TextLibs.Binascii
