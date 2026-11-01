import PyLean.Pickle.Basic

/-!
Integers in pickle: the binary encodings (`BININT*`, `LONG1`, `LONG4`), the
protocol 0/1 text encodings (`INT`, `LONG`), and the text parsers used by the
two unpicklers.
-/

namespace PyLean.Pickle

open PyLean

/-! ## Two's-complement encodings -/

/-- `encode_long` (`Lib/pickle.py:372-400`). `x.bit_length()` is the bit length
of `|x|`. -/
def encodeLong (x : Int) : Bytes :=
  if x = 0 then [] else
  let nbytes := bitLength x.natAbs / 8 + 1
  let result := toBytesSigned x nbytes
  if x < 0 ∧ nbytes > 1 then
    if result.getLast? = some 0xff ∧ (result.getD (nbytes - 2) 0 &&& 0x80) ≠ 0 then
      result.dropLast
    else result
  else result

/-- `decode_long` (`Lib/pickle.py:402-420`) and `_PyLong_FromByteArray(.., 1, 1)`. -/
def decodeLong (b : Bytes) : Int := leInt b

/-- `struct.pack("<i", n)`. -/
def packI32 (n : Int) : Py Bytes :=
  if -2147483648 ≤ n ∧ n ≤ 2147483647 then .ok (toBytesSigned n 4)
  else .error (structError "'i' format requires -2147483648 <= number <= 2147483647")

/-- `struct.pack("<I", n)`. -/
def packU32 (n : Nat) : Py Bytes :=
  if n ≤ 4294967295 then .ok (leBytes n 4)
  else .error (structError "'I' format requires 0 <= number <= 4294967295")

/-- `_Pickler.save_long` (`Lib/pickle.py:822-851`). `bin` is `proto >= 1`. -/
def pySaveLong (proto : Nat) (x : Int) : Py Bytes :=
  let bin := proto ≥ 1
  let fits32 := -0x80000000 ≤ x ∧ x ≤ 0x7fffffff
  if bin ∧ x ≥ 0 ∧ x ≤ 0xff then .ok (oBININT1 :: leBytes x.toNat 1)
  else if bin ∧ x ≥ 0 ∧ x ≤ 0xffff then .ok (oBININT2 :: leBytes x.toNat 2)
  else if bin ∧ fits32 then .ok (oBININT :: toBytesSigned x 4)
  else if proto ≥ 2 then
    let encoded := encodeLong x
    let n := encoded.length
    if n < 256 then .ok (oLONG1 :: leBytes n 1 ++ encoded)
    else do
      let hdr ← packI32 n
      .ok (oLONG4 :: hdr ++ encoded)
  else if fits32 then .ok (oINT :: decInt x ++ [nl])
  else do
    let r ← reprInt x
    .ok (oLONG :: r ++ [0x4c, nl])

/-- The C byte count and two's-complement bytes of a nonzero int
(`Modules/_pickle.c:2404-2441`): `nbytes` is computed before trimming and
checked against `0x7fffffff`. -/
def cLongBytes (x : Int) : Py Bytes :=
  let nbits := bitLength x.natAbs
  let nbytes := nbits / 8 + 1
  if nbytes > 0x7fffffff then .error (.overflowError "int too large to pickle")
  else
    let pdata := toBytesSigned x nbytes
    if x < 0 ∧ nbytes > 1 ∧ pdata.getD (nbytes - 1) 0 = 0xff ∧ (pdata.getD (nbytes - 2) 0 &&& 0x80) ≠ 0
    then .ok (pdata.take (nbytes - 1))
    else .ok pdata

/-- `save_long` in `Modules/_pickle.c:2338-2501`. The 4-byte fast path writes
the low bytes of `val` and picks the opcode from which bytes are nonzero. -/
def cSaveLong (proto : Nat) (x : Int) : Py Bytes :=
  let bin := proto ≥ 1
  if -0x80000000 ≤ x ∧ x ≤ 0x7fffffff then
    if bin then
      let p := toBytesSigned x 4
      if p.getD 3 0 ≠ 0 ∨ p.getD 2 0 ≠ 0 then .ok (oBININT :: p)
      else if p.getD 1 0 ≠ 0 then .ok (oBININT2 :: p.take 2)
      else .ok (oBININT1 :: p.take 1)
    else .ok (oINT :: decInt x ++ [nl])
  else if proto ≥ 2 then
    -- x ≠ 0 here: zero takes the fast path above.
    do
      let pdata ← cLongBytes x
      let n := pdata.length
      if n < 256 then .ok (oLONG1 :: leBytes n 1 ++ pdata)
      else .ok (oLONG4 :: leBytes n 4 ++ pdata)
  else do
    let r ← reprInt x
    .ok (oLONG :: r ++ [0x4c, nl])

/-! ## Text parsers -/

/-- Result of `PyLong_FromString(str, &pend, 10)` on a NUL-terminated string
(`Objects/longobject.c:3055-3159`, `long_from_string_base` at :2962-3052). -/
inductive PLRes where
  /-- success; the value. `pend` then points at the terminating NUL. -/
  | ok (v : Int)
  /-- `invalid literal` (syntax error), `pend` set. -/
  | syntax
  /-- the 4300-digit limit (`pend` not set); number of digits. -/
  | limit (digits : Nat)
  deriving Repr, DecidableEq

def skipSpace : Bytes → Bytes
  | c :: r => if isSpace c then skipSpace r else c :: r
  | [] => []

/-- Scan digits and underscores (`long_from_string_base`'s loop): returns the
digit values, whether the scan is valid (no double or trailing underscore),
and the rest. `prevUnd` records whether the previous character was `_`. -/
def scanDigits : Bool → Bytes → List Nat × Bool × Bytes
  | prevUnd, c :: r =>
    if isDigit c then
      let (ds, ok, rest) := scanDigits false r
      ((c.toNat - 48) :: ds, ok, rest)
    else if c == 0x5f then
      if prevUnd then ([], false, c :: r)
      else scanDigits true r
    else ([], !prevUnd, c :: r)
  | prevUnd, [] => ([], !prevUnd, [])

def digitsVal (ds : List Nat) : Nat := ds.foldl (fun a d => 10 * a + d) 0

/-- The optional sign: is it negative, and the rest. -/
def signSplit : Bytes → Bool × Bytes
  | 0x2b :: r => (false, r)
  | 0x2d :: r => (true, r)
  | r => (false, r)

/-- `long_from_string_base` (`Objects/longobject.c:2962-3052`) on the text
after the sign, then the sign. -/
def lfsBase (neg : Bool) (s2 : Bytes) : PLRes :=
  match s2 with
  | 0x5f :: _ => .syntax
  | _ =>
    let (ds, ok, rest) := scanDigits false s2
    if !ok then .syntax
    else if ds = [] then .syntax
    else if skipSpace rest ≠ [] then .syntax
    else if ds.length > maxStrDigits then .limit ds.length
    else
      let v : Int := digitsVal ds
      .ok (if neg then -v else v)

/-- `PyLong_FromString(s, pend, 10)` (`Objects/longobject.c:3055-3159`) where
`s` is the C string (the bytes before the first NUL): leading whitespace, an
optional sign, then `long_from_string_base`. -/
def pyLongFromString (s : Bytes) : PLRes :=
  let p := signSplit (skipSpace s)
  lfsBase p.1 p.2

def invalidLiteral (b : Bytes) : PyExc :=
  .valueError s!"invalid literal for int() with base 10: {(bytesRepr (b.take 200)).take 200}"

/-- `int(b)` for a bytes object: `_PyLong_FromBytes` (`Objects/longobject.c:3166-3183`)
rejects anything after an embedded NUL. -/
def pyIntOfBytes (b : Bytes) : Py Int :=
  let cstr := b.takeWhile (· ≠ 0)
  match pyLongFromString cstr with
  | .ok v => if cstr.length = b.length then .ok v else .error (invalidLiteral b)
  | .syntax => .error (invalidLiteral b)
  | .limit d => .error (.valueError (limitToIntMsg d))

/-- The exception `PyLong_FromString` raises in C for a syntax error: the
message is built from the first 200 bytes decoded as UTF-8, which itself raises
`UnicodeDecodeError` on invalid UTF-8 (`Objects/longobject.c:3150-3158`). -/
def cLongSyntaxError (cstr : Bytes) : PyExc :=
  if (utf8Dec false (cstr.take 200)).isSome then .valueError "~invalid literal for int() with base 10"
  else unicodeDecodeError

/-- `PyLong_FromString(s, NULL, 10)` in C on the line buffer (NUL-terminated
copy of the line, `Modules/_pickle.c:1585-1598`). -/
def cLongFromLine (line : Bytes) : Py Int :=
  let cstr := line.takeWhile (· ≠ 0)
  match pyLongFromString cstr with
  | .ok v => .ok v
  | .syntax => .error (cLongSyntaxError cstr)
  | .limit d => .error (.valueError (limitToIntMsg d))

/-- C `long` on LP64. -/
def longMin : Int := -(2 ^ 63)
def longMax : Int := 2 ^ 63 - 1

/-- `strtol(s, &endptr, 10)` on a NUL-terminated string: the value (clamped),
the number of bytes consumed (`endptr - s`, `0` when no digits), and whether
`errno` is set (`ERANGE`). This is glibc, where the differential test runs: no
conversion leaves `errno` alone. Darwin's libc sets `EINVAL` there, which only
matters for a line that starts with a NUL byte (`I\0\n` is `0` on Linux and a
`ValueError` on macOS). -/
def strtol (s : Bytes) : Int × Nat × Bool :=
  let cstr := s.takeWhile (· ≠ 0)
  let p := signSplit (skipSpace cstr)
  let s2 := p.2
  let ds := s2.takeWhile isDigit
  if ds = [] then (0, 0, false)
  else
    let v : Int := digitsVal (ds.map (fun c => c.toNat - 48))
    let v := if p.1 then -v else v
    let consumed := cstr.length - (s2.length - ds.length)
    if v < longMin then (longMin, consumed, true)
    else if v > longMax then (longMax, consumed, true)
    else (v, consumed, false)

/-- Values an `INT`/`LONG` line can decode to: an int, or a bool. -/
inductive IntVal where
  | int (v : Int)
  | bool (b : Bool)
  deriving Repr, DecidableEq

/-- `_Unpickler.load_int` after `readline()` (`Lib/pickle.py:1402-1411`). -/
def pyLoadIntLine (data : Bytes) : Py IntVal :=
  if data = [0x30, 0x30, nl] then .ok (.bool false)
  else if data = [0x30, 0x31, nl] then .ok (.bool true)
  else .int <$> pyIntOfBytes data

/-- `load_int` (`Modules/_pickle.c:5521-5562`) on a line returned by
`_Unpickler_Readline` (which always ends in `\n`). -/
def cLoadIntLine (s : Bytes) : Py IntVal :=
  if s.length < 2 then .error (unpicklingError "pickle data was truncated")
  else
    let (x, consumed, erange) := strtol s
    let endc := s.getD consumed 0
    if erange || (endc != nl && endc != 0) then
      match cLongFromLine s with
      | .ok v => .ok (.int v)
      | .error _ => .error (.valueError "could not convert string to int")
    else if s.length = 3 ∧ (x = 0 ∨ x = 1) then .ok (.bool (x = 1))
    else .ok (.int x)

/-- `_Unpickler.load_long` after `readline()` (`Lib/pickle.py:1425-1430`). -/
def pyLoadLongLine (line : Bytes) : Py Int :=
  let val := line.dropLast
  let val := if val ≠ [] ∧ val.getLast? = some 0x4c then val.dropLast else val
  pyIntOfBytes val

/-- `load_long` (`Modules/_pickle.c:5674-5700`): a final `L` before the newline
is overwritten with NUL. -/
def cLoadLongLine (s : Bytes) : Py Int :=
  if s.length < 2 then .error (unpicklingError "pickle data was truncated")
  else
    let s := if s.getD (s.length - 2) 0 = 0x4c then s.set (s.length - 2) 0 else s
    cLongFromLine s

end PyLean.Pickle
