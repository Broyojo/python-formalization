import PyLean.Core

/-!
Byte-level vocabulary shared by the pickle models (CPython 3.14.7).

* A pickle stream is `Bytes := List UInt8`.
* A Python `str` is a list of code points (`List Nat`, each `< 0x110000`,
  lone surrogates allowed), since Lean's `Char` excludes surrogates.
* Exceptions that `Core.PyExc` has no constructor for use `PyExc.named`:
  `UnpicklingError`, `PicklingError`, `EOFError`, `AttributeError`,
  `UnicodeDecodeError`, and `error` (`struct.error`).
-/

namespace PyLean.Pickle

open PyLean

abbrev Bytes := List UInt8

/-! ## Opcodes (`Lib/pickle.py:105-186`) -/

def oMARK : UInt8 := 0x28            -- '('
def oSTOP : UInt8 := 0x2e            -- '.'
def oPOP : UInt8 := 0x30             -- '0'
def oPOP_MARK : UInt8 := 0x31        -- '1'
def oDUP : UInt8 := 0x32             -- '2'
def oFLOAT : UInt8 := 0x46           -- 'F'
def oINT : UInt8 := 0x49             -- 'I'
def oBININT : UInt8 := 0x4a          -- 'J'
def oBININT1 : UInt8 := 0x4b         -- 'K'
def oLONG : UInt8 := 0x4c            -- 'L'
def oBININT2 : UInt8 := 0x4d         -- 'M'
def oNONE : UInt8 := 0x4e            -- 'N'
def oPERSID : UInt8 := 0x50          -- 'P'
def oBINPERSID : UInt8 := 0x51       -- 'Q'
def oREDUCE : UInt8 := 0x52          -- 'R'
def oSTRING : UInt8 := 0x53          -- 'S'
def oBINSTRING : UInt8 := 0x54       -- 'T'
def oSHORT_BINSTRING : UInt8 := 0x55 -- 'U'
def oUNICODE : UInt8 := 0x56         -- 'V'
def oBINUNICODE : UInt8 := 0x58      -- 'X'
def oAPPEND : UInt8 := 0x61          -- 'a'
def oBUILD : UInt8 := 0x62           -- 'b'
def oGLOBAL : UInt8 := 0x63          -- 'c'
def oDICT : UInt8 := 0x64            -- 'd'
def oEMPTY_DICT : UInt8 := 0x7d      -- '}'
def oAPPENDS : UInt8 := 0x65         -- 'e'
def oGET : UInt8 := 0x67             -- 'g'
def oBINGET : UInt8 := 0x68          -- 'h'
def oINST : UInt8 := 0x69            -- 'i'
def oLONG_BINGET : UInt8 := 0x6a     -- 'j'
def oLIST : UInt8 := 0x6c            -- 'l'
def oEMPTY_LIST : UInt8 := 0x5d      -- ']'
def oOBJ : UInt8 := 0x6f             -- 'o'
def oPUT : UInt8 := 0x70             -- 'p'
def oBINPUT : UInt8 := 0x71          -- 'q'
def oLONG_BINPUT : UInt8 := 0x72     -- 'r'
def oSETITEM : UInt8 := 0x73         -- 's'
def oTUPLE : UInt8 := 0x74           -- 't'
def oEMPTY_TUPLE : UInt8 := 0x29     -- ')'
def oSETITEMS : UInt8 := 0x75        -- 'u'
def oBINFLOAT : UInt8 := 0x47        -- 'G'
def oPROTO : UInt8 := 0x80
def oNEWOBJ : UInt8 := 0x81
def oEXT1 : UInt8 := 0x82
def oEXT2 : UInt8 := 0x83
def oEXT4 : UInt8 := 0x84
def oTUPLE1 : UInt8 := 0x85
def oTUPLE2 : UInt8 := 0x86
def oTUPLE3 : UInt8 := 0x87
def oNEWTRUE : UInt8 := 0x88
def oNEWFALSE : UInt8 := 0x89
def oLONG1 : UInt8 := 0x8a
def oLONG4 : UInt8 := 0x8b
def oBINBYTES : UInt8 := 0x42        -- 'B'
def oSHORT_BINBYTES : UInt8 := 0x43  -- 'C'
def oSHORT_BINUNICODE : UInt8 := 0x8c
def oBINUNICODE8 : UInt8 := 0x8d
def oBINBYTES8 : UInt8 := 0x8e
def oEMPTY_SET : UInt8 := 0x8f
def oADDITEMS : UInt8 := 0x90
def oFROZENSET : UInt8 := 0x91
def oNEWOBJ_EX : UInt8 := 0x92
def oSTACK_GLOBAL : UInt8 := 0x93
def oMEMOIZE : UInt8 := 0x94
def oFRAME : UInt8 := 0x95
def oBYTEARRAY8 : UInt8 := 0x96
def oNEXT_BUFFER : UInt8 := 0x97
def oREADONLY_BUFFER : UInt8 := 0x98

def nl : UInt8 := 0x0a

/-! ## Little-endian integers (`struct.pack`, `calc_binsize`, `calc_binint`) -/

/-- `k` little-endian bytes of `n mod 256^k`. -/
def leBytes : Nat → Nat → Bytes
  | _, 0 => []
  | n, k + 1 => (n % 256).toUInt8 :: leBytes (n / 256) k

/-- Unsigned little-endian value of a byte string. -/
def leNat : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

/-- Signed (two's complement) little-endian value: `int.from_bytes(b, 'little',
signed=True)`; the empty string is `0`. -/
def leInt (bs : Bytes) : Int :=
  if bs ≠ [] ∧ leNat bs ≥ 2 ^ (8 * bs.length - 1) then (leNat bs : Int) - 2 ^ (8 * bs.length)
  else leNat bs

/-- `x.to_bytes(n, 'little', signed=True)` for an `x` that fits. -/
def toBytesSigned (x : Int) (n : Nat) : Bytes :=
  leBytes (x % ((2 : Int) ^ (8 * n))).toNat n

/-- `PY_SSIZE_T_MAX` and `sys.maxsize` on a 64-bit build. -/
def ssizeMaxN : Nat := 2 ^ 63 - 1

/-! ## ASCII helpers -/

def ascii (s : String) : Bytes := s.toList.map (fun c => c.toNat.toUInt8)

/-- Decimal digits of `n` as ASCII bytes, most significant first. -/
def decDigits (n : Nat) : Bytes :=
  if h : n < 10 then [(48 + n).toUInt8]
  else decDigits (n / 10) ++ [(48 + n % 10).toUInt8]
termination_by n
decreasing_by omega

/-- `repr(x)` of an int, ignoring the digit limit. -/
def decInt (x : Int) : Bytes :=
  if x < 0 then 0x2d :: decDigits x.natAbs else decDigits x.natAbs

/-- `sys.get_int_max_str_digits()` default (`_PY_LONG_DEFAULT_MAX_STR_DIGITS`). -/
def maxStrDigits : Nat := 4300

def limitToStrMsg : String :=
  "Exceeds the limit (4300 digits) for integer string conversion; use sys.set_int_max_str_digits() to increase the limit"

def limitToIntMsg (digits : Nat) : String :=
  s!"Exceeds the limit (4300 digits) for integer string conversion: value has {digits} digits; use sys.set_int_max_str_digits() to increase the limit"

/-- `repr(x)` of an int (`Objects/longobject.c` `long_to_decimal_string_internal`):
`ValueError` beyond 4300 decimal digits. -/
def reprInt (x : Int) : Py Bytes :=
  if (decDigits x.natAbs).length > maxStrDigits then .error (.valueError limitToStrMsg)
  else .ok (decInt x)

def hexDigit (n : Nat) : UInt8 := if n < 10 then (48 + n).toUInt8 else (87 + n).toUInt8

/-- `repr(bytes)` (`Objects/bytesobject.c` `PyBytes_Repr`, smartquotes on). -/
def bytesRepr (b : Bytes) : String :=
  let quote : Char := if b.contains 0x27 && !b.contains 0x22 then '"' else '\''
  let body := b.foldl (fun acc c =>
    let n := c.toNat
    if n == quote.toNat || n == 0x5c then acc.push '\\' |>.push (Char.ofNat n)
    else if n == 0x09 then acc ++ "\\t"
    else if n == 0x0a then acc ++ "\\n"
    else if n == 0x0d then acc ++ "\\r"
    else if n < 0x20 || n ≥ 0x7f then
      acc ++ "\\x" |>.push (Char.ofNat (hexDigit (n / 16)).toNat) |>.push (Char.ofNat (hexDigit (n % 16)).toNat)
    else acc.push (Char.ofNat n)) ""
  "b" ++ quote.toString ++ body ++ quote.toString

/-- C `isspace` in the C locale and `Py_ISSPACE` (`Python/pyctype.c`): the same
six bytes. -/
def isSpace (c : UInt8) : Bool :=
  c == 0x20 || c == 0x09 || c == 0x0a || c == 0x0b || c == 0x0c || c == 0x0d

def isDigit (c : UInt8) : Bool := 0x30 ≤ c && c ≤ 0x39

/-! ## UTF-8 (`Objects/unicodeobject.c`, `Objects/stringlib/codecs.h`) -/

/-- `str.encode('utf-8', 'surrogatepass')`: lone surrogates are encoded like
any other code point below 0x10000. -/
def utf8Char (c : Nat) : Bytes :=
  if c < 0x80 then [c.toUInt8]
  else if c < 0x800 then [(0xc0 + c / 64).toUInt8, (0x80 + c % 64).toUInt8]
  else if c < 0x10000 then
    [(0xe0 + c / 4096).toUInt8, (0x80 + c / 64 % 64).toUInt8, (0x80 + c % 64).toUInt8]
  else [(0xf0 + c / 262144).toUInt8, (0x80 + c / 4096 % 64).toUInt8,
        (0x80 + c / 64 % 64).toUInt8, (0x80 + c % 64).toUInt8]

def utf8Enc (s : List Nat) : Bytes := s.flatMap utf8Char

def isCont (b : UInt8) : Bool := 0x80 ≤ b && b ≤ 0xbf

/-- The UTF-8 decoder with error handler `surrogatepass` (or `strict` when
`sp = false`): `none` when it raises `UnicodeDecodeError`. Structural on the
input; each step consumes 1-4 bytes. -/
def utf8Dec (sp : Bool) : Bytes → Option (List Nat)
  | [] => some []
  | b0 :: rest =>
    if b0 < 0x80 then (b0.toNat :: ·) <$> utf8Dec sp rest
    else if 0xc2 ≤ b0 && b0 ≤ 0xdf then
      match rest with
      | b1 :: r => if isCont b1 then
          (((b0.toNat - 0xc0) * 64 + (b1.toNat - 0x80)) :: ·) <$> utf8Dec sp r else none
      | _ => none
    else if 0xe0 ≤ b0 && b0 ≤ 0xef then
      match rest with
      | b1 :: b2 :: r =>
        let lo : UInt8 := if b0 == 0xe0 then 0xa0 else 0x80
        let hi : UInt8 := if b0 == 0xed && !sp then 0x9f else 0xbf
        if lo ≤ b1 && b1 ≤ hi && isCont b2 then
          (((b0.toNat - 0xe0) * 4096 + (b1.toNat - 0x80) * 64 + (b2.toNat - 0x80)) :: ·) <$> utf8Dec sp r
        else none
      | _ => none
    else if 0xf0 ≤ b0 && b0 ≤ 0xf4 then
      match rest with
      | b1 :: b2 :: b3 :: r =>
        let lo : UInt8 := if b0 == 0xf0 then 0x90 else 0x80
        let hi : UInt8 := if b0 == 0xf4 then 0x8f else 0xbf
        if lo ≤ b1 && b1 ≤ hi && isCont b2 && isCont b3 then
          (((b0.toNat - 0xf0) * 262144 + (b1.toNat - 0x80) * 4096 + (b2.toNat - 0x80) * 64
            + (b3.toNat - 0x80)) :: ·) <$> utf8Dec sp r
        else none
      | _ => none
    else none

/-- `UnicodeDecodeError`; the message embeds positions, so it is not compared. -/
def unicodeDecodeError : PyExc := .named "UnicodeDecodeError" "~can't decode"

def decodeUtf8SP (b : Bytes) : Py (List Nat) :=
  match utf8Dec true b with
  | some s => .ok s
  | none => .error unicodeDecodeError

/-- `bytes.decode('ascii')` (the default `encoding`/`errors` of `loads`). -/
def decodeAscii (b : Bytes) : Py (List Nat) :=
  if b.all (· < 0x80) then .ok (b.map (·.toNat)) else .error unicodeDecodeError

/-! ## raw-unicode-escape -/

/-- `PyUnicode_AsRawUnicodeEscapeString` (`Objects/unicodeobject.c`): code points
`>= 0x10000` as `\UXXXXXXXX`, `>= 0x100` as `\uXXXX` (lowercase hex), the rest as
Latin-1 bytes. -/
def rueChar (c : Nat) : Bytes :=
  if c ≥ 0x10000 then
    [0x5c, 0x55] ++ (List.range 8).reverse.map (fun i => hexDigit (c / 16 ^ i % 16))
  else if c ≥ 256 then
    [0x5c, 0x75] ++ (List.range 4).reverse.map (fun i => hexDigit (c / 16 ^ i % 16))
  else [c.toUInt8]

def rueEncode (s : List Nat) : Bytes := s.flatMap rueChar

def hexVal (c : UInt8) : Option Nat :=
  if 0x30 ≤ c && c ≤ 0x39 then some (c.toNat - 0x30)
  else if 0x61 ≤ c && c ≤ 0x66 then some (c.toNat - 0x61 + 10)
  else if 0x41 ≤ c && c ≤ 0x46 then some (c.toNat - 0x41 + 10)
  else none

/-- Read `k` hex digits, accumulating into `acc`. -/
def readHex : Nat → Nat → Bytes → Option (Nat × Bytes)
  | 0, acc, r => some (acc, r)
  | _ + 1, _, [] => none
  | k + 1, acc, c :: r => match hexVal c with
    | some d => readHex k (acc * 16 + d) r
    | none => none

theorem readHex_len {k acc : Nat} {r r' : Bytes} {ch : Nat} (h : readHex k acc r = some (ch, r')) :
    r'.length ≤ r.length := by
  induction k generalizing acc r with
  | zero => simp [readHex] at h; obtain ⟨_, rfl⟩ := h; omega
  | succ k ih =>
    cases r with
    | nil => simp [readHex] at h
    | cons c r =>
      simp only [readHex] at h
      split at h
      · have := ih h; simp; omega
      · simp at h

/-- `_PyUnicode_DecodeRawUnicodeEscapeStateful` with `errors='strict'` and no
`consumed` (`Objects/unicodeobject.c:7045-7176`). -/
def rueDecode : Bytes → Option (List Nat)
  | [] => some []
  | [c] => some [c.toNat]
  | c :: d :: r =>
    if c != 0x5c then (c.toNat :: ·) <$> rueDecode (d :: r)
    else if d == 0x75 || d == 0x55 then
      match hr : readHex (if d == 0x75 then 4 else 8) 0 r with
      | some (ch, r') => if ch > 0x10ffff then none else (ch :: ·) <$> rueDecode r'
      | none => none
    else (fun t => 0x5c :: d.toNat :: t) <$> rueDecode r
termination_by b => b.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := readHex_len hr; omega)

def decodeRUE (b : Bytes) : Py (List Nat) :=
  match rueDecode b with
  | some s => .ok s
  | none => .error (.named "UnicodeDecodeError" "~rawunicodeescape")

/-! ## Errors -/

def unpicklingError (m : String) : PyExc := .named "UnpicklingError" m
def picklingError (m : String) : PyExc := .named "PicklingError" m
def eofError (m : String) : PyExc := .named "EOFError" m
def structError (m : String) : PyExc := .named "error" m
def attributeError (m : String) : PyExc := .named "AttributeError" m
/-- Inputs the model deliberately does not cover (code-executing opcodes,
floats, out-of-band buffers). The differential test never generates them. -/
def excluded (m : String) : PyExc := .named "Excluded" m

end PyLean.Pickle
