import PyLean.Ipaddress.Model

/-!
IPv4 text: `_BaseV4._parse_octet` (Lib/ipaddress.py:1206-1239), `_BaseV4._ip_int_from_string`
(:1180-1203), `_BaseV4._string_from_ip_int` (:1242-1252), `IPv4Address.__init__` (:1269-1302) with
`_check_int_address` (:407-414) and `_check_packed_address` (:416-421), and `_BaseAddress.__str__`
(:601-602), CPython 3.15.2.

Strings are lists of code points. A message embeds `%r` of a string; it is rendered exactly when the
string is printable ASCII with no quote or backslash (then `repr` is the string in single quotes),
and otherwise the message is `~` (compared by class only).
-/

namespace PyLean.Ipaddress

open PyLean

/-- `repr(s)` when it is `'s'`: printable ASCII without `'` or `\`. -/
def reprPlain (s : List Char) : Option String :=
  if s.all (fun c => 32 ≤ c.toNat && c.toNat < 127 && c != '\'' && c != '\\') then
    some ("'" ++ String.ofList s ++ "'")
  else none

/-- `str.split(sep)` for a one-character separator. -/
def splitOn1 (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = sep then [] :: splitOn1 sep cs
    else match splitOn1 sep cs with
      | p :: ps => (c :: p) :: ps
      | [] => [[c]]

/-- `sep.join(parts)` for a one-character separator. -/
def joinOn1 (sep : Char) : List (List Char) → List Char
  | [] => []
  | [p] => p
  | p :: ps => p ++ sep :: joinOn1 sep ps

/-- `c.isascii() and c.isdigit()` for one character: `0` to `9`. -/
def isDigitC (c : Char) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

/-- `int(s, 10)` on ASCII digits. -/
def digitsVal (s : List Char) : Nat := s.foldl (fun v c => v * 10 + (c.toNat - 48)) 0

/-- The `ValueError`s `_parse_octet` raises. -/
inductive OctetErr where
  | empty
  | nonDigit
  | tooLong
  | leadingZero
  | tooBig (v : Nat)
  deriving DecidableEq, Repr

/-- `_BaseV4._parse_octet`, ipaddress.py:1206-1239, check for check. -/
def parseOctet (s : List Char) : Except OctetErr Nat :=
  if s.isEmpty then .error .empty
  else if !(s.all isDigitC) then .error .nonDigit
  else if s.length > 3 then .error .tooLong
  else if s ≠ ['0'] ∧ s.head? = some '0' then .error .leadingZero
  else
    let v := digitsVal s
    if v > 255 then .error (.tooBig v) else .ok v

/-- `str(exc)` of those errors. -/
def octetMsg (s : List Char) : OctetErr → Option String
  | .empty => some "Empty octet not permitted"
  | .nonDigit => (reprPlain s).map ("Only decimal digits permitted in " ++ ·)
  | .tooLong => (reprPlain s).map ("At most 3 characters permitted in " ++ ·)
  | .leadingZero => (reprPlain s).map ("Leading zeros are not permitted in " ++ ·)
  | .tooBig v => some s!"Octet {v} (> 255) not permitted"

def avErr (m : Option String) : PyExc :=
  .named "AddressValueError" (m.getD "~AddressValueError")

/-- The octets parsed left to right, the first error kept with its octet: `map(_parse_octet, octets)`
consumed by `int.from_bytes`. -/
def parseOctets : List (List Char) → Except (List Char × OctetErr) (List Nat)
  | [] => .ok []
  | o :: os =>
    match parseOctet o with
    | .error e => .error (o, e)
    | .ok v => (parseOctets os).map (v :: ·)

/-- `int.from_bytes(bs, 'big')`. -/
def fromBytesBig (bs : List Nat) : Nat := bs.foldl (fun v b => v * 256 + b) 0

/-- `_BaseV4._ip_int_from_string`, ipaddress.py:1180-1203. -/
def ipIntFromString4 (s : List Char) : Py Nat :=
  if s.isEmpty then .error (avErr (some "Address cannot be empty"))
  else
    let octets := splitOn1 '.' s
    if octets.length ≠ 4 then .error (avErr ((reprPlain s).map ("Expected 4 octets in " ++ ·)))
    else
      match parseOctets octets with
      | .ok bs => .ok (fromBytesBig bs)
      | .error (o, e) =>
        .error (avErr (do let m ← octetMsg o e; let r ← reprPlain s; pure (m ++ " in " ++ r)))

/-- `ip_int.to_bytes(4, 'big')` for `ip_int < 2**32`. -/
def toBytes4 (n : Nat) : List Nat := [n / 2 ^ 24 % 256, n / 2 ^ 16 % 256, n / 2 ^ 8 % 256, n % 256]

/-- `_BaseV4._string_from_ip_int`, ipaddress.py:1242-1252: `'.'.join(map(str, ...))`. -/
def stringFromIpInt4 (n : Nat) : List Char :=
  joinOn1 '.' ((toBytes4 n).map (fun b => (toString b).toList))

/-- The argument of `IPv4Address(address)`: an int, a bytes object, or anything else, which is
taken through `str()` (here its string). -/
inductive AddrArg where
  | int (v : Int)
  | bytes (b : List Nat)
  | str (s : List Char)

/-- `IPv4Address.__init__`, ipaddress.py:1269-1302: the `_ip` it stores. The int branch
(:1286-1289) and the bytes branch (:1292-1295, `int.from_bytes(address)` is big-endian), then
`str(address)` (:1299-1302). -/
def ipv4Init (a : AddrArg) : Py Nat :=
  match a with
  | .int v => checkIntAddress 32 v
  | .bytes b => do
    checkPackedAddress 32 4 b
    pure (fromBytesBig b)
  | .str s =>
    if '/' ∈ s then .error (avErr ((reprPlain s).map ("Unexpected '/' in " ++ ·)))
    else ipIntFromString4 s

/-- `str(IPv4Address)`, `_BaseAddress.__str__`, ipaddress.py:601-602. -/
def ipv4Str (ip : Nat) : List Char := stringFromIpInt4 ip

end PyLean.Ipaddress
