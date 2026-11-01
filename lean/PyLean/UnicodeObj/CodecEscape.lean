import PyLean.UnicodeObj.CodecAscii

/-!
`unicode_escape` and `raw_unicode_escape`: `_PyUnicode_DecodeUnicodeEscapeInternal2`
(unicodeobject.c:6522-6769), `PyUnicode_AsUnicodeEscapeString` (:6821-6919),
`_PyUnicode_DecodeRawUnicodeEscapeStateful` (:6924-7057) and
`PyUnicode_AsRawUnicodeEscapeString` (:7069-7131).

`\N{...}` looks names up in the Unicode name database, which the model takes as the
parameter `nameToCode`, supplied by the difftest. The `DeprecationWarning` for an invalid
escape (:6772-6808) has no effect on the result and is not modelled.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- The value of a hex digit, as the three branches at unicodeobject.c:6664-6676 compute it. -/
def hexValue (c : Nat) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87)
  else if 65 ≤ c ∧ c ≤ 70 then some (c - 55)
  else none

/-- The `hexescape` loop: the value of `count` digits, or how many digits were read before
a bad one (`.error (n, false)`) or before the end of the input (`.error (n, true)`). -/
def hexEscape : Nat → List Nat → Nat → Nat → Except (Nat × Bool) Nat
  | 0, _, _, acc => .ok acc
  | _ + 1, [], n, _ => .error (n, true)
  | count + 1, c :: cs, n, acc =>
    match hexValue c with
    | some v => hexEscape count cs (n + 1) (acc * 16 + v)
    | none => .error (n, false)

/-- A `\`-escape of `unicode_escape` of a hex form: `prefix` bytes before the digits. -/
def stepHex (consumed : Bool) (count : Nat) (message : String) (rest : List Nat) : DStep :=
  match hexEscape count rest 0 0 with
  | .ok ch =>
    if ch > maxUnicode then .fail "illegal Unicode character" 0 (2 + count)
    else .char ch (2 + count)
  | .error (n, true) => if consumed then .stop else .fail message 0 (2 + n)
  | .error (n, false) => .fail message 0 (2 + n)

/-- The name in `\N{name}`: the bytes up to `}`, or `none` if there is no `}`. -/
def nameBytes : List Nat → Option (List Nat)
  | [] => none
  | 125 :: _ => some []
  | c :: cs => (nameBytes cs).map (c :: ·)

/-- The `\N` case, unicodeobject.c:6686-6718. `rest` follows the `N`. -/
def stepName (nameToCode : List Nat → Option Nat) (consumed : Bool) (rest : List Nat) : DStep :=
  let malformed := "malformed \\N character escape"
  match rest with
  | [] => if consumed then .stop else .fail malformed 0 2
  | 123 :: t =>
    match nameBytes t with
    | none => if consumed then .stop else .fail malformed 0 (3 + t.length)
    | some [] => .fail malformed 0 3
    | some name =>
      match nameToCode name with
      | some ch => .char ch (4 + name.length)
      | none => .fail "unknown Unicode character name" 0 (4 + name.length)
  | _ => .fail malformed 0 2

/-- One octal escape, unicodeobject.c:6640-6655: the value and the digits after the first. -/
def octalEscape (d0 : Nat) : List Nat → Nat × Nat
  | a :: b :: _ =>
    if 48 ≤ a ∧ a ≤ 55 then
      if 48 ≤ b ∧ b ≤ 55 then ((d0 * 8 + (a - 48)) * 8 + (b - 48), 2)
      else (d0 * 8 + (a - 48), 1)
    else (d0, 0)
  | [a] => if 48 ≤ a ∧ a ≤ 55 then (d0 * 8 + (a - 48), 1) else (d0, 0)
  | [] => (d0, 0)

/-- One round of the loop of the `unicode_escape` decoder, unicodeobject.c:6577-6746. -/
def stepUnicodeEscape (nameToCode : List Nat → Option Nat) (consumed : Bool) : List Nat → DStep
  | [] => .stop
  | c :: t =>
    if c != 92 then .char c 1
    else
      match t with
      | [] => if consumed then .stop else .fail "\\ at end of string" 0 1
      | e :: r =>
        if e == 10 then .multi [] 2
        else if e == 92 then .char 92 2
        else if e == 39 then .char 39 2
        else if e == 34 then .char 34 2
        else if e == 98 then .char 8 2
        else if e == 102 then .char 12 2
        else if e == 116 then .char 9 2
        else if e == 110 then .char 10 2
        else if e == 114 then .char 13 2
        else if e == 118 then .char 11 2
        else if e == 97 then .char 7 2
        else if 48 ≤ e ∧ e ≤ 55 then
          let (ch, n) := octalEscape (e - 48) r
          .char ch (2 + n)
        else if e == 120 then stepHex consumed 2 "truncated \\xXX escape" r
        else if e == 117 then stepHex consumed 4 "truncated \\uXXXX escape" r
        else if e == 85 then stepHex consumed 8 "truncated \\UXXXXXXXX escape" r
        else if e == 78 then stepName nameToCode consumed r
        else .multi [92, e] 2

/-- `_PyUnicode_DecodeUnicodeEscapeInternal2`, unicodeobject.c:6522-6769. -/
def unicodeEscapeDecode (input : Bytes) (h : ErrHandler) (nameToCode : List Nat → Option Nat)
    (final : Bool) : Py (Str × Nat) :=
  if input.isEmpty then .ok ([], 0)
  else
    decodeDriver (stepUnicodeEscape nameToCode !final) h "unicodeescape" .unknown input
      (input.length + 1) 0 input []

/-- `\xHH`, `\uHHHH` or `\U00HHHHHH`, with the digits as `/` and `%` of `ch`. -/
def hex2 (c : Nat) : Bytes := [hexLower (c / 16 % 16), hexLower (c % 16)]
def hex4 (c : Nat) : Bytes := [hexLower (c / 4096 % 16), hexLower (c / 256 % 16)] ++ hex2 c
def hex8 (c : Nat) : Bytes :=
  [48, 48, hexLower (c / 1048576 % 16), hexLower (c / 65536 % 16)] ++ hex4 c

/-- The bytes `PyUnicode_AsUnicodeEscapeString` writes for one character,
unicodeobject.c:6855-6916. -/
def unicodeEscapeChar (ch : Nat) : Bytes :=
  if ch < 0x100 then
    if ch ≥ 32 ∧ ch < 127 then
      if ch != 92 then [ch] else [92, 92]
    else if ch = 9 then [92, 116]
    else if ch = 10 then [92, 110]
    else if ch = 13 then [92, 114]
    else [92, 120] ++ hex2 ch
  else if ch < 0x10000 then [92, 117] ++ hex4 ch
  else [92, 85] ++ hex8 ch

/-- `PyUnicode_AsUnicodeEscapeString`, unicodeobject.c:6821-6919. -/
def unicodeEscapeEncode (s : Str) : Bytes := s.flatMap unicodeEscapeChar

/-- The `\\u` and `\\U` forms of the raw decoder, unicodeobject.c:6994-7027. -/
def rawHex (consumed : Bool) (count : Nat) (message : String) (r : List Nat) : DStep :=
  match hexEscape count r 0 0 with
  | .ok ch =>
    if ch > maxUnicode then .fail "\\Uxxxxxxxx out of range" 0 (2 + count)
    else .char ch (2 + count)
  | .error (n, true) => if consumed then .stop else .fail message 0 (2 + n)
  | .error (n, false) => .fail message 0 (2 + n)

/-- One round of the loop of the raw decoder, unicodeobject.c:6961-7047. -/
def stepRawEscape (consumed : Bool) : List Nat → DStep
  | [] => .stop
  | c :: t =>
    if c != 92 then .char c 1
    else
      match t with
      | [] => if consumed then .stop else .char c 1
      | e :: r =>
        if e == 117 then rawHex consumed 4 "truncated \\uXXXX escape" r
        else if e == 85 then rawHex consumed 8 "truncated \\UXXXXXXXX escape" r
        else .multi [92, e] 2

/-- `_PyUnicode_DecodeRawUnicodeEscapeStateful`, unicodeobject.c:6924-7057. -/
def rawEscapeDecode (input : Bytes) (h : ErrHandler) (final : Bool) : Py (Str × Nat) :=
  if input.isEmpty then .ok ([], 0)
  else
    decodeDriver (stepRawEscape !final) h "rawunicodeescape" .unknown input (input.length + 1) 0
      input []

/-- The bytes `PyUnicode_AsRawUnicodeEscapeString` writes for one character,
unicodeobject.c@3.14.7:7223-7252. -/
def rawEscapeChar (ch : Nat) : Bytes :=
  if ch < 0x100 then [ch]
  else if ch < 0x10000 then [92, 117] ++ hex4 ch
  else [92, 85] ++ hex8 ch

/-- `PyUnicode_AsRawUnicodeEscapeString`, unicodeobject.c:7069-7131. -/
def rawEscapeEncode (s : Str) : Bytes := s.flatMap rawEscapeChar

end PyLean.UnicodeObj
