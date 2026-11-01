import PyLean.PyGrammar.Peg.State

/-!
`Parser/string_parser.c` and the escape decoders it calls
(`_PyUnicode_DecodeUnicodeEscapeInternal2` in `Objects/unicodeobject.c`,
`_PyBytes_DecodeEscape2` in `Objects/bytesobject.c`).
-/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- Outcome of a decoder: the value and the offset of the first invalid escape,
or an exception. -/
abbrev Dec (α : Type) := Except PyError (α × Option Nat)

/-- `str(UnicodeDecodeError)` for `'unicodeescape'`. -/
def uniErr (buf : Array Nat) (start stop : Nat) (reason : String) : PyError :=
  let msg :=
    if stop == start + 1 then
      let b := buf.getD start 0
      let hex := String.ofList (Nat.toDigits 16 b)
      let hex := if hex.length < 2 then "0" ++ hex else hex
      s!"'unicodeescape' codec can't decode byte 0x{hex} in position {start}: {reason}"
    else
      s!"'unicodeescape' codec can't decode bytes in position {start}-{stop - 1}: {reason}"
  { cls := "UnicodeDecodeError", msg }

/-- The hex-digit loop of `_PyUnicode_DecodeUnicodeEscapeInternal2`:
reads `count` digits at `s`. Returns the value, or the stop position on failure. -/
def hexDigits (buf : Array Nat) : Nat → Nat → Nat → Except Nat (Nat × Nat)
  | 0, s, ch => .ok (ch, s)
  | n + 1, s, ch =>
    if s ≥ buf.size then .error s
    else
      let d := digitVal (buf.getD s 0)
      if d < 16 then hexDigits buf n (s + 1) (ch <<< 4 + d) else .error s

/-- `_PyUnicode_DecodeUnicodeEscapeInternal2`. Bytes above 127 never occur in `buf`
because `decode_unicode_with_escapes` rewrites them first. `f` is fuel. -/
def decodeUnicodeEscape (ucn : List (List Nat × Nat)) (buf : Array Nat) :
    Nat → Nat → List Nat → Option Nat → Dec (List Nat)
  | 0, _, acc, inv => .ok (acc.reverse, inv)
  | f + 1, s, acc, inv =>
    if s ≥ buf.size then .ok (acc.reverse, inv) else
    let c := buf.getD s 0
    let s := s + 1
    if c != ch! '\\' then decodeUnicodeEscape ucn buf f s (c :: acc) inv else
    let start := s - 1
    if s ≥ buf.size then .error (uniErr buf start s "\\ at end of string") else
    let c := buf.getD s 0
    let s := s + 1
    let simple (v : Nat) := decodeUnicodeEscape ucn buf f s (v :: acc) inv
    if c == ch! '\n' then decodeUnicodeEscape ucn buf f s acc inv
    else if c == ch! '\\' then simple 92
    else if c == ch! '\'' then simple 39
    else if c == ch! '"' then simple 34
    else if c == ch! 'b' then simple 8
    else if c == ch! 'f' then simple 12
    else if c == ch! 't' then simple 9
    else if c == ch! 'n' then simple 10
    else if c == ch! 'r' then simple 13
    else if c == ch! 'v' then simple 11
    else if c == ch! 'a' then simple 7
    else if ch! '0' ≤ c && c ≤ ch! '7' then
      let isOct (x : Nat) := ch! '0' ≤ x && x ≤ ch! '7'
      let ch0 := c - 48
      let (ch1, s1) :=
        if s < buf.size && isOct (buf.getD s 0) then
          let ch1 := (ch0 <<< 3) + buf.getD s 0 - 48
          let s1 := s + 1
          if s1 < buf.size && isOct (buf.getD s1 0) then
            ((ch1 <<< 3) + buf.getD s1 0 - 48, s1 + 1)
          else (ch1, s1)
        else (ch0, s)
      let inv' := if ch1 > 0o377 && inv.isNone then some (s1 - 3) else inv
      decodeUnicodeEscape ucn buf f s1 (ch1 :: acc) inv'
    else if c == ch! 'x' || c == ch! 'u' || c == ch! 'U' then
      let (count, msg) : Nat × String :=
        if c == ch! 'x' then (2, "truncated \\xXX escape")
        else if c == ch! 'u' then (4, "truncated \\uXXXX escape")
        else (8, "truncated \\UXXXXXXXX escape")
      match hexDigits buf count s 0 with
      | .error stop => .error (uniErr buf start stop msg)
      | .ok (ch, s) =>
        if ch > 0x10FFFF then .error (uniErr buf start s "illegal Unicode character")
        else decodeUnicodeEscape ucn buf f s (ch :: acc) inv
    else if c == ch! 'N' then
      let malformed := "malformed \\N character escape"
      if s ≥ buf.size then .error (uniErr buf start s malformed)
      else if buf.getD s 0 == ch! '{' then
        let nameStart := s + 1
        let rest := (buf.extract nameStart buf.size).toList
        let name := rest.takeWhile (· != ch! '}')
        let close := nameStart + name.length
        if close ≥ buf.size then .error (uniErr buf start close malformed)
        else if name.isEmpty then .error (uniErr buf start close malformed)
        else
          let s := close + 1
          match ucn.find? (fun e => e.1 == name) with
          | some (_, ch) => decodeUnicodeEscape ucn buf f s (ch :: acc) inv
          | none => .error (uniErr buf start s "unknown Unicode character name")
      else .error (uniErr buf start s malformed)
    else
      let inv' := if inv.isNone then some (s - 1) else inv
      decodeUnicodeEscape ucn buf f s (c :: 92 :: acc) inv'

/-- `%08x` -/
def hex8 (c : Nat) : List Nat :=
  let ds := Nat.toDigits 16 c
  (List.replicate (8 - ds.length) '0' ++ ds).map Char.toNat

/-- The rewriting loop of `decode_unicode_with_escapes`, `Parser/string_parser.c:135-218`:
non-ASCII runs become `\UXXXXXXXX`, and a backslash before one, or at the end, `\u005c`. -/
def escapeNonAscii : Nat → List Nat → List Nat
  | 0, _ | _, [] => []
  | f + 1, s =>
    let (out, s) : List Nat × List Nat :=
      match s with
      | 92 :: r =>
        match r with
        | [] => ([92, 117, 48, 48, 53, 99], [])
        | c :: _ =>
          if c ≥ 0x80 then ([92, 117, 48, 48, 53, 99], r) else ([92], r)
      | _ => ([], s)
    match s with
    | [] => out
    | c :: r =>
      if c ≥ 0x80 then
        let run := s.takeWhile (· ≥ 0x80)
        let cps := utf8Decode run
        out ++ cps.flatMap (fun x => 92 :: 85 :: hex8 x) ++ escapeNonAscii f (s.drop run.length)
      else out ++ c :: escapeNonAscii f r

/-- `warn_invalid_escape_sequence`, `Parser/string_parser.c:14-119`, with warnings not
turned into errors. The message is what `PyErr_WarnExplicitObject` receives. -/
def warnInvalidEscapeSeq (buf : Array Nat) (ptr : Nat) (t : Token) : PM Unit := do
  let p ← get
  if p.callInvalidRules then return
  let c := buf.getD ptr 0
  if (t.type == TokKind.FSTRING_MIDDLE.num || t.type == TokKind.FSTRING_END.num
      || t.type == TokKind.TSTRING_MIDDLE.num || t.type == TokKind.TSTRING_END.num)
      && (c == ch! '{' || c == ch! '}') then return
  let octal := ch! '4' ≤ c && c ≤ ch! '7'
  let text3 := String.ofList ((buf.extract ptr (ptr + 3)).toList.map Char.ofNat)
  let msg :=
    if octal then
      s!"\"\\{text3}\" is an invalid octal escape sequence. Such sequences will not work in "
        ++ s!"the future. Did you mean \"\\\\{text3}\"? A raw string is also an option."
    else
      s!"\"\\{chStr c}\" is an invalid escape sequence. Such sequences will not work in the "
        ++ s!"future. Did you mean \"\\\\{chStr c}\"? A raw string is also an option."
  let category := if p.featureVersion ≥ 12 then "SyntaxWarning" else "DeprecationWarning"
  let lineno := t.lineno + (((buf.extract 0 ptr).toList.filter (· == 10)).length : Int)
  modify fun p => { p with tok := { p.tok with warnings := (category, msg, lineno) :: p.tok.warnings } }

/-- `decode_unicode_with_escapes`, `Parser/string_parser.c:135-218`. -/
def decodeUnicodeWithEscapes (s : List Nat) (t : Option Token) : PM (Option (List Nat)) := do
  let buf := (escapeNonAscii (s.length + 1) s).toArray
  let ucn := (← get).cfg.ucn
  match decodeUnicodeEscape ucn buf (buf.size + 1) 0 [] none with
  | .error e =>
    setErr e
    return none
  | .ok (v, inv) =>
    match inv, t with
    | some ptr, some tok => warnInvalidEscapeSeq buf ptr tok
    | _, _ => pure ()
    return some v

/-- `_PyBytes_DecodeEscape2`, `Objects/bytesobject.c`. -/
def decodeBytesEscape (buf : Array Nat) : Nat → Nat → List Nat → Option Nat → Dec (List Nat)
  | 0, _, acc, inv => .ok (acc.reverse, inv)
  | f + 1, s, acc, inv =>
    if s ≥ buf.size then .ok (acc.reverse, inv) else
    let c := buf.getD s 0
    if c != ch! '\\' then decodeBytesEscape buf f (s + 1) (c :: acc) inv else
    let s := s + 1
    if s == buf.size then .error { cls := "ValueError", msg := "Trailing \\ in string" } else
    let c := buf.getD s 0
    let s := s + 1
    let simple (v : Nat) := decodeBytesEscape buf f s (v :: acc) inv
    if c == ch! '\n' then decodeBytesEscape buf f s acc inv
    else if c == ch! '\\' then simple 92
    else if c == ch! '\'' then simple 39
    else if c == ch! '"' then simple 34
    else if c == ch! 'b' then simple 8
    else if c == ch! 'f' then simple 12
    else if c == ch! 't' then simple 9
    else if c == ch! 'n' then simple 10
    else if c == ch! 'r' then simple 13
    else if c == ch! 'v' then simple 11
    else if c == ch! 'a' then simple 7
    else if ch! '0' ≤ c && c ≤ ch! '7' then
      let isOct (x : Nat) := ch! '0' ≤ x && x ≤ ch! '7'
      let c0 := c - 48
      let (c1, s1) :=
        if s < buf.size && isOct (buf.getD s 0) then
          let c1 := (c0 <<< 3) + buf.getD s 0 - 48
          let s1 := s + 1
          if s1 < buf.size && isOct (buf.getD s1 0) then
            ((c1 <<< 3) + buf.getD s1 0 - 48, s1 + 1)
          else (c1, s1)
        else (c0, s)
      let inv' := if c1 > 0o377 && inv.isNone then some (s1 - 3) else inv
      decodeBytesEscape buf f s1 ((c1 % 256) :: acc) inv'
    else if c == ch! 'x' then
      let d1 := digitVal (buf.getD s 0)
      let d2 := digitVal (buf.getD (s + 1) 0)
      if s + 1 < buf.size && d1 < 16 && d2 < 16 then
        decodeBytesEscape buf f (s + 2) ((d1 <<< 4 + d2) :: acc) inv
      else
        .error { cls := "ValueError", msg := s!"invalid \\x escape at position {s - 2}" }
    else
      let inv' := if inv.isNone then some (s - 1) else inv
      decodeBytesEscape buf f s (c :: 92 :: acc) inv'

/-- `_PyPegen_decode_string`, `Parser/string_parser.c:242-248`. -/
def decodeString (raw : Bool) (s : List Nat) (t : Option Token) : PM (Option (List Nat)) :=
  if raw then return some (utf8Decode s) else decodeUnicodeWithEscapes s t

/-- Result of `_PyPegen_parse_string`. -/
inductive StrVal where
  | str (cps : List Nat)
  | bytes (bs : List Nat)
  | fail

/-- The prefix letters of a string token: `b`, `u`, `r` in either case. -/
def stringPfx : Nat → List Nat → Bool → Bool → List Nat × Bool × Bool
  | 0, s, b, r => (s, b, r)
  | f + 1, s, b, r =>
    if b && r then (s, b, r) else
    match s with
    | 98 :: x | 66 :: x => stringPfx f x true r
    | 117 :: x | 85 :: x => stringPfx f x b r
    | 114 :: x | 82 :: x => stringPfx f x b true
    | _ => (s, b, r)

/-- The checks and quote stripping of `_PyPegen_parse_string`: the text between the quotes, the
text to the end of the token (the C string `s` walks), `bytesmode` and `rawmode`. -/
def stringParts (tok : List Nat) : List Nat × List Nat × Bool × Bool :=
  let (s, bytesmode, rawmode) := stringPfx 4 tok false false
  let quote := s.headD 0
  let body := s.drop 1
  let len := body.length - 1
  let (body, len) :=
    if len ≥ 4 && body.getD 0 0 == quote && body.getD 1 0 == quote then
      (body.drop 2, len - 4)
    else (body, len)
  -- `strchr(s, '\\')` scans to the end of the token, quotes included.
  (body.take len, body, bytesmode, rawmode || !body.contains 92)

/-- `_PyPegen_parse_string`, `Parser/string_parser.c:245-338`. -/
def parseString (t : Token) : PM StrVal := do
  let (content, body, bytesmode, rawmode) := stringParts t.bytes
  if bytesmode then
    -- `for (ch = s; *ch; ch++)` also scans the closing quotes
    if body.any (· ≥ 0x80) then
      raiseErrorKnownLocation "SyntaxError" t.lineno t.colOffset t.endLineno t.endColOffset
        "bytes can only contain ASCII literal characters"
      return .fail
    if rawmode then return .bytes content
    let buf := content.toArray
    match decodeBytesEscape buf (buf.size + 1) 0 [] none with
    | .error e =>
      setErr e
      return .fail
    | .ok (v, inv) =>
      match inv with
      | some ptr => warnInvalidEscapeSeq buf ptr t
      | none => pure ()
      return .bytes v
  match ← decodeString rawmode content (some t) with
  | some v => return .str v
  | none => return .fail

end PyLean.PyGrammar.Peg
