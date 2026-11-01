import PyLean.PyGrammar.Ast
import PyLean.PyGrammar.UniTables

/-!
Tokenizer state, the operations on it, and the helpers of
`Parser/tokenizer/helpers.c` and `Parser/lexer/state.c`.

The input is one array of bytes. `Parser/tokenizer/string_tokenizer.c` and
`utf8_tokenizer.c` walk a fully translated C string through it. For
`readline_tokenizer.c` the array is the concatenation of the lines, and `inp`
marks how much has been "read"; C's `tok->cur = tok->inp = tok->buf` overwrite is
`buf := cur` here, since the two agree on every offset relative to `buf`.
-/

namespace PyLean.PyGrammar.Lexer

open Lean

/-- A byte or code-point literal: `ch! 'a'` elaborates to the number 97. -/
macro "ch! " c:char : term => do
  return Lean.Syntax.mkNumLit (toString c.getChar.toNat)

/-! `Include/errcode.h:22-40` -/
def E_OK : Nat := 10
def E_EOF : Nat := 11
def E_INTR : Nat := 12
def E_TOKEN : Nat := 13
def E_NOMEM : Nat := 15
def E_ERROR : Nat := 17
def E_TABSPACE : Nat := 18
def E_TOODEEP : Nat := 20
def E_DEDENT : Nat := 21
def E_DECODE : Nat := 22
def E_EOFS : Nat := 23
def E_EOLS : Nat := 24
def E_LINECONT : Nat := 25
def E_INTERACT_STOP : Nat := 28
def E_COLUMNOVERFLOW : Nat := 29

/-- `Parser/lexer/state.h:6-8,46` -/
def MAXINDENT : Nat := 100
def MAXLEVEL : Nat := 200
def MAXFSTRINGLEVEL : Nat := 150
def MAX_EXPR_NESTING : Int := 3

/-- An exception as `_syntaxerror_range` (`Parser/tokenizer/helpers.c:27-85`) builds it,
or as the parser does later. `text` is the source line in code points. -/
structure PyError where
  cls : String
  msg : String
  lineno : Option Int := none
  offset : Option Int := none
  endLineno : Option Int := none
  endOffset : Option Int := none
  text : Option (List Nat) := none
  deriving Repr, Inhabited, BEq

/-- `tokenizer_mode`, `Parser/lexer/state.h:48-72`. -/
structure Mode where
  /-- `kind == TOK_FSTRING_MODE` -/
  fstringMode : Bool := false
  curlyDepth : Int := 0
  curlyExprStart : Int := 0
  quote : Nat := 0
  quoteSize : Nat := 0
  raw : Bool := false
  start : Nat := 0
  multiLineStart : Nat := 0
  firstLine : Int := 0
  /-- `last_expr_buffer`, as the source offset it was copied from. -/
  lastExprBuf : Option Nat := none
  lastExprSize : Int := 0
  lastExprEnd : Int := 0
  inDebug : Bool := false
  inFormatSpec : Bool := false
  /-- `string_kind == TSTRING` -/
  tstring : Bool := false
  deriving Repr, Inhabited

/-- `struct tok_state`, `Parser/lexer/state.h:75-140`, the fields with behaviour.
`tok_mode_stack` is `modes`, innermost first. -/
structure TokState where
  src : Array Nat := #[]
  buf : Nat := 0
  cur : Nat := 0
  inp : Nat := 0
  /-- `tok->start`; `none` is `NULL`. -/
  start : Option Nat := none
  done : Nat := E_OK
  tabsize : Nat := 8
  indent : Nat := 0
  /-- `indstack[0..indent]`, top first. -/
  indstack : List Nat := [0]
  altindstack : List Nat := [0]
  atbol : Bool := true
  pendin : Int := 0
  /-- `tok->prompt != NULL`: interactive prompting. Always false on strings. -/
  prompt : Bool := false
  lineno : Int := 0
  firstLineno : Int := 0
  startingColOffset : Int := -1
  colOffset : Int := -1
  level : Nat := 0
  /-- `parenstack[level-1], …`: `(char, lineno, col)`, top first. -/
  parenstack : List (Nat × Int × Int) := []
  contLine : Bool := false
  lineStart : Nat := 0
  multiLineStart : Nat := 0
  decodingErred : Bool := false
  /-- `tok->encoding`. -/
  encoding : Option String := none
  typeComments : Bool := false
  reportWarnings : Bool := true
  modes : List Mode := [{}]
  /-- `tok_mode_stack_index` -/
  modeIndex : Nat := 0
  extraTokens : Bool := false
  commentNewline : Bool := false
  implicitNewline : Bool := false
  /-- Readline mode: `tok->underflow == tok_underflow_readline`. -/
  readline : Bool := false
  /-- Offset in `src` where a fake newline was added to the last line, if any. -/
  fakeNewlineAt : Option Nat := none
  /-- The Python exception currently set (`PyErr_Occurred()`). -/
  err : Option PyError := none
  /-- Warnings emitted so far, newest first: `(category, message, lineno)`. -/
  warnings : List (String × String × Int) := []
  /-- `token->metadata` of the token being built. -/
  metadata : Option (List Nat) := none
  deriving Repr, Inhabited

/-- What `tok_get` returns: `MAKE_TOKEN` with its `p_start`, `p_end`, or
`MAKE_TYPE_COMMENT_TOKEN` with explicit columns. -/
structure Ret where
  type : Nat
  pStart : Option Nat := none
  pEnd : Option Nat := none
  typeCols : Option (Int × Int) := none
  /-- Model only: a fuel bound ran out. Never a Python outcome. -/
  fuelOut : Bool := false
  deriving Repr, Inhabited

/-- The tokenizer monad. `throw` is `return MAKE_TOKEN(...)`: the state survives. -/
abbrev M (α : Type) := EStateM Ret TokState α

/-- `Py_ISDIGIT` -/
@[inline] def isDigit (c : Int) : Bool := 48 ≤ c && c ≤ 57
/-- `Py_ISXDIGIT` -/
@[inline] def isXDigit (c : Int) : Bool :=
  isDigit c || (97 ≤ c && c ≤ 102) || (65 ≤ c && c ≤ 70)
/-- `Py_ISALNUM` -/
@[inline] def isAlnum (c : Int) : Bool :=
  isDigit c || (97 ≤ c && c ≤ 122) || (65 ≤ c && c ≤ 90)
/-- `Py_TOLOWER` -/
@[inline] def toLower (c : Nat) : Nat := if 65 ≤ c ∧ c ≤ 90 then c + 32 else c

/-- `is_potential_identifier_start`, `Parser/lexer/lexer.c:12-16`. -/
@[inline] def isIdStart (c : Int) : Bool :=
  (97 ≤ c && c ≤ 122) || (65 ≤ c && c ≤ 90) || c == 95 || 128 ≤ c
/-- `is_potential_identifier_char`, `Parser/lexer/lexer.c:18-23`. -/
@[inline] def isIdChar (c : Int) : Bool :=
  (97 ≤ c && c ≤ 122) || (65 ≤ c && c ≤ 90) || isDigit c || c == 95 || 128 ≤ c

/-- Membership in a flat range table. -/
def inRanges (c : Nat) : List Nat → Bool
  | lo :: hi :: rest => if c < lo then false else c ≤ hi || inRanges c rest
  | _ => false

/-- `_PyUnicode_IsXidStart`, with `_` as `_PyUnicode_ScanIdentifier` allows it. -/
def isXidStart (c : Nat) : Bool :=
  if c < 128 then (97 ≤ c && c ≤ 122) || (65 ≤ c && c ≤ 90) || c == 95
  else inRanges c xidStartRanges

/-- `_PyUnicode_IsXidContinue`. -/
def isXidContinue (c : Nat) : Bool :=
  if c < 128 then isIdChar (c : Int) else inRanges c xidContinueRanges

/-- `Py_UNICODE_ISPRINTABLE`. -/
def isPrintable (c : Nat) : Bool :=
  if c < 128 then 32 ≤ c && c < 127 else inRanges c printableRanges

/-- `src[i]`, with a NUL terminator past the end as a C string has. -/
@[inline] def TokState.at (s : TokState) (i : Nat) : Nat := s.src.getD i 0

/-- Bytes `src[a..b)`. -/
def TokState.slice (s : TokState) (a b : Nat) : List Nat :=
  (s.src.extract a b).toList

/-- `strlen` from `p`: the buffer ends at `inp` in readline mode, where it is
NUL-terminated there, and at the end of the string otherwise. -/
def TokState.strlen (s : TokState) (p : Nat) : Int :=
  (if s.readline then (s.inp : Int) else (s.src.size : Int)) - (p : Int)

/-- `INSIDE_FSTRING` -/
@[inline] def TokState.insideFString (s : TokState) : Bool := s.modeIndex > 0

/-- `TOK_GET_MODE` -/
@[inline] def TokState.mode (s : TokState) : Mode := s.modes.headD {}

/-- Update `TOK_GET_MODE`. -/
@[inline] def TokState.setMode (s : TokState) (f : Mode → Mode) : TokState :=
  { s with modes := match s.modes with
      | m :: ms => f m :: ms
      | [] => [] }

/-- `INSIDE_FSTRING_EXPR` -/
@[inline] def Mode.insideExpr (m : Mode) : Bool := m.curlyExprStart ≥ 0

/-- `INSIDE_FSTRING_EXPR_AT_TOP` -/
@[inline] def Mode.insideExprAtTop (m : Mode) : Bool := m.curlyDepth - m.curlyExprStart == 1

/-- `TOK_GET_STRING_PREFIX` as a one-character string. -/
def Mode.prefixStr (m : Mode) : String := if m.tstring then "t" else "f"

/-- Decode UTF-8 into code points, replacing errors with U+FFFD the way
`PyUnicode_DecodeUTF8(..., "replace")` does (one replacement per maximal subpart). -/
def decodeReplace (fuel : Nat) (bs : List Nat) : List Nat :=
  match fuel, bs with
  | 0, _ | _, [] => []
  | fuel + 1, b :: rest =>
    if b < 0x80 then b :: decodeReplace fuel rest
    else
      let isC (x : Nat) := 0x80 ≤ x && x < 0xC0
      if 0xC2 ≤ b && b < 0xE0 then
        match rest with
        | c :: r => if isC c then (((b &&& 0x1F) <<< 6) ||| (c &&& 0x3F)) :: decodeReplace fuel r
                    else 0xFFFD :: decodeReplace fuel rest
        | [] => [0xFFFD]
      else if 0xE0 ≤ b && b < 0xF0 then
        let lo := if b == 0xE0 then 0xA0 else 0x80
        let hi := if b == 0xED then 0x9F else 0xBF
        match rest with
        | c :: r =>
          if lo ≤ c && c ≤ hi then
            match r with
            | d :: r' =>
              if isC d then
                (((b &&& 0x0F) <<< 12) ||| ((c &&& 0x3F) <<< 6) ||| (d &&& 0x3F))
                  :: decodeReplace fuel r'
              else 0xFFFD :: decodeReplace fuel r
            | [] => [0xFFFD]
          else 0xFFFD :: decodeReplace fuel rest
        | [] => [0xFFFD]
      else if 0xF0 ≤ b && b < 0xF5 then
        let lo := if b == 0xF0 then 0x90 else 0x80
        let hi := if b == 0xF4 then 0x8F else 0xBF
        match rest with
        | c :: r =>
          if lo ≤ c && c ≤ hi then
            match r with
            | d :: r' =>
              if isC d then
                match r' with
                | e :: r'' =>
                  if isC e then
                    (((b &&& 0x07) <<< 18) ||| ((c &&& 0x3F) <<< 12) ||| ((d &&& 0x3F) <<< 6)
                      ||| (e &&& 0x3F)) :: decodeReplace fuel r''
                  else 0xFFFD :: decodeReplace fuel r'
                | [] => [0xFFFD]
              else 0xFFFD :: decodeReplace fuel r
            | [] => [0xFFFD]
          else 0xFFFD :: decodeReplace fuel rest
        | [] => [0xFFFD]
      else 0xFFFD :: decodeReplace fuel rest

/-- `PyUnicode_DecodeUTF8(s, n, "replace")`. -/
def utf8Decode (bs : List Nat) : List Nat := decodeReplace (bs.length + 1) bs

/-- Encode one code point as UTF-8. -/
def utf8Enc (c : Nat) : List Nat :=
  if c < 0x80 then [c]
  else if c < 0x800 then [0xC0 ||| (c >>> 6), 0x80 ||| (c &&& 0x3F)]
  else if c < 0x10000 then
    [0xE0 ||| (c >>> 12), 0x80 ||| ((c >>> 6) &&& 0x3F), 0x80 ||| (c &&& 0x3F)]
  else
    [0xF0 ||| (c >>> 18), 0x80 ||| ((c >>> 12) &&& 0x3F), 0x80 ||| ((c >>> 6) &&& 0x3F),
     0x80 ||| (c &&& 0x3F)]

/-- UTF-8 encode a list of code points. -/
def utf8Encode (cs : List Nat) : List Nat := cs.flatMap utf8Enc

/-- The first ill-formed UTF-8 sequence of `s` at offset `i`, as `PyUnicode_FromStringAndSize`
reports it: offset, byte and reason. -/
def firstBadUtf8 : Nat → List Nat → Nat → Option (Nat × Nat × String)
  | 0, _, _ => none
  | _, [], _ => none
  | f + 1, b :: r, i =>
    let need : Option Nat :=
      if b < 0x80 then some 0
      else if 0xC2 ≤ b && b < 0xE0 then some 1
      else if 0xE0 ≤ b && b < 0xF0 then some 2
      else if 0xF0 ≤ b && b < 0xF5 then some 3
      else none
    match need with
    | none => some (i, b, "invalid start byte")
    | some n =>
      let cs := r.take n
      if !(cs.all fun c => 0x80 ≤ c && c < 0xC0) then
        some (i, b, "invalid continuation byte")
      else if cs.length < n then some (i, b, "unexpected end of data")
      else firstBadUtf8 f (r.drop n) (i + n + 1)

/-- `str(UnicodeDecodeError)` of `PyUnicode_DecodeUTF8(s, n, NULL)`. -/
def utf8Error (i b : Nat) (why : String) : PyError :=
  { cls := "UnicodeDecodeError",
    msg := s!"'utf-8' codec can't decode byte 0x{String.ofList (Nat.toDigits 16 b)} in position {i}: {why}" }

/-- `%04X`. -/
def hex4 (c : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 c |>.map Char.toUpper)
  String.ofList (List.replicate (4 - s.length) '0') ++ s

/-- `%c` of a code point. -/
def chStr (c : Nat) : String := String.singleton (Char.ofNat c)

/-- `_syntaxerror_range`, `Parser/tokenizer/helpers.c:27-85`. -/
def syntaxErrorRange (msg : String) (colOffset endColOffset : Int) (s : TokState) : TokState :=
  if s.done == E_ERROR then s else
  let errtext := utf8Decode (s.slice s.lineStart s.cur)
  let col := if colOffset == -1 then (errtext.length : Int) else colOffset
  let ecol := if endColOffset == -1 then col else endColOffset
  -- `strcspn(tok->line_start, "\n")`
  let rest := (s.src.extract s.lineStart s.src.size).toList
  let lineLen := (rest.takeWhile (· != 10)).length
  let errtext' :=
    if lineLen != s.cur - s.lineStart then utf8Decode (rest.take lineLen) else errtext
  { s with
    err := some { cls := "SyntaxError", msg, lineno := some s.lineno, offset := some col,
                  endLineno := some s.lineno, endOffset := some ecol, text := some errtext' }
    done := E_ERROR }

/-- `_PyTokenizer_syntaxerror`. -/
def syntaxerror (msg : String) : M Nat := do
  modify (syntaxErrorRange msg (-1) (-1))
  return TokKind.ERRORTOKEN.num

/-- `_PyTokenizer_syntaxerror_known_range`. -/
def syntaxerrorKnownRange (col ecol : Int) (msg : String) : M Nat := do
  modify (syntaxErrorRange msg col ecol)
  return TokKind.ERRORTOKEN.num

/-- `_PyTokenizer_indenterror`. -/
def indenterror : M Nat := do
  modify fun s => { s with done := E_TABSPACE, cur := s.inp }
  return TokKind.ERRORTOKEN.num

/-- `_PyTokenizer_parser_warn` with warnings not turned into errors. -/
def parserWarn (category msg : String) : M Unit :=
  modify fun s =>
    if s.reportWarnings then { s with warnings := (category, msg, s.lineno) :: s.warnings } else s

/-- `_PyTokenizer_warn_invalid_escape_sequence`. -/
def warnInvalidEscape (c : Nat) : M Unit :=
  parserWarn "SyntaxWarning"
    ("\"\\" ++ chStr c ++ "\" is an invalid escape sequence. Such sequences will not work in "
      ++ "the future. Did you mean \"\\\\" ++ chStr c ++ "\"? A raw string is also an option.")

/-- `_PyTokenizer_translate_newlines`, `Parser/tokenizer/helpers.c:284-328`. `s` stops
at the first NUL, as a C string does. -/
def translateNewlines (s : List Nat) (execInput preserveCrlf : Bool) : List Nat :=
  let rec go : List Nat → Bool → Nat → List Nat → List Nat × Nat
    | [], _, c, acc => (acc, c)
    | c0 :: rest, skip, c, acc =>
      -- `if (skip_next_lf) {...}`: a `\n` after `\r` is dropped.
      if skip && c0 == 10 then
        match rest with
        | [] => (acc, 0)
        | c1 :: rest' =>
          if !preserveCrlf && c1 == 13 then go rest' true 10 (10 :: acc)
          else go rest' false c1 (c1 :: acc)
      else if !preserveCrlf && c0 == 13 then go rest true 10 (10 :: acc)
      else go rest false c0 (c0 :: acc)
  let (acc, c) := go (s.takeWhile (· != 0)) false 0 []
  let acc := if execInput && c != 10 && c != 0 then 10 :: acc else acc
  acc.reverse

/-- `_PyLexer_token_setup`, `Parser/lexer/state.c:117-137` needs `ISSTRINGLIT`. -/
def isStringLit (t : Nat) : Bool :=
  t == TokKind.STRING.num || t == TokKind.FSTRING_MIDDLE.num || t == TokKind.TSTRING_MIDDLE.num

/-- `struct token`, `Parser/lexer/state.h:29-33`. -/
structure LexTok where
  level : Nat := 0
  lineno : Int := 0
  colOffset : Int := -1
  endLineno : Int := 0
  endColOffset : Int := -1
  start : Option Nat := none
  end_ : Option Nat := none
  metadata : Option (List Nat) := none
  deriving Repr, Inhabited

/-- `_PyLexer_token_setup`, and `_PyLexer_type_comment_token_setup` for `typeCols`. -/
def tokenSetup (s : TokState) (r : Ret) : LexTok :=
  match r.typeCols with
  | some (c, e) =>
    { level := s.level, lineno := s.lineno, endLineno := s.lineno, colOffset := c,
      endColOffset := e, start := r.pStart, end_ := r.pEnd, metadata := s.metadata }
  | none =>
    let lineno := if isStringLit r.type then s.firstLineno else s.lineno
    match r.pStart, r.pEnd with
    | some a, some b =>
      { level := s.level, lineno, endLineno := s.lineno, colOffset := s.startingColOffset,
        endColOffset := s.colOffset, start := some a, end_ := some b, metadata := s.metadata }
    | _, _ =>
      { level := s.level, lineno, endLineno := s.lineno, colOffset := -1, endColOffset := -1,
        start := r.pStart, end_ := r.pEnd, metadata := s.metadata }

/-! ### Tokens: `Parser/token.c`, which `Tools/build/generate_token.py` derives from
`Grammar/Tokens`; here the same derivation runs over the generated table. -/

/-- All kinds with an exact spelling, as code lists. -/
def exactTable : List (List Nat × TokKind) :=
  ([60, 62], TokKind.NOTEQUAL) ::  -- `<>`, added by `generate_token.py`
    TokKind.all.filterMap fun k => (k.exact?).map fun e => (e.toList.map Char.toNat, k)

/-- Look a spelling up, `OP` if absent. -/
def exactLookup (cs : List Nat) : Nat :=
  match exactTable.find? (fun p => p.1 == cs) with
  | some (_, k) => k.num
  | none => TokKind.OP.num

/-- `_PyToken_OneChar` -/
def oneChar (c : Int) : Nat := exactLookup [c.toNat]
/-- `_PyToken_TwoChars`; `EOF` matches nothing. -/
def twoChars (a b : Int) : Nat :=
  if b < 0 then TokKind.OP.num else exactLookup [a.toNat, b.toNat]
/-- `_PyToken_ThreeChars` -/
def threeChars (a b c : Int) : Nat :=
  if c < 0 then TokKind.OP.num else exactLookup [a.toNat, b.toNat, c.toNat]

end PyLean.PyGrammar.Lexer
