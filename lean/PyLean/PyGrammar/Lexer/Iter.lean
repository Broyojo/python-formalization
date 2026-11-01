import PyLean.PyGrammar.Lexer.Get

/-!
`Python/Python-tokenize.c`, the `_tokenize.TokenizerIter` iterator, over the readline
tokenizer of `Parser/tokenizer/readline_tokenizer.c`. Lines of a `str` source go through
`PyUnicode_AsUTF8AndSize`, so the model reads UTF-8 bytes. `readline` here is
`io.StringIO(text).readline`, which splits at `\n` only.
-/

namespace PyLean.PyGrammar.Lexer

/-- `_PyTokenizer_FromReadline(readline, NULL, 1, 1)` over the whole text, with the fake
newline of `tok_underflow_readline` (`Parser/tokenizer/readline_tokenizer.c:71-106`) added
in advance and its position remembered. -/
def fromReadline (text : List Nat) (extraTokens : Bool) : TokState :=
  let bytes := utf8Encode text
  let needsNl := match bytes.getLast? with
    | some c => c != 10
    | none => false
  let src := if needsNl then bytes ++ [10] else bytes
  { src := src.toArray, readline := true, extraTokens,
    fakeNewlineAt := if needsNl then some bytes.length else none }

/-- `tokenizeriterobject`, `Python/Python-tokenize.c:32-42`. -/
structure IterState where
  tok : TokState
  done : Bool := false
  lastLine : List Nat := []
  /-- `last_line != NULL` -/
  hasLine : Bool := false
  lastLineno : Int := 0
  lastEndLineno : Int := 0
  byteColOffsetDiff : Int := 0
  deriving Repr, Inhabited

/-- One tuple of `TokenizerIter`: type, string, start, end, line. -/
structure TokInfo where
  type : Nat
  str : List Nat
  lineno : Int
  col : Int
  endLineno : Int
  endCol : Int
  line : List Nat
  deriving Repr, Inhabited, DecidableEq

/-- What `tokenizeriter_next` does. -/
inductive IterOut where
  | tok (t : TokInfo)
  | stop
  | raise (e : PyError)
  deriving Repr, Inhabited

/-- `_tokenizer_error`, `Python/Python-tokenize.c:88-181`. -/
def tokenizerErrorIter (s : TokState) : PyError :=
  let located (cls msg : String) : PyError :=
    let size := s.inp - s.buf
    let line := utf8Decode (s.slice s.buf (s.buf + (size - 1)))
    let bytes := utf8Encode line
    let offset := ((utf8Decode ((bytes ++ [0]).take size)).length : Int)
    { cls, msg, lineno := some s.lineno, offset := some offset, text := some line }
  if s.done == E_TOKEN then located "SyntaxError" "invalid token"
  else if s.done == E_EOF then
    { cls := "SyntaxError", msg := "unexpected EOF in multi-line statement",
      lineno := some s.lineno, offset := some ((s.inp : Int) - s.buf) }
  else if s.done == E_DEDENT then
    located "IndentationError" "unindent does not match any outer indentation level"
  else if s.done == E_INTR then { cls := "KeyboardInterrupt", msg := "" }
  else if s.done == E_NOMEM then { cls := "MemoryError", msg := "" }
  else if s.done == E_TABSPACE then
    located "TabError" "inconsistent use of tabs and spaces in indentation"
  else if s.done == E_TOODEEP then located "IndentationError" "too many levels of indentation"
  else if s.done == E_LINECONT then
    located "SyntaxError" "unexpected character after line continuation character"
  else located "SyntaxError" "unknown tokenization error"

/-- `_PyPegen_byte_offset_to_character_offset_line`, `Parser/pegen.c:27-49`. -/
def charCountLine (data : Array Nat) : Nat → Int → Int → Int
  | 0, _, _ => 0
  | f + 1, col, stop =>
    if col ≥ stop then 0 else
    let ch := data.getD col.toNat 0
    let step : Int :=
      if ch < 0x80 then 1 else if ch &&& 0xe0 == 0xc0 then 2
      else if ch &&& 0xf0 == 0xe0 then 3 else 4
    1 + charCountLine data f (col + step) stop

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

/-- `tokenizeriter_next`, `Python/Python-tokenize.c:242-349`. -/
def iterNext (it : IterState) : IterState × IterOut :=
  let (s, type, t) := tokenizerGet it.tok
  let it := { it with tok := s }
  if type == TokKind.ERRORTOKEN.num then
    (it, .raise (s.err.getD (tokenizerErrorIter s)))
  else if it.done then (it, .stop)
  else
    let raw : List Nat :=
      match t.start, t.end_ with
      | some a, some b => s.slice a b
      | _, _ => []
    -- `PyUnicode_FromStringAndSize(token.start, token.end - token.start)` is strict
    match firstBadUtf8 (raw.length + 1) raw 0 with
    | some (i, b, why) =>
      let hex := String.ofList (Nat.toDigits 16 b)
      (it, .raise { cls := "UnicodeDecodeError",
                    msg := s!"'utf-8' codec can't decode byte 0x{hex} in position {i}: {why}" })
    | none =>
    let str : List Nat := utf8Decode raw
    let isTrailing := type == TokKind.ENDMARKER.num
      || (type == TokKind.DEDENT.num && s.done == E_EOF)
    let lineStart := if isStringLit type then s.multiLineStart else s.lineStart
    let (it, line, lineChanged) : IterState × List Nat × Bool :=
      if s.extraTokens && isTrailing then (it, [], true)
      else
        let size : Int := (s.inp : Int) - lineStart
        let size := if size ≥ 1 && s.implicitNewline then size - 1 else size
        -- `_get_current_line`
        if s.lineno != it.lastLineno then
          let line := utf8Decode (s.slice lineStart (lineStart + size.toNat))
          ({ it with lastLine := line, hasLine := true, byteColOffsetDiff := 0 }, line, true)
        else (it, it.lastLine, false)
    -- `line == NULL`: `goto exit` with no exception, which ends the iteration.
    if !(s.extraTokens && isTrailing) && !it.hasLine then
      ({ it with done := it.done || type == TokKind.ENDMARKER.num }, .stop)
    else
    let lineno := if isStringLit type then s.firstLineno else s.lineno
    let endLineno := s.lineno
    -- `_get_col_offsets`
    let data := (utf8Encode line).toArray
    let fuel := data.size + 2
    let (it, col, byteOffset) : IterState × Int × Int :=
      match t.start with
      | some a =>
        if a ≥ lineStart then
          let bo : Int := (a : Int) - lineStart
          if lineChanged then
            let c := charCountLine data fuel 0 bo
            ({ it with byteColOffsetDiff := bo - c }, c, bo)
          else (it, bo - it.byteColOffsetDiff, bo)
        else (it, -1, -1)
      | none => (it, -1, -1)
    let (it, endCol) : IterState × Int :=
      match t.end_ with
      | some b =>
        if b ≥ s.lineStart then
          let ebo : Int := (b : Int) - s.lineStart
          if lineno == endLineno then
            let n := charCountLine data fuel byteOffset ebo
            ({ it with byteColOffsetDiff := it.byteColOffsetDiff
                  + ((b : Int) - (t.start.getD 0 : Int) - n) }, col + n)
          else
            let e := ((utf8Decode ((s.slice s.lineStart s.src.size).take ebo.toNat)).length : Int)
            ({ it with byteColOffsetDiff := it.byteColOffsetDiff + (ebo - e) }, e)
        else (it, -1)
      | none => (it, -1)
    let it := { it with lastLineno := lineno, lastEndLineno := endLineno }
    let (lineno, endLineno, col, endCol, type, str) :=
      if s.extraTokens then
        let (lineno, endLineno, col, endCol) :=
          if isTrailing then (lineno + 1, lineno + 1, (0 : Int), (0 : Int))
          else (lineno, endLineno, col, endCol)
        -- adjustments to match the original Python tokenize implementation
        if type > TokKind.DEDENT.num && type < TokKind.OP.num then
          (lineno, endLineno, col, endCol, TokKind.OP.num, str)
        else if type == TokKind.NEWLINE.num then
          let str' :=
            if !s.implicitNewline then
              if s.at (s.start.getD 0) == 13 then [13, 10] else [10]
            else str
          (lineno, endLineno, col, endCol + 1, type, str')
        else if type == TokKind.NL.num && s.implicitNewline then
          (lineno, endLineno, col, endCol, type, [])
        else (lineno, endLineno, col, endCol, type, str)
      else (lineno, endLineno, col, endCol, type, str)
    let it := if type == TokKind.ENDMARKER.num then { it with done := true } else it
    (it, .tok ⟨type, str, lineno, col, endLineno, endCol, line⟩)

/-- Run the iterator to the end: the tokens, and the exception that stopped it, if any. -/
def iterAll : Nat → IterState → List TokInfo → List TokInfo × Option PyError
  | 0, _, acc => (acc.reverse, some { cls := "<model fuel exhausted>", msg := "" })
  | f + 1, it, acc =>
    match iterNext it with
    | (_, .stop) => (acc.reverse, none)
    | (_, .raise e) => (acc.reverse, some e)
    | (it, .tok t) => iterAll f it (t :: acc)

/-- `list(_tokenize.TokenizerIter(io.StringIO(text).readline, extra_tokens=extra))`. -/
def tokenizeText (text : List Nat) (extra : Bool) : List TokInfo × Option PyError :=
  iterAll (text.length * 2 + 64) { tok := fromReadline text extra } []

end PyLean.PyGrammar.Lexer
