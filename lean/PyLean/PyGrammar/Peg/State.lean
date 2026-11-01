import PyLean.PyGrammar.Lexer.Get
import PyLean.PyGrammar.Peg.GrammarData
import PyLean.PyGrammar.Peg.Numbers

/-!
The parser state and the token, memo and error machinery of `Parser/pegen.c` and
`Parser/pegen_errors.c`.
-/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- `Py_file_input` and friends, in the order `_PyPegen_parse` tests them. -/
inductive StartRule where
  | file | single | eval | funcType
  deriving DecidableEq, Repr, Inhabited

/-- What the model takes from outside the parser, as explicit data: the Unicode
name database used by `\N{...}` and NFKC normalization of identifiers, which are
tables of `Modules/unicodedata*`, not parser behaviour. Identifiers absent from
`nfkc` are already normalized. -/
structure Cfg where
  ucn : List (List Nat × Nat) := []
  nfkc : List (List Nat × List Nat) := []
  deriving Repr, Inhabited

/-- `Parser` in `Parser/pegen.h`. Memos are by token index; `PyErr_Occurred()` is
`tok.err`, shared with the tokenizer. -/
structure PS where
  tok : TokState
  tokens : Array Token := #[]
  memo : Array (List (Nat × Ast × Nat)) := #[]
  mark : Nat := 0
  startRule : StartRule := .file
  parsingStarted : Bool := false
  errorIndicator : Bool := false
  flagBarry : Bool := false
  flagDontImplyDedent : Bool := false
  flagIncomplete : Bool := false
  featureVersion : Nat := 14
  /-- `type_ignore_comments`: `(lineno, tag)`, oldest first. -/
  typeIgnores : List (Int × List Nat) := []
  knownErrToken : Option Token := none
  level : Nat := 0
  callInvalidRules : Bool := false
  /-- `last_stmt_location`: lineno and col_offset. -/
  lastStmt : Int × Int := (0, 0)
  cfg : Cfg := {}
  deriving Repr, Inhabited

/-- `MAXSTACK` -/
def MAXSTACK : Nat := 6000

/-- Parser actions run here. -/
abbrev PM (α : Type) := StateM PS α

/-- `p->fill` -/
@[inline] def PS.fill (p : PS) : Nat := p.tokens.size

/-- `PyErr_Occurred()` -/
@[inline] def PS.errOccurred (p : PS) : Bool := p.tok.err.isSome

/-- `PyErr_SetString` -/
def setErr (e : PyError) : PM Unit :=
  modify fun p => { p with tok := { p.tok with err := some e } }

/-- `p->tokens[i]` -/
@[inline] def PS.tokenAt (p : PS) (i : Nat) : Token := p.tokens.getD i default

/-- The bytes of a `struct token`. -/
def tokBytes (s : TokState) (t : LexTok) : List Nat :=
  match t.start, t.end_ with
  | some a, some b => s.slice a b
  | _, _ => []

/-- `_PyPegen_byte_offset_to_character_offset_raw`, `Parser/pegen.c:53-65`, on the
UTF-8 bytes `str` of a line. -/
def byteToCharRaw (str : List Nat) (colOffset : Int) : Int :=
  let len := (str.length : Int)
  let c := if colOffset > len + 1 then len + 1 else colOffset
  ((utf8Decode ((str ++ [0]).take c.toNat)).length : Int)

/-- `get_error_line_from_tokenizer_buffers`, `Parser/pegen_errors.c:236-270`, for a
string source: walk `lineno - 1` newlines in `tok->str`, stopping at `tok->inp`. -/
def errorLineFromBuffers (p : PS) (lineno : Int) : List Nat :=
  let s := p.tok
  let bufEnd : Nat := s.inp
  let rec walk : Nat → Nat → Nat
    | 0, cur => cur
    | n + 1, cur =>
      -- `strchr(cur_line, '\n')`
      let rest := (s.src.extract cur s.src.size).toList
      match rest.findIdx? (· == 10) with
      | none => cur
      | some i =>
        if cur + i + 1 > bufEnd then cur else walk n (cur + i + 1)
  let start := walk (lineno - 1).toNat 0
  let rest := (s.src.extract start s.src.size).toList
  utf8Decode (rest.takeWhile (· != 10))

/-- `_PyPegen_raise_error_known_location`, `Parser/pegen_errors.c:272-356`. A
`CURRENT_POS` end position is `-5`. `filename` never names a real file here, so
`_PyErr_ProgramDecodedTextObject` yields nothing. -/
def raiseKnownLocation (cls : String) (lineno colOffset endLineno endColOffset : Int)
    (msg : String) : PM Unit := do
  let p ← get
  if p.errorIndicator && p.errOccurred then return
  set { p with errorIndicator := true }
  let s := p.tok
  let endLineno := if endLineno == -5 then s.lineno else endLineno
  let endColOffset := if endColOffset == -5 then (s.cur : Int) - s.lineStart else endColOffset
  let errorLine : List Nat :=
    if s.lineno ≤ lineno && s.inp > s.buf then utf8Decode (s.slice s.lineStart s.inp)
    else errorLineFromBuffers p lineno
  let bytes := utf8Encode errorLine
  let col := byteToCharRaw bytes colOffset
  let ecol := if endColOffset > 0 then byteToCharRaw bytes endColOffset else endColOffset
  setErr { cls, msg, lineno := some lineno, offset := some col, endLineno := some endLineno,
           endOffset := some ecol, text := some errorLine }

/-- `RAISE_ERROR_KNOWN_LOCATION`, `Parser/pegen.h:196-208`. -/
def raiseErrorKnownLocation (cls : String) (lineno col endLineno endCol : Int)
    (msg : String) : PM Unit :=
  raiseKnownLocation cls lineno (if col == -5 then -5 else col + 1) endLineno
    (if endCol == -5 then -5 else endCol + 1) msg

/-- `raise_unclosed_parentheses_error`, `Parser/pegen_errors.c:12-19`. -/
def raiseUnclosed : PM Unit := do
  let p ← get
  let (c, line, col) := p.tok.parenstack.headD (0, 0, 0)
  raiseErrorKnownLocation "SyntaxError" line col line (-1) s!"'{chStr c}' was never closed"

/-- `_Pypegen_stack_overflow`, `Parser/pegen_errors.c:408-413`. -/
def stackOverflow : PM Unit := do
  modify fun p => { p with errorIndicator := true }
  setErr { cls := "MemoryError",
           msg := "Parser stack overflowed - Python source too complex to parse" }

/-- `_get_keyword_or_name_type` -/
def keywordOrName (bytes : List Nat) : Nat :=
  match keywords.find? (fun k => k.1 == bytes) with
  | some (_, t) => t
  | none => TokKind.NAME.num

/-- `_PyPegen_raise_error` once the token `t` is chosen, `Parser/pegen_errors.c:190-220`. -/
def raiseAtToken (cls : String) (t : Token) (msg : String) : PM Unit := do
  let p ← get
  let s := p.tok
  let col : Int :=
    if t.colOffset == -1 then
      if s.cur == s.buf then 0 else (s.cur : Int) - s.lineStart
    else t.colOffset + 1
  let ecol : Int := if t.endColOffset != -1 then t.endColOffset + 1 else -1
  raiseKnownLocation cls t.lineno col t.endLineno ecol msg

/-- `_PyPegen_raise_error` with `use_mark == 0`, `Parser/pegen_errors.c:173-222`. -/
def raiseError0 (cls msg : String) : PM Unit := do
  let p ← get
  if p.errorIndicator && p.errOccurred then return
  if p.fill == 0 then
    raiseKnownLocation cls 0 0 0 (-1) msg
    return
  raiseAtToken cls ((p.knownErrToken).getD (p.tokenAt (p.fill - 1))) msg

/-- `_Pypegen_tokenizer_error`, `Parser/pegen_errors.c:21-80`. Always returns -1. -/
def tokenizerError : PM Int := do
  if (← get).errOccurred then return -1
  modify fun p => { p with errorIndicator := true }
  let s := (← get).tok
  let known (cls msg : String) (col : Int) : PM Int := do
    raiseErrorKnownLocation cls s.lineno (if col ≥ 0 then col else 0) s.lineno (-1) msg
    return -1
  if s.done == E_TOKEN then known "SyntaxError" "invalid token" (-1)
  else if s.done == E_EOF then
    if s.level != 0 then raiseUnclosed else raiseError0 "SyntaxError" "unexpected EOF while parsing"
    return -1
  else if s.done == E_DEDENT then
    raiseError0 "IndentationError" "unindent does not match any outer indentation level"
    return -1
  else if s.done == E_INTR then
    setErr { cls := "KeyboardInterrupt", msg := "" }
    return -1
  else if s.done == E_NOMEM then
    setErr { cls := "MemoryError", msg := "" }
    return -1
  else if s.done == E_TABSPACE then
    known "TabError" "inconsistent use of tabs and spaces in indentation" (-1)
  else if s.done == E_TOODEEP then
    known "IndentationError" "too many levels of indentation" (-1)
  else if s.done == E_LINECONT then
    known "SyntaxError" "unexpected character after line continuation character"
      ((s.cur : Int) - s.buf - 1)
  else if s.done == E_COLUMNOVERFLOW then
    setErr { cls := "OverflowError",
             msg := "Parser column offset overflow - source line is too big" }
    return -1
  else known "SyntaxError" "unknown parsing error" (-1)

/-- `_Pypegen_raise_decode_error`, `Parser/pegen_errors.c:82-116`. -/
def raiseDecodeError : PM Int := do
  let p ← get
  match p.tok.err with
  | some e =>
    let errtype :=
      if e.cls == "UnicodeDecodeError" || e.cls == "UnicodeError" then some "unicode error"
      else if e.cls == "ValueError" then some "value error" else none
    match errtype with
    | some t =>
      set { p with tok := { p.tok with err := none } }
      raiseError0 "SyntaxError" s!"({t}) {e.msg}"
    | none => pure ()
  | none => pure ()
  return -1

/-- Read tokens, recording and skipping `# type: ignore` comments. -/
def getTokSkippingIgnores : Nat → TokState → List (Int × List Nat) →
    TokState × Nat × LexTok × List (Int × List Nat)
  | 0, s, ig => let (s, ty, t) := tokenizerGet s; (s, ty, t, ig)
  | f + 1, s, ig =>
    let (s, ty, t) := tokenizerGet s
    if ty == TokKind.TYPE_IGNORE.num then
      let len := (t.endColOffset - t.colOffset).toNat
      getTokSkippingIgnores f s (ig ++ [(s.lineno, ((tokBytes s t).take len))])
    else (s, ty, t, ig)

/-- `_PyPegen_fill_token` with `initialize_token`, `Parser/pegen.c:160-302`. -/
def fillToken : PM Int := do
  let p ← get
  let (s, ty, t, ig) := getTokSkippingIgnores (p.tok.src.size + 2) p.tok p.typeIgnores
  let p := { p with tok := s, typeIgnores := ig }
  -- At the end in single input mode insert a newline and reset the parsing
  let (p, ty) :=
    if p.startRule == .single && ty == TokKind.ENDMARKER.num && p.parsingStarted then
      let p := { p with parsingStarted := false }
      let p :=
        if p.tok.indent != 0 && !p.flagDontImplyDedent then
          { p with tok := { p.tok with pendin := -(p.tok.indent : Int), indent := 0 } }
        else p
      (p, TokKind.NEWLINE.num)
    else ({ p with parsingStarted := true }, ty)
  let bytes := tokBytes p.tok t
  let token : Token :=
    { type := if ty == TokKind.NAME.num then keywordOrName bytes else ty
      bytes, metadata := t.metadata, level := t.level, lineno := t.lineno,
      colOffset := t.colOffset, endLineno := t.endLineno, endColOffset := t.endColOffset }
  set { p with tokens := p.tokens.push token, memo := p.memo.push [] }
  if ty == TokKind.ERRORTOKEN.num && p.tok.done == E_DECODE then return ← raiseDecodeError
  if ty == TokKind.ERRORTOKEN.num then return ← tokenizerError
  return 0

/-- `_PyPegen_raise_error`, `Parser/pegen_errors.c:173-222`, any `use_mark`. -/
def raiseError (cls : String) (useMark : Bool) (msg : String) : PM Unit := do
  let p ← get
  if p.errorIndicator && p.errOccurred then return
  if p.fill == 0 then
    raiseKnownLocation cls 0 0 0 (-1) msg
    return
  if useMark && p.mark == p.fill then
    if (← fillToken) < 0 then
      modify fun p => { p with errorIndicator := true }
      return
  let p ← get
  let t := (p.knownErrToken).getD (p.tokenAt (if useMark then p.mark else p.fill - 1))
  raiseAtToken cls t msg

/-- The loop of `_PyPegen_tokenize_full_source_to_check_for_errors`. -/
def tokenizeRest (curLine : Int) : Nat → PM Unit
  | 0 => pure ()
  | f + 1 => do
    let p ← get
    let (s, ty, _) := tokenizerGet p.tok
    set { p with tok := s }
    if ty == TokKind.ERRORTOKEN.num then
      if s.err.isSome then return
      if s.level != 0 then
        let (_, line, _) := s.parenstack.headD (0, 0, 0)
        if curLine > line then raiseUnclosed
    else if ty == TokKind.ENDMARKER.num then return
    else tokenizeRest curLine f

/-- `_PyPegen_tokenize_full_source_to_check_for_errors`, `Parser/pegen_errors.c:118-171`. -/
def tokenizeFullSource : PM Unit := do
  let p ← get
  if p.tok.prompt then return
  let saved := p.tok.err
  set { p with tok := { p.tok with err := none } }
  let current := p.knownErrToken.getD (p.tokenAt (p.fill - 1))
  tokenizeRest current.lineno (p.tok.src.size + 2)
  let p ← get
  if !(p.tok.err.isSome && p.tok.modeIndex == 0) then
    set { p with tok := { p.tok with err := saved } }

/-- `PyErr_ExceptionMatches(PyExc_SyntaxError)`. -/
def isSyntaxErrorClass (c : String) : Bool :=
  c == "SyntaxError" || c == "IndentationError" || c == "TabError"

/-- `_Pypegen_set_syntax_error`, `Parser/pegen_errors.c:358-406`. -/
def setSyntaxError (lastToken : Token) : PM Unit := do
  let p ← get
  if p.errOccurred then
    let isTokOk := p.tok.done == 16 || p.tok.done == E_OK
    if isTokOk && ((p.tok.err.map (·.cls)).map isSyntaxErrorClass).getD false then
      tokenizeFullSource
    return
  if p.fill == 0 then raiseError0 "SyntaxError" "error at start before reading any input"
  if lastToken.type == TokKind.ERRORTOKEN.num && p.tok.done == E_EOF then
    if p.tok.level != 0 then raiseUnclosed
    else raiseError0 "SyntaxError" "unexpected EOF while parsing"
    return
  if lastToken.type == TokKind.INDENT.num || lastToken.type == TokKind.DEDENT.num then
    raiseError0 "IndentationError"
      (if lastToken.type == TokKind.INDENT.num then "unexpected indent" else "unexpected unindent")
    return
  raiseErrorKnownLocation "SyntaxError" lastToken.lineno lastToken.colOffset
    lastToken.endLineno lastToken.endColOffset "invalid syntax"
  tokenizeFullSource

/-- `_PyPegen_is_memoized`, `Parser/pegen.c:363-400`. `some r` when the C function
returns nonzero. -/
def isMemoized (ty : Nat) : PM (Option Ast) := do
  let p ← get
  if p.mark == p.fill then
    if (← fillToken) < 0 then
      modify fun p => { p with errorIndicator := true }
      return some .null
  let p ← get
  match (p.memo.getD p.mark []).find? (fun m => m.1 == ty) with
  | some (_, node, mark) =>
    set { p with mark := mark }
    return some node
  | none => return none

/-- `_PyPegen_insert_memo`, `Parser/pegen.c:74-90`. -/
def insertMemo (mark ty : Nat) (node : Ast) : PM Unit :=
  modify fun p =>
    { p with memo := p.memo.modify mark fun l => (ty, node, p.mark) :: l }

/-- `_PyPegen_update_memo`, `Parser/pegen.c:92-107`. -/
def updateMemo (mark ty : Nat) (node : Ast) : PM Unit :=
  modify fun p =>
    { p with memo := p.memo.modify mark fun l =>
        if l.any (fun m => m.1 == ty) then
          l.map fun m => if m.1 == ty then (ty, node, p.mark) else m
        else (ty, node, p.mark) :: l }

/-- `_PyPegen_expect_token`, `Parser/pegen.c:430-443`. -/
def expectToken (ty : Nat) : PM Ast := do
  let p ← get
  if p.mark == p.fill then
    if (← fillToken) < 0 then
      modify fun p => { p with errorIndicator := true }
      return .null
  let p ← get
  let t := p.tokenAt p.mark
  if t.type != ty then return .null
  set { p with mark := p.mark + 1 }
  return .tok t

/-- `_PyPegen_new_identifier`, `Parser/pegen.c:506-569`. -/
def newIdentifier (bytes : List Nat) : PM Ast := do
  let id := utf8Decode bytes
  let p ← get
  let id :=
    if id.all (· < 128) then id
    else match p.cfg.nfkc.find? (fun e => e.1 == id) with
      | some (_, n) => n
      | none => id
  let names : List (List Nat × String) :=
    [([78, 111, 110, 101], "None"), ([84, 114, 117, 101], "True"),
     ([70, 97, 108, 115, 101], "False")]
  match names.find? (fun e => e.1 == id) with
  | some (_, n) =>
    setErr { cls := "ValueError", msg := s!"identifier field can't represent '{n}' constant" }
    modify fun p => { p with errorIndicator := true }
    return .null
  | none => return .ident id

/-- A located node. -/
def tokLoc (t : Token) : Loc := ⟨t.lineno, t.colOffset, t.endLineno, t.endColOffset⟩

/-- `_PyPegen_name_from_token`, `Parser/pegen.c:571-589`. -/
def nameFromToken (t : Ast) : PM Ast := do
  match t with
  | .tok t =>
    match ← newIdentifier t.bytes with
    | .null =>
      modify fun p => { p with errorIndicator := true }
      return .null
    | id => return .node .Name [id, .node .Load [] none] (some (tokLoc t))
  | _ => return .null

/-- `_PyPegen_name_token`, `Parser/pegen.c:591-596`. -/
def nameToken : PM Ast := do nameFromToken (← expectToken TokKind.NAME.num)

/-- `_PyPegen_soft_keyword_token`, `Parser/pegen.c:604-619`. -/
def softKeywordToken : PM Ast := do
  match ← expectToken TokKind.NAME.num with
  | .tok t =>
    if softKeywords.contains t.bytes then nameFromToken (.tok t) else return .null
  | _ => return .null

/-- `_PyPegen_expect_soft_keyword`, `Parser/pegen.c:468-489`. -/
def expectSoftKeyword (kw : List Nat) : PM Ast := do
  let p ← get
  if p.mark == p.fill then
    if (← fillToken) < 0 then
      modify fun p => { p with errorIndicator := true }
      return .null
  let p ← get
  let t := p.tokenAt p.mark
  if t.type != TokKind.NAME.num then return .null
  if t.bytes != kw then return .null
  nameToken

/-- `_PyPegen_number_token`, `Parser/pegen.c:692-746`. -/
def numberToken : PM Ast := do
  match ← expectToken TokKind.NUMBER.num with
  | .tok t =>
    if (← get).featureVersion < 6 && t.bytes.contains 95 then
      modify fun p => { p with errorIndicator := true }
      raiseError0 "SyntaxError"
        "Underscores in numeric literals are only supported in Python 3.6 and greater"
      return .null
    match parseNumber t.bytes with
    | .ok c => return .node .Constant [.const c, .null] (some (tokLoc t))
    | .limit msg =>
      modify fun p => { p with errorIndicator := true }
      raiseErrorKnownLocation "SyntaxError" t.lineno (-1) t.endLineno (-1)
        (msg ++ " - Consider hexadecimal for huge integer literals "
          ++ "to avoid decimal conversion limits.")
      return .null
  | _ => return .null

/-- `_PyPegen_get_last_nonnwhitespace_token`, `Parser/pegen.c:491-503`. -/
def lastNonWhitespaceToken (p : PS) : Token :=
  let rec go : Nat → Token → Token
    | 0, tok => tok
    | m + 1, _ =>
      let t := p.tokenAt m
      if t.type != TokKind.ENDMARKER.num
          && (t.type < TokKind.NEWLINE.num || t.type > TokKind.DEDENT.num) then t
      else go m t
  go p.mark default

end PyLean.PyGrammar.Peg
