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
  featureVersion : Nat := 15
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

/-- `_PyPegen_byte_offset_to_character_offset_raw`, `Parser/pegen.c:52-66`, on the
UTF-8 bytes `str` of a line. -/
def byteToCharRaw (str : List Nat) (colOffset : Int) : Int :=
  let len := (str.length : Int)
  let c := if colOffset > len + 1 then len + 1 else colOffset
  ((utf8Decode ((str ++ [0]).take c.toNat)).length : Int)

/-- `get_error_line_from_tokenizer_buffers`, `Parser/pegen_errors.c:244-284`, for a
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

/-- `_PyPegen_raise_error_known_location`, `Parser/pegen_errors.c:287-381`. A
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

/-- `RAISE_ERROR_KNOWN_LOCATION`, `Parser/pegen.h:187-200`. -/
def raiseErrorKnownLocation (cls : String) (lineno col endLineno endCol : Int)
    (msg : String) : PM Unit :=
  raiseKnownLocation cls lineno (if col == -5 then -5 else col + 1) endLineno
    (if endCol == -5 then -5 else endCol + 1) msg

/-- `raise_unclosed_parentheses_error`, `Parser/pegen_errors.c:14-21`. -/
def raiseUnclosed : PM Unit := do
  let p ← get
  let (c, line, col) := p.tok.parenstack.headD (0, 0, 0)
  raiseErrorKnownLocation "SyntaxError" line col line (-1) s!"'{chStr c}' was never closed"

/-- `_Pypegen_stack_overflow`, `Parser/pegen_errors.c:427-432`. -/
def stackOverflow : PM Unit := do
  modify fun p => { p with errorIndicator := true }
  setErr { cls := "MemoryError",
           msg := "Parser stack overflowed - Python source too complex to parse" }

/-- `_get_keyword_or_name_type` -/
def keywordOrName (bytes : List Nat) : Nat :=
  match keywords.find? (fun k => k.1 == bytes) with
  | some (_, t) => t
  | none => TokKind.NAME.num

/-- `_PyPegen_raise_error` once the token `t` is chosen, `Parser/pegen_errors.c:207-237`. -/
def raiseAtToken (cls : String) (t : Token) (msg : String) : PM Unit := do
  let p ← get
  let s := p.tok
  let col : Int :=
    if t.colOffset == -1 then
      if s.cur == s.buf then 0 else (s.cur : Int) - s.lineStart
    else t.colOffset + 1
  let ecol : Int := if t.endColOffset != -1 then t.endColOffset + 1 else -1
  raiseKnownLocation cls t.lineno col t.endLineno ecol msg

/-- `_PyPegen_raise_error` with `use_mark == 0`, `Parser/pegen_errors.c:190-239`. -/
def raiseError0 (cls msg : String) : PM Unit := do
  let p ← get
  if p.errorIndicator && p.errOccurred then return
  if p.fill == 0 then
    raiseKnownLocation cls 0 0 0 (-1) msg
    return
  raiseAtToken cls ((p.knownErrToken).getD (p.tokenAt (p.fill - 1))) msg

/-- The `switch (p->tok->done)` of `_Pypegen_tokenizer_error`, `Parser/pegen_errors.c:34-80`. -/
def tokenizerErrorSwitch (s : TokState) : PM Unit :=
  let known (cls msg : String) (col : Int) : PM Unit :=
    raiseErrorKnownLocation cls s.lineno (if col ≥ 0 then col else 0) s.lineno (-1) msg
  if s.done == E_TOKEN then known "SyntaxError" "invalid token" (-1)
  else if s.done == E_EOF then
    if s.level != 0 then raiseUnclosed else raiseError0 "SyntaxError" "unexpected EOF while parsing"
  else if s.done == E_DEDENT then
    raiseError0 "IndentationError" "unindent does not match any outer indentation level"
  else if s.done == E_INTR then setErr { cls := "KeyboardInterrupt", msg := "" }
  else if s.done == E_NOMEM then setErr { cls := "MemoryError", msg := "" }
  else if s.done == E_TABSPACE then
    known "TabError" "inconsistent use of tabs and spaces in indentation" (-1)
  else if s.done == E_TOODEEP then known "IndentationError" "too many levels of indentation" (-1)
  else if s.done == E_LINECONT then
    known "SyntaxError" "unexpected character after line continuation character"
      ((s.cur : Int) - s.buf - 1)
  else if s.done == E_COLUMNOVERFLOW then
    setErr { cls := "OverflowError", msg := "Parser column offset overflow - source line is too big" }
  else known "SyntaxError" "unknown parsing error" (-1)

/-- `_Pypegen_tokenizer_error`, `Parser/pegen_errors.c:24-81`. Always returns -1. -/
def tokenizerError : PM Int := do
  if (← get).errOccurred then return -1
  modify fun p => { p with errorIndicator := true }
  tokenizerErrorSwitch (← get).tok
  return -1

/-- The prefix `_Pypegen_raise_decode_error` gives an exception class, if it rewrites it. -/
def decodeErrType (c : String) : Option String :=
  if c == "UnicodeDecodeError" || c == "UnicodeError" then some "unicode error"
  else if c == "ValueError" then some "value error"
  else none

/-- The body of `_Pypegen_raise_decode_error_known_location`, `Parser/pegen_errors.c:90-131`, on
the current exception. `loc` is the location of `a`, `none` when `a` is `NULL`. -/
def raiseDecodeBody (loc : Option Loc) : Option PyError → PM Unit
  | some e =>
    match decodeErrType e.cls with
    | some t => do
      modify fun p => { p with tok := { p.tok with err := none } }
      match loc with
      | some l =>
        raiseErrorKnownLocation "SyntaxError" l.lineno l.colOffset l.endLineno l.endColOffset
          s!"({t}) {e.msg}"
      | none => raiseError0 "SyntaxError" s!"({t}) {e.msg}"
    | none => pure ()
  | none => pure ()

/-- `_Pypegen_raise_decode_error`, `Parser/pegen_errors.c:84-87`: no location. -/
def raiseDecodeError : PM Int := do
  raiseDecodeBody none (← get).tok.err
  return -1

/-- `_Pypegen_raise_decode_error_known_location(p, a)` with `a` at `l`. -/
def raiseDecodeKnown (l : Loc) : PM Int := do
  raiseDecodeBody (some l) (← get).tok.err
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

/-- `_PyPegen_fill_token`, `Parser/pegen.c:245-293`, up to the end of `initialize_token`,
`Parser/pegen.c:182-220`: the state
with the new token and its memo slot, and the type the tokenizer returned. -/
def pushToken (p : PS) : PS × Nat :=
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
  ({ p with tokens := p.tokens.push token, memo := p.memo.push [] }, ty)

/-- `_PyPegen_fill_token`, `Parser/pegen.c:245-293`, with the tail of `initialize_token`. -/
def fillToken : PM Int := do
  let r := pushToken (← get)
  set r.1
  if r.2 == TokKind.ERRORTOKEN.num then
    if r.1.tok.done == E_DECODE then raiseDecodeError else tokenizerError
  else return 0

/-- `_PyPegen_raise_error`, `Parser/pegen_errors.c:198-241`, any `use_mark`. -/
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

/-- `_PyPegen_tokenize_full_source_to_check_for_errors`, `Parser/pegen_errors.c:134-193`. -/
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

/-- `_Pypegen_set_syntax_error` past its first checks, `Parser/pegen_errors.c:400-423`. `p` is
the state on entry. -/
def setSyntaxErrorTail (p : PS) (lastToken : Token) : PM Unit :=
  if lastToken.type == TokKind.ERRORTOKEN.num && p.tok.done == E_EOF then
    if p.tok.level != 0 then raiseUnclosed
    else raiseError0 "SyntaxError" "unexpected EOF while parsing"
  else if lastToken.type == TokKind.INDENT.num || lastToken.type == TokKind.DEDENT.num then
    raiseError0 "IndentationError"
      (if lastToken.type == TokKind.INDENT.num then "unexpected indent" else "unexpected unindent")
  else do
    raiseErrorKnownLocation "SyntaxError" lastToken.lineno lastToken.colOffset
      lastToken.endLineno lastToken.endColOffset "invalid syntax"
    tokenizeFullSource

/-- `_Pypegen_set_syntax_error`, `Parser/pegen_errors.c:384-424`. -/
def setSyntaxError (lastToken : Token) : PM Unit := do
  let p ← get
  if p.errOccurred then
    let isTokOk := p.tok.done == 16 || p.tok.done == E_OK
    if isTokOk && ((p.tok.err.map (·.cls)).map isSyntaxErrorClass).getD false then
      tokenizeFullSource
    return
  if p.fill == 0 then raiseError0 "SyntaxError" "error at start before reading any input"
  setSyntaxErrorTail p lastToken

/-- `if (p->mark == p->fill) { if (_PyPegen_fill_token(p) < 0) { p->error_indicator = 1; return
NULL; } }`, the head of every token-reading function. `false` is the error return. -/
def ensureToken : PM Bool := fun p =>
  if p.mark == p.fill then
    let r := fillToken p
    if r.1 < 0 then (false, { r.2 with errorIndicator := true }) else (true, r.2)
  else (true, p)

/-- The lookup of `_PyPegen_is_memoized`, `Parser/pegen.c:351-372`. -/
def memoLookup (ty : Nat) : PM (Option Ast) := fun p =>
  match (p.memo.getD p.mark []).find? (fun m => m.1 == ty) with
  | some (_, node, mark) => (some node, { p with mark := mark })
  | none => (none, p)

/-- `_PyPegen_is_memoized`, `Parser/pegen.c:342-373`. `some r` when the C function
returns nonzero. -/
def isMemoized (ty : Nat) : PM (Option Ast) := fun p =>
  let e := ensureToken p
  if e.1 then memoLookup ty e.2 else (some .null, e.2)

/-- `_PyPegen_insert_memo`, `Parser/pegen.c:81-94`. -/
def insertMemo (mark ty : Nat) (node : Ast) : PM Unit :=
  modify fun p =>
    { p with memo := p.memo.modify mark fun l => (ty, node, p.mark) :: l }

/-- `_PyPegen_update_memo`, `Parser/pegen.c:98-110`. -/
def updateMemo (mark ty : Nat) (node : Ast) : PM Unit :=
  modify fun p =>
    { p with memo := p.memo.modify mark fun l =>
        if l.any (fun m => m.1 == ty) then
          l.map fun m => if m.1 == ty then (ty, node, p.mark) else m
        else (ty, node, p.mark) :: l }

/-- The tail of `_PyPegen_expect_token`, with the token read. -/
def takeToken (ty : Nat) : PM Ast := fun p =>
  let t := p.tokenAt p.mark
  if t.type != ty then (.null, p) else (.tok t, { p with mark := p.mark + 1 })

/-- `_PyPegen_expect_token`, `Parser/pegen.c:405-419`. -/
def expectToken (ty : Nat) : PM Ast := do
  if !(← ensureToken) then return .null
  takeToken ty

/-- `_PyPegen_new_identifier`, `Parser/pegen.c:495-562`. -/
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

/-- `_PyPegen_name_from_token`, `Parser/pegen.c:565-582`. -/
def nameFromToken (t : Ast) : PM Ast := fun p =>
  match t with
  | .tok t =>
    let n := newIdentifier t.bytes p
    match n.1 with
    | .null => (.null, { n.2 with errorIndicator := true })
    | id => (.node .Name [id, .node .Load [] none] (some (tokLoc t)), n.2)
  | _ => (.null, p)

/-- `_PyPegen_name_token`, `Parser/pegen.c:585-589`. -/
def nameToken : PM Ast := do nameFromToken (← expectToken TokKind.NAME.num)

/-- `_PyPegen_soft_keyword_token`, `Parser/pegen.c:597-612`. A `NAME` that is not a soft keyword
stays consumed: the function returns `NULL` with `p->mark` advanced. -/
def softKeywordToken : PM Ast := fun p =>
  let e := expectToken TokKind.NAME.num p
  match e.1 with
  | .tok t => if softKeywords.contains t.bytes then nameFromToken (.tok t) e.2 else (.null, e.2)
  | _ => (.null, e.2)

/-- `_PyPegen_expect_soft_keyword`, `Parser/pegen.c:457-478`. -/
def expectSoftKeyword (kw : List Nat) : PM Ast := fun p =>
  let e := ensureToken p
  if !e.1 then (.null, e.2) else
  let t := e.2.tokenAt e.2.mark
  if t.type != TokKind.NAME.num then (.null, e.2)
  else if t.bytes != kw then (.null, e.2)
  else nameToken e.2

/-- The tail of `_PyPegen_number_token`, `Parser/pegen.c:688-741`, on what
`_PyPegen_expect_token` returned. -/
def numberFromToken (t : Ast) : PM Ast := fun p =>
  match t with
  | .tok t =>
    if p.featureVersion < 6 && t.bytes.contains 95 then
      (.null, (raiseError0 "SyntaxError"
        "Underscores in numeric literals are only supported in Python 3.6 and greater"
        { p with errorIndicator := true }).2)
    else
      match parseNumber t.bytes with
      | .ok c => (.node .Constant [.const c, .null] (some (tokLoc t)), p)
      | .limit msg =>
        (.null, (raiseErrorKnownLocation "SyntaxError" t.lineno (-1) t.endLineno (-1)
          (msg ++ " - Consider hexadecimal for huge integer literals "
            ++ "to avoid decimal conversion limits.")
          { p with errorIndicator := true }).2)
  | _ => (.null, p)

/-- `_PyPegen_number_token`, `Parser/pegen.c:688-741`. -/
def numberToken : PM Ast := do numberFromToken (← expectToken TokKind.NUMBER.num)

/-- `_PyPegen_get_last_nonnwhitespace_token`, `Parser/pegen.c:481-492`. -/
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
