import PyLean.PyGrammar.Lexer.State

/-!
The tokenizer proper: a line-by-line mirror of `Parser/lexer/lexer.c` (3.14.7).
A C `goto` becomes a call of the function for its label, and `return MAKE_TOKEN(t)`
becomes `emit`, which throws the token out of the state monad with the state kept.
Loop bounds are `fuel` arguments; every call site passes more than the source can
consume, and `Ret.fuelOut` marks exhaustion, which is never a Python outcome.
-/

namespace PyLean.PyGrammar.Lexer

/-- `EOF` -/
def EOF : Int := -1

/-- A model fuel bound ran out. -/
def fuelOut {α : Type} : M α := throw { type := TokKind.ERRORTOKEN.num, fuelOut := true }

/-- `MAKE_TOKEN(t)` with no text. -/
@[inline] def emit0 {α : Type} (t : Nat) : M α := throw { type := t }

/-- `MAKE_TOKEN(t)` with `p_start`, `p_end`. -/
@[inline] def emit {α : Type} (t a b : Nat) : M α := throw { type := t, pStart := a, pEnd := b }

/-- `tok_underflow_string`, `Parser/tokenizer/string_tokenizer.c:8-27`, and the part of
`tok_underflow_readline` (`readline_tokenizer.c:70-102`) that survives once all lines
sit in one array. Returns `rc`. -/
def underflow (s : TokState) : Bool × TokState :=
  -- `strchr(tok->inp, '\n')`, then `strchr(tok->inp, '\0')`
  let n := s.src.size
  let rec findEnd : Nat → Nat → Option Nat
    | 0, _ => none
    | f + 1, i =>
      if i ≥ n then none
      else if s.src.getD i 0 == 10 then some (i + 1) else findEnd f (i + 1)
  let endPos := findEnd (n - s.inp + 1) s.inp
  match endPos with
  | none =>
    if s.inp ≥ n then
      if s.readline then
        let s1 := if s.start.isNone && !s.insideFString then { s with buf := s.cur } else s
        (false, { s1 with done := E_EOF, lineStart := s1.cur, implicitNewline := s1.implicitNewline })
      else (false, { s with done := E_EOF })
    else
      -- string tokenizer, last line without newline (`exec_input` false)
      let s1 := if s.start.isNone then { s with buf := s.cur } else s
      (true, { s1 with lineStart := s1.cur, lineno := s1.lineno + 1, colOffset := 0, inp := n })
  | some e =>
    if s.readline then
      let s1 := if s.start.isNone && !s.insideFString then { s with buf := s.cur } else s
      let fake := s1.fakeNewlineAt == some (e - 1)
      let s2 := { s1 with inp := e, implicitNewline := fake, lineStart := s1.cur }
      -- `_PyLexer_update_ftstring_expr(tok, 0)`
      let s3 :=
        if s2.modeIndex != 0 then
          let m := s2.mode
          if m.lastExprBuf.isNone || !(decide (m.lastExprEnd < (0 : Int))) then s2
          else s2.setMode fun m => { m with lastExprSize := m.lastExprSize + s2.strlen s2.cur }
        else s2
      (true, { s3 with lineno := s3.lineno + 1, colOffset := 0 })
    else
      let s1 := if s.start.isNone then { s with buf := s.cur } else s
      (true, { s1 with lineStart := s1.cur, lineno := s1.lineno + 1, colOffset := 0, inp := e })

/-- The fast path of `tok_nextc`. -/
@[inline] def nextcFast (s : TokState) : Int × TokState :=
  if s.colOffset.toNat ≥ 2147483647 then (EOF, { s with done := E_COLUMNOVERFLOW })
  else
    ((s.at s.cur : Int), { s with colOffset := s.colOffset + 1, cur := s.cur + 1 })

/-- `tok_nextc`, `Parser/lexer/lexer.c:60-96`. After a successful `underflow`
`cur != inp`, so the C `for (;;)` runs at most twice. -/
def nextcS (s : TokState) : Int × TokState :=
  if s.cur != s.inp then nextcFast s
  else if s.done != E_OK then (EOF, s)
  else
    let (rc, s) := underflow s
    if !rc then (EOF, { s with cur := s.inp })
    else
      let s := { s with lineStart := s.cur }
      if (s.slice s.lineStart s.inp).contains 0 then
        (EOF, { syntaxErrorRange "source code cannot contain null bytes" (-1) (-1) s with
                cur := s.inp })
      else nextcFast s

/-- `tok_nextc` in the monad. -/
@[inline] def nextc : M Int := fun s =>
  let (c, s) := nextcS s
  .ok c s

/-- `tok_backup`, `Parser/lexer/lexer.c:100-111`. -/
@[inline] def backup (c : Int) : M Unit :=
  modify fun s =>
    if c != EOF then { s with cur := s.cur - 1, colOffset := s.colOffset - 1 } else s

/-- `set_ftstring_expr`, `Parser/lexer/lexer.c:114-237`. The comment-stripping second
half operates on the same buffer as the scan in the first. Fails with `MemoryError`
on a negative size, which `PyUnicode_DecodeUTF8` turns into that exception. -/
def setFtstringExpr : M Bool := do
  let s ← get
  let m := s.mode
  if !(m.inDebug || m.tstring) || s.metadata.isSome then return false
  let n := m.lastExprSize - m.lastExprEnd
  let off := m.lastExprBuf.getD 0
  let bytes : List Nat :=
    if n ≤ 0 then [] else s.slice off (off + n.toNat)
  -- First loop: look for `#` outside string literals.
  let rec scan : List Nat → Bool → Nat → Bool
    | [], _, _ => false
    | ch :: rest, inStr, q =>
      if ch == ch! '\\' then
        match rest with
        | [] => false
        | _ :: t => scan t inStr q
      else if ch == ch! '"' || ch == ch! '\'' then
        if !inStr then scan rest true ch
        else if ch == q then scan rest false q
        else scan rest inStr q
      else if ch == ch! '#' && !inStr then true
      else scan rest inStr q
  -- Second loop: drop comments, keeping a newline if one ends them.
  let rec strip : Nat → List Nat → Bool → Nat → List Nat
    | 0, _, _, _ => []
    | _ + 1, [], _, _ => []
    | f + 1, ch :: rest, inStr, q =>
      if ch == ch! '"' || ch == ch! '\'' then
        if !inStr then ch :: strip f rest true ch
        else if ch == q then ch :: strip f rest false q
        else ch :: strip f rest inStr q
      else if ch == ch! '#' && !inStr then
        match rest.dropWhile (· != 10) with
        | [] => []
        | _ :: t => 10 :: strip f t inStr q
      else ch :: strip f rest inStr q
  if n < 0 then
    modify fun s => { s with err := some { cls := "MemoryError", msg := "" } }
    return true
  let out := if scan bytes false 0 then strip (bytes.length + 1) bytes false 0 else bytes
  -- `PyUnicode_DecodeUTF8(..., NULL)` is strict: a stale size can cut a character in two.
  match firstBadUtf8 (out.length + 1) out 0 with
  | some (i, b, why) =>
    modify fun s => { s with err := some (utf8Error i b why) }
    return true
  | none =>
    modify fun s => { s with metadata := some (utf8Decode out) }
    return false

/-- `_PyLexer_update_ftstring_expr`, `Parser/lexer/lexer.c@3.14.7:227-279`, without the case
`cur == 0`, which is in `underflow`. Allocation cannot fail in the model. -/
def updateFtstringExpr (cur : Nat) : M Unit :=
  modify fun s =>
    let size := s.strlen s.cur
    if cur == ch! '{' then
      s.setMode fun m => { m with lastExprBuf := some s.cur, lastExprSize := size, lastExprEnd := -1 }
    else if cur == ch! '}' || cur == ch! '!' then
      s.setMode fun m => { m with lastExprEnd := s.strlen (s.start.getD 0) }
    else if cur == ch! ':' then
      s.setMode fun m =>
        if m.lastExprEnd == -1 then { m with lastExprEnd := s.strlen (s.start.getD 0) } else m
    else s

/-- `lookahead`, `Parser/lexer/lexer.c:240-260`. -/
def lookahead (test : List Nat) : M Bool := do
  let rec go : List Nat → List Nat → M Bool
    | rest, consumed => do
      let c ← nextc
      match rest with
      | [] =>
        let res := !isIdChar c
        backup c
        consumed.forM fun x => backup x
        return res
      | t :: ts =>
        if c == (t : Int) then go ts (t :: consumed)
        else
          backup c
          consumed.forM fun x => backup x
          return false
  go test []

/-- `verify_end_of_number`, `Parser/lexer/lexer.c:263-318`. -/
def verifyEndOfNumber (c : Int) (kind : String) : M Bool := do
  if (← get).extraTokens then return true
  let r ←
    if c == ch! 'a' then lookahead [ch! 'n', ch! 'd']
    else if c == ch! 'e' then lookahead [ch! 'l', ch! 's', ch! 'e']
    else if c == ch! 'f' then lookahead [ch! 'o', ch! 'r']
    else if c == ch! 'i' then do
      let c2 ← nextc
      let r := c2 == ch! 'f' || c2 == ch! 'n' || c2 == ch! 's'
      backup c2
      pure r
    else if c == ch! 'o' then lookahead [ch! 'r']
    else if c == ch! 'n' then lookahead [ch! 'o', ch! 't']
    else pure false
  if r then
    backup c
    parserWarn "SyntaxWarning" s!"invalid {kind} literal"
    let _ ← nextc
  else if c < 128 && isIdChar c then
    backup c
    let _ ← syntaxerror s!"invalid {kind} literal"
    return false
  return true

/-- `verify_identifier`, `Parser/lexer/lexer.c:322-368`. `_PyUnicode_ScanIdentifier`
over the decoded token. -/
def verifyIdentifier : M Bool := do
  let s ← get
  if s.extraTokens then return true
  if s.decodingErred then return false
  let start := s.start.getD 0
  let cps := utf8Decode (s.slice start s.cur)
  -- `_PyUnicode_ScanIdentifier`
  let rec scan : List Nat → Nat → Nat
    | [], i => i
    | c :: rest, i => if isXidContinue c then scan rest (i + 1) else i
  let invalid : Nat :=
    match cps with
    | [] => 0
    | c :: rest => if isXidStart c then scan rest 1 else 0
  if invalid < cps.length then
    let ch := cps.getD invalid 0
    if invalid + 1 < cps.length then
      let n := (utf8Encode (cps.take (invalid + 1))).length
      modify fun s => { s with cur := start + n }
    if isPrintable ch then
      let _ ← syntaxerror s!"invalid character '{chStr ch}' (U+{hex4 ch})"
    else
      let _ ← syntaxerror s!"invalid non-printable character U+{hex4 ch}"
    return false
  return true

/-- `do { c = tok_nextc(tok); } while (p(c));` returning the first `c` failing `p`. -/
def skipWhile (p : Int → Bool) : Nat → M Int
  | 0 => fuelOut
  | f + 1 => do
    let c ← nextc
    if p c then skipWhile p f else return c

/-- `tok_decimal_tail`, `Parser/lexer/lexer.c:371-390`. -/
def decimalTail : Nat → M Int
  | 0 => fuelOut
  | f + 1 => do
    let c ← skipWhile isDigit (f + 1)
    if c != ch! '_' then return c
    let c ← nextc
    if !isDigit c then
      backup c
      let _ ← syntaxerror "invalid decimal literal"
      return 0
    decimalTail f

/-- `tok_continuation_line`, `Parser/lexer/lexer.c:393-411`. -/
def continuationLine : M Int := do
  let c ← nextc
  let c ← if c == ch! '\r' then nextc else pure c
  if c != ch! '\n' then
    modify fun s => { s with done := E_LINECONT }
    return -1
  let c ← nextc
  if c == EOF then
    modify fun s => { s with done := E_EOF, cur := s.inp }
    return -1
  backup c
  return c

/-- `maybe_raise_syntax_error_for_string_prefixes`, `Parser/lexer/lexer.c:413-456`. -/
def prefixError (b r u f t : Bool) : M Bool := do
  let err (p q : String) : M Bool := do
    let s ← get
    let _ ← syntaxerrorKnownRange (((s.start.getD 0 : Int) + 1 - (s.lineStart : Int)))
      ((s.cur : Int) - (s.lineStart : Int)) s!"'{p}' and '{q}' prefixes are incompatible"
    return true
  if u && b then return ← err "u" "b"
  if u && r then return ← err "u" "r"
  if u && f then return ← err "u" "f"
  if u && t then return ← err "u" "t"
  if b && f then return ← err "b" "f"
  if b && t then return ← err "b" "t"
  if f && t then return ← err "f" "t"
  return false

/-- `MAKE_TOKEN(ERRORTOKEN)` -/
@[inline] def errTok {α : Type} : M α := emit0 TokKind.ERRORTOKEN.num

/-- `return MAKE_TOKEN(_PyTokenizer_syntaxerror(tok, msg))`. -/
def errMsg {α : Type} (msg : String) : M α := do
  let t ← syntaxerror msg
  emit0 t

/-- Common end of the number branch: `tok_backup`, then `MAKE_TOKEN(NUMBER)`,
`Parser/lexer/lexer.c:1003-1006`. -/
def endNumber {α : Type} (c : Int) : M α := do
  backup c
  let s ← get
  emit TokKind.NUMBER.num (s.start.getD 0) s.cur

/-- The `imaginary:` label, `Parser/lexer/lexer.c:992-997`. -/
def imaginaryPart {α : Type} : M α := do
  let c ← nextc
  if !(← verifyEndOfNumber c "imaginary") then errTok
  endNumber c

/-- `if (c == 'j' ...) ... else verify`, `Parser/lexer/lexer.c:990-1000`. -/
def afterExponent {α : Type} (c : Int) : M α := do
  if c == ch! 'j' || c == ch! 'J' then imaginaryPart
  else
    if !(← verifyEndOfNumber c "decimal") then errTok
    endNumber c

/-- The `exponent:` label, `Parser/lexer/lexer.c:963-989`. -/
def exponentPart {α : Type} (fuel : Nat) (e : Int) : M α := do
  let c ← nextc
  if c == ch! '+' || c == ch! '-' then
    let c ← nextc
    if !isDigit c then
      backup c
      errMsg "invalid decimal literal"
  else if !isDigit c then
    backup c
    if !(← verifyEndOfNumber e "decimal") then errTok
    backup e
    let s ← get
    emit TokKind.NUMBER.num (s.start.getD 0) s.cur
  let c ← decimalTail fuel
  if c == 0 then errTok
  afterExponent c

/-- From the `fraction:` label to the exponent check, `Parser/lexer/lexer.c:954-963`. -/
def fractionPart {α : Type} (fuel : Nat) (c : Int) : M α := do
  let c ←
    if isDigit c then do
      let c ← decimalTail fuel
      if c == 0 then errTok
      pure c
    else pure c
  if c == ch! 'e' || c == ch! 'E' then exponentPart fuel c else afterExponent c

/-- `do { if '_' ...; check digit; do nextc while digit } while (c == '_')` for a
radix `digit` predicate, with the messages of each radix. -/
def radixDigits (fuel : Nat) (isD : Int → Bool) (kind : String) (reportDigit : Bool) : Nat → M Int
  | 0 => fuelOut
  | f + 1 => do
    let c ← nextc
    radixBody fuel isD kind reportDigit f c
where
  radixBody (fuel : Nat) (isD : Int → Bool) (kind : String) (reportDigit : Bool) :
      Nat → Int → M Int
    | 0, _ => fuelOut
    | f + 1, c => do
      let c ← if c == ch! '_' then nextc else pure c
      if !isD c then
        if reportDigit && isDigit c then
          errMsg s!"invalid digit '{chStr c.toNat}' in {kind} literal"
        else
          backup c
          errMsg s!"invalid {kind} literal"
      let c ← skipWhile isD fuel
      if c == ch! '_' then radixBody fuel isD kind reportDigit f c else return c

/-- `Parser/lexer/lexer.c:815-1007`: the `Number` branch. Precondition: `c` is a digit. -/
def numberBranch {α : Type} (c : Int) (fuel : Nat) : M α := do
  if c == ch! '0' then
    let c ← nextc
    if c == ch! 'x' || c == ch! 'X' then
      let c ← radixDigits fuel isXDigit "hexadecimal" false fuel
      if !(← verifyEndOfNumber c "hexadecimal") then errTok
      endNumber c
    else if c == ch! 'o' || c == ch! 'O' then
      let c ← radixDigits fuel (fun c => 48 ≤ c && c < 56) "octal" true fuel
      if isDigit c then errMsg s!"invalid digit '{chStr c.toNat}' in octal literal"
      if !(← verifyEndOfNumber c "octal") then errTok
      endNumber c
    else if c == ch! 'b' || c == ch! 'B' then
      let c ← radixDigits fuel (fun c => c == 48 || c == 49) "binary" true fuel
      if isDigit c then errMsg s!"invalid digit '{chStr c.toNat}' in binary literal"
      if !(← verifyEndOfNumber c "binary") then errTok
      endNumber c
    else
      -- maybe old-style octal; `c` is its first char; '0' is allowed as a literal
      let rec zeros : Nat → Int → M Int
        | 0, _ => fuelOut
        | f + 1, c => do
          let c ←
            if c == ch! '_' then do
              let c ← nextc
              if !isDigit c then
                backup c
                errMsg "invalid decimal literal"
              pure c
            else pure c
          if c != ch! '0' then return c
          let c ← nextc
          zeros f c
      let c ← zeros fuel c
      let zerosEnd := (← get).cur
      let nonzero := isDigit c
      let c ←
        if isDigit c then do
          let c ← decimalTail fuel
          if c == 0 then errTok
          pure c
        else pure c
      if c == ch! '.' then
        let c ← nextc
        fractionPart fuel c
      else if c == ch! 'e' || c == ch! 'E' then exponentPart fuel c
      else if c == ch! 'j' || c == ch! 'J' then imaginaryPart
      else
        if nonzero && !(← get).extraTokens then
          backup c
          let s ← get
          let t ← syntaxerrorKnownRange ((s.start.getD 0 : Int) + 1 - (s.lineStart : Int))
            ((zerosEnd : Int) - (s.lineStart : Int))
            ("leading zeros in decimal integer literals are not permitted; "
              ++ "use an 0o prefix for octal integers")
          emit0 t
        if !(← verifyEndOfNumber c "decimal") then errTok
        endNumber c
  else
    let c ← decimalTail fuel
    if c == 0 then errTok
    if c == ch! '.' then
      let c ← nextc
      fractionPart fuel c
    else if c == ch! 'e' || c == ch! 'E' then exponentPart fuel c
    else afterExponent c

/-- The string-body loop, `Parser/lexer/lexer.c:1119-1204`. -/
def stringBody (quote quoteSize : Int) : Nat → Int → Bool → M Unit
  | 0, _, _ => fuelOut
  | f + 1, endQuoteSize, hasEscaped => do
    if endQuoteSize == quoteSize then return
    let c ← nextc
    let s ← get
    if s.done == E_ERROR then
      let t := s
      let _ := t
      errTok
    if s.done == E_DECODE then return
    if c == EOF || (quoteSize == 1 && c == ch! '\n') then
      -- shift the state's location to the start of the string and report from the quote
      modify fun s => { s with cur := s.start.getD 0 + 1, lineStart := s.multiLineStart,
                               lineno := s.firstLineno }
      let start := s.lineno
      let s ← get
      if s.insideFString then
        let m := s.mode
        if (m.quote : Int) == quote && (m.quoteSize : Int) == quoteSize then
          errMsg s!"{m.prefixStr}-string: expecting '}'"
      if quoteSize == 3 then
        let _ ← syntaxerror
          s!"unterminated triple-quoted string literal (detected at line {start})"
        if c != ch! '\n' then modify fun s => { s with done := E_EOFS }
        errTok
      else
        if hasEscaped then
          let _ ← syntaxerror
            (s!"unterminated string literal (detected at line {start}); "
              ++ "perhaps you escaped the end quote?")
        else
          let _ ← syntaxerror s!"unterminated string literal (detected at line {start})"
        if c != ch! '\n' then modify fun s => { s with done := E_EOLS }
        errTok
    if c == quote then stringBody quote quoteSize f (endQuoteSize + 1) hasEscaped
    else if c == ch! '\\' then
      let c ← nextc
      let hasEscaped := hasEscaped || c == quote
      if c == ch! '\r' then
        let _ ← nextc
      stringBody quote quoteSize f 0 hasEscaped
    else stringBody quote quoteSize f 0 hasEscaped

/-- The `letter_quote:` label through the end of the string branch,
`Parser/lexer/lexer.c:1088-1209`. Precondition: `c` is a quote. -/
def letterQuote {α : Type} (c : Int) (fuel : Nat) : M α := do
  let quote := c
  modify fun s => { s with firstLineno := s.lineno, multiLineStart := s.lineStart }
  -- Find the quote size and start of string
  let c ← nextc
  let (quoteSize, endQuoteSize, c) ←
    if c == quote then do
      let c ← nextc
      if c == quote then pure ((3 : Int), (0 : Int), c)
      else pure ((1 : Int), (1 : Int), c)
    else pure ((1 : Int), (0 : Int), c)
  if c != quote then backup c
  stringBody quote quoteSize fuel endQuoteSize false
  let s ← get
  emit TokKind.STRING.num (s.start.getD 0) s.cur

/-- The depth check failing in `f_string_quote:`. -/
def tooManyFStrings (t : Ret) : M Unit := do
  let e ← syntaxerror "too many nested f-strings or t-strings"
  throw { t with type := e }

/-- `tok_mode_stack[++tok_mode_stack_index]`, after its depth check. -/
def pushMode (m : Mode) (t : Ret) : M Unit := fun s =>
  if s.modeIndex + 1 ≥ MAXFSTRINGLEVEL then tooManyFStrings t s
  else .ok () { s with modes := m :: s.modes, modeIndex := s.modeIndex + 1 }

/-- `tok_mode_stack_index--`, at the end of an f-string. -/
def popMode : M Unit :=
  modify fun s => { s with modes := s.modes.drop 1, modeIndex := s.modeIndex - 1 }

/-- The depth check failing on an open bracket. -/
def tooManyParens : M Unit := errMsg "too many nested parentheses"

/-- `tok->parenstack[tok->level++] = c`, after its depth check. -/
def openBracket (c : Int) : M Unit := fun s =>
  if s.level ≥ MAXLEVEL then tooManyParens s
  else
    let col : Int := (s.start.getD 0 : Int) - (s.lineStart : Int)
    let s1 := { s with parenstack := (c.toNat, s.lineno, col) :: s.parenstack,
                       level := s.level + 1 }
    .ok () (if s1.insideFString then s1.setMode fun m => { m with curlyDepth := m.curlyDepth + 1 }
            else s1)

/-- The `f_string_quote:` branch, `Parser/lexer/lexer.c:1010-1085`. -/
def fStringQuote {α : Type} (c : Int) : M α := do
  let quote := c
  modify fun s => { s with firstLineno := s.lineno, multiLineStart := s.lineStart }
  let afterQuote ← nextc
  let quoteSize ←
    if afterQuote == quote then do
      let aa ← nextc
      if aa == quote then pure 3
      else
        backup aa
        backup afterQuote
        pure 1
    else pure 1
  if afterQuote != quote then backup afterQuote
  let s ← get
  let st := s.start.getD 0
  let t : Ret := { type := TokKind.ERRORTOKEN.num, pStart := st, pEnd := s.cur }
  let first := s.at st
  let second := toLower (s.at (st + 1))
  let (raw, tstr) :=
    if first == ch! 'T' || first == ch! 't' then (second == ch! 'r', true)
    else if first == ch! 'F' || first == ch! 'f' then (second == ch! 'r', false)
    else (true, second == ch! 't')
  let m : Mode :=
    { fstringMode := true, quote := quote.toNat, quoteSize := quoteSize, start := st,
      multiLineStart := s.lineStart, firstLine := s.lineno, lastExprBuf := none,
      lastExprSize := 0, lastExprEnd := -1, inFormatSpec := false, inDebug := false,
      raw, tstring := tstr, curlyDepth := 0, curlyExprStart := -1 }
  pushMode m t
  throw { t with type := if tstr then TokKind.TSTRING_START.num else TokKind.FSTRING_START.num }

/-- The start of punctuation handling, for an f-string expression's `:`, `}`, `!` and `{`. -/
def punctFString (c : Int) : M Unit := do
  let s ← get
  let cur := s.mode
  let isPunct := c == ch! ':' || c == ch! '}' || c == ch! '!' || c == ch! '{'
  if isPunct && s.insideFString && cur.insideExpr then
    let cursor : Int := cur.curlyDepth - (if c != ch! '{' then 1 else 0)
    let inFormatSpec := cur.inFormatSpec
    let withDebug := cursor == 1 && (cur.inDebug || inFormatSpec)
    let cursorValid := cursor == 0 || withDebug
    if cursorValid then updateFtstringExpr c.toNat
    if cursorValid && c != ch! '{' then
      if ← setFtstringExpr then errTok
    if c == ch! ':' && cursor == cur.curlyExprStart then
      modify fun s =>
        if s.insideFString then s.setMode fun m => { m with fstringMode := true, inFormatSpec := true }
        else s
      let s ← get
      emit (oneChar c) (s.start.getD 0) s.cur

/-- Two- and three-character tokens. -/
def punctTwo (c : Int) : M Unit := do
  -- Check for two-character token
  let c2 ← nextc
  let tok2 := twoChars c c2
  if tok2 != TokKind.OP.num then
    let c3 ← nextc
    let tok3 := threeChars c c2 c3
    let t ←
      if tok3 != TokKind.OP.num then pure tok3
      else do
        backup c3
        pure tok2
    let s ← get
    emit t (s.start.getD 0) s.cur
  backup c2

/-- Keep track of parentheses nesting level. -/
def punctBracket (c : Int) : M Unit := do
  -- Keep track of parentheses nesting level
  let s ← get
  let cur := s.mode
  if c == ch! '(' || c == ch! '[' || c == ch! '{' then
    openBracket c
  else if c == ch! ')' || c == ch! ']' || c == ch! '}' then
    if s.insideFString && cur.curlyDepth == 0 && c == ch! '}' then
      errMsg s!"{cur.prefixStr}-string: single '}' is not allowed"
    if !s.extraTokens && s.level == 0 then
      errMsg s!"unmatched '{chStr c.toNat}'"
    if s.level > 0 then
      let (opening, openLine, _) := s.parenstack.headD (0, 0, 0)
      modify fun s => { s with level := s.level - 1, parenstack := s.parenstack.drop 1 }
      if !s.extraTokens && !((opening == ch! '(' && c == ch! ')') ||
          (opening == ch! '[' && c == ch! ']') || (opening == ch! '{' && c == ch! '}')) then
        if s.insideFString && opening == ch! '{' then
          let previous := cur.curlyDepth - 1
          if previous == cur.curlyExprStart then
            errMsg s!"{cur.prefixStr}-string: unmatched '{chStr c.toNat}'"
        if openLine != s.lineno then
          errMsg (s!"closing parenthesis '{chStr c.toNat}' does not match "
            ++ s!"opening parenthesis '{chStr opening}' on line {openLine}")
        else
          errMsg (s!"closing parenthesis '{chStr c.toNat}' does not match "
            ++ s!"opening parenthesis '{chStr opening}'")
    if s.insideFString then
      modify fun s => s.setMode fun m => { m with curlyDepth := m.curlyDepth - 1 }
      let m := (← get).mode
      if m.curlyDepth < 0 then
        errMsg s!"{m.prefixStr}-string: unmatched '{chStr c.toNat}'"
      if c == ch! '}' && m.curlyDepth == m.curlyExprStart then
        modify fun s =>
          if s.insideFString then
            s.setMode fun m =>
              { m with curlyExprStart := m.curlyExprStart - 1, fstringMode := true,
                       inFormatSpec := false, inDebug := false }
          else s

/-- The last checks, and the one-character token. -/
def punctFinal {α : Type} (c : Int) : M α := do
  if !isPrintable c.toNat then
    errMsg s!"invalid non-printable character U+{hex4 c.toNat}"
  if c == ch! '=' && (← get).mode.insideExprAtTop then
    modify fun s => s.setMode fun m => { m with inDebug := true }
  let s ← get
  emit (oneChar c) (s.start.getD 0) s.cur

/-- Everything after the string branches for a character that starts no token so far:
`Parser/lexer/lexer.c:1220-1359`. -/
def punctuation {α : Type} (c : Int) : M α := do
  punctFString c
  punctTwo c
  punctBracket c
  punctFinal c

/-- `f_string_quote:` onward, `Parser/lexer/lexer.c:1009-1359`, for a `c` that the
earlier branches left alone. The line continuation returns to `again:`. -/
def fromFStringQuote (c : Int) (fuel : Nat) : M Unit := do
  let s ← get
  let c0 := toLower (s.at (s.start.getD 0))
  if (c0 == ch! 'f' || c0 == ch! 'r' || c0 == ch! 't') && (c == ch! '\'' || c == ch! '"') then
    fStringQuote c
  if c == ch! '\'' || c == ch! '"' then letterQuote c fuel
  if c == ch! '\\' then
    let c ← continuationLine
    if c == -1 then errTok
    modify fun s => { s with contLine := true }
    return
  punctuation c

/-- What to do after one pass over `again:`. -/
inductive Jump where
  | nextline | again
  deriving Repr

/-- Result of the prefix loop, `Parser/lexer/lexer.c:704-741`. -/
inductive Prefix where
  | fQuote (c : Int)
  | lQuote (c : Int)
  | ident (c : Int)

/-- `Parser/lexer/lexer.c:704-741`. -/
def prefixLoop : Nat → Bool → Bool → Bool → Bool → Bool → Int → M Prefix
  | 0, _, _, _, _, _, _ => fuelOut
  | f + 1, b, r, u, ff, t, c => do
    let (b', r', u', ff', t', go) :=
      if !b && (c == ch! 'b' || c == ch! 'B') then (true, r, u, ff, t, true)
      else if !u && (c == ch! 'u' || c == ch! 'U') then (b, r, true, ff, t, true)
      else if !r && (c == ch! 'r' || c == ch! 'R') then (b, true, u, ff, t, true)
      else if !ff && (c == ch! 'f' || c == ch! 'F') then (b, r, u, true, t, true)
      else if !t && (c == ch! 't' || c == ch! 'T') then (b, r, u, ff, true, true)
      else (b, r, u, ff, t, false)
    if !go then return .ident c
    let c ← nextc
    if c == ch! '"' || c == ch! '\'' then
      if ← prefixError b' r' u' ff' t' then errTok
      if ff' || t' then return .fQuote c
      return .lQuote c
    prefixLoop f b' r' u' ff' t' c

/-- The body of a comment and type-comment handling, `Parser/lexer/lexer.c:610-685`.
Returns the character after the comment. -/
def commentBranch (fuel : Nat) (blankline : Bool) (c : Int) : M Int := do
  let rec eat : Nat → Int → M Int
    | 0, _ => fuelOut
    | f + 1, c =>
      if c != EOF && c != ch! '\n' && c != ch! '\r' then do
        let c ← nextc
        eat f c
      else return c
  let c ← eat fuel c
  let s ← get
  let st := s.start.getD 0
  if s.typeComments then
    -- `prefix = "# type: "`; spaces mean zero or more spaces or tabs.
    let pfx : List Nat := [ch! '#', ch! ' ', ch! 't', ch! 'y', ch! 'p', ch! 'e', ch! ':', ch! ' ']
    let rec skipWs : Nat → Nat → Int → Nat × Int
      | 0, p, col => (p, col)
      | f + 1, p, col =>
        if s.at p == ch! ' ' || s.at p == ch! '\t' then skipWs f (p + 1) (col + 1) else (p, col)
    let rec go : List Nat → Nat → Int → Option (Nat × Int)
      | [], p, col => some (p, col)
      | x :: xs, p, col =>
        if p ≥ s.cur then none
        else if x == ch! ' ' then
          let (p, col) := skipWs (s.cur - p + 1) p col
          go xs p col
        else if x == s.at p then go xs (p + 1) (col + 1)
        else none
    match go pfx st s.startingColOffset with
    | some (p, col) =>
      let ignoreEnd := p + 6
      let ignoreEndCol := col + 6
      backup c
      let s ← get
      let isIgnore :=
        s.cur ≥ ignoreEnd && s.slice p ignoreEnd == [ch! 'i', ch! 'g', ch! 'n', ch! 'o', ch! 'r', ch! 'e']
        && !(s.cur > ignoreEnd && (s.at ignoreEnd ≥ 128 || isAlnum (s.at ignoreEnd)))
      if isIgnore then
        if blankline then
          let _ ← nextc
          modify fun s => { s with atbol := true }
        let s ← get
        throw { type := TokKind.TYPE_IGNORE.num, pStart := ignoreEnd, pEnd := s.cur,
                typeCols := some (ignoreEndCol, s.colOffset) }
      else
        throw { type := TokKind.TYPE_COMMENT.num, pStart := p, pEnd := s.cur,
                typeCols := some (col, s.colOffset) }
    | none => pure ()
  if s.extraTokens then
    backup c
    modify fun s => { s with commentNewline := blankline }
    let s ← get
    emit TokKind.COMMENT.num st s.cur
  return c

/-- One pass from `again:`, `Parser/lexer/lexer.c:598-1359`. Every path either emits or
jumps back. -/
def againPass (fuel : Nat) (blankline : Bool) : M Jump := do
  modify fun s => { s with start := none }
  let c ← skipWhile (fun c => c == ch! ' ' || c == ch! '\t' || c == 12) fuel
  modify fun s => { s with start := some (s.cur - (if s.cur == 0 then 0 else 1)),
                           startingColOffset := s.colOffset - 1 }
  -- Skip comment, unless it's a type comment
  let c ← if c == ch! '#' then commentBranch fuel blankline c else pure c
  let s ← get
  if s.done == E_INTERACT_STOP then emit0 TokKind.ENDMARKER.num
  -- Check for EOF and errors now
  if c == EOF then
    if s.level != 0 then errTok
    emit0 (if s.done == E_EOF then TokKind.ENDMARKER.num else TokKind.ERRORTOKEN.num)
  -- Identifier
  if isIdStart c then
    match ← prefixLoop 8 false false false false false c with
    | .fQuote c =>
      fromFStringQuote c fuel
      return .again
    | .lQuote c => letterQuote c fuel
    | .ident c =>
      let rec idTail : Nat → Int → Bool → M (Int × Bool)
        | 0, _, _ => fuelOut
        | f + 1, c, n =>
          if isIdChar c then do
            let n := n || 128 ≤ c
            let c ← nextc
            idTail f c n
          else return (c, n)
      let (c, nonascii) ← idTail fuel c false
      backup c
      if nonascii then
        if !(← verifyIdentifier) then errTok
      let s ← get
      emit TokKind.NAME.num (s.start.getD 0) s.cur
  let c ← if c == ch! '\r' then nextc else pure c
  -- Newline
  if c == ch! '\n' then
    modify fun s => { s with atbol := true }
    let s ← get
    let st := s.start.getD 0
    if blankline || s.level > 0 then
      if s.extraTokens then
        modify fun s => { s with commentNewline := false }
        emit TokKind.NL.num st s.cur
      return .nextline
    if s.commentNewline && s.extraTokens then
      modify fun s => { s with commentNewline := false }
      emit TokKind.NL.num st s.cur
    modify fun s => { s with contLine := false }
    emit TokKind.NEWLINE.num st (s.cur - 1)
  -- Period or number starting with period?
  if c == ch! '.' then
    let c ← nextc
    if isDigit c then fractionPart fuel c
    if c == ch! '.' then
      let c ← nextc
      if c == ch! '.' then
        let s ← get
        emit TokKind.ELLIPSIS.num (s.start.getD 0) s.cur
      backup c
      backup (ch! '.')
    else backup c
    let s ← get
    emit TokKind.DOT.num (s.start.getD 0) s.cur
  if isDigit c then numberBranch c fuel
  fromFStringQuote c fuel
  return .again

/-- The dedent loop of the indentation check. -/
def popIndents (col : Nat) : Nat → M Unit
  | 0 => pure ()
  | f + 1 => fun s =>
    if s.indent > 0 && col < s.indstack.headD 0 then
      popIndents col f { s with pendin := s.pendin - 1, indent := s.indent - 1,
                                indstack := s.indstack.drop 1,
                                altindstack := s.altindstack.drop 1 }
    else .ok () s

/-- The `MAXINDENT` check failing. -/
def tooDeep : M Unit := do
  modify fun s => { s with done := E_TOODEEP, cur := s.inp }
  errTok

/-- `return MAKE_TOKEN(_PyTokenizer_indenterror(tok))`. -/
def tabError : M Unit := do
  let t ← indenterror
  emit0 t

/-- `tok->indstack[++tok->indent] = col`, after its depth check. -/
def pushIndent (col altcol : Nat) : M Unit := fun s =>
  if s.indent + 1 ≥ MAXINDENT then tooDeep s
  else if altcol ≤ s.altindstack.headD 0 then tabError s
  else
    .ok () { s with pendin := s.pendin + 1, indent := s.indent + 1,
                    indstack := col :: s.indstack, altindstack := altcol :: s.altindstack }

/-- The dedent branch: pop, then the indentation must match the stack. -/
def dedentTo (col altcol n : Nat) : M Unit := do
  popIndents col n
  let s ← get
  if col != s.indstack.headD 0 then
    modify fun s => { s with done := E_DEDENT, cur := s.inp }
    errTok
  if altcol != s.altindstack.headD 0 then tabError

/-- Comparing a line's indentation with the stack, `Parser/lexer/lexer.c:609-668`. -/
def indentStack (col altcol : Nat) : M Unit := fun s =>
  if col == s.indstack.headD 0 then
    if altcol != s.altindstack.headD 0 then tabError s else .ok () s
  else if col > s.indstack.headD 0 then pushIndent col altcol s
  else dedentTo col altcol (s.indent + 1) s

/-- The indentation block, `Parser/lexer/lexer.c:472-569`. Returns `blankline`. -/
def indentation (fuel : Nat) : M Bool := do
  modify fun s => { s with atbol := false }
  let rec scan : Nat → Nat → Nat → Nat → M (Nat × Nat × Nat × Int)
    | 0, _, _, _ => fuelOut
    | f + 1, col, altcol, contCol => do
      let c ← nextc
      if c == ch! ' ' then scan f (col + 1) (altcol + 1) contCol
      else if c == ch! '\t' then
        let t := (← get).tabsize
        scan f ((col / t + 1) * t) (altcol + 1) contCol
      else if c == 12 then scan f 0 0 contCol
      else if c == ch! '\\' then
        let contCol := if contCol != 0 then contCol else col
        let c ← continuationLine
        if c == -1 then errTok
        scan f col altcol contCol
      else if c == EOF && (← get).err.isSome then errTok
      else return (col, altcol, contCol, c)
  let (col, altcol, contCol, c) ← scan fuel 0 0 0
  backup c
  let s ← get
  let (blankline, col, altcol) :=
    if c == ch! '#' || c == ch! '\n' || c == ch! '\r' then
      if col == 0 && c == ch! '\n' && s.prompt then (false, col, altcol)
      else if s.prompt && s.lineno == 1 then (false, 0, 0)
      else (true, col, altcol)
    else (false, col, altcol)
  if !blankline && s.level == 0 then
    indentStack (if contCol != 0 then contCol else col) (if contCol != 0 then contCol else altcol)
  return blankline

/-- `tok_get_normal_mode`, `Parser/lexer/lexer.c:459-1360`. The `nextline:` and `again:`
labels are the two states of the loop. Never returns normally. -/
def normalMode (fuel : Nat) : Nat → Option Bool → M Unit
  | 0, _ => fuelOut
  | f + 1, none => do
    -- nextline:
    modify fun s => { s with start := none, startingColOffset := -1 }
    let blankline ← if (← get).atbol then indentation fuel else pure false
    modify fun s => { s with start := some s.cur, startingColOffset := s.colOffset }
    -- Return pending indents/dedents
    let s ← get
    if s.pendin != 0 then
      if s.pendin < 0 then
        modify fun s => { s with pendin := s.pendin + 1 }
        if s.extraTokens then emit TokKind.DEDENT.num s.cur s.cur
        emit0 TokKind.DEDENT.num
      else
        modify fun s => { s with pendin := s.pendin - 1 }
        if s.extraTokens then emit TokKind.INDENT.num s.buf s.cur
        emit0 TokKind.INDENT.num
    -- Peek ahead at the next character
    let c ← nextc
    backup c
    normalMode fuel f (some blankline)
  | f + 1, some blankline => do
    match ← againPass fuel blankline with
    | .nextline => normalMode fuel f none
    | .again => normalMode fuel f (some blankline)

/-- `FTSTRING_MIDDLE` of the current mode. -/
def Mode.middle (m : Mode) : Nat :=
  if m.tstring then TokKind.TSTRING_MIDDLE.num else TokKind.FSTRING_MIDDLE.num

/-- `FTSTRING_END` of the current mode. -/
def Mode.end_ (m : Mode) : Nat :=
  if m.tstring then TokKind.TSTRING_END.num else TokKind.FSTRING_END.num

/-- The `f_string_middle:` loop, `Parser/lexer/lexer.c:1417-1567`. Returns when
`end_quote_size == quote_size`. -/
def fstringMiddle : Nat → Nat → Bool → M Unit
  | 0, _, _ => fuelOut
  | f + 1, endQuoteSize, unicodeEscape => do
    let cur := (← get).mode
    if endQuoteSize == cur.quoteSize then return
    let c ← nextc
    let s ← get
    if s.done == E_ERROR || s.done == E_DECODE then errTok
    let inFormatSpec := cur.inFormatSpec && cur.insideExpr
    let st := s.start.getD 0
    if c == EOF || (cur.quoteSize == 1 && c == ch! '\n') then
      if s.decodingErred then errTok
      if inFormatSpec && c == ch! '\n' then
        if cur.quoteSize == 1 then
          let p := cur.prefixStr
          errMsg (s!"{p}-string: newlines are not allowed in format specifiers for "
            ++ s!"single quoted {p}-strings")
        backup c
        modify fun s => s.setMode fun m => { m with fstringMode := false, inFormatSpec := false }
        let s ← get
        emit cur.middle st s.cur
      let start := s.lineno
      modify fun s => { s with cur := cur.start + 1, lineStart := cur.multiLineStart,
                               lineno := cur.firstLine }
      if cur.quoteSize == 3 then
        let _ ← syntaxerror
          s!"unterminated triple-quoted {cur.prefixStr}-string literal (detected at line {start})"
        if c != ch! '\n' then modify fun s => { s with done := E_EOFS }
        errTok
      else
        errMsg s!"unterminated {cur.prefixStr}-string literal (detected at line {start})"
    if c == (cur.quote : Int) then fstringMiddle f (endQuoteSize + 1) unicodeEscape
    else if c == ch! '{' then
      updateFtstringExpr c.toNat
      let peek ← nextc
      if peek != ch! '{' || inFormatSpec then
        backup peek
        backup c
        modify fun s => s.setMode fun m => { m with curlyExprStart := m.curlyExprStart + 1 }
        if cur.curlyExprStart + 1 ≥ MAX_EXPR_NESTING then
          errMsg s!"{cur.prefixStr}-string: expressions nested too deeply"
        modify fun s => s.setMode fun m => { m with fstringMode := false, inFormatSpec := false }
        let s ← get
        emit cur.middle st s.cur
      else
        let s ← get
        emit cur.middle st (s.cur - 1)
    else if c == ch! '}' then
      if unicodeEscape then
        let s ← get
        emit cur.middle st s.cur
      let peek ← nextc
      if peek == ch! '}' && !inFormatSpec && cur.curlyDepth == 0 then
        let s ← get
        emit cur.middle st (s.cur - 1)
      else
        backup peek
        backup c
        modify fun s => s.setMode fun m => { m with fstringMode := false, inFormatSpec := false }
        let s ← get
        emit cur.middle st s.cur
    else if c == ch! '\\' then
      let peek ← nextc
      let peek ← if peek == ch! '\r' then nextc else pure peek
      if peek == ch! '{' || peek == ch! '}' then
        if !cur.raw then warnInvalidEscape peek.toNat
        backup peek
        fstringMiddle f 0 unicodeEscape
      else if !cur.raw && peek == ch! 'N' then
        let peek ← nextc
        if peek == ch! '{' then fstringMiddle f 0 true
        else
          backup peek
          fstringMiddle f 0 unicodeEscape
      else fstringMiddle f 0 unicodeEscape
    else fstringMiddle f 0 unicodeEscape

/-- `tok_get_fstring_mode`, `Parser/lexer/lexer.c:1363-1577`. -/
def fstringMode (fuel : Nat) : M Unit := do
  modify fun s => { s with start := some s.cur, firstLineno := s.lineno,
                           startingColOffset := s.colOffset }
  let cur := (← get).mode
  let startChar ← nextc
  if startChar == ch! '{' then
    let peek1 ← nextc
    backup peek1
    backup startChar
    if peek1 != ch! '{' then
      modify fun s => s.setMode fun m => { m with curlyExprStart := m.curlyExprStart + 1 }
      if cur.curlyExprStart + 1 ≥ MAX_EXPR_NESTING then
        errMsg s!"{cur.prefixStr}-string: expressions nested too deeply"
      modify fun s => s.setMode fun m => { m with fstringMode := false }
      normalMode fuel fuel none
  else backup startChar
  -- Check if we are at the end of the string
  let rec atEnd : Nat → M Bool
    | 0 => return true
    | n + 1 => do
      let q ← nextc
      if q != (cur.quote : Int) then
        backup q
        return false
      atEnd n
  if ← atEnd cur.quoteSize then
    let s ← get
    let st := s.start.getD 0
    popMode
    emit cur.end_ st s.cur
  -- f_string_middle:
  modify fun s => { s with multiLineStart := s.lineStart }
  fstringMiddle fuel 0 false
  -- Backup the quotes to emit a final FSTRING_MIDDLE; the FSTRING_END comes next time.
  (List.replicate cur.quoteSize (cur.quote : Int)).forM fun q => backup q
  let s ← get
  emit cur.middle (s.start.getD 0) s.cur

/-- `_PyTokenizer_Get` over `tok_get`, `Parser/lexer/lexer.c:1580-1588`:
returns the state, the token type and the token. `metadata` is per-token. -/
def tokenizerGet (s : TokState) : TokState × Nat × LexTok :=
  let s := { s with metadata := none }
  let fuel := s.src.size + 16
  let body : M Unit := if s.mode.fstringMode then fstringMode fuel else normalMode fuel fuel none
  let (s, r) : TokState × Ret :=
    match body s with
    | .ok _ s => (s, { type := TokKind.ERRORTOKEN.num, fuelOut := true })
    | .error r s => (s, r)
  if r.fuelOut then
    ({ s with err := some { cls := "<model fuel exhausted>", msg := "" }, done := E_ERROR },
      TokKind.ERRORTOKEN.num, tokenSetup s r)
  else
    let t := tokenSetup s r
    if s.decodingErred then ({ s with done := E_DECODE }, TokKind.ERRORTOKEN.num, t)
    else (s, r.type, t)

end PyLean.PyGrammar.Lexer
