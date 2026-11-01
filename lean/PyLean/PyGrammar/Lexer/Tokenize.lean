import PyLean.PyGrammar.Lexer.Iter

/-!
`Lib/tokenize.py` and its C twins in `Parser/tokenizer/helpers.c`: the coding cookie and BOM
logic, which both sides implement separately, and the `Untokenizer`.
-/

namespace PyLean.PyGrammar.Lexer

/-- `Lib/tokenize.py:_get_normal_name` and C `get_normal_name` work on at most 12 characters. -/
def prefixTwelve (s : List Nat) : List Nat :=
  (s.take 12).map fun c =>
    if c == 95 then 45 else toLower c

/-- Literal as code points. -/
@[inline] def lit (s : String) : List Nat := s.toList.map Char.toNat

/-- `get_normal_name`, `Parser/tokenizer/helpers.c:356-382`. -/
def cGetNormalName (s : List Nat) : List Nat :=
  let buf := prefixTwelve (s.takeWhile (· != 0))
  if buf == lit "utf-8" || (lit "utf-8-").isPrefixOf buf then lit "utf-8"
  else if buf == lit "latin-1" || buf == lit "iso-8859-1" || buf == lit "iso-latin-1"
      || (lit "latin-1-").isPrefixOf buf || (lit "iso-8859-1-").isPrefixOf buf
      || (lit "iso-latin-1-").isPrefixOf buf then lit "iso-8859-1"
  else s

/-- `_get_normal_name`, `Lib/tokenize.py:347-356`, with `str.lower` on ASCII. -/
def pyGetNormalName (orig : List Nat) : List Nat :=
  let enc := prefixTwelve orig
  if enc == lit "utf-8" || (lit "utf-8-").isPrefixOf enc then lit "utf-8"
  else if enc == lit "latin-1" || enc == lit "iso-8859-1" || enc == lit "iso-latin-1"
      || (lit "latin-1-").isPrefixOf enc || (lit "iso-8859-1-").isPrefixOf enc
      || (lit "iso-latin-1-").isPrefixOf enc then lit "iso-8859-1"
  else orig

/-- Characters of an encoding name: `[-\w.]`, ASCII. -/
def isEncChar (c : Nat) : Bool :=
  isAlnum c || c == 45 || c == 95 || c == 46

/-- The name after `coding[:=]` at `t`, skipping spaces and tabs. -/
def encodingAt (t : List Nat) : List Nat :=
  (t.dropWhile (fun c => c == 32 || c == 9)).takeWhile isEncChar

/-- Search `s` for `coding[:=]` followed by a non-empty name, as the second loop of
`get_coding_spec` and the lazy `.*?` of `cookie_re` both do. -/
def findCoding : List Nat → Option (List Nat)
  | [] => none
  | l@(_ :: r) =>
    if (lit "coding").isPrefixOf l then
      match l.drop 6 with
      | c :: t =>
        if c == 58 || c == 61 then
          let n := encodingAt t
          if n.isEmpty then findCoding r else some n
        else findCoding r
      | [] => findCoding r
    else findCoding r

/-- `get_coding_spec`, `Parser/tokenizer/helpers.c:386-432`: only whitespace may come before
the `#`, and the search stops 6 bytes from the end of the line. -/
def cGetCodingSpec (line : List Nat) : Option (List Nat) :=
  let rest := line.dropWhile (fun c => c == 32 || c == 9 || c == 12)
  match rest with
  | 35 :: _ =>
    let spaces := line.length - rest.length
    if spaces + 6 < line.length then (findCoding rest).map cGetNormalName else none
  | _ => none

/-- `cookie_re`, `Lib/tokenize.py:39`: `^[ \t\f]*#.*?coding[:=][ \t]*([-\w.]+)`, ASCII,
with `.` stopping at a newline. Result normalized by `_get_normal_name`. -/
def pyFindCookie (line : List Nat) : Option (List Nat) :=
  let rest := line.dropWhile (fun c => c == 32 || c == 9 || c == 12)
  match rest with
  | 35 :: _ => (findCoding (rest.takeWhile (· != 10))).map pyGetNormalName
  | _ => none

/-- `blank_re`, `Lib/tokenize.py:40`: `^[ \t\f]*(?:[#\r\n]|$)`. -/
def pyBlank (line : List Nat) : Bool :=
  match line.dropWhile (fun c => c == 32 || c == 9 || c == 12) with
  | [] => true
  | c :: _ => c == 35 || c == 13 || c == 10

/-- `Stop checking coding spec after a line containing anything except a comment`:
the loop of `_PyTokenizer_check_coding_spec`, `Parser/tokenizer/helpers.c:439-489`. -/
def cSeeksNext (line : List Nat) : Bool :=
  match line.dropWhile (fun c => c == 32 || c == 9 || c == 12) with
  | [] => true
  | c :: _ => c == 35 || c == 10 || c == 13

/-- Lines of bytes as `readline` splits them, at `\n` only. -/
def splitLinesLF (s : List Nat) : List (List Nat) :=
  let rec go : List Nat → List Nat → List (List Nat)
    | [], acc => if acc.isEmpty then [] else [acc.reverse]
    | c :: r, acc =>
      if c == 10 then (10 :: acc).reverse :: go r [] else go r (c :: acc)
  go s []

/-- Lines as `translate_newlines` makes them: `\r`, `\r\n` and `\n` all end one. -/
def splitLinesC (s : List Nat) : List (List Nat) :=
  splitLinesLF (translateNewlines s false false)

/-- The cookie the compiler sees in a source (`decode_str`,
`Parser/tokenizer/string_tokenizer.c:96-111`): lines 1 and 2, the second only if the first is
blank or a comment. -/
def cCookie (s : List Nat) : Option (List Nat) :=
  match splitLinesC s with
  | [] => none
  | l1 :: rest =>
    match cGetCodingSpec l1 with
    | some c => some c
    | none =>
      if cSeeksNext l1 then
        match rest with
        | l2 :: _ => cGetCodingSpec l2
        | [] => none
      else none

/-- The cookie `detect_encoding` finds, `Lib/tokenize.py:396-454` without the BOM. -/
def pyCookie (s : List Nat) : Option (List Nat) :=
  match splitLinesLF s with
  | [] => none
  | l1 :: rest =>
    match pyFindCookie l1 with
    | some c => some c
    | none =>
      if pyBlank l1 then
        match rest with
        | l2 :: _ => pyFindCookie l2
        | [] => none
      else none

/-- `str.isspace` -/
def isSpaceCp (c : Nat) : Bool :=
  (9 ≤ c && c ≤ 13) || (28 ≤ c && c ≤ 32) || c == 0x85 || c == 0xA0 || c == 0x1680
    || (0x2000 ≤ c && c ≤ 0x200A) || c == 0x2028 || c == 0x2029 || c == 0x202F || c == 0x205F
    || c == 0x3000

/-- `Untokenizer`, `Lib/tokenize.py:165-323`. `tokens` is newest first. -/
structure Unt where
  tokens : List (List Nat) := []
  prevRow : Int := 1
  prevCol : Int := 0
  prevType : Option Nat := none
  prevLine : List Nat := []
  deriving Repr, Inhabited

/-- `str.rstrip('\\\r\n')` -/
def rstripBs (s : List Nat) : List Nat :=
  ((s.reverse).dropWhile fun c => c == 92 || c == 13 || c == 10).reverse

/-- `add_backslash_continuation` -/
def addBackslashContinuation (u : Unt) (row : Int) : Unt :=
  let off := row - u.prevRow
  if off == 0 then u else
  let nl : List Nat := if (lit "\r\n").reverse.isPrefixOf u.prevLine.reverse then [13, 10] else [10]
  let ws := (rstripBs u.prevLine).reverse.takeWhile isSpaceCp
  let one := 92 :: nl
  { u with tokens := (ws ++ (List.replicate off.toNat one).flatten) :: u.tokens, prevCol := 0 }

/-- `add_whitespace`; `none` raises `ValueError`. -/
def addWhitespace (u : Unt) (row col : Int) : Option Unt :=
  if row < u.prevRow || (row == u.prevRow && col < u.prevCol) then none else
  let u := addBackslashContinuation u row
  let off := col - u.prevCol
  some (if off != 0 then { u with tokens := List.replicate off.toNat 32 :: u.tokens } else u)

/-- `escape_brackets`, `Lib/tokenize.py:202-223`. `chars` is newest first. -/
def escapeBrackets : List Nat → List Nat → Bool → List Nat
  | [], chars, _ => chars.reverse
  | c :: rest, chars, consume =>
    let (chars, consume) :=
      if c == 125 then
        if consume then (chars, false) else (125 :: chars, consume)
      else (chars, consume)
    if c == 123 then
      -- `characters[-2::-1]`: backslashes just before the last character
      let nb := ((chars.drop 1).takeWhile (· == 92)).length
      if nb % 2 == 0 || chars.head? != some 78 then
        escapeBrackets rest (123 :: 123 :: chars) consume
      else escapeBrackets rest (123 :: chars) true
    else escapeBrackets rest (c :: chars) consume

/-- The split of `str.splitlines()`. -/
def isLineBreak (c : Nat) : Bool :=
  c == 10 || c == 13 || c == 11 || c == 12 || (28 ≤ c && c ≤ 30) || c == 0x85 || c == 0x2028
    || c == 0x2029

/-- `token.splitlines()[-1]` of a non-empty token. -/
def lastLineOf (s : List Nat) : List Nat :=
  let t := match s.reverse with
    | c :: r => if isLineBreak c then r else c :: r
    | [] => []
  (t.takeWhile (!isLineBreak ·)).reverse

/-- `str.count` of a two-character string, non-overlapping. -/
def count2 (a : Nat) : List Nat → Nat
  | x :: y :: r => if x == a && y == a then 1 + count2 a r else count2 a (y :: r)
  | _ => 0

/-- `Untokenizer.untokenize` on 5-tuples. `indents` newest first, `startline` as in the
source. `none` is an exception from `add_whitespace` or `indents.pop()`. -/
def untokLoop : List TokInfo → Unt → List (List Nat) → Bool → Option Unt
  | [], u, _, _ => some u
  | t :: ts, u, indents, startline =>
    if t.type == TokKind.ENDMARKER.num then some u
    else if t.type == TokKind.INDENT.num then untokLoop ts u (t.str :: indents) startline
    else if t.type == TokKind.DEDENT.num then
      match indents with
      | [] => none
      | _ :: rest => untokLoop ts { u with prevRow := t.endLineno, prevCol := t.endCol } rest startline
    else
      let isNl := t.type == TokKind.NEWLINE.num || t.type == TokKind.NL.num
      let (u, startline', token, endCol) : Unt × Bool × List Nat × Int :=
        if isNl then (u, true, t.str, t.endCol)
        else if startline && !indents.isEmpty then
          let indent := indents.headD []
          if t.col ≥ indent.length then
            ({ u with tokens := indent :: u.tokens, prevCol := indent.length }, false, t.str, t.endCol)
          else (u, false, t.str, t.endCol)
        else if t.type == TokKind.FSTRING_MIDDLE.num || t.type == TokKind.TSTRING_MIDDLE.num then
          if t.str.contains 123 || t.str.contains 125 then
            let tok := escapeBrackets t.str [] false
            let last := lastLineOf tok
            (u, startline, tok, t.endCol + count2 123 last + count2 125 last)
          else (u, startline, t.str, t.endCol)
        else (u, startline, t.str, t.endCol)
      match addWhitespace u t.lineno t.col with
      | none => none
      | some u =>
        let u := { u with tokens := token :: u.tokens, prevRow := t.endLineno, prevCol := endCol }
        let u := if isNl then { u with prevRow := u.prevRow + 1, prevCol := 0 } else u
        untokLoop ts { u with prevType := some t.type, prevLine := t.line } indents startline'

/-- `tokenize.untokenize` on full token tuples. -/
def untokenize (ts : List TokInfo) : Option (List Nat) :=
  (untokLoop ts {} [] false).map fun u => (u.tokens.reverse).flatten

/-- `_transform_msg`, `Lib/tokenize.py:571-579`. -/
def transformMsg (m : String) : String :=
  let hasIt (s : List Char) : Bool :=
    let needle := "unterminated triple-quoted string literal".toList
    let rec go : List Char → Bool
      | [] => false
      | l@(_ :: t) => needle.isPrefixOf l || go t
    go s
  if hasIt m.toList then "EOF in multi-line string" else m

/-- `TokenInfo.exact_type`, `Lib/tokenize.py:54-58`. -/
def exactType (t : TokInfo) : Nat :=
  if t.type == TokKind.OP.num then
    let k := exactLookup (utf8Encode t.str)
    if k != TokKind.OP.num then k else t.type
  else t.type

/-- `NT_OFFSET`, `Lib/token.py`. -/
def NT_OFFSET : Nat := 256
/-- `ISTERMINAL` -/
def isTerminal (x : Nat) : Bool := decide (x < NT_OFFSET)
/-- `ISNONTERMINAL` -/
def isNonTerminal (x : Nat) : Bool := decide (x ≥ NT_OFFSET)
/-- `ISEOF` -/
def isEof (x : Nat) : Bool := x == TokKind.ENDMARKER.num

/-! ### Properties -/

/-- `Lib/token.py`: every token number is terminal or nonterminal and never both, every kind in
`Grammar/Tokens` is terminal, and `ENDMARKER` is the only EOF. -/
def TokenPredicates : Prop :=
  (∀ x : Nat, isTerminal x = !isNonTerminal x) ∧
  (TokKind.all.all fun k => isTerminal k.num && (isEof k.num == (k == .ENDMARKER))) = true

theorem tokenPredicates_proven : TokenPredicates := by
  constructor
  · intro x
    by_cases h : x < NT_OFFSET
    · simp [isTerminal, isNonTerminal, h, Nat.not_le.mpr h]
    · simp [isTerminal, isNonTerminal, h, Nat.le_of_not_lt h]
  · decide +kernel

/-- `TokenInfo.exact_type`: an `OP` token with an exact spelling has the type of that spelling. -/
def ExactTypeResolves : Prop :=
  (TokKind.all.all fun k =>
    match k.exact? with
    | some e =>
      exactType { type := TokKind.OP.num, str := e.toList.map Char.toNat, lineno := 1, col := 0,
                  endLineno := 1, endCol := 1, line := [] } == k.num
    | none => true) = true

set_option maxRecDepth 100000 in
theorem exactTypeResolves_proven : ExactTypeResolves := by
  unfold ExactTypeResolves; decide +kernel

/-- `_get_normal_name` "Imitates get_normal_name in Parser/tokenizer/helpers.c": the two agree
on every name without a NUL. -/
def NormalNameTwin : Prop :=
  ∀ s : List Nat, 0 ∉ s → cGetNormalName s = pyGetNormalName s

theorem takeWhile_ne_zero (s : List Nat) (h : 0 ∉ s) : s.takeWhile (· != 0) = s := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ 0 := fun e => h (by simp [e])
    have hr : 0 ∉ xs := fun m => h (List.mem_cons_of_mem _ m)
    simp [List.takeWhile_cons, hx, ih hr]

theorem normalNameTwin_proven : NormalNameTwin := by
  intro s h
  simp [cGetNormalName, pyGetNormalName, takeWhile_ne_zero s h]

/-- `detect_encoding` and the C tokenizer read the same cookie from the same bytes. -/
def CookieTwin : Prop := ∀ s : List Nat, cCookie s = pyCookie s

/-- `#\r#\r# coding: latin-1\n`: to C these are three lines, and the cookie is on the third;
to `readline` they are one. -/
def crCookie : List Nat :=
  [35, 13, 35, 13, 35, 32] ++ lit "coding: latin-1\n"

set_option maxRecDepth 10000 in
theorem cookieTwin_refuted : ¬ CookieTwin := fun h =>
  absurd (h crCookie) (by decide +kernel)

end PyLean.PyGrammar.Lexer
