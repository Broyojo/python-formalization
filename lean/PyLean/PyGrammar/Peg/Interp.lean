import PyLean.PyGrammar.Peg.Actions

/-!
The PEG interpreter. Each definition mirrors what `Tools/peg_generator/pegen/c_generator.py`
emits for a rule, so that `callRule` on the data of `GrammarData.lean` is `Parser/parser.c`:
ordered choice, lookaheads, cut, `(memo)` rules, left recursion by seed growing, soft
keywords, the `invalid_` guard, the `MAXSTACK` level counter, and the rule that an action
returning `NULL` without an exception ends the rule with `NULL` and leaves `p->mark` alone.

`fuel` bounds call depth plus loop iterations, and running out of it is reported through
`PyError.cls = "<model fuel exhausted>"`, which is never a Python outcome. `Result` is the
pair of the rule's value (`.null` is `NULL`) and the state.
-/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- The model's fuel ran out. -/
def outOfFuel : PM Ast := do
  modify fun p => { p with errorIndicator := true }
  setErr { cls := "<model fuel exhausted>", msg := "" }
  return .null

/-- `add_level`: `if (p->level++ == MAXSTACK ...) _Pypegen_stack_overflow(p);`. The second
disjunct, `_Py_ReachedRecursionLimitWithMargin`, depends on the C stack of the running
build and is not modelled. -/
def addLevel : PM Unit := do
  let level := (← get).level
  modify fun p => { p with level := p.level + 1 }
  if level == MAXSTACK then stackOverflow

/-- `p->level--` -/
@[inline] def subLevel : PM Unit := modify fun p => { p with level := p.level - 1 }

/-- `p->level--; return v;` -/
@[inline] def retLevel (v : Ast) : PM Ast := do
  subLevel
  return v

/-- Non-`NULL`. -/
@[inline] def nonNull : Ast → Bool
  | .null => false
  | _ => true

/-- `_set_up_token_start_metadata_extraction`: `none` is the error return. -/
def startLocation (mark : Nat) : PM (Option (Int × Int)) := fun p =>
  let e := ensureToken p
  if !e.1 then (none, e.2) else
  let t := e.2.tokenAt mark
  (some (t.lineno, t.colOffset), e.2)

/-- `_PyPegen_expect_forced_result`, `Parser/pegen.c:430-440`. -/
def forcedResult (res : Ast) (expected : String) : PM Ast := fun p =>
  if p.errorIndicator then (.null, p) else
  match res with
  | .null => (.null, (raiseError "SyntaxError" false s!"expected ({expected})" p).2)
  | r => (r, p)

/-- `_PyPegen_expect_forced_token`, `Parser/pegen.c:443-462`. -/
def forcedToken (ty : Nat) (expected : String) : PM Ast := fun p =>
  if p.errorIndicator then (.null, p) else
  let e := ensureToken p
  if !e.1 then (.null, e.2) else
  let t := e.2.tokenAt e.2.mark
  if t.type != ty then
    (.null, (raiseRange "SyntaxError" (.tok t) (.tok t) s!"expected '{expected}'" e.2).2)
  else (.tok t, { e.2 with mark := e.2.mark + 1 })

/-- `emit_action`/`emit_default_action`: compute `_res` for a matched alternative.
`some` carries `_res`; `none` is the error return. -/
def altResult (a : Alt) (isGather : Bool) (env : Array Ast) (start : Int × Int) :
    PM (Option Ast) := do
  match a.action with
  | some act =>
    let ex : Extra ←
      if a.extra then do
        let t := lastNonWhitespaceToken (← get)
        pure { startLine := start.1, startCol := start.2, endLine := t.endLineno,
               endCol := t.endColOffset }
      else pure {}
    let r ← evalA env ex act
    let p ← get
    if (!nonNull r || p.errorIndicator) && p.errOccurred then
      modify fun p => { p with errorIndicator := true }
      return none
    return some r
  | none =>
    if a.nvars > 1 then
      if isGather then
        return some (.seq (env.getD 0 .null :: seqOf (env.getD 1 .null)))
      return some (rec_ .PDummy [])
    return some (env.getD 0 .null)

/-- `int _mark = p->mark` and `EXTRA`'s start location. -/
def ruleStart (r : Rule) : PM (Sum Ast (Nat × (Int × Int))) := fun p =>
  if r.extra then
    let e := startLocation p.mark p
    match e.1 with
    | some s => (.inr (p.mark, s), e.2)
    | none => (.inl .null, e.2)
  else (.inr (p.mark, (0, 0)), p)

/-- The head of every rule function, up to `int _mark = p->mark` and `EXTRA`'s start location:
`add_level`, the `error_indicator` check, the `(memo)` lookup. `inl v` is an early return of `v`;
`inr` carries `_mark` and the start location. -/
def rulePrologue (id : Nat) (r : Rule) : PM (Sum Ast (Nat × (Int × Int))) := fun p =>
  let p1 := (addLevel p).2
  if p1.errorIndicator then (.inl .null, p1) else
  let r2 : Option Ast × PS := if r.memo then isMemoized (1000 + id) p1 else (none, p1)
  match r2.1 with
  | some v => (.inl v, r2.2)
  | none => ruleStart r r2.2

/-- The end of `_handle_loop_rule_body`, on what `handle_alt_loop` returned. -/
def loopFinish (r : Rule) (res : List Ast × Nat × Bool × Bool) : PM Ast := fun p =>
  if !res.2.2.2 then retLevel .null p else
  let q := { p with mark := res.2.1 }
  if res.2.2.1 then retLevel .null q
  else if r.kind == .loop1 && (res.1.isEmpty || q.errorIndicator) then retLevel .null q
  else retLevel (.seq res.1.reverse) q

mutual
  /-- One item call. -/
  def runCall : Nat → Call → PM Ast
    | 0, _ => outOfFuel
    | f + 1, c =>
      match c with
      | .tok t => expectToken t
      | .name => nameToken
      | .number => numberToken
      | .string => expectToken TokKind.STRING.num
      | .softKeywordToken => softKeywordToken
      | .softKw s => expectSoftKeyword s
      | .forcedTok t s => forcedToken t s
      | .forcedRule r s => fun p =>
        let b := callRule f r p
        forcedResult b.1 s b.2
      | .rule r => callRule f r

  /-- `join_conditions`: the `&&` chain of an alternative. Returns `none` on failure, or
  the bound variables, oldest first, and whether a cut was passed. -/
  def runItems : Nat → List Item → Array Ast → Bool → PM (Option (Array Ast) × Bool)
    | 0, _, _, cut => fun p => ((none, cut), (outOfFuel p).2)
    | _ + 1, [], env, cut => fun p => ((some env, cut), p)
    | f + 1, .call c :: rest, env, cut => fun p =>
      let r := runCall f c p
      if nonNull r.1 then runItems f rest (env.push r.1) cut r.2 else ((none, cut), r.2)
    | f + 1, .opt c :: rest, env, cut => fun p =>
      let r := runCall f c p
      if r.2.errorIndicator then ((none, cut), r.2)
      else runItems f rest (env.push r.1) cut r.2
    | f + 1, .look positive c :: rest, env, cut => fun p =>
      let r := runCall f c p
      let q := { r.2 with mark := p.mark }
      if nonNull r.1 == positive then runItems f rest env cut q else ((none, cut), q)
    | f + 1, .cut :: rest, env, _ => runItems f rest (env.push (.int 1)) true

  /-- The alternatives of a non-loop rule, `visit_Rhs`/`visit_Alt`/`handle_alt_normal`.
  `some r` is `goto done` with `_res = r`; `none` is an error or cut return. An
  empty list falls off the end: `_res = NULL`, which also reaches `done`. -/
  def runAlts : Nat → List Alt → Bool → Nat → Int × Int → PM (Option Ast)
    | 0, _, _, _, _ => fun p => (none, (outOfFuel p).2)
    | _ + 1, [], _, _, _ => fun p => (some .null, p)
    | f + 1, a :: rest, isGather, mark, start => fun p =>
      if a.guardInvalid && !p.callInvalidRules then runAlts f rest isGather mark start p
      else if p.errorIndicator then (none, p)
      else
        let r := runItems f a.items #[] false p
        match r.1.1 with
        | some env => altResult a isGather env start r.2
        | none =>
          let q := { r.2 with mark := mark }
          if r.1.2 then (none, q) else runAlts f rest isGather mark start q

  /-- `handle_alt_loop`: `while (items) { ...; _children[_n++] = _res; _mark = p->mark; }`.
  Returns the children, the final `_mark`, the cut flag, and `false` on an error return. -/
  def runLoop : Nat → Alt → Nat → Int × Int → List Ast → PM (List Ast × Nat × Bool × Bool)
    | 0, _, mark, _, acc => fun p => ((acc, mark, false, false), (outOfFuel p).2)
    | f + 1, a, mark, start, acc => fun p =>
      let r := runItems f a.items #[] false p
      match r.1.1 with
      | some env =>
        let s := altResult a false env start r.2
        match s.1 with
        | some v => runLoop f a s.2.mark start (v :: acc) s.2
        | none => ((acc, mark, r.1.2, false), s.2)
      | none => ((acc, mark, r.1.2, true), r.2)

  /-- `_handle_default_rule_body`, `_handle_loop_rule_body`: the function `name_rule`, or
  `name_raw` for a left-recursive leader. -/
  def ruleBody : Nat → Nat → Rule → PM Ast
    | 0, _, _ => outOfFuel
    | f + 1, id, r => fun p =>
      let e := rulePrologue id r p
      match e.1 with
      | .inl v => retLevel v e.2
      | .inr x =>
        match r.kind with
        | .normal | .gather =>
          let a := runAlts f r.alts (r.kind == .gather) x.1 x.2 e.2
          match a.1 with
          | none => retLevel .null a.2
          | some v =>
            retLevel v (if r.memo then (insertMemo x.1 (1000 + id) v a.2).2 else a.2)
        | .loop0 | .loop1 =>
          if e.2.errorIndicator then retLevel .null e.2
          else
            let l := runLoop f (r.alts.headD default) x.1 x.2 [] e.2
            loopFinish r l.1 l.2

  /-- The `while (1)` of `_set_up_rule_memoization`: grow the seed. -/
  def growSeed : Nat → Nat → Rule → Nat → Nat → Ast → PM Ast
    | 0, _, _, _, _, _ => outOfFuel
    | f + 1, id, r, mark, resmark, res => fun p =>
      let p1 := (updateMemo mark (1000 + id) res p).2
      let b := ruleBody f id r { p1 with mark := mark }
      if b.2.errorIndicator then retLevel .null b.2
      else if !nonNull b.1 || b.2.mark ≤ resmark then retLevel res { b.2 with mark := resmark }
      else growSeed f id r mark b.2.mark b.1 b.2

  /-- `name_rule(p)`, `visit_Rule`. -/
  def callRule : Nat → Nat → PM Ast
    | 0, _ => outOfFuel
    | f + 1, id => fun p =>
      let r := ruleOf id
      if r.leftRec && r.leader then
        let m := isMemoized (1000 + id) (addLevel p).2
        match m.1 with
        | some v => retLevel v m.2
        | none => growSeed f id r m.2.mark m.2.mark .null m.2
      else if r.withoutInvalid then
        let b := ruleBody f id r { p with callInvalidRules := false }
        (b.1, { b.2 with callInvalidRules := p.callInvalidRules })
      else ruleBody f id r p
end

/-- `_PyPegen_parse`, the trailer of `Grammar/python.gram`. -/
def parseStart (fuel : Nat) : PM Ast := do
  match (← get).startRule with
  | .file => callRule fuel rule_file
  | .single => callRule fuel rule_interactive
  | .eval => callRule fuel rule_eval
  | .funcType => callRule fuel rule_func_type

/-- `bad_single_statement`, `Parser/pegen.c:755-778`, over the bytes after `tok->cur`. -/
def badSingleStatement : Nat → List Nat → Bool
  | 0, _ => false
  | f + 1, s =>
    let s := s.dropWhile fun c => c == 32 || c == 9 || c == 10 || c == 12
    match s with
    | [] => false
    | 0 :: _ => false
    | 35 :: r => badSingleStatement f (r.dropWhile (· != 10))
    | _ => true

/-- `reset_parser_state_for_error_pass`, `Parser/pegen.c:880-894`. -/
def resetForErrorPass : PM Unit :=
  modify fun p =>
    { p with lastStmt := (0, 0), memo := p.memo.map (fun _ => []), mark := 0,
             callInvalidRules := true }

/-- `_is_end_of_source`, `Parser/pegen.c:896-899`. -/
def isEndOfSource (p : PS) : Bool :=
  let err := p.tok.done
  err == E_EOF || err == E_EOFS || err == E_EOLS

/-- `_PyPegen_run_parser`, `Parser/pegen.c:948-1000`. `_PyPegen_set_syntax_error_metadata` fills
`SyntaxError._metadata`, which is outside `PyError`. -/
def runParser (fuel : Nat) : PM Ast := do
  let res ← parseStart fuel
  let p ← get
  if nonNull res && p.errOccurred then return .null
  if !nonNull res then
    if p.flagIncomplete && isEndOfSource p then
      set { p with tok := { p.tok with err := none } }
      raiseError "_IncompleteInputError" false "incomplete input"
      return .null
    if p.errOccurred && !((p.tok.err.map (·.cls)).map isSyntaxErrorClass).getD false then
      return .null
    let last := p.tokenAt (p.fill - 1)
    resetForErrorPass
    let _ ← parseStart fuel
    setSyntaxError last
    return .null
  if p.startRule == .single then
    let rest := (p.tok.src.extract p.tok.cur p.tok.src.size).toList
    if badSingleStatement (rest.length + 1) rest then
      raiseError "SyntaxError" false "multiple statements found while compiling a single statement"
      return .null
  return res

/-- The result of parsing: a tree or the exception. -/
def parseResult (p : PS) (r : Ast) : Except PyError Ast :=
  match p.tok.err with
  | some e => .error e
  | none =>
    match r with
    | .null => .error { cls := "SystemError", msg := "parser returned NULL without error" }
    | t => .ok t

/-- `compute_parser_flags`, `Parser/pegen.c:780-803`: `PyCF_*` and `CO_FUTURE_BARRY_AS_BDFL` bits
to `PyPARSE_*` bits. -/
def computeParserFlags (cf : Nat) : Nat :=
  (if cf &&& 0x200 != 0 then 0x0002 else 0)
    ||| (if cf &&& 0x800 != 0 then 0x0010 else 0)
    ||| (if cf &&& 0x400000 != 0 then 0x0020 else 0)
    ||| (if cf &&& 0x1000 != 0 then 0x0040 else 0)
    ||| (if cf &&& 0x4000 != 0 then 0x0100 else 0)

/-- `_PyPegen_Parser_New`, `Parser/pegen.c:807-865`, with `PyPARSE_*` flags. -/
def parserNew (tok : TokState) (start : StartRule) (flags featureVersion : Nat) (cfg : Cfg) : PS :=
  { tok := { tok with typeComments := flags &&& 0x0040 != 0 }, startRule := start, cfg,
    flagBarry := flags &&& 0x0020 != 0, flagDontImplyDedent := flags &&& 0x0002 != 0,
    flagIncomplete := flags &&& 0x0100 != 0, featureVersion }

/-- `_PyTokenizer_FromUTF8`, `Parser/tokenizer/utf8_tokenizer.c:31-55`. -/
def fromUtf8 (src : List Nat) (execInput preserveCrlf : Bool) : TokState :=
  let t := (translateNewlines src execInput preserveCrlf).toArray
  { src := t, encoding := some "utf-8" }

/-- Default fuel: call depth is bounded by `MAXSTACK` and loops by the token count. -/
def defaultFuel (n : Nat) : Nat := 20000 + 64 * n

/-- `_PyPegen_run_parser_from_string` with `PyCF_IGNORE_COOKIE`, `Parser/pegen.c:1054-1096`:
what `compile(str, ...)` and `ast.parse(str)` do. `cfFlags` are the other compile flags. -/
def parseStr (cfg : Cfg) (src : List Nat) (start : StartRule) (typeComments := false)
    (featureVersion := 14) (cfFlags : Nat := 0) (fuel := defaultFuel src.length) :
    Except PyError Ast :=
  let tok := fromUtf8 src (start == .file) false
  let flags := computeParserFlags (cfFlags ||| 0x800 ||| (if typeComments then 0x1000 else 0))
  let p := parserNew tok start flags featureVersion cfg
  let (r, p) := (runParser fuel).run p
  parseResult p r

end PyLean.PyGrammar.Peg
