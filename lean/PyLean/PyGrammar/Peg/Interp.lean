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
  let p ← get
  set { p with level := p.level + 1 }
  if p.level == MAXSTACK then stackOverflow

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
def startLocation (mark : Nat) : PM (Option (Int × Int)) := do
  let p ← get
  if p.mark == p.fill then
    if (← fillToken) < 0 then
      modify fun p => { p with errorIndicator := true }
      return none
  let t := (← get).tokenAt mark
  return some (t.lineno, t.colOffset)

/-- `_PyPegen_expect_forced_result`, `Parser/pegen.c:430-440`. -/
def forcedResult (res : Ast) (expected : String) : PM Ast := do
  if (← get).errorIndicator then return .null
  match res with
  | .null =>
    raiseError "SyntaxError" false s!"expected ({expected})"
    return .null
  | r => return r

/-- `_PyPegen_expect_forced_token`, `Parser/pegen.c:443-462`. -/
def forcedToken (ty : Nat) (expected : String) : PM Ast := do
  if (← get).errorIndicator then return .null
  let p ← get
  if p.mark == p.fill then
    if (← fillToken) < 0 then
      modify fun p => { p with errorIndicator := true }
      return .null
  let p ← get
  let t := p.tokenAt p.mark
  if t.type != ty then
    raiseRange "SyntaxError" (.tok t) (.tok t) s!"expected '{expected}'"
    return .null
  set { p with mark := p.mark + 1 }
  return .tok t

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
      set { p with errorIndicator := true }
      return none
    return some r
  | none =>
    if a.nvars > 1 then
      if isGather then
        return some (.seq (env.getD 0 .null :: seqOf (env.getD 1 .null)))
      return some (rec_ .PDummy [])
    return some (env.getD 0 .null)

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
      | .forcedRule r s => do forcedResult (← callRule f r) s
      | .rule r => callRule f r

  /-- `join_conditions`: the `&&` chain of an alternative. Returns `none` on failure, or
  the bound variables, oldest first, and whether a cut was passed. -/
  def runItems : Nat → List Item → Array Ast → Bool → PM (Option (Array Ast) × Bool)
    | 0, _, _, cut => do
      let _ ← outOfFuel
      return (none, cut)
    | _ + 1, [], env, cut => return (some env, cut)
    | f + 1, it :: rest, env, cut => do
      match it with
      | .call c =>
        let v ← runCall f c
        if nonNull v then runItems f rest (env.push v) cut else return (none, cut)
      | .opt c =>
        let v ← runCall f c
        if (← get).errorIndicator then return (none, cut)
        runItems f rest (env.push v) cut
      | .look positive c =>
        let mark := (← get).mark
        let v ← runCall f c
        modify fun p => { p with mark := mark }
        if nonNull v == positive then runItems f rest env cut else return (none, cut)
      | .cut => runItems f rest (env.push (.int 1)) true

  /-- The alternatives of a non-loop rule, `visit_Rhs`/`visit_Alt`/`handle_alt_normal`.
  `some r` is `goto done` with `_res = r`; `none` is an error or cut return. An
  empty list falls off the end: `_res = NULL`, which also reaches `done`. -/
  def runAlts : Nat → List Alt → Bool → Nat → Int × Int → PM (Option Ast)
    | 0, _, _, _, _ => do
      let _ ← outOfFuel
      return none
    | _ + 1, [], _, _, _ => return some .null
    | f + 1, a :: rest, isGather, mark, start => do
      if a.guardInvalid && !(← get).callInvalidRules then
        return ← runAlts f rest isGather mark start
      if (← get).errorIndicator then return none
      let (m, cut) ← runItems f a.items #[] false
      match m with
      | some env =>
        match ← altResult a isGather env start with
        | some r => return some r
        | none => return none
      | none =>
        modify fun p => { p with mark := mark }
        if cut then return none
        runAlts f rest isGather mark start

  /-- `handle_alt_loop`: `while (items) { ...; _children[_n++] = _res; _mark = p->mark; }`.
  Returns the children, the final `_mark`, the cut flag, and `false` on an error return. -/
  def runLoop : Nat → Alt → Nat → Int × Int → List Ast → PM (List Ast × Nat × Bool × Bool)
    | 0, _, mark, _, acc => do
      let _ ← outOfFuel
      return (acc, mark, false, false)
    | f + 1, a, mark, start, acc => do
      let (m, cut) ← runItems f a.items #[] false
      match m with
      | some env =>
        match ← altResult a false env start with
        | some r =>
          let mark' := (← get).mark
          runLoop f a mark' start (r :: acc)
        | none => return (acc, mark, cut, false)
      | none => return (acc, mark, cut, true)

  /-- `_handle_default_rule_body`, `_handle_loop_rule_body`: the function `name_rule`, or
  `name_raw` for a left-recursive leader. -/
  def ruleBody : Nat → Nat → Rule → PM Ast
    | 0, _, _ => outOfFuel
    | f + 1, id, r => do
      addLevel
      if (← get).errorIndicator then return ← retLevel .null
      if r.memo then
        match ← isMemoized (1000 + id) with
        | some v => return ← retLevel v
        | none => pure ()
      let mark := (← get).mark
      let start ←
        if r.extra then
          match ← startLocation mark with
          | some s => pure s
          | none => return ← retLevel .null
        else pure (0, 0)
      match r.kind with
      | .normal | .gather =>
        match ← runAlts f r.alts (r.kind == .gather) mark start with
        | none => retLevel .null
        | some v =>
          if r.memo then insertMemo mark (1000 + id) v
          retLevel v
      | .loop0 | .loop1 =>
        let a := r.alts.headD default
        if (← get).errorIndicator then return ← retLevel .null
        let (acc, mark', cut, ok) ← runLoop f a mark start []
        if !ok then return ← retLevel .null
        modify fun p => { p with mark := mark' }
        if cut then return ← retLevel .null
        if r.kind == .loop1 then
          if acc.isEmpty || (← get).errorIndicator then return ← retLevel .null
        retLevel (.seq acc.reverse)

  /-- The `while (1)` of `_set_up_rule_memoization`: grow the seed. -/
  def growSeed : Nat → Nat → Rule → Nat → Nat → Ast → PM Ast
    | 0, _, _, _, _, _ => outOfFuel
    | f + 1, id, r, mark, resmark, res => do
      updateMemo mark (1000 + id) res
      modify fun p => { p with mark := mark }
      let raw ← ruleBody f id r
      if (← get).errorIndicator then return ← retLevel .null
      let p ← get
      if !nonNull raw || p.mark ≤ resmark then
        modify fun p => { p with mark := resmark }
        retLevel res
      else growSeed f id r mark p.mark raw

  /-- `name_rule(p)`, `visit_Rule`. -/
  def callRule : Nat → Nat → PM Ast
    | 0, _ => outOfFuel
    | f + 1, id => do
      let r := ruleOf id
      if r.leftRec && r.leader then
        addLevel
        match ← isMemoized (1000 + id) with
        | some v => retLevel v
        | none =>
          let mark := (← get).mark
          growSeed f id r mark mark .null
      else if r.withoutInvalid then
        let prev := (← get).callInvalidRules
        modify fun p => { p with callInvalidRules := false }
        let v ← ruleBody f id r
        modify fun p => { p with callInvalidRules := prev }
        return v
      else ruleBody f id r
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

/-- `_PyPegen_Parser_New`, `Parser/pegen.c:806-865`, with `PyPARSE_*` flags. -/
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
