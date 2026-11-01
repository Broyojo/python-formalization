import PyLean.PyGrammar.Check.Validate
import PyLean.PyGrammar.Peg.Numbers

/-!
`Python/ast_preprocess.c` and `Python/future.c`. What 3.14 still folds at this stage is
small: `__debug__`, docstring removal at `optimize=2`, `str % tuple` into `JoinedStr`, and
the numeric literals of `match` patterns.

The C `astfold_*` switch cases are a table `visits`, one row per constructor, listing the
fields visited in C order, so that the walk itself is one function.
-/

namespace PyLean.PyGrammar.Check

open PyLean Peg

/-- `_PyASTPreprocessState`. `cf` is the `cf_finally` stack, innermost first, as
`(in_finally, in_funcdef, in_loop)`. -/
structure PState where
  optimize : Int := 0
  futureAnnotations : Bool := false
  syntaxCheckOnly : Bool := false
  enableWarnings : Bool := false
  cf : List (Bool × Bool × Bool) := []
  /-- `(message, lineno, col_offset + 1, end_lineno, end_col_offset + 1)`, newest first. -/
  warnings : List (String × Int × Int × Int × Int) := []
  /-- Set when fuel ran out; never a Python outcome. -/
  fuelOut : Bool := false
  deriving Repr, Inhabited

/-- The folder's monad. -/
abbrev FM (α : Type) := StateM PState α

/-- A step of a `astfold_*` case. -/
inductive Step where
  /-- `CALL`, `CALL_OPT` or `CALL_SEQ` on a field, by its ASDL type. -/
  | fld (i : Nat)
  /-- `CALL(astfold_body, ...)` -/
  | body (i : Nat)
  /-- `if (!(ff_features & CO_FUTURE_ANNOTATIONS)) CALL_OPT(...)` -/
  | ann (i : Nat)
  /-- `PUSH_CONTEXT(finally, funcdef, loop)` -/
  | push (fin func loop : Bool)
  /-- `POP_CONTEXT` -/
  | pop

/-- The visits of each `case`, `Python/ast_preprocess.c:521-969`. -/
def visits : Ctor → List Step
  -- astfold_expr
  | .BoolOp => [.fld 1]
  | .NamedExpr => [.fld 0, .fld 1]
  | .BinOp => [.fld 0, .fld 2]
  | .UnaryOp => [.fld 1]
  | .Lambda => [.fld 0, .fld 1]
  | .IfExp => [.fld 0, .fld 1, .fld 2]
  | .Dict => [.fld 0, .fld 1]
  | .Set => [.fld 0]
  | .ListComp | .SetComp | .GeneratorExp => [.fld 0, .fld 1]
  | .DictComp => [.fld 0, .fld 1, .fld 2]
  | .Await | .Yield | .YieldFrom => [.fld 0]
  | .Compare => [.fld 0, .fld 2]
  | .Call => [.fld 0, .fld 1, .fld 2]
  | .FormattedValue => [.fld 0, .fld 2]
  | .Interpolation => [.fld 0, .fld 3]
  | .JoinedStr | .TemplateStr => [.fld 0]
  | .Attribute => [.fld 0]
  | .Subscript => [.fld 0, .fld 1]
  | .Starred => [.fld 0]
  | .Slice => [.fld 0, .fld 1, .fld 2]
  | .List | .Tuple => [.fld 0]
  -- astfold_keyword, comprehension, arguments, arg, withitem, handler, match_case
  | .keyword_ => [.fld 1]
  | .comprehension_ => [.fld 0, .fld 1, .fld 2]
  | .arguments_ => [.fld 0, .fld 1, .fld 2, .fld 3, .fld 4, .fld 5, .fld 6]
  | .arg_ => [.ann 1]
  | .withitem_ => [.fld 0, .fld 1]
  | .ExceptHandler => [.fld 0, .fld 2]
  | .match_case_ => [.fld 0, .fld 1, .fld 2]
  -- astfold_stmt
  | .FunctionDef | .AsyncFunctionDef =>
    [.fld 6, .fld 1, .push false true false, .body 2, .pop, .fld 3, .ann 4]
  | .ClassDef => [.fld 5, .fld 1, .fld 2, .body 3, .fld 4]
  | .Return => [.fld 0]
  | .Delete => [.fld 0]
  | .Assign => [.fld 0, .fld 1]
  | .AugAssign => [.fld 0, .fld 2]
  | .AnnAssign => [.fld 0, .ann 1, .fld 2]
  | .TypeAlias => [.fld 0, .fld 1, .fld 2]
  | .For | .AsyncFor => [.fld 0, .fld 1, .push false false true, .fld 2, .pop, .fld 3]
  | .While => [.fld 0, .push false false true, .fld 1, .pop, .fld 2]
  | .If => [.fld 0, .fld 1, .fld 2]
  | .With | .AsyncWith => [.fld 0, .fld 1]
  | .Raise => [.fld 0, .fld 1]
  | .Try | .TryStar => [.fld 0, .fld 1, .fld 2, .push true false false, .fld 3, .pop]
  | .Assert => [.fld 0, .fld 1]
  | .Expr => [.fld 0]
  | .Match => [.fld 0, .fld 1]
  -- astfold_pattern; `fold_const_match_patterns` is handled in `foldMatchValue`
  | .MatchSequence => [.fld 0]
  | .MatchMapping => [.fld 1]
  | .MatchClass => [.fld 0, .fld 1, .fld 3]
  | .MatchAs => [.fld 0]
  | .MatchOr => [.fld 0]
  -- astfold_type_param
  | .TypeVar => [.fld 1, .fld 2]
  | .ParamSpec | .TypeVarTuple => [.fld 1]
  | _ => []

/-- `_PyAST_GetDocString`, `Python/ast.c:1101-1115`. -/
def getDocString : List Ast → Option (List Nat)
  | .node .Expr [.node .Constant (.const (.str s) :: _) _] _ :: _ => some s
  | _ => none

/-- `control_flow_in_finally_warning` -/
def cfWarn (kw : String) (l : Loc) : FM Unit :=
  modify fun s => { s with warnings :=
    (s!"'{kw}' in a 'finally' block", l.lineno, l.colOffset + 1, l.endLineno, l.endColOffset + 1)
      :: s.warnings }

/-- `before_return` -/
def beforeReturn (l : Loc) : FM Unit := fun s =>
  match s.enableWarnings, s.cf with
  | true, (fin, func, _) :: _ => if fin && !func then cfWarn "return" l s else ((), s)
  | _, _ => ((), s)

/-- `before_loop_exit` -/
def beforeLoopExit (l : Loc) (kw : String) : FM Unit := fun s =>
  match s.enableWarnings, s.cf with
  | true, (fin, _, loop) :: _ => if fin && !loop then cfWarn kw l s else ((), s)
  | _, _ => ((), s)

/-- `parse_literal`, `Python/ast_preprocess.c:171-211`, on the rest of the format: the
literal text with `%%` collapsed, and what follows. -/
def parseLiteral : List Nat → List Nat × List Nat
  | [] => ([], [])
  | 37 :: 37 :: r =>
    let (l, rest) := parseLiteral r
    (37 :: l, rest)
  | 37 :: r => ([], 37 :: r)
  | c :: r =>
    let (l, rest) := parseLiteral r
    (c :: l, rest)

/-- Is the next character a digit? -/
@[inline] def isD (c : Nat) : Bool := 48 ≤ c && c ≤ 57

/-- The digit loop of `simple_format_arg_parse`: at most `MAXDIGITS - 1` digits followed by
another character, or `none`. Returns the value, the next character and the rest. -/
def digitsLoop (ch : Nat) (rest : List Nat) (v digits : Nat) : Nat → Option (Nat × Nat × List Nat)
  | 0 => none
  | f + 1 =>
    if isD ch then
      match rest with
      | [] => none
      | c :: r =>
        if digits + 1 ≥ 3 then none
        else digitsLoop c r (v * 10 + (ch - 48)) (digits + 1) f
    else some (v, ch, rest)

/-- The flags loop of `simple_format_arg_parse`: returns `ljust` and the first other
character. -/
def flagsLoop : List Nat → Bool → Option (Bool × Nat × List Nat)
  | [], _ => none
  | c :: r, lj =>
    if c == 45 then flagsLoop r true
    else if c == 43 || c == 32 || c == 35 || c == 48 then flagsLoop r lj
    else some (lj, c, r)

/-- `simple_format_arg_parse`, `Python/ast_preprocess.c:216-228`. Returns
`(spec, ljust, width, prec, rest)`, width and prec `-1` when absent. -/
def simpleFormatArgParse (s : List Nat) : Option (Nat × Bool × Int × Int × List Nat) := do
  let (lj, ch, rest) ← flagsLoop s false
  let (width, ch, rest) ←
    if isD ch then do
      let (v, c, r) ← digitsLoop ch rest 0 0 5
      pure ((v : Int), c, r)
    else pure ((-1 : Int), ch, rest)
  let (prec, ch, rest) ←
    if ch == 46 then do
      match rest with
      | [] => none
      | c :: r =>
        if isD c then do
          let (v, c', r') ← digitsLoop c r 0 0 5
          pure ((v : Int), c', r')
        else pure ((0 : Int), c, r)
    else pure ((-1 : Int), ch, rest)
  some (ch, lj, width, prec, rest)

/-- A `Constant` the preprocessor synthesizes, at location `-1`. -/
def constAtM1 (s : List Nat) : Ast :=
  .node .Constant [.const (.str s), .null] (some ⟨-1, -1, -1, -1⟩)

/-- `parse_format`, `Python/ast_preprocess.c:276-316`. -/
def parseFormat (s : List Nat) (arg : Ast) : Option (Ast × List Nat) := do
  let (spec, lj, width, prec, rest) ← simpleFormatArgParse s
  if spec == 115 || spec == 114 || spec == 97 then
    let w := if !lj && width > 0 then ">" else ""
    let w := if width ≥ 0 then w ++ toString width else w
    let w := if prec ≥ 0 then w ++ "." ++ toString prec else w
    let fs : Ast := if w.isEmpty then .null else constAtM1 (w.toList.map Char.toNat)
    let l := match arg with
      | .node _ _ (some l) => l
      | _ => default
    some (.node .FormattedValue [arg, .int spec, fs] (some l), rest)
  else none

/-- The loop of `optimize_format`, `Python/ast_preprocess.c:319-368`: `none` leaves the
node as it is. -/
def formatLoop : Nat → List Nat → List Ast → List Ast → Option (List Ast)
  | 0, _, _, _ => none
  | f + 1, fmt, elts, acc =>
    let (lit, rest) := parseLiteral fmt
    let acc := if lit.isEmpty then acc else constAtM1 lit :: acc
    match rest with
    | [] => if elts.isEmpty then some acc.reverse else none
    | _ :: after =>
      match elts with
      | [] => none
      | e :: es =>
        match parseFormat after e with
        | some (x, r) => formatLoop f r es (x :: acc)
        | none => none

/-- `fold_binop`, `Python/ast_preprocess.c:371-393`. -/
def foldBinop (st : PState) (node : Ast) : Ast :=
  if st.syntaxCheckOnly then node else
  match node with
  | .node .BinOp [.node .Constant (.const (.str fmt) :: _) _, .node .Mod _ _,
      .node .Tuple (.seq elts :: _) _] l =>
    let starred := elts.any fun e => match e with
      | .node .Starred _ _ => true
      | _ => false
    if starred then node else
    match formatLoop (fmt.length + 2) fmt elts [] with
    | some seq => .node .JoinedStr [.seq seq] l
    | none => node
  | _ => node

/-- Sign bit of a binary64. -/
def signBit : Nat := 0x8000000000000000

/-- `int` to binary64, `none` on `OverflowError`. -/
def intToBits (i : Int) : Option Nat :=
  let m := i.natAbs
  if m == 0 then some 0 else
  let b := roundToBits m 1
  if b == infBits then none
  else some (if i < 0 then b ||| signBit else b)

/-- `PyNumber_Negative` on a constant, `none` on `TypeError`. -/
def negConst : PyConst → Option PyConst
  | .int v => some (.int (-v))
  | .float b => some (.float (b ^^^ signBit))
  | .complex r i => some (.complex (r ^^^ signBit) (i ^^^ signBit))
  | .true_ => some (.int (-1))
  | .false_ => some (.int 0)
  | _ => none

/-- A real left operand as a float: `none` when it is out of range or not a number. -/
def realBits : PyConst → Option Nat
  | .int v => intToBits v
  | .float b => some b
  | .true_ => some 0x3FF0000000000000
  | .false_ => some 0
  | _ => none

/-- `real + complex` and `real - complex` on what `signed_real ('+'|'-') imaginary` can
produce: the imaginary literal has real part `+0.0`. `PyNumber_Add`/`Subtract` of
`Objects/complexobject.c`, `real_add`-style: `z.real = a ± b.real`. -/
def complexArith (add : Bool) (l r : PyConst) : Option PyConst :=
  match r with
  | .complex 0 im =>
    match realBits l with
    | some a =>
      if add then
        -- `-0.0 + 0.0 == 0.0`, and anything else keeps its value
        some (.complex (if a == signBit then 0 else a) im)
      else
        -- `a - 0.0 == a`, including `-0.0`; `-b.imag`
        some (.complex a (im ^^^ signBit))
    | none => none
  | _ => none

/-- `fold_const_match_patterns`, `Python/ast_preprocess.c:861-899`. -/
def foldMatchValue (st : PState) : Nat → Ast → Ast
  | 0, e => e
  | f + 1, e =>
    if st.syntaxCheckOnly then e else
    match e with
    | .node .UnaryOp [.node .USub _ _, .node .Constant (.const v :: _) _] l =>
      match negConst v with
      | some c => .node .Constant [.const c, .null] l
      | none => e
    | .node .BinOp [left, op, right] l =>
      let isAdd := match op with
        | .node .Add _ _ => some true
        | .node .Sub _ _ => some false
        | _ => none
      match isAdd, right with
      | some add, .node .Constant (.const r :: _) _ =>
        let left' := foldMatchValue st f left
        match left' with
        | .node .Constant (.const lv :: _) _ =>
          match complexArith add lv r with
          | some c => .node .Constant [.const c, .null] l
          | none => .node .BinOp [left', op, right] l
        | _ => .node .BinOp [left', op, right] l
      | _, _ => e
    | _ => e

/-- `remove_docstring`, `Python/ast_preprocess.c:442-464`, at index 0. -/
def removeDocstring : List Ast → List Ast
  | [.node _ _ (some l)] =>
    [.node .Pass [] (some ⟨l.lineno, l.colOffset, l.lineno, l.colOffset + 4⟩)]
  | _ :: rest => rest
  | [] => []

/-- "Turn a constant folded string expression statement into a JoinedStr so that it is not
mistaken for a docstring", the end of `astfold_body`. -/
def hideDocstring : List Ast → List Ast
  | .node .Expr [v] l :: rest => .node .Expr [.node .JoinedStr [.seq [v]] l] l :: rest
  | xs => xs

/-- `BEFORE_RETURN` and `BEFORE_LOOP_EXIT`, the checks made ahead of a node's children. -/
def preVisit (c : Ctor) (l : Option Loc) : FM Unit :=
  match c, l with
  | .Return, some loc => beforeReturn loc
  | .Break, some loc => beforeLoopExit loc "break"
  | .Continue, some loc => beforeLoopExit loc "continue"
  | _, _ => pure ()

/-- The patterns' values: `CALL(fold_const_match_patterns, ...)` for `MatchValue` and
`CALL_SEQ(fold_const_match_patterns, ...)` for the keys of `MatchMapping`. -/
def mappingKeys (st : PState) (f : Nat) (c : Ctor) (fs : List Ast) : List Ast :=
  match c, fs with
  | .MatchValue, [v] => [foldMatchValue st (f + 1) v]
  | .MatchMapping, [.seq keys, ps, rest] =>
    [.seq (keys.map (foldMatchValue st (f + 1))), ps, rest]
  | _, _ => fs

/-- What a node's own `case` does after its children: `fold_binop`, and the `Name_kind` case. -/
def postFold (st : PState) (c : Ctor) (fs : List Ast) (l : Option Loc) : Ast :=
  match c with
  | .BinOp => foldBinop st (.node c fs l)
  | .Name =>
    if st.syntaxCheckOnly then .node c fs l else
    match fs with
    | [.ident id, .node .Load _ _] =>
      if id == "__debug__".toList.map Char.toNat then
        .node .Constant [.const (if st.optimize == 0 then .true_ else .false_), .null] l
      else .node c fs l
    | _ => .node c fs l
  | _ => .node c fs l

mutual
  /-- `astfold_expr`, `astfold_stmt` and the rest: the node's `visits`, then its own rule. -/
  def fold : Nat → Ast → FM Ast
    | 0, e => fun s => (e, { s with fuelOut := true })
    | f + 1, e =>
      match e with
      | .node c fs l => fun s =>
        let r := runSteps f (visits c) fs (preVisit c l s).2
        (postFold r.2 c (mappingKeys r.2 f c r.1) l, r.2)
      | .seq xs => fun s =>
        let r := foldList f xs s
        (.seq r.1, r.2)
      | a => fun s => (a, s)

  /-- `CALL_SEQ`: elements in order, `NULL` skipped. -/
  def foldList : Nat → List Ast → FM (List Ast)
    | 0, xs => fun s => (xs, { s with fuelOut := true })
    | _ + 1, [] => fun s => ([], s)
    | f + 1, x :: xs => fun s =>
      let r1 := fold f x s
      let r2 := foldList f xs r1.2
      (r1.1 :: r2.1, r2.2)

  /-- `astfold_body`, `Python/ast_preprocess.c`. -/
  def foldBody : Nat → List Ast → FM (List Ast)
    | 0, xs => fun s => (xs, { s with fuelOut := true })
    | f + 1, stmts => fun st =>
      let doc := (getDocString stmts).isSome
      let strip := doc && decide (st.optimize ≥ 2)
      let doc' := if strip then false else doc
      let r := foldList f (if strip then removeDocstring stmts else stmts) st
      if !doc' && (getDocString r.1).isSome then (hideDocstring r.1, r.2) else r

  /-- Run a `visits` row over the fields. -/
  def runSteps : Nat → List Step → List Ast → FM (List Ast)
    | 0, _, fs => fun s => (fs, { s with fuelOut := true })
    | _ + 1, [], fs => fun s => (fs, s)
    | f + 1, s :: rest, fs => fun st =>
      match s with
      | .fld i =>
        let r := fold f (fs.getD i .null) st
        runSteps f rest (fs.set i r.1) r.2
      | .body i =>
        match fs.getD i .null with
        | .seq xs =>
          let r := foldBody f xs st
          runSteps f rest (fs.set i (.seq r.1)) r.2
        | x =>
          let r := fold f x st
          runSteps f rest (fs.set i r.1) r.2
      | .ann i =>
        if st.futureAnnotations then runSteps f rest fs st
        else
          let r := fold f (fs.getD i .null) st
          runSteps f rest (fs.set i r.1) r.2
      | .push a b c => runSteps f rest fs { st with cf := (a, b, c) :: st.cf }
      | .pop => runSteps f rest fs { st with cf := st.cf.drop 1 }
end

/-- `astfold_mod`, `Python/ast_preprocess.c:497-516`. -/
def foldMod (fuel : Nat) (m : Ast) : FM Ast := fun st =>
  match m with
  | .node .Module (b :: rest) l =>
    let r := foldBody fuel (seqL b) st
    (.node .Module (.seq r.1 :: rest) l, r.2)
  | .node .Interactive [b] l =>
    let r := foldList fuel (seqL b) st
    (.node .Interactive [.seq r.1] l, r.2)
  | .node .Expression [b] l =>
    let r := fold fuel b st
    (.node .Expression [r.1] l, r.2)
  | m => (m, st)

/-- `FUTURE_*` names accepted by `future_check_features`, `Python/future.c`. -/
def knownFutures : List (List Nat) :=
  ["nested_scopes", "generators", "division", "absolute_import", "with_statement",
   "print_function", "unicode_literals", "barry_as_FLUFL", "generator_stop",
   "annotations"].map (·.toList.map Char.toNat)

/-- An exception with a source range and no text, as `PyErr_RangedSyntaxLocationObject`
leaves it for a file that does not exist. -/
structure FutureError where
  msg : String
  loc : Loc
  deriving Repr, Inhabited

/-- `future_check_features`, `Python/future.c:9-62`. Returns whether `annotations` was seen. -/
def futureCheckFeatures (names : List Ast) : Except FutureError Bool :=
  names.foldlM (init := false) fun acc a =>
    match a with
    | .node _ (.ident n :: _) l =>
      let loc := l.getD default
      if n == "annotations".toList.map Char.toNat then .ok true
      else if knownFutures.contains n then .ok acc
      else if n == "braces".toList.map Char.toNat then .error ⟨"not a chance", loc⟩
      else
        let bs := (String.ofList (n.map Char.ofNat)).toList.take 100
        .error ⟨"future feature " ++ String.ofList bs ++ " is not defined", loc⟩
    | _ => .ok acc

/-- The statement loop of `future_parse`. -/
def futureLoop : List Ast → Bool → Except FutureError Bool
  | [], acc => .ok acc
  | .node .ImportFrom [.ident mod, names, .int 0] _ :: rest, acc =>
    if mod == "__future__".toList.map Char.toNat then
      match futureCheckFeatures (seqL names) with
      | .ok a => futureLoop rest (acc || a)
      | .error e => .error e
    else .ok acc
  | _ :: _, acc => .ok acc

/-- `future_parse`, `Python/future.c:65-106`. -/
def futureParse (m : Ast) : Except FutureError Bool :=
  match m with
  | .node .Module (b :: _) _ | .node .Interactive (b :: _) _ =>
    let body := seqL b
    futureLoop (if (getDocString body).isSome then body.drop 1 else body) false
  | _ => .ok false

/-- `_PyCompile_AstPreprocess`, `Python/compile.c:1544-1562`, when the tree is kept:
`optimize` as given (`-1` means `0` here), `no_const_folding` as stated. -/
def astPreprocess (m : Ast) (optimize : Int) (syntaxOnly : Bool) :
    Except FutureError Ast := do
  let ann ← futureParse m
  let st : PState := { optimize := if optimize == -1 then 0 else optimize,
                       syntaxCheckOnly := syntaxOnly, futureAnnotations := ann }
  return ((foldMod (8 * astSize m + 64) m).run st).1

end PyLean.PyGrammar.Check
