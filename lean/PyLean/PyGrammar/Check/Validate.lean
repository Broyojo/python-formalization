import PyLean.Core
import PyLean.PyGrammar.Ast

/-!
`Python/ast.c`: `_PyAST_Validate`, a line-by-line mirror over the generic `Ast`. Fuel bounds
the recursion on the tree; the C code's `Py_EnterRecursiveCall` limit depends on the C stack
and is not modelled, so `validate` reports `PyExc.modelFuel` where the tree is deeper than
its fuel.
-/

namespace PyLean.PyGrammar.Check

open PyLean

/-- What a C validator returns: `1`, or `0` with an exception set. -/
abbrev V := Py Unit

/-- `return 1;` -/
@[inline] def ok1 : V := .ok ()

/-- `PyErr_SetString(PyExc_ValueError, m); return 0;` -/
@[inline] def verr (m : String) : V := .error (.valueError m)

/-- `PyErr_SetString(PyExc_TypeError, m); return 0;` -/
@[inline] def terr (m : String) : V := .error (.typeError m)

/-- Not a Python exception: the C code dereferences `NULL` here and the process dies. -/
def nullDeref : V := .error (.named "<NULL dereference>" "")

/-- `a && b` over validators. -/
@[inline] def V.and (a : V) (b : Unit → V) : V :=
  match a with
  | .ok () => b ()
  | e => e

/-- Elements of a sequence field. -/
def seqL : Ast → List Ast
  | .seq xs => xs
  | _ => []

/-- `seq->size` -/
def seqLen (a : Ast) : Nat := (seqL a).length

/-- `VALIDATE_POSITIONS`, `Python/ast.c:30-49`. A node with no attributes passes. -/
def validatePositions : Option Loc → V
  | none => ok1
  | some l =>
    if l.lineno > l.endLineno then
      verr s!"AST node line range ({l.lineno}, {l.endLineno}) is not valid"
    else if (l.lineno < 0 && l.endLineno != l.lineno)
        || (l.colOffset < 0 && l.colOffset != l.endColOffset) then
      verr (s!"AST node column range ({l.colOffset}, {l.endColOffset}) for line range "
        ++ s!"({l.lineno}, {l.endLineno}) is not valid")
    else if l.lineno == l.endLineno && l.colOffset > l.endColOffset then
      verr s!"line {l.lineno}, column {l.colOffset}-{l.endColOffset} is not a valid range"
    else ok1

/-- `validate_name`, `Python/ast.c:52-69`. -/
def validateName (name : Ast) : V :=
  match name with
  | .ident [78, 111, 110, 101] => verr "identifier field can't represent 'None' constant"
  | .ident [84, 114, 117, 101] => verr "identifier field can't represent 'True' constant"
  | .ident [70, 97, 108, 115, 101] => verr "identifier field can't represent 'False' constant"
  | _ => ok1

/-- `expr_context_name` -/
def ctxName : Ctor → String
  | .Load => "Load"
  | .Store => "Store"
  | _ => "Del"

/-- `validate_constant`, `Python/ast.c:157-207`. Every `PyConst` is of an allowed type, so
only tuples and frozensets recurse, and they cannot fail. -/
def validateConstant (_ : PyConst) : V := ok1

/-- The `ctx` field of a node for the first switch of `validate_expr`. -/
def ctxOfAst : Ast → Ctor
  | .node c _ _ => c
  | _ => .Load

/-- `ensure_literal_number` -/
def ensureLiteralNumber (e : Ast) (real imag : Bool) : Bool :=
  match e with
  | .node .Constant (.const v :: _) _ =>
    match v with
    | .float _ | .int _ => real
    | .complex _ _ => imag
    | _ => false
  | _ => false

/-- `ensure_literal_negative` -/
def ensureLiteralNegative (e : Ast) (real imag : Bool) : Bool :=
  match e with
  | .node .UnaryOp [.node .USub _ _, operand] _ =>
    match operand with
    | .node .Constant _ _ => ensureLiteralNumber operand real imag
    | _ => false
  | _ => false

/-- `ensure_literal_complex` -/
def ensureLiteralComplex (e : Ast) : Bool :=
  match e with
  | .node .BinOp [left, op, right] _ =>
    let opOk := match op with
      | .node .Add _ _ | .node .Sub _ _ => true
      | _ => false
    let leftOk := match left with
      | .node .Constant _ _ => ensureLiteralNumber left true false
      | .node .UnaryOp _ _ => ensureLiteralNegative left true false
      | _ => false
    let rightOk := match right with
      | .node .Constant _ _ => ensureLiteralNumber right false true
      | _ => false
    opOk && leftOk && rightOk
  | _ => false

/-- `validate_capture` -/
def validateCapture (name : Ast) : V :=
  match name with
  | .ident [95] => verr "can't capture name '_' in patterns"
  | _ => validateName name

/-- `_validate_nonempty_seq` -/
def validateNonemptySeq (s : Ast) (what owner : String) : V :=
  if seqLen s != 0 then ok1 else verr s!"empty {what} on {owner}"

/-- `!x` for an optional pointer. -/
@[inline] def isNull : Ast → Bool
  | .null => true
  | _ => false

mutual
  /-- `validate_comprehension`, `Python/ast.c:72-87`. -/
  def validateComprehension : Nat → Ast → V
    | 0, _ => .error .modelFuel
    | f + 1, gens =>
      if seqLen gens == 0 then verr "comprehension with no generators" else
      validateComps f (seqL gens)

  def validateComps : Nat → List Ast → V
    | 0, _ => .error .modelFuel
    | _ + 1, [] => ok1
    | f + 1, .node _ [target, iter, ifs, _] _ :: rest =>
      (validateExpr f target .Store).and fun _ =>
      (validateExpr f iter .Load).and fun _ =>
      (validateExprs f (seqL ifs) .Load false).and fun _ =>
      validateComps f rest
    | f + 1, _ :: rest => validateComps f rest

  /-- `validate_keywords` -/
  def validateKeywords : Nat → List Ast → V
    | 0, _ => .error .modelFuel
    | _ + 1, [] => ok1
    | f + 1, .node _ [_, value] _ :: rest =>
      (validateExpr f value .Load).and fun _ => validateKeywords f rest
    | f + 1, _ :: rest => validateKeywords f rest

  /-- `validate_args` -/
  def validateArgs : Nat → List Ast → V
    | 0, _ => .error .modelFuel
    | _ + 1, [] => ok1
    | f + 1, .node _ [_, annotation, _] l :: rest =>
      (validatePositions l).and fun _ =>
      (if isNull annotation then ok1 else validateExpr f annotation .Load).and fun _ =>
      validateArgs f rest
    | f + 1, _ :: rest => validateArgs f rest

  /-- `arg->annotation` of an optional `arg`. -/
  def validateOptArgAnnotation : Nat → Ast → V
    | 0, _ => .error .modelFuel
    | f + 1, .node _ [_, annotation, _] _ =>
      if isNull annotation then ok1 else validateExpr f annotation .Load
    | _ + 1, _ => ok1

  /-- `validate_arguments`, `Python/ast.c:128-154`. -/
  def validateArguments : Nat → Ast → V
    | 0, _ => .error .modelFuel
    | f + 1, .node _ [posonly, args, vararg, kwonly, kwDefaults, kwarg, defaults] _ =>
      (validateArgs f (seqL posonly)).and fun _ =>
      (validateArgs f (seqL args)).and fun _ =>
      (validateOptArgAnnotation f vararg).and fun _ =>
      (validateArgs f (seqL kwonly)).and fun _ =>
      (validateOptArgAnnotation f kwarg).and fun _ =>
      if seqLen defaults > seqLen posonly + seqLen args then
        verr "more positional defaults than args on arguments"
      else if seqLen kwDefaults != seqLen kwonly then
        verr "length of kwonlyargs is not the same as kw_defaults on arguments"
      else
        (validateExprs f (seqL defaults) .Load false).and fun _ =>
        validateExprs f (seqL kwDefaults) .Load true
    | _ + 1, _ => ok1

  /-- `validate_expr`, `Python/ast.c:210-410`. -/
  def validateExpr : Nat → Ast → Ctor → V
    | 0, _, _ => .error .modelFuel
    | f + 1, exp, ctx =>
      match exp with
      | .node c fs l =>
        (validatePositions l).and fun _ =>
        -- First check expression context.
        let actual : Except V (Option Ctor) :=
          match c, fs with
          | .Attribute, [_, _, x] => .ok (some (ctxOfAst x))
          | .Subscript, [_, _, x] => .ok (some (ctxOfAst x))
          | .Starred, [_, x] => .ok (some (ctxOfAst x))
          | .Name, [id, x] =>
            match validateName id with
            | .ok () => .ok (some (ctxOfAst x))
            | e => .error e
          | .List, [_, x] => .ok (some (ctxOfAst x))
          | .Tuple, [_, x] => .ok (some (ctxOfAst x))
          | _, _ =>
            if ctx != .Load then
              .error (verr s!"expression which can't be assigned to in {ctxName ctx} context")
            else .ok none
        match actual with
        | .error e => e
        | .ok a =>
          match a with
          | some x =>
            if x != ctx then
              verr s!"expression must have {ctxName ctx} context but has {ctxName x} instead"
            else validateExprBody f c fs ctx
          | none => validateExprBody f c fs ctx
      | _ => ok1

  /-- The second switch of `validate_expr`. -/
  def validateExprBody : Nat → Ctor → List Ast → Ctor → V
    | 0, _, _, _ => .error .modelFuel
    | f + 1, c, fs, ctx =>
      match c, fs with
      | .BoolOp, [_, values] =>
        if seqLen values < 2 then verr "BoolOp with less than 2 values"
        else validateExprs f (seqL values) .Load false
      | .BinOp, [left, _, right] =>
        (validateExpr f left .Load).and fun _ => validateExpr f right .Load
      | .UnaryOp, [_, operand] => validateExpr f operand .Load
      | .Lambda, [args, body] =>
        (validateArguments f args).and fun _ => validateExpr f body .Load
      | .IfExp, [t, b, o] =>
        (validateExpr f t .Load).and fun _ =>
        (validateExpr f b .Load).and fun _ => validateExpr f o .Load
      | .Dict, [keys, values] =>
        if seqLen keys != seqLen values then
          verr "Dict doesn't have the same number of keys as values"
        else
          (validateExprs f (seqL keys) .Load true).and fun _ =>
          validateExprs f (seqL values) .Load false
      | .Set, [elts] => validateExprs f (seqL elts) .Load false
      | .ListComp, [elt, gens] | .SetComp, [elt, gens] | .GeneratorExp, [elt, gens] =>
        (validateComprehension f gens).and fun _ => validateExpr f elt .Load
      | .DictComp, [key, value, gens] =>
        (validateComprehension f gens).and fun _ =>
        (validateExpr f key .Load).and fun _ => validateExpr f value .Load
      | .Yield, [v] => if isNull v then ok1 else validateExpr f v .Load
      | .YieldFrom, [v] | .Await, [v] => validateExpr f v .Load
      | .Compare, [left, ops, comparators] =>
        if seqLen comparators == 0 then verr "Compare with no comparators"
        else if seqLen comparators != seqLen ops then
          verr "Compare has a different number of comparators and operands"
        else
          (validateExprs f (seqL comparators) .Load false).and fun _ =>
          validateExpr f left .Load
      | .Call, [func, args, keywords] =>
        (validateExpr f func .Load).and fun _ =>
        (validateExprs f (seqL args) .Load false).and fun _ =>
        validateKeywords f (seqL keywords)
      | .Constant, _ => ok1
      | .JoinedStr, [v] | .TemplateStr, [v] => validateExprs f (seqL v) .Load false
      | .FormattedValue, [v, _, spec] =>
        (validateExpr f v .Load).and fun _ =>
        if isNull spec then ok1 else validateExpr f spec .Load
      | .Interpolation, [v, _, _, spec] =>
        (validateExpr f v .Load).and fun _ =>
        if isNull spec then ok1 else validateExpr f spec .Load
      | .Attribute, [v, _, _] => validateExpr f v .Load
      | .Subscript, [v, s, _] =>
        (validateExpr f s .Load).and fun _ => validateExpr f v .Load
      | .Starred, [v, _] => validateExpr f v ctx
      | .Slice, [a, b, s] =>
        (if isNull a then ok1 else validateExpr f a .Load).and fun _ =>
        (if isNull b then ok1 else validateExpr f b .Load).and fun _ =>
        if isNull s then ok1 else validateExpr f s .Load
      | .List, [e, _] | .Tuple, [e, _] => validateExprs f (seqL e) ctx false
      | .NamedExpr, [target, value] =>
        match target with
        | .node .Name _ _ => validateExpr f value .Load
        | _ => terr "NamedExpr target must be a Name"
      | .Name, _ => ok1
      | _, _ => ok1

  /-- `validate_exprs` -/
  def validateExprs : Nat → List Ast → Ctor → Bool → V
    | 0, _, _, _ => .error .modelFuel
    | _ + 1, [], _, _ => ok1
    | f + 1, e :: rest, ctx, nullOk =>
      if isNull e then
        if nullOk then validateExprs f rest ctx nullOk
        else verr "None disallowed in expression list"
      else (validateExpr f e ctx).and fun _ => validateExprs f rest ctx nullOk

  /-- `validate_pattern_match_value`, `Python/ast.c:484-536`. -/
  def validateMatchValue : Nat → Ast → V
    | 0, _ => .error .modelFuel
    | f + 1, exp =>
      (validateExpr f exp .Load).and fun _ =>
      let bad := verr "patterns may only match literals and attribute lookups"
      match exp with
      | .node .Constant (.const v :: _) _ =>
        match v with
        | .int _ | .float _ | .bytes _ | .complex _ _ | .str _ => ok1
        | _ => verr "unexpected constant inside of a literal pattern"
      | .node .Attribute _ _ => ok1
      | .node .UnaryOp _ _ => if ensureLiteralNegative exp true true then ok1 else bad
      | .node .BinOp _ _ => if ensureLiteralComplex exp then ok1 else bad
      | .node .JoinedStr _ _ | .node .TemplateStr _ _ => ok1
      | _ => bad

  /-- The key loop of `MatchMapping` in `validate_pattern`. -/
  def validateMappingKeys : Nat → List Ast → V
    | 0, _ => .error .modelFuel
    | _ + 1, [] => ok1
    | f + 1, key :: rest =>
      match key with
      | .node .Constant (.const .none :: _) _ | .node .Constant (.const .true_ :: _) _
      | .node .Constant (.const .false_ :: _) _ => validateMappingKeys f rest
      | _ => (validateMatchValue f key).and fun _ => validateMappingKeys f rest

  /-- `validate_pattern`, `Python/ast.c:550-699`. -/
  def validatePattern : Nat → Ast → Bool → V
    | 0, _, _ => .error .modelFuel
    | f + 1, p, starOk =>
      match p with
      | .null => nullDeref
      | .node c fs l =>
        (validatePositions l).and fun _ =>
        match c, fs with
        | .MatchValue, [v] => validateMatchValue f v
        | .MatchSingleton, [v] =>
          match v with
          | .const .none | .const .true_ | .const .false_ => ok1
          | _ => verr "MatchSingleton can only contain True, False and None"
        | .MatchSequence, [ps] => validatePatterns f (seqL ps) true
        | .MatchMapping, [keys, ps, rest] =>
          if seqLen keys != seqLen ps then
            verr "MatchMapping doesn't have the same number of keys as patterns"
          else
            (if isNull rest then ok1 else validateCapture rest).and fun _ =>
            (validateMappingKeys f (seqL keys)).and fun _ =>
            validatePatterns f (seqL ps) false
        | .MatchClass, [cls, ps, kwdAttrs, kwdPs] =>
          if seqLen kwdAttrs != seqLen kwdPs then
            verr "MatchClass doesn't have the same number of keyword attributes as patterns"
          else
            (validateExpr f cls .Load).and fun _ =>
            (classRoot f cls).and fun _ =>
            ((seqL kwdAttrs).foldl (fun acc n => acc.and fun _ => validateName n) ok1).and fun _ =>
            (validatePatterns f (seqL ps) false).and fun _ =>
            validatePatterns f (seqL kwdPs) false
        | .MatchStar, [name] =>
          if !starOk then verr "can't use MatchStar here"
          else if isNull name then ok1 else validateCapture name
        | .MatchAs, [pat, name] =>
          (if isNull name then ok1 else validateCapture name).and fun _ =>
          if isNull pat then ok1
          else if isNull name then verr "MatchAs must specify a target name if a pattern is given"
          else validatePattern f pat false
        | .MatchOr, [ps] =>
          if seqLen ps < 2 then verr "MatchOr requires at least 2 patterns"
          else validatePatterns f (seqL ps) false
        | _, _ => ok1
      | _ => ok1

  /-- The `while (1)` over `cls` in `MatchClass`. -/
  def classRoot : Nat → Ast → V
    | 0, _ => .error .modelFuel
    | f + 1, cls =>
      match cls with
      | .node .Name _ _ => ok1
      | .node .Attribute (v :: _) _ => classRoot f v
      | _ => verr "MatchClass cls field can only contain Name or Attribute nodes."

  /-- `validate_patterns` -/
  def validatePatterns : Nat → List Ast → Bool → V
    | 0, _, _ => .error .modelFuel
    | _ + 1, [], _ => ok1
    | f + 1, p :: rest, starOk =>
      (validatePattern f p starOk).and fun _ => validatePatterns f rest starOk

  /-- `validate_assignlist` -/
  def validateAssignlist : Nat → Ast → Ctor → V
    | 0, _, _ => .error .modelFuel
    | f + 1, targets, ctx =>
      (validateNonemptySeq targets "targets" (if ctx == .Del then "Delete" else "Assign")).and
        fun _ => validateExprs f (seqL targets) ctx false

  /-- `validate_body` -/
  def validateBody : Nat → Ast → String → V
    | 0, _, _ => .error .modelFuel
    | f + 1, body, owner =>
      (validateNonemptySeq body "body" owner).and fun _ => validateStmts f (seqL body)

  /-- The `with` item loop. -/
  def validateWithItems : Nat → List Ast → V
    | 0, _ => .error .modelFuel
    | _ + 1, [] => ok1
    | f + 1, .node _ [ctxExpr, vars] _ :: rest =>
      (validateExpr f ctxExpr .Load).and fun _ =>
      (if isNull vars then ok1 else validateExpr f vars .Store).and fun _ =>
      validateWithItems f rest
    | f + 1, _ :: rest => validateWithItems f rest

  /-- The `match` case loop. -/
  def validateCases : Nat → List Ast → V
    | 0, _ => .error .modelFuel
    | _ + 1, [] => ok1
    | f + 1, .node _ [pat, guard, body] _ :: rest =>
      (validatePattern f pat false).and fun _ =>
      (if isNull guard then ok1 else validateExpr f guard .Load).and fun _ =>
      (validateBody f body "match_case").and fun _ =>
      validateCases f rest
    | f + 1, _ :: rest => validateCases f rest

  /-- The handler loop; only `Try` checks handler positions (`Python/ast.c`, `Try_kind`
  against `TryStar_kind`). -/
  def validateHandlers : Nat → List Ast → Bool → V
    | 0, _, _ => .error .modelFuel
    | _ + 1, [], _ => ok1
    | _ + 1, .null :: _, _ => nullDeref
    | f + 1, .node _ [ty, _, body] l :: rest, positions =>
      (if positions then validatePositions l else ok1).and fun _ =>
      (if isNull ty then ok1 else validateExpr f ty .Load).and fun _ =>
      (validateBody f body "ExceptHandler").and fun _ =>
      validateHandlers f rest positions
    | f + 1, _ :: rest, positions => validateHandlers f rest positions

  /-- The shared body of `Try_kind`/`TryStar_kind`. -/
  def validateTry : Nat → String → Ast → Ast → Ast → Ast → Bool → V
    | 0, _, _, _, _, _, _ => .error .modelFuel
    | f + 1, name, body, handlers, orelse, finalbody, positions =>
      (validateBody f body name).and fun _ =>
      if seqLen handlers == 0 && seqLen finalbody == 0 then
        verr s!"{name} has neither except handlers nor finalbody"
      else if seqLen handlers == 0 && seqLen orelse != 0 then
        verr s!"{name} has orelse but no except handlers"
      else
        (validateHandlers f (seqL handlers) positions).and fun _ =>
        (validateStmts f (seqL finalbody)).and fun _ =>
        validateStmts f (seqL orelse)

  /-- `validate_typeparam` -/
  def validateTypeParam : Nat → Ast → V
    | 0, _ => .error .modelFuel
    | f + 1, tp =>
      match tp with
      | .node c fs l =>
        (validatePositions l).and fun _ =>
        match c, fs with
        | .TypeVar, [name, bound, dflt] =>
          (validateName name).and fun _ =>
          (if isNull bound then ok1 else validateExpr f bound .Load).and fun _ =>
          if isNull dflt then ok1 else validateExpr f dflt .Load
        | .ParamSpec, [name, dflt] | .TypeVarTuple, [name, dflt] =>
          (validateName name).and fun _ =>
          if isNull dflt then ok1 else validateExpr f dflt .Load
        | _, _ => ok1
      | _ => ok1

  /-- `validate_type_params` -/
  def validateTypeParams : Nat → List Ast → V
    | 0, _ => .error .modelFuel
    | _ + 1, [] => ok1
    | f + 1, tp :: rest =>
      (if isNull tp then ok1 else validateTypeParam f tp).and fun _ =>
      validateTypeParams f rest

  /-- `validate_stmt`, `Python/ast.c:727-951`. -/
  def validateStmt : Nat → Ast → V
    | 0, _ => .error .modelFuel
    | f + 1, stmt =>
      match stmt with
      | .node c fs l =>
        (validatePositions l).and fun _ =>
        match c, fs with
        | .FunctionDef, [_, args, body, decs, returns, _, tps]
        | .AsyncFunctionDef, [_, args, body, decs, returns, _, tps] =>
          (validateBody f body (if c == .FunctionDef then "FunctionDef" else "AsyncFunctionDef")).and
            fun _ =>
          (validateTypeParams f (seqL tps)).and fun _ =>
          (validateArguments f args).and fun _ =>
          (validateExprs f (seqL decs) .Load false).and fun _ =>
          if isNull returns then ok1 else validateExpr f returns .Load
        | .ClassDef, [_, bases, keywords, body, decs, tps] =>
          (validateBody f body "ClassDef").and fun _ =>
          (validateTypeParams f (seqL tps)).and fun _ =>
          (validateExprs f (seqL bases) .Load false).and fun _ =>
          (validateKeywords f (seqL keywords)).and fun _ =>
          validateExprs f (seqL decs) .Load false
        | .Return, [v] => if isNull v then ok1 else validateExpr f v .Load
        | .Delete, [t] => validateAssignlist f t .Del
        | .Assign, [t, v, _] =>
          (validateAssignlist f t .Store).and fun _ => validateExpr f v .Load
        | .AugAssign, [t, _, v] =>
          (validateExpr f t .Store).and fun _ => validateExpr f v .Load
        | .AnnAssign, [t, ann, v, simple] =>
          let isName := match t with
            | .node .Name _ _ => true
            | _ => false
          let isSimple := match simple with
            | .int 0 => false
            | _ => true
          if !isName && isSimple then terr "AnnAssign with simple non-Name target" else
          (validateExpr f t .Store).and fun _ =>
          (if isNull v then ok1 else validateExpr f v .Load).and fun _ =>
          validateExpr f ann .Load
        | .TypeAlias, [name, tps, v] =>
          match name with
          | .node .Name _ _ =>
            (validateExpr f name .Store).and fun _ =>
            (validateTypeParams f (seqL tps)).and fun _ =>
            validateExpr f v .Load
          | _ => terr "TypeAlias with non-Name name"
        | .For, [t, it, body, orelse, _] | .AsyncFor, [t, it, body, orelse, _] =>
          (validateExpr f t .Store).and fun _ =>
          (validateExpr f it .Load).and fun _ =>
          (validateBody f body (if c == .For then "For" else "AsyncFor")).and fun _ =>
          validateStmts f (seqL orelse)
        | .While, [t, body, orelse] | .If, [t, body, orelse] =>
          (validateExpr f t .Load).and fun _ =>
          (validateBody f body (if c == .While then "While" else "If")).and fun _ =>
          validateStmts f (seqL orelse)
        | .With, [items, body, _] | .AsyncWith, [items, body, _] =>
          let n := if c == .With then "With" else "AsyncWith"
          (validateNonemptySeq items "items" n).and fun _ =>
          (validateWithItems f (seqL items)).and fun _ =>
          validateBody f body n
        | .Match, [subject, cases] =>
          (validateExpr f subject .Load).and fun _ =>
          (validateNonemptySeq cases "cases" "Match").and fun _ =>
          validateCases f (seqL cases)
        | .Raise, [exc, cause] =>
          if !isNull exc then
            (validateExpr f exc .Load).and fun _ =>
            if isNull cause then ok1 else validateExpr f cause .Load
          else if !isNull cause then verr "Raise with cause but no exception"
          else ok1
        | .Try, [b, h, o, fb] => validateTry f "Try" b h o fb true
        | .TryStar, [b, h, o, fb] => validateTry f "TryStar" b h o fb false
        | .Assert, [t, m] =>
          (validateExpr f t .Load).and fun _ =>
          if isNull m then ok1 else validateExpr f m .Load
        | .Import, [names] => validateNonemptySeq names "names" "Import"
        | .ImportFrom, [_, names, level] =>
          let neg := match level with
            | .int v => decide (v < 0)
            | _ => false
          if neg then verr "Negative ImportFrom level"
          else validateNonemptySeq names "names" "ImportFrom"
        | .Global, [names] => validateNonemptySeq names "names" "Global"
        | .Nonlocal, [names] => validateNonemptySeq names "names" "Nonlocal"
        | .Expr, [v] => validateExpr f v .Load
        | _, _ => ok1
      | _ => ok1

  /-- `validate_stmts` -/
  def validateStmts : Nat → List Ast → V
    | 0, _ => .error .modelFuel
    | _ + 1, [] => ok1
    | f + 1, s :: rest =>
      if isNull s then verr "None disallowed in statement list"
      else (validateStmt f s).and fun _ => validateStmts f rest
end

/-- Node count, a bound for all the fuel above. -/
def astSize : Ast → Nat
  | .node _ fs _ => 1 + sizeList fs
  | .seq xs => 1 + sizeList xs
  | _ => 1
where
  sizeList : List Ast → Nat
    | [] => 0
    | x :: xs => astSize x + sizeList xs

/-- `_PyAST_Validate`, `Python/ast.c:1047-1074`. -/
def validate (m : Ast) : V :=
  let f := 8 * astSize m + 64
  match m with
  | .node .Module (body :: _) _ | .node .Interactive (body :: _) _ =>
    validateStmts f (seqL body)
  | .node .Expression [body] _ => validateExpr f body .Load
  | .node .FunctionType [args, returns] _ =>
    (validateExprs f (seqL args) .Load false).and fun _ => validateExpr f returns .Load
  | _ => .error (.named "SystemError" "impossible module node")

end PyLean.PyGrammar.Check
