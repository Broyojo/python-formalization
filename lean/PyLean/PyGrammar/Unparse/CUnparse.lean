import PyLean.PyGrammar.Unparse.Python

/-!
`Python/ast_unparse.c`: the C twin of `Lib/_ast_unparse.py`, used for annotations under
`from __future__ import annotations`. Each `append_*` is a function from the node to the text
it writes, so a failing `-1` return is the `Except`.
-/

namespace PyLean.PyGrammar.Unparse

open PyLean Lexer

/-- Priority levels of `Python/ast_unparse.c`. -/
def prTuple : Nat := 0
def prTest : Nat := 1
def prOr : Nat := 2
def prAnd : Nat := 3
def prNot : Nat := 4
def prCmp : Nat := 5
def prExpr : Nat := 6
def prBor : Nat := 6
def prBxor : Nat := 7
def prBand : Nat := 8
def prShift : Nat := 9
def prArith : Nat := 10
def prTerm : Nat := 11
def prFactor : Nat := 12
def prPower : Nat := 13
def prAwait : Nat := 14
def prAtom : Nat := 15

/-- A failing append. -/
abbrev CU := Except PyExc (List Nat)

/-- `APPEND_STR_IF(level > pr, "(")` around a body. -/
@[inline] def parenIf (c : Bool) (body : List Nat) : List Nat :=
  if c then 40 :: body ++ [41] else body

/-- `append_repr`, with the replacement of `inf` for floats that are infinite and for every
complex. -/
def appendRepr : PyConst → CU
  | .float b =>
    .ok (if b &&& 0x7FFFFFFFFFFFFFFF == 0x7FF0000000000000 then
      constRepr.replaceInf (floatRepr b) else floatRepr b)
  | .complex r i => .ok (replaceInfOnly (complexRepr r i))
  | c => constRepr c
where
  /-- `PyUnicode_Replace(repr, "inf", "1e309")`, `nan` left alone. -/
  replaceInfOnly : List Nat → List Nat
    | 105 :: 110 :: 102 :: r => cp "1e309" ++ replaceInfOnly r
    | c :: r => c :: replaceInfOnly r
    | [] => []

/-- `escape_braces` -/
def escapeBraces (s : List Nat) : List Nat :=
  replaceCp (replaceCp s 123 [123, 123]) 125 [125, 125]

/-- `append_interpolation_str` -/
def appendInterpolationStr (s : List Nat) : List Nat :=
  (if s.head? == some 123 then cp "{ " else cp "{") ++ s

/-- `append_interpolation_conversion` -/
def appendConversion (conv : Ast) : CU :=
  match conv with
  | .int v =>
    if v < 0 then .ok []
    else if v == 97 then .ok (cp "!a")
    else if v == 114 then .ok (cp "!r")
    else if v == 115 then .ok (cp "!s")
    else .error (.named "SystemError" "unknown f-value conversion kind")
  | _ => .ok []

/-- Join with `", "` as `APPEND_STR_IF(i > 0, ", ")` does. -/
def joinComma (xs : List (List Nat)) : List Nat :=
  match xs with
  | [] => []
  | x :: r => x ++ r.flatMap (fun y => 44 :: 32 :: y)

/-- `cmpop` text with its spaces. -/
def cmpOp (o : Ast) : Except PyExc (List Nat) :=
  match o with
  | .node c _ _ =>
    match cmpStr c with
    | "" => .error (.named "SystemError" "unexpected comparison kind")
    | s => .ok (cp (" " ++ s ++ " "))
  | _ => .error (.named "SystemError" "unexpected comparison kind")

/-- `append_ast_constant` on the items of a tuple. -/
def appendConstantTuple : List PyConst → Except PyExc (List (List Nat))
  | [] => .ok []
  | c :: rest => do
    let a ← appendRepr c
    return a :: (← appendConstantTuple rest)

mutual
  /-- `append_ast_expr`, `Python/ast_unparse.c`. -/
  def appendExpr : Nat → Ast → Nat → CU
    | 0, _, _ => .error .modelFuel
    | f + 1, e, level =>
      match e with
      | .node c fs _ => appendNode f c fs level
      | _ => .ok []

  /-- `APPEND_EXPR` over a list at one level, joined by `", "`. -/
  def appendList : Nat → List Ast → Nat → Except PyExc (List (List Nat))
    | 0, _, _ => .error .modelFuel
    | _ + 1, [], _ => .ok []
    | f + 1, x :: xs, level => do
      let a ← appendExpr f x level
      return a :: (← appendList f xs level)

  /-- `append_ast_comprehensions` -/
  def appendComps : Nat → List Ast → CU
    | 0, _ => .error .modelFuel
    | _ + 1, [] => .ok []
    | f + 1, .node _ [t, it, ifs, isAsync] _ :: rest => do
      let tt ← appendExpr f t prTuple
      let ii ← appendExpr f it (prTest + 1)
      let cs ← appendList f (seqU ifs) (prTest + 1)
      let r ← appendComps f rest
      return cp (if present isAsync then " async for " else " for ") ++ tt ++ cp " in " ++ ii
        ++ cs.flatMap (fun c => cp " if " ++ c) ++ r
    | f + 1, _ :: rest => appendComps f rest

  /-- `append_ast_arg` -/
  def appendArg : Nat → Ast → CU
    | 0, _ => .error .modelFuel
    | f + 1, .node _ [a, ann, _] _ => do
      if present ann then
        return idOf a ++ cp ": " ++ (← appendExpr f ann prTest)
      return idOf a
    | _ + 1, _ => .ok []

  /-- The positional loop of `append_ast_args`. -/
  def appendPos : Nat → List Ast → Nat → Nat → Nat → List Ast → Except PyExc (List (List Nat))
    | 0, _, _, _, _, _ => .error .modelFuel
    | _ + 1, [], _, _, _, _ => .ok []
    | f + 1, a :: rest, i, npos, nall, defaults => do
      let t ← appendArg f a
      let di : Int := (i : Int) - nall + defaults.length
      let d ← if di ≥ 0 then do
          pure (61 :: (← appendExpr f (defaults.getD di.toNat .null) prTest))
        else pure []
      let s := if npos != 0 && i + 1 == npos then cp ", /" else []
      return (t ++ d ++ s) :: (← appendPos f rest (i + 1) npos nall defaults)

  /-- The keyword-only loop of `append_ast_args`. -/
  def appendKw : Nat → List Ast → Nat → Nat → List Ast → Except PyExc (List (List Nat))
    | 0, _, _, _, _ => .error .modelFuel
    | _ + 1, [], _, _, _ => .ok []
    | f + 1, a :: rest, i, n, defaults => do
      let t ← appendArg f a
      let di : Int := (i : Int) - n + defaults.length
      let d ← if di ≥ 0 && present (defaults.getD di.toNat .null) then do
          pure (61 :: (← appendExpr f (defaults.getD di.toNat .null) prTest))
        else pure []
      return (t ++ d) :: (← appendKw f rest (i + 1) n defaults)

  /-- `append_ast_args` -/
  def appendArgs : Nat → List Ast → CU
    | 0, _ => .error .modelFuel
    | f + 1, [posonly, args, vararg, kwonly, kwDefaults, kwarg, defaults] => do
      let all := seqU posonly ++ seqU args
      let pos ← appendPos f all 0 (seqU posonly).length all.length (seqU defaults)
      let star : List (List Nat) ←
        if present vararg || present kwonly then do
          if present vararg then pure [42 :: (← appendArg f vararg)] else pure [[42]]
        else pure []
      let kw ← appendKw f (seqU kwonly) 0 (seqU kwonly).length (seqU kwDefaults)
      let kwa : List (List Nat) ←
        if present kwarg then do pure [cp "**" ++ (← appendArg f kwarg)] else pure []
      return joinComma (pos ++ star ++ kw ++ kwa)
    | _ + 1, _ => .ok []

  /-- `append_ast_keyword` -/
  def appendKeyword : Nat → Ast → CU
    | 0, _ => .error .modelFuel
    | f + 1, .node _ [a, v] _ => do
      let h := match a with
        | .null => cp "**"
        | _ => idOf a ++ [61]
      return h ++ (← appendExpr f v prTest)
    | _ + 1, _ => .ok []

  def appendKeywords : Nat → List Ast → Except PyExc (List (List Nat))
    | 0, _ => .error .modelFuel
    | _ + 1, [] => .ok []
    | f + 1, k :: rest => do
      let a ← appendKeyword f k
      return a :: (← appendKeywords f rest)

  /-- `append_fstring_element` -/
  def appendElement : Nat → Ast → Bool → CU
    | 0, _, _ => .error .modelFuel
    | f + 1, e, isSpec =>
      match e with
      | .node .Constant (.const (.str s) :: _) _ => .ok (escapeBraces s)
      | .node .JoinedStr [v] _ => appendJoined f v isSpec
      | .node .TemplateStr [v] _ => do
        return 116 :: (← appendRepr (.str (← buildBody f (seqU v) false)))
      | .node .FormattedValue [v, conv, spec] _ => do
        let tv ← appendExpr f v (prTest + 1)
        let c ← appendConversion conv
        let s ← appendSpec f spec
        return appendInterpolationStr tv ++ c ++ s ++ [125]
      | .node .Interpolation [_, .const (.str s), conv, spec] _ => do
        let c ← appendConversion conv
        let sp ← appendSpec f spec
        return appendInterpolationStr s ++ c ++ sp ++ [125]
      | _ => .error (.named "SystemError" "unknown expression kind inside f-string or t-string")

  /-- `append_interpolation_format_spec` -/
  def appendSpec : Nat → Ast → CU
    | 0, _ => .error .modelFuel
    | f + 1, spec =>
      match spec with
      | .null => .ok []
      | _ => do return 58 :: (← appendElement f spec true)

  /-- `build_ftstring_body` -/
  def buildBody : Nat → List Ast → Bool → CU
    | 0, _, _ => .error .modelFuel
    | _ + 1, [], _ => .ok []
    | f + 1, x :: xs, isSpec => do
      let a ← appendElement f x isSpec
      return a ++ (← buildBody f xs isSpec)

  /-- `append_joinedstr` -/
  def appendJoined : Nat → Ast → Bool → CU
    | 0, _, _ => .error .modelFuel
    | f + 1, values, isSpec => do
      let body ← buildBody f (seqU values) isSpec
      if isSpec then return body
      return 102 :: (← appendRepr (.str body))

  /-- The dict loop. -/
  def appendDict : Nat → List (Ast × Ast) → Except PyExc (List (List Nat))
    | 0, _ => .error .modelFuel
    | _ + 1, [] => .ok []
    | f + 1, (k, v) :: rest => do
      let a ← match k with
        | .null => do pure (cp "**" ++ (← appendExpr f v prExpr))
        | _ => do pure ((← appendExpr f k prTest) ++ cp ": " ++ (← appendExpr f v prTest))
      return a :: (← appendDict f rest)

  /-- The compare loop. -/
  def appendCmp : Nat → List Ast → List Ast → CU
    | 0, _, _ => .error .modelFuel
    | f + 1, o :: os, e :: es => do
      let op ← cmpOp o
      let t ← appendExpr f e (prCmp + 1)
      return op ++ t ++ (← appendCmp f os es)
    | _ + 1, _, _ => .ok []

  /-- The cases of `append_ast_expr`. -/
  def appendNode : Nat → Ctor → List Ast → Nat → CU
    | 0, _, _, _ => .error .modelFuel
    | f + 1, c, fs, level =>
      match c, fs with
      | .BoolOp, [.node o _ _, values] => do
        let (op, pr) : String × Nat := if o == .And then (" and ", prAnd) else (" or ", prOr)
        let xs ← appendList f (seqU values) (pr + 1)
        let body := match xs with
          | [] => []
          | x :: r => x ++ r.flatMap (fun y => cp op ++ y)
        return parenIf (level > pr) body
      | .BinOp, [l, .node o _ _, r] => do
        if binopStr o == "" then throw (.named "SystemError" "unknown binary operator")
        let pr := if o == .Pow then prPower else
          match o with
          | .Add | .Sub => prArith
          | .Mult | .MatMult | .Div | .Mod | .FloorDiv => prTerm
          | .LShift | .RShift => prShift
          | .BitOr => prBor
          | .BitXor => prBxor
          | _ => prBand
        let rassoc := o == .Pow
        let a ← appendExpr f l (if rassoc then pr + 1 else pr)
        let b ← appendExpr f r (if rassoc then pr else pr + 1)
        return parenIf (level > pr) (a ++ cp (" " ++ binopStr o ++ " ") ++ b)
      | .UnaryOp, [.node o _ _, v] => do
        let (op, pr) : String × Nat := match o with
          | .Invert => ("~", prFactor)
          | .Not => ("not ", prNot)
          | .UAdd => ("+", prFactor)
          | _ => ("-", prFactor)
        return parenIf (level > pr) (cp op ++ (← appendExpr f v pr))
      | .Lambda, [.node _ afs _, body] => do
        let n := (seqU (afs.getD 1 .null)).length + (seqU (afs.getD 0 .null)).length
        let a ← appendArgs f afs
        let b ← appendExpr f body prTest
        return parenIf (level > prTest) (cp (if n != 0 then "lambda " else "lambda") ++ a ++ cp ": " ++ b)
      | .IfExp, [t, b, o] => do
        let x ← appendExpr f b (prTest + 1)
        let y ← appendExpr f t (prTest + 1)
        let z ← appendExpr f o prTest
        return parenIf (level > prTest) (x ++ cp " if " ++ y ++ cp " else " ++ z)
      | .Dict, [keys, values] => do
        return 123 :: joinComma (← appendDict f ((seqU keys).zip (seqU values))) ++ [125]
      | .Set, [elts] => do
        return 123 :: joinComma (← appendList f (seqU elts) prTest) ++ [125]
      | .GeneratorExp, [e, g] => do
        return 40 :: (← appendExpr f e prTest) ++ (← appendComps f (seqU g)) ++ [41]
      | .ListComp, [e, g] => do
        return 91 :: (← appendExpr f e prTest) ++ (← appendComps f (seqU g)) ++ [93]
      | .SetComp, [e, g] => do
        return 123 :: (← appendExpr f e prTest) ++ (← appendComps f (seqU g)) ++ [125]
      | .DictComp, [k, v, g] => do
        return 123 :: (← appendExpr f k prTest) ++ cp ": " ++ (← appendExpr f v prTest)
          ++ (← appendComps f (seqU g)) ++ [125]
      | .Yield, [v] =>
        if present v then do
          return cp "(yield " ++ (← appendExpr f v prTest) ++ [41]
        else .ok (cp "(yield)")
      | .YieldFrom, [v] => do return cp "(yield from " ++ (← appendExpr f v prTest) ++ [41]
      | .Await, [v] => do
        return parenIf (level > prAwait) (cp "await " ++ (← appendExpr f v prAtom))
      | .Compare, [l, ops, cs] => do
        let a ← appendExpr f l (prCmp + 1)
        let t ← appendCmp f (seqU ops) (seqU cs)
        return parenIf (level > prCmp) (a ++ t)
      | .Call, [func, args, keywords] => do
        let fn ← appendExpr f func prAtom
        match seqU args, seqU keywords with
        | [.node .GeneratorExp [e, g] _], [] =>
          return fn ++ 40 :: (← appendExpr f e prTest) ++ (← appendComps f (seqU g)) ++ [41]
        | a, k =>
          let xs ← appendList f a prTest
          let ks ← appendKeywords f k
          return fn ++ 40 :: joinComma (xs ++ ks) ++ [41]
      | .Constant, (.const v :: kind :: _) =>
        match v with
        | .ellipsis => .ok (cp "...")
        | .tuple xs => do
          let ts ← appendConstantTuple xs
          let k := match kind with
            | .str s => s
            | _ => []
          return k ++ 40 :: joinComma ts ++ (if xs.length == 1 then [44] else []) ++ [41]
        | _ => do
          let k := match kind with
            | .str s => s
            | _ => []
          return k ++ (← appendRepr v)
      | .JoinedStr, [v] => appendJoined f v false
      | .TemplateStr, _ | .FormattedValue, _ | .Interpolation, _ =>
        appendElement f (.node c fs none) false
      | .Attribute, [v, attr, _] => do
        let t ← appendExpr f v prAtom
        let isInt := match v with
          | .node .Constant (.const (.int _) :: _) _ => true
          | _ => false
        return t ++ cp (if isInt then " ." else ".") ++ idOf attr
      | .Subscript, [v, s, _] => do
        return (← appendExpr f v prAtom) ++ 91 :: (← appendExpr f s prTuple) ++ [93]
      | .Starred, [v, _] => do return 42 :: (← appendExpr f v prExpr)
      | .Slice, [lo, hi, st] => do
        let a ← if present lo then appendExpr f lo prTest else pure []
        let b ← if present hi then appendExpr f hi prTest else pure []
        let c' ← if present st then do pure (58 :: (← appendExpr f st prTest)) else pure []
        return a ++ 58 :: b ++ c'
      | .Name, [id, _] => .ok (idOf id)
      | .List, [elts, _] => do
        return 91 :: joinComma (← appendList f (seqU elts) prTest) ++ [93]
      | .Tuple, [elts, _] => do
        let xs ← appendList f (seqU elts) prTest
        match xs with
        | [] => return cp "()"
        | [x] => return parenIf (level > prTuple) (x ++ [44])
        | _ => return parenIf (level > prTuple) (joinComma xs)
      | .NamedExpr, [t, v] => do
        let a ← appendExpr f t prAtom
        let b ← appendExpr f v prAtom
        return parenIf (level > prTuple) (a ++ cp " := " ++ b)
      | _, _ => .error (.named "SystemError" "unknown expression kind")
end

/-- `_PyAST_ExprAsUnicode` -/
def exprAsUnicode (n : Nat) (e : Ast) : CU := appendExpr (unparseFuel n) e prTest

end PyLean.PyGrammar.Unparse
