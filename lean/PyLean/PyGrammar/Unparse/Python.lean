import PyLean.PyGrammar.Unparse.Repr
import PyLean.PyGrammar.Ast
import PyLean.Core

/-!
`Lib/_ast_unparse.py`, `class Unparser`, mirrored method by method over the generic `Ast`.

The one structural change: `self._precedences` is a dict keyed by node identity, set just
before a node is traversed. Here the precedence travels as the argument of `visit`, and the
default of `get_precedence` (`_Precedence.TEST`) is passed where the source sets nothing.
Trees from the parser never share a precedence-relevant node, so this is the same function.
-/

namespace PyLean.PyGrammar.Unparse

open PyLean Lexer

/-- `_Precedence`, `Lib/_ast_unparse.py:14-36`. -/
def pNamedExpr : Nat := 1
def pTuple : Nat := 2
def pYield : Nat := 3
def pTest : Nat := 4
def pOr : Nat := 5
def pAnd : Nat := 6
def pNot : Nat := 7
def pCmp : Nat := 8
def pExpr : Nat := 9
def pBor : Nat := 9
def pBxor : Nat := 10
def pBand : Nat := 11
def pShift : Nat := 12
def pArith : Nat := 13
def pTerm : Nat := 14
def pFactor : Nat := 15
def pPower : Nat := 16
def pAwait : Nat := 17
def pAtom : Nat := 18

/-- `_Precedence.next` -/
def pNext (p : Nat) : Nat := if p ≥ pAtom then p else p + 1

/-- Unparser state. `source` is `self._source`, newest part first. -/
structure US where
  source : List (List Nat) := []
  typeIgnores : List (Int × List Nat) := []
  indent : Nat := 0
  inTryStar : Bool := false
  inInteractive : Bool := false
  deriving Repr, Inhabited

/-- Methods of `Unparser` run here. -/
abbrev UM (α : Type) := EStateM PyExc US α

/-- `self.write(text)` -/
@[inline] def write (t : List Nat) : UM Unit := modify fun s => { s with source := t :: s.source }

/-- `self.write(literal)` -/
@[inline] def wr (t : String) : UM Unit := write (cp t)

/-- `self._source` joined. -/
def joined (parts : List (List Nat)) : List Nat := parts.reverse.flatten

/-- `interleave`, `Lib/_ast_unparse.py:62-72`. -/
def interleave {α : Type} (inter : UM Unit) (f : α → UM Unit) : List α → UM Unit
  | [] => pure ()
  | x :: xs => do
    f x
    let rec go : List α → UM Unit
      | [] => pure ()
      | y :: ys => do
        inter
        f y
        go ys
    go xs

/-- `items_view` -/
def itemsView {α : Type} (f : α → UM Unit) (items : List α) : UM Unit :=
  match items with
  | [x] => do
    f x
    wr ","
  | _ => interleave (wr ", ") f items

/-- `maybe_newline` -/
def maybeNewline : UM Unit := do
  if !(← get).source.isEmpty then wr "\n"

/-- `maybe_semicolon` -/
def maybeSemicolon : UM Unit := do
  if !(← get).source.isEmpty then wr "; "

/-- `fill`, `Lib/_ast_unparse.py:94-102`. -/
def fill (text : String := "") (allowSemicolon : Bool := true) : UM Unit := do
  let s ← get
  if s.inInteractive && s.indent == 0 && allowSemicolon then
    maybeSemicolon
    wr text
  else
    maybeNewline
    write ((List.replicate (4 * (← get).indent) 32) ++ cp text)

/-- `delimit_if` around an action. -/
@[inline] def delimitIf (a b : String) (c : Bool) (body : UM Unit) : UM Unit := do
  if c then wr a
  body
  if c then wr b

/-- `require_parens` -/
@[inline] def requireParens (precedence nodePrec : Nat) (body : UM Unit) : UM Unit :=
  delimitIf "(" ")" (nodePrec > precedence) body

/-- `block` without `extra`. -/
def block (extra : Option (List Nat)) (body : UM Unit) : UM Unit := do
  wr ":"
  match extra with
  | some e => write e
  | none => pure ()
  modify fun s => { s with indent := s.indent + 1 }
  body
  modify fun s => { s with indent := s.indent - 1 }

/-- Quotes: `_SINGLE_QUOTES`, `_MULTI_QUOTES`, `_ALL_QUOTES`. -/
def qS1 : List Nat := [39]
def qD1 : List Nat := [34]
def qD3 : List Nat := [34, 34, 34]
def qS3 : List Nat := [39, 39, 39]
def multiQuotes : List (List Nat) := [qD3, qS3]
def allQuotes : List (List Nat) := [qS1, qD1, qD3, qS3]

/-- `needle in hay` for strings. -/
def contains (hay needle : List Nat) : Bool :=
  let rec go : List Nat → Bool
    | [] => needle.isEmpty
    | h@(_ :: t) => needle.isPrefixOf h || go t
  go hay

/-- `_str_literal_helper`, `Lib/_ast_unparse.py:532-568`. -/
def strLiteralHelper (string : List Nat) (quoteTypes : List (List Nat)) (escapeSpecial : Bool) :
    List Nat × List (List Nat) :=
  let escapeChar (c : Nat) : List Nat :=
    if !escapeSpecial && (c == 10 || c == 9) then [c]
    else if c == 92 || !printable c then unicodeEscape c
    else [c]
  let escaped := string.flatMap escapeChar
  let possible := if escaped.contains 10 then quoteTypes.filter (multiQuotes.contains ·) else quoteTypes
  let possible := possible.filter (fun q => !contains escaped q)
  match possible with
  | [] =>
    let s := strRepr string
    let c := s.headD 0
    let quote := (quoteTypes.find? (fun q => q.contains c)).getD [c]
    (((s.drop 1).dropLast), [quote])
  | _ =>
    if escaped.isEmpty then (escaped, possible)
    else
      let last := escaped.getLastD 0
      -- `sort(key=lambda q: q[0] == escaped_string[-1])`, stable
      let sorted := possible.filter (fun q => q.headD 0 != last)
        ++ possible.filter (fun q => q.headD 0 == last)
      if (sorted.headD []).headD 0 == last then
        (escaped.dropLast ++ [92, last], sorted)
      else (escaped, sorted)

/-- `_write_str_avoiding_backslashes` -/
def writeStrAvoidingBackslashes (string : List Nat) (quoteTypes : List (List Nat)) : UM Unit := do
  let (s, qs) := strLiteralHelper string quoteTypes false
  let q := qs.headD []
  write (q ++ s ++ q)

/-- `_write_constant`, `Lib/_ast_unparse.py:693-703`. -/
def constRepr : PyConst → Except PyExc (List Nat)
  | .none => .ok (cp "None")
  | .true_ => .ok (cp "True")
  | .false_ => .ok (cp "False")
  | .ellipsis => .ok (cp "Ellipsis")
  | .int v => if intTooLong v then .error (.valueError intReprLimit) else .ok (intRepr v)
  | .float b => .ok (replaceInf (floatRepr b))
  | .complex r i => .ok (replaceInf (complexRepr r i))
  | .str s => .ok (strRepr s)
  | .bytes s => .ok (bytesRepr s)
  | _ => .ok []
where
  /-- `repr(value).replace("inf", _INFSTR).replace("nan", f"({_INFSTR}-{_INFSTR})")`. -/
  replaceInf : List Nat → List Nat
    | 105 :: 110 :: 102 :: r => cp "1e309" ++ replaceInf r
    | 110 :: 97 :: 110 :: r => cp "(1e309-1e309)" ++ replaceInf r
    | c :: r => c :: replaceInf r
    | [] => []

/-- `self._write_constant(value)` -/
def writeConstant (c : PyConst) : UM Unit :=
  match constRepr c with
  | .ok t => write t
  | .error e => throw e

/-- `str.replace` of one code point by a string. -/
def replaceCp (s : List Nat) (c : Nat) (by_ : List Nat) : List Nat :=
  s.flatMap fun x => if x == c then by_ else [x]

/-- `get_raw_docstring`, when the body list has one. -/
def rawDocstring : List Ast → Option Ast
  | .node .Expr [v@(.node .Constant (.const (.str _) :: _) _)] _ :: _ => some v
  | _ => none

/-- `_ftstring_helper`'s fallback, `repr('"' + value)` with the prefix stripped. -/
def reprNoPrefix (v : List Nat) : List Nat :=
  let r := strRepr (34 :: v)
  (r.drop 2).dropLast

/-- The main loop of `_ftstring_helper`. `none` is `fallback_to_repr`. -/
def ftstringLoop : List (List Nat × Bool) → List (List Nat) → List (List Nat) →
    Except PyExc (Option (List (List Nat) × List (List Nat)))
  | [], qs, acc => .ok (some (acc.reverse, qs))
  | (value, isConstant) :: rest, qs, acc =>
    if isConstant then
      let (v, newQ) := strLiteralHelper value qs true
      if newQ.all (fun q => !qs.contains q) then .ok none
      else ftstringLoop rest newQ (v :: acc)
    else
      let qs' := if value.contains 10 then qs.filter (multiQuotes.contains ·) else qs
      if value.contains 10 && qs'.isEmpty then
        .error (.assertionError "")
      else
        let filtered := qs'.filter (fun q => !contains value q)
        ftstringLoop rest (if filtered.isEmpty then qs' else filtered) (value :: acc)

/-- `_ftstring_helper`, `Lib/_ast_unparse.py:576-616`. -/
def ftstringHelper (parts : List (List Nat × Bool)) : UM Unit := do
  match ftstringLoop parts allQuotes [] with
  | .error e => throw e
  | .ok (some (ps, qs)) =>
    let q := qs.headD []
    write (q ++ ps.flatten ++ q)
  | .ok none =>
    let ps := parts.map fun (v, c) => if c then reprNoPrefix v else v
    write (qS3 ++ ps.flatten ++ qS3)

/-- `unop`, `binop`, `cmpops` as tables. -/
def binopStr : Ctor → String
  | .Add => "+" | .Sub => "-" | .Mult => "*" | .MatMult => "@" | .Div => "/" | .Mod => "%"
  | .LShift => "<<" | .RShift => ">>" | .BitOr => "|" | .BitXor => "^" | .BitAnd => "&"
  | .FloorDiv => "//" | .Pow => "**"
  | _ => ""

/-- `binop_precedence` -/
def binopPrec : Ctor → Nat
  | .Add | .Sub => pArith
  | .Mult | .MatMult | .Div | .Mod | .FloorDiv => pTerm
  | .LShift | .RShift => pShift
  | .BitOr => pBor
  | .BitXor => pBxor
  | .BitAnd => pBand
  | .Pow => pPower
  | _ => pTest

/-- `cmpops` -/
def cmpStr : Ctor → String
  | .Eq => "==" | .NotEq => "!=" | .Lt => "<" | .LtE => "<=" | .Gt => ">" | .GtE => ">="
  | .Is => "is" | .IsNot => "is not" | .In => "in" | .NotIn => "not in"
  | _ => ""

/-- Name of a field that is an identifier. -/
def idOf : Ast → List Nat
  | .ident s | .str s => s
  | _ => []

/-- `if x:` on an optional or a list field. -/
def present : Ast → Bool
  | .null => false
  | .seq [] => false
  | .int 0 => false
  | .ident [] => false
  | _ => true

/-- `seq` of a field. -/
def seqU : Ast → List Ast
  | .seq xs => xs
  | _ => []

/-- `get_type_comment` -/
def typeComment (l : Option Loc) (tc : Ast) : UM (Option (List Nat)) := do
  let s ← get
  let line := match l with
    | some l => l.lineno
    | none => 0
  match (s.typeIgnores.find? (fun e => e.1 == line)).map (·.2) with
  | some c => if c.isEmpty then fromTc tc else return some (cp " # type: " ++ c)
  | none => fromTc tc
where
  fromTc (tc : Ast) : UM (Option (List Nat)) :=
    match tc with
    | .str c => return some (cp " # type: " ++ c)
    | _ => return none

mutual
  /-- `self.traverse(node)`: `prec` is `get_precedence(node)`. -/
  def visit : Nat → Nat → Ast → UM Unit
    | 0, _, _ => throw .modelFuel
    | f + 1, prec, node =>
      match node with
      | .seq xs => visitList f xs
      | .node c fs l => visitNode f prec c fs l
      | _ => pure ()
  termination_by structural f _ _ => f

  /-- `for item in node: self.traverse(item)`, each at the default precedence. -/
  def visitList : Nat → List Ast → UM Unit
    | 0, _ => throw .modelFuel
    | _ + 1, [] => pure ()
    | f + 1, x :: xs => do
      visit f pTest x
      visitList f xs
  termination_by structural f _ => f

  /-- `_write_docstring_and_traverse_body`. -/
  def docstringBody : Nat → List Ast → Bool → UM Unit
    | 0, _, _ => throw .modelFuel
    | f + 1, body, allowed =>
      match (if allowed then rawDocstring body else none) with
      | some d => do
        fill "" false
        match d with
        | .node _ (.const (.str s) :: kind :: _) _ =>
          if kind.field? "" |>.isNone then
            match kind with
            | .str [117] => wr "u"
            | _ => pure ()
          writeStrAvoidingBackslashes s multiQuotes
        | _ => pure ()
        visitList f (body.drop 1)
      | none => visitList f body
  termination_by structural f _ _ => f

  /-- `_write_ftstring_inner`, `Lib/_ast_unparse.py:635-654`. -/
  def ftInner : Nat → Ast → Bool → UM Unit
    | 0, _, _ => throw .modelFuel
    | f + 1, node, isSpec =>
      match node with
      | .node .JoinedStr [values] _ => ftInnerList f (seqU values) isSpec
      | .node .Constant (.const (.str v) :: _) _ => do
        let value := replaceCp (replaceCp v 123 [123, 123]) 125 [125, 125]
        let value :=
          if isSpec then
            let v := replaceCp value 92 [92, 92]
            let v := replaceCp v 39 [92, 39]
            let v := replaceCp v 34 [92, 34]
            replaceCp v 10 [92, 110]
          else value
        write value
      | .node .FormattedValue [value, conv, spec] _ => writeInterpolation f value none conv spec
      | .node .Interpolation [value, str, conv, spec] _ =>
        match str with
        | .const (.str s) => writeInterpolation f value (some s) conv spec
        | _ => writeInterpolation f value none conv spec
      | _ => throw (.valueError "~Unexpected node inside JoinedStr")
  termination_by structural f _ _ => f

  def ftInnerList : Nat → List Ast → Bool → UM Unit
    | 0, _, _ => throw .modelFuel
    | _ + 1, [], _ => pure ()
    | f + 1, x :: xs, isSpec => do
      ftInner f x isSpec
      ftInnerList f xs isSpec
  termination_by structural f _ _ => f

  /-- `_write_interpolation`, `Lib/_ast_unparse.py:661-675`, with
  `_unparse_interpolation_value`: a fresh `Unparser` at `TEST.next()`. -/
  def writeInterpolation : Nat → Ast → Option (List Nat) → Ast → Ast → UM Unit
    | 0, _, _, _, _ => throw .modelFuel
    | f + 1, value, str, conv, spec => do
      wr "{"
      let expr ←
        match str with
        | some s => pure s
        | none =>
          match (visit f (pNext pTest) value).run {} with
          | .ok _ s => pure (joined s.source)
          | .error e _ => throw e
      if expr.head? == some 123 then wr " "
      write expr
      match conv with
      | .int v => if v != -1 then write [33, v.toNat]
      | _ => pure ()
      if present spec then
        wr ":"
        ftInner f spec true
      wr "}"
  termination_by structural f _ _ _ _ => f

  /-- `_write_ftstring`: one buffer per value. -/
  def ftParts : Nat → List Ast → UM (List (List Nat × Bool))
    | 0, _ => throw .modelFuel
    | _ + 1, [] => return []
    | f + 1, v :: vs => do
      let saved := (← get).source
      modify fun s => { s with source := [] }
      ftInner f v false
      let buf := joined (← get).source
      modify fun s => { s with source := saved }
      let isConst := match v with
        | .node .Constant _ _ => true
        | _ => false
      return (buf, isConst) :: (← ftParts f vs)
  termination_by structural f _ => f

  /-- `do_visit_try` -/
  def visitTry : Nat → Ast → Ast → Ast → Ast → UM Unit
    | 0, _, _, _, _ => throw .modelFuel
    | f + 1, body, handlers, orelse, finalbody => do
      fill "try" false
      block none (visitList f (seqU body))
      visitList f (seqU handlers)
      if present orelse then
        fill "else" false
        block none (visitList f (seqU orelse))
      if present finalbody then
        fill "finally" false
        block none (visitList f (seqU finalbody))
  termination_by structural f _ _ _ _ => f

  /-- The `while` of `visit_If`, `Lib/_ast_unparse.py:492-508`. -/
  def ifChain : Nat → Ast → UM Unit
    | 0, _ => throw .modelFuel
    | f + 1, orelse =>
      match orelse with
      | .seq [.node .If [test, body, o] _] => do
        fill "elif " false
        visit f pTest test
        block none (visitList f (seqU body))
        ifChain f o
      | _ => do
        if present orelse then
          fill "else" false
          block none (visitList f (seqU orelse))
  termination_by structural f _ => f

  /-- `visit_arguments`, `Lib/_ast_unparse.py:994-1043`. -/
  def visitArguments : Nat → List Ast → UM Unit
    | 0, _ => throw .modelFuel
    | f + 1, [posonly, args, vararg, kwonly, kwDefaults, kwarg, defaults] => do
      let allArgs := seqU posonly ++ seqU args
      let dflts := List.replicate (allArgs.length - (seqU defaults).length) Ast.null ++ seqU defaults
      let npos := (seqU posonly).length
      let first ← normalArgs f (allArgs.zip dflts) 1 npos true
      let mut first := first
      if present vararg || present kwonly then
        if first then first := false else wr ", "
        wr "*"
        if present vararg then
          match vararg with
          | .node _ [a, ann, _] _ =>
            write (idOf a)
            if present ann then
              wr ": "
              visit f pTest ann
          | _ => pure ()
      if present kwonly then
        kwArgs f ((seqU kwonly).zip (seqU kwDefaults))
      if present kwarg then
        if first then first := false else wr ", "
        match kwarg with
        | .node _ [a, ann, _] _ =>
          write (cp "**" ++ idOf a)
          if present ann then
            wr ": "
            visit f pTest ann
        | _ => pure ()
    | _ + 1, _ => pure ()
  termination_by structural f _ => f

  def normalArgs : Nat → List (Ast × Ast) → Nat → Nat → Bool → UM Bool
    | 0, _, _, _, _ => throw .modelFuel
    | _ + 1, [], _, _, first => return first
    | f + 1, (a, d) :: rest, index, npos, first => do
      if !first then wr ", "
      visit f pTest a
      if present d then
        wr "="
        visit f pTest d
      if index == npos then wr ", /"
      normalArgs f rest (index + 1) npos false
  termination_by structural f _ _ _ _ => f

  def kwArgs : Nat → List (Ast × Ast) → UM Unit
    | 0, _ => throw .modelFuel
    | _ + 1, [] => pure ()
    | f + 1, (a, d) :: rest => do
      wr ", "
      visit f pTest a
      if present d then
        wr "="
        visit f pTest d
      kwArgs f rest
  termination_by structural f _ => f

  /-- `_function_helper`, `Lib/_ast_unparse.py:423-438`. -/
  def functionHelper : Nat → String → List Ast → Option Loc → UM Unit
    | 0, _, _, _ => throw .modelFuel
    | f + 1, suffix, [name, args, body, decs, returns, tc, tps], l => do
      maybeNewline
      decorators f (seqU decs)
      fill (suffix ++ " " ++ String.ofList ((idOf name).map Char.ofNat)) false
      typeParamsHelper f tps
      wr "("
      visit f pTest args
      wr ")"
      if present returns then
        wr " -> "
        visit f pTest returns
      let extra ← typeComment l tc
      block extra (docstringBody f (seqU body) true)
    | _ + 1, _, _, _ => pure ()
  termination_by structural f _ _ _ => f

  def decorators : Nat → List Ast → UM Unit
    | 0, _ => throw .modelFuel
    | _ + 1, [] => pure ()
    | f + 1, d :: ds => do
      fill "@" false
      visit f pTest d
      decorators f ds
  termination_by structural f _ => f

  /-- `_type_params_helper` -/
  def typeParamsHelper : Nat → Ast → UM Unit
    | 0, _ => throw .modelFuel
    | f + 1, tps =>
      match seqU tps with
      | [] => pure ()
      | xs => do
        wr "["
        sepList f xs ", "
        wr "]"
  termination_by structural f _ => f

  /-- `self.interleave(lambda: self.write(sep), self.traverse, xs)` -/
  def sepList : Nat → List Ast → String → UM Unit
    | 0, _, _ => throw .modelFuel
    | _ + 1, [], _ => pure ()
    | f + 1, [x], _ => visit f pTest x
    | f + 1, x :: xs, sep => do
      visit f pTest x
      wr sep
      sepList f xs sep
  termination_by structural f _ _ => f

  /-- `items_view(self.traverse, xs)` -/
  def itemsList : Nat → List Ast → UM Unit
    | 0, _ => throw .modelFuel
    | f + 1, [x] => do
      visit f pTest x
      wr ","
    | f + 1, xs => sepList f xs ", "
  termination_by structural f _ => f

  /-- `visit_ClassDef`/`visit_Call`'s comma loop. -/
  def commaArgs : Nat → List Ast → Bool → UM Bool
    | 0, _, _ => throw .modelFuel
    | _ + 1, [], comma => return comma
    | f + 1, e :: es, comma => do
      if comma then wr ", "
      visit f pTest e
      commaArgs f es true
  termination_by structural f _ _ => f

  /-- `visit_comprehension` for each generator -/
  def gens : Nat → List Ast → UM Unit
    | 0, _ => throw .modelFuel
    | _ + 1, [] => pure ()
    | f + 1, g :: gs => do
      visit f pTest g
      gens f gs
  termination_by structural f _ => f

  /-- `visit_Compare`'s tail. -/
  def cmpTail : Nat → List Ast → List Ast → UM Unit
    | 0, _, _ => throw .modelFuel
    | f + 1, .node o _ _ :: os, e :: es => do
      wr (" " ++ cmpStr o ++ " ")
      visit f (pNext pCmp) e
      cmpTail f os es
    | _ + 1, _, _ => pure ()
  termination_by structural f _ _ => f

  /-- `visit_BoolOp`'s `increasing_level_traverse`. -/
  def boolVals : Nat → List Ast → Nat → String → UM Unit
    | 0, _, _, _ => throw .modelFuel
    | _ + 1, [], _, _ => pure ()
    | f + 1, [v], p, _ => visit f (pNext p) v
    | f + 1, v :: vs, p, sep => do
      visit f (pNext p) v
      wr sep
      boolVals f vs (pNext p) sep
  termination_by structural f _ _ _ => f

  /-- `visit_Dict`'s items. -/
  def dictItems : Nat → List (Ast × Ast) → UM Unit
    | 0, _ => throw .modelFuel
    | _ + 1, [] => pure ()
    | f + 1, (k, v) :: rest => do
      match k with
      | .null =>
        wr "**"
        visit f pExpr v
      | _ =>
        visit f pTest k
        wr ": "
        visit f pTest v
      if !rest.isEmpty then wr ", "
      dictItems f rest
  termination_by structural f _ => f

  /-- `visit_MatchMapping`'s pairs. -/
  def mapPairs : Nat → List (Ast × Ast) → UM Unit
    | 0, _ => throw .modelFuel
    | _ + 1, [] => pure ()
    | f + 1, (k, p) :: rest => do
      visit f pTest k
      wr ": "
      visit f pTest p
      if !rest.isEmpty then wr ", "
      mapPairs f rest
  termination_by structural f _ => f

  /-- `visit_MatchClass`'s keyword pairs. -/
  def attrPairs : Nat → List (Ast × Ast) → UM Unit
    | 0, _ => throw .modelFuel
    | _ + 1, [] => pure ()
    | f + 1, (a, p) :: rest => do
      write (idOf a ++ [61])
      visit f pTest p
      if !rest.isEmpty then wr ", "
      attrPairs f rest
  termination_by structural f _ => f

  /-- `visit_MatchOr`'s patterns, each at `BOR.next()`. -/
  def orPats : Nat → List Ast → UM Unit
    | 0, _ => throw .modelFuel
    | _ + 1, [] => pure ()
    | f + 1, [x] => visit f (pNext pBor) x
    | f + 1, x :: xs => do
      visit f (pNext pBor) x
      wr " | "
      orPats f xs
  termination_by structural f _ => f

  /-- `for target in node.targets` of `visit_Assign`. -/
  def assignTargets : Nat → List Ast → UM Unit
    | 0, _ => throw .modelFuel
    | _ + 1, [] => pure ()
    | f + 1, t :: ts => do
      visit f pTuple t
      wr " = "
      assignTargets f ts
  termination_by structural f _ => f

  /-- `node.ifs` of `visit_comprehension`. -/
  def compIfs : Nat → List Ast → UM Unit
    | 0, _ => throw .modelFuel
    | _ + 1, [] => pure ()
    | f + 1, i :: is_ => do
      wr " if "
      visit f (pNext pTest) i
      compIfs f is_
  termination_by structural f _ => f

  /-- The `visit_*` methods. -/
  def visitNode : Nat → Nat → Ctor → List Ast → Option Loc → UM Unit
    | 0, _, _, _, _ => throw .modelFuel
    | f + 1, prec, c, fs, l =>
      match c, fs with
      | .Module, [body, ignores] => do
        modify fun s => { s with typeIgnores := (seqU ignores).filterMap fun t =>
          match t with
          | .node _ [.int n, .str tag] _ => some (n, cp "ignore" ++ tag)
          | _ => none }
        docstringBody f (seqU body) true
        modify fun s => { s with typeIgnores := [] }
      | .Interactive, [body] => do
        modify fun s => { s with inInteractive := true }
        docstringBody f (seqU body) false
        modify fun s => { s with inInteractive := false }
      | .Expression, [body] => visit f pTest body
      | .FunctionType, [args, returns] => do
        wr "("
        sepList f (seqU args) ", "
        wr ")"
        wr " -> "
        visit f pTest returns
      | .Expr, [v] => do
        fill
        visit f pYield v
      | .NamedExpr, [t, v] => requireParens pNamedExpr prec do
        visit f pAtom t
        wr " := "
        visit f pAtom v
      | .Import, [names] => do
        fill "import "
        sepList f (seqU names) ", "
      | .ImportFrom, [mod, names, level] => do
        fill "from "
        let n := match level with
          | .int v => v.toNat
          | _ => 0
        write (List.replicate n 46)
        if present mod then write (idOf mod)
        wr " import "
        sepList f (seqU names) ", "
      | .Assign, [targets, v, tc] => do
        fill
        assignTargets f (seqU targets)
        visit f pTest v
        match ← typeComment l tc with
        | some t => write t
        | none => pure ()
      | .AugAssign, [t, .node o _ _, v] => do
        fill
        visit f pTest t
        wr (" " ++ binopStr o ++ "= ")
        visit f pTest v
      | .AnnAssign, [t, ann, v, simple] => do
        fill
        let isName := match t with
          | .node .Name _ _ => true
          | _ => false
        delimitIf "(" ")" (!present simple && isName) (visit f pTest t)
        wr ": "
        visit f pTest ann
        if present v then
          wr " = "
          visit f pTest v
      | .Return, [v] => do
        fill "return"
        if present v then
          wr " "
          visit f pTest v
      | .Pass, _ => fill "pass"
      | .Break, _ => fill "break"
      | .Continue, _ => fill "continue"
      | .Delete, [t] => do
        fill "del "
        sepList f (seqU t) ", "
      | .Assert, [t, m] => do
        fill "assert "
        visit f pTest t
        if present m then
          wr ", "
          visit f pTest m
      | .Global, [names] | .Nonlocal, [names] => do
        fill (if c == .Global then "global " else "nonlocal ")
        interleave (wr ", ") (fun n => write (idOf n)) (seqU names)
      | .Await, [v] => requireParens pAwait prec do
        wr "await"
        if present v then
          wr " "
          visit f pAtom v
      | .Yield, [v] => requireParens pYield prec do
        wr "yield"
        if present v then
          wr " "
          visit f pAtom v
      | .YieldFrom, [v] => requireParens pYield prec do
        wr "yield from "
        if !present v then throw (.valueError "Node can't be used without a value attribute.")
        visit f pAtom v
      | .Raise, [exc, cause] => do
        fill "raise"
        if !present exc then
          if present cause then throw (.valueError "Node can't use cause without an exception.")
          return
        wr " "
        visit f pTest exc
        if present cause then
          wr " from "
          visit f pTest cause
      | .Try, [b, h, o, fb] | .TryStar, [b, h, o, fb] => do
        let prev := (← get).inTryStar
        modify fun s => { s with inTryStar := c == .TryStar }
        visitTry f b h o fb
        modify fun s => { s with inTryStar := prev }
      | .ExceptHandler, [ty, name, body] => do
        fill (if (← get).inTryStar then "except*" else "except") false
        if present ty then
          wr " "
          visit f pTest ty
        if present name then
          wr " as "
          write (idOf name)
        block none (visitList f (seqU body))
      | .ClassDef, [name, bases, keywords, body, decs, tps] => do
        maybeNewline
        decorators f (seqU decs)
        fill ("class " ++ String.ofList ((idOf name).map Char.ofNat)) false
        typeParamsHelper f tps
        delimitIf "(" ")" (present bases || present keywords) do
          let comma ← commaArgs f (seqU bases) false
          let _ ← commaArgs f (seqU keywords) comma
        block none (docstringBody f (seqU body) true)
      | .FunctionDef, _ => functionHelper f "def" fs l
      | .AsyncFunctionDef, _ => functionHelper f "async def" fs l
      | .TypeVar, [name, bound, d] => do
        write (idOf name)
        if present bound then
          wr ": "
          visit f pTest bound
        if present d then
          wr " = "
          visit f pTest d
      | .TypeVarTuple, [name, d] => do
        write (42 :: idOf name)
        if present d then
          wr " = "
          visit f pTest d
      | .ParamSpec, [name, d] => do
        write (cp "**" ++ idOf name)
        if present d then
          wr " = "
          visit f pTest d
      | .TypeAlias, [name, tps, v] => do
        fill "type "
        visit f pTest name
        typeParamsHelper f tps
        wr " = "
        visit f pTest v
      | .For, [t, it, body, o, tc] | .AsyncFor, [t, it, body, o, tc] => do
        fill (if c == .For then "for " else "async for ") false
        visit f pTuple t
        wr " in "
        visit f pTest it
        let extra ← typeComment l tc
        block extra (visitList f (seqU body))
        if present o then
          fill "else" false
          block none (visitList f (seqU o))
      | .If, [test, body, o] => do
        fill "if " false
        visit f pTest test
        block none (visitList f (seqU body))
        ifChain f o
      | .While, [test, body, o] => do
        fill "while " false
        visit f pTest test
        block none (visitList f (seqU body))
        if present o then
          fill "else" false
          block none (visitList f (seqU o))
      | .With, [items, body, tc] | .AsyncWith, [items, body, tc] => do
        fill (if c == .With then "with " else "async with ") false
        sepList f (seqU items) ", "
        let extra ← typeComment l tc
        block extra (visitList f (seqU body))
      | .JoinedStr, [values] | .TemplateStr, [values] => do
        wr (if c == .JoinedStr then "f" else "t")
        ftstringHelper (← ftParts f (seqU values))
      | .FormattedValue, [value, conv, spec] => writeInterpolation f value none conv spec
      | .Interpolation, [value, str, conv, spec] =>
        match str with
        | .const (.str s) => writeInterpolation f value (some s) conv spec
        | _ => writeInterpolation f value none conv spec
      | .Name, [id, _] => write (idOf id)
      | .Constant, (.const v :: kind :: _) =>
        match v with
        | .tuple xs => do
          wr "("
          itemsView writeConstant xs
          wr ")"
        | .ellipsis => wr "..."
        | _ => do
          match kind with
          | .str [117] => wr "u"
          | _ => pure ()
          writeConstant v
      | .List, [elts, _] => do
        wr "["
        sepList f (seqU elts) ", "
        wr "]"
      | .ListComp, [elt, g] | .GeneratorExp, [elt, g] | .SetComp, [elt, g] => do
        wr (match c with
          | .ListComp => "["
          | .SetComp => "{"
          | _ => "(")
        visit f pTest elt
        gens f (seqU g)
        wr (match c with
          | .ListComp => "]"
          | .SetComp => "}"
          | _ => ")")
      | .DictComp, [k, v, g] => do
        wr "{"
        visit f pTest k
        wr ": "
        visit f pTest v
        gens f (seqU g)
        wr "}"
      | .comprehension_, [t, it, ifs, isAsync] => do
        wr (if present isAsync then " async for " else " for ")
        visit f pTuple t
        wr " in "
        visit f (pNext pTest) it
        compIfs f (seqU ifs)
      | .IfExp, [test, body, o] => requireParens pTest prec do
        visit f (pNext pTest) body
        wr " if "
        visit f (pNext pTest) test
        wr " else "
        visit f pTest o
      | .Set, [elts] =>
        if present elts then do
          wr "{"
          sepList f (seqU elts) ", "
          wr "}"
        else wr "{*()}"
      | .Dict, [keys, values] => do
        wr "{"
        dictItems f ((seqU keys).zip (seqU values))
        wr "}"
      | .Tuple, [elts, _] =>
        delimitIf "(" ")" ((seqU elts).isEmpty || prec > pTuple) (itemsList f (seqU elts))
      | .UnaryOp, [.node o _ _, operand] => do
        let (op, p) : String × Nat := match o with
          | .Invert => ("~", pFactor)
          | .Not => ("not", pNot)
          | .UAdd => ("+", pFactor)
          | _ => ("-", pFactor)
        requireParens p prec do
          wr op
          if p != pFactor then wr " "
          visit f p operand
      | .BinOp, [left, .node o _ _, right] => do
        let p := binopPrec o
        requireParens p prec do
          let (lp, rp) := if o == .Pow then (pNext p, p) else (p, pNext p)
          visit f lp left
          wr (" " ++ binopStr o ++ " ")
          visit f rp right
      | .Compare, [left, ops, comparators] => requireParens pCmp prec do
        visit f (pNext pCmp) left
        cmpTail f (seqU ops) (seqU comparators)
      | .BoolOp, [.node o _ _, values] => do
        let (op, p) : String × Nat := if o == .And then ("and", pAnd) else ("or", pOr)
        requireParens p prec (boolVals f (seqU values) p (" " ++ op ++ " "))
      | .Attribute, [v, attr, _] => do
        visit f pAtom v
        match v with
        | .node .Constant (.const (.int _) :: _) _
        | .node .Constant (.const .true_ :: _) _
        | .node .Constant (.const .false_ :: _) _ => wr " "
        | _ => pure ()
        wr "."
        write (idOf attr)
      | .Call, [func, args, keywords] => do
        visit f pAtom func
        wr "("
        let comma ← commaArgs f (seqU args) false
        let _ ← commaArgs f (seqU keywords) comma
        wr ")"
      | .Subscript, [v, s, _] => do
        visit f pAtom v
        wr "["
        match s with
        | .node .Tuple (.seq (x :: xs) :: _) _ => itemsList f (x :: xs)
        | _ => visit f pTest s
        wr "]"
      | .Starred, [v, _] => do
        wr "*"
        visit f pExpr v
      | .Slice, [lo, hi, st] => do
        if present lo then visit f pTest lo
        wr ":"
        if present hi then visit f pTest hi
        if present st then
          wr ":"
          visit f pTest st
      | .Match, [subject, cases] => do
        fill "match " false
        visit f pTest subject
        block none (visitList f (seqU cases))
      | .arg_, [a, ann, _] => do
        write (idOf a)
        if present ann then
          wr ": "
          visit f pTest ann
      | .arguments_, _ => visitArguments f fs
      | .keyword_, [a, v] => do
        match a with
        | .null => wr "**"
        | _ =>
          write (idOf a)
          wr "="
        visit f pTest v
      | .Lambda, [args, body] => requireParens pTest prec do
        wr "lambda"
        let saved := (← get).source
        modify fun s => { s with source := [] }
        visit f pTest args
        let buf := (← get).source
        modify fun s => { s with source := saved }
        if !buf.isEmpty then
          wr " "
          modify fun s => { s with source := buf ++ s.source }
        wr ": "
        visit f pTest body
      | .alias_, [name, asname] => do
        write (idOf name)
        if present asname then write (cp " as " ++ idOf asname)
      | .withitem_, [e, v] => do
        visit f pTest e
        if present v then
          wr " as "
          visit f pTest v
      | .match_case_, [p, guard, body] => do
        fill "case " false
        visit f pTest p
        if present guard then
          wr " if "
          visit f pTest guard
        block none (visitList f (seqU body))
      | .MatchValue, [v] => visit f pTest v
      | .MatchSingleton, [.const v] => writeConstant v
      | .MatchSequence, [ps] => do
        wr "["
        sepList f (seqU ps) ", "
        wr "]"
      | .MatchStar, [name] =>
        match name with
        | .null => wr "*_"
        | _ => write (42 :: idOf name)
      | .MatchMapping, [keys, ps, rest] => do
        wr "{"
        mapPairs f ((seqU keys).zip (seqU ps))
        match rest with
        | .null => pure ()
        | _ =>
          if present keys then wr ", "
          write (cp "**" ++ idOf rest)
        wr "}"
      | .MatchClass, [cls, ps, attrs, kwd] => do
        visit f pAtom cls
        wr "("
        sepList f (seqU ps) ", "
        if present attrs then
          if present ps then wr ", "
          attrPairs f ((seqU attrs).zip (seqU kwd))
        wr ")"
      | .MatchAs, [p, name] =>
        match name, p with
        | .null, _ => wr "_"
        | _, .null => write (idOf name)
        | _, _ => requireParens pTest prec do
          visit f pBor p
          write (cp " as " ++ idOf name)
      | .MatchOr, [ps] => requireParens pBor prec (orPats f (seqU ps))
      | _, _ => throw (.named "AttributeError" "~unexpected node")
  termination_by structural f _ _ _ _ => f
end

/-- A bound on nesting for `unparse`. -/
def unparseFuel (n : Nat) : Nat := 8 * n + 64

/-- `ast.unparse(tree)`, with `n` a bound on the tree's size. -/
def unparseN (n : Nat) (t : Ast) : Py (List Nat) :=
  match (visit (unparseFuel n) pTest t).run {} with
  | .ok _ s => .ok (joined s.source)
  | .error e _ => .error e

end PyLean.PyGrammar.Unparse
