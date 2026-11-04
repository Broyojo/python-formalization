import PyLean.PyGrammar.Peg.Strings
import PyLean.PyGrammar.Unparse.Repr

/-!
The action helpers: `Parser/action_helpers.c`, the macros of `Parser/pegen.h`, and the
evaluator of parsed C actions. Values are `Ast`s: `.null` is `NULL`, a C `int` is `.int`,
and the parser's own records are nodes with a `P…` constructor.
-/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- Elements of a sequence; `NULL` counts as empty, as `asdl_seq_LEN(NULL) == 0`. -/
def seqOf : Ast → List Ast
  | .seq xs => xs
  | _ => []

/-- `(expr)->v.X.name`, by the ASDL field name. -/
def fieldOf (a : Ast) (name : String) : Ast :=
  (a.field? name).getD .null

/-- The location of a node or token. -/
def locOf : Ast → Loc
  | .node _ _ (some l) => l
  | .tok t => tokLoc t
  | _ => default

/-- An `int`-valued location argument. -/
def locArgs (l : Loc) : List Ast :=
  [.int l.lineno, .int l.colOffset, .int l.endLineno, .int l.endColOffset]

/-- Replace `NULL` by an empty sequence in sequence fields. -/
def normFields : List (String × FieldBase × FieldQuant) → List Ast → List Ast
  | (_, _, q) :: fs, a :: as =>
    (match a, q with
      | .null, .seq | .null, .optSeq => .seq []
      | _, _ => a) :: normFields fs as
  | _, _ => []

/-- `_PyAST_c(args)`: `NULL` for a sequence field becomes an empty sequence, which is how
`PyAST_mod2obj` shows it, and the last four arguments of a located constructor are its
location. -/
def mkAst (c : Ctor) (args : List Ast) : Ast :=
  let fields := c.fields
  let loc : Option Loc :=
    match args.drop fields.length with
    | [.int p, .int q, .int r, .int s] => some ⟨p, q, r, s⟩
    | _ => none
  .node c (normFields fields args) loc

/-- `mkAst` with a given location. -/
def mkAt (c : Ctor) (fields : List Ast) (l : Loc) : Ast := mkAst c (fields ++ locArgs l)

/-- An internal record. -/
def rec_ (c : Ctor) (fields : List Ast) : Ast := .node c fields none

/-- Field `i` of an internal record. -/
def recField (p : Ast) (i : Nat) : Ast :=
  match p with
  | .node _ fs _ => fs.getD i .null
  | _ => .null

/-- `_PyPegen_set_expr_context`, `Parser/action_helpers.c:320-348`. Recursion is on
`Starred`, `Tuple` and `List` nesting; `f` exceeds any parser depth (`MAXSTACK`). -/
def setExprContext (ctx : Ast) : Nat → Ast → Ast
  | 0, e => e
  | f + 1, e =>
    match e with
    | .node .Name [id, _] l => .node .Name [id, ctx] l
    | .node .Tuple [elts, _] l => .node .Tuple [.seq ((seqOf elts).map (setExprContext ctx f)), ctx] l
    | .node .List [elts, _] l => .node .List [.seq ((seqOf elts).map (setExprContext ctx f)), ctx] l
    | .node .Subscript [v, s, _] l => .node .Subscript [v, s, ctx] l
    | .node .Attribute [v, a, _] l => .node .Attribute [v, a, ctx] l
    | .node .Starred [v, _] l => .node .Starred [setExprContext ctx f v, ctx] l
    | e => e

/-- `_get_names` -/
def getNames (s : Ast) : Ast := .seq ((seqOf s).map fun p => recField p 0)

/-- `_get_defaults` -/
def getDefaults (s : Ast) : Ast := .seq ((seqOf s).map fun p => recField p 1)

/-- `_PyPegen_join_sequences` -/
def joinSeq (a b : Ast) : Ast := .seq (seqOf a ++ seqOf b)

/-- `x == NULL` -/
@[inline] def isNullA : Ast → Bool
  | .null => true
  | _ => false

/-- `_make_posonlyargs` -/
def posonlyOf (slashNo slashWith : Ast) : Ast :=
  if !isNullA slashNo then slashNo
  else if !isNullA slashWith then joinSeq (recField slashWith 0) (getNames (recField slashWith 1))
  else .seq []

/-- `_make_posargs`. Its `assert(0)` branch is kept. -/
def posargsOf (plain namesDef : Ast) : Ast :=
  if !isNullA namesDef then
    if !isNullA plain then joinSeq plain (getNames namesDef) else getNames namesDef
  else if !isNullA plain then plain
  else .seq []

/-- `_make_posdefaults` -/
def posdefaultsOf (slashWith namesDef : Ast) : Ast :=
  if !isNullA slashWith && !isNullA namesDef then
    joinSeq (getDefaults (recField slashWith 1)) (getDefaults namesDef)
  else if isNullA slashWith && !isNullA namesDef then getDefaults namesDef
  else if !isNullA slashWith && isNullA namesDef then getDefaults (recField slashWith 1)
  else .seq []

/-- `_PyPegen_make_arguments`, with `_make_kwargs` inline. -/
def makeArguments (slashNo slashWith plain namesDef starEtc : Ast) : Ast :=
  let kwonly := recField starEtc 1
  mkAst .arguments_ [posonlyOf slashNo slashWith, posargsOf plain namesDef, recField starEtc 0,
    getNames kwonly, getDefaults kwonly, recField starEtc 2, posdefaultsOf slashWith namesDef]

/-- `_PyPegen_new_type_comment` on a token. -/
def typeCommentOf (t : Ast) : Ast :=
  match t with
  | .tok t => .str (utf8Decode t.bytes)
  | _ => .null

/-- `_PyPegen_add_type_comment_to_arg` -/
def addTypeComment (a tc : Ast) : Ast :=
  match tc, a with
  | .null, _ => a
  | _, .node c [x, y, _] l => .node c [x, y, typeCommentOf tc] l
  | _, _ => a

/-- `_PyPegen_get_expr_name`, `Parser/action_helpers.c` (`NULL` on the default case). -/
def exprName (e : Ast) : Option String :=
  match e with
  | .node c fs _ =>
    match c with
    | .Attribute => some "attribute"
    | .Subscript => some "subscript"
    | .Starred => some "starred"
    | .Name => some "name"
    | .List => some "list"
    | .Tuple => some "tuple"
    | .Lambda => some "lambda"
    | .Call => some "function call"
    | .BoolOp | .BinOp | .UnaryOp => some "expression"
    | .GeneratorExp => some "generator expression"
    | .Yield | .YieldFrom => some "yield expression"
    | .Await => some "await expression"
    | .ListComp => some "list comprehension"
    | .SetComp => some "set comprehension"
    | .DictComp => some "dict comprehension"
    | .Dict => some "dict literal"
    | .Set => some "set display"
    | .JoinedStr | .FormattedValue => some "f-string expression"
    | .TemplateStr | .Interpolation => some "t-string expression"
    | .Constant =>
      match fs with
      | .const .none :: _ => some "None"
      | .const .false_ :: _ => some "False"
      | .const .true_ :: _ => some "True"
      | .const .ellipsis :: _ => some "ellipsis"
      | _ => some "literal"
    | .Compare => some "comparison"
    | .IfExp => some "conditional expression"
    | .NamedExpr => some "named expression"
    | _ => none
  | _ => none

/-- The C enum `_expr_kind`, `Include/internal/pycore_ast.h:361-369` (0 for a constructor that is
not an expression, which `_PyPegen_get_expr_name` is never given). -/
def exprKindNum : Ctor → Int
  | .BoolOp => 1 | .NamedExpr => 2 | .BinOp => 3 | .UnaryOp => 4 | .Lambda => 5 | .IfExp => 6
  | .Dict => 7 | .Set => 8 | .ListComp => 9 | .SetComp => 10 | .DictComp => 11
  | .GeneratorExp => 12 | .Await => 13 | .Yield => 14 | .YieldFrom => 15 | .Compare => 16
  | .Call => 17 | .FormattedValue => 18 | .Interpolation => 19 | .JoinedStr => 20
  | .TemplateStr => 21 | .Constant => 22 | .Attribute => 23 | .Subscript => 24 | .Starred => 25
  | .Name => 26 | .List => 27 | .Tuple => 28 | .Slice => 29
  | _ => 0

/-- `e->kind` as the C enum. -/
def exprKindOf : Ast → Int
  | .node c _ _ => exprKindNum c
  | _ => 0

/-- The `SystemError` of `_PyPegen_get_expr_name`'s default case,
`Parser/action_helpers.c:1154-1157`: `PyErr_Format(PyExc_SystemError, "unexpected expression in
assignment %d (line %d)", e->kind, e->lineno)`. -/
def exprNameErr (e : Ast) : PyError :=
  { cls := "SystemError",
    msg := s!"unexpected expression in assignment {exprKindOf e} (line {(locOf e).lineno})" }

/-- `_PyPegen_get_invalid_target`, `Parser/action_helpers.c`. `kind` is `TARGETS_TYPE`:
0 `STAR_TARGETS`, 1 `DEL_TARGETS`, 2 `FOR_TARGETS`. -/
def invalidTarget (kind : Nat) : Nat → Ast → Ast
  | 0, e => e
  | f + 1, e =>
    let visit (xs : List Ast) : Ast :=
      (xs.map (invalidTarget kind f)).find? (fun x => match x with | .null => false | _ => true)
        |>.getD .null
    match e with
    | .null => .null
    | .node .List (elts :: _) _ => visit (seqOf elts)
    | .node .Tuple (elts :: _) _ => visit (seqOf elts)
    | .node .Starred (v :: _) _ => if kind == 1 then e else invalidTarget kind f v
    | .node .Compare (left :: ops :: _) _ =>
      if kind == 2 then
        match seqOf ops with
        | .node .In _ _ :: _ => invalidTarget kind f left
        | _ => .null
      else e
    | .node .Name _ _ | .node .Subscript _ _ | .node .Attribute _ _ => .null
    | e => e

/-- `PyUnicode` text of code points as a Lean string, for messages. -/
def cpsStr (cs : List Nat) : String := String.ofList (cs.map Char.ofNat)

/-- `PyUnicode_FromFormatV` for the conversions the grammar's messages use. Arguments
are `Ast`s: `%U`/`%s` a string or identifier, `%c` a code point, `%i`/`%d` an int. -/
def formatMsg : List Char → List Ast → String
  | [], _ => ""
  | '%' :: '%' :: r, as => "%" ++ formatMsg r as
  | '%' :: c :: r, a :: as =>
    let piece :=
      match a with
      | .str cs | .ident cs =>
        if c == 'R' then "'" ++ cpsStr cs ++ "'" else cpsStr cs
      | .int i => if c == 'c' then chStr i.toNat else toString i
      | _ => ""
    piece ++ formatMsg r as
  | c :: r, as => String.singleton c ++ formatMsg r as

/-- A message and its arguments out of evaluated action arguments. -/
def msgOf : List Ast → String
  | .str cs :: args => formatMsg (cpsStr cs).toList args
  | _ => ""

/-- `RAISE_SYNTAX_ERROR_KNOWN_RANGE`-style location from two nodes. -/
def raiseRange (cls : String) (a b : Ast) (msg : String) : PM Unit :=
  let la := locOf a
  let lb := locOf b
  raiseErrorKnownLocation cls la.lineno la.colOffset lb.endLineno lb.endColOffset msg

/-- `_PyPegen_ensure_imaginary`/`ensure_real`'s test. -/
def isComplexConst (e : Ast) : Bool :=
  match e with
  | .node .Constant (.const (.complex _ _) :: _) _ => true
  | _ => false

/-- `Constant`-ness of a node. -/
def isConstant (e : Ast) : Bool :=
  match e with
  | .node .Constant _ _ => true
  | _ => false

/-- `Constant` holding an empty `str`. -/
def isEmptyStrConst (e : Ast) : Bool :=
  match e with
  | .node .Constant (.const (.str []) :: _) _ => true
  | _ => false

/-- `_get_interpolation_conversion` -/
def interpolationConversion (debug conversion format : Ast) : Int :=
  match conversion with
  | .null =>
    match debug, format with
    | .null, _ => -1
    | _, .null => 114
    | _, _ => -1
  | c =>
    match fieldOf (recField c 0) "id" with
    | .ident (x :: _) => x
    | _ => -1

/-- `_PyUnicode_IsWhitespace` -/
def isUnicodeSpace (c : Nat) : Bool :=
  (9 ≤ c && c ≤ 13) || (28 ≤ c && c ≤ 32) || c == 0x85 || c == 0xA0 || c == 0x1680
    || (0x2000 ≤ c && c ≤ 0x200A) || c == 0x2028 || c == 0x2029 || c == 0x202F || c == 0x205F
    || c == 0x3000

/-- The inner loop of `_strip_interpolation_debug_expr`, on the reversed text: drop whitespace,
noting a line end. -/
def dropTrailingSpace : List Nat → Bool → List Nat × Bool
  | [], nl => ([], nl)
  | c :: t, nl =>
    if isUnicodeSpace c then dropTrailingSpace t (nl || c == 13 || c == 10) else (c :: t, nl)

/-- The outer loop: whitespace, and a backslash if a line end followed it. -/
def stripDebugTail : Nat → List Nat → List Nat
  | 0, r => r
  | f + 1, r =>
    match r with
    | [] => []
    | _ =>
      match dropTrailingSpace r false with
      | (92 :: t, true) => stripDebugTail f t
      | (r', _) => r'

/-- `_strip_interpolation_debug_expr`, `Parser/action_helpers.c:1544-1576`: whitespace and line
continuations after the debug `=` go with it. Text with no `=` there is kept whole. -/
def stripInterpolationDebugExpr (s : List Nat) : List Nat :=
  match stripDebugTail s.length s.reverse with
  | 61 :: t => t.reverse
  | _ => s

/-- Metadata text of a `Token`/`ResultTokenWithMetadata`, as a Python str constant. -/
def metaConst (m : Ast) : Ast :=
  match m with
  | .str s => .const (.str s)
  | _ => .null

/-- The debug-text bookkeeping shared by `_PyPegen_interpolation` and
`_PyPegen_formatted_value`: `(debug_end_line, debug_end_offset, metadata)`. -/
def debugInfo (conversion format closing : Ast) (endLine endCol : Int) : Int × Int × Ast :=
  match conversion, format with
  | .null, .null =>
    let m := match closing with
      | .tok t => (t.metadata.map Ast.str).getD .null
      | _ => .null
    (endLine, endCol, m)
  | .null, f =>
    let l := locOf (recField f 0)
    (l.lineno, l.colOffset + 1, recField f 1)
  | c, _ =>
    let l := locOf (recField c 0)
    (l.lineno, l.colOffset, recField c 1)

/-- `_PyPegen_formatted_value` -/
def formattedValue (expression debug conversion format closing : Ast)
    (l c el ec : Int) : Ast :=
  let conv := interpolationConversion debug conversion format
  let loc : Loc := ⟨l, c, el, ec⟩
  let fv := mkAt .FormattedValue [expression, .int conv, recField format 0] loc
  match debug with
  | .null => fv
  | _ =>
    let (dline, dcol, mdata) := debugInfo conversion format closing el ec
    let text := mkAt .Constant [metaConst mdata, .null] ⟨l, c + 1, dline, dcol - 1⟩
    mkAt .JoinedStr [.seq [text, fv]] ⟨l, c, dline, dcol⟩

/-- `_PyPegen_interpolation` -/
def interpolation (expression debug conversion format closing : Ast)
    (l c el ec : Int) : Ast :=
  let conv := interpolationConversion debug conversion format
  let (dline, dcol, mdata) := debugInfo conversion format closing el ec
  let exprstr := match mdata with
    | .str s =>
      match debug with
      | .null => .const (.str s)
      | _ => .const (.str (stripInterpolationDebugExpr s))
    | _ => .null
  let loc : Loc := ⟨l, c, el, ec⟩
  let fv := mkAt .Interpolation [expression, exprstr, .int conv, recField format 0] loc
  match debug with
  | .null => fv
  | _ =>
    let text := mkAt .Constant [metaConst mdata, .null] ⟨l, c + 1, dline, dcol - 1⟩
    mkAt .JoinedStr [.seq [text, fv]] ⟨l, c, dline, dcol⟩

/-- `_PyPegen_decode_fstring_part`, `Parser/action_helpers.c`. Fails with `.null`. -/
def decodeFstringPart (isRaw : Bool) (constant : Ast) (tok : Ast) : PM Ast := do
  let cps := match constant with
    | .node .Constant (.const (.str s) :: _) _ => s
    | _ => []
  let bstr := utf8Encode cps
  let bstr' := if bstr == [123, 123] || bstr == [125, 125] then bstr.take 1 else bstr
  let isRaw := isRaw || !bstr.contains 92
  let t := match tok with
    | .tok t => some t
    | _ => none
  match ← decodeString isRaw bstr' t with
  | none =>
    let _ ← raiseDecodeKnown (locOf constant)
    return .null
  | some s => return mkAt .Constant [.const (.str s), .null] (locOf constant)

/-- The item loop of `_get_resized_exprs`. -/
def resizedLoop (isRaw : Bool) (tstr : Bool) (b : Ast) :
    List Ast → List Ast → PM (Option (List Ast))
  | [], acc => return some acc.reverse
  | item :: rest, acc => do
    match item with
    | .node .JoinedStr (values :: _) l =>
      match seqOf values with
      | [first, second] => resizedLoop isRaw tstr b rest (second :: first :: acc)
      | _ =>
        let line := match l with
          | some l => l.lineno
          | none => 0
        setErr { cls := "SystemError",
                 msg := if tstr
                   then s!"unexpected TemplateStr node without debug data in t-string at line {line}"
                   else s!"unexpected JoinedStr node without debug data in f-string at line {line}" }
        return none
    | .node .Constant _ _ =>
      match ← decodeFstringPart isRaw item b with
      | .null => return none
      | it =>
        if isEmptyStrConst it then resizedLoop isRaw tstr b rest acc
        else resizedLoop isRaw tstr b rest (it :: acc)
    | _ => resizedLoop isRaw tstr b rest (item :: acc)

/-- `_get_resized_exprs` -/
def getResizedExprs (a raw b : Ast) (tstr : Bool) : PM (Option (List Ast)) := do
  let quote := match a with
    | .tok t => t.bytes
    | _ => []
  let isRaw := quote.contains 114 || quote.contains 82
  resizedLoop isRaw tstr b (seqOf raw) []

/-- Text of a `Constant` str. -/
def constStr (e : Ast) : List Nat :=
  match e with
  | .node .Constant (.const (.str s) :: _) _ => s
  | _ => []

/-- Value of a `Constant` bytes. -/
def constBytes (e : Ast) : List Nat :=
  match e with
  | .node .Constant (.const (.bytes s) :: _) _ => s
  | _ => []

/-- `Constant.kind` -/
def constKind (e : Ast) : Ast := (fieldOf e "kind")

/-- Fold a run of constants starting with `first`: returns the concatenation, the last
constant, and what follows the run. -/
def foldConsts : List Ast → List Nat → Ast → List Nat × Ast × List Ast
  | [], acc, last => (acc, last, [])
  | e :: rest, acc, last =>
    if isConstant e then foldConsts rest (acc ++ constStr e) e else (acc, last, e :: rest)

/-- `i + 1 < n && asdl_seq_GET(flattened, i + 1)->kind == Constant_kind` -/
def nextIsConstant : List Ast → Bool
  | n :: _ => isConstant n
  | [] => false

/-- The folding loop of `_build_concatenated_str`. `f` is fuel, the list's length. -/
def foldLoop : Nat → List Ast → List Ast
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, e :: rest =>
    if isConstant e && nextIsConstant rest then
      let r := foldConsts rest (constStr e) e
      let l1 := locOf e
      let l2 := locOf r.2.1
      let c := mkAt .Constant [.const (.str r.1), constKind e]
        ⟨l1.lineno, l1.colOffset, l2.endLineno, l2.endColOffset⟩
      if r.1.isEmpty then foldLoop f r.2.2 else c :: foldLoop f r.2.2
    else if isEmptyStrConst e then foldLoop f rest
    else e :: foldLoop f rest

/-- `_build_concatenated_str`, `Parser/action_helpers.c`. -/
def buildConcatenatedStr (strings : Ast) : List Ast :=
  let flat := (seqOf strings).flatMap fun e =>
    match e with
    | .node .JoinedStr (v :: _) _ | .node .TemplateStr (v :: _) _ => seqOf v
    | e => [e]
  foldLoop (flat.length + 1) flat

/-- `PyBytes_CheckExact(elem->v.Constant.value)` on a `Constant`. -/
def isBytesConst (e : Ast) : Bool :=
  match e with
  | .node .Constant (.const (.bytes _) :: _) _ => true
  | _ => false

/-- `_PyPegen_concatenate_strings`, `Parser/action_helpers.c:1970-2029`: the kind loop (a
`Constant` is bytes or unicode, anything else an f-string; a `TemplateStr` is `assert(0)`, which
`Grammar/python.gram` never reaches), the mixing check, a lone literal returned as is, two or more
bytes or str literals joined by `_build_concatenated_bytes`/`_build_concatenated_unicode` with the
kind of the first, and otherwise `_build_concatenated_joined_str`. -/
def concatenateStrings (strings : Ast) (l c el ec : Int) : PM Ast := do
  let xs := seqOf strings
  let bytesFound := xs.any isBytesConst
  let unicodeFound := xs.any fun e => isConstant e && !isBytesConst e
  let fFound := xs.any fun e => !isConstant e
  if (unicodeFound || fFound) && bytesFound then
    raiseError0 "SyntaxError" "cannot mix bytes and nonbytes literals"
    return .null
  let loc : Loc := ⟨l, c, el, ec⟩
  if !fFound then
    match xs with
    | [x] => return x
    | first :: _ =>
      if bytesFound then
        return mkAt .Constant [.const (.bytes (xs.flatMap constBytes)), constKind first] loc
      else
        return mkAt .Constant [.const (.str (xs.flatMap constStr)), constKind first] loc
    | [] => return .null
  return mkAt .JoinedStr [.seq (buildConcatenatedStr strings)] loc

/-- `_PyPegen_setup_full_format_spec`, `Parser/action_helpers.c`. -/
def setupFullFormatSpec (colon spec : Ast) (l c el ec : Int) : PM Ast := do
  match spec with
  | .null => return .null
  | _ =>
    let kept := (seqOf spec).filter (fun e => !isEmptyStrConst e)
    let loc : Loc := ⟨l, c, el, ec⟩
    let simple := match kept with
      | [] => true
      | [x] => isConstant x
      | _ => false
    let res ←
      if simple then pure (mkAt .JoinedStr [.seq kept] loc)
      else concatenateStrings (.seq kept) l c el ec
    match res with
    | .null => return .null
    | _ =>
      let m := match colon with
        | .tok t => (t.metadata.map Ast.str).getD .null
        | _ => .null
      return rec_ .PResultTokenWithMetadata [res, m]

/-- `_PyPegen_collect_call_seqs`, `Parser/action_helpers.c`. -/
def collectCallSeqs (a b : Ast) (l c el ec : Int) : Ast :=
  let loc : Loc := ⟨l, c, el, ec⟩
  let dummy := rec_ .PDummy []
  match b with
  | .null => mkAt .Call [dummy, a, .null] loc
  | _ =>
    let xs := seqOf b
    let isKw (k : Ast) := match recField k 1 with
      | .int 0 => false
      | _ => true
    let starreds := (xs.filter (! isKw ·)).map (recField · 0)
    let kws := (xs.filter isKw).map (recField · 0)
    mkAt .Call [dummy, .seq (seqOf a ++ starreds), .seq kws] loc

/-- `_PyPegen_get_last_comprehension_item` -/
def lastComprehensionItem (c : Ast) : Ast :=
  match (seqOf (fieldOf c "ifs")).getLast? with
  | some x => x
  | none => fieldOf c "iter"

/-- `TOK_GET_STRING_PREFIX` -/
def tokPrefix (p : PS) : Nat := if p.tok.mode.tstring then ch! 't' else ch! 'f'

/-- What a token adds in `_PyPegen_seq_count_dots`: 3 for `ELLIPSIS`, 1 for `DOT`. -/
def dotWeight (t : Ast) : Int :=
  match t with
  | .tok t => if t.type == TokKind.ELLIPSIS.num then 3 else 1
  | _ => 0

/-- `_PyPegen_seq_count_dots`, `Parser/action_helpers.c:143-161`. -/
def countDots (dots : Ast) : Int := (seqOf dots).foldl (fun acc t => acc + dotWeight t) 0

/-- `_PyPegen_check_legacy_stmt`, `Parser/action_helpers.c:951-962`. -/
def isLegacyStmt (e : Ast) : Bool :=
  match e with
  | .node .Name (.ident id :: _) _ => id == [112, 114, 105, 110, 116] || id == [101, 120, 101, 99]
  | _ => false

/-- `_PyPegen_raise_error_for_missing_comma`, `Parser/action_helpers.c:965-991`. -/
def raiseErrorForMissingComma (a b : Ast) : PM Ast := do
  if isLegacyStmt a then return .null
  let p ← get
  if (p.tokenAt (p.mark - 1)).level == 0 then return .null
  let la := locOf a
  let msg := "invalid syntax. Perhaps you forgot a comma?"
  if la.endLineno > la.lineno then
    raiseErrorKnownLocation "SyntaxError" la.endLineno la.colOffset la.endLineno la.endColOffset msg
  else
    let lb := locOf b
    raiseErrorKnownLocation "SyntaxError" la.lineno la.colOffset lb.endLineno lb.endColOffset msg
  return .null

/-- `_PyErr_EmitSyntaxWarning`, `Python/errors.c:1980-1997`: `PyErr_WarnExplicitObject` with
`SyntaxWarning`, 0 on success. When the filter makes the warning an exception, it is replaced by a
`SyntaxError` with the warning's message at the given location (`_PyErr_RaiseSyntaxError`,
`:1956-1973`) and -1 is returned. Its `text` is `PyErr_ProgramTextObject(filename, lineno)`, `None`
here: `filename` never names a readable file in this model. -/
def emitSyntaxWarning (msg : String) (lineno col endLineno endCol : Int) : PM Int := do
  if (← get).cfg.warnErrors.contains "SyntaxWarning" then
    setErr { cls := "SyntaxError", msg, lineno := some lineno, offset := some col,
             endLineno := some endLineno, endOffset := some endCol, text := none }
    return -1
  modify fun p =>
    { p with tok := { p.tok with warnings := ("SyntaxWarning", msg, lineno) :: p.tok.warnings } }
  return 0

/-- The message of `_warn_relative_import_of_lazy`, `Parser/action_helpers.c:2052-2065`: `buf` is
`count` dots. -/
def lazyMsg (dots : Ast) : String :=
  let buf := String.ofList (List.replicate (countDots dots).toNat '.')
  s!"'from {buf} lazy import' is the same as 'from {buf}lazy import'; "
    ++ s!"did you mean 'lazy from {buf} import'?"

/-- `_warn_relative_import_of_lazy`, `Parser/action_helpers.c:2031-2079`: 0, or the result of
`_PyErr_EmitSyntaxWarning` (`:2071-2078`) at the module name, columns made one-based. The
`PyMem_RawMalloc` and `PyUnicode_FromFormat` failures (`:2052-2068`) are allocation failure, outside
the model. `dots` is never empty here (`level > 0`), and its elements are tokens. -/
def warnRelativeImportOfLazy (dots module : Ast) : PM Int := do
  let p ← get
  if p.callInvalidRules then return 0
  let m := locOf module
  match (seqOf dots).getLast? with
  | some (.tok d) =>
    if d.endLineno == m.lineno && d.endColOffset == m.colOffset then return 0
    emitSyntaxWarning (lazyMsg dots) m.lineno (m.colOffset + 1) m.endLineno (m.endColOffset + 1)
  | _ => return 0

/-- `alias->name` is `barry_as_FLUFL`. -/
def isBarryAlias (al : Ast) : Bool :=
  match fieldOf al "name" with
  | .ident s => s == "barry_as_FLUFL".toList.map Char.toNat
  | _ => false

/-- `module == "__future__"` -/
def isFutureModule (m : Ast) : Bool :=
  match fieldOf m "id" with
  | .ident s => s == "__future__".toList.map Char.toNat
  | _ => false

/-- `module == "lazy"` -/
def isLazyModule (m : Ast) : Bool :=
  match fieldOf m "id" with
  | .ident s => s == [108, 97, 122, 121]
  | _ => false

/-- `x != NULL` -/
def hasValue : Ast → Bool
  | .null => false
  | _ => true

/-- `_PyPegen_checked_from_import`, `Parser/action_helpers.c:2081-2114`. Fails with `.null`: the
`lazy from __future__` error (`:2089-2093`) and a failed warning (`:2108-2110`). -/
def checkedFromImport (dots moduleName names lazy : Ast) (l c el ec : Int) : PM Ast := do
  let level := countDots dots
  if level == 0 && isFutureModule moduleName then
    if hasValue lazy then
      raiseRange "SyntaxError" lazy lazy "lazy from __future__ import is not allowed"
      return .null
    if (seqOf names).any isBarryAlias then
      modify fun p => { p with flagBarry := true, tok := { p.tok with barryAsBdfl := true } }
  else if level > 0 && !hasValue lazy && isLazyModule moduleName then
    if (← warnRelativeImportOfLazy dots moduleName) < 0 then return .null
  return mkAst .ImportFrom
    [fieldOf moduleName "id", names, .int level, .int (if hasValue lazy then 1 else 0),
     .int l, .int c, .int el, .int ec]

/-- `KeywordOrStarred.is_keyword` -/
def isKeywordRec (k : Ast) : Bool :=
  match recField k 1 with
  | .int 0 => false
  | _ => true

/-- `_PyPegen_ensure_imaginary`, `Parser/action_helpers.c`. -/
def ensureImaginary (e : Ast) : PM Ast := do
  if !(isConstant e && isComplexConst e) then
    let l := locOf e
    raiseErrorKnownLocation "SyntaxError" l.lineno l.colOffset l.endLineno l.endColOffset
      "imaginary number required in complex literal"
    return .null
  return e

/-- `_PyPegen_ensure_real`, `Parser/action_helpers.c`. -/
def ensureReal (e : Ast) : PM Ast := do
  if !isConstant e || isComplexConst e then
    let l := locOf e
    raiseErrorKnownLocation "SyntaxError" l.lineno l.colOffset l.endLineno l.endColOffset
      "real number required in complex literal"
    return .null
  return e

/-- `_PyPegen_check_barry_as_flufl`, `Parser/action_helpers.c`. -/
def checkBarry (t : Ast) : PM Ast := do
  let p ← get
  let s := match t with
    | .tok t => t.bytes
    | _ => []
  if p.flagBarry && s != [60, 62] then
    raiseError0 "SyntaxError" "with Barry as BDFL, use '<>' instead of '!='"
    return .int (-1)
  if !p.flagBarry then return .int (if s == [33, 61] then 0 else 1)
  return .int 0

/-- The conversion name does not start where the `!` ends. -/
def notAdjacent (a0 a1 : Ast) : Bool :=
  (locOf a0).lineno != (locOf a1).lineno || (locOf a0).endColOffset != (locOf a1).colOffset

/-- `_PyPegen_check_fstring_conversion`, `Parser/action_helpers.c:1005-1027`: the adjacency check
first, then the conversion name (one of `s`, `r`, `a`), whose `%R` is `repr` of the identifier
(`'a\u200d'` for a name with a zero-width joiner); success is `result_token_with_metadata`
(`:993-1003`) of the name and the `!` token's metadata. -/
def checkFstringConversion (a0 a1 : Ast) : PM Ast := do
  let lt := locOf a0
  let lc := locOf a1
  let pfx := tokPrefix (← get)
  if notAdjacent a0 a1 then
    let pc := chStr pfx
    raiseRange "SyntaxError" a0 a1
      s!"{pc}-string: conversion type must come right after the exclamation mark"
    return .null
  let id := match fieldOf a1 "id" with
    | .ident s => s
    | _ => []
  let first := id.headD 0
  if id.length > 1 || !(first == ch! 's' || first == ch! 'r' || first == ch! 'a') then
    raiseErrorKnownLocation "SyntaxError" lc.lineno lc.colOffset lc.endLineno lc.endColOffset
      s!"{chStr pfx}-string: invalid conversion character {cpsStr (Unparse.strRepr id)}: expected 's', 'r', or 'a'"
    return .null
  let m := match a0 with
    | .tok t => (t.metadata.map Ast.str).getD .null
    | _ => .null
  return rec_ .PResultTokenWithMetadata [a1, m]

/-- The message of `_PyPegen_arguments_parsing_error`. -/
def argumentErrorMessage (kwargUnpacking : Bool) : String :=
  if kwargUnpacking then "positional argument follows keyword argument unpacking"
  else "positional argument follows keyword argument"

/-- `_PyPegen_arguments_parsing_error`, `Parser/action_helpers.c`. -/
def argumentsParsingError (e : Ast) : PM Ast := do
  let kw := (seqOf (fieldOf e "keywords")).any fun k =>
    match fieldOf k "arg" with
    | .null => true
    | _ => false
  raiseError0 "SyntaxError" (argumentErrorMessage kw)
  return .null

/-- `_PyPegen_nonparen_genexp_in_call`, `Parser/action_helpers.c`. -/
def nonparenGenexp (a0 a1 : Ast) : PM Ast := do
  let cargs := seqOf (fieldOf a0 "args")
  if cargs.length ≤ 1 then return .null
  let last := (seqOf a1).getLastD .null
  raiseRange "SyntaxError" (cargs.getLastD .null) (lastComprehensionItem last)
    "Generator expression must be parenthesized"
  return .null

/-- `_PyPegen_register_stmts`, `Parser/action_helpers.c`. -/
def registerStmts (a0 : Ast) : PM Ast := do
  let p ← get
  if !p.callInvalidRules then return a0
  match (seqOf a0).getLast? with
  | none => return a0
  | some last =>
    let l := locOf last
    if p.lastStmt.1 > l.lineno then return a0
    modify fun p => { p with lastStmt := (l.lineno, l.colOffset) }
    return a0

/-- Call a helper of `Parser/action_helpers.c`, or a macro of `Parser/pegen.h`. -/
def callHelper (h : Helper) (args : List Ast) : PM Ast := do
  let a0 := args.getD 0 .null
  let a1 := args.getD 1 .null
  let a2 := args.getD 2 .null
  let int (i : Nat) : Int := match args.getD i .null with
    | .int v => v
    | _ => 0
  match h with
  | .dummy_name => return rec_ .PDummy []
  | .singleton_seq => return .seq [a0]
  | .seq_insert_in_front => return .seq (a0 :: seqOf a1)
  | .seq_append_to_end => return .seq (seqOf a0 ++ [a1])
  | .seq_flatten => return .seq ((seqOf a0).flatMap seqOf)
  | .seq_first_item => return (seqOf a0).headD .null
  | .seq_last_item => return (seqOf a0).getLastD .null
  | .join_names_with_dot =>
    -- `_PyPegen_join_names_with_dot`, `Parser/action_helpers.c:123-139`: `"%U.%U"` of the two
    -- ids, a `Load` `Name` from the first name's start to the second's end.
    let id (e : Ast) := match fieldOf e "id" with
      | .ident s => s
      | _ => []
    let la := locOf a0
    let lb := locOf a1
    return mkAt .Name [.ident (id a0 ++ [46] ++ id a1), rec_ .Load []]
      ⟨la.lineno, la.colOffset, lb.endLineno, lb.endColOffset⟩
  | .seq_count_dots => return .int (countDots a0)
  | .alias_for_star =>
    return mkAst .alias_ ([.ident [42], .null] ++ args)
  | .map_names_to_ids => return .seq ((seqOf a0).map (fieldOf · "id"))
  | .cmpop_expr_pair => return rec_ .PCmpopExprPair [a0, a1]
  | .get_cmpops => return .seq ((seqOf a0).map (recField · 0))
  | .get_exprs => return .seq ((seqOf a0).map (recField · 1))
  | .set_expr_context => return setExprContext a1 100000 a0
  | .key_value_pair => return rec_ .PKeyValuePair [a0, a1]
  | .get_keys => return .seq ((seqOf a0).map (recField · 0))
  | .get_values => return .seq ((seqOf a0).map (recField · 1))
  | .key_pattern_pair => return rec_ .PKeyPatternPair [a0, a1]
  | .get_pattern_keys => return .seq ((seqOf a0).map (recField · 0))
  | .get_patterns => return .seq ((seqOf a0).map (recField · 1))
  | .name_default_pair => return rec_ .PNameDefaultPair [addTypeComment a0 a2, a1]
  | .slash_with_default => return rec_ .PSlashWithDefault [a0, a1]
  | .star_etc => return rec_ .PStarEtc [a0, a1, a2]
  | .join_sequences => return joinSeq a0 a1
  | .make_arguments =>
    return makeArguments a0 a1 a2 (args.getD 3 .null) (args.getD 4 .null)
  | .empty_arguments => return makeArguments .null .null .null .null .null
  | .augoperator => return rec_ .PAugOperator [a0]
  | .function_def_decorators =>
    match a1 with
    | .node c [n, ar, b, _, r, tc, tp] l => return .node c [n, ar, b, a0, r, tc, tp] l
    | x => return x
  | .class_def_decorators =>
    match a1 with
    | .node c [n, ba, kw, b, _, tp] l => return .node c [n, ba, kw, b, a0, tp] l
    | x => return x
  | .keyword_or_starred => return rec_ .PKeywordOrStarred [a0, a1]
  | .seq_extract_starred_exprs =>
    let xs := (seqOf a0).filter (fun k => !isKeywordRec k)
    return if xs.isEmpty then .null else .seq (xs.map (recField · 0))
  | .seq_delete_starred_exprs =>
    let xs := (seqOf a0).filter isKeywordRec
    return if xs.isEmpty then .null else .seq (xs.map (recField · 0))
  | .ensure_imaginary => ensureImaginary a0
  | .ensure_real => ensureReal a0
  | .make_module =>
    let ti := (← get).typeIgnores.map fun (line, tag) =>
      mkAst .TypeIgnore [.int line, .str (utf8Decode tag)]
    return mkAst .Module [a0, .seq ti]
  | .add_type_comment_to_arg => return addTypeComment a0 a1
  | .NEW_TYPE_COMMENT => return typeCommentOf a0
  | .check_barry_as_flufl => checkBarry a0
  | .check_legacy_stmt => return .int (if isLegacyStmt a0 then 1 else 0)
  | .raise_error_for_missing_comma => raiseErrorForMissingComma a0 a1
  | .tokens_are_adjacent =>
    match a0, a1 with
    | .tok x, .tok y =>
      return .int (if x.endLineno == y.lineno && x.endColOffset == y.colOffset then 1 else 0)
    | _, _ => return .int 0
  | .check_fstring_conversion => checkFstringConversion a0 a1
  | .setup_full_format_spec => setupFullFormatSpec a0 a1 (int 2) (int 3) (int 4) (int 5)
  | .get_expr_name =>
    match exprName a0 with
    | some s => return .str (s.toList.map Char.toNat)
    | none =>
      setErr (exprNameErr a0)
      return .null
  | .get_last_comprehension_item => return lastComprehensionItem a0
  | .collect_call_seqs => return collectCallSeqs a0 a1 (int 2) (int 3) (int 4) (int 5)
  | .arguments_parsing_error => argumentsParsingError a0
  | .nonparen_genexp_in_call => nonparenGenexp a0 a1
  | .template_str =>
    match ← getResizedExprs a0 a1 a2 true with
    | none => return .null
    | some xs =>
      let la := locOf a0
      let lb := locOf a2
      return mkAt .TemplateStr [.seq xs] ⟨la.lineno, la.colOffset, lb.endLineno, lb.endColOffset⟩
  | .joined_str =>
    match ← getResizedExprs a0 a1 a2 false with
    | none => return .null
    | some xs =>
      let la := locOf a0
      let lb := locOf a2
      return mkAt .JoinedStr [.seq xs] ⟨la.lineno, la.colOffset, lb.endLineno, lb.endColOffset⟩
  | .decoded_constant_from_token =>
    match a0 with
    | .tok t =>
      let p ← get
      let raw := p.tok.insideFString && p.tok.mode.raw
      match ← decodeString raw t.bytes (some t) with
      | none => return .null
      | some s => return mkAt .Constant [.const (.str s), .null] (tokLoc t)
    | _ => return .null
  | .constant_from_token =>
    match a0 with
    | .tok t => return mkAt .Constant [.const (.str (utf8Decode t.bytes)), .null] (tokLoc t)
    | _ => return .null
  | .constant_from_string =>
    match a0 with
    | .tok t =>
      match ← parseString t with
      | .fail =>
        let _ ← raiseDecodeError
        return .null
      | v =>
        let c : PyConst := match v with
          | .str s => .str s
          | .bytes s => .bytes s
          | .fail => .none
        let kind : Ast := if t.bytes.head? == some 117 then .str [117] else .null
        return mkAt .Constant [.const c, kind] (tokLoc t)
    | _ => return .null
  | .interpolation =>
    return interpolation a0 a1 a2 (args.getD 3 .null) (args.getD 4 .null)
      (int 5) (int 6) (int 7) (int 8)
  | .formatted_value =>
    return formattedValue a0 a1 a2 (args.getD 3 .null) (args.getD 4 .null)
      (int 5) (int 6) (int 7) (int 8)
  | .concatenate_strings => concatenateStrings a0 (int 1) (int 2) (int 3) (int 4)
  | .concatenate_tstrings =>
    return mkAt .TemplateStr [.seq (buildConcatenatedStr a0)] ⟨int 1, int 2, int 3, int 4⟩
  | .checked_from_import =>
    checkedFromImport a0 a1 (args.getD 2 .null) (args.getD 3 .null) (int 4) (int 5) (int 6) (int 7)
  | .register_stmts => registerStmts a0
  | .interactive_exit => return .null
  | .PyErr_Occurred => return .int (if (← get).errOccurred then 1 else 0)
  | .asdl_seq_LEN => return .int ((seqOf a0).length : Int)
  | .asdl_seq_GET => return (seqOf a0).getD (int 1).toNat .null
  | .PyBytes_AS_STRING =>
    return a0
  | .RAISE_SYNTAX_ERROR =>
    raiseError "SyntaxError" false (msgOf args)
    return .null
  | .RAISE_INDENTATION_ERROR =>
    raiseError "IndentationError" false (msgOf args)
    return .null
  | .RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN =>
    raiseError "SyntaxError" true (msgOf args)
    return .null
  | .RAISE_SYNTAX_ERROR_KNOWN_LOCATION =>
    raiseRange "SyntaxError" a0 a0 (msgOf (args.drop 1))
    return .null
  | .RAISE_SYNTAX_ERROR_KNOWN_RANGE =>
    raiseRange "SyntaxError" a0 a1 (msgOf (args.drop 2))
    return .null
  | .RAISE_SYNTAX_ERROR_STARTING_FROM =>
    let l := locOf a0
    raiseErrorKnownLocation "SyntaxError" l.lineno l.colOffset (-5) (-5) (msgOf (args.drop 1))
    return .null
  | .RAISE_SYNTAX_ERROR_INVALID_TARGET =>
    match invalidTarget (int 0).toNat 100000 a1 with
    | .null => return .null
    | t =>
      let what := (exprName t).getD ""
      let msg := if int 0 == 0 || int 0 == 2 then s!"cannot assign to {what}"
        else s!"cannot delete {what}"
      raiseRange "SyntaxError" t t msg
      return .null
  | .RAISE_ERROR_KNOWN_LOCATION =>
    raiseErrorKnownLocation "SyntaxError" (int 1) (int 2) (int 3) (int 4)
      (msgOf (args.drop 5))
    return .null

/-- C truth value: non-`NULL`, nonzero. -/
def truth : Ast → Bool
  | .null => false
  | .int 0 => false
  | _ => true

/-- The location values `EXTRA` expands to. -/
structure Extra where
  startLine : Int := 0
  startCol : Int := 0
  endLine : Int := 0
  endCol : Int := 0
  deriving Inhabited

/-- `x->lineno` etc., on a node or a token, and members of parser records. -/
def attrOf (a : Ast) (name : String) : Ast :=
  let l := locOf a
  if name == "lineno" then .int l.lineno
  else if name == "col_offset" then .int l.colOffset
  else if name == "end_lineno" then .int l.endLineno
  else if name == "end_col_offset" then .int l.endColOffset
  else if name == "level" then
    match a with
    | .tok t => .int t.level
    | _ => .null
  else if name == "bytes" then
    match a with
    | .tok t => .str (utf8Decode t.bytes)
    | _ => .null
  else if name == "key" then recField a 0
  else if name == "value" then recField a 1
  else .null

/-- Evaluate a C action. -/
def evalA (env : Array Ast) (ex : Extra) : AE → PM Ast
  | .var i => return env.getD i .null
  | .null => return .null
  | .extra0 => return .int ex.startLine
  | .extra1 => return .int ex.startCol
  | .extra2 => return .int ex.endLine
  | .extra3 => return .int ex.endCol
  | .lastTok => do
    let p ← get
    return .tok (p.tokenAt (p.mark - 1))
  | .tokState => return .null
  | .pyNone => return .const .none
  | .pyTrue => return .const .true_
  | .pyFalse => return .const .false_
  | .pyEllipsis => return .const .ellipsis
  | .int n => return .int n
  | .str s => return .str (s.toList.map Char.toNat)
  | .ctor c => return .node c [] none
  | .mk c args => do return mkAst c (← evalList env ex args)
  | .call h args => do callHelper h (← evalList env ex args)
  | .check e => do
    let v ← evalA env ex e
    match v with
    | .null => modify fun p => { p with errorIndicator := true }
    | _ => pure ()
    return v
  | .checkNull e => do
    let v ← evalA env ex e
    match v with
    | .null =>
      if (← get).errOccurred then modify fun p => { p with errorIndicator := true }
    | _ => pure ()
    return v
  | .checkVersion v msg node => do
    let n ← evalA env ex node
    match n with
    | .null =>
      modify fun p => { p with errorIndicator := true }
      return .null
    | _ =>
      let ver ← evalA env ex v
      let m ← evalA env ex msg
      let version := match ver with
        | .int i => i
        | _ => 0
      if ((← get).featureVersion : Int) < version then
        modify fun p => { p with errorIndicator := true }
        let text := match m with
          | .str s => cpsStr s
          | _ => ""
        raiseError0 "SyntaxError" s!"{text} only supported in Python 3.{version} and greater"
        return .null
      return n
  | .ite c a b => do
    if truth (← evalA env ex c) then evalA env ex a else evalA env ex b
  | .and_ a b => do
    if truth (← evalA env ex a) then
      return .int (if truth (← evalA env ex b) then 1 else 0)
    return .int 0
  | .or_ a b => do
    if truth (← evalA env ex a) then return .int 1
    return .int (if truth (← evalA env ex b) then 1 else 0)
  | .eq a b => do
    let x ← evalA env ex a
    let y ← evalA env ex b
    return .int (if x == y then 1 else 0)
  | .not_ a => do return .int (if truth (← evalA env ex a) then 0 else 1)
  | .sub a b => do
    match ← evalA env ex a, ← evalA env ex b with
    | .int x, .int y => return .int (x - y)
    | _, _ => return .null
  | .add a b => do
    match ← evalA env ex a, ← evalA env ex b with
    | .int x, .int y => return .int (x + y)
    | _, _ => return .null
  | .field e name => do return fieldOf (← evalA env ex e) name
  | .kind e => do
    match ← evalA env ex e with
    | .node .PAugOperator [k] _ => return k
    | .node c _ _ => return .node c [] none
    | _ => return .null
  | .attr e name => do return attrOf (← evalA env ex e) name
where
  evalList (env : Array Ast) (ex : Extra) : List AE → PM (List Ast)
    | [] => return []
    | a :: as => do
      let v ← evalA env ex a
      return v :: (← evalList env ex as)

end PyLean.PyGrammar.Peg
