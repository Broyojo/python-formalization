import PyLean.DiffCore
import PyLean.TypeObj.Harness
import PyLean.TypeObj.StructSeqDiff
import PyLean.TypeObj.FromSpec

/-! Differential-testing handler for `typeobj` cases (`"mod": "typeobj"`).

A case carries a scenario as JSON trees (see `difftest/typeobj_diff.py`): `codes` holds
the bodies of functions and classes, `main` the top-level statements. The result is the
observable trace: the `log` events and the `probe` outcomes, in order. -/

namespace PyLean.TypeObj

open Lean PyLean PyLean.Diff

def parseLit : Json → Except String Val
  | .null => pure .none
  | .bool b => pure (.bool b)
  | .str s => pure (.str s)
  | .num n =>
    match (Json.num n).getInt? with
    | .ok i => pure (.int i)
    | .error e => throw e
  | .arr a =>
    match a.toList with
    | [.str "notimpl"] => pure .notImpl
    | [.str "ellipsis"] => pure .ellipsis
    | [.str "bigint", .str s] =>
      match s.toInt? with
      | some i => pure (.int i)
      | none => throw "bad bigint"
    | [.str "float", .str s] =>
      match s.toNat? with
      | some b => pure (.float b)
      | none => throw "bad float"
    | _ => throw "bad literal"
  | _ => throw "bad literal"

def parseBinOp : String → Except String BinOpE
  | "+" => pure .add | "-" => pure .sub | "*" => pure .mul | "@" => pure .matmul
  | "%" => pure .mod | "//" => pure .floordiv | "/" => pure .truediv
  | "<<" => pure .lshift | ">>" => pure .rshift | "&" => pure .band | "|" => pure .bor
  | "^" => pure .bxor | "**" => pure .pow
  | s => throw s!"bad op {s}"

def parseCmp : String → Except String CmpOp
  | "<" => pure .lt | "<=" => pure .le | "==" => pure .eq
  | "!=" => pure .ne | ">" => pure .gt | ">=" => pure .ge
  | s => throw s!"bad cmp {s}"

mutual
  partial def parseExpr (j : Json) : Except String Expr := do
    let a ← j.getArr?
    let tag ← (a.getD 0 .null).getStr?
    match tag, a.toList.drop 1 with
    | "lit", [v] => .lit <$> parseLit v
    | "name", [.str n] => pure (.name n)
    | "attr", [e, .str n] => do pure (.attr (← parseExpr e) n)
    | "call", [f, args, kw] =>
      pure (.call (← parseExpr f) (← parseExprs args) (← parseKw kw))
    | "bin", [.str op, x, y] =>
      pure (.bin (← parseBinOp op) (← parseExpr x) (← parseExpr y))
    | "un", [.str op, x] =>
      let o ← match op with
        | "-" => pure UnOpE.neg
        | "+" => pure .pos
        | "~" => pure .invert
        | "not" => pure .not
        | _ => throw "bad unop"
      pure (.un o (← parseExpr x))
    | "cmp", [.str op, x, y] =>
      pure (.cmp (← parseCmp op) (← parseExpr x) (← parseExpr y))
    | "is", [x, y] => pure (.isE (← parseExpr x) (← parseExpr y))
    | "in", [x, y] => pure (.inE (← parseExpr x) (← parseExpr y))
    | "notin", [x, y] => pure (.notInE (← parseExpr x) (← parseExpr y))
    | "tuple", [es] => .tupleE <$> parseExprs es
    | "list", [es] => .listE <$> parseExprs es
    | "dict", [ps] =>
      let items ← ps.getArr?
      let mut out : List (Expr × Expr) := []
      for it in items.toList do
        let p ← it.getArr?
        out := out ++ [(← parseExpr (p.getD 0 .null), ← parseExpr (p.getD 1 .null))]
      pure (.dictE out)
    | "sub", [x, k] => pure (.sub (← parseExpr x) (← parseExpr k))
    | "super", [] => pure .super0
    | t, _ => throw s!"bad expr {t}"

  partial def parseExprs (j : Json) : Except String (List Expr) := do
    let a ← j.getArr?
    a.toList.mapM parseExpr

  partial def parseKw (j : Json) : Except String (List (Name × Expr)) := do
    let a ← j.getArr?
    a.toList.mapM fun it => do
      let p ← it.getArr?
      let k ← (p.getD 0 .null).getStr?
      pure (k, ← parseExpr (p.getD 1 .null))
end

def parseOptName (j : Json) : Except String (Option Name) :=
  match j with
  | .null => pure none
  | .str s => pure (some s)
  | _ => throw "bad name"

def parseParams (j : Json) : Except String ParamSpec := do
  let names (k : String) : Except String (List Name) := do
    let a ← (← field j k).getArr?
    a.toList.mapM (·.getStr?)
  pure {
    pos := ← names "pos", posonly := ← getNat j "posonly", kwonly := ← names "kwonly"
    varargs := ← parseOptName (← field j "varargs")
    varkw := ← parseOptName (← field j "varkw")
    defaults := ← parseExprs (← field j "defaults")
    kwdefaults := ← parseKw (← field j "kwdefaults") }

partial def parseStmt (j : Json) : Except String Stmt := do
  let a ← j.getArr?
  let tag ← (a.getD 0 .null).getStr?
  match tag, a.toList.drop 1 with
  | "expr", [e] => .expr <$> parseExpr e
  | "assign", [.str n, e] => .assign n <$> parseExpr e
  | "setattr", [o, .str n, e] => pure (.setattr (← parseExpr o) n (← parseExpr e))
  | "delattr", [o, .str n] => pure (.delattr (← parseExpr o) n)
  | "setitem", [o, k, e] => pure (.setitem (← parseExpr o) (← parseExpr k) (← parseExpr e))
  | "delitem", [o, k] => pure (.delitem (← parseExpr o) (← parseExpr k))
  | "aug", [.str n, .str op, e] => pure (.aug n (← parseBinOp op) (← parseExpr e))
  | "ret", [e] => .ret <$> parseExpr e
  | "raise", [e] => .raiseS <$> parseExpr e
  | "raisefrom", [e, c] => pure (.raiseFrom (← parseExpr e) (← parseExpr c))
  | "log", [.str s] => pure (.log s)
  | "def", [.str n, .str q, p, c] => pure (.defS n q (← parseParams p) (← c.getNat?))
  | "class", [.str n, bases, kw, .bool cell, c] =>
    pure (.classS n (← parseExprs bases) (← parseKw kw) cell (← c.getNat?))
  | "try", [b, e, .str v, h] =>
    let bs ← (← b.getArr?).toList.mapM parseStmt
    let hs ← (← h.getArr?).toList.mapM parseStmt
    pure (.tryS bs (← parseExpr e) v hs)
  | "if", [c, t, e] =>
    let ts ← (← t.getArr?).toList.mapM parseStmt
    let es ← (← e.getArr?).toList.mapM parseStmt
    pure (.ifS (← parseExpr c) ts es)
  | "probe", [.str t, e] => .probe t <$> parseExpr e
  | "probes", [.str t, b] =>
    .probeS t <$> (← b.getArr?).toList.mapM parseStmt
  | t, _ => throw s!"bad stmt {t}"

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "scenario" =>
    let codes ← (← (← field j "codes").getArr?).mapM fun b => do
      (← b.getArr?).toList.mapM parseStmt
    let main ← (← (← field j "main").getArr?).toList.mapM parseStmt
    pure (Json.mkObj [("ok", toJson (runScenario codes main))])
  | "fromspec_sizes" =>
    let e ← getInt j "extra"
    let sp ← getInt j "spec"
    pure (Json.mkObj [("ok", toJson (sizedHeaptypes e sp))])
  | "ss_newtype" | "ss_inittype" | "ss_repr" | "ss_capi" | "ss_new" | "ss_reduce" | "ss_replace" =>
    StructSeq.Diff.run fn j
  | _ => throw s!"unknown fn {fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.TypeObj
