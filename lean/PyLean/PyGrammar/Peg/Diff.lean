import PyLean.DiffCore
import PyLean.PyGrammar.Peg.Interp

/-! Difftest handler for the PEG interpreter and parser actions: `fn` starts with `peg.`. -/

namespace PyLean.PyGrammar.Peg

open Lean PyLean PyLean.Diff Lexer

/-- Encode an optional int the way `pygrammar_diff.py` prints it. -/
def optI : Option Int → String
  | some i => toString i
  | none => "None"

/-- An exception as class plus a message that carries the location, so that
`common.agree` compares all of it. -/
def encErr (e : PyError) : Json :=
  let text := match e.text with
    | some t => "[" ++ ",".intercalate (t.map toString) ++ "]"
    | none => "None"
  Json.mkObj [("exc", toJson e.cls),
    ("msg", toJson s!"{e.msg}|{optI e.lineno}|{optI e.offset}|{optI e.endLineno}|{optI e.endOffset}|{text}")]

/-- Read the oracle tables of a case. -/
def getCfg (j : Json) : Except String Cfg := do
  let ucn : List (String × Nat) ← match j.getObjVal? "ucn" with
    | .ok v => do
      let items ← v.getArr?
      items.toList.mapM fun it => do
        let a ← it.getArr?
        return (← a[0]!.getStr?, ← a[1]!.getNat?)
    | .error _ => pure []
  let nfkc : List (List Nat × List Nat) ← match j.getObjVal? "nfkc" with
    | .ok v => do
      let items ← v.getArr?
      items.toList.mapM fun it => do
        let a ← it.getArr?
        return (← fromJson? a[0]!, ← fromJson? a[1]!)
    | .error _ => pure []
  return { ucn := ucn.map (fun (n, c) => (n.toList.map Char.toNat, c)), nfkc }

/-- `compile(src, "<unknown>", mode, PyCF_ONLY_AST)`. -/
def parseCase (j : Json) : Except String Json := do
  let src : List Nat ← fromJson? (← field j "src")
  let mode ← getStr j "mode"
  let start : StartRule ← match mode with
    | "exec" => pure .file
    | "single" => pure .single
    | "eval" => pure .eval
    | "func_type" => pure .funcType
    | m => throw s!"bad mode {m}"
  let tc ← match j.getObjVal? "type_comments" with
    | .ok v => v.getBool?
    | .error _ => pure false
  let fv ← match j.getObjVal? "feature_version" with
    | .ok v => v.getNat?
    | .error _ => pure 14
  let cfg ← getCfg j
  if src.contains 0 then
    return encErr { cls := "SyntaxError", msg := "source code cannot contain null bytes" }
  match parseStr cfg src start tc fv with
  | .ok t => return Json.mkObj [("ok", t.toJ)]
  | .error e => return encErr e

def handler : Handler := fun fn j =>
  if fn == "peg.parse" then some (parseCase j) else none

end PyLean.PyGrammar.Peg
