import PyLean.DiffCore
import PyLean.PyGrammar.Ast
import PyLean.PyGrammar.Check.Preprocess

/-! Difftest handler for `Python/ast.c` and `Python/ast_preprocess.c`: `fn` starts with `check.`. -/

namespace PyLean.PyGrammar.Check

open Lean PyLean PyLean.Diff

/-- A location-carrying error, in the difftest's `msg|l|o|el|eo|None` shape. -/
def encFuture (e : FutureError) : Json :=
  Json.mkObj [("exc", toJson "SyntaxError"),
    ("msg", toJson s!"{e.msg}|{e.loc.lineno}|{e.loc.colOffset + 1}|{e.loc.endLineno}|{e.loc.endColOffset + 1}|None")]

def handler : Handler := fun fn j =>
  if fn == "check.validate" then
    some do
      let t ← Ast.ofJ (← field j "tree")
      return encPy (fun _ => Json.null) (validate t)
  else if fn == "check.preprocess" then
    some do
      let t ← Ast.ofJ (← field j "tree")
      let opt ← getInt j "optimize"
      let only ← getBool j "syntax_only"
      match astPreprocess t opt only with
      | .ok r => return Json.mkObj [("ok", r.toJ)]
      | .error e => return encFuture e
  else none

end PyLean.PyGrammar.Check
