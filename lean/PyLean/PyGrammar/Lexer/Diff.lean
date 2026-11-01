import PyLean.DiffCore
import PyLean.PyGrammar.Lexer.Iter

/-! Difftest handler for the lexer and tokenize parts: `fn` starts with `lex.`. -/

namespace PyLean.PyGrammar.Lexer

open Lean PyLean PyLean.Diff

def optI : Option Int → String
  | some i => toString i
  | none => "None"

def encTok (t : TokInfo) : Json :=
  Json.arr #[toJson t.type, toJson t.str, toJson t.lineno, toJson t.col, toJson t.endLineno,
             toJson t.endCol, toJson t.line]

/-- `{"ok": [tokens, error-or-null]}`: errors end the stream without hiding earlier tokens. -/
def encStream (r : List TokInfo × Option PyError) : Json :=
  let err : Json := match r.2 with
    | some e =>
      let text := match e.text with
        | some t => "[" ++ ",".intercalate (t.map toString) ++ "]"
        | none => "None"
      toJson s!"{e.cls}|{e.msg}|{optI e.lineno}|{optI e.offset}|{text}"
    | none => Json.null
  Json.mkObj [("ok", Json.arr #[Json.arr (r.1.map encTok).toArray, err])]

def handler : Handler := fun fn j =>
  if fn == "lex.tokens" then
    some do
      let text : List Nat ← fromJson? (← field j "text")
      let extra ← getBool j "extra"
      return encStream (tokenizeText text extra)
  else none

end PyLean.PyGrammar.Lexer
