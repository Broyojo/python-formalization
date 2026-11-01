import PyLean.DiffCore
import PyLean.JsonMod.DecC
import PyLean.JsonMod.Enc

/-!
Differential-testing handler for `json` cases (`"mod": "json"`).

Strings travel as lists of code points; ints as decimal strings. A decoded
value is `null`, a bool, `{"int": "<n>"}`, `{"s": [...]}`,
`{"hook": "float"|"int"|"const", "t": [...]}`, a JSON list, or
`{"obj": [[key, value], ...]}`. An encoder input uses `null`, bools,
`{"i": "<n>"}`, `{"s": [...]}`, `{"l": [...]}`, `{"d": [[key, value], ...]}`,
`{"back": k}` and `{"other": 0}`; keys are `{"s": [...]}`, `{"i": "<n>"}`,
`{"b": bool}`, `null` or `{"t": "<n>"}`.
-/

namespace PyLean.JsonMod

open Lean PyLean PyLean.Diff

def encStr (s : PStr) : Json := Json.arr (s.toArray.map toJson)

partial def encJVal : JVal → Json
  | .null => Json.null
  | .bool b => toJson b
  | .int n => Json.mkObj [("int", toJson (toString n))]
  | .str s => Json.mkObj [("s", encStr s)]
  | .hook k t =>
    let kn := match k with | .float => "float" | .int => "int" | .const => "const"
    Json.mkObj [("hook", toJson kn), ("t", encStr t)]
  | .arr xs => Json.arr (xs.toArray.map encJVal)
  | .obj kvs => Json.mkObj [("obj", Json.arr (kvs.toArray.map fun (k, v) => Json.arr #[encStr k, encJVal v]))]

def decStr (j : Json) : Except String PStr := do
  let a ← j.getArr?
  a.toList.mapM (·.getNat?)

def decIntStr (j : Json) : Except String Int := do
  let t ← j.getStr?
  match t.toInt? with
  | some n => pure n
  | none => throw s!"bad int {t}"

def decKey (j : Json) : Except String EKey :=
  match j with
  | .null => pure .none
  | _ =>
    match j.getObjVal? "s", j.getObjVal? "i", j.getObjVal? "b", j.getObjVal? "t" with
    | .ok s, _, _, _ => .str <$> decStr s
    | _, .ok i, _, _ => .int <$> decIntStr i
    | _, _, .ok b, _ => .bool <$> b.getBool?
    | _, _, _, .ok t => .tup <$> decIntStr t
    | _, _, _, _ => throw "bad key"

partial def decEVal (j : Json) : Except String EVal :=
  match j with
  | .null => pure .none
  | .bool b => pure (.bool b)
  | _ =>
    match j.getObjVal? "s", j.getObjVal? "i", j.getObjVal? "l", j.getObjVal? "d" with
    | .ok s, _, _, _ => .str <$> decStr s
    | _, .ok i, _, _ => .int <$> decIntStr i
    | _, _, .ok l, _ => do
      let a ← l.getArr?
      return .list (← a.toList.mapM decEVal)
    | _, _, _, .ok d => do
      let a ← d.getArr?
      let ps ← a.toList.mapM fun p => do
        let q ← p.getArr?
        return (← decKey (q.getD 0 .null), ← decEVal (q.getD 1 .null))
      return .dict ps
    | _, _, _, _ =>
      match j.getObjVal? "back" with
      | .ok k => .back <$> k.getNat?
      | .error _ => pure .other

def getDCfg (j : Json) : Except String DCfg := do
  return { strict := ← getBool j "strict", pairsHook := ← getBool j "pairs", intHook := ← getBool j "inthook" }

def getECfg (j : Json) : Except String ECfg := do
  let indent ← match j.getObjVal? "indent" with
    | .ok .null | .error _ => pure none
    | .ok v => some <$> decStr v
  return { ensureAscii := ← getBool j "ensure_ascii", checkCircular := ← getBool j "check_circular",
           sortKeys := ← getBool j "sort_keys", skipKeys := ← getBool j "skipkeys", indent,
           itemSep := ← decStr (← field j "item_sep"), keySep := ← decStr (← field j "key_sep") }

def encDR {α : Type} (doc : PStr) (enc : α → Json) : DR α → Json
  | .ok v => Json.mkObj [("ok", enc v)]
  | .error e => encPy enc (.error (e.toPy doc))

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "loads_py" | "loads_c" =>
    let s ← decStr (← field j "s")
    let cfg ← getDCfg j
    let r := if fn = "loads_py" then loadsPy cfg s else loadsC cfg s
    return encDR s encJVal r
  | "raw_py" | "raw_c" =>
    let s ← decStr (← field j "s")
    let cfg ← getDCfg j
    let idx ← decIntStr (← field j "idx")
    let r := if fn = "raw_py" then rawDecodePy cfg s idx else rawDecodeC cfg s idx
    return encDR s (fun (v, e) => Json.arr #[encJVal v, toJson (toString e)]) r
  | "dumps_py" | "dumps_c" =>
    let v ← decEVal (← field j "v")
    let cfg ← getECfg j
    let r := if fn = "dumps_py" then dumpsPy cfg v else dumpsC cfg v
    return encPy encStr r
  | other => throw s!"unknown fn {other}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.JsonMod
