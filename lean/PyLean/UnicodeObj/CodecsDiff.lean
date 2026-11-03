import PyLean.DiffCore
import PyLean.StrSearch.Diff
import PyLean.UnicodeObj.CodecsErr
import PyLean.UnicodeObj.CodecAscii
import PyLean.UnicodeObj.CodecEscapeProps

/-! Difftest handler for `Python/codecs.c` and `Modules/_codecsmodule.c` (`fn` names start
with `codecs_`). -/

namespace PyLean.UnicodeObj.CodecsDiff

open Lean PyLean PyLean.Diff PyLean.StrSearch PyLean.UnicodeObj PyLean.UnicodeObj.Codecs

def getErrH (name : String) : Except String ErrHandler := do
  match name with
  | "strict" => return .strict
  | "ignore" => return .ignore
  | "replace" => return .replace
  | "surrogateescape" => return .surrogateescape
  | "backslashreplace" => return .backslashreplace
  | "surrogatepass" => return .surrogatepass
  | "xmlcharrefreplace" => return .xmlcharrefreplace
  | "namereplace" => return .namereplace
  | e => throw s!"bad handler {e}"

def getSlot (j : Json) : Except String Slot := do
  match ← getStr j "k" with
  | "null" => return .null
  | "str" => return .str (← getSeq j "v")
  | "bytes" => return .bytes (← getSeq j "v")
  | "none" | "int" => return .other
  | k => throw s!"bad slot {k}"

/-- The builtin part of the MRO relation. -/
def builtinSub (c b : String) : Bool :=
  c == b || go 6 c
where
  go : Nat → String → Bool
    | 0, _ => false
    | n + 1, x => match builtinBase x with
      | some y => y == b || go n y
      | none => false

/-- The hierarchy of a case: the MRO of the object's class as Python reports it, and the
builtin bases for every other class. -/
def getHier (j : Json) : Except String Hier := do
  let cls ← getStr j "cls"
  let mro ← (← field j "mro").getArr?
  let mro ← mro.toList.mapM (·.getStr?)
  return ⟨fun c b => if c == cls then mro.contains b else builtinSub c b⟩

def getExcObj (j : Json) : Except String ExcObj := do
  return { cls := ← getStr j "cls", tpName := ← getStr j "tp",
           encoding := ← getSlot (← field j "encoding"), object := ← getSlot (← field j "object"),
           start := ← getInt j "start", stop := ← getInt j "end" }

/-- `ucnhash_capi->getname(c, buf, 256, 1)` for the characters of a case. -/
def getNameTable (j : Json) : Except String (Nat → Option Str) := do
  let arr ← (← field j "names").getArr?
  let l ← arr.toList.mapM fun e => do
    let pair ← e.getArr?
    let c ← pair[0]!.getNat?
    match pair[1]! with
    | .null => return (c, none)
    | v => return (c, some (← (← v.getArr?).toList.mapM (·.getNat?)))
  return fun c => (l.lookup c).join

def encRep : Rep → Json
  | .str s => Json.arr #[toJson "str", toJson s]
  | .bytes b => Json.arr #[toJson "bytes", toJson b]

def encHandler (r : HPy (Rep × Nat)) : Json :=
  match r with
  | .ok (rep, pos) => Json.mkObj [("rep", encRep rep), ("pos", toJson pos)]
  | .error .reraise => Json.mkObj [("raised", toJson "self")]
  | .error (.exc e) => Json.mkObj [("raised", toJson e.className), ("msg", toJson e.message)]

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "codecs_handler" =>
    let H ← getHier j
    let e ← getExcObj j
    let h ← getErrH (← getStr j "h")
    let names ← getNameTable j
    return Json.mkObj [("ok", encHandler (callBuiltin H (.ok names) h e))]
  | "codecs_ucs1_encode" =>
    let names ← getNameTable j
    return encPy toJson (ucs1Encode (← getSeq j "s") (← getNat j "limit")
      (← getErrH (← getStr j "h")) names)
  | _ => throw s!"unknown fn {fn}"

def handler : PyLean.Diff.Handler := fun fn j =>
  if fn.startsWith "codecs_" then some (run fn j) else none

end PyLean.UnicodeObj.CodecsDiff
