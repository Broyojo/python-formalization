import PyLean.DiffCore
import PyLean.PyIO.Newline
import PyLean.PyIO.TextOps
import PyLean.PyIO.DiffFile

/-! Difftest handler for `IncrementalNewlineDecoder`: `none` for a `fn` this area
does not own. -/

namespace PyLean.PyIO

open Lean PyLean PyLean.Diff

def nNats (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM Json.getNat?

def stepND (dec : NDec → List Nat → Bool → Py (NDec × List Nat)) (bytesMode : Bool)
    (d : NDec) (op : Json) : Except String (NDec × Json) := do
  match ← getStr op "op" with
  | "decode" =>
    match dec d (← nNats (← field op "s")) (← getBool op "final") with
    | .ok (d', out) => return (d', Json.mkObj [("ok", Json.mkObj [("s", toJson out)])])
    | .error e => return (d, encPy (fun (_ : Unit) => Json.null) (.error e))
  | "getstate" =>
    let (b, f) := d.getstate
    return (d, Json.mkObj [("ok", Json.arr #[Json.mkObj [("b", toJson b)], toJson f])])
  | "setstate" =>
    return (d.setstate (← nNats (← field op "b")) (← getInt op "flag"), Json.mkObj [("ok", Json.null)])
  | "reset" => return (d.reset, Json.mkObj [("ok", Json.null)])
  | "newlines" =>
    let v : Json := match newlinesVal d.seennl with
      | .atom .none => Json.null
      | .atom (.str s) => Json.mkObj [("s", toJson s)]
      | .list l => Json.arr (l.map fun a => match a with
          | .str s => Json.mkObj [("s", toJson s)]
          | _ => Json.null).toArray
      | _ => Json.null
    return (d, Json.mkObj [("ok", v)])
  | o =>
    let _ := bytesMode
    throw s!"unknown op {o}"

def getTEnc (n : String) : TEnc :=
  match n with
  | "ascii" => .ascii | "latin-1" => .latin1 | "utf-16" => .utf16 | "utf-16-le" => .utf16le
  | "utf-16-be" => .utf16be | "utf-32" => .utf32 | "utf-32-le" => .utf32le | "utf-32-be" => .utf32be
  | _ => .utf8

def getOptOptNats (j : Json) (k : String) : Except String (Option (List Nat)) := getOptNats j k

def getOptBool (j : Json) (k : String) : Except String (Option Bool) :=
  match j.getObjVal? k with
  | .ok .null | .error _ => .ok none
  | .ok v => some <$> v.getBool?

def getTXOp (j : Json) : Except String TXOp := do
  match ← getStr j "op" with
  | "read" => return .read (← getOptInt j "n")
  | "readline" => return .readline (← getOptInt j "n")
  | "next" => return .next
  | "readlines" => return .readlines (← getOptInt j "n")
  | "write" => return .write (← nNats (← field j "b"))
  | "seek" => return .seek (← getInt j "pos") (← getInt j "whence")
  | "tell" => return .tell
  | "seektell" => return .seekTell
  | "truncate" => return .truncate (← getOptInt j "n")
  | "flush" => return .flush | "close" => return .close | "detach" => return .detach
  | "closed" => return .closed | "encoding" => return .encoding | "errors" => return .errors
  | "newlines" => return .newlines | "line_buffering" => return .lineBuffering
  | "write_through" => return .writeThrough | "seekable" => return .seekable
  | "readable" => return .readable | "writable" => return .writable | "isatty" => return .isatty
  | "fileno" => return .fileno | "name" => return .name | "chunkget" => return .chunkGet
  | "chunkset" => return .chunkSet (← getInt j "v")
  | "reconfigure" =>
    let nl : Option (Option (List Nat)) ← match j.getObjVal? "hasnl" with
      | .ok (.bool true) => pure (some (← getOptNats j "newline"))
      | _ => pure none
    return .reconfigure nl (← getOptBool j "lb") (← getOptBool j "wt")
  | "bufvalue" => return .bufvalue
  | o => throw s!"unknown op {o}"

def getSAny (j : Json) : Except String (SOp ⊕ SXOp) := do
  match ← getStr j "op" with
  | "readable" => return .inr .readable | "writable" => return .inr .writable
  | "seekable" => return .inr .seekable | "flush" => return .inr .flush | "isatty" => return .inr .isatty
  | "fileno" => return .inr .fileno | "detach" => return .inr .detach
  | "encoding" => return .inr .encoding | "errors" => return .inr .errors
  | "line_buffering" => return .inr .lineBuffering | "name" => return .inr .name
  | "getstate" => return .inr .getstate
  | "setstate" => return .inr (.setstate (← getOptNats j "v") (← getOptNats j "nl") (← getInt j "pos"))
  | _ => return .inl (← getSOp j)

def runText (fn : String) (j : Json) : Option (Except String Json) :=
  match fn with
  | "nldec_c" | "nldec_py" => some do
    let translate ← getBool j "translate"
    let inner ← getBool j "inner"
    let ops ← (← field j "ops").getArr?
    let dec := if fn = "nldec_c" then NC.decode else NP.decode
    let mut d := NDec.fresh (if inner then some [] else none) translate
    let mut out : Array Json := #[]
    for op in ops do
      let (d', r) ← stepND dec inner d op
      d := d'
      out := out.push r
    return Json.mkObj [("ok", Json.arr out)]
  | "tiow_c" | "tiow_py" => some do
    let data ← nNats (← field j "data")
    let nl ← getOptNats j "newline"
    let ops ← (← (← field j "ops").getArr?).toList.mapM getTXOp
    if fn = "tiow_c" then
      let en ← getStr j "enc"
      let er ← getStr j "errors"
      let init := TCm.init data (getTEnc en) (en.toList.map Char.toNat) (er.toList.map Char.toNat)
        (er == "surrogatepass") nl (← getBool j "lb") (← getBool j "wt") 8192
      match init with
      | .error e => return encPy (fun (_ : Unit) => Json.null) (.error e)
      | .ok t => return Json.mkObj [("ok", Json.arr ((runOps TCm.stepOp t ops).2.map (encPy bVal)).toArray)]
    else
      match TP.initW data nl with
      | .error e => return encPy (fun (_ : Unit) => Json.null) (.error e)
      | .ok t => return Json.mkObj [("ok", Json.arr ((runOps TP.stepW t ops).2.map (encPy bVal)).toArray)]
  | "stringx_c" | "stringx_py" => some do
    let init ← getOptNats j "init"
    let nl ← getOptNats j "newline"
    let ops ← (← (← field j "ops").getArr?).toList.mapM getSAny
    if fn = "stringx_c" then
      match SC.init init nl with
      | .error e => return encPy (fun (_ : Unit) => Json.null) (.error e)
      | .ok t => return Json.mkObj [("ok", Json.arr ((runOps stepSAnyC t ops).2.map (encPy bVal)).toArray)]
    else
      match TP.init init nl with
      | .error e => return encPy (fun (_ : Unit) => Json.null) (.error e)
      | .ok t => return Json.mkObj [("ok", Json.arr ((runOps stepSAnyP t ops).2.map (encPy bVal)).toArray)]
  | _ => none

end PyLean.PyIO
