import PyLean.DiffCore
import PyLean.PyIO.BufOps
import PyLean.PyIO.DiffFile

/-! Difftest handler for the buffered classes: `none` for a `fn` this area does
not own. -/

namespace PyLean.PyIO

open Lean PyLean PyLean.Diff

def getRStep (j : Json) : Except String RStep :=
  match j with
  | .null => .ok .block
  | _ =>
    match j.getObjVal? "raise" with
    | .ok c => do return .raise (← c.getStr?) (← (← j.getObjVal? "msg").getStr?)
    | .error _ =>
      match j.getObjVal? "bad" with
      | .ok v => do return .bad (← v.getInt?)
      | .error _ => do return .short (← (← j.getObjVal? "short").getNat?)

def getSStep (j : Json) : Except String SStep :=
  match j with
  | .null => .ok .ok
  | _ =>
    match j.getObjVal? "raise" with
    | .ok c => do return .raise (← c.getStr?) (← (← j.getObjVal? "msg").getStr?)
    | .error _ => do return .bad (← (← j.getObjVal? "bad").getInt?)

def encRCall : RCall → Json
  | .readinto n => Json.arr #[toJson "readinto", toJson n]
  | .write b => Json.arr #[toJson "write", toJson b]
  | .seek p w => Json.arr #[toJson "seek", toJson p, toJson w]
  | .tell => Json.arr #[toJson "tell"]
  | .truncate none => Json.arr #[toJson "truncate", Json.null]
  | .truncate (some p) => Json.arr #[toJson "truncate", toJson p]
  | .flush => Json.arr #[toJson "flush"]
  | .close => Json.arr #[toJson "close"]

def getRaw (j : Json) : Except String Raw := do
  let data ← bNats (← field j "data")
  let rs ← (← (← field j "rs").getArr?).toList.mapM getRStep
  let ws ← (← (← field j "ws").getArr?).toList.mapM getRStep
  let ss ← (← (← field j "ss").getArr?).toList.mapM getSStep
  let fl ← bNats (← field j "flags")
  let cf : Option (String × String) ← match j.getObjVal? "closeFail" with
    | .ok .null | .error _ => pure none
    | .ok v =>
      let a ← v.getArr?
      pure (some ((← (a.getD 0 .null).getStr?), (← (a.getD 1 .null).getStr?)))
  return ⟨data, 0, rs, ws, ss, fl.getD 0 0 != 0, fl.getD 1 0 != 0, fl.getD 2 0 != 0, false, cf, []⟩

def getBfOp (j : Json) : Except String BfOp := do
  match ← getStr j "op" with
  | "read" => return .read (← getOptInt j "n")
  | "read1" => return .read1 (← getInt j "n")
  | "peek" => return .peek (← getInt j "n")
  | "readinto" => return .readinto (← getNat j "n")
  | "readinto1" => return .readinto1 (← getNat j "n")
  | "readline" => return .readline (← getOptInt j "n")
  | "next" => return .next
  | "write" => return .write (← bNats (← field j "b"))
  | "seek" => return .seek (← getInt j "pos") (← getInt j "whence")
  | "tell" => return .tell
  | "truncate" => return .truncate (← getOptInt j "n")
  | "flush" => return .flush
  | "close" => return .close
  | "detach" => return .detach
  | "closed" => return .closed
  | "readable" => return .readable
  | "writable" => return .writable
  | "seekable" => return .seekable
  | "isatty" => return .isatty
  | "fileno" => return .fileno
  | "name" => return .name
  | "mode" => return .mode
  | "getstate" => return .getstate
  | o => throw s!"unknown op {o}"

def encBuf (rs : List (Py Val)) (r : Raw) : Json :=
  Json.mkObj [("ok", Json.arr (rs.map (encPy bVal)).toArray),
    ("log", Json.arr (r.log.map encRCall).toArray),
    ("data", toJson r.data), ("pos", toJson r.pos)]

def runBuffered (fn : String) (j : Json) : Option (Except String Json) :=
  match fn with
  | "buf_c" | "buf_py" => some do
    let raw ← getRaw j
    let kind ← getNat j "kind"
    let size ← getInt j "size"
    let ops ← (← (← field j "ops").getArr?).toList.mapM getBfOp
    if fn = "buf_c" then
      match BC2.init kind raw size with
      | .error e => return encPy (fun (_ : Unit) => Json.null) (.error e)
      | .ok s =>
        let (s', rs) := runOps BC2.stepOp s ops
        return encBuf rs s'.raw
    else
      match BP2.init kind raw size with
      | .error e => return encPy (fun (_ : Unit) => Json.null) (.error e)
      | .ok s =>
        let (s', rs) := runOps BP2.stepOp s ops
        return encBuf rs s'.raw
  | _ => none

end PyLean.PyIO
