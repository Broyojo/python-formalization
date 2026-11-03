import PyLean.DiffCore
import PyLean.PyIO.BufOps
import PyLean.PyIO.DiffFile

/-! Difftest handler for the buffered classes: `none` for a `fn` this area does
not own. -/

namespace PyLean.PyIO

open Lean PyLean PyLean.Diff

def getRaise (j : Json) : Except String (Option (String × String)) :=
  match j.getObjVal? "raise" with
  | .ok c => do return some ((← c.getStr?), (← (← j.getObjVal? "msg").getStr?))
  | .error _ => return none

def getRStep (j : Json) : Except String RStep := do
  if j matches .null then return .block
  if let some (c, m) ← getRaise j then return .raise c m
  if let .ok v := j.getObjVal? "bad" then return .bad (← v.getInt?)
  if let .ok _ := j.getObjVal? "wrong" then return .wrong
  return .short (← (← j.getObjVal? "short").getNat?)

def getSStep (j : Json) : Except String SStep := do
  if j matches .null then return .ok
  if let some (c, m) ← getRaise j then return .raise c m
  if let .ok _ := j.getObjVal? "wrong" then return .wrong
  return .bad (← (← j.getObjVal? "bad").getInt?)

def getCStep (j : Json) : Except String CStep := do
  if j matches .null then return .ok
  if let some (c, m) ← getRaise j then return .raise c m
  return .lie (← (← j.getObjVal? "lie").getBool?)

/-- Bytes the harness cannot predict (uninitialized memory) compare by length. -/
def maskAtom : Atom → Atom
  | .bytes b => .bytes (b.map fun _ => 0)
  | a => a

def maskVal : Val → Val
  | .atom a => .atom (maskAtom a)
  | .list l => .list (l.map maskAtom)

def maskPy (m : Bool) (r : Py Val) : Py Val :=
  if m then (match r with | .ok v => .ok (maskVal v) | e => e) else r

def encRCall (m : Bool) : RCall → Json
  | .readinto n => Json.arr #[toJson "readinto", toJson n]
  | .write b => Json.arr #[toJson "write", toJson b]
  | .seek p w => Json.arr #[toJson "seek", toJson p, toJson w]
  | .tell => Json.arr #[toJson "tell"]
  | .truncate none => Json.arr #[toJson "truncate", Json.null]
  | .truncate (some p) => Json.arr #[toJson "truncate", toJson p]
  | .flush => Json.arr #[toJson "flush"]
  | .close => Json.arr #[toJson "close"]
  | .closed => Json.arr #[toJson "closed"]
  | .isatty => Json.arr #[toJson "isatty"]
  | .re r => Json.arr #[toJson "re", encPy bVal (maskPy m r)]

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

def getReHook (j : Json) : Except String (Nat × BfOp) := do
  let a ← j.getArr?
  return ((← (a.getD 0 .null).getNat?), (← getBfOp (a.getD 1 .null)))

def getRaw (j : Json) : Except String Raw := do
  let data ← bNats (← field j "data")
  let rs ← (← (← field j "rs").getArr?).toList.mapM getRStep
  let ws ← (← (← field j "ws").getArr?).toList.mapM getRStep
  let ss ← (← (← field j "ss").getArr?).toList.mapM getSStep
  let cs ← (← (← field j "cs").getArr?).toList.mapM getCStep
  let hooks ← (← (← field j "hooks").getArr?).toList.mapM getReHook
  let fl ← bNats (← field j "flags")
  let cf : Option (String × String) ← match j.getObjVal? "closeFail" with
    | .ok .null | .error _ => pure none
    | .ok v =>
      let a ← v.getArr?
      pure (some ((← (a.getD 0 .null).getStr?), (← (a.getD 1 .null).getStr?)))
  return { data, pos := 0, rs, ws, ss, cs, canRead := fl.getD 0 0 != 0, canWrite := fl.getD 1 0 != 0,
           canSeek := fl.getD 2 0 != 0, closed := false, closeFail := cf, hooks, tick := 0, log := [] }

def encOutcome {σ : Type} (m : Bool) (raw : σ → Raw) : Outcome σ → Json
  | .crashed => Json.mkObj [("ok", Json.null), ("crash", Json.bool true)]
  | .hung => Json.mkObj [("ok", Json.null), ("hang", Json.bool true)]
  | .initErr e => encPy (fun (_ : Unit) => Json.null) (.error e)
  | .done s rs =>
    let r := raw s
    Json.mkObj [("ok", Json.arr (rs.map (fun x => encPy bVal (maskPy m x))).toArray),
      ("log", Json.arr (r.log.map (encRCall m)).toArray),
      ("data", toJson r.data), ("pos", toJson r.pos)]

def runBuffered (fn : String) (j : Json) : Option (Except String Json) :=
  match fn with
  | "buf_c" | "buf_py" => some do
    let raw ← getRaw j
    let kind ← getNat j "kind"
    let size ← getInt j "size"
    let mask ← getBool j "mask"
    let ops ← (← (← field j "ops").getArr?).toList.mapM getBfOp
    if fn = "buf_c" then return encOutcome mask (·.raw) (runC kind raw size ops)
    else return encOutcome mask (·.raw) (runP kind raw size ops)
  | _ => none

end PyLean.PyIO
