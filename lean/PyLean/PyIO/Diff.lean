import PyLean.DiffCore
import PyLean.PyIO.BytesIO
import PyLean.PyIO.StringC
import PyLean.PyIO.StringPy
import PyLean.PyIO.DiffText
import PyLean.PyIO.DiffBuffered
import PyLean.PyIO.DiffFile
import PyLean.PyIO.BytesShare
import PyLean.PyIO.BytesCallbacks

/-! Differential-testing handler for `pyio` cases (`"mod": "pyio"`).

A case is `{"fn": "bytesio_c" | "bytesio_py" | "stringio_c" | "stringio_py",
"init": ..., "newline": ..., "ops": [...]}`. Bytes and str travel as lists of
ints (`{"b": [...]}` / `{"s": [...]}` in results); each operation is an
object `{"op": name, ...}`. The result is `{"ok": [r1, r2, ...]}` with one
`{"ok": v}` or `{"exc": cls, "msg": m}` per operation, or the constructor's
exception. `fn = "ratio"` checks the binary64 emulation used by `tell()`. -/

namespace PyLean.PyIO

open Lean PyLean PyLean.Diff

def encAtom : Atom → Json
  | .none => Json.null
  | .int i => toJson i
  | .bool b => toJson b
  | .bytes b => Json.mkObj [("b", toJson b)]
  | .str s => Json.mkObj [("s", toJson s)]

def encVal : Val → Json
  | .atom a => encAtom a
  | .list l => Json.arr (l.map encAtom).toArray

def getBOp (j : Json) : Except String BOp := do
  match ← getStr j "op" with
  | "read" => return .read (← getOptInt j "n")
  | "read1" => return .read1 (← getOptInt j "n")
  | "readline" => return .readline (← getOptInt j "n")
  | "readlines" => return .readlines (← getOptInt j "n")
  | "readinto" => return .readinto (← getNat j "n")
  | "write" => return .write (← getNats j "b")
  | "seek" => return .seek (← getInt j "pos") (← getInt j "whence")
  | "tell" => return .tell
  | "truncate" => return .truncate (← getOptInt j "n")
  | "getvalue" => return .getvalue
  | "getbuffer" => return .getbuffer
  | "release" => return .release
  | "close" => return .close
  | "next" => return .next
  | "closed" => return .closed
  | o => throw s!"unknown op {o}"

def encResults (rs : List (Py Val)) : Json :=
  Json.mkObj [("ok", Json.arr (rs.map (encPy encVal)).toArray)]

def getShareOp (j : Json) : Except String Share.SOp := do
  match ← getStr j "op" with
  | "write" => return .write (← getNats j "b")
  | "getvalue" => return .getvalue
  | "read" => return .read (← getOptInt j "n")
  | "readline" => return .readline (← getOptInt j "n")
  | "seek" => return .seek (← getInt j "pos") (← getInt j "whence")
  | "tell" => return .tell
  | "truncate" => return .truncate (← getOptInt j "n")
  | "getbuffer" => return .getbuffer
  | "viewset" => return .viewSet (← getNat j "v") (← getNat j "i") (← getNat j "x")
  | "viewbytes" => return .viewBytes (← getNat j "v")
  | "release" => return .release (← getNat j "v")
  | "close" => return .close
  | "closed" => return .closed
  | "drop" => return .drop (← getNat j "h")
  | "hash" => return .hash (← getNat j "h")
  | "same" => return .same (← getNat j "h") (← getNat j "k")
  | o => throw s!"unknown op {o}"

def runShare (fn : String) (j : Json) : Option (Except String Json) :=
  match fn with
  | "share_c" => some do
    let init ← getNats j "init"
    let ops ← (← (← field j "ops").getArr?).toList.mapM getShareOp
    return encResults (Share.runS init (← getBool j "keep") ops).2
  | _ => none

/-- `{"kind": "data", "b": [...]}`, `{"kind": "hooked", "hook": [...], "r": [...] or null}`,
`{"kind": "str", "s": [...]}` or `{"kind": "obj", "t": name}`. -/
def getWItem (j : Json) : Except String WItem := do
  match ← getStr j "kind" with
  | "data" => return .data (← bNats (← field j "b"))
  | "hooked" =>
    let hook ← (← (← field j "hook").getArr?).toList.mapM getHook
    match j.getObjVal? "r" with
    | .ok .null | .error _ => return .hooked hook none
    | .ok v => return .hooked hook (some (← bNats v))
  | "str" => return .bad (.str (← bNats (← field j "s")))
  | "obj" => return .bad (.obj (← getStr j "t"))
  | k => throw s!"unknown item kind {k}"

def getIStep (j : Json) : Except String IStep := do
  let hook ← (← (← field j "hook").getArr?).toList.mapM getHook
  match j.getObjVal? "item" with
  | .ok x => return .item hook (← getWItem x)
  | .error _ => return .raise hook

def getCbOp (j : Json) : Except String (BOp ⊕ CBOp) := do
  match ← getStr j "op" with
  | "writeitem" => return .inr (.writeItem (← getWItem (← field j "x")))
  | "reinititem" => return .inr (.reinitItem (← getWItem (← field j "x")))
  | "writelinesit" =>
    match j.getObjVal? "notiter" with
    | .ok t => return .inr (.writelinesIt (.notIter (← t.getStr?)))
    | .error _ => return .inr (.writelinesIt (.iter (← (← (← field j "steps").getArr?).toList.mapM getIStep)))
  | _ => return .inl (← getBOp j)

def runCallbacks (fn : String) (j : Json) : Option (Except String Json) :=
  match fn with
  | "bytescb_c" | "bytescb_py" => some do
    let init ← getNats j "init"
    let ops ← (← (← field j "ops").getArr?).toList.mapM getCbOp
    return encResults (runOps (if fn = "bytescb_c" then stepCbC else stepCbP) (bInit init) ops).2
  | _ => none

def encRun : Py (List (Py Val)) → Json
  | .ok rs => encResults rs
  | .error e => encPy (fun (_ : Unit) => Json.null) (.error e)

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "bytesio_c" | "bytesio_py" =>
    let init ← getNats j "init"
    let ops ← ((← (← field j "ops").getArr?).mapM getBOp)
    return encResults (if fn = "bytesio_c" then runBC init ops.toList else runBPy init ops.toList)
  | "stringio_c" | "stringio_py" =>
    let init ← getOptNats j "init"
    let nl ← getOptNats j "newline"
    let ops ← ((← (← field j "ops").getArr?).mapM getSOp)
    return encRun (if fn = "stringio_c" then runSC init nl ops.toList else runSPy init nl ops.toList)
  | "ratio" =>
    return encPy toJson (.ok (dTrunc (dMulNat (dDiv (← getNat j "a") (← getNat j "b")) (← getNat j "c"))) : Py Nat)
  | other => throw s!"unknown fn {other}"

def handler : Handler := fun fn j =>
  match runText fn j with
  | some r => some r
  | none =>
    match runBuffered fn j with
    | some r => some r
    | none =>
      match runFile fn j with
      | some r => some r
      | none =>
        match runShare fn j with
        | some r => some r
        | none =>
          match runCallbacks fn j with
          | some r => some r
          | none => some (run fn j)

end PyLean.PyIO
