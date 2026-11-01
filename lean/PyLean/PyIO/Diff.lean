import PyLean.DiffCore
import PyLean.PyIO.BytesIO
import PyLean.PyIO.StringC
import PyLean.PyIO.StringPy

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

def getNats (j : Json) (key : String) : Except String (List Nat) := do
  let arr ← (← field j key).getArr?
  (arr.mapM Json.getNat?).map Array.toList

def getOptNats (j : Json) (key : String) : Except String (Option (List Nat)) :=
  match j.getObjVal? key with
  | .ok .null | .error _ => .ok none
  | .ok _ => some <$> getNats j key

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

def getSOp (j : Json) : Except String SOp := do
  match ← getStr j "op" with
  | "read" => return .read (← getOptInt j "n")
  | "readline" => return .readline (← getOptInt j "n")
  | "readlines" => return .readlines (← getOptInt j "n")
  | "write" => return .write (← getNats j "b")
  | "seek" => return .seek (← getInt j "pos") (← getInt j "whence")
  | "tell" => return .tell
  | "truncate" => return .truncate (← getOptInt j "n")
  | "getvalue" => return .getvalue
  | "close" => return .close
  | "next" => return .next
  | "closed" => return .closed
  | "newlines" => return .newlines
  | "seektell" => return .seekTell
  | o => throw s!"unknown op {o}"

def encResults (rs : List (Py Val)) : Json :=
  Json.mkObj [("ok", Json.arr (rs.map (encPy encVal)).toArray)]

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

def handler : Handler := fun fn j => some (run fn j)

end PyLean.PyIO
