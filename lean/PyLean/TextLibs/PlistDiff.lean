import PyLean.DiffCore
import PyLean.TextLibs.PlistWrite

/-! `plist.*` difftest cases; see `PlistArea` in `difftest/textlibs_diff.py`.

* `plist.loads`: `b` (bytes) or `s` (code points), `fmt` (`"none"`, `"xml"`, `"binary"` or an
  other object's `repr`), `aware`, and `r`, the frames left when `loads` is called.
* `plist.dumps`: the heap `h` (see `wobjJ`), `root`, `fmt`, `sort`, `skip`, `aware`, `r`.
* `plist.rt`: a `plist.dumps` case whose output, when it is bytes, is read back with
  `loads(..., aware_datetime=aware)` with `r2` frames.

A loaded object is encoded by walking it from the root: a list or dict the first time is
`{"L"|"D": n, "v": ...}` with `n` the number of containers met before it, and then `{"R": n}`. -/

namespace PyLean.TextLibs.Plist

open Lean PyLean PyLean.Diff

def natsJ (j : Json) : Except String (List Nat) := do (← j.getArr?).toList.mapM Json.getNat?

/-- `hex(i)`. -/
def hexInt (i : Int) : String :=
  (if i < 0 then "-0x" else "0x") ++ String.ofList (Nat.toDigits 16 i.natAbs)

/-- Encode the object in slot `ref`; `memo` lists the containers already met. -/
partial def encObj (objs : List (Option Obj)) (ref : Nat) (memo : List Nat) : Json × List Nat :=
  match memo.idxOf? ref with
  | some i => (Json.mkObj [("R", toJson i)], memo)
  | none =>
    match objs.getD ref none with
    | none => (Json.mkObj [("undef", toJson ref)], memo)
    | some o =>
      match o with
      | .none => (Json.mkObj [("n", toJson 0)], memo)
      | .bool b => (Json.mkObj [("b", toJson b)], memo)
      | .int i => (Json.mkObj [("i", toJson (hexInt i))], memo)
      | .real bits => (Json.mkObj [("f", toJson bits)], memo)
      | .date us a => (Json.mkObj [("t", toJson us), ("a", toJson a)], memo)
      | .data b => (Json.mkObj [("y", toJson b)], memo)
      | .str s => (Json.mkObj [("s", toJson s)], memo)
      | .uid n => (Json.mkObj [("u", toJson n)], memo)
      | .arr refs =>
        let id := memo.length
        let (vs, memo) := refs.foldl (fun (acc : Array Json × List Nat) x =>
          let (j, m) := encObj objs x acc.2
          (acc.1.push j, m)) (#[], memo ++ [ref])
        (Json.mkObj [("L", toJson id), ("v", Json.arr vs)], memo)
      | .dict items =>
        let id := memo.length
        let (vs, memo) := items.foldl (fun (acc : Array Json × List Nat) (k, v) =>
          let (jk, m) := encObj objs k acc.2
          let (jv, m) := encObj objs v m
          (acc.1.push (Json.arr #[jk, jv]), m)) (#[], memo ++ [ref])
        (Json.mkObj [("D", toJson id), ("v", Json.arr vs)], memo)

def encRes (r : Res) : Json := (encObj r.objs r.root []).1

def fmtJ (s : String) : Fmt :=
  match s with
  | "none" => .none
  | "xml" => .xml
  | "binary" => .binary
  | rp => .other rp

/-- The XML side is not part of these cases: the generator only reaches it through `isFmtXml`,
whose cases ask for the detection alone. -/
def noXml : XmlParse := fun _ _ _ => .error (.named "NotModelled" "xml")
def noXmlW : XmlWrite := fun _ _ _ _ => .error (.named "NotModelled" "xml")

def pairJ (j : Json) : Except String (Nat × Nat) := do
  let a ← j.getArr?
  return (← (a.getD 0 Json.null).getNat?, ← (a.getD 1 Json.null).getNat?)

def wobjJ (j : Json) : Except String WObj := do
  if let .ok _ := j.getObjVal? "n" then return .none
  if let .ok v := j.getObjVal? "b" then return .bool (← v.getBool?)
  if let .ok v := j.getObjVal? "i" then return .int (← v.getInt?)
  if let .ok v := j.getObjVal? "f" then return .float (← v.getNat?)
  if let .ok v := j.getObjVal? "s" then return .str (← natsJ v)
  if let .ok v := j.getObjVal? "y" then return .bytes (← natsJ v)
  if let .ok v := j.getObjVal? "ba" then return .bytearray (← natsJ v)
  if let .ok v := j.getObjVal? "t" then
    let off ← match j.getObjVal? "o" with
      | .ok .null | .error _ => pure none
      | .ok o => some <$> o.getInt?
    return .date (← v.getInt?) off
  if let .ok v := j.getObjVal? "u" then return .uid (← v.getInt?)
  if let .ok v := j.getObjVal? "l" then return .list (← natsJ v)
  if let .ok v := j.getObjVal? "tu" then return .tuple (← natsJ v)
  if let .ok v := j.getObjVal? "d" then return .dict (← (← v.getArr?).toList.mapM pairJ)
  if let .ok v := j.getObjVal? "fd" then return .fdict (← (← v.getArr?).toList.mapM pairJ)
  if let .ok v := j.getObjVal? "x" then
    return .other (← v.getStr?) (← getStr j "ty")
  throw "bad wobj"

def heapJ (j : Json) : Except String WHeap := do
  (← (← field j "h").getArr?).toList.mapM wobjJ

def cfgJ (j : Json) : Except String WCfg := do
  return ⟨← getBool j "sort", ← getBool j "skip", ← getBool j "aware", fun us => .ok us⟩

def argJ (j : Json) : Except String LoadArg := do
  match j.getObjVal? "b" with
  | .ok v => return .bytes (← natsJ v)
  | .error _ => return .str (← natsJ (← field j "s"))

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "plist.loads" =>
    let r := loadsR noXml (← getNat j "r") (← argJ j) (fmtJ (← getStr j "fmt")) (← getBool j "aware")
    return encPy encRes r
  | "plist.detect" =>
    let b ← natsJ (← field j "b")
    return Json.mkObj [("ok", Json.arr #[toJson (isFmtXml b), toJson (isFmtBinary b)])]
  | "plist.dumps" =>
    let r := dumpsR noXmlW (← getNat j "r") (← heapJ j) (← getNat j "root")
      (fmtJ (← getStr j "fmt")) (← cfgJ j)
    return encPy toJson r
  | "plist.rt" =>
    let cfg ← cfgJ j
    let r1 ← getNat j "r"
    let r2 ← getNat j "r2"
    let H ← heapJ j
    let root ← getNat j "root"
    match dumpsR noXmlW r1 H root .binary cfg with
    | .error e => return Json.mkObj [("ok", Json.mkObj [("wexc", toJson e.className)])]
    | .ok b => return Json.mkObj [("ok", encPy encRes (loadsR noXml r2 (.bytes b) .none cfg.awareDatetime))]
  | _ => throw s!"unknown fn {fn}"

end PyLean.TextLibs.Plist
