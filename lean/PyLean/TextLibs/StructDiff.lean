import PyLean.DiffCore
import PyLean.TextLibs.StructModel

/-! `struct.*` difftest cases. Values travel as `{"t": tag, "v": value}`; see
`difftest/textlibs_diff.py`. -/

namespace PyLean.TextLibs.Struct

open Lean PyLean PyLean.Diff

def natList (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM Json.getNat?

def decSV (j : Json) : Except String SV := do
  let v ← field j "v"
  match ← getStr j "t" with
  | "i" => return .int (← v.getInt?)
  | "idx" => return .index (← v.getInt?)
  | "b" => return .bytes (← natList v)
  | "ba" => return .bytearray (← natList v)
  | "f" => return .float (← v.getNat?)
  | "c" => match ← natList v with
    | [a, b] => return .cplx a b
    | _ => throw "bad complex"
  | "o" => return .other (← v.getBool?)
  | t => throw s!"bad tag {t}"

def encSV : SV → Json
  | .int n => Json.mkObj [("t", "i"), ("v", toJson n)]
  | .index n => Json.mkObj [("t", "idx"), ("v", toJson n)]
  | .bytes b => Json.mkObj [("t", "b"), ("v", toJson b)]
  | .bytearray b => Json.mkObj [("t", "ba"), ("v", toJson b)]
  | .float x => Json.mkObj [("t", "f"), ("v", toJson x)]
  | .cplx a b => Json.mkObj [("t", "c"), ("v", toJson [a, b])]
  | .bool b => Json.mkObj [("t", "B"), ("v", toJson b)]
  | .other t => Json.mkObj [("t", "o"), ("v", toJson t)]

def decFmt (j : Json) : Except String FmtArg := do
  let f ← field j "fmt"
  if let .ok s := f.getObjVal? "s" then return .str (← natList s)
  if let .ok s := f.getObjVal? "b" then return .bytes (← natList s)
  return .other (← getStr f "o") (← getBool f "h")

def getArgs (j : Json) : Except String (List SV) := do
  (← (← field j "args").getArr?).toList.mapM decSV

def run (fn : String) (j : Json) : Except String Json := do
  let encL (r : Py (List SV)) := encPy (fun l => Json.arr (l.map encSV).toArray) r
  match fn with
  | "struct.calcsize" => return encPy toJson (calcsize (← decFmt j))
  | "struct.info" =>
    return encPy (fun s => Json.mkObj [("size", toJson s.sSize), ("len", toJson s.sLen),
        ("sizeof", toJson (sSizeof s)), ("repr", toJson (sRepr s))]) (structInit (← decFmt j))
  | "struct.uninit" =>
    return Json.mkObj [("ok", Json.mkObj [("size", toJson (sGetSize sNew)),
      ("pack", encPy toJson (do structPack (← ensureReady sNew) [])),
      ("unpack", encPy (fun _ => Json.null) (do structUnpack (← ensureReady sNew) [])),
      ("format", encPy toJson (do return sGetFormat (← ensureReady sNew)))])]
  | "struct.iter_hint" =>
    let b ← natList (← field j "buf")
    let k ← getNat j "k"
    let f ← decFmt j
    return encPy toJson (do
      let s ← cacheStruct f
      let _ ← structIterUnpack s b
      return unpackiterLen s b (k * s.sSize))
  | "struct.pack" => return encPy toJson (modPack (← decFmt j) (← getArgs j))
  | "struct.Struct.pack" =>
    let f ← decFmt j
    let a ← getArgs j
    return encPy toJson (do structPack (← structInit f) a)
  | "struct.unpack" => return encL (modUnpack (← decFmt j) (← natList (← field j "buf")))
  | "struct.unpack_from" =>
    return encL (modUnpackFrom (← decFmt j) (← natList (← field j "buf")) (← getInt j "off"))
  | "struct.iter_unpack" =>
    return encPy (fun l => Json.arr (l.map fun t => Json.arr (t.map encSV).toArray).toArray)
      (modIterUnpack (← decFmt j) (← natList (← field j "buf")))
  | "struct.pack_into" =>
    return encPy toJson (modPackInto (← decFmt j) (← natList (← field j "buf")) (← getInt j "off")
      (← getArgs j))
  | _ => throw s!"unknown fn {fn}"

end PyLean.TextLibs.Struct
