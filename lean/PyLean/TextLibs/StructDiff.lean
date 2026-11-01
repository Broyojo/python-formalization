import PyLean.DiffCore
import PyLean.TextLibs.StructModel

/-! `struct.*` difftest cases. Values travel as `{"t": tag, "v": value}`; see
`difftest/textlibs_diff.py`. -/

namespace PyLean.TextLibs.Struct

open Lean PyLean PyLean.Diff

def natList (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM Json.getNat?

def decExc (j : Json) : Except String PyExc := do
  let a ← j.getArr?
  let cls ← a[0]!.getStr?
  let msg ← a[1]!.getStr?
  return match cls with
    | "ValueError" => .valueError msg
    | "TypeError" => .typeError msg
    | "OverflowError" => .overflowError msg
    | _ => .named cls msg

/-- `{"ok": v}` or `{"raise": [cls, msg]}`. -/
def decRes {α : Type} (f : Json → Except String α) (j : Json) : Except String (Except PyExc α) := do
  if let .ok e := j.getObjVal? "raise" then return .error (← decExc e)
  return .ok (← f (← field j "ok"))

def optRes {α : Type} (f : Json → Except String α) (j : Json) (k : String) :
    Except String (Option (Except PyExc α)) := do
  match j.getObjVal? k with
  | .ok .null | .error _ => return none
  | .ok v => return some (← decRes f v)

def decSV (j : Json) : Except String SV := do
  let v ← field j "v"
  match ← getStr j "t" with
  | "obj" =>
    return .obj { index := ← optRes Json.getInt? v "index", float := ← optRes Json.getNat? v "float"
                  cplx := ← optRes (fun x => do
                    let a ← x.getArr?
                    return (← a[0]!.getNat?, ← a[1]!.getNat?)) v "cplx"
                  truth := ← decRes Json.getBool? (← field v "truth") }
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
  | .obj _ => Json.null

def decFmt (j : Json) : Except String FmtArg := do
  let f ← field j "fmt"
  if let .ok s := f.getObjVal? "s" then return .str (← natList s)
  if let .ok s := f.getObjVal? "b" then return .bytes (← natList s)
  if let .ok e := f.getObjVal? "hr" then return .hashRaises (← getStr f "o") (← decExc e)
  return .other (← getStr f "o") (← getBool f "h")

def decBuf (j : Json) : Except String BufArg := do
  if let .ok b := j.getObjVal? "bytes" then return .bytes (← natList b)
  if let .ok b := j.getObjVal? "ba" then return .bytearray (← natList b)
  if let .ok e := j.getObjVal? "raises" then return .raises (← getStr j "ty") (← decExc e)
  return .notBuffer (← getStr j "ty")

def decOff (j : Json) : Except String OffArg := do
  if let .ok n := j.getObjVal? "i" then return .int (← n.getInt?)
  if let .ok r := j.getObjVal? "idx" then return .index "O" (← decRes Json.getInt? r) none
  return .notIndex (← getStr j "ty")

def decFmtObj (f : Json) : Except String FmtArg := do
  if let .ok s := f.getObjVal? "s" then return .str (← natList s)
  return .bytes (← natList (← field f "b"))

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
  | "struct.pack_into2" =>
    let f ← decFmt j
    let a : PackIntoArgs ← match ← getNat j "n" with
      | 0 => pure .noBuffer
      | 1 => pure .noOffset
      | _ => pure (.full (← decBuf (← field j "buf")) (← decOff (← field j "off")) (← getArgs j))
    return encPy toJson (do structPackIntoA (← structInit f) a)
  | "struct.mod2" =>
    let f ← decFmt j
    match ← getStr j "op" with
    | "unpack" => return encL (modUnpackA f (← decBuf (← field j "buf")))
    | "unpack_from" => return encL (modUnpackFromA f (← decBuf (← field j "buf")) (← decOff (← field j "off")))
    | "iter" => return encPy (fun (_ : UIter) => Json.null) (modIterUnpackA f (← decBuf (← field j "buf")))
    | "pack0" => return encPy toJson (modPackA [] none)
    | _ => return encPy toJson (modPackIntoA .noBuffer none)
  | "struct.unpack2" =>
    let f ← decFmt j
    let b ← decBuf (← field j "buf")
    return encL (do structUnpackA (← structInit f) b)
  | "struct.unpack_from2" =>
    let f ← decFmt j
    let b ← decBuf (← field j "buf")
    let o ← decOff (← field j "off")
    return encL (do structUnpackFromA (← structInit f) b o)
  | "struct.iter2" =>
    let f ← decFmt j
    let b ← decBuf (← field j "buf")
    let ops ← (← (← field j "ops").getArr?).toList.mapM fun o => do
      if (o.getStr?).toOption == some "next" then return (none : Option (Option FmtArg))
      if (o.getStr?).toOption == some "len" then return some none
      return some (some (← decFmtObj o))
    return encPy (fun (x : Json) => x) (do
      let s0 ← structInit f
      let it0 ← structIterUnpackA s0 b
      let mut s := s0
      let mut it := it0
      let mut out : Array Json := #[]
      for op in ops do
        match op with
        | none =>
          let (it', r) := iterNextU s it
          it := it'
          out := out.push (encL (r.map (·.getD [])))
          if let .ok none := r then out := out.push Json.null
        | some none => out := out.push (encPy toJson (iterLenU s it))
        | some (some g) =>
          match structInit g with
          | .ok t => s := t
          | .error _ => pure ()
      return Json.arr out)
  | _ => throw s!"unknown fn {fn}"

end PyLean.TextLibs.Struct
