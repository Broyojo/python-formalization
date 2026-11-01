import PyLean.DiffCore
import PyLean.StrSearch.Diff
import PyLean.UnicodeObj.CodecProps
import PyLean.UnicodeObj.CodecCharmap

/-! Difftest handler for the codecs slice (`fn` names start with `codec_`). -/

namespace PyLean.UnicodeObj.CodecDiff

open Lean PyLean PyLean.Diff PyLean.StrSearch

def getHandler (j : Json) : Except String ErrHandler := do
  match ← getStr j "errors" with
  | "strict" => return .strict
  | "ignore" => return .ignore
  | "replace" => return .replace
  | "surrogateescape" => return .surrogateescape
  | "backslashreplace" => return .backslashreplace
  | "surrogatepass" => return .surrogatepass
  | "xmlcharrefreplace" => return .xmlcharrefreplace
  | "namereplace" => return .namereplace
  | e => throw s!"bad handler {e}"

/-- The name table of a case: `[[key, value], ...]` of lists and ints. -/
def getNames (j : Json) : Except String (List (List Nat × Nat)) := do
  match j.getObjVal? "names" with
  | .error _ => return []
  | .ok v =>
    (← v.getArr?).toList.mapM fun e => do
      let pair ← e.getArr?
      return (← (← pair[0]!.getArr?).toList.mapM (·.getNat?), ← pair[1]!.getNat?)

/-- The reverse table, for `namereplace`. -/
def getCodeNames (j : Json) : Except String (Nat → Option Str) := do
  let l ← getNames j
  return fun c => (l.find? (·.2 == c)).map (·.1)

def getMapItem (j : Json) : Except String MapItem := do
  match ← getStr j "t" with
  | "none" => return .pyNone
  | "int" => return .int (← getInt j "v")
  | "str" => return .str (← getSeq j "s")
  | "wrong" => return .wrong
  | "raise" => return .raises (.valueError "boom")
  | t => throw s!"bad item {t}"

def getDecMap (j : Json) : Except String DecMap := do
  match ← getStr j "k" with
  | "str" => return .str (← getSeq j "table")
  | _ =>
    let arr ← (← field j "table").getArr?
    let items ← arr.toList.mapM fun e => do
      let pair ← e.getArr?
      return (← pair[0]!.getNat?, ← getMapItem pair[1]!)
    return .map fun c => (items.lookup c).getD .missing

def getEncMap (j : Json) : Except String EncMap := do
  match ← getStr j "k" with
  | "build" =>
    match buildEncodingMap (← getSeq j "table") with
    | .trie t => return .trie t
    | .dict d => return .map fun c => match d.lookup c with
      | some v => .int v
      | none => .missing
  | _ =>
    let arr ← (← field j "table").getArr?
    let items ← arr.toList.mapM fun e => do
      let pair ← e.getArr?
      let i := pair[1]!
      let item : EncItem ← match ← getStr i "t" with
        | "none" => pure .pyNone
        | "int" => pure (.int (← getInt i "v"))
        | "bytes" => pure (.bytes (← getSeq i "s"))
        | "wrong" => pure (.wrong "float")
        | "raise" => pure (.raises (.valueError "boom"))
        | t => throw s!"bad item {t}"
      return (← pair[0]!.getNat?, item)
    return .map fun c => (items.lookup c).getD .missing

def encPair (p : Str × Nat) : Json := Json.arr #[toJson p.1, toJson p.2]

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "codec_utf8_decode" =>
    return encPy toJson (utf8Decode (← getSeq j "b") (← getHandler j))
  | "codec_utf8_stateful" =>
    return encPy (fun (p : Str × Nat) => Json.arr #[toJson p.1, toJson p.2])
      (utf8DecodeStateful (← getSeq j "b") (← getHandler j))
  | "codec_wide_decode" =>
    let f := if (← getNat j "width") == 2 then utf16DecodeFull else utf32DecodeFull
    return encPy (fun (p : Str × Nat) => Json.arr #[toJson p.1, toJson p.2])
      (f (← getSeq j "b") (← getInt j "bo") (← getHandler j) (← getBool j "final"))
  | "codec_wide_encode" =>
    let f := if (← getNat j "width") == 2 then utf16EncodeFull else utf32EncodeFull
    return encPy toJson (f (← getSeq j "s") (← getInt j "bo") (← getHandler j) (fun _ => none))
  | "codec_ucs1_encode" =>
    return encPy toJson (ucs1Encode (← getSeq j "s") (← getNat j "limit") (← getHandler j)
      (← getCodeNames j))
  | "codec_ascii_decode" => return encPy toJson (asciiDecode (← getSeq j "b") (← getHandler j))
  | "codec_latin1_decode" =>
    return encPy toJson (.ok (latin1Decode (← getSeq j "b")) : Py Str)
  | "codec_ue_decode" =>
    let names ← getNames j
    return encPy encPair (unicodeEscapeDecode (← getSeq j "b") (← getHandler j)
      (fun n => names.lookup n) (← getBool j "final"))
  | "codec_ue_encode" => return encPy toJson (.ok (unicodeEscapeEncode (← getSeq j "s")) : Py Bytes)
  | "codec_raw_decode" =>
    return encPy encPair (rawEscapeDecode (← getSeq j "b") (← getHandler j) (← getBool j "final"))
  | "codec_raw_encode" => return encPy toJson (.ok (rawEscapeEncode (← getSeq j "s")) : Py Bytes)
  | "codec_utf7_decode" =>
    return encPy encPair (utf7Decode (← getSeq j "b") (← getHandler j) (← getBool j "final"))
  | "codec_utf7_encode" => return encPy toJson (.ok (utf7Encode (← getSeq j "s")) : Py Bytes)
  | "codec_charmap_decode" =>
    return encPy toJson (charmapDecode (← getSeq j "b") (← getDecMap (← field j "map")) (← getHandler j))
  | "codec_charmap_encode" =>
    return encPy toJson (charmapEncode (← getSeq j "s") (← getEncMap (← field j "map")) (← getHandler j)
      (← getCodeNames j))
  | "codec_charmap_build" =>
    let v : Json := match buildEncodingMap (← getSeq j "table") with
      | .dict d => Json.arr (d.map fun e => Json.arr #[toJson e.1, toJson e.2]).toArray
      | .trie t => toJson (encodingMapSize t)
    return Json.mkObj [("ok", v)]
  | "codec_dispatch" =>
    let b ← getSeq j "b"
    let r : Py Str := match shortcutOf (← getSeq j "name") with
      | .utf8 => utf8Decode b .strict
      | .utf16 => (utf16DecodeFull b 0 .strict true).map (·.1)
      | .utf32 => (utf32DecodeFull b 0 .strict true).map (·.1)
      | .ascii => asciiDecode b .strict
      | .latin1 => .ok (latin1Decode b)
      | .registry => .error .modelFuel
    return encPy toJson r
  | "codec_utf8_encode" =>
    return encPy toJson (utf8Encode (← getSeq j "s") (← getHandler j))
  | _ => throw s!"unknown fn {fn}"

def handler : PyLean.Diff.Handler := fun fn j =>
  if fn.startsWith "codec_" then some (run fn j) else none

end PyLean.UnicodeObj.CodecDiff
