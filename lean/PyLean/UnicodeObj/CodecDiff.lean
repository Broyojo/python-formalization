import PyLean.DiffCore
import PyLean.StrSearch.Diff
import PyLean.UnicodeObj.CodecProps
import PyLean.UnicodeObj.CodecCharmap
import PyLean.UnicodeObj.CodecCallback
import PyLean.UnicodeObj.ObjectAscii

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

/-- One step of a scripted decode handler, given where the error ended. -/
def getDecResp (j : Json) : Except String (Nat → DecResp) := do
  match ← getStr j "t" with
  | "raise" => return fun _ => .raises (.valueError "boom")
  | "bad" => return fun _ => .bad
  | "ret" =>
    let oj ← field j "obj"
    let obj : ObjEdit ← match ← getStr oj "k" with
      | "keep" => pure .keep
      | "set" => pure (.set (← getSeq oj "b"))
      | "wrong" => pure .wrongType
      | "del" => pure .deleted
      | k => throw s!"bad obj {k}"
    let rep ← getSeq j "rep"
    let pos ← getInt j "pos"
    if (← getBool j "rel") then return fun stop => .ret rep (stop + pos) obj
    else return fun _ => .ret rep pos obj
  | t => throw s!"bad step {t}"

/-- One step of a scripted encode handler. -/
def getEncResp (j : Json) : Except String (Nat → EncResp) := do
  match ← getStr j "t" with
  | "raise" => return fun _ => .raises (.valueError "boom")
  | "bad" => return fun _ => .bad
  | "badrep" =>
    let pos ← getInt j "pos"
    return fun _ => .badRep pos
  | "str" | "bytes" =>
    let w ← getSeq j "rep"
    let rep : EncRep := if (← getStr j "t") == "str" then .str w else .bytes w
    let pos ← getInt j "pos"
    if (← getBool j "rel") then return fun stop => .ret rep (stop + pos)
    else return fun _ => .ret rep pos
  | t => throw s!"bad step {t}"

/-- A handler from a finite script. Past the end it raises, as the Python side does, so a
handler that keeps moving the position back cannot run for ever on either side. -/
def scriptDec (items : List (Nat → DecResp)) : DecCB := fun hist =>
  match items[hist.length - 1]? with
  | some f => f ((hist.getLast?.map (·.stop)).getD 0)
  | none => .raises (.named "RuntimeError" "done")

def scriptEnc (items : List (Nat → EncResp)) : EncCB := fun hist =>
  match items[hist.length - 1]? with
  | some f => f ((hist.getLast?.map (·.stop)).getD 0)
  | none => .raises (.named "RuntimeError" "done")

def getDH (j : Json) : Except String DH := do
  match j.getObjVal? "missing" with
  | .ok _ => return .missing "uo_nonesuch"
  | .error _ =>
    let arr ← (← field j "script").getArr?
    return .custom (scriptDec (← arr.toList.mapM getDecResp))

/-- A handler by name, a script, or a missing one. -/
def getDHX (j : Json) : Except String DH := do
  match j.getObjVal? "handler" with
  | .ok _ => return .std (← getHandler (Json.mkObj [("errors", ← field j "handler")]))
  | .error _ => getDH j

def getEH (j : Json) : Except String EH := do
  match j.getObjVal? "missing" with
  | .ok _ => return .missing "uo_nonesuch"
  | .error _ =>
    let arr ← (← field j "script").getArr?
    return .custom (scriptEnc (← arr.toList.mapM getEncResp))

/-- Enough for scripts of a few steps, each of which can restart a short input. -/
def cbFuel : Nat := 400

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

/-- What `Chunked` compares, as far as the first and second chunk got, with the values consumed. -/
def chunkView (dec : Bytes → Bool → Py (Str × Nat)) (b : Bytes) (k : Nat) : Json :=
  let whole : Json := match dec b true with
    | .ok (s, n) => Json.arr #[toJson s, toJson n]
    | .error _ => Json.null
  match dec (b.take k) false with
  | .error _ => Json.arr #["first", whole]
  | .ok (s1, n) =>
    match dec (b.drop n) true with
    | .error _ => Json.arr #["second", toJson s1, toJson n, whole]
    | .ok (s2, m) => Json.arr #["both", toJson s1, toJson n, toJson s2, toJson m, whole]

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
  | "codec_utf8_obj" =>
    let b ← getSeq j "b"
    let consumed ← (← field j "consumed").getBool?
    let enc (r : (Str × Kind) × Nat) : Json :=
      Json.arr #[toJson r.1.1, toJson r.1.2.width, toJson (r.1.2 == .ascii),
        toJson (if consumed then r.2 else 0)]
    if (j.getObjVal? "null").toOption.isSome then
      return encPy enc (unicodeDecodeUtf8 b (.std .strict) true consumed (b.length + 100))
    else
      return encPy enc (unicodeDecodeUtf8 b (← getDHX j) false consumed (b.length + 100))
  | "codec_utf8_writer" =>
    let b ← getSeq j "b"
    let consumed ← (← field j "consumed").getBool?
    let pre ← getSeq j "pre"
    let w0 : UWriter := if pre.isEmpty then {} else { text := pre, cap := prepareCap 0 (maxCharOf pre) }
    let (w1, r) := writerDecodeStateful w0 b (b.length : Int) (← getDHX j) consumed (b.length + 100)
    let (text, kind) := w1.finish
    return encPy (fun (x : Json) => x) (.ok (Json.arr #[encPy (fun (_ : Nat) => Json.null) r,
      toJson (match r with | .ok n => n | .error _ => 0), toJson text, toJson kind.width,
      toJson (kind == .ascii)]))
  | "codec_chunks" =>
    let b ← getSeq j "b"
    let k ← getNat j "k"
    let h ← getHandler j
    let dec : Bytes → Bool → Py (Str × Nat) ← match ← getStr j "codec" with
      | "utf-8" => pure fun x final => utf8DecodeLoop x h (!final) (x.length + 1) 0 x []
      | "utf-16-le" => pure fun x final => utf16DecodeFull x (-1) h final
      | "utf-16-be" => pure fun x final => utf16DecodeFull x 1 h final
      | "utf-32-le" => pure fun x final => utf32DecodeFull x (-1) h final
      | "utf-32-be" => pure fun x final => utf32DecodeFull x 1 h final
      | "raw_unicode_escape" => pure fun x final => rawEscapeDecode x h final
      | "unicode_escape" => pure fun x final => unicodeEscapeDecode x h (fun _ => none) final
      | c => throw s!"bad codec {c}"
    return encPy (fun (x : Json) => x) (.ok (chunkView dec b k))
  | "codec_ascii_obj" =>
    let b ← getSeq j "b"
    let enc (r : Str × Kind) : Json :=
      Json.arr #[toJson r.1, toJson r.2.width, toJson (r.2 == .ascii)]
    return encPy enc (asciiDecodeC b (← getDHX j) (b.length + 100))
  | "codec_cb_decode" =>
    let b ← getSeq j "b"
    let H ← getDH j
    let final ← getBool j "final"
    -- with `final` the consumed count is the original size, not the position: text only
    let enc := fun (r : Py (Str × Nat)) =>
      if final then encPy toJson (r.map (·.1)) else encPy encPair r
    match ← getStr j "codec" with
    | "utf-8" => return enc (utf8DecodeX b H (!final) cbFuel)
    | "utf-16" => return enc (utf16DecodeX b (← getInt j "bo") H final cbFuel)
    | "utf-32" => return enc (utf32DecodeX b (← getInt j "bo") H final cbFuel)
    | "unicode_escape" => return enc (unicodeEscapeDecodeX b H (fun _ => none) final cbFuel)
    | "raw_unicode_escape" => return enc (rawEscapeDecodeX b H final cbFuel)
    | "utf-7" => return enc (utf7DecodeX b H final cbFuel)
    | "ascii" => return encPy toJson (asciiDecodeX b H cbFuel)
    | "charmap" => return encPy toJson (charmapDecodeX b (.str (← getSeq j "table")) H cbFuel)
    | c => throw s!"bad codec {c}"
  | "codec_cb_encode" =>
    let s ← getSeq j "s"
    let H ← getEH j
    let nameOf : Nat → Option Str := fun _ => none
    match ← getStr j "codec" with
    | "ascii" => return encPy toJson (ucs1EncodeLoopX s 128 H nameOf cbFuel [] 0 s [])
    | "latin-1" => return encPy toJson (ucs1EncodeLoopX s 256 H nameOf cbFuel [] 0 s [])
    | "utf-8" => return encPy toJson (utf8EncodeLoopX s H nameOf cbFuel [] 0 s [])
    | "utf-16" => return encPy toJson (utf16EncodeX s (← getInt j "bo") H nameOf cbFuel)
    | "utf-32" => return encPy toJson (utf32EncodeX s (← getInt j "bo") H nameOf cbFuel)
    | "charmap" =>
      return encPy toJson (charmapEncodeLoopX s (← getEncMap (← field j "map")) H nameOf cbFuel [] 0 s [])
    | c => throw s!"bad codec {c}"
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
