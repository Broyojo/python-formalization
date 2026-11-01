import PyLean.DiffCore
import PyLean.TextLibs.BinasciiRest

/-! `binascii.*` and `base64.*` difftest cases; see `difftest/textlibs_diff.py`. -/

namespace PyLean.TextLibs.Binascii

open Lean PyLean PyLean.Diff

def bytesOf (j : Json) (key : String) : Except String (List Nat) := do
  (← (← field j key).getArr?).toList.mapM Json.getNat?

/-- `{"b": [...]}` is bytes, `{"s": [...]}` is a str by code points. -/
def decData (j : Json) (key : String) : Except String Data := do
  let d ← field j key
  if let .ok b := d.getObjVal? "b" then
    return .bytes (← (← b.getArr?).toList.mapM Json.getNat?)
  if let .ok t := d.getObjVal? "nb" then return .notBuffer (← t.getStr?)
  if let .ok x := d.getObjVal? "rz" then
    let a ← x.getArr?
    let cls ← a[0]!.getStr?
    let msg ← a[1]!.getStr?
    return .raises "BF" (match cls with
      | "TypeError" => .typeError msg
      | "ValueError" => .valueError msg
      | _ => .named cls msg)
  let s ← d.getObjVal? "s"
  return .str (← (← s.getArr?).toList.mapM Json.getNat?)

def optData (j : Json) (key : String) : Except String (Option Data) :=
  match j.getObjVal? key with
  | .ok .null | .error _ => .ok none
  | .ok _ => some <$> decData j key

def decExcJ (j : Json) : Except String PyExc := do
  let a ← j.getArr?
  let cls ← a[0]!.getStr?
  let msg ← a[1]!.getStr?
  return match cls with
    | "TypeError" => .typeError msg
    | "ValueError" => .valueError msg
    | "OverflowError" => .overflowError msg
    | _ => .named cls msg

/-- `true`, `false`, or `{"raise": [cls, msg]}`. -/
def decFlag (j : Json) (key : String) : Except String (Py Bool) := do
  let v ← field j key
  if let .ok x := v.getObjVal? "raise" then return .error (← decExcJ x)
  return .ok (← v.getBool?)

def decIntP (j : Json) (key : String) : Except String (Py Int) := do
  let v ← field j key
  if let .ok x := v.getObjVal? "raise" then return .error (← decExcJ x)
  return .ok (← v.getInt?)

def decSep (j : Json) : Except String SepArg := do
  match j.getObjVal? "sep" with
  | .error _ | .ok .null => return .absent
  | .ok v =>
    if let .ok s := v.getObjVal? "s" then
      return .str (← (← s.getArr?).toList.mapM Json.getNat?)
    if let .ok b := v.getObjVal? "b" then
      return .bytes (← (← b.getArr?).toList.mapM Json.getNat?)
    if let .ok n := v.getObjVal? "len" then return .seqlen (← n.getNat?)
    return .lenRaises (← decExcJ (← field v "raise"))

def decRead (j : Json) : Except String ReadStep := do
  if let .ok k := j.getObjVal? "give" then return .give (← k.getNat?)
  return .raises (← decExcJ (← field j "raise"))

def decWrite (j : Json) : Except String (Py Unit) := do
  if j.isNull then return .ok ()
  return .error (← decExcJ (← field j "raise"))

def encFile (f : FileSim) (r : Py Unit) : Json :=
  Json.mkObj [("ok", Json.mkObj [("written", toJson f.written),
    ("res", encPy (fun _ => Json.null) r)])]

def run (fn : String) (j : Json) : Except String Json := do
  let r (x : Py (List Nat)) := encPy toJson x
  match fn with
  | "binascii.api" =>
    let d ← decData j "d"
    return r (match ← getStr j "op" with
      | "b2a_base64" => b2aBase64A d (.ok true)
      | "a2b_hex" => a2bHexA d
      | "a2b_uu" => a2bUuA d
      | "b2a_uu" => b2aUuA d (.ok false)
      | "crc_hqx" => (do return [← crcHqxA d (.ok 0)])
      | "a2b_qp" => a2bQpA d (.ok false)
      | "b2a_qp" => b2aQpA d (.ok false) (.ok true) (.ok false)
      | _ => a2bBase64A d (.ok false))
  | "binascii.flag" =>
    let d ← decData j "d"
    let f ← decFlag j "f"
    return r (match ← getStr j "op" with
      | "b2a_base64" => b2aBase64A d f
      | "a2b_base64" => a2bBase64A d f
      | "b2a_uu" => b2aUuA d f
      | "a2b_qp" => a2bQpA d f
      | "b2a_qp1" => b2aQpA d f (.ok true) (.ok false)
      | "b2a_qp2" => b2aQpA d (.ok false) f (.ok false)
      | _ => b2aQpA d (.ok false) (.ok true) f)
  | "binascii.hex" =>
    return r (b2aHexA (← decData j "d") (← decSep j) (← decIntP j "group"))
  | "base64.any" => return r (encodeAny (← getStr j "name") (← decData j "d"))
  | "base64.encode_file" =>
    let reads ← (← (← field j "reads").getArr?).toList.mapM decRead
    let writes ← (← (← field j "writes").getArr?).toList.mapM decWrite
    let d ← bytesOf j "d"
    let (f, x) := encodeFile (d.length + reads.length + 4) { data := d, reads, writes }
    return encFile f x
  | "base64.decode_file" =>
    let lines ← (← (← field j "lines").getArr?).toList.mapM fun l => do
      if let .ok x := l.getObjVal? "raise" then return (.error (← decExcJ x) : Py (List Nat))
      return .ok (← (← l.getArr?).toList.mapM Json.getNat?)
    let writes ← (← (← field j "writes").getArr?).toList.mapM decWrite
    let (f, x) := decodeFile lines { data := [], writes }
    return encFile f x
  | "binascii.a2b_base64" => return r (a2bBase64 (← getBool j "strict") (← decData j "d"))
  | "binascii.b2a_base64" =>
    return toJsonOk (b2aBase64 (← bytesOf j "d") (← getBool j "newline"))
  | "binascii.a2b_hex" => return r (a2bHex (← decData j "d"))
  | "binascii.b2a_hex" => return toJsonOk (b2aHex (← bytesOf j "d"))
  | "base64.b64decode" =>
    return r (b64decode (← decData j "d") (← optData j "alt") (← getBool j "validate"))
  | "base64.urlsafe_b64encode" => return toJsonOk (urlsafeEncode (← bytesOf j "d"))
  | "base64.urlsafe_b64decode" => return r (urlsafeDecode (← decData j "d"))
  | "base64.b32encode" => return toJsonOk (b32encode b32alphabet (← bytesOf j "d"))
  | "base64.b32hexencode" => return toJsonOk (b32encode b32hexalphabet (← bytesOf j "d"))
  | "base64.b32decode" =>
    return r (b32decode b32alphabet (← decData j "d") (← getBool j "casefold") (← optData j "map01"))
  | "base64.b32hexdecode" =>
    return r (b32decode b32hexalphabet (← decData j "d") (← getBool j "casefold") none)
  | "base64.b16encode" => return toJsonOk (b16encode (← bytesOf j "d"))
  | "base64.b16decode" => return r (b16decode (← decData j "d") (← getBool j "casefold"))
  | "binascii.a2b_uu" => return r (a2bUu (← decData j "d"))
  | "binascii.b2a_uu" => return r (b2aUu (← bytesOf j "d") (← getBool j "backtick"))
  | "binascii.crc_hqx" => return toJsonOk [crcHqx (← bytesOf j "d") (← getInt j "crc")]
  | "binascii.a2b_qp" => return r (a2bQp (← decData j "d") (← getBool j "header"))
  | "binascii.b2a_qp" =>
    return toJsonOk (b2aQp (← bytesOf j "d") ⟨← getBool j "quotetabs", ← getBool j "istext", ← getBool j "header"⟩)
  | "binascii.qp_bound" =>
    let d ← bytesOf j "d"
    let o : QpOpts := ⟨← getBool j "quotetabs", ← getBool j "istext", ← getBool j "header"⟩
    return Json.mkObj [("ok", toJson (decide
      ((b2aQp d o).length ≤ b2aQpSize o (qpCrlf d) (d.length + 1) none d 0)))]
  | "base64.a85encode" =>
    return toJsonOk (a85encode (← bytesOf j "d") (← getBool j "foldspaces") (← getInt j "wrapcol")
      (← getBool j "pad") (← getBool j "adobe"))
  | "base64.a85decode" =>
    return r (a85decode (← decData j "d") (← getBool j "foldspaces") (← getBool j "adobe")
      (← bytesOf j "ignore"))
  | "base64.b85encode" => return toJsonOk (b85encode (← bytesOf j "d") (← getBool j "pad"))
  | "base64.b85decode" => return r (b85decode (← decData j "d"))
  | "base64.z85encode" => return toJsonOk (z85encode (← bytesOf j "d"))
  | "base64.z85decode" => return r (z85decode (← decData j "d"))
  | "base64.encodebytes" => return toJsonOk (encodebytes (← bytesOf j "d"))
  | "base64.decodebytes" => return r (decodebytes (← bytesOf j "d"))
  | "base64.standard_b64encode" => return r (standardB64encode (← bytesOf j "d"))
  | "base64.standard_b64decode" => return r (standardB64decode (← decData j "d"))
  | "base64.input_check" =>
    let tc : TypeCheck ← match ← getStr j "kind" with
      | "none" => pure (.notBuffer (← getStr j "cls"))
      | _ => pure (.view (← getStr j "format") (← getNat j "ndim") (← getStr j "cls"))
    return encPy (fun _ => Json.null) (inputTypeCheck tc)
  | "base64.main_select" =>
    let flags ← (← (← field j "flags").getArr?).toList.mapM Json.getStr?
    let cs := flags.map (fun f => (f.toList.getD 1 '?'))
    return Json.mkObj [("ok", toJson ((mainSelect cs (some true)).map (fun b => if b then "encode" else "decode")))]
  | _ => throw s!"unknown fn {fn}"
where
  toJsonOk (l : List Nat) : Json := Json.mkObj [("ok", toJson l)]

end PyLean.TextLibs.Binascii
