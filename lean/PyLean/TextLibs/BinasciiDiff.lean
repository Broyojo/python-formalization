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
  let s ← d.getObjVal? "s"
  return .str (← (← s.getArr?).toList.mapM Json.getNat?)

def optData (j : Json) (key : String) : Except String (Option Data) :=
  match j.getObjVal? key with
  | .ok .null | .error _ => .ok none
  | .ok _ => some <$> decData j key

def run (fn : String) (j : Json) : Except String Json := do
  let r (x : Py (List Nat)) := encPy toJson x
  match fn with
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
  | "base64.encode" =>
    let d ← bytesOf j "d"
    return toJsonOk (encodeStream (d.length + 1) d)
  | "base64.decode" =>
    let d ← bytesOf j "d"
    return r (decodeStream (splitLines (d.length + 1) d))
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
