import PyLean.DiffCore
import PyLean.TextLibs.BinasciiModel

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
  | _ => throw s!"unknown fn {fn}"
where
  toJsonOk (l : List Nat) : Json := Json.mkObj [("ok", toJson l)]

end PyLean.TextLibs.Binascii
