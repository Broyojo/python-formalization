import PyLean.DiffCore
import PyLean.TextLibs.BinasciiC

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

def optBool (j : Json) (key : String) (dflt : Bool) : Bool :=
  match j.getObjVal? key with
  | .ok v => (v.getBool?).toOption.getD dflt
  | .error _ => dflt

def optInt (j : Json) (key : String) (dflt : Int) : Int :=
  match j.getObjVal? key with
  | .ok v => (v.getInt?).toOption.getD dflt
  | .error _ => dflt

/-- `strict_mode`, when given. -/
def optBoolO (j : Json) (key : String) : Option Bool :=
  match j.getObjVal? key with
  | .ok v => (v.getBool?).toOption
  | .error _ => none

/-- `null`, `{"b": [...]}` or `{"ty": name}`. -/
def decAlpha (j : Json) : Except String AlphaArg := do
  match j.getObjVal? "alpha" with
  | .error _ | .ok .null => return .absent
  | .ok v =>
    if let .ok t := v.getObjVal? "ty" then return .other (← t.getStr?)
    return .bytes (← (← (← v.getObjVal? "b").getArr?).toList.mapM Json.getNat?)

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
  let dflt : Data := .bytes []
  let ig0 ← optData j "ig"
  let igD := ig0.getD dflt
  let alpha := ((optData j "alpha").toOption).join
  match fn with
  | "binascii.api" =>
    let d ← decData j "d"
    return r (match ← getStr j "op" with
      | "b2a_base64" => b2aBase64A d (.ok true)
      | "a2b_hex" => a2bHexI d dflt
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
  | "base64.any" => return r (encodeAnyC (← getStr j "name") (← decData j "d"))
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
  | "binascii.a2b_base64" =>
    return r (a2bB64 (← decData j "d") (optBoolO j "strict") (optBool j "padded" true) (← decAlpha j) ig0
      (optBool j "canonical" false))
  | "binascii.b2a_base64" =>
    return r (b2aB64 (.bytes (← bytesOf j "d")) (optBool j "padded" true) (optInt j "wrapcol" 0)
      (optBool j "newline" true) alpha)
  | "binascii.a2b_base32" =>
    return r (a2bB32 (← decData j "d") (optBool j "padded" true) (← decAlpha j) igD (optBool j "canonical" false))
  | "binascii.b2a_base32" =>
    return r (b2aB32 (.bytes (← bytesOf j "d")) (optBool j "padded" true) (optInt j "wrapcol" 0) alpha)
  | "binascii.a2b_ascii85" =>
    return r (a2bA85 (← decData j "d") (optBool j "foldspaces" false) (optBool j "adobe" false) igD
      (optBool j "canonical" false))
  | "binascii.b2a_ascii85" =>
    return r (b2aA85 (.bytes (← bytesOf j "d")) (optBool j "foldspaces" false) (optInt j "wrapcol" 0)
      (optBool j "pad" false) (optBool j "adobe" false))
  | "binascii.a2b_base85" =>
    return r (a2bB85 (← decData j "d") (← decAlpha j) igD (optBool j "canonical" false))
  | "binascii.b2a_base85" =>
    return r (b2aB85 (.bytes (← bytesOf j "d")) (optBool j "pad" false) (optInt j "wrapcol" 0) alpha)
  | "binascii.a2b_hex" => return r (a2bHexI (← decData j "d") igD)
  | "binascii.b2a_hex" => return toJsonOk (b2aHex (← bytesOf j "d"))
  | "base64.b64encode" =>
    let alt := (← optData j "alt").bind fun | .bytes b => some b | _ => none
    return r (pyB64encode (.bytes (← bytesOf j "d")) alt (optBool j "padded" true) (optInt j "wrapcol" 0))
  | "base64.b64decode" =>
    return r (pyB64decode (← decData j "d") (← optData j "alt") (optBoolO j "validate")
      (optBool j "padded" true) ig0 (optBool j "canonical" false))
  | "base64.urlsafe_b64encode" => return r (pyUrlsafeEnc (.bytes (← bytesOf j "d")) (optBool j "padded" true))
  | "base64.urlsafe_b64decode" => return r (pyUrlsafeDec (← decData j "d") (optBool j "padded" false))
  | "base64.b32encode" =>
    return r (b2aB32 (.bytes (← bytesOf j "d")) (optBool j "padded" true) (optInt j "wrapcol" 0) none)
  | "base64.b32hexencode" =>
    return r (b2aB32 (.bytes (← bytesOf j "d")) (optBool j "padded" true) (optInt j "wrapcol" 0)
      (some (.bytes b32hexAlpha)))
  | "base64.b32decode" =>
    return r (pyB32decode (← decData j "d") (← getBool j "casefold") (← optData j "map01")
      (optBool j "padded" true) igD (optBool j "canonical" false))
  | "base64.b32hexdecode" =>
    return r (pyB32hexdecode (← decData j "d") (← getBool j "casefold") (optBool j "padded" true) igD
      (optBool j "canonical" false))
  | "base64.b16encode" => return r (pyB16encode (.bytes (← bytesOf j "d")) (optInt j "wrapcol" 0))
  | "base64.b16decode" => return r (pyB16decode (← decData j "d") (← getBool j "casefold") igD)
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
    return r (b2aA85 (.bytes (← bytesOf j "d")) (← getBool j "foldspaces") (← getInt j "wrapcol")
      (← getBool j "pad") (← getBool j "adobe"))
  | "base64.a85decode" =>
    return r (a2bA85 (← decData j "d") (← getBool j "foldspaces") (← getBool j "adobe")
      (.bytes (← bytesOf j "ignore")) (optBool j "canonical" false))
  | "base64.b85encode" =>
    return r (b2aB85 (.bytes (← bytesOf j "d")) (← getBool j "pad") (optInt j "wrapcol" 0) none)
  | "base64.b85decode" => return r (a2bB85 (← decData j "d") .absent igD (optBool j "canonical" false))
  | "base64.z85encode" =>
    return r (b2aB85 (.bytes (← bytesOf j "d")) (optBool j "pad" false) (optInt j "wrapcol" 0)
      (some (.bytes z85Alpha)))
  | "base64.z85decode" =>
    return r (a2bB85 (← decData j "d") (.bytes z85Alpha) igD (optBool j "canonical" false))
  | "base64.encodebytes" => return toJsonOk (pyEncodebytes (← bytesOf j "d"))
  | "base64.decodebytes" => return r (decodebytes (← bytesOf j "d"))
  | "base64.standard_b64encode" => return r (pyB64encode (.bytes (← bytesOf j "d")) none true 0)
  | "base64.standard_b64decode" => return r (pyB64decode (← decData j "d") none none true none false)
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
