import PyLean.DiffCore
import PyLean.StrSearch.Diff
import PyLean.UnicodeObj.CodecProps

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
  | "codec_utf8_encode" =>
    return encPy toJson (utf8Encode (← getSeq j "s") (← getHandler j))
  | _ => throw s!"unknown fn {fn}"

def handler : PyLean.Diff.Handler := fun fn j =>
  if fn.startsWith "codec_" then some (run fn j) else none

end PyLean.UnicodeObj.CodecDiff
