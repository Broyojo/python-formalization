import PyLean.DiffCore
import PyLean.StrSearch.Diff
import PyLean.UnicodeObj.MethStrip
import PyLean.UnicodeObj.MethPad
import PyLean.UnicodeObj.MethTail

/-! Difftest handler for the `str` method slice (`fn` names start with `meth_`). -/

namespace PyLean.UnicodeObj.MethDiff

open Lean PyLean PyLean.Diff PyLean.StrSearch

def encStr (s : Str) : Json := toJson s

/-- An exception as the Python side reports it. -/
def decExc (cls msg : String) : PyExc :=
  match cls with
  | "ValueError" => .valueError msg
  | "TypeError" => .typeError msg
  | "IndexError" => .indexError msg
  | "OverflowError" => .overflowError msg
  | c => .named c msg

partial def decArg (j : Json) : Except String Arg := do
  match ← getStr j "t" with
  | "int" => return .int (← getInt j "v")
  | "str" => return .str (← getSeq j "s")
  | "none" => return .none
  | "tuple" =>
    let items ← (← field j "items").getArr?
    return .tuple (← items.toList.mapM decArg)
  | "index" =>
    let r ← field j "r"
    let res : Py Int ← match r.getObjVal? "ok" with
      | .ok v => pure (.ok (← v.getInt?))
      | .error _ => pure (.error (decExc (← getStr r "exc") (← getStr r "msg")))
    return .index (← getStr j "tp") res
  | "other" => return .other (← getStr j "tp")
  | t => throw s!"bad arg {t}"

def stripKind : String → Except String StripKind
  | "strip" => .ok .both
  | "lstrip" => .ok .left
  | "rstrip" => .ok .right
  | k => .error s!"bad strip {k}"

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "meth_strip" =>
    let st ← stripKind (← getStr j "op")
    return encPy encStr (doArgstrip (← getSeq j "s") st (← decArg (← field j "chars")))
  | "meth_findchar" =>
    return encPy toJson (.ok (pyUnicodeFindChar (← getSeq j "s") (← getNat j "ch")
      (← getInt j "start") (← getInt j "end") (← getInt j "dir")) : Py Int)
  | "meth_substring" =>
    return encPy encStr (pyUnicodeSubstring (← getSeq j "s") (← getInt j "start") (← getInt j "end"))
  | "meth_pad" =>
    let s ← getSeq j "s"
    let w ← decArg (← field j "width")
    let f ← match j.getObjVal? "fill" with
      | .ok .null | .error _ => pure none
      | .ok v => pure (some (← decArg v))
    let r ← match ← getStr j "op" with
      | "center" => pure (unicodeCenter s w f)
      | "ljust" => pure (unicodeLjust s w f)
      | "rjust" => pure (unicodeRjust s w f)
      | "zfill" => pure (unicodeZfill s w)
      | o => throw s!"bad op {o}"
    return encPy encStr r
  | "meth_startswith" =>
    let s ← getSeq j "s"
    let sub ← decArg (← field j "sub")
    let optArg (k : String) : Except String (Option Arg) := do
      match j.getObjVal? k with
      | .ok .null | .error _ => pure none
      | .ok v => pure (some (← decArg v))
    let st ← optArg "start"
    let en ← optArg "end"
    let r ← match ← getStr j "op" with
      | "startswith" => pure (unicodeStartsEnds "startswith" (-1) s sub st en)
      | "endswith" => pure (unicodeStartsEnds "endswith" 1 s sub st en)
      | o => throw s!"bad op {o}"
    return encPy toJson r
  | "meth_removeaffix" =>
    let s ← getSeq j "s"
    let a ← decArg (← field j "affix")
    let r ← match ← getStr j "op" with
      | "removeprefix" => pure (unicodeRemoveprefix s a)
      | "removesuffix" => pure (unicodeRemovesuffix s a)
      | o => throw s!"bad op {o}"
    return encPy encStr r
  | "meth_tailmatch" =>
    return encPy toJson (pyUnicodeTailmatch (← decArg (← field j "str")) (← decArg (← field j "sub"))
      (← getInt j "start") (← getInt j "end") (← getInt j "dir"))
  | _ => throw s!"unknown fn {fn}"

def handler : Handler := fun fn j =>
  if fn.startsWith "meth_" then some (run fn j) else none

end PyLean.UnicodeObj.MethDiff
