import PyLean.DiffCore
import PyLean.StrSearch.Model

/-!
Differential-testing handler for `strsearch` cases (`"mod": "strsearch"`).

Every case carries `"ty"` (`"str"`, `"bytes"` or `"bytearray"`) and `"s"`, the
receiver as a list of code points / byte values. Sequences in arguments and
results are lists of ints; `null` or a missing key is `None`.
-/

namespace PyLean.StrSearch

open Lean PyLean PyLean.Diff

def encSeq (s : Seq) : Json := toJson s

def encSeqs (l : List Seq) : Json := Json.arr (l.map encSeq).toArray

def encTriple (t : Seq × Seq × Seq) : Json := Json.arr #[encSeq t.1, encSeq t.2.1, encSeq t.2.2]

def getSeq (j : Json) (key : String) : Except String Seq := do
  let arr ← (← field j key).getArr?
  arr.toList.mapM (·.getNat?)

def getOptSeq (j : Json) (key : String) : Except String (Option Seq) :=
  match j.getObjVal? key with
  | .ok .null | .error _ => .ok none
  | .ok v => do
    let arr ← v.getArr?
    return some (← arr.toList.mapM (·.getNat?))

def getIntD (j : Json) (key : String) (d : Int) : Except String Int := do
  return (← getOptInt j key).getD d

def getAffix (j : Json) : Except String Affix :=
  match j.getObjVal? "tuple" with
  | .ok v => do
    let arr ← v.getArr?
    let ps ← arr.toList.mapM fun p => do (← p.getArr?).toList.mapM (·.getNat?)
    return .tuple ps
  | .error _ => do return .one (← getSeq j "prefix")

def stripType : String → Option StripType
  | "strip" => some .both
  | "lstrip" => some .left
  | "rstrip" => some .right
  | _ => none

def run (fn : String) (j : Json) : Except String Json := do
  let ty ← getStr j "ty"
  let isStr := ty == "str"
  let isBA := ty == "bytearray"
  let s ← getSeq j "s"
  let start ← getOptInt j "start"
  let «end» ← getOptInt j "end"
  let bsub : Except String BSub := do
    match j.getObjVal? "subint" with
    | .ok v => return .byte (← v.getInt?)
    | .error _ => return .buf (← getSeq j "sub")
  match fn with
  | "find" | "rfind" =>
    let fwd := fn == "find"
    if isStr then return encPy toJson (.ok (strFind s (← getSeq j "sub") start «end» fwd) : Py Int)
    else return encPy toJson (bytesFind s (← bsub) start «end» fwd)
  | "index" | "rindex" =>
    let fwd := fn == "index"
    if isStr then return encPy toJson (strIndex s (← getSeq j "sub") start «end» fwd)
    else return encPy toJson (bytesIndex s (← bsub) start «end» fwd)
  | "count" =>
    if isStr then return encPy toJson (.ok (strCount s (← getSeq j "sub") start «end») : Py Int)
    else return encPy toJson (bytesCount s (← bsub) start «end»)
  | "startswith" | "endswith" =>
    let a ← getAffix j
    let r := match isStr, fn == "startswith" with
      | true, true => strStartswith s a start «end»
      | true, false => strEndswith s a start «end»
      | false, true => bytesStartswith s a start «end»
      | false, false => bytesEndswith s a start «end»
    return encPy toJson (.ok r : Py Bool)
  | "replace" =>
    let old ← getSeq j "old"
    let new ← getSeq j "new"
    let count ← getIntD j "count" (-1)
    return encPy encSeq (if isStr then strReplace s old new count else bytesReplace s old new count)
  | "split" | "rsplit" =>
    let sep ← getOptSeq j "sep"
    let maxsplit ← getIntD j "maxsplit" (-1)
    let r := match isStr, fn == "split" with
      | true, true => strSplit s sep maxsplit
      | true, false => strRSplit s sep maxsplit
      | false, true => bytesSplit s sep maxsplit
      | false, false => bytesRSplit s sep maxsplit
    return encPy encSeqs r
  | "partition" | "rpartition" =>
    let sep ← getSeq j "sep"
    let r := match isStr, fn == "partition" with
      | true, true => strPartition s sep
      | true, false => strRPartition s sep
      | false, true => bytesPartition s sep
      | false, false => bytesRPartition s sep
    return encPy encTriple r
  | "expandtabs" =>
    let t ← getIntD j "tabsize" 8
    return encPy encSeq (if isStr then strExpandtabs s t else bytesExpandtabs s t)
  | "zfill" =>
    let w ← getInt j "width"
    return encPy encSeq (if isStr then strZfill s w else bytesZfill s w)
  | "center" | "ljust" | "rjust" =>
    let w ← getInt j "width"
    let fill := (← getOptInt j "fill").getD 32 |>.toNat
    let r := match fn, isStr with
      | "center", true => strCenter s w fill
      | "center", false => bytesCenter s w fill
      | "ljust", true => strLjust s w fill
      | "ljust", false => bytesLjust s w fill
      | _, true => strRjust s w fill
      | _, false => bytesRjust s w fill
    return encPy encSeq r
  | "removeprefix" | "removesuffix" =>
    let p ← getSeq j "p"
    let r := match fn == "removeprefix", isStr with
      | true, true => strRemoveprefix s p
      | true, false => bytesRemoveprefix s p
      | false, true => strRemovesuffix s p
      | false, false => bytesRemovesuffix s p
    return encPy encSeq (.ok r : Py Seq)
  | "strip" | "lstrip" | "rstrip" =>
    let some t := stripType fn | throw "unreachable"
    let chars ← getOptSeq j "chars"
    let r := if isStr then strStrip s chars t
      else if isBA then bytearrayStrip s chars t
      else bytesStrip s chars t
    return encPy encSeq (.ok r : Py Seq)
  | "splitlines" =>
    let keep ← getBool j "keepends"
    return encPy encSeqs (.ok (if isStr then strSplitlines s keep else bytesSplitlines s keep) : Py (List Seq))
  | other => throw s!"unknown fn {other}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.StrSearch
