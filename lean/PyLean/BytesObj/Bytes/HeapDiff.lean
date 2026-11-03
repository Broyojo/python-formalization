import PyLean.BytesObj.Bytes.Diff
import PyLean.BytesObj.Bytes.Heap2

/-!
Differential-testing handler for the heap model (`fn` = `bare.<op>`, family `bare` of
`difftest/bytesobj_diff.py`). A case gives the initial bytes `s`, statements `prep` run at top
level, the operation and its arguments. The answer is the operation's result (`{"ok": v}` or
`{"exc": ..}`) and the object afterwards: contents, `__alloc__()`, `ob_start - ob_bytes`,
`ob_exports` and the number of views the callbacks hold. Undefined behaviour is the whole answer.
-/

namespace PyLean.BytesObj.Bytes

open Lean PyLean PyLean.Diff PyLean.StrSearch

def decAct (j : Json) : Except String Act := do
  let arr ← j.getArr?
  match ← (arr.getD 0 .null).getStr? with
  | "set" => return .set (← (arr.getD 1 .null).getInt?) (← (arr.getD 2 .null).getInt?)
  | "resize" => return .resize (← (arr.getD 1 .null).getInt?)
  | "del" => return .delFront (← (arr.getD 1 .null).getInt?)
  | "grab" => return .grab
  | "drop" => return .drop
  | t => throw s!"act {t}"

def decActs (j : Json) : Except String (List Act) := do
  (← j.getArr?).toList.mapM decAct

/-- `["ok", v]` or `["exc", cls, msg]`. -/
def decRes {α : Type} (val : Json → Except String α) (j : Json) : Except String (Py α) := do
  let arr ← j.getArr?
  match ← (arr.getD 0 .null).getStr? with
  | "ok" => return .ok (← val (arr.getD 1 .null))
  | "exc" => return .error (← decExc (Json.arr #[arr.getD 1 .null, arr.getD 2 .null]))
  | t => throw s!"res {t}"

def decSeqJ (j : Json) : Except String Seq := do (← j.getArr?).toList.mapM (·.getNat?)

def decItem (j : Json) : Except String Item := do
  let arr ← j.getArr?
  let at' (i : Nat) := arr.getD i .null
  match ← (at' 0).getStr? with
  | "obj" => return .obj (← decObj (at' 1))
  | "idx" => return .idx (← decActs (at' 1)) (← decRes (·.getInt?) (at' 2))
  | "buf" => return .buf (← decActs (at' 1)) (← decRes decSeqJ (at' 2)) (← decActs (at' 3))
  | "me" => return .me
  | t => throw s!"item {t}"

def decArg (j : Json) : Except String Arg := do
  let arr ← j.getArr?
  let at' (i : Nat) := arr.getD i .null
  match ← (at' 0).getStr? with
  | "obj" => return .obj (← decObj (at' 1))
  | "idx" => return .idx (← decActs (at' 1)) (← decRes (·.getInt?) (at' 2))
  | "buf" => return .buf (← decActs (at' 1)) (← decRes decSeqJ (at' 2)) (← decActs (at' 3))
  | "slen" => return .slen (← decActs (at' 1)) (← decRes (·.getInt?) (at' 2)) (← decSeqJ (at' 3))
  | "it" =>
    let steps ← (← (at' 1).getArr?).toList.mapM fun s => do
      let a ← s.getArr?
      return (← decActs (a.getD 0 .null), ← decItem (a.getD 1 .null))
    let fin ← match at' 3 with
      | .null => pure none
      | e => some <$> decExc e
    return .it steps (← decActs (at' 2)) fin
  | "me" => return .me
  | t => throw s!"arg {t}"

def optArg (j : Json) (k : String) : Except String (Option Arg) :=
  match j.getObjVal? k with
  | .ok .null | .error _ => .ok none
  | .ok v => some <$> decArg v

def argK (j : Json) (k : String) : Except String Arg := do decArg (← field j k)

def decKey (j : Json) : Except String Key := do
  let arr ← j.getArr?
  let opt (i : Nat) : Except String (Option Arg) :=
    match arr.getD i .null with
    | .null => .ok none
    | v => some <$> decArg v
  match ← (arr.getD 0 .null).getStr? with
  | "one" => return .one (← decArg (arr.getD 1 .null))
  | "slice" => return .slice (← opt 1) (← opt 2) (← opt 3)
  | t => throw s!"key {t}"

/-- The `keepends` of `splitlines`: `["tobj", b]`, `["tcls", acts, res]`, `["me"]`. -/
def decTArg (j : Json) : Except String TArg := do
  let arr ← j.getArr?
  match ← (arr.getD 0 .null).getStr? with
  | "tobj" => return .obj (← (arr.getD 1 .null).getBool?)
  | "tcls" => return .cls (← decActs (arr.getD 1 .null)) (← decRes (·.getBool?) (arr.getD 2 .null))
  | "me" => return .me
  | t => throw s!"targ {t}"

def heapStJ (h : H) : Json :=
  Json.arr #[toJson h.ba.data, toJson (baAllocMethod h.ba), toJson h.ba.offset, toJson h.ba.exports,
    toJson h.kept]

def isUB (e : PyExc) : Bool := e.className == "CUndefinedBehaviour"

/-- The answer for a result encoded by `enc`. -/
def heapAns {α : Type} (enc : α → Json) (r : Py α × H) : Json :=
  match r.1 with
  | .error e =>
    if isUB e then encPy (fun (_ : Unit) => Json.null) (.error e)
    else
      -- a message the model does not render compares as "~" (the class still compares)
      let e := if e.message.startsWith "~" then PyExc.named e.className "~" else e
      Json.mkObj [("ok", Json.arr #[encPy (fun (_ : Unit) => Json.null) (.error e), heapStJ r.2])]
  | .ok v => Json.mkObj [("ok", Json.arr #[Json.mkObj [("ok", enc v)], heapStJ r.2])]

def unitJ (_ : Unit) : Json := Json.null

def seqsJ (xs : List Seq) : Json := Json.arr (xs.map (fun s => toJson s)).toArray

def runBare (op : String) (j : Json) : Except String Json := do
  let s ← getSeqK j "s"
  let some b0 := (baNew (some (.bytes s)) none none).toOption | throw "init failed"
  let h0 := runActs { ba := b0 } (← decActs (← field j "prep"))
  let ans {α : Type} (enc : α → Json) (x : E α) : Json := heapAns enc (x h0)
  match op with
  | "find" => return ans toJson (baFindE cRead (← argK j "sub") (← optArg j "start") (← optArg j "end") true)
  | "rfind" => return ans toJson (baFindE cRead (← argK j "sub") (← optArg j "start") (← optArg j "end") false)
  | "index" => return ans toJson (baIndexE cRead (← argK j "sub") (← optArg j "start") (← optArg j "end") true)
  | "rindex" => return ans toJson (baIndexE cRead (← argK j "sub") (← optArg j "start") (← optArg j "end") false)
  | "count" => return ans toJson (baCountE cRead (← argK j "sub") (← optArg j "start") (← optArg j "end"))
  | "startswith" | "endswith" =>
    let sj ← (← field j "sub").getArr?
    let sub ← match ← (sj.getD 0 .null).getStr? with
      | "one" => pure (AffixArg.one (← decArg (sj.getD 1 .null)))
      | _ => pure (AffixArg.tuple (← (← (sj.getD 1 .null).getArr?).toList.mapM decArg))
    return ans toJson (baTailmatchE cRead op sub (← optArg j "start") (← optArg j "end") (op == "endswith"))
  | "contains" => return ans toJson (baContainsE cRead (← argK j "sub"))
  | "strip" | "lstrip" | "rstrip" =>
    let t := if op = "strip" then StripType.both else if op = "lstrip" then .left else .right
    return ans toJson (baStripE true (← optArg j "arg") t)
  | "getitem" =>
    let enc : SubRes → Json := fun r => match r with
      | .byte v => Json.arr #["byte", toJson v]
      | .slice s => Json.arr #["slice", toJson s]
    return ans enc (baSubscriptE (← decKey (← field j "key")))
  | "setsub" => return ans unitJ (baAssSubE (← decKey (← field j "key")) (← optArg j "value"))
  | "sqset" =>
    -- `PySequence_SetItem` / `PySequence_DelItem` add the length to a negative index first
    let i ← getInt j "i"
    let v ← optArg j "value"
    return ans unitJ (do
      let size ← curSize
      baSetItemE (if i < 0 then i + size else i) v)
  | "insert" => return ans unitJ (baInsertE (← argK j "index") (← argK j "item"))
  | "append" => return ans unitJ (baAppendE (← argK j "item"))
  | "remove" => return ans unitJ (baRemoveE (← argK j "item"))
  | "pop" => return ans toJson (baPopE (← optArg j "index"))
  | "take" => return ans toJson (baTakeBytesE (← optArg j "n"))
  | "iadd" => return ans unitJ (baIConcatE (← argK j "other"))
  | "add" => return ans toJson (baConcatE (← argK j "other"))
  | "extend" => return ans unitJ (baExtendE (← argK j "x"))
  | "init" =>
    let enc ← match j.getObjVal? "enc" with
      | .ok .null | .error _ => pure none
      | .ok v => do
        let a ← v.getArr?
        let name ← (a.getD 1 .null).getStr?
        match ← (a.getD 0 .null).getStr? with
        | "builtin" => pure (some (name, Codec.builtin))
        | _ =>
          let res ← decRes decSeqJ (a.getD 3 .null)
          let unique ← (a.getD 4 .null).getBool?
          -- the empty and the one-byte `bytes` are shared singletons, never uniquely referenced
          let unique := unique && (match res with | .ok e => decide (e.length ≥ 2) | .error _ => false)
          pure (some (name, Codec.py (← decActs (a.getD 2 .null)) res unique))
    return ans unitJ (baInitE (← optArg j "x") enc (← optStr j "err"))
  | "translate" => return ans toJson (baTranslateE (← argK j "table") (← optArg j "del"))
  | "split" => return ans seqsJ (baSplitE cRead (← optArg j "sep") (← optArg j "maxsplit") false)
  | "rsplit" => return ans seqsJ (baSplitE cRead (← optArg j "sep") (← optArg j "maxsplit") true)
  | "partition" | "rpartition" =>
    let enc : Seq × Seq × Seq → Json := fun (a, b, c) => Json.arr #[toJson a, toJson b, toJson c]
    return ans enc (baPartitionE (← argK j "sep") (op == "rpartition"))
  | "hex" => return ans toJson (baHexE cRead (← optArg j "sep") (← optArg j "bps"))
  | "join" => return ans toJson (baJoinE cRead (← argK j "it"))
  | "rich" =>
    let enc : Option Bool → Json := fun r => match r with
      | some b => toJson b
      | none => "NotImplemented"
    return ans enc (baRichE cRead (← argK j "other") (← cmpOf (← getStr j "cmp")))
  | "center" | "ljust" | "rjust" =>
    let k := if op = "center" then PadKind.center else if op = "ljust" then .ljust else .rjust
    return ans toJson (baJustE k (← argK j "width") (← optArg j "fill"))
  | "zfill" => return ans toJson (baPadE .zfill (← argK j "width") 0)
  | "resize" => return ans unitJ (baResizeMethodE (← argK j "n"))
  | "pred" =>
    let x ← match ← getStr j "name" with
      | "isalnum" => pure baIsalnumE
      | "isalpha" => pure baIsalphaE
      | "isascii" => pure baIsasciiE
      | "isdigit" => pure baIsdigitE
      | "islower" => pure baIslowerE
      | "isspace" => pure baIsspaceE
      | "istitle" => pure baIstitleE
      | "isupper" => pure baIsupperE
      | n => throw s!"pred {n}"
    return ans toJson x
  | "map" =>
    let x ← match ← getStr j "name" with
      | "capitalize" => pure baCapitalizeE
      | "swapcase" => pure baSwapcaseE
      | "title" => pure baTitleE
      | "upper" => pure baUpperE
      | "lower" => pure baLowerE
      | n => throw s!"map {n}"
    return ans toJson x
  | "replace" => return ans toJson (baReplaceE (← argK j "old") (← argK j "new") (← optArg j "count"))
  | "expandtabs" => return ans toJson (baExpandtabsE (← optArg j "tabsize"))
  | "splitlines" =>
    let k ← match j.getObjVal? "keepends" with
      | .ok .null | .error _ => pure none
      | .ok v => some <$> decTArg v
    return ans seqsJ (baSplitlinesTE k)
  | other => throw s!"unknown bare op {other}"

def heapHandler : Handler := fun fn j =>
  if fn.startsWith "bare." then some (runBare (fn.drop 5).toString j) else none

end PyLean.BytesObj.Bytes
