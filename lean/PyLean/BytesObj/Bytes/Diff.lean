import PyLean.DiffCore
import PyLean.BytesObj.Bytes.ByteArray
import PyLean.BytesObj.Bytes.Slots

/-!
Differential-testing handler for bytes and bytearray: `fn` names start with
`bytes.` or `bytearray.`.

An object is a tagged JSON array (see `decObj`); bytes and bytearray results are
`["B", ints]` and `["A", ints]`, a `str` result is `["S", code points]`, a tuple
or list is an array, `None` is `null`. `difftest/bytesobj_diff.py` (family bytes)
builds the real objects from the same encoding.
-/

namespace PyLean.BytesObj.Bytes

open Lean PyLean PyLean.Diff PyLean.StrSearch
open PyLean.RangeSlice (Slice)

/-- An exception by class and message. -/
def decExc (j : Json) : Except String PyExc := do
  let arr ← j.getArr?
  let cls ← (arr.getD 0 Json.null).getStr?
  let msg ← (arr.getD 1 Json.null).getStr?
  if cls = "TypeError" then return .typeError msg
  if cls = "ValueError" then return .valueError msg
  return .named cls msg

partial def decObj (j : Json) : Except String Obj := do
  let arr ← j.getArr?
  let tag ← (arr.getD 0 Json.null).getStr?
  let at' (i : Nat) := arr.getD i Json.null
  let seqAt (i : Nat) : Except String Seq := do
    (← (at' i).getArr?).toList.mapM (·.getNat?)
  match tag with
  | "none" => return .none
  | "bool" => return .bool (← (at' 1).getBool?)
  | "int" => return .int (← (at' 1).getInt?)
  | "pow" => return .int ((← (at' 1).getInt?) ^ (← (at' 2).getNat?))
  | "float" =>
    return .float (Binary64.F64.ofBits (← (at' 7).getNat?))
  | "str" => return .str (← seqAt 1)
  | "bytes" => return .bytes (← seqAt 1)
  | "bytearray" => return .bytearray (← seqAt 1)
  | "memview" => return .memview (← seqAt 1) (← seqAt 2)
  | "list" => return .list (← (← (at' 1).getArr?).toList.mapM decObj)
  | "tuple" => return .tuple (← (← (at' 1).getArr?).toList.mapM decObj)
  | "iter" => return .iter (← (← (at' 1).getArr?).toList.mapM decObj)
  | "iterraises" => return .iterRaises (← (← (at' 1).getArr?).toList.mapM decObj) (← decExc (at' 2))
  | "mapraises" => return .mapRaises (← (← (at' 1).getArr?).toList.mapM decObj) (← decExc (at' 2))
  | "iterhint" =>
    let xs ← (← (at' 1).getArr?).toList.mapM decObj
    match at' 2 with
    | .arr _ => return .iterHint xs (.error (← decExc (at' 2)))
    | h => return .iterHint xs (.ok (← h.getInt?))
  | "itercallraises" => return .iterCallRaises (← decExc (at' 1))
  | "dict" =>
    let items ← (at' 1).getArr?
    let kv ← items.toList.mapM fun p => do
      let pa ← p.getArr?
      let k ← (← (pa.getD 0 Json.null).getArr?).toList.mapM (·.getNat?)
      return (k, ← decObj (pa.getD 1 Json.null))
    return .dict kv
  | "index" => return .index (← (at' 1).getInt?)
  | "indexraises" => return .indexRaises (← decExc (at' 1))
  | "dunder" => return .dunder (← decObj (at' 1))
  | "dunderraises" => return .dunderRaises (← decExc (at' 1))
  | "plain" => return .plain
  | t => throw s!"obj tag {t}"

def fieldObj (j : Json) (k : String) : Except String Obj := do decObj (← field j k)

def optObj (j : Json) (k : String) : Except String (Option Obj) :=
  match j.getObjVal? k with
  | .ok .null | .error _ => .ok none
  | .ok v => some <$> decObj v

def getSeqK (j : Json) (k : String) : Except String Seq := do
  (← (← field j k).getArr?).toList.mapM (·.getNat?)

def optStr (j : Json) (k : String) : Except String (Option String) :=
  match j.getObjVal? k with
  | .ok .null | .error _ => .ok none
  | .ok v => some <$> v.getStr?

def jB (s : Seq) : Json := Json.arr #["B", toJson s]
def jA (s : List Int) : Json := Json.arr #["A", toJson s]
def jS (s : Seq) : Json := Json.arr #["S", toJson s]

def jOptI : Json → Except String (Option Int)
  | .null => .ok none
  | v => some <$> v.getInt?

def getSlice (j : Json) (k : String) : Except String Slice := do
  let arr ← (← field j k).getArr?
  return ⟨← jOptI (arr.getD 0 .null), ← jOptI (arr.getD 1 .null), ← jOptI (arr.getD 2 .null)⟩

def cmpOf : String → Except String CmpOp
  | "lt" => .ok .lt | "le" => .ok .le | "eq" => .ok .eq
  | "ne" => .ok .ne | "gt" => .ok .gt | "ge" => .ok .ge
  | o => .error s!"cmp {o}"

/-- Read-only methods shared by `bytes` and `bytearray`; `wrap` encodes a byte-string
result as the receiver's type. -/
def runCommon (wrap : Seq → Json) (m : String) (s : Seq) (j : Json) :
    Except String (Option Json) := do
  let pyB (r : Py Bool) := encPy toJson r
  let pyI (r : Py Int) := encPy toJson r
  let okB (b : Bool) := encPy toJson (Except.ok b : Py Bool)
  let okW (t : Seq) := Json.mkObj [("ok", wrap t)]
  let st ← getOptInt j "start"
  let en ← getOptInt j "end"
  match m with
  | "isspace" => return some (okB (bytesIsSpace s))
  | "isalpha" => return some (okB (bytesIsAlpha s))
  | "isalnum" => return some (okB (bytesIsAlnum s))
  | "isdigit" => return some (okB (bytesIsDigit s))
  | "islower" => return some (okB (bytesIsLower s))
  | "isupper" => return some (okB (bytesIsUpper s))
  | "istitle" => return some (okB (bytesIsTitle s))
  | "isascii" => return some (okB (bytesIsAscii s))
  | "lower" => return some (okW (bytesLower s))
  | "upper" => return some (okW (bytesUpper s))
  | "title" => return some (okW (bytesTitle s))
  | "capitalize" => return some (okW (bytesCapitalize s))
  | "swapcase" => return some (okW (bytesSwapcase s))
  | "find" => return some (pyI (bytesFindObj s (← fieldObj j "sub") st en true))
  | "rfind" => return some (pyI (bytesFindObj s (← fieldObj j "sub") st en false))
  | "index" => return some (pyI (bytesIndexObj s (← fieldObj j "sub") st en true))
  | "rindex" => return some (pyI (bytesIndexObj s (← fieldObj j "sub") st en false))
  | "count" => return some (pyI (bytesCountObj s (← fieldObj j "sub") st en))
  | "contains" => return some (pyB (bytesContains s (← fieldObj j "sub")))
  | "startswith" =>
    return some (pyB (bytesTailmatchObj s "startswith" (← fieldObj j "sub") (argStart st) (argEnd en) false))
  | "endswith" =>
    return some (pyB (bytesTailmatchObj s "endswith" (← fieldObj j "sub") (argStart st) (argEnd en) true))
  | "hex" =>
    return some (encPy jS (bytesHex s (← optObj j "sep") ((← getOptInt j "n").getD 1)))
  | "decode" => return some (encPy jS (bytesDecode s (← optStr j "enc") (← optStr j "err")))
  | "getslice" => return none
  | _ => return none

/-- A result with its class: `[type name, ["B", ints]]`. -/
def jTB (p : String × Seq) : Json := Json.arr #[toJson p.1, jB p.2]

def runBytes (m : String) (j : Json) : Except String Json := do
  let s ← getSeqK j "s"
  if let some r ← runCommon jB m s j then return r
  match m with
  | "repr" => return encPy jS (bytesRepr s true)
  | "bufinfo" =>
    let (data, ro) := bytesBufferInfo s
    return Json.mkObj [("ok", Json.arr #[toJson data, toJson ro])]
  | "mod" => return encPy jB (bytesMod s (← fieldObj j "arg"))
  | "rmod" =>
    let r := bytesModObj (← fieldObj j "x") (.bytes s)
    return encPy (fun (o : Option Seq) => match o with | some b => jB b | none => "NotImplemented") r
  | "concat" => return encPy jB (bytesConcat (.bytes s) (← fieldObj j "arg"))
  | "mul" => return encPy jB (bytesMul s (← getInt j "n"))
  | "getitem" => return encPy toJson (bytesGetItem s (← getInt j "i"))
  | "getslice" => return encPy jB (bytesGetSlice s (← getSlice j "sl"))
  | "rich" =>
    let r := bytesRichcompareObj (.bytes s) (← fieldObj j "other") (← cmpOf (← getStr j "op"))
    return Json.mkObj [("ok", match r with | some b => toJson b | none => "NotImplemented")]
  | "join" => return encPy jB (pyBytesJoin (.bytes s) (← fieldObj j "it"))
  | "translate" =>
    return encPy jB (bytesTranslate s (← fieldObj j "table") (← optObj j "delete"))
  | "removeprefix" =>
    let a ← fieldObj j "arg"
    return encPy jB ((bytesRemoveprefix s) <$> getBuffer a)
  | "removesuffix" =>
    let a ← fieldObj j "arg"
    return encPy jB ((bytesRemovesuffix s) <$> getBuffer a)
  | "strip" | "lstrip" | "rstrip" =>
    let chars ← optObj j "chars"
    let t := if m = "strip" then StripType.both else if m = "lstrip" then .left else .right
    return encPy jB (do
      let cs ← match chars with
        | none => pure none
        | some o => some <$> getBuffer o
      return bytesStrip s cs t)
  | "new" =>
    return encPy jB (bytesNew (← optObj j "x") (← optStr j "enc") (← optStr j "err"))
  | "fromhex" => return encPy jB (bytesFromHex (← fieldObj j "x"))
  | "strw" =>
    let r := bytesStrW (← getNat j "bw") s
    return encPy (fun (p : Seq × List String) => Json.arr #[jS p.1, toJson p.2]) r
  | "richw" =>
    let r := bytesRichcompareW (← getNat j "bw") (.bytes s) (← fieldObj j "other") (← cmpOf (← getStr j "op"))
    return encPy (fun (p : Option Bool × List String) =>
      Json.arr #[(match p.1 with | some b => toJson b | none => "NotImplemented"), toJson p.2]) r
  | "seqgetitem" => return encPy toJson (pySequenceGetItem s (← getInt j "i"))
  | "getitemobj" => return encPy toJson (bytesSubscriptObj s (← fieldObj j "item"))
  | "getbuffer" =>
    return encPy (fun (p : Seq × Bool) => Json.arr #[toJson p.1, toJson p.2]) (bytesGetBuffer s (← getInt j "flags"))
  | "escapew" =>
    return encPy (fun (p : Seq × Option String) => Json.arr #[jB p.1, Json.null])
      (bytesDecodeEscapeW s (← optStr j "err") true)
  | "partitionobj" | "rpartitionobj" =>
    let f := if m == "partitionobj" then bytesPartitionObj else bytesRPartitionObj
    let enc (o : Obj) : Json := Json.arr #[toJson o.typeName, toJson ((o.buffer?).getD [])]
    return encPy (fun (t : Obj × Obj × Obj) => Json.arr #[enc t.1, enc t.2.1, enc t.2.2])
      (f s (← fieldObj j "sep"))
  | "newsub" =>
    return encPy jTB (bytesNewType "BSubB" (← optObj j "x") (← optStr j "enc") (← optStr j "err"))
  | "fromhexsub" => return encPy jTB (bytesFromHexType "BSubB" (← fieldObj j "x"))
  | "fromhexcls" =>
    -- type(result) for the test's classes: BSubB keeps bytes.__new__ and object.__init__,
    -- BHexInit has `__init__(self, a, b)`, BHexNew has a `__new__` that returns 42
    let call : Option (Seq → Py Json) ← match (← getStr j "cls") with
      | "bytes" => pure none
      | "BSubB" => pure (some fun r => (plainSubCall "BSubB" r).map jTB)
      | "BHexInit" => pure (some fun _ =>
          .error (.typeError "BHexInit.__init__() missing 1 required positional argument: 'b'"))
      | "BHexNew" => pure (some fun _ => .ok (Json.arr #["obj", "int", "42"]))
      | c => throw s!"cls {c}"
    return encPy id (bytesFromHexT (fun r => jTB ("bytes", r)) call (← fieldObj j "x"))
  | "getnewargs" =>
    match bytesGetnewargs s with
    | .tuple [a] => return Json.mkObj [("ok", Json.arr #["tuple", toJson (1 : Nat), toJson a.typeName,
        jB ((a.buffer?).getD [])])]
    | _ => throw "getnewargs"
  | "pickle" =>
    match bytesGetnewargs s with
    | .tuple [a] => return encPy jTB (bytesNewType "BSubB" (some a) none none)
    | _ => throw "pickle"
  | "dunderbytes" => return encPy jTB (.ok (bytesDunderBytes "bytes" s) : Py (String × Seq))
  | "dunderbytessub" => return encPy jTB (.ok (bytesDunderBytes "BSubB" s) : Py (String × Seq))
  | "maketrans" =>
    let ao ← fieldObj j "a"
    let bo ← fieldObj j "b"
    return encPy jB (do
      let a ← getBuffer ao
      let b ← getBuffer bo
      bytesMaketrans a b)
  | "escape" =>
    let r := bytesDecodeEscape s (← optStr j "err")
    return encPy (fun (p : Seq × Option String) =>
      Json.arr #[jB p.1, toJson s.length, match p.2 with | some w => toJson w | none => Json.null]) r
  | "iter" =>
    -- [["next"], ["len"], ["reduce"], ["setstate", n]]: results in order
    let ops ← (← field j "ops").getArr?
    let mut it := bytesIter s
    let mut out : Array Json := #[]
    for op in ops do
      let a ← op.getArr?
      let name ← (a.getD 0 .null).getStr?
      match name with
      | "next" =>
        let (v, it') := striterNext it
        it := it'
        out := out.push (match v with | some x => toJson x | none => "stop")
      | "len" => out := out.push (toJson (striterLen it))
      | "reduce" =>
        out := out.push (match striterReduce it with
          | some (t, i) => Json.arr #[jB t, toJson i]
          | none => "empty")
      | "setstate" =>
        match striterSetstate it (← (a.getD 1 .null).getInt?) with
        | .ok it' => it := it'; out := out.push "ok"
        | .error e => out := out.push (encPy (fun (_ : Unit) => Json.null) (.error e))
      | n => throw s!"iter op {n}"
    return Json.mkObj [("ok", Json.arr out)]
  | "size" => return encPy toJson (pyBytesSize (← fieldObj j "x"))
  | "asstring" => return encPy jB (pyBytesAsString (← fieldObj j "x"))
  | "asstringandsize" =>
    return encPy jB (pyBytesAsStringAndSize (← fieldObj j "x") (← getBool j "wantlen"))
  | "pyconcat" =>
    let (r, e) := pyBytesConcat (some s) (some (← fieldObj j "x")) false
    let (r2, e2) := pyBytesConcat (some s) (some (← fieldObj j "x")) true
    if r != r2 then throw "unique and shared branches disagree"
    let _ := e2
    match r, e with
    | some v, _ => return Json.mkObj [("ok", jB v)]
    | none, some x => return encPy jB (.error x)
    | none, none => throw "no result"
  | "pyjoin" =>
    return encPy jB (pyBytesJoin (← fieldObj j "x") (← fieldObj j "it"))
  | "fromformat" =>
    let args ← (← (← field j "args").getArr?).toList.mapM fun a => do
      let p ← a.getArr?
      let tag ← (p.getD 0 .null).getStr?
      match tag with
      | "i" => return CArg.int (← (p.getD 1 .null).getInt?)
      | "s" => return CArg.str (← (← (p.getD 1 .null).getArr?).toList.mapM (·.getNat?))
      | "p" => return CArg.ptr (← (p.getD 1 .null).getNat?)
      | t => throw s!"carg {t}"
    return encPy jB (bytesFromFormat s args)
  | "privfind" =>
    return encPy toJson (Except.ok (privateBytesFind s (← getSeqK j "n") (← getInt j "off")) : Py Int)
  | other => throw s!"unknown bytes method {other}"

/-- A state machine over `_testcapi.PyBytesWriter`. Each op gives its result and `get_size()`. -/
def runWriter (j : Json) : Except String Json := do
  let ba ← getBool j "ba"
  let known0 : Bool := ← getBool j "known"
  match writerCreate (← getInt j "size") ba with
  | .error e => return encPy (fun (_ : Unit) => Json.null) (.error e)
  | .ok w0 =>
    let mut w := w0
    let mut data : Seq := []
    let mut out : Array Json := #[]
    let none' := Json.mkObj [("ok", Json.null)]
    let err (e : PyExc) : Json := encPy (fun (_ : Unit) => Json.null) (.error e)
    for op in ← (← field j "ops").getArr? do
      let a ← op.getArr?
      let name ← (a.getD 0 .null).getStr?
      let arg (i : Nat) := a.getD i .null
      let bytesAt (i : Nat) : Except String Seq := do (← (arg i).getArr?).toList.mapM (·.getNat?)
      match name with
      | "write" =>
        match writerWriteBytes w data (← bytesAt 1) (← (arg 2).getInt?) with
        | .ok (w', d') => w := w'; data := d'; out := out.push (Json.arr #[none', toJson w.size])
        | .error e => out := out.push (Json.arr #[err e, toJson w.size])
      | "grow" =>
        let n ← (arg 1).getInt?
        match writerGrow w n with
        | .ok w' =>
          w := w'
          data := data.take w.size.toNat
          out := out.push (Json.arr #[none', toJson w.size])
        | .error e => out := out.push (Json.arr #[err e, toJson w.size])
      | "resize" =>
        match writerResize w (← (arg 1).getInt?) with
        | .ok w' =>
          w := w'
          data := data.take w.size.toNat
          out := out.push (Json.arr #[none', toJson w.size])
        | .error e => out := out.push (Json.arr #[err e, toJson w.size])
      | "fmti" | "fmts" =>
        let carg : CArg ← if name == "fmti" then pure (.int (← (arg 2).getInt?)) else pure (.str (← bytesAt 2))
        let (w', text, e) := writerFormat w (← bytesAt 1) [carg]
        w := w'
        data := data ++ text
        out := out.push (Json.arr #[(match e with | some x => err x | none => none'), toJson w.size])
      | "finish" =>
        let k : Int := match (arg 1).getInt? with | .ok k => k | .error _ => w.size
        match writerFinishSize w k with
        | .ok () =>
          let r : List Int := List.replicate k.toNat 0
          out := out.push (Json.arr #[Json.mkObj [("ok", Json.arr #[toJson r.length, toJson ba,
            if known0 then toJson (data.take k.toNat) else Json.null])], toJson (-1 : Int)])
        | .error e => out := out.push (Json.arr #[err e, toJson (-1 : Int)])
      | n => throw s!"writer op {n}"
    return Json.mkObj [("ok", Json.arr out)]

def stJ (b : BA) : Json := Json.arr #[toJson b.data, toJson (baAllocMethod b)]

/-- One mutating or reading operation of the state-machine test. -/
def stepBA (b : BA) (op : Json) : Except String (Json × BA) := do
  let m ← getStr op "m"
  let keep (r : Py BA) : Json × BA :=
    match r with
    | .ok b' => (Json.mkObj [("ok", Json.null)], b')
    | .error e => (encPy (fun (_ : Unit) => Json.null) (.error e), b)
  match m with
  | "append" => return keep (baAppend b (← fieldObj op "x"))
  | "insert" => return keep (baInsert b (← getInt op "i") (← fieldObj op "x"))
  | "pop" =>
    match baPop b (← getOptInt op "i") with
    | .ok (v, b') => return (Json.mkObj [("ok", toJson v)], b')
    | .error e => return (encPy (fun (_ : Unit) => Json.null) (.error e), b)
  | "remove" => return keep (baRemove b (← fieldObj op "x"))
  | "clear" => return keep (baClear b)
  | "reverse" => return (Json.mkObj [("ok", Json.null)], baReverse b)
  | "extend" => return keep (baExtend b (← fieldObj op "x"))
  | "resize" =>
    let n ← getInt op "n"
    match baResizeMethod b n with
    | .ok b' => return (Json.mkObj [("ok", Json.null)], b')
    | .error e => return (encPy (fun (_ : Unit) => Json.null) (.error e), baResizeLeft b n)
  | "take" =>
    match baTakeBytes b (← fieldObj op "x") with
    | .ok (t, b') => return (Json.mkObj [("ok", toJson t)], b')
    | .error e => return (encPy (fun (_ : Unit) => Json.null) (.error e), b)
  | "setitem" => return keep (baAssIndex b (← getInt op "i") (some (← fieldObj op "x")))
  | "delitem" => return keep (baAssIndex b (← getInt op "i") none)
  | "setslice" => return keep (baAssSlice b (← getSlice op "sl") (some (← fieldObj op "x")))
  | "setslice_self" => return keep (baAssSlice b (← getSlice op "sl") (some (.bytearray b.seq)))
  | "delslice" => return keep (baAssSlice b (← getSlice op "sl") none)
  | "iconcat" => return keep (baIConcat b (← fieldObj op "x"))
  | "imul" =>
    match Sequences.repeatCount (← getInt op "n") with
    | .error e => return (encPy (fun (_ : Unit) => Json.null) (.error e), b)
    | .ok n =>
      match baIRepeat b n with
      | .ok b' => return (Json.mkObj [("ok", Json.null)], b')
      | .error e =>
        let n := if n < 0 then 0 else n
        return (encPy (fun (_ : Unit) => Json.null) (.error e),
          if n > 0 ∧ b.size > Int.tdiv baSizeMax n then b else baResizeLeft b (b.size * n))
  | "export" => return (Json.mkObj [("ok", Json.null)], baGetBuffer b)
  | "release" =>
    if b.exports > 0 then return (Json.mkObj [("ok", Json.null)], baReleaseBuffer b)
    else return (Json.mkObj [("ok", Json.null)], b)
  | "copy" =>
    match baCopy b with
    | .ok c => return (Json.mkObj [("ok", stJ c)], b)
    | .error e => return (encPy (fun (_ : Unit) => Json.null) (.error e), b)
  | "getitem" => return (encPy toJson (baGetItem b (← getInt op "i")), b)
  | "getslice" => return (encPy (fun s => jA (seqData s)) (baGetSlice b (← getSlice op "sl")), b)
  | "mul" =>
    match Sequences.repeatCount (← getInt op "n") with
    | .error e => return (encPy (fun (_ : Unit) => Json.null) (.error e), b)
    | .ok n =>
      match baRepeat b n with
      | .ok c => return (Json.mkObj [("ok", stJ c)], b)
      | .error e => return (encPy (fun (_ : Unit) => Json.null) (.error e), b)
  | "concat" =>
    match baConcat (.bytearray b.seq) (← fieldObj op "x") with
    | .ok c => return (Json.mkObj [("ok", stJ c)], b)
    | .error e => return (encPy (fun (_ : Unit) => Json.null) (.error e), b)
  | "init" =>
    let (b', e) := baInit b (← optObj op "x") (← optStr op "enc") (← optStr op "err")
    match e with
    | none => return (Json.mkObj [("ok", Json.null)], b')
    | some x => return (encPy (fun (_ : Unit) => Json.null) (.error x), b')
  | "sizeof" => return (Json.mkObj [("ok", toJson (baSizeof b))], b)
  | "itersetstate" =>
    -- a fresh iterator, `__setstate__(n)`, then `__reduce__`, the hint and `next`
    match baIterSetstate b {} (← getInt op "n") with
    | .error e => return (encPy (fun (_ : Unit) => Json.null) (.error e), b)
    | .ok it =>
      let red := match baIterReduce it with | some i => toJson i | none => "empty"
      let h := baIterLen b it
      let (v, _) := baIterNext b it
      return (Json.mkObj [("ok", Json.arr #[red, toJson h,
        match v with | some x => toJson x | none => "stop"])], b)
  | other => throw s!"unknown bytearray op {other}"

def runBA (m : String) (j : Json) : Except String Json := do
  if m == "ops" then
    let init ← getSeqK j "s"
    let some b0 := (baNew (some (.bytes init)) none none).toOption | throw "init failed"
    let mut b := b0
    let mut it : BAIter := {}
    let mut out : Array Json := #[]
    for op in ← (← field j "ops").getArr? do
      match (← getStr op "m") with
      | "iterstart" =>
        it := {}
        out := out.push (Json.arr #[Json.mkObj [("ok", Json.null)], stJ b])
      | "iternext" =>
        let (v, it') := baIterNext b it
        it := it'
        let r := match v with | some x => toJson x | none => "stop"
        out := out.push (Json.arr #[Json.mkObj [("ok", Json.arr #[r, toJson (baIterLen b it)])], stJ b])
      | _ =>
        let (r, b') ← stepBA b op
        b := b'
        out := out.push (Json.arr #[r, stJ b])
    return Json.mkObj [("ok", Json.arr out)]
  let s ← getSeqK j "s"
  let wrap (t : Seq) : Json := jA (seqData t)
  if let some r ← runCommon wrap m s j then return r
  match m with
  | "repr" => return encPy jS (bytearrayRepr "bytearray" s)
  | "reprsub" => return encPy jS (bytearrayRepr "BSub" s)
  | "bufinfo" =>
    let some b0 := (baNew (some (.bytes s)) none none).toOption | throw "init failed"
    let ((data, ro), _) := baBufferInfo b0
    return Json.mkObj [("ok", Json.arr #[toJson data, toJson ro])]
  | "mod" => return encPy wrap (bytearrayMod s (← fieldObj j "arg"))
  | "rich" =>
    let r := baRichcompare (.bytearray s) (← fieldObj j "other") (← cmpOf (← getStr j "op"))
    return Json.mkObj [("ok", match r with | some b => toJson b | none => "NotImplemented")]
  | "join" => return encPy wrap (stringlibJoin s (← fieldObj j "it"))
  | "translate" =>
    return encPy wrap (bytearrayTranslate s (← fieldObj j "table") (← optObj j "delete"))
  | "removeprefix" =>
    let a ← fieldObj j "arg"
    return encPy wrap ((bytesRemoveprefix s) <$> getBuffer a)
  | "removesuffix" =>
    let a ← fieldObj j "arg"
    return encPy wrap ((bytesRemovesuffix s) <$> getBuffer a)
  | "strip" | "lstrip" | "rstrip" =>
    let chars ← optObj j "chars"
    let t := if m = "strip" then StripType.both else if m = "lstrip" then .left else .right
    return encPy wrap (do
      let cs ← match chars with
        | none => pure none
        | some o => some <$> getBuffer o
      return bytearrayStrip s cs t)
  | "new" =>
    return encPy (fun (b : BA) => jA b.data) (baNew (← optObj j "x") (← optStr j "enc") (← optStr j "err"))
  | "fromhex" => return encPy wrap (bytesFromHex (← fieldObj j "x"))
  | "reduce" =>
    let r := match baReduce s (← getInt j "proto") with
      | .empty => Json.arr #[]
      | .text cs => Json.arr #[jS cs, jS (asc "latin-1")]
      | .bin b => Json.arr #[jB b]
    return Json.mkObj [("ok", r)]
  | "initfail" =>
    -- `b.__init__(items)` on a fresh object; the bytes after the bad item are garbage
    let items ← (← (← field j "items").getArr?).toList.mapM decObj
    let (b, e) := baInit {} (some (.list items)) none none
    let k := (items.findIdx? (fun o => match o with
      | .int v => decide (v < 0 ∨ v ≥ 256) | _ => false)).getD items.length
    return Json.mkObj [("ok", Json.arr #[toJson b.data.length, toJson (b.data.take k),
      toJson (e.map PyExc.className)])]
  | "evilextend" =>
    -- `__buffer__` runs `self.clear()`; the bytes before the value are garbage
    let v : SetVal := { bytes := ← getSeqK j "v", mutate := baClear }
    let some b0 := (baNew (some (.bytes s)) none none).toOption | throw "init failed"
    match baExtendBuffer b0 v with
    | .ok b =>
      return Json.mkObj [("ok", Json.arr #[toJson b.data.length,
        toJson (b.data.drop s.length)])]
    | .error e => return encPy (fun (_ : Unit) => Json.null) (.error e)
  | other => throw s!"unknown bytearray method {other}"

def handler : Handler := fun fn j =>
  if fn == "bytes.writer" then some (runWriter j)
  else if fn.startsWith "bytes." then some (runBytes (fn.drop 6).toString j)
  else if fn.startsWith "bytearray." then some (runBA (fn.drop 10).toString j)
  else none

end PyLean.BytesObj.Bytes
