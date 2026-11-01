import PyLean.DiffCore
import PyLean.BytesObj.Mem.Model

/-! Differential-testing handler for memoryview: `fn` names start with `mem.`.

`mem.script` runs one script. `"mem"` is the byte store, `"exps"` the exporters laid out
in it (their full `Py_buffer`), `"ops"` a list of operations on numbered handles, and the
result is the list of the operations' results. A handle `h` means `h % len(handles)`, and
an operation with no live handle returns `{"skip": true}`; both sides do the same (see the
`family mem` section of `difftest/bytesobj_diff.py`). -/

namespace PyLean.BytesObj.Mem

open Lean PyLean PyLean.Diff
open PyLean.RangeSlice (Slice)

/-- One script run. -/
structure DS where
  st : St
  /-- Model numbers of the handles, in Python's order. -/
  handles : Array Nat := #[]
  iters : Array Nat := #[]
  dropped : List Nat := []
  exps : Array Buf := #[]
  /-- Exporters with a raw (unregistered) view: the difftest must not reallocate them. -/
  pinned : List Nat := []

def okJ (v : Json) : Json := Json.mkObj [("ok", v)]
def errJ (e : PyExc) : Json := Json.mkObj [("exc", toJson e.className), ("msg", toJson e.message)]
def skipJ : Json := Json.mkObj [("skip", toJson true)]
def bytesJ (l : List Nat) : Json := Json.mkObj [("bytes", toJson l)]

def itemJ : Item → Json
  | .int n => toJson n
  | .bool b => Json.mkObj [("bool", toJson b)]
  | .float d => Json.mkObj [("float", toJson d)]
  | .bytes b => bytesJ b

partial def treeJ : Tree → Json
  | .leaf i => itemJ i
  | .node l => Json.arr (l.map treeJ).toArray

def jOpt (j : Json) (f : Json → Except String α) : Except String (Option α) :=
  match j with
  | .null => .ok none
  | v => some <$> f v

def jChars (j : Json) : Except String (List Char) := do return (← j.getStr?).toList

def jInts (j : Json) : Except String (List Int) := do
  (← j.getArr?).toList.mapM (·.getInt?)

def jNats (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM (·.getNat?)

def jBuf (j : Json) (i : Nat) : Except String Buf := do
  return { obj := some (.exp i)
           buf := ← getInt j "buf", len := ← getInt j "len", itemsize := ← getInt j "itemsize"
           readonly := ← getBool j "readonly", ndim := ← getNat j "ndim"
           format := some (← getStr j "format").toList
           shape := ← jOpt (← field j "shape") jInts
           strides := ← jOpt (← field j "strides") jInts
           suboffsets := ← jOpt (← field j "suboffsets") jInts }

def jUnhash (j : Json) : Except String (Option PyExc) := do
  match ← field j "unhash" with
  | .null => return none
  | v =>
    let c ← getStr v "cls"
    let m ← getStr v "msg"
    return some (if c == "TypeError" then .typeError m else .valueError m)

def DS.pick (d : DS) (h : Int) : Option Nat :=
  if d.handles.isEmpty then none
  else
    let i := (h % (d.handles.size : Int)).toNat
    let id := d.handles[i]!
    if d.dropped.contains id then none else some id

def jRel (d : DS) (j : Json) : Except String (Option Nat) :=
  match j.getObjVal? "rel" with
  | .ok .null | .error _ => .ok none
  | .ok v => do return d.pick (← v.getInt?)

/-- The exceptions the Python twins of the callbacks raise (`_RAISES`), all with `boom`. -/
def excOf (cls : String) : PyExc :=
  match cls with
  | "ValueError" => .valueError "boom"
  | "TypeError" => .typeError "boom"
  | "OverflowError" => .overflowError "boom"
  | c => .named c "boom"

/-- How a callback ends: `{"raise": cls}`, `{"wrong": type}`, or its value. -/
def jRet {α : Type} (value : Except String α) (v : Json) : Except String (Ret α) := do
  if let .ok c := v.getObjVal? "raise" then return .raises (excOf (← c.getStr?))
  if let .ok w := v.getObjVal? "wrong" then return .wrong (← w.getStr?)
  return .val (← value)

/-- An argument object; `none` when it names a dead handle. -/
def jObj (d : DS) (j : Json) : Except String (Option Obj) := do
  match j with
  | .null => return some .none
  | .num _ => return some (.int (← j.getInt?))
  | .obj _ =>
    if let .ok v := j.getObjVal? "bool" then return some (.bool (← v.getBool?))
    if let .ok v := j.getObjVal? "float" then return some (.float (← v.getNat?))
    if let .ok v := j.getObjVal? "bytes" then return some (.bytes (← jNats v))
    if let .ok v := j.getObjVal? "str" then return some (.str (← jChars v))
    if let .ok v := j.getObjVal? "list" then return some (.list (← v.getNat?))
    if let .ok v := j.getObjVal? "mv" then
      return (d.pick (← v.getInt?)).map .view
    if let .ok v := j.getObjVal? "exp" then
      let k ← v.getNat?
      let hook : Option Nat ← match j.getObjVal? "hook" with
        | .ok h => pure (d.pick (← h.getInt?))
        | .error _ => pure none
      let b : Buf := { d.exps[k]! with hook := hook }
      let r ← match j.getObjVal? "end" with
        | .ok e => jRet (.ok b) e
        | .error _ => pure (.val b)
      return some (.exporter r (← jRel d j))
    if let .ok v := j.getObjVal? "idx" then
      return some (.index (← jRet v.getInt? v) (← jRel d j))
    if let .ok v := j.getObjVal? "flt" then
      return some (.floatLike (← jRet v.getNat? v) (← jRel d j))
    if let .ok v := j.getObjVal? "bln" then
      return some (.boolLike (← jRet v.getBool? v) (← jRel d j))
    if let .ok v := j.getObjVal? "lenobj" then
      return some (.lenLike (← jRet v.getInt? v) (← jRel d j))
    if let .ok v := j.getObjVal? "eqobj" then
      return some (.eqLike (← jRet v.getBool? v) (← jRel d j))
    throw "bad object"
  | _ => throw "bad object"

def jSlice (j : Json) : Except String Slice := do
  let arr ← j.getArr?
  let opt (k : Nat) : Except String (Option Int) :=
    jOpt (arr[k]?.getD .null) (·.getInt?)
  return ⟨← opt 0, ← opt 1, ← opt 2⟩

def jKeyElem (d : DS) (j : Json) : Except String (Option KeyElem) := do
  if let .ok v := j.getObjVal? "slice" then
    let fail ← match j.getObjVal? "fail" with
      | .ok f =>
        let part ← match ← getStr f "part" with
          | "start" => pure SlicePart.start
          | "stop" => pure SlicePart.stop
          | "step" => pure SlicePart.step
          | p => throw s!"slice part {p}"
        let how ← match f.getObjVal? "notindex" with
          | .ok _ => pure (Ret.raises (.typeError
              "slice indices must be integers or None or have an __index__ method"))
          | .error _ => jRet (.ok ()) f
        pure (some { part := part, how := how : SliceFail })
      | .error _ => pure none
    return some (.slice (← jSlice v) (← jRel d j) fail)
  return (← jObj d j).map .obj

def jKey (d : DS) (j : Json) : Except String (Option Key) := do
  if let .ok _ := j.getObjVal? "ellipsis" then return some .ellipsis
  if let .ok v := j.getObjVal? "tuple" then
    let es ← (← v.getArr?).toList.mapM (jKeyElem d)
    return (es.mapM id).map .tuple
  return (← jKeyElem d j).map .one

def jCmpOp (s : String) : CmpOp :=
  if s == "eq" then .eq else if s == "ne" then .ne else .other

def jAttr (s : String) : Except String Attr :=
  match s with
  | "obj" => .ok .obj | "nbytes" => .ok .nbytes | "readonly" => .ok .readonly
  | "itemsize" => .ok .itemsize | "format" => .ok .format | "ndim" => .ok .ndim
  | "shape" => .ok .shape | "strides" => .ok .strides | "suboffsets" => .ok .suboffsets
  | "c_contiguous" => .ok .cContiguous | "f_contiguous" => .ok .fContiguous
  | "contiguous" => .ok .contiguous
  | a => .error s!"attr {a}"

def DS.handleOf (d : DS) (id : Nat) : Option Nat := d.handles.findIdx? (· == id)

/-- The JSON of view `id`, registering a new handle when Python would. -/
def DS.reg (d : DS) (id : Nat) : Json × DS :=
  match d.handleOf id with
  | some h => (Json.mkObj [("mv", toJson h)], d)
  | none => (Json.mkObj [("mv", toJson d.handles.size)], { d with handles := d.handles.push id })

def refJ (d : DS) : Option ORef → Json
  | none => .null
  | some (.exp i) => Json.mkObj [("exp", toJson i)]
  | some (.mv i) => Json.mkObj [("mv", toJson ((d.handleOf i).getD 999999))]

def attrJ (d : DS) : AttrVal → Json
  | .obj r => refJ d r
  | .int n => toJson n
  | .bool b => Json.mkObj [("bool", toJson b)]
  | .fmt s => toJson (String.ofList s)
  | .tuple l => toJson l

/-- The result of running `x`, with the new state kept. -/
def runM {α : Type} (d : DS) (x : M α) (enc : DS → α → Json × DS) : Json × DS :=
  let (r, st) := x d.st
  let d := { d with st := st }
  match r with
  | .ok a =>
    let (j, d) := enc d a
    (okJ j, d)
  | .error e => (errJ e, d)

def plain {α : Type} (f : α → Json) : DS → α → Json × DS := fun d a => (f a, d)

def viewRes : DS → Nat → Json × DS := fun d i => d.reg i

def subRes : DS → Sub → Json × DS
  | d, .item x => (itemJ x, d)
  | d, .view i => d.reg i

def argAt (op : Array Json) (k : Nat) : Except String Json :=
  match op[k]? with
  | some v => .ok v
  | none => .error s!"missing argument {k}"

def optArg (op : Array Json) (k : Nat) : Json := op[k]?.getD .null

/-- `true` when view `id` has no other reference, so that dropping it deallocates it. -/
def canDrop (d : DS) (id : Nat) : Bool :=
  getExports d.st id == 0 &&
    !d.st.iters.any (fun it => it.seq == some id) &&
    !d.st.mbufs.any (fun b => !b.released && b.master.obj == some (.mv id))

/-- A `bytearray` with no live managed buffer can be resized. -/
def canResize (d : DS) (k : Nat) : Bool :=
  !d.st.mbufs.any (fun b => !b.released && b.master.obj == some (.exp k))

def stepOp (d : DS) (op : Array Json) : Except String (Json × DS) := do
  let name ← (← argAt op 0).getStr?
  let withH (f : Nat → Except String (Json × DS)) : Except String (Json × DS) := do
    match d.pick (← (← argAt op 1).getInt?) with
    | none => return (skipJ, d)
    | some id => f id
  let withO (j : Json) (f : Obj → Except String (Json × DS)) : Except String (Json × DS) := do
    match ← jObj d j with
    | none => return (skipJ, d)
    | some o => f o
  match name with
  | "view" => withO (← argAt op 1) fun o => return runM d (memoryviewNew o) viewRes
  | "fromflags" =>
    withO (← argAt op 1) fun o => do
      return runM d (memoryviewFromFlags o (← (← argAt op 2).getNat?)) viewRes
  | "buffer" => withH fun i => do
      return runM d (memoryBufferProc i (← (← argAt op 2).getNat?)) viewRes
  | "get" => withH fun i => do
      match ← jKey d (← argAt op 2) with
      | none => return (skipJ, d)
      | some k => return runM d (memorySubscript i k) subRes
  | "set" => withH fun i => do
      match ← jKey d (← argAt op 2) with
      | none => return (skipJ, d)
      | some k =>
        withO (← argAt op 3) fun v => return runM d (memoryAssSub i k (some v)) (plain fun _ => .null)
  | "del" => withH fun i => do
      match ← jKey d (← argAt op 2) with
      | none => return (skipJ, d)
      | some k => return runM d (memoryAssSub i k none) (plain fun _ => .null)
  | "len" => withH fun i => return runM d (memoryLength i) (plain toJson)
  | "tolist" => withH fun i => return runM d (memoryviewTolist i) (plain treeJ)
  | "tobytes" => withH fun i => do
      return runM d (memoryviewTobytes i (← jOpt (optArg op 2) jChars)) (plain bytesJ)
  | "hex" => withH fun i => do
      let sep ← match optArg op 2 with
        | .null => pure none
        | j => pure (some ((← jObj d j).getD .none))
      let bps ← match optArg op 3 with
        | .null => pure 1
        | j => j.getInt?
      return runM d (memoryviewHex i sep bps) (plain fun s => toJson (String.ofList s))
  | "cast" => withH fun i => do
      let sh ← match optArg op 3 with
        | .null => pure none
        | .arr a =>
          let l ← a.toList.mapM (jObj d)
          pure (some (.seq (l.map (·.getD .none))))
        | _ => pure (some ShapeArg.other)
      return runM d (memoryviewCast i (← jChars (← argAt op 2)) sh) viewRes
  | "toreadonly" => withH fun i => return runM d (memoryviewToreadonly i) viewRes
  | "release" => withH fun i => return runM d (memoryviewRelease i) (plain fun _ => .null)
  | "enter" => withH fun i => return runM d (memoryEnter i) (plain fun j => Json.mkObj [("same", toJson (j == i))])
  | "exit" => withH fun i => return runM d (memoryExit i) (plain fun _ => .null)
  | "cmp" => withH fun i => do
      withO (← argAt op 2) fun w => do
        let o := jCmpOp (← (← argAt op 3).getStr?)
        return runM d (memoryRichcompare i w o) (plain fun r =>
          match r with
          | none => Json.mkObj [("notimpl", toJson true)]
          | some b => Json.mkObj [("bool", toJson b)])
  | "hash" => withH fun i =>
      return runM d (memoryHash i) (plain fun b => Json.mkObj [("hash", toJson b)])
  | "count" => withH fun i => do
      withO (← argAt op 2) fun v => return runM d (memoryviewCount i v) (plain toJson)
  | "index" => withH fun i => do
      let start ← match optArg op 3 with
        | .null => pure 0
        | j => pure (RangeSlice.clampSsize (← j.getInt?))
      let stop ← match optArg op 4 with
        | .null => pure ssizeMax
        | j => pure (RangeSlice.clampSsize (← j.getInt?))
      withO (← argAt op 2) fun v => return runM d (memoryviewIndex i v start stop) (plain toJson)
  | "iter" => withH fun i => do
      let (r, st) := memoryIter i d.st
      let d := { d with st := st }
      match r with
      | .ok it => return (okJ .null, { d with iters := d.iters.push it })
      | .error e => return (errJ e, d)
  | "next" =>
      let h ← (← argAt op 1).getInt?
      if d.iters.isEmpty then return (skipJ, d)
      let it := d.iters[(h % (d.iters.size : Int)).toNat]!
      return runM d (memoryiterNext it) (plain fun r =>
        match r with
        | none => Json.mkObj [("stop", toJson true)]
        | some x => itemJ x)
  | "attr" => withH fun i => do
      let a ← jAttr (← (← argAt op 2).getStr?)
      return runM d (memoryGet i a) (fun d v => (attrJ d v, d))
  | "repr" => withH fun i => return runM d (memoryRepr i) (plain toJson)
  | "weak" => withH fun i => do
      let t := d.pick (← (← argAt op 2).getInt?)
      let st := d.st.setMv i { d.st.mv i with weakcb := t }
      return (okJ .null, { d with st := st })
  | "drop" => withH fun i => do
      if canDrop d i then
        let (_, st) := memoryDealloc i d.st
        return (okJ .null, { d with st := st, dropped := i :: d.dropped })
      else return (skipJ, d)
  | "clear" => withH fun i => do
      -- `memory_clear` and `mbuf_clear` as the collector runs them on a cycle
      if getExports d.st i == 0 then
        return runM d (memoryClear i) (plain fun _ => .null)
      else return (skipJ, d)
  | "resize" =>
      let k ← (← argAt op 1).getNat?
      if d.pinned.contains k then return (skipJ, d)
      return (okJ (Json.mkObj [("bool", toJson (canResize d k))]), d)
  | "contig" =>
      withO (← argAt op 1) fun o => do
        let w ← (← argAt op 2).getBool?
        let order := ((← (← argAt op 3).getStr?).toList.headD 'C')
        return runM d (memoryViewGetContiguous o w order) viewRes
  | "toc" => withH fun i => do
      let order := ((← (← argAt op 2).getStr?).toList.headD 'C')
      let x : M (List Nat) := do
        let b ← memoryGetbuf i bufFullRO
        let st ← M.get
        let r ← M.onError (M.lift (pyBufferToContiguous st.mem b b.len order)) (pyBufferRelease b)
        memoryReleasebuf i
        return r
      return runM d x (plain bytesJ)
  | "iscontig" => withH fun i => do
      let order := ((← (← argAt op 2).getStr?).toList.headD 'C')
      -- `is_contiguous` in Modules/_testbuffer.c replaces any `PyObject_GetBuffer` error
      return runM d (M.mapErr (fun _ =>
            .typeError "is_contiguous: object does not implement the buffer protocol") (do
          let b ← memoryGetbuf i bufFullRO
          memoryReleasebuf i
          return pyBufferIsContiguous b order))
        (plain fun b => Json.mkObj [("bool", toJson b)])
  | "restricted" =>
      -- the view `__release_buffer__` receives, Objects/typeobject.c:10833
      let e := d.exps[(← (← argAt op 1).getNat?)]!
      let (r, st1) := restrictedView e d.st
      let .ok i := r | throw "restricted"
      let okTrue {α : Type} (m : M α) : Json :=
        match (m st1).1 with
        | .ok _ => okJ (toJson true)
        | .error er => errJ er
      let lenJ : Json := match (memoryLength i st1).1 with
        | .ok n => okJ (toJson n)
        | .error er => errJ er
      return (okJ (Json.arr #[okTrue (memoryviewCast i ['B'] none), okTrue (memoryviewToreadonly i),
        okTrue (memoryviewNew (.view i)), okTrue (memorySubscript i (.one (.slice ⟨none, none, none⟩ none))),
        okTrue (memoryBufferProc i 0), lenJ]), d)
  | "fromnil" =>
      let k ← (← argAt op 1).getNat?
      return runM d (memoryViewFromBuffer d.exps[k]! false) viewRes
  | "frommem" =>
      let k ← (← argAt op 1).getNat?
      let e := d.exps[k]!
      let d := { d with pinned := k :: d.pinned }
      return runM d (memoryViewFromMemory e.buf e.len (← (← argAt op 2).getBool?)) viewRes
  | "frombuffer" =>
      let k ← (← argAt op 1).getNat?
      let e := d.exps[k]!
      let d := { d with pinned := k :: d.pinned }
      let flags ← (← argAt op 2).getNat?
      match simpleGetbuffer e flags with
      | .ok info => return runM d (memoryViewFromBuffer info false) viewRes
      | .error e => return (errJ e, d)
  | other => throw s!"unknown op {other}"

def script (j : Json) : Except String Json := do
  let mem ← jNats (← field j "mem")
  let exps ← (← (← field j "exps").getArr?).toList.mapIdxM fun i e => jBuf e i
  let unh ← (← (← field j "exps").getArr?).toList.mapM jUnhash
  let ops ← (← field j "ops").getArr?
  let hooks ← (← (← field j "exps").getArr?).toList.mapM fun e =>
    match e.getObjVal? "hashrel" with
    | .ok v => (some <$> v.getNat?)
    | .error _ => (pure none : Except String (Option Nat))
  let mut d : DS := { st := { mem := mem, unhashable := unh }, exps := exps.toArray }
  let noStruct := match j.getObjVal? "nostruct" with
    | .ok (.bool b) => b
    | _ => false
  d := { d with st := { d.st with hashHook := hooks, noStruct := noStruct } }
  let mut out : Array Json := #[]
  for op in ops do
    let (r, d') ← stepOp d (← op.getArr?)
    d := d'
    out := out.push r
  return Json.mkObj [("ok", Json.arr out)]

/-- The pure conversions, exercised over the whole bit space. -/
def single (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "mem.narrow32" => return okJ (toJson (narrow32 (← getNat j "d")))
  | "mem.widen32" => return okJ (toJson (widen32 (← getNat j "x")))
  | "mem.pack2" =>
    return encPy (fun (n : Nat) => toJson n) (pack2 (← getNat j "d"))
  | "mem.unpack2" => return okJ (toJson (unpack2 (← getNat j "x")))
  | "mem.long2d" => return encPy (fun (n : Nat) => toJson n) (longAsDouble (← getInt j "n"))
  | "mem.deqint" => return okJ (toJson (dEqInt (← getNat j "d") (← getInt j "n")))
  | "mem.fmtchar" =>
    let r := getNativeFmtchar (← getStr j "fmt").toList
    return okJ (match r with
      | none => Json.null
      | some (c, n) => Json.arr #[toJson (String.singleton c), toJson n])
  | "mem.fmtstr" =>
    let r := getNativeFmtstr (← getStr j "fmt").toList
    return okJ (match r with
      | none => Json.null
      | some s => toJson (String.ofList s))
  | _ => throw s!"unknown fn {fn}"

def handler : Handler := fun fn j =>
  if fn == "mem.script" then some (script j)
  else if fn.startsWith "mem." then some (single fn j)
  else none

end PyLean.BytesObj.Mem
