import PyLean.Pickle.DecPy

/-!
The C `Unpickler` (`Modules/_pickle.c:5492-7355`) as used by `pickle.loads`
on a bytes object (`_pickle_loads_impl`, :8249-8275): the whole input is the
buffer and there is no file `read`, so running out of data is
`pickle data was truncated`. Same restrictions as `DecPy`.

The C stack is one flat array with a separate mark stack (`marks`); `fence`
is the position of the topmost mark. The memo is an array indexed by memo
index; it is modelled as a finite map (array growth and `MemoryError` are not
modelled).
-/

namespace PyLean.Pickle

open PyLean

structure CSt where
  inp : Bytes
  /-- `next_read_idx`. -/
  idx : Nat := 0
  /-- `input_len`, capped at `frame_end` inside a frame. -/
  inputLen : Nat
  /-- `frame_end`, `none` for -1. -/
  frameEnd : Option Nat := none
  savedInputLen : Nat := 0
  /-- `self->stack`, top first. -/
  stack : List DV := []
  /-- `self->marks`, top first: stack sizes. -/
  marks : List Nat := []
  memo : List (Nat × DV) := []
  heap : Heap := []
  proto : Nat := 0

abbrev CM := StateT CSt (Except PyExc)

def cThrow {α : Type} (e : PyExc) : CM α := throw e
def cLift {α : Type} : Py α → CM α
  | .ok a => pure a
  | .error e => throw e

def truncated : PyExc := unpicklingError "pickle data was truncated"

/-- `_Unpickler_LeaveFrame` (`Modules/_pickle.c:1280-1290`). -/
def cLeaveFrame (straddle : Bool) : CM Unit := do
  if straddle then cThrow (unpicklingError "pickle exhausted before end of frame")
  modify fun s => { s with inputLen := s.savedInputLen, frameEnd := none }

/-- `_Unpickler_Read` (macro at `Modules/_pickle.c:1577-1582`, `_Unpickler_ReadImpl`
at :1464-1505). -/
def cRead (n : Nat) : CM Bytes := do
  let s ← get
  if s.idx + n ≤ s.inputLen then
    set { s with idx := s.idx + n }
    return (s.inp.drop s.idx).take n
  else
    if s.idx > ssizeMaxN - n then cThrow (unpicklingError "read would overflow (invalid bytecode)")
    match s.frameEnd with
    | some fe =>
      cLeaveFrame (decide (s.idx < fe))
      let s ← get
      if n ≤ s.inputLen - s.idx then
        set { s with idx := s.idx + n }
        return (s.inp.drop s.idx).take n
      else cThrow truncated
    | none => cThrow truncated

/-- `_Unpickler_ReadInto` (`Modules/_pickle.c:1514-1574`) for in-memory input. -/
def cReadInto (n : Nat) : CM Bytes := do
  let s ← get
  let inBuffer := s.inputLen - s.idx
  let first := if inBuffer > 0 then (s.inp.drop s.idx).take (min inBuffer n) else []
  set { s with idx := s.idx + first.length }
  if inBuffer > 0 ∧ first.length = n then return first
  let rest := n - first.length
  match s.frameEnd with
  | some _ =>
    cLeaveFrame (decide (inBuffer > 0))
    let s ← get
    let inBuffer2 := s.inputLen - s.idx
    if inBuffer2 > 0 then
      let more := (s.inp.drop s.idx).take (min inBuffer2 rest)
      set { s with idx := s.idx + more.length }
      if more.length = rest then return first ++ more
    cThrow truncated
  | none => cThrow truncated

/-- `_Unpickler_Readline` (`Modules/_pickle.c:1606-1639`). -/
def cReadline : CM Bytes := do
  let s ← get
  let window := (s.inp.drop s.idx).take (s.inputLen - s.idx)
  match window.findIdx? (· == nl) with
  | some i =>
    set { s with idx := s.idx + i + 1 }
    return window.take (i + 1)
  | none =>
    match s.frameEnd with
    | some fe =>
      cLeaveFrame (decide (s.idx < fe))
      let s ← get
      let window := (s.inp.drop s.idx).take (s.inputLen - s.idx)
      match window.findIdx? (· == nl) with
      | some i =>
        set { s with idx := s.idx + i + 1 }
        return window.take (i + 1)
      | none => cThrow truncated
    | none => cThrow truncated

def cFence (s : CSt) : Nat := s.marks.headD 0

/-- `Pdata_stack_underflow` (`Modules/_pickle.c:517-526`). -/
def cUnderflow {α : Type} : CM α := do
  if (← get).marks ≠ [] then cThrow (unpicklingError "unexpected MARK found")
  else cThrow (unpicklingError "unpickling stack underflow")

def cPush (v : DV) : CM Unit := modify fun s => { s with stack := v :: s.stack }

/-- `Pdata_pop` (`Modules/_pickle.c:531-540`). -/
def cPop : CM DV := do
  let s ← get
  if s.stack.length ≤ cFence s then cUnderflow
  else match s.stack with
    | v :: r => set { s with stack := r }; return v
    | [] => cUnderflow

/-- `marker` (`Modules/_pickle.c:5499-5511`). -/
def cMarker : CM Nat := do
  let s ← get
  match s.marks with
  | m :: r => set { s with marks := r }; return m
  | [] => cThrow (unpicklingError "could not find MARK")

/-- The stack items from position `start` up, in push order, and the stack
with them removed (`Pdata_poptuple` / `Pdata_poplist` without the fence check). -/
def splitAt (s : CSt) (start : Nat) : List DV × List DV :=
  let k := s.stack.length - start
  ((s.stack.take k).reverse, s.stack.drop k)

/-- `Pdata_poptuple` (`Modules/_pickle.c:563-581`). -/
def cPopTuple (start : Nat) : CM (List DV) := do
  let s ← get
  if start < cFence s then cUnderflow
  let (items, rest) := splitAt s start
  set { s with stack := rest }
  return items

def cAlloc (o : HObj) : CM DV := do
  let s ← get
  let (h, v) := s.heap.alloc o
  set { s with heap := h }
  return v

def cSetHeap (h : Heap) : CM Unit := modify fun s => { s with heap := h }

def cMemoGetD (idx : Nat) (shown : Int) : CM Unit := do
  match (← get).memo.lookup idx with
  | some v => cPush v
  | none => cThrow (unpicklingError s!"Memo value not found at index {shown}")

/-- `_Unpickler_MemoPut` (`Modules/_pickle.c:1697-1736`). -/
def cMemoPutD (idx : Nat) (v : DV) : CM Unit := modify fun s =>
  { s with memo := if s.memo.any (·.1 == idx) then s.memo.map (fun p => if p.1 == idx then (idx, v) else p)
                   else s.memo ++ [(idx, v)] }

/-- `calc_binint` (`Modules/_pickle.c:5607-5626`): 1 and 2 bytes unsigned,
4 bytes signed. -/
def calcBinint (b : Bytes) : Int := if b.length = 4 then leInt b else leNat b

/-- `calc_binsize` (`Modules/_pickle.c:5575-5601`): `none` above
`PY_SSIZE_T_MAX`. -/
def calcBinsize (b : Bytes) : Option Nat :=
  let x := leNat b
  if x > ssizeMaxN then none else some x

/-- The top of stack for `PUT`-like opcodes, with the fence check. -/
def cTopChecked : CM DV := do
  let s ← get
  if s.stack.length ≤ cFence s then cUnderflow
  else match s.stack with
    | v :: _ => return v
    | [] => cUnderflow

/-- `PyLong_AsSsize_t` of a parsed memo key. -/
def asSsize (v : Int) : Py Int :=
  if v < ssizeMin ∨ v > ssizeMax then .error (.overflowError "Python int too large to convert to C ssize_t")
  else .ok v

/-- `do_append` (`Modules/_pickle.c:6787-6857`). -/
def cDoAppend (x : Int) : CM Unit := do
  let s ← get
  let len := s.stack.length
  if x > len ∨ x ≤ cFence s then cUnderflow
  else if x = len then pure ()
  else
    let x := x.toNat
    let lst := s.stack.getD (len - x) .none
    let (items, rest) := splitAt s x
    set { s with stack := rest }
    let h := s.heap
    if hasExtend h lst then cSetHeap (← cLift (extendObj h lst items))
    else
      match lst with
      | .glob _ => cThrow (excluded "global as APPEND target")
      | _ => cThrow (attributeError s!"'{lst.typeName h}' object has no attribute 'append'")

/-- The loop of `do_setitems`, :6897-6903. -/
def cSetitemsGo (d : DV) (h : Heap) : List DV → Py Heap
  | k :: v :: r => do cSetitemsGo d (← setItem h d k v) r
  | _ => .ok h

/-- `do_setitems` (`Modules/_pickle.c:6877-6909`). -/
def cDoSetitems (x : Int) : CM Unit := do
  let s ← get
  let len := s.stack.length
  if x > len ∨ x ≤ cFence s then cUnderflow
  else if x = len then pure ()
  else
    let x := x.toNat
    if (len - x) % 2 ≠ 0 then cThrow (unpicklingError "odd number of items for SETITEMS")
    else
      let d := s.stack.getD (len - x) .none
      let (items, rest) := splitAt s x
      let r := cSetitemsGo d s.heap items
      set { s with stack := rest }
      cSetHeap (← cLift r)

/-- `invalid load key` (`Modules/_pickle.c:7308-7319`). -/
def cBadKey (c : UInt8) : PyExc :=
  if 0x20 ≤ c ∧ c ≤ 0x7e ∧ c ≠ 0x27 ∧ c ≠ 0x5c then
    unpicklingError s!"invalid load key, '{Char.ofNat c.toNat}'."
  else unpicklingError s!"invalid load key, '\\x{Char.ofNat (hexDigit (c.toNat / 16)).toNat}{Char.ofNat (hexDigit (c.toNat % 16)).toNat}'."

/-! ## Opcode handlers (`Modules/_pickle.c:5514-7204`) -/

def cLoadNone : CM Unit := cPush .none
def cLoadBinint : CM Unit := do cPush (.int (calcBinint (← cRead 4)))
def cLoadBinint1 : CM Unit := do cPush (.int (calcBinint (← cRead 1)))
def cLoadBinint2 : CM Unit := do cPush (.int (calcBinint (← cRead 2)))

/-- `load_int`, :5521-5562. -/
def cLoadInt : CM Unit := do
  match ← cLift (cLoadIntLine (← cReadline)) with
  | .int v => cPush (.int v)
  | .bool b => cPush (.bool b)

def cLoadLong : CM Unit := do cPush (.int (← cLift (cLoadLongLine (← cReadline))))

/-- `load_counted_long`, :5703-5734. -/
def cLoadCountedLong (nb : Nat) : CM Unit := do
  let size := calcBinint (← cRead nb)
  if size < 0 then cThrow (unpicklingError "LONG pickle has negative byte count")
  else if size = 0 then cPush (.int 0)
  else cPush (.int (decodeLong (← cRead size.toNat)))

/-- `load_counted_binbytes`, :5870-5912. -/
def cLoadCountedBinbytes (nb : Nat) : CM Unit := do
  match calcBinsize (← cRead nb) with
  | none => cThrow (.overflowError s!"BINBYTES exceeds system's maximum size of {ssizeMaxN} bytes")
  | some size => cPush (.bytes (← cReadInto size))

/-- `load_counted_bytearray`, :5915-5958. -/
def cLoadCountedBytearray : CM Unit := do
  match calcBinsize (← cRead 8) with
  | none => cThrow (.overflowError s!"BYTEARRAY8 exceeds system's maximum size of {ssizeMaxN} bytes")
  | some size => cPush (← cAlloc (.bytearray (← cReadInto size)))

/-- `load_counted_binstring`, :5834-5867. -/
def cLoadCountedBinstring (nb : Nat) : CM Unit := do
  let size := calcBinint (← cRead nb)
  if size < 0 then cThrow (unpicklingError "BINSTRING pickle has negative byte count")
  else cPush (← cLift (decodeString (← cRead size.toNat)))

/-- `load_string`, :5787-5831. -/
def cLoadString : CM Unit := do
  let s := (← cReadline).dropLast
  if quotedString s then
    cPush (← cLift (decodeString (← cLift (escapeDecode 0 ((s.drop 1).dropLast)))))
  else cThrow (unpicklingError "the STRING opcode argument must be quoted")

def cLoadUnicode : CM Unit := do cPush (.str (← cLift (decodeRUE (← cReadline).dropLast)))

/-- `load_counted_binunicode`, :6029-6055. -/
def cLoadCountedBinunicode (nb : Nat) : CM Unit := do
  match calcBinsize (← cRead nb) with
  | none => cThrow (.overflowError s!"BINUNICODE exceeds system's maximum size of {ssizeMaxN} bytes")
  | some size => cPush (.str (← cLift (decodeUtf8SP (← cRead size))))

/-- `load_counted_tuple`, :6058-6070. -/
def cLoadCountedTuple (len : Nat) : CM Unit := do
  let s ← get
  if s.stack.length < len then cUnderflow
  else cPush (.tuple (← cPopTuple (s.stack.length - len)))

/-- `load_tuple`, :6073-6081. -/
def cLoadTuple : CM Unit := do
  let i ← cMarker
  cPush (.tuple (← cPopTuple i))

def cLoadEmptyList : CM Unit := do cPush (← cAlloc (.list []))
def cLoadEmptyDict : CM Unit := do cPush (← cAlloc (.dict []))
def cLoadEmptySet : CM Unit := do cPush (← cAlloc (.set []))

/-- `load_list`, :6117-6130. -/
def cLoadList : CM Unit := do
  let i ← cMarker
  let (items, rest) := splitAt (← get) i
  modify fun s => { s with stack := rest }
  cPush (← cAlloc (.list items))

/-- The pairs of `load_dict`, :6150-6157. -/
def cDictBuild (h : Heap) (acc : List (DV × DV)) : List DV → Py (List (DV × DV))
  | k :: v :: r => do cDictBuild h (← dictSet h acc k v) r
  | _ => .ok acc

/-- `load_dict`, :6133-6162. -/
def cLoadDict : CM Unit := do
  let i ← cMarker
  let s ← get
  let j := s.stack.length
  if (j - i) % 2 ≠ 0 then cThrow (unpicklingError "odd number of items for DICT")
  else
    let (items, rest) := splitAt s i
    let kvs ← cLift (cDictBuild s.heap [] items)
    modify fun s => { s with stack := rest }
    cPush (← cAlloc (.dict kvs))

/-- `load_additems`, :6927-6978. -/
def cLoadAdditems : CM Unit := do
  let mark ← cMarker
  let s ← get
  let len := s.stack.length
  if mark > len ∨ mark ≤ cFence s then cUnderflow
  else if mark = len then pure ()
  else
    let so := s.stack.getD (len - mark) .none
    if isSetRef s.heap so then
      let items ← cPopTuple mark
      cSetHeap (← cLift (setUpdate (← get).heap so items))
    else
      modify fun s => { s with stack := s.stack.drop (len - mark) }
      cThrow (noAdd s.heap so)

/-- `load_frozenset`, :6165-6185. -/
def cLoadFrozenset : CM Unit := do
  let i ← cMarker
  let items ← cPopTuple i
  cPush (← cLift (mkFrozenset (← get).heap items))

/-- `load_append`, :6860-6865. -/
def cLoadAppend : CM Unit := do
  let s ← get
  if (s.stack.length : Int) - 1 ≤ cFence s then cUnderflow
  else cDoAppend (s.stack.length - 1)

def cLoadAppends : CM Unit := do cDoAppend (← cMarker)

/-- `load_dup`, :6526-6536. -/
def cLoadDup : CM Unit := do
  let s ← get
  if s.stack.length ≤ cFence s then cUnderflow
  else cPush (s.stack.headD .none)

def cLoadBinget : CM Unit := do
  let i := leNat (← cRead 1)
  cMemoGetD i i

def cLoadLongBinget : CM Unit := do
  let i := leNat (← cRead 4)
  cMemoGetD i i

/-- `load_get`, :6539-6567. -/
def cLoadGet : CM Unit := do
  let line ← cReadline
  if line.length < 2 then cThrow truncated
  else
    let key ← cLift (cLongFromLine line)
    let idx ← cLift (asSsize key)
    if idx < 0 then cThrow (unpicklingError s!"Memo value not found at index {idx}")
    else cMemoGetD idx.toNat idx

def cLoadMark : CM Unit := modify fun s => { s with marks := s.stack.length :: s.marks }

def cLoadBinput : CM Unit := do
  let b ← cRead 1
  let v ← cTopChecked
  cMemoPutD (leNat b) v

def cLoadLongBinput : CM Unit := do
  let b ← cRead 4
  let v ← cTopChecked
  cMemoPutD (leNat b) v

/-- `load_put`, :6701-6729. -/
def cLoadPut : CM Unit := do
  let line ← cReadline
  if line.length < 2 then cThrow truncated
  else
    let v ← cTopChecked
    let key ← cLift (cLongFromLine line)
    let idx ← cLift (asSsize key)
    if idx < 0 then cThrow (.valueError "negative PUT argument")
    else cMemoPutD idx.toNat v

def cLoadMemoize : CM Unit := do
  let v ← cTopChecked
  cMemoPutD (← get).memo.length v

/-- `load_pop`, :6487-6511. -/
def cLoadPop : CM Unit := do
  let s ← get
  let len := s.stack.length
  match s.marks with
  | m :: r =>
    if m = len then set { s with marks := r }
    else if len ≤ cFence s then cUnderflow
    else modify fun s => { s with stack := s.stack.drop 1 }
  | [] =>
    if len ≤ cFence s then cUnderflow
    else modify fun s => { s with stack := s.stack.drop 1 }

/-- `load_pop_mark`, :6514-6523. -/
def cLoadPopMark : CM Unit := do
  let i ← cMarker
  modify fun s => { s with stack := s.stack.drop (s.stack.length - i) }

def cLoadSetitem : CM Unit := do cDoSetitems (((← get).stack.length : Int) - 2)
def cLoadSetitems : CM Unit := do cDoSetitems (← cMarker)

/-- `load_proto`, :7146-7162. -/
def cLoadProto : CM Unit := do
  let i := leNat (← cRead 1)
  if i ≤ 5 then modify fun s => { s with proto := i }
  else cThrow (.valueError s!"unsupported pickle protocol: {i}")

/-- The tail of `load_frame` after the size check: read the frame through and
rewind, capping `input_len`. -/
def cOpenFrame (b : Bytes) : CM Unit := do
  match calcBinsize b with
  | none => cThrow (.overflowError s!"FRAME length exceeds system's maximum of {ssizeMaxN} bytes")
  | some frameLen =>
    discard (cRead frameLen)
    modify fun s =>
      let start := s.idx - frameLen
      { s with idx := start, frameEnd := some (start + frameLen), savedInputLen := s.inputLen,
               inputLen := start + frameLen }

/-- `load_frame`, :7165-7204. -/
def cLoadFrame : CM Unit := do
  let b ← cRead 8
  let s ← get
  match s.frameEnd with
  | some fe =>
    if s.idx < fe then cThrow (unpicklingError "beginning of a new frame before end of current frame")
    else
      set { s with inputLen := s.savedInputLen, frameEnd := none }
      cOpenFrame b
  | none => cOpenFrame b

def cLoadTrue : CM Unit := cPush (.bool true)
def cLoadFalse : CM Unit := cPush (.bool false)

/-- `load_global`, :6369-6402. -/
def cLoadGlobal : CM Unit := do
  let m := (← cReadline).dropLast
  let n := (← cReadline).dropLast
  let m ← cLift (utf8Name m)
  let n ← cLift (utf8Name n)
  cPush (.glob (← cLift (findGlob (← get).proto m n)))

/-- `load_stack_global`, :6405-6435. -/
def cLoadStackGlobal : CM Unit := do
  let name ← cPop
  let module ← cPop
  match module, name with
  | .str m, .str n => cPush (.glob (← cLift (findGlob (← get).proto m n)))
  | _, _ => cThrow (unpicklingError "STACK_GLOBAL requires str")

/-- `load_reduce`, :7119-7143. -/
def cLoadReduce : CM Unit := do
  let args ← cPop
  let func ← cPop
  match func, args with
  | .glob g, .tuple xs =>
    let (h', v) ← cLift (callGlob (← get).heap g xs)
    cSetHeap h'
    cPush v
  | _, _ => cThrow (excluded "REDUCE")

/-- The `switch` of `load`, in the order of `pyTable`. -/
def cTable : List (UInt8 × CM Unit) := [
  (oPROTO, cLoadProto), (oFRAME, cLoadFrame), (oNONE, cLoadNone), (oNEWFALSE, cLoadFalse),
  (oNEWTRUE, cLoadTrue), (oINT, cLoadInt), (oBININT, cLoadBinint), (oBININT1, cLoadBinint1),
  (oBININT2, cLoadBinint2), (oLONG, cLoadLong), (oLONG1, cLoadCountedLong 1), (oLONG4, cLoadCountedLong 4),
  (oSTRING, cLoadString), (oBINSTRING, cLoadCountedBinstring 4), (oSHORT_BINSTRING, cLoadCountedBinstring 1),
  (oBINBYTES, cLoadCountedBinbytes 4), (oSHORT_BINBYTES, cLoadCountedBinbytes 1), (oBINBYTES8, cLoadCountedBinbytes 8),
  (oBYTEARRAY8, cLoadCountedBytearray), (oUNICODE, cLoadUnicode), (oBINUNICODE, cLoadCountedBinunicode 4),
  (oSHORT_BINUNICODE, cLoadCountedBinunicode 1), (oBINUNICODE8, cLoadCountedBinunicode 8), (oTUPLE, cLoadTuple),
  (oEMPTY_TUPLE, cLoadCountedTuple 0), (oTUPLE1, cLoadCountedTuple 1), (oTUPLE2, cLoadCountedTuple 2),
  (oTUPLE3, cLoadCountedTuple 3), (oEMPTY_LIST, cLoadEmptyList), (oEMPTY_DICT, cLoadEmptyDict),
  (oEMPTY_SET, cLoadEmptySet), (oFROZENSET, cLoadFrozenset), (oLIST, cLoadList), (oDICT, cLoadDict),
  (oAPPEND, cLoadAppend), (oAPPENDS, cLoadAppends), (oSETITEM, cLoadSetitem), (oSETITEMS, cLoadSetitems),
  (oADDITEMS, cLoadAdditems), (oPOP, cLoadPop), (oPOP_MARK, cLoadPopMark), (oDUP, cLoadDup),
  (oGET, cLoadGet), (oBINGET, cLoadBinget), (oLONG_BINGET, cLoadLongBinget), (oPUT, cLoadPut),
  (oBINPUT, cLoadBinput), (oLONG_BINPUT, cLoadLongBinput), (oMEMOIZE, cLoadMemoize), (oMARK, cLoadMark),
  (oGLOBAL, cLoadGlobal), (oSTACK_GLOBAL, cLoadStackGlobal), (oREDUCE, cLoadReduce)]

/-- One opcode of the C `load` loop (`Modules/_pickle.c:7207-7340`); `true`
on `STOP`. -/
def cStep (op : UInt8) : CM Bool :=
  if op == oSTOP then pure true
  else match cTable.lookup op with
    | some h => do h; return false
    | none =>
      if excludedOps.contains op then cThrow (excluded "opcode") else cThrow (cBadKey op)

def cLoop : Nat → CM DV
  | 0 => cThrow .modelFuel
  | fuel + 1 => do
    let s ← get
    let r := (cRead 1).run s
    match r with
    | .error (.named "UnpicklingError" _) => cThrow (eofError "Ran out of input")
    | .error e => cThrow e
    | .ok (b, s') =>
      set s'
      if ← cStep (b.headD 0) then cPop
      else cLoop fuel

/-- `pickle.loads(data)`: the result and the final heap. -/
def cLoads (data : Bytes) : Py (DV × Heap) := do
  let (v, s) ← (cLoop (data.length + 1)).run { inp := data, inputLen := data.length }
  return (v, s.heap)

end PyLean.Pickle
