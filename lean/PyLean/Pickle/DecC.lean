import PyLean.Pickle.DecPy

/-!
The C `Unpickler` (`Modules/_pickle.c:5369-7225`) as used by `pickle.loads`
on a bytes object (`_pickle_loads_impl`, :8119-8145): the whole input is the
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

/-- `_Unpickler_LeaveFrame` (`Modules/_pickle.c:1281-1291`). -/
def cLeaveFrame (straddle : Bool) : CM Unit := do
  if straddle then cThrow (unpicklingError "pickle exhausted before end of frame")
  modify fun s => { s with inputLen := s.savedInputLen, frameEnd := none }

/-- `_Unpickler_Read` (macro at `Modules/_pickle.c:1549-1554`, `_Unpickler_ReadImpl`
at :1386-1427). -/
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

/-- `_Unpickler_ReadInto` (`Modules/_pickle.c:1436-1546`) for in-memory input. -/
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

/-- `_Unpickler_Readline` (`Modules/_pickle.c:1578-1611`). -/
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

/-- `Pdata_stack_underflow` (`Modules/_pickle.c:519-528`). -/
def cUnderflow {α : Type} : CM α := do
  if (← get).marks ≠ [] then cThrow (unpicklingError "unexpected MARK found")
  else cThrow (unpicklingError "unpickling stack underflow")

def cPush (v : DV) : CM Unit := modify fun s => { s with stack := v :: s.stack }

/-- `Pdata_pop` (`Modules/_pickle.c:533-542`). -/
def cPop : CM DV := do
  let s ← get
  if s.stack.length ≤ cFence s then cUnderflow
  else match s.stack with
    | v :: r => set { s with stack := r }; return v
    | [] => cUnderflow

/-- `marker` (`Modules/_pickle.c:5376-5388`). -/
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

/-- `Pdata_poptuple` (`Modules/_pickle.c:565-583`). -/
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

/-- `_Unpickler_MemoPut` (`Modules/_pickle.c:1646-1664`). -/
def cMemoPutD (idx : Nat) (v : DV) : CM Unit := modify fun s =>
  { s with memo := if s.memo.any (·.1 == idx) then s.memo.map (fun p => if p.1 == idx then (idx, v) else p)
                   else s.memo ++ [(idx, v)] }

/-- `calc_binint` (`Modules/_pickle.c:5484-5503`): 1 and 2 bytes unsigned,
4 bytes signed. -/
def calcBinint (b : Bytes) : Int := if b.length = 4 then leInt b else leNat b

/-- `calc_binsize` (`Modules/_pickle.c:5452-5478`): `none` above
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

/-- `do_append` (`Modules/_pickle.c:6651-6723`). -/
def cDoAppend (x : Int) : CM Unit := do
  let s ← get
  let len := s.stack.length
  if x > len ∨ x ≤ cFence s then cUnderflow
  if x = len then return
  let x := x.toNat
  let lst := s.stack.getD (len - x) .none
  let (items, rest) := splitAt s x
  set { s with stack := rest }
  let h := s.heap
  if hasExtend h lst then cSetHeap (← cLift (extendObj h lst items))
  else match lst with
    | .glob _ => cThrow (excluded "global as APPEND target")
    | _ => cThrow (attributeError s!"'{lst.typeName h}' object has no attribute 'append'")

/-- `do_setitems` (`Modules/_pickle.c:6743-6777`). -/
def cDoSetitems (x : Int) : CM Unit := do
  let s ← get
  let len := s.stack.length
  if x > len ∨ x ≤ cFence s then cUnderflow
  if x = len then return
  let x := x.toNat
  if (len - x) % 2 ≠ 0 then cThrow (unpicklingError "odd number of items for SETITEMS")
  let d := s.stack.getD (len - x) .none
  let (items, rest) := splitAt s x
  let rec go (h : Heap) : List DV → Py Heap
    | k :: v :: r => do go (← setItem h d k v) r
    | _ => .ok h
  let r := go s.heap items
  set { s with stack := rest }
  cSetHeap (← cLift r)

/-- `invalid load key` (`Modules/_pickle.c:7178-7189`). -/
def cBadKey (c : UInt8) : PyExc :=
  if 0x20 ≤ c ∧ c ≤ 0x7e ∧ c ≠ 0x27 ∧ c ≠ 0x5c then
    unpicklingError s!"invalid load key, '{Char.ofNat c.toNat}'."
  else unpicklingError s!"invalid load key, '\\x{Char.ofNat (hexDigit (c.toNat / 16)).toNat}{Char.ofNat (hexDigit (c.toNat % 16)).toNat}'."

/-- One opcode of the C `load` loop (`Modules/_pickle.c:7077-7210`); `true`
on `STOP`. -/
def cStep (op : UInt8) : CM Bool := do
  if op == oNONE then cPush .none; return false
  else if op == oBININT then cPush (.int (calcBinint (← cRead 4))); return false
  else if op == oBININT1 then cPush (.int (calcBinint (← cRead 1))); return false
  else if op == oBININT2 then cPush (.int (calcBinint (← cRead 2))); return false
  else if op == oINT then
    match ← cLift (cLoadIntLine (← cReadline)) with
    | .int v => cPush (.int v)
    | .bool b => cPush (.bool b)
    return false
  else if op == oLONG then cPush (.int (← cLift (cLoadLongLine (← cReadline)))); return false
  else if op == oLONG1 || op == oLONG4 then
    -- load_counted_long, :5580-5611
    let size := calcBinint (← cRead (if op == oLONG1 then 1 else 4))
    if size < 0 then cThrow (unpicklingError "LONG pickle has negative byte count")
    if size = 0 then cPush (.int 0)
    else cPush (.int (decodeLong (← cRead size.toNat)))
    return false
  else if op == oSHORT_BINBYTES || op == oBINBYTES || op == oBINBYTES8 then
    -- load_counted_binbytes, :5747-5774
    let nb := if op == oSHORT_BINBYTES then 1 else if op == oBINBYTES then 4 else 8
    match calcBinsize (← cRead nb) with
    | none => cThrow (.overflowError s!"BINBYTES exceeds system's maximum size of {ssizeMaxN} bytes")
    | some size => cPush (.bytes (← cReadInto size))
    return false
  else if op == oBYTEARRAY8 then
    match calcBinsize (← cRead 8) with
    | none => cThrow (.overflowError s!"BYTEARRAY8 exceeds system's maximum size of {ssizeMaxN} bytes")
    | some size => cPush (← cAlloc (.bytearray (← cReadInto size)))
    return false
  else if op == oSHORT_BINSTRING || op == oBINSTRING then
    -- load_counted_binstring, :5711-5744
    let size := calcBinint (← cRead (if op == oSHORT_BINSTRING then 1 else 4))
    if size < 0 then cThrow (unpicklingError "BINSTRING pickle has negative byte count")
    cPush (← cLift (decodeString (← cRead size.toNat)))
    return false
  else if op == oSTRING then
    -- load_string, :5664-5708
    let s := (← cReadline).dropLast
    if s.length ≥ 2 ∧ s.head? = s.getLast? ∧ (s.head? = some 0x27 ∨ s.head? = some 0x22) then
      cPush (← cLift (decodeString (← cLift (escapeDecode 0 ((s.drop 1).dropLast)))))
    else cThrow (unpicklingError "the STRING opcode argument must be quoted")
    return false
  else if op == oUNICODE then
    cPush (.str (← cLift (decodeRUE (← cReadline).dropLast))); return false
  else if op == oSHORT_BINUNICODE || op == oBINUNICODE || op == oBINUNICODE8 then
    -- load_counted_binunicode, :5878-5904
    let nb := if op == oSHORT_BINUNICODE then 1 else if op == oBINUNICODE then 4 else 8
    match calcBinsize (← cRead nb) with
    | none => cThrow (.overflowError s!"BINUNICODE exceeds system's maximum size of {ssizeMaxN} bytes")
    | some size => cPush (.str (← cLift (decodeUtf8SP (← cRead size))))
    return false
  else if op == oEMPTY_TUPLE || op == oTUPLE1 || op == oTUPLE2 || op == oTUPLE3 then
    -- load_counted_tuple, :5907-5919
    let len := if op == oEMPTY_TUPLE then 0 else if op == oTUPLE1 then 1 else if op == oTUPLE2 then 2 else 3
    let s ← get
    if s.stack.length < len then cUnderflow
    cPush (.tuple (← cPopTuple (s.stack.length - len)))
    return false
  else if op == oTUPLE then
    let i ← cMarker
    let s ← get
    if s.stack.length < s.stack.length - i then cUnderflow
    cPush (.tuple (← cPopTuple i))
    return false
  else if op == oEMPTY_LIST then cPush (← cAlloc (.list [])); return false
  else if op == oLIST then
    let i ← cMarker
    let (items, rest) := splitAt (← get) i
    modify fun s => { s with stack := rest }
    cPush (← cAlloc (.list items)); return false
  else if op == oEMPTY_DICT then cPush (← cAlloc (.dict [])); return false
  else if op == oDICT then
    -- load_dict, :5982-6011
    let i ← cMarker
    let s ← get
    let j := s.stack.length
    if (j - i) % 2 ≠ 0 then cThrow (unpicklingError "odd number of items for DICT")
    let (items, rest) := splitAt s i
    let rec build (acc : List (DV × DV)) : List DV → Py (List (DV × DV))
      | k :: v :: r => do build (← dictSet s.heap acc k v) r
      | _ => .ok acc
    let kvs ← cLift (build [] items)
    modify fun s => { s with stack := rest }
    cPush (← cAlloc (.dict kvs)); return false
  else if op == oEMPTY_SET then cPush (← cAlloc (.set [])); return false
  else if op == oADDITEMS then
    -- load_additems, :6795-6848
    let mark ← cMarker
    let s ← get
    let len := s.stack.length
    if mark > len ∨ mark ≤ cFence s then cUnderflow
    if mark = len then return false
    let so := s.stack.getD (len - mark) .none
    if isSetRef s.heap so then
      let items ← cPopTuple mark
      cSetHeap (← cLift (setUpdate (← get).heap so items))
    else
      modify fun s => { s with stack := s.stack.drop (len - mark) }
      cThrow (noAdd s.heap so)
    return false
  else if op == oFROZENSET then
    let i ← cMarker
    let items ← cPopTuple i
    cPush (← cLift (mkFrozenset (← get).heap items)); return false
  else if op == oAPPEND then
    let s ← get
    if (s.stack.length : Int) - 1 ≤ cFence s then cUnderflow
    cDoAppend (s.stack.length - 1); return false
  else if op == oAPPENDS then cDoAppend (← cMarker); return false
  else if op == oDUP then
    let s ← get
    if s.stack.length ≤ cFence s then cUnderflow
    cPush (s.stack.headD .none); return false
  else if op == oBINGET then
    let i := leNat (← cRead 1)
    cMemoGetD i i; return false
  else if op == oLONG_BINGET then
    let i := leNat (← cRead 4)
    cMemoGetD i i; return false
  else if op == oGET then
    -- load_get, :6388-6421
    let line ← cReadline
    if line.length < 2 then cThrow truncated
    let key ← cLift (cLongFromLine line)
    let idx ← cLift (asSsize key)
    if idx < 0 then cThrow (unpicklingError s!"Memo value not found at index {idx}")
    cMemoGetD idx.toNat idx; return false
  else if op == oMARK then
    modify fun s => { s with marks := s.stack.length :: s.marks }; return false
  else if op == oBINPUT then
    let b ← cRead 1
    let v ← cTopChecked
    cMemoPutD (leNat b) v; return false
  else if op == oLONG_BINPUT then
    let b ← cRead 4
    let v ← cTopChecked
    cMemoPutD (leNat b) v; return false
  else if op == oPUT then
    -- load_put, :6565-6593
    let line ← cReadline
    if line.length < 2 then cThrow truncated
    let v ← cTopChecked
    let key ← cLift (cLongFromLine line)
    let idx ← cLift (asSsize key)
    if idx < 0 then cThrow (.valueError "negative PUT argument")
    cMemoPutD idx.toNat v; return false
  else if op == oMEMOIZE then
    let v ← cTopChecked
    cMemoPutD (← get).memo.length v; return false
  else if op == oPOP then
    -- load_pop, :6336-6360
    let s ← get
    let len := s.stack.length
    match s.marks with
    | m :: r =>
      if m = len then set { s with marks := r }; return false
      else pure ()
    | [] => pure ()
    if len ≤ cFence s then cUnderflow
    modify fun s => { s with stack := s.stack.drop 1 }; return false
  else if op == oPOP_MARK then
    let i ← cMarker
    let s ← get
    set { s with stack := s.stack.drop (s.stack.length - i) }; return false
  else if op == oSETITEM then cDoSetitems (((← get).stack.length : Int) - 2); return false
  else if op == oSETITEMS then cDoSetitems (← cMarker); return false
  else if op == oPROTO then
    let i := leNat (← cRead 1)
    if i ≤ 5 then modify fun s => { s with proto := i } else cThrow (.valueError s!"unsupported pickle protocol: {i}")
    return false
  else if op == oFRAME then
    -- load_frame, :7035-7074
    let b ← cRead 8
    let s ← get
    match s.frameEnd with
    | some fe =>
      if s.idx < fe then cThrow (unpicklingError "beginning of a new frame before end of current frame")
      set { s with inputLen := s.savedInputLen, frameEnd := none }
    | none => pure ()
    match calcBinsize b with
    | none => cThrow (.overflowError s!"FRAME length exceeds system's maximum of {ssizeMaxN} bytes")
    | some frameLen =>
      discard (cRead frameLen)
      modify fun s =>
        let start := s.idx - frameLen
        { s with idx := start, frameEnd := some (start + frameLen), savedInputLen := s.inputLen,
                 inputLen := start + frameLen }
    return false
  else if op == oNEWTRUE then cPush (.bool true); return false
  else if op == oNEWFALSE then cPush (.bool false); return false
  else if op == oGLOBAL then
    -- load_global, :6218-6251
    let m := (← cReadline).dropLast
    let n := (← cReadline).dropLast
    let m ← cLift (match utf8Dec false m with | some s => .ok s | none => .error unicodeDecodeError)
    let n ← cLift (match utf8Dec false n with | some s => .ok s | none => .error unicodeDecodeError)
    cPush (.glob (← cLift (findGlob (← get).proto m n))); return false
  else if op == oSTACK_GLOBAL then
    -- load_stack_global, :6254-6284
    let name ← cPop
    let module ← cPop
    match module, name with
    | .str m, .str n => cPush (.glob (← cLift (findGlob (← get).proto m n)))
    | _, _ => cThrow (unpicklingError "STACK_GLOBAL requires str")
    return false
  else if op == oREDUCE then
    -- load_reduce, :6989-7013
    let args ← cPop
    let func ← cPop
    match func, args with
    | .glob g, .tuple xs =>
      let (h', v) ← cLift (callGlob (← get).heap g xs)
      cSetHeap h'
      cPush v
    | _, _ => cThrow (excluded "REDUCE")
    return false
  else if op == oSTOP then return true
  else if op == oFLOAT || op == oBINFLOAT || op == oPERSID || op == oBINPERSID || op == oINST
      || op == oOBJ || op == oNEWOBJ || op == oNEWOBJ_EX || op == oBUILD || op == oEXT1
      || op == oEXT2 || op == oEXT4 || op == oNEXT_BUFFER || op == oREADONLY_BUFFER then
    cThrow (excluded "opcode")
  else cThrow (cBadKey op)

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
