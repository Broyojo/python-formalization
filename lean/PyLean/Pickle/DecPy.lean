import PyLean.Pickle.Obj

/-!
`_Unpickler` (`Lib/pickle.py:1244-1858`) reading from `io.BytesIO(data)`
(`_loads`, `:1878-1884`), with `encoding='ASCII'`, `errors='strict'`, no
`buffers`, and `find_class` restricted to the five globals the picklers emit
(`Obj.findGlob`). Opcodes that run code or are out of scope (persistent ids,
floats, `INST`/`OBJ`/`NEWOBJ*`, `BUILD`, `EXT*`, out-of-band buffers) raise the
model-only `Excluded` exception; the differential test never generates them.
-/

namespace PyLean.Pickle

open PyLean

/-- `bytes.decode` escape processing of `codecs.escape_decode`
(`_PyBytes_DecodeEscape2`, `Objects/bytesobject.c:1081-1191`), strict. `pos`
is the offset of the current byte in the original data. -/
def escapeDecode (pos : Nat) : Bytes → Py Bytes
  | [] => .ok []
  | c :: r =>
    if c != 0x5c then (c :: ·) <$> escapeDecode (pos + 1) r
    else match r with
      | [] => .error (.valueError "Trailing \\ in string")
      | d :: r' =>
        if d == 0x0a then escapeDecode (pos + 2) r'
        else if d == 0x5c then (0x5c :: ·) <$> escapeDecode (pos + 2) r'
        else if d == 0x27 then (0x27 :: ·) <$> escapeDecode (pos + 2) r'
        else if d == 0x22 then (0x22 :: ·) <$> escapeDecode (pos + 2) r'
        else if d == 0x62 then (0x08 :: ·) <$> escapeDecode (pos + 2) r'
        else if d == 0x66 then (0x0c :: ·) <$> escapeDecode (pos + 2) r'
        else if d == 0x74 then (0x09 :: ·) <$> escapeDecode (pos + 2) r'
        else if d == 0x6e then (0x0a :: ·) <$> escapeDecode (pos + 2) r'
        else if d == 0x72 then (0x0d :: ·) <$> escapeDecode (pos + 2) r'
        else if d == 0x76 then (0x0b :: ·) <$> escapeDecode (pos + 2) r'
        else if d == 0x61 then (0x07 :: ·) <$> escapeDecode (pos + 2) r'
        else if 0x30 ≤ d && d ≤ 0x37 then
          match r' with
          | e :: r2 =>
            if 0x30 ≤ e && e ≤ 0x37 then
              match r2 with
              | f :: r3 =>
                if 0x30 ≤ f && f ≤ 0x37 then
                  ((((d.toNat - 48) * 64 + (e.toNat - 48) * 8 + (f.toNat - 48)) % 256).toUInt8 :: ·) <$>
                    escapeDecode (pos + 4) r3
                else (((d.toNat - 48) * 8 + (e.toNat - 48)).toUInt8 :: ·) <$> escapeDecode (pos + 3) (f :: r3)
              | [] => pure [((d.toNat - 48) * 8 + (e.toNat - 48)).toUInt8]
            else ((d.toNat - 48).toUInt8 :: ·) <$> escapeDecode (pos + 2) (e :: r2)
          | [] => pure [(d.toNat - 48).toUInt8]
        else if d == 0x78 then
          match r' with
          | e :: f :: r2 => match hexVal e, hexVal f with
            | some a, some b => ((a * 16 + b).toUInt8 :: ·) <$> escapeDecode (pos + 4) r2
            | _, _ => .error (.valueError s!"invalid \\x escape at position {pos}")
          | _ => .error (.valueError s!"invalid \\x escape at position {pos}")
        else (0x5c :: ·) <$> escapeDecode (pos + 1) (d :: r')
termination_by b => b.length

/-- The STRING-family decoding with the default `encoding='ASCII'`. -/
def decodeString (b : Bytes) : Py DV := .str <$> decodeAscii b

/-! ## State -/

structure PySt where
  /-- The `io.BytesIO` data and position. -/
  inp : Bytes
  pos : Nat := 0
  /-- `_Unframer.current_frame`: frame data and position. -/
  frame : Option (Bytes × Nat) := none
  /-- `self.stack`, top first. -/
  stack : List DV := []
  /-- `self.metastack`, top first. -/
  metastack : List (List DV) := []
  /-- `self.memo` (a dict; keys are unique). -/
  memo : List (Int × DV) := []
  heap : Heap := []
  proto : Nat := 0

abbrev PyM := StateT PySt (Except PyExc)

def pyThrow {α : Type} (e : PyExc) : PyM α := throw e
def pyLift {α : Type} : Py α → PyM α
  | .ok a => pure a
  | .error e => throw e

/-- `self._file_read(n)` on the BytesIO. -/
def fileRead (n : Nat) : PyM Bytes := do
  let s ← get
  let d := (s.inp.drop s.pos).take n
  set { s with pos := s.pos + d.length }
  return d

/-- `self._file_readline()`: up to and including the next newline. -/
def fileReadline : PyM Bytes := do
  let s ← get
  let rest := s.inp.drop s.pos
  let line := match rest.findIdx? (· == nl) with
    | some i => rest.take (i + 1)
    | Option.none => rest
  set { s with pos := s.pos + line.length }
  return line

/-- `_Unframer.read` (`Lib/pickle.py:280-291`). -/
def pyRead (n : Nat) : PyM Bytes := do
  let s ← get
  match s.frame with
  | some (f, fp) =>
    let data := (f.drop fp).take n
    set { s with frame := some (f, fp + data.length) }
    if data = [] ∧ n ≠ 0 then
      modify fun s => { s with frame := Option.none }
      fileRead n
    else if data.length < n then pyThrow (unpicklingError "pickle exhausted before end of frame")
    else return data
  | Option.none => fileRead n

/-- `_Unframer.readline` (`Lib/pickle.py:293-304`). -/
def pyReadline : PyM Bytes := do
  let s ← get
  match s.frame with
  | some (f, fp) =>
    let rest := f.drop fp
    let data := match rest.findIdx? (· == nl) with
      | some i => rest.take (i + 1)
      | Option.none => rest
    set { s with frame := some (f, fp + data.length) }
    if data = [] then
      modify fun s => { s with frame := Option.none }
      fileReadline
    else if data.getLast? ≠ some nl then pyThrow (unpicklingError "pickle exhausted before end of frame")
    else return data
  | Option.none => fileReadline

/-- `_Unframer.readinto(buf)` with `len(buf) = n`, returning the new buffer
contents (`buf[:] = ...` may shorten it) (`Lib/pickle.py:263-278`). -/
def pyReadinto (n : Nat) : PyM Bytes := do
  let s ← get
  match s.frame with
  | some (f, fp) =>
    let data := (f.drop fp).take n
    set { s with frame := some (f, fp + data.length) }
    if data.length = 0 ∧ n ≠ 0 then
      modify fun s => { s with frame := Option.none }
      fileRead n
    else if data.length < n then pyThrow (unpicklingError "pickle exhausted before end of frame")
    else return data
  | Option.none => fileRead n

def push (v : DV) : PyM Unit := modify fun s => { s with stack := v :: s.stack }

/-- `self.stack.pop()`. -/
def pyPop : PyM DV := do
  let s ← get
  match s.stack with
  | v :: r => set { s with stack := r }; return v
  | [] => pyThrow (.indexError "pop from empty list")

/-- `self.stack[-1]`. -/
def pyTop : PyM DV := do
  match (← get).stack with
  | v :: _ => return v
  | [] => pyThrow (.indexError "list index out of range")

/-- `pop_mark` (`Lib/pickle.py:1325-1329`): the items in push order. -/
def pyPopMark : PyM (List DV) := do
  let s ← get
  match s.metastack with
  | m :: r => set { s with stack := m, metastack := r }; return s.stack.reverse
  | [] => pyThrow (.indexError "pop from empty list")

def pyAlloc (o : HObj) : PyM DV := do
  let s ← get
  let (h, v) := s.heap.alloc o
  set { s with heap := h }
  return v

def setHeap (h : Heap) : PyM Unit := modify fun s => { s with heap := h }

/-- `read(1)[0]`: `IndexError` at end of input. -/
def pyRead1 : PyM Nat := do
  match ← pyRead 1 with
  | b :: _ => return b.toNat
  | [] => pyThrow (.indexError "index out of range")

/-- `unpack('<X', read(k))`. -/
def pyUnpack (k : Nat) : PyM Bytes := do
  let d ← pyRead k
  if d.length = k then return d
  else pyThrow (structError s!"unpack requires a buffer of {k} bytes")

def memoGetPy (i : Int) : PyM DV := do
  match (← get).memo.lookup i with
  | some v => push v
              return v
  | Option.none => pyThrow (unpicklingError s!"Memo value not found at index {i}")

def memoPutPy (i : Int) (v : DV) : PyM Unit := modify fun s =>
  { s with memo := if s.memo.any (·.1 == i) then s.memo.map (fun p => if p.1 == i then (i, v) else p)
                    else s.memo ++ [(i, v)] }

/-- Python's error for an unknown opcode byte: `KeyError(key[0])`. -/
def pyKeyError (c : UInt8) : PyExc := .keyError (toString c.toNat)

/-- One opcode of `_Unpickler.load` (`Lib/pickle.py:1294-1323`); `some v` on
`STOP`. -/
def pyStep (op : UInt8) : PyM (Option DV) := do
  let h := (← get).heap
  if op == oPROTO then
    -- load_proto, :1336-1341
    let p ← pyRead1
    if p ≤ 5 then modify fun s => { s with proto := p } else pyThrow (.valueError s!"unsupported pickle protocol: {p}")
    return Option.none
  else if op == oFRAME then
    -- load_frame, :1343-1347; _Unframer.load_frame, :306-310
    let size := leNat (← pyUnpack 8)
    if size > ssizeMaxN then pyThrow (.valueError s!"frame size > sys.maxsize: {size}")
    let s ← get
    match s.frame with
    | some (f, fp) =>
      set { s with frame := some (f, f.length) }
      if fp < f.length then pyThrow (unpicklingError "beginning of a new frame before end of current frame")
    | Option.none => pure ()
    let data ← fileRead size
    modify fun s => { s with frame := some (data, 0) }
    return Option.none
  else if op == oNONE then push .none; return Option.none
  else if op == oNEWFALSE then push (.bool false); return Option.none
  else if op == oNEWTRUE then push (.bool true); return Option.none
  else if op == oINT then
    match ← pyLift (pyLoadIntLine (← pyReadline)) with
    | .int v => push (.int v)
    | .bool b => push (.bool b)
    return Option.none
  else if op == oBININT then push (.int (leInt (← pyUnpack 4))); return Option.none
  else if op == oBININT1 then push (.int (← pyRead1)); return Option.none
  else if op == oBININT2 then push (.int (leNat (← pyUnpack 2))); return Option.none
  else if op == oLONG then push (.int (← pyLift (pyLoadLongLine (← pyReadline)))); return Option.none
  else if op == oLONG1 then
    let n ← pyRead1
    push (.int (decodeLong (← pyRead n))); return Option.none
  else if op == oLONG4 then
    let n := leInt (← pyUnpack 4)
    if n < 0 then pyThrow (unpicklingError "LONG pickle has negative byte count")
    push (.int (decodeLong (← pyRead n.toNat))); return Option.none
  else if op == oSTRING then
    let data := (← pyReadline).dropLast
    if data.length ≥ 2 ∧ data.head? = data.getLast? ∧ (data.head? = some 0x22 ∨ data.head? = some 0x27) then
      push (← pyLift (decodeString (← pyLift (escapeDecode 0 ((data.drop 1).dropLast)))))
    else pyThrow (unpicklingError "the STRING opcode argument must be quoted")
    return Option.none
  else if op == oBINSTRING then
    let n := leInt (← pyUnpack 4)
    if n < 0 then pyThrow (unpicklingError "BINSTRING pickle has negative byte count")
    push (← pyLift (decodeString (← pyRead n.toNat))); return Option.none
  else if op == oSHORT_BINSTRING then
    let n ← pyRead1
    push (← pyLift (decodeString (← pyRead n))); return Option.none
  else if op == oBINBYTES then
    let n := leNat (← pyUnpack 4)
    push (.bytes (← pyRead n)); return Option.none
  else if op == oSHORT_BINBYTES then
    let n ← pyRead1
    push (.bytes (← pyRead n)); return Option.none
  else if op == oBINBYTES8 then
    let n := leNat (← pyUnpack 8)
    if n > ssizeMaxN then pyThrow (unpicklingError s!"BINBYTES8 exceeds system's maximum size of {ssizeMaxN} bytes")
    push (.bytes (← pyRead n)); return Option.none
  else if op == oBYTEARRAY8 then
    let n := leNat (← pyUnpack 8)
    if n > ssizeMaxN then pyThrow (unpicklingError s!"BYTEARRAY8 exceeds system's maximum size of {ssizeMaxN} bytes")
    let b ← pyReadinto n
    push (← pyAlloc (.bytearray b)); return Option.none
  else if op == oUNICODE then
    push (.str (← pyLift (decodeRUE (← pyReadline).dropLast))); return Option.none
  else if op == oBINUNICODE then
    let n := leNat (← pyUnpack 4)
    push (.str (← pyLift (decodeUtf8SP (← pyRead n)))); return Option.none
  else if op == oSHORT_BINUNICODE then
    let n ← pyRead1
    push (.str (← pyLift (decodeUtf8SP (← pyRead n)))); return Option.none
  else if op == oBINUNICODE8 then
    let n := leNat (← pyUnpack 8)
    if n > ssizeMaxN then pyThrow (unpicklingError s!"BINUNICODE8 exceeds system's maximum size of {ssizeMaxN} bytes")
    push (.str (← pyLift (decodeUtf8SP (← pyRead n)))); return Option.none
  else if op == oTUPLE then push (.tuple (← pyPopMark)); return Option.none
  else if op == oEMPTY_TUPLE then push (.tuple []); return Option.none
  else if op == oTUPLE1 then
    let s ← get
    match s.stack with
    | a :: r => set { s with stack := .tuple [a] :: r }
    | [] => pyThrow (.indexError "list index out of range")
    return Option.none
  else if op == oTUPLE2 then
    let s ← get
    match s.stack with
    | b :: a :: r => set { s with stack := .tuple [a, b] :: r }
    | _ => pyThrow (.indexError "list index out of range")
    return Option.none
  else if op == oTUPLE3 then
    let s ← get
    match s.stack with
    | c :: b :: a :: r => set { s with stack := .tuple [a, b, c] :: r }
    | _ => pyThrow (.indexError "list index out of range")
    return Option.none
  else if op == oEMPTY_LIST then push (← pyAlloc (.list [])); return Option.none
  else if op == oEMPTY_DICT then push (← pyAlloc (.dict [])); return Option.none
  else if op == oEMPTY_SET then push (← pyAlloc (.set [])); return Option.none
  else if op == oFROZENSET then
    let items ← pyPopMark
    push (← pyLift (mkFrozenset (← get).heap items)); return Option.none
  else if op == oLIST then
    let items ← pyPopMark
    push (← pyAlloc (.list items)); return Option.none
  else if op == oDICT then
    -- load_dict, :1580-1585: {items[i]: items[i+1] for i in range(0, len(items), 2)}
    let items ← pyPopMark
    let rec build (acc : List (DV × DV)) : List DV → Py (List (DV × DV))
      | [] => .ok acc
      | [_] => .error (.indexError "list index out of range")
      | k :: v :: r => do build (← dictSet h acc k v) r
    let kvs ← pyLift (build [] items)
    push (← pyAlloc (.dict kvs)); return Option.none
  else if op == oAPPEND then
    let value ← pyPop
    let lst ← pyTop
    setHeap (← pyLift (appendTo (← get).heap lst value)); return Option.none
  else if op == oAPPENDS then
    let items ← pyPopMark
    let lst ← pyTop
    let h := (← get).heap
    if hasExtend h lst then setHeap (← pyLift (extendObj h lst items))
    else match lst with
      | .glob _ => pyThrow (excluded "global as APPENDS target")
      | _ => pyThrow (attributeError s!"'{lst.typeName h}' object has no attribute 'append'")
    return Option.none
  else if op == oSETITEM then
    let value ← pyPop
    let key ← pyPop
    let d ← pyTop
    setHeap (← pyLift (setItem (← get).heap d key value)); return Option.none
  else if op == oSETITEMS then
    let items ← pyPopMark
    let d ← pyTop
    let rec go (h : Heap) : List DV → Py Heap
      | [] => .ok h
      | [_] => .error (.indexError "list index out of range")
      | k :: v :: r => do go (← setItem h d k v) r
    setHeap (← pyLift (go (← get).heap items)); return Option.none
  else if op == oADDITEMS then
    let items ← pyPopMark
    let so ← pyTop
    let h := (← get).heap
    if isSetRef h so then setHeap (← pyLift (setUpdate h so items))
    else pyThrow (noAdd h so)
    return Option.none
  else if op == oPOP then
    -- load_pop, :1704-1709
    if (← get).stack ≠ [] then discard pyPop else discard pyPopMark
    return Option.none
  else if op == oPOP_MARK then discard pyPopMark; return Option.none
  else if op == oDUP then push (← pyTop); return Option.none
  else if op == oGET then
    let i ← pyLift (pyIntOfBytes (← pyReadline).dropLast)
    discard (memoGetPy i); return Option.none
  else if op == oBINGET then discard (memoGetPy (← pyRead1)); return Option.none
  else if op == oLONG_BINGET then discard (memoGetPy (leNat (← pyUnpack 4))); return Option.none
  else if op == oPUT then
    let i ← pyLift (pyIntOfBytes (← pyReadline).dropLast)
    if i < 0 then pyThrow (.valueError "negative PUT argument")
    memoPutPy i (← pyTop); return Option.none
  else if op == oBINPUT then
    let i ← pyRead1
    memoPutPy i (← pyTop); return Option.none
  else if op == oLONG_BINPUT then
    let i := leNat (← pyUnpack 4)
    memoPutPy i (← pyTop); return Option.none
  else if op == oMEMOIZE then
    let v ← pyTop
    memoPutPy (← get).memo.length v; return Option.none
  else if op == oMARK then
    modify fun s => { s with metastack := s.stack :: s.metastack, stack := [] }; return Option.none
  else if op == oSTOP then return some (← pyPop)
  else if op == oGLOBAL then
    -- load_global, :1633-1638 (names decoded as UTF-8)
    let m := (← pyReadline).dropLast
    let n := (← pyReadline).dropLast
    let m ← pyLift (match utf8Dec false m with | some s => .ok s | Option.none => .error unicodeDecodeError)
    let n ← pyLift (match utf8Dec false n with | some s => .ok s | Option.none => .error unicodeDecodeError)
    push (.glob (← pyLift (findGlob (← get).proto m n))); return Option.none
  else if op == oSTACK_GLOBAL then
    -- load_stack_global, :1640-1646
    let name ← pyPop
    let module ← pyPop
    match module, name with
    | .str m, .str n => push (.glob (← pyLift (findGlob (← get).proto m n)))
    | _, _ => pyThrow (unpicklingError "STACK_GLOBAL requires str")
    return Option.none
  else if op == oREDUCE then
    -- load_reduce, :1697-1702
    let args ← pyPop
    let func ← pyTop
    match func, args with
    | .glob g, .tuple xs =>
      let (h', v) ← pyLift (callGlob (← get).heap g xs)
      modify fun s => { s with heap := h', stack := v :: s.stack.drop 1 }
    | _, _ => pyThrow (excluded "REDUCE")
    return Option.none
  else if op == oFLOAT || op == oBINFLOAT || op == oPERSID || op == oBINPERSID || op == oINST
      || op == oOBJ || op == oNEWOBJ || op == oNEWOBJ_EX || op == oBUILD || op == oEXT1
      || op == oEXT2 || op == oEXT4 || op == oNEXT_BUFFER || op == oREADONLY_BUFFER then
    pyThrow (excluded "opcode")
  else pyThrow (pyKeyError op)

/-- The dispatch loop of `_Unpickler.load`, with fuel (each step consumes at
least one input byte). -/
def pyLoop : Nat → PyM DV
  | 0 => pyThrow .modelFuel
  | fuel + 1 => do
    match ← pyRead 1 with
    | [] => pyThrow (eofError "")
    | op :: _ =>
      match ← pyStep op with
      | some v => return v
      | Option.none => pyLoop fuel

/-- `pickle._loads(data)`: the result and the final heap. -/
def pyLoads (data : Bytes) : Py (DV × Heap) := do
  let (v, s) ← (pyLoop (data.length + 1)).run { inp := data }
  return (v, s.heap)

end PyLean.Pickle
