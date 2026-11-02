import PyLean.Pickle.Obj

/-!
`_Unpickler` (`Lib/pickle.py:1270-1889`) reading from `io.BytesIO(data)`
(`_loads`, `:1909-1915`), with `encoding='ASCII'`, `errors='strict'`, no
`buffers`, and `find_class` restricted to the five globals the picklers emit
(`Obj.findGlob`). Opcodes that run code or are out of scope (persistent ids,
floats, `INST`/`OBJ`/`NEWOBJ*`, `BUILD`, `EXT*`, out-of-band buffers) raise the
model-only `Excluded` exception; the differential test never generates them.
-/

namespace PyLean.Pickle

open PyLean

/-- `bytes.decode` escape processing of `codecs.escape_decode`
(`_PyBytes_DecodeEscape2`, `Objects/bytesobject.c:1170-1276`), strict. `pos`
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

/-- `_MIN_READ_BUF_SIZE` (`Lib/pickle.py:194`). -/
def minReadBufSize : Nat := 1 <<< 20

/-- The `while` of `_Unframer._chunked_file_read` (`Lib/pickle.py:313-316`). The
fuel is `size`: every round adds at least one byte to `cursize`. -/
def chunkedLoop : Nat → Nat → Nat → Bytes → PyM Bytes
  | 0, _, _, b => return b
  | fuel + 1, size, cursize, b =>
    if cursize < size ∧ b.length = cursize then do
      let delta := min cursize (size - cursize)
      let d ← fileRead delta
      chunkedLoop fuel size (cursize + delta) (b ++ d)
    else return b

/-- `_Unframer._chunked_file_read(size)` (`Lib/pickle.py:310-317`). -/
def chunkedFileRead (size : Nat) : PyM Bytes := do
  let cursize := min size minReadBufSize
  let b ← fileRead cursize
  chunkedLoop size size cursize b

/-- `self._file_readline()`: up to and including the next newline. -/
def fileReadline : PyM Bytes := do
  let s ← get
  let rest := s.inp.drop s.pos
  let line := match rest.findIdx? (· == nl) with
    | some i => rest.take (i + 1)
    | Option.none => rest
  set { s with pos := s.pos + line.length }
  return line

/-- `_Unframer.read` (`Lib/pickle.py:284-295`). The frame branch keeps
`file_read`; only the branch without a frame reads in chunks. -/
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
  | Option.none => chunkedFileRead n

/-- `_Unframer.readline` (`Lib/pickle.py:297-308`). -/
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

/-- `_Unframer.readinto(buf)` with `len(buf) = n`: the new buffer contents
(`buf[:] = ...` may shorten it) and the int it returns (`Lib/pickle.py:267-282`). -/
def pyReadinto (n : Nat) : PyM (Bytes × Nat) := do
  let s ← get
  match s.frame with
  | some (f, fp) =>
    let data := (f.drop fp).take n
    set { s with frame := some (f, fp + data.length) }
    if data.length = 0 ∧ n ≠ 0 then
      modify fun s => { s with frame := Option.none }
      return (← fileRead n, n)
    else if data.length < n then pyThrow (unpicklingError "pickle exhausted before end of frame")
    else return (data, data.length)
  | Option.none => return (← fileRead n, n)

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

/-- `pop_mark` (`Lib/pickle.py:1351-1355`): the items in push order. -/
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

/-! ## Opcode handlers (`Lib/pickle.py:1362-1889`) -/

/-- `load_proto`, :1362-1367. -/
def pyLoadProto : PyM Unit := do
  let p ← pyRead1
  if p ≤ 5 then modify fun s => { s with proto := p }
  else pyThrow (.valueError s!"unsupported pickle protocol: {p}")

/-- `data = self._chunked_file_read(frame_size)` and what follows it in
`_Unframer.load_frame`, `Lib/pickle.py:323-326`: a short read is `EOFError`. -/
def pyReadFrame (size : Nat) : PyM Unit := do
  let data ← chunkedFileRead size
  if data.length < size then pyThrow (eofError "")
  else modify fun s => { s with frame := some (data, 0) }

/-- The tail of `load_frame` once the size is read: `_Unframer.load_frame`, :319-326. -/
def pyStartFrame (size : Nat) : PyM Unit := do
  let s ← get
  match s.frame with
  | some (f, fp) =>
    set { s with frame := some (f, f.length) }
    if fp < f.length then pyThrow (unpicklingError "beginning of a new frame before end of current frame")
    else pyReadFrame size
  | Option.none => pyReadFrame size

/-- `load_frame`, :1369-1373. -/
def pyLoadFrame : PyM Unit := do
  let size := leNat (← pyUnpack 8)
  if size > ssizeMaxN then pyThrow (.valueError s!"frame size > sys.maxsize: {size}")
  else pyStartFrame size

def pyLoadNone : PyM Unit := push .none
def pyLoadFalse : PyM Unit := push (.bool false)
def pyLoadTrue : PyM Unit := push (.bool true)

/-- `load_int`, :1402-1411. -/
def pyLoadInt : PyM Unit := do
  match ← pyLift (pyLoadIntLine (← pyReadline)) with
  | .int v => push (.int v)
  | .bool b => push (.bool b)

def pyLoadBinint : PyM Unit := do push (.int (leInt (← pyUnpack 4)))
def pyLoadBinint1 : PyM Unit := do push (.int (← pyRead1))
def pyLoadBinint2 : PyM Unit := do push (.int (leNat (← pyUnpack 2)))
def pyLoadLong : PyM Unit := do push (.int (← pyLift (pyLoadLongLine (← pyReadline))))

/-- `load_long1`, :1432-1436. -/
def pyLoadLong1 : PyM Unit := do
  let n ← pyRead1
  push (.int (decodeLong (← pyRead n)))

/-- `load_long4`, :1438-1445. -/
def pyLoadLong4 : PyM Unit := do
  let n := leInt (← pyUnpack 4)
  if n < 0 then pyThrow (unpicklingError "LONG pickle has negative byte count")
  else push (.int (decodeLong (← pyRead n.toNat)))

def quotedString (data : Bytes) : Prop :=
  data.length ≥ 2 ∧ data.head? = data.getLast? ∧ (data.head? = some 0x22 ∨ data.head? = some 0x27)

instance (data : Bytes) : Decidable (quotedString data) := by unfold quotedString; exact inferInstance

/-- `load_string`, :1464-1472. -/
def pyLoadString : PyM Unit := do
  let data := (← pyReadline).dropLast
  if quotedString data then
    push (← pyLift (decodeString (← pyLift (escapeDecode 0 ((data.drop 1).dropLast)))))
  else pyThrow (unpicklingError "the STRING opcode argument must be quoted")

/-- `load_binstring`, :1474-1481. -/
def pyLoadBinstring : PyM Unit := do
  let n := leInt (← pyUnpack 4)
  if n < 0 then pyThrow (unpicklingError "BINSTRING pickle has negative byte count")
  else push (← pyLift (decodeString (← pyRead n.toNat)))

def pyLoadShortBinstring : PyM Unit := do
  let n ← pyRead1
  push (← pyLift (decodeString (← pyRead n)))

def pyLoadBinbytes : PyM Unit := do
  let n := leNat (← pyUnpack 4)
  push (.bytes (← pyRead n))

def pyLoadShortBinbytes : PyM Unit := do
  let n ← pyRead1
  push (.bytes (← pyRead n))

/-- `load_binbytes8`, :1511-1517. -/
def pyLoadBinbytes8 : PyM Unit := do
  let n := leNat (← pyUnpack 8)
  if n > ssizeMaxN then pyThrow (unpicklingError s!"BINBYTES8 exceeds system's maximum size of {ssizeMaxN} bytes")
  else push (.bytes (← pyRead n))

/-- The `while` of `load_bytearray8`, :1527-1530. As in `chunkedLoop`, the fuel
is `size`. -/
def bytearrayLoop : Nat → Nat → Nat → Bytes → PyM Bytes
  | 0, _, _, b => return b
  | fuel + 1, size, cursize, b =>
    if cursize < size ∧ b.length = cursize then do
      let delta := min cursize (size - cursize)
      let d ← pyRead delta
      bytearrayLoop fuel size (cursize + delta) (b ++ d)
    else return b

/-- `load_bytearray8`, :1519-1531. -/
def pyLoadBytearray8 : PyM Unit := do
  let size := leNat (← pyUnpack 8)
  if size > ssizeMaxN then pyThrow (unpicklingError s!"BYTEARRAY8 exceeds system's maximum size of {ssizeMaxN} bytes")
  else
    let cursize := min size minReadBufSize
    let (b, r) ← pyReadinto cursize
    let b ← if r = cursize then bytearrayLoop size size cursize b else pure b
    push (← pyAlloc (.bytearray b))

def pyLoadUnicode : PyM Unit := do push (.str (← pyLift (decodeRUE (← pyReadline).dropLast)))

def pyLoadBinunicode : PyM Unit := do
  let n := leNat (← pyUnpack 4)
  push (.str (← pyLift (decodeUtf8SP (← pyRead n))))

def pyLoadShortBinunicode : PyM Unit := do
  let n ← pyRead1
  push (.str (← pyLift (decodeUtf8SP (← pyRead n))))

/-- `load_binunicode8`, :1503-1509. -/
def pyLoadBinunicode8 : PyM Unit := do
  let n := leNat (← pyUnpack 8)
  if n > ssizeMaxN then pyThrow (unpicklingError s!"BINUNICODE8 exceeds system's maximum size of {ssizeMaxN} bytes")
  else push (.str (← pyLift (decodeUtf8SP (← pyRead n))))

def pyLoadTuple : PyM Unit := do push (.tuple (← pyPopMark))
def pyLoadEmptyTuple : PyM Unit := push (.tuple [])

/-- `load_tuple1`, :1577-1579: `self.stack[-1] = (self.stack[-1],)`. -/
def pyLoadTuple1 : PyM Unit := do
  let s ← get
  match s.stack with
  | a :: r => set { s with stack := .tuple [a] :: r }
  | [] => pyThrow (.indexError "list index out of range")

def pyLoadTuple2 : PyM Unit := do
  let s ← get
  match s.stack with
  | b :: a :: r => set { s with stack := .tuple [a, b] :: r }
  | _ => pyThrow (.indexError "list index out of range")

def pyLoadTuple3 : PyM Unit := do
  let s ← get
  match s.stack with
  | c :: b :: a :: r => set { s with stack := .tuple [a, b, c] :: r }
  | _ => pyThrow (.indexError "list index out of range")

def pyLoadEmptyList : PyM Unit := do push (← pyAlloc (.list []))
def pyLoadEmptyDict : PyM Unit := do push (← pyAlloc (.dict []))
def pyLoadEmptySet : PyM Unit := do push (← pyAlloc (.set []))

/-- `load_frozenset`, :1601-1604. -/
def pyLoadFrozenset : PyM Unit := do
  let items ← pyPopMark
  push (← pyLift (mkFrozenset (← get).heap items))

/-- `load_list`, :1606-1609. -/
def pyLoadList : PyM Unit := do
  let items ← pyPopMark
  push (← pyAlloc (.list items))

/-- The dict comprehension of `load_dict`, :1614-1615. -/
def dictBuild (h : Heap) (acc : List (DV × DV)) : List DV → Py (List (DV × DV))
  | [] => .ok acc
  | [_] => .error (.indexError "list index out of range")
  | k :: v :: r => do dictBuild h (← dictSet h acc k v) r

/-- `load_dict`, :1611-1616. -/
def pyLoadDict : PyM Unit := do
  let items ← pyPopMark
  let kvs ← pyLift (dictBuild (← get).heap [] items)
  push (← pyAlloc (.dict kvs))

/-- `load_append`, :1803-1807. -/
def pyLoadAppend : PyM Unit := do
  let value ← pyPop
  let lst ← pyTop
  setHeap (← pyLift (appendTo (← get).heap lst value))

/-- The `extend`, falling back on `append`, of `load_appends`, :1813-1826. -/
def pyExtendItems (lst : DV) (items : List DV) : PyM Unit := do
  let h := (← get).heap
  if hasExtend h lst then setHeap (← pyLift (extendObj h lst items))
  else
    match lst with
    | .glob _ => pyThrow (excluded "global as APPENDS target")
    | _ => pyThrow (attributeError s!"'{lst.typeName h}' object has no attribute 'append'")

/-- `load_appends`, :1810-1826. -/
def pyLoadAppends : PyM Unit := do
  let items ← pyPopMark
  let lst ← pyTop
  pyExtendItems lst items

/-- `load_setitem`, :1828-1834. -/
def pyLoadSetitem : PyM Unit := do
  let value ← pyPop
  let key ← pyPop
  let d ← pyTop
  setHeap (← pyLift (setItem (← get).heap d key value))

/-- The loop of `load_setitems`, :1839-1840. -/
def setitemsGo (d : DV) (h : Heap) : List DV → Py Heap
  | [] => .ok h
  | [_] => .error (.indexError "list index out of range")
  | k :: v :: r => do setitemsGo d (← setItem h d k v) r

/-- `load_setitems`, :1836-1840. -/
def pyLoadSetitems : PyM Unit := do
  let items ← pyPopMark
  let d ← pyTop
  setHeap (← pyLift (setitemsGo d (← get).heap items))

/-- `load_additems`, :1843-1851. -/
def pyLoadAdditems : PyM Unit := do
  let items ← pyPopMark
  let so ← pyTop
  let h := (← get).heap
  if isSetRef h so then setHeap (← pyLift (setUpdate h so items))
  else pyThrow (noAdd h so)

/-- `load_pop`, :1735-1740. -/
def pyLoadPop : PyM Unit := do
  if (← get).stack ≠ [] then discard pyPop else discard pyPopMark

def pyLoadPopMark : PyM Unit := do discard pyPopMark
def pyLoadDup : PyM Unit := do push (← pyTop)

/-- `load_get`, :1750-1757. -/
def pyLoadGet : PyM Unit := do
  let i ← pyLift (pyIntOfBytes (← pyReadline).dropLast)
  discard (memoGetPy i)

def pyLoadBinget : PyM Unit := do discard (memoGetPy (← pyRead1))
def pyLoadLongBinget : PyM Unit := do discard (memoGetPy (leNat (← pyUnpack 4)))

/-- `load_put`, :1777-1782. -/
def pyLoadPut : PyM Unit := do
  let i ← pyLift (pyIntOfBytes (← pyReadline).dropLast)
  if i < 0 then pyThrow (.valueError "negative PUT argument")
  else memoPutPy i (← pyTop)

def pyLoadBinput : PyM Unit := do
  let i ← pyRead1
  memoPutPy i (← pyTop)

def pyLoadLongBinput : PyM Unit := do
  let i := leNat (← pyUnpack 4)
  memoPutPy i (← pyTop)

/-- `load_memoize`, :1798-1800: the value is evaluated first. -/
def pyLoadMemoize : PyM Unit := do
  let v ← pyTop
  memoPutPy (← get).memo.length v

/-- `load_mark`, :1878-1882. -/
def pyLoadMark : PyM Unit :=
  modify fun s => { s with metastack := s.stack :: s.metastack, stack := [] }

def utf8Name (b : Bytes) : Py (List Nat) :=
  match utf8Dec false b with
  | some s => .ok s
  | Option.none => .error unicodeDecodeError

/-- `load_global`, :1664-1669 (names decoded as UTF-8). -/
def pyLoadGlobal : PyM Unit := do
  let m := (← pyReadline).dropLast
  let n := (← pyReadline).dropLast
  let m ← pyLift (utf8Name m)
  let n ← pyLift (utf8Name n)
  push (.glob (← pyLift (findGlob (← get).proto m n)))

/-- `load_stack_global`, :1671-1677. -/
def pyLoadStackGlobal : PyM Unit := do
  let name ← pyPop
  let module ← pyPop
  match module, name with
  | .str m, .str n => push (.glob (← pyLift (findGlob (← get).proto m n)))
  | _, _ => pyThrow (unpicklingError "STACK_GLOBAL requires str")

/-- `load_reduce`, :1728-1733. -/
def pyLoadReduce : PyM Unit := do
  let args ← pyPop
  let func ← pyTop
  match func, args with
  | .glob g, .tuple xs =>
    let (h', v) ← pyLift (callGlob (← get).heap g xs)
    modify fun s => { s with heap := h', stack := v :: s.stack.drop 1 }
  | _, _ => pyThrow (excluded "REDUCE")

/-- The `dispatch` dict for the modelled opcodes other than `STOP`. -/
def pyTable : List (UInt8 × PyM Unit) := [
  (oPROTO, pyLoadProto), (oFRAME, pyLoadFrame), (oNONE, pyLoadNone), (oNEWFALSE, pyLoadFalse),
  (oNEWTRUE, pyLoadTrue), (oINT, pyLoadInt), (oBININT, pyLoadBinint), (oBININT1, pyLoadBinint1),
  (oBININT2, pyLoadBinint2), (oLONG, pyLoadLong), (oLONG1, pyLoadLong1), (oLONG4, pyLoadLong4),
  (oSTRING, pyLoadString), (oBINSTRING, pyLoadBinstring), (oSHORT_BINSTRING, pyLoadShortBinstring),
  (oBINBYTES, pyLoadBinbytes), (oSHORT_BINBYTES, pyLoadShortBinbytes), (oBINBYTES8, pyLoadBinbytes8),
  (oBYTEARRAY8, pyLoadBytearray8), (oUNICODE, pyLoadUnicode), (oBINUNICODE, pyLoadBinunicode),
  (oSHORT_BINUNICODE, pyLoadShortBinunicode), (oBINUNICODE8, pyLoadBinunicode8), (oTUPLE, pyLoadTuple),
  (oEMPTY_TUPLE, pyLoadEmptyTuple), (oTUPLE1, pyLoadTuple1), (oTUPLE2, pyLoadTuple2), (oTUPLE3, pyLoadTuple3),
  (oEMPTY_LIST, pyLoadEmptyList), (oEMPTY_DICT, pyLoadEmptyDict), (oEMPTY_SET, pyLoadEmptySet),
  (oFROZENSET, pyLoadFrozenset), (oLIST, pyLoadList), (oDICT, pyLoadDict), (oAPPEND, pyLoadAppend),
  (oAPPENDS, pyLoadAppends), (oSETITEM, pyLoadSetitem), (oSETITEMS, pyLoadSetitems),
  (oADDITEMS, pyLoadAdditems), (oPOP, pyLoadPop), (oPOP_MARK, pyLoadPopMark), (oDUP, pyLoadDup),
  (oGET, pyLoadGet), (oBINGET, pyLoadBinget), (oLONG_BINGET, pyLoadLongBinget), (oPUT, pyLoadPut),
  (oBINPUT, pyLoadBinput), (oLONG_BINPUT, pyLoadLongBinput), (oMEMOIZE, pyLoadMemoize), (oMARK, pyLoadMark),
  (oGLOBAL, pyLoadGlobal), (oSTACK_GLOBAL, pyLoadStackGlobal), (oREDUCE, pyLoadReduce)]

/-- Opcodes that run code or are out of scope for the plain-data model. -/
def excludedOps : List UInt8 := [oFLOAT, oBINFLOAT, oPERSID, oBINPERSID, oINST, oOBJ, oNEWOBJ, oNEWOBJ_EX,
  oBUILD, oEXT1, oEXT2, oEXT4, oNEXT_BUFFER, oREADONLY_BUFFER]

/-- One opcode of `_Unpickler.load` (`Lib/pickle.py:1320-1349`); `some v` on
`STOP` (`load_stop`, :1884-1886). -/
def pyStep (op : UInt8) : PyM (Option DV) :=
  if op == oSTOP then do return some (← pyPop)
  else match pyTable.lookup op with
    | some h => do h; return Option.none
    | Option.none =>
      if excludedOps.contains op then pyThrow (excluded "opcode") else pyThrow (pyKeyError op)

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
