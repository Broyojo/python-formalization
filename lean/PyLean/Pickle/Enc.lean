import PyLean.Pickle.Long
import PyLean.Pickle.Value

/-!
The two picklers: `_Pickler` (`Lib/pickle.py:434-1267`) and the C `Pickler`
(`Modules/_pickle.c:741-4942`), restricted to the plain-data types.

Each pickler emits the sequence of calls it makes on its output layer
(`Event`): Python's `_Framer` (`Lib/pickle.py:197-257`) and C's
`_Pickler_Write`/`_Pickler_OpcodeBoundary`/`_Pickler_write_bytes`
(`Modules/_pickle.c:996-1132`, `:2553-2617`). A framer then turns the call
sequence into bytes. Framing decisions depend only on these calls and never
feed back into the pickler, so running the framer afterwards is the same as
running it interleaved.

`batched(items, 1000)` loops are unrolled item by item: item `i` starts a
batch when `i % 1000 = 0`, and that batch holds `min(1000, n - i)` items.
The C `do { ... } while` batch loops are unrolled the same way.
-/

namespace PyLean.Pickle

open PyLean

inductive Event where
  /-- `framer.write(data)` / `_Pickler_Write(data)`. -/
  | w (data : Bytes)
  /-- Start of `save()`: `framer.commit_frame()` / `_Pickler_OpcodeBoundary`. -/
  | boundary
  /-- `_write_large_bytes(header, payload)` / `_Pickler_write_bytes` with
  `data_size >= FRAME_SIZE_TARGET`. -/
  | large (hdr payload : Bytes)
  /-- `framer.start_framing()` / `self->framing = 1`. -/
  | start
  /-- `framer.end_framing()` / the final `_Pickler_CommitFrame`. -/
  | finish
  deriving Repr, DecidableEq

def frameSizeTarget : Nat := 65536
def frameSizeMin : Nat := 4
def batchSize : Nat := 1000

structure EncSt where
  /-- `id(obj) -> memo index`, most recent first. -/
  memo : List (Oid × Nat) := []
  /-- Output-layer calls, most recent first. -/
  ev : List Event := []

abbrev EncM := StateT EncSt (Except PyExc)

def emit (e : Event) : EncM Unit := modify fun s => { s with ev := e :: s.ev }
def wr (b : Bytes) : EncM Unit := emit (.w b)
def liftPy {α : Type} : Py α → EncM α
  | .ok a => pure a
  | .error e => throw e

def memoLookup (o : Oid) : EncM (Option Nat) := do
  return (← get).memo.lookup o

def memoSize : EncM Nat := do return (← get).memo.length

def memoSet (o : Oid) (idx : Nat) : EncM Unit :=
  modify fun s => { s with memo := (o, idx) :: s.memo }

/-- Item `i` of `n`: the length of the batch that contains it. -/
def batchLen (n i : Nat) : Nat := min batchSize (n - (i - i % batchSize))

/-- The module name written by `GLOBAL`: with `fix_imports` and protocol < 3,
`builtins` becomes `__builtin__` (`_compat_pickle.REVERSE_IMPORT_MAPPING`,
`Lib/pickle.py:1236-1243`, `Modules/_pickle.c:3875-3935`). -/
def globModuleOut (proto : Nat) (g : Glob) : String :=
  if proto < 3 ∧ g.module = "builtins" then "__builtin__" else g.module

/-- Write `d` when `c` holds. -/
def optWr (c : Prop) [Decidable c] (d : Bytes) : EncM Unit := if c then wr d else pure ()

/-- `if bin: EMPTY else: MARK + opcode` at the start of `save_list`/`save_dict`. -/
def pyEmptyOp (proto : Nat) (empty op : UInt8) : EncM Unit :=
  if proto ≥ 1 then wr [empty] else wr [oMARK, op]

/-- One item of `_batch_appends` or `_batch_setitems`: `item` saves it. -/
def pyBatchStep (proto n i : Nat) (item : EncM Unit) (one many : UInt8) : EncM Unit :=
  if proto = 0 then do
    item
    wr [one]
  else do
    optWr (i % batchSize = 0 ∧ batchLen n i ≠ 1) [oMARK]
    item
    optWr ((i + 1) % batchSize = 0 ∨ i + 1 = n) [if batchLen n i ≠ 1 then many else one]

/-- One item of the `ADDITEMS` batches, in either pickler. -/
def addStep (n i : Nat) (item : EncM Unit) : EncM Unit := do
  optWr (i % batchSize = 0) [oMARK]
  item
  optWr ((i + 1) % batchSize = 0 ∨ i + 1 = n) [oADDITEMS]

/-! ## Python `_Pickler` -/

/-- `_Pickler.put` (`Lib/pickle.py:541-550`). -/
def pyPut (proto : Nat) (idx : Nat) : Py Bytes :=
  if proto ≥ 4 then .ok [oMEMOIZE]
  else if proto ≥ 1 then
    if idx < 256 then .ok [oBINPUT, idx.toUInt8]
    else (oLONG_BINPUT :: ·) <$> packU32 idx
  else .ok (oPUT :: decDigits idx ++ [nl])

/-- `_Pickler.get` (`Lib/pickle.py:553-560`). -/
def pyGet (proto : Nat) (i : Nat) : Py Bytes :=
  if proto ≥ 1 then
    if i < 256 then .ok [oBINGET, i.toUInt8]
    else (oLONG_BINGET :: ·) <$> packU32 i
  else .ok (oGET :: decDigits i ++ [nl])

/-- `_Pickler.memoize` (`Lib/pickle.py:518-538`). -/
def pyMemoize (proto : Nat) (o : Oid) : EncM Unit := do
  let idx ← memoSize
  wr (← liftPy (pyPut proto idx))
  memoSet o idx

/-- `save_str`'s protocol-0 escaping (`Lib/pickle.py:950-956`): `\`, NUL,
`\n`, `\r`, `\x1a` become `\uXXXX` before `raw-unicode-escape`. -/
def pyStrEscape (s : List Nat) : List Nat :=
  s.flatMap fun c =>
    if c = 0x5c then [0x5c, 0x75, 0x30, 0x30, 0x35, 0x63]
    else if c = 0 then [0x5c, 0x75, 0x30, 0x30, 0x30, 0x30]
    else if c = 0x0a then [0x5c, 0x75, 0x30, 0x30, 0x30, 0x61]
    else if c = 0x0d then [0x5c, 0x75, 0x30, 0x30, 0x30, 0x64]
    else if c = 0x1a then [0x5c, 0x75, 0x30, 0x30, 0x31, 0x61]
    else [c]

/-- The binary branch of `save_str`, on the UTF-8 data. -/
def pyStrData (proto : Nat) (data : Bytes) : EncM Unit :=
  let n := data.length
  if n ≤ 0xff ∧ proto ≥ 4 then wr (oSHORT_BINUNICODE :: leBytes n 1 ++ data)
  else if n > 0xffffffff ∧ proto ≥ 4 then emit (.large (oBINUNICODE8 :: leBytes n 8) data)
  else if n ≥ frameSizeTarget then
    (liftPy (packU32 n) >>= fun x => emit (.large (oBINUNICODE :: x) data))
  else (liftPy (packU32 n) >>= fun x => wr (oBINUNICODE :: x ++ data))

/-- `save_str` before the memo (`Lib/pickle.py:936-956`). -/
def pyStrBody (proto : Nat) (s : List Nat) : EncM Unit :=
  if proto ≥ 1 then pyStrData proto (utf8Enc s)
  else wr (oUNICODE :: rueEncode (pyStrEscape s) ++ [nl])

/-- `save_str` (`Lib/pickle.py:936-957`). -/
def pySaveStr (proto : Nat) (o : Oid) (s : List Nat) : EncM Unit := do
  pyStrBody proto s
  pyMemoize proto o

/-- `_save_bytes_no_memo` (`Lib/pickle.py:860-872`), protocol >= 3. -/
def pySaveBytesData (proto : Nat) (b : Bytes) : EncM Unit := do
  let n := b.length
  if n ≤ 0xff then wr (oSHORT_BINBYTES :: leBytes n 1 ++ b)
  else if n > 0xffffffff ∧ proto ≥ 4 then emit (.large (oBINBYTES8 :: leBytes n 8) b)
  else if n ≥ frameSizeTarget then
    (liftPy (packU32 n) >>= fun x => emit (.large (oBINBYTES :: x) b))
  else (liftPy (packU32 n) >>= fun x => wr (oBINBYTES :: x ++ b))

/-- `_save_bytearray_no_memo` (`Lib/pickle.py:886-894`), protocol 5. -/
def pySaveBytearrayData (b : Bytes) : EncM Unit := do
  let n := b.length
  if n ≥ frameSizeTarget then emit (.large (oBYTEARRAY8 :: leBytes n 8) b)
  else wr (oBYTEARRAY8 :: leBytes n 8 ++ b)

/-- `save(s)` for a `str`: commit check, memo check (`Lib/pickle.py:562-576`),
`save_str`. -/
def pySaveStrObj (proto : Nat) (o : Oid) (s : List Nat) : EncM Unit := do
  emit .boundary
  match ← memoLookup o with
  | some i => wr (← liftPy (pyGet proto i))
  | none => pySaveStr proto o s

/-- What `save_global` writes before the memo. -/
def pyGlobalRef (proto : Nat) (g : Glob) : EncM Unit :=
  if proto ≥ 4 then do
    pySaveStrObj proto (.tmp (.glob g) 0) ((ascii g.module).map (·.toNat))
    pySaveStrObj proto (.tmp (.glob g) 1) ((ascii g.name).map (·.toNat))
    wr [oSTACK_GLOBAL]
  else do
    wr (oGLOBAL :: ascii (globModuleOut proto g) ++ [nl])
    wr (ascii g.name ++ [nl])

/-- `save(func)` for one of the globals: `save_type` (types) or
`__reduce_ex__` returning the name (`codecs.encode`), then `save_global`
(`Lib/pickle.py:1164-1227`). -/
def pySaveGlobal (proto : Nat) (g : Glob) : EncM Unit := do
  emit .boundary
  match ← memoLookup (.glob g) with
  | some i => wr (← liftPy (pyGet proto i))
  | none =>
    pyGlobalRef proto g
    pyMemoize proto (.glob g)

/-- `save_tuple` (`Lib/pickle.py:959-1016`) for a tuple with `n` elements,
given the action that saves the elements in order. -/
def pyTupleWith (proto : Nat) (o : Oid) (n : Nat) (elems : EncM Unit) : EncM Unit := do
  if n = 0 then
    if proto ≥ 1 then wr [oEMPTY_TUPLE] else wr [oMARK, oTUPLE]
  else if n ≤ 3 ∧ proto ≥ 2 then
    elems
    match ← memoLookup o with
    | some i => wr (List.replicate n oPOP ++ (← liftPy (pyGet proto i)))
    | none =>
      wr [if n = 1 then oTUPLE1 else if n = 2 then oTUPLE2 else oTUPLE3]
      pyMemoize proto o
  else
    wr [oMARK]
    elems
    match ← memoLookup o with
    | some i =>
      if proto ≥ 1 then wr (oPOP_MARK :: (← liftPy (pyGet proto i)))
      else wr (List.replicate (n + 1) oPOP ++ (← liftPy (pyGet proto i)))
    | none =>
      wr [oTUPLE]
      pyMemoize proto o

/-- `save(t)` for a tuple. -/
def pyTupleObj (proto : Nat) (o : Oid) (n : Nat) (elems : EncM Unit) : EncM Unit := do
  emit .boundary
  match ← memoLookup o with
  | some i => wr (← liftPy (pyGet proto i))
  | none => pyTupleWith proto o n elems

/-- `save_reduce(func, args, obj=obj)` (`Lib/pickle.py:652-797`) for these
callables (none is named `__newobj__`/`__newobj_ex__`; no state or items):
`save(func)`, `save(args)`, `REDUCE`, then memoize `obj`, or `POP` + get if
saving the arguments memoized it. -/
def pyReduceWith (proto : Nat) (o : Oid) (g : Glob) (args : EncM Unit) : EncM Unit := do
  pySaveGlobal proto g
  args
  wr [oREDUCE]
  match ← memoLookup o with
  | some i => wr (oPOP :: (← liftPy (pyGet proto i)))
  | none => pyMemoize proto o

/-- `save(b)` for `bytes` (`save_bytes`, `Lib/pickle.py:874-884`). -/
def pySaveBytesObj (proto : Nat) (o : Oid) (b : Bytes) : EncM Unit := do
  emit .boundary
  match ← memoLookup o with
  | some i => wr (← liftPy (pyGet proto i))
  | none =>
    if proto < 3 then
      if b = [] then pyReduceWith proto o .bytes (pyTupleObj proto (.tmp o 0) 0 (pure ()))
      else pyReduceWith proto o .codecsEncode <|
        (pyTupleObj proto (.tmp o 0) 2 do
          pySaveStrObj proto (latin1StrOid o b) (b.map (·.toNat))
          pySaveStrObj proto .latin1 ((ascii "latin1").map (·.toNat)))
    else
      pySaveBytesData proto b
      pyMemoize proto o

/-- `save(ba)` for `bytearray` (`save_bytearray`, `Lib/pickle.py:896-906`). -/
def pySaveBytearrayObj (proto : Nat) (o : Oid) (b : Bytes) : EncM Unit := do
  emit .boundary
  match ← memoLookup o with
  | some i => wr (← liftPy (pyGet proto i))
  | none =>
    if proto < 5 then
      if b = [] then pyReduceWith proto o .bytearray (pyTupleObj proto (.tmp o 0) 0 (pure ()))
      else pyReduceWith proto o .bytearray <|
        (pyTupleObj proto (.tmp o 0) 1 (pySaveBytesObj proto (bytesCopyOid o b) b))
    else
      pySaveBytearrayData b
      pyMemoize proto o

/-- `save_list` header and memo (`Lib/pickle.py:1018-1026`), then the items. -/
def pyListWith (proto : Nat) (o : Oid) (items : EncM Unit) : EncM Unit := do
  pyEmptyOp proto oEMPTY_LIST oLIST
  pyMemoize proto o
  items

mutual
/-- `_Pickler.save` (`Lib/pickle.py:562-634`) for plain data. -/
def pySave (proto : Nat) : PV → EncM Unit
  | .none => do emit .boundary; wr [oNONE]
  | .bool b => do
    emit .boundary
    -- save_bool, Lib/pickle.py:815-820
    if proto ≥ 2 then wr [if b then oNEWTRUE else oNEWFALSE]
    else wr [oINT, 0x30, if b then 0x31 else 0x30, nl]
  | .int i => do emit .boundary; wr (← liftPy (pySaveLong proto i))
  | .str o s => pySaveStrObj proto o s
  | .bytes o b => pySaveBytesObj proto o b
  | .bytearray o b => pySaveBytearrayObj proto o b
  | .tuple o xs => pyTupleObj proto o xs.length (pySaveElems proto xs)
  | .list o xs => do
    emit .boundary
    match ← memoLookup o with
    | some i => wr (← liftPy (pyGet proto i))
    | none => pyListWith proto o (pyAppends proto xs.length 0 xs)
  | .dict o kvs => do
    emit .boundary
    match ← memoLookup o with
    | some i => wr (← liftPy (pyGet proto i))
    | none =>
      -- save_dict, Lib/pickle.py:1067-1074
      pyEmptyOp proto oEMPTY_DICT oDICT
      pyMemoize proto o
      pySetitems proto kvs.length 0 kvs
  | .set o xs => do
    emit .boundary
    match ← memoLookup o with
    | some i => wr (← liftPy (pyGet proto i))
    | none =>
      -- save_set, Lib/pickle.py:1115-1135
      if proto < 4 then
        pyReduceWith proto o .set
          (pyTupleObj proto (.tmp o 0) 1 do
            emit .boundary
            pyListWith proto (.tmp o 1) (pyAppends proto xs.length 0 xs))
      else
        wr [oEMPTY_SET]
        pyMemoize proto o
        pyAdditems proto xs.length 0 xs
  | .frozenset o xs => do
    emit .boundary
    match ← memoLookup o with
    | some i => wr (← liftPy (pyGet proto i))
    | none =>
      -- save_frozenset, Lib/pickle.py:1137-1162
      if proto < 4 then
        pyReduceWith proto o .frozenset
          (pyTupleObj proto (.tmp o 0) 1 do
            emit .boundary
            pyListWith proto (.tmp o 1) (pyAppends proto xs.length 0 xs))
      else
        wr [oMARK]
        pySaveElems proto xs
        match ← memoLookup o with
        | some i => wr (oPOP_MARK :: (← liftPy (pyGet proto i)))
        | none =>
          wr [oFROZENSET]
          pyMemoize proto o

/-- `save` each element in order (tuple and frozenset elements). -/
def pySaveElems (proto : Nat) : List PV → EncM Unit
  | [] => pure ()
  | x :: xs => do pySave proto x; pySaveElems proto xs

/-- `_batch_appends` (`Lib/pickle.py:1031-1065`) from item `i` of `n`. -/
def pyAppends (proto : Nat) (n i : Nat) : List PV → EncM Unit
  | [] => pure ()
  | x :: xs => do
    pyBatchStep proto n i (pySave proto x) oAPPEND oAPPENDS
    pyAppends proto n (i + 1) xs

/-- `_batch_setitems` (`Lib/pickle.py:1078-1113`) from pair `i` of `n`. -/
def pySetitems (proto : Nat) (n i : Nat) : List (PV × PV) → EncM Unit
  | [] => pure ()
  | (k, v) :: kvs => do
    pyBatchStep proto n i (do pySave proto k; pySave proto v) oSETITEM oSETITEMS
    pySetitems proto n (i + 1) kvs

/-- The `ADDITEMS` batches of `save_set` (`Lib/pickle.py:1124-1133`): every
batch, even of one item, is `MARK ... ADDITEMS`. -/
def pyAdditems (proto : Nat) (n i : Nat) : List PV → EncM Unit
  | [] => pure ()
  | x :: xs => do
    addStep n i (pySave proto x)
    pyAdditems proto n (i + 1) xs
end

/-! ## C `Pickler` -/

/-- `memo_put`'s opcode (`Modules/_pickle.c:1947-1997`). -/
def cPut (proto : Nat) (idx : Nat) : Py Bytes :=
  if proto ≥ 4 then .ok [oMEMOIZE]
  else if proto = 0 then .ok (oPUT :: decDigits idx ++ [nl])
  else if idx < 256 then .ok [oBINPUT, idx.toUInt8]
  else if idx ≤ 0xffffffff then .ok (oLONG_BINPUT :: leBytes idx 4)
  else .error (picklingError "memo id too large for LONG_BINPUT")

/-- `memo_get`'s opcode (`Modules/_pickle.c:1899-1944`). -/
def cGet (proto : Nat) (i : Nat) : Py Bytes :=
  if proto = 0 then .ok (oGET :: decDigits i ++ [nl])
  else if i < 256 then .ok [oBINGET, i.toUInt8]
  else if i ≤ 0xffffffff then .ok (oLONG_BINGET :: leBytes i 4)
  else .error (picklingError "memo id too large for LONG_BINGET")

def cMemoPut (proto : Nat) (o : Oid) : EncM Unit := do
  let idx ← memoSize
  memoSet o idx
  wr (← liftPy (cPut proto idx))

/-- `raw_unicode_escape` (`Modules/_pickle.c:2847-2909`). -/
def cRawUnicodeEscape (s : List Nat) : Bytes :=
  s.flatMap fun ch =>
    if ch ≥ 0x10000 then
      [0x5c, 0x55] ++ (List.range 8).reverse.map (fun i => hexDigit (ch / 16 ^ i % 16))
    else if ch ≥ 256 ∨ ch = 0x5c ∨ ch = 0 ∨ ch = 0x0a ∨ ch = 0x0d ∨ ch = 0x1a then
      [0x5c, 0x75] ++ (List.range 4).reverse.map (fun i => hexDigit (ch / 16 ^ i % 16))
    else [ch.toUInt8]

/-- `_Pickler_write_bytes` (`Modules/_pickle.c:2553-2617`) for `dumps` (no
file `write`): payloads of at least `FRAME_SIZE_TARGET` bytes bypass the
frame. -/
def cWriteBytes (hdr data : Bytes) : EncM Unit :=
  if data.length ≥ frameSizeTarget then emit (.large hdr data)
  else do wr hdr; wr data

/-- `write_unicode_binary` (`Modules/_pickle.c:2912-2966`) on the UTF-8 data. -/
def cStrData (proto : Nat) (data : Bytes) : EncM Unit := do
  let hdr ←
    if data.length ≤ 0xff ∧ proto ≥ 4 then pure (oSHORT_BINUNICODE :: leBytes data.length 1)
    else if data.length ≤ 0xffffffff then pure (oBINUNICODE :: leBytes data.length 4)
    else if proto ≥ 4 then pure (oBINUNICODE8 :: leBytes data.length 8)
    else throw (.overflowError
      "serializing a string larger than 4 GiB requires pickle protocol 4 or higher")
  cWriteBytes hdr data

/-- `save_unicode` before the memo. -/
def cStrBody (proto : Nat) (s : List Nat) : EncM Unit :=
  if proto ≥ 1 then cStrData proto (utf8Enc s)
  else do
    wr [oUNICODE]
    wr (cRawUnicodeEscape s)
    wr [nl]

/-- `save_unicode` (`Modules/_pickle.c:2969-3004`). -/
def cSaveStr (proto : Nat) (o : Oid) (s : List Nat) : EncM Unit := do
  cStrBody proto s
  cMemoPut proto o

/-- `_save_bytes_data` (`Modules/_pickle.c:2619-2664`), protocol >= 3. -/
def cSaveBytesData (proto : Nat) (b : Bytes) : EncM Unit := do
  let hdr ←
    if b.length ≤ 0xff then pure (oSHORT_BINBYTES :: leBytes b.length 1)
    else if b.length ≤ 0xffffffff then pure (oBINBYTES :: leBytes b.length 4)
    else if proto ≥ 4 then pure (oBINBYTES8 :: leBytes b.length 8)
    else throw (.overflowError
      "serializing a bytes object larger than 4 GiB requires pickle protocol 4 or higher")
  cWriteBytes hdr b

/-- C `save()` on a `str` (`Modules/_pickle.c:4623-4671`). -/
def cSaveStrObj (proto : Nat) (o : Oid) (s : List Nat) : EncM Unit := do
  emit .boundary
  match ← memoLookup o with
  | some i => wr (← liftPy (cGet proto i))
  | none => cSaveStr proto o s

/-- What `save_global` writes before the memo. -/
def cGlobalRef (proto : Nat) (g : Glob) : EncM Unit :=
  if proto ≥ 4 then do
    cSaveStrObj proto (.tmp (.glob g) 0) ((ascii g.module).map (·.toNat))
    cSaveStrObj proto (.tmp (.glob g) 1) ((ascii g.name).map (·.toNat))
    wr [oSTACK_GLOBAL]
  else do
    wr [oGLOBAL]
    wr (ascii (globModuleOut proto g))
    wr [nl]
    wr (ascii g.name)
    wr [nl]

/-- C `save()` on a global: `save_type` / reduce to a name, then
`save_global` (`Modules/_pickle.c:3937-4165`). -/
def cSaveGlobal (proto : Nat) (g : Glob) : EncM Unit := do
  emit .boundary
  match ← memoLookup (.glob g) with
  | some i => wr (← liftPy (cGet proto i))
  | none =>
    cGlobalRef proto g
    cMemoPut proto (.glob g)

/-- Write `POP` `n` times, one `_Pickler_Write` each. -/
def cPops : Nat → EncM Unit
  | 0 => pure ()
  | n + 1 => do wr [oPOP]; cPops n

/-- Drop what a recursive tuple pushed: `POP_MARK`, or `POP`s at protocol 0. -/
def cPopMark (proto n : Nat) : EncM Unit :=
  if proto ≠ 0 then wr [oPOP_MARK] else cPops (n + 1)

/-- `save_tuple` (`Modules/_pickle.c:3035-3133`). -/
def cTupleWith (proto : Nat) (o : Oid) (n : Nat) (elems : EncM Unit) : EncM Unit := do
  if n = 0 then
    if proto ≠ 0 then wr [oEMPTY_TUPLE] else wr [oMARK, oTUPLE]
  else if n ≤ 3 ∧ proto ≥ 2 then
    elems
    match ← memoLookup o with
    | some i =>
      cPops n
      wr (← liftPy (cGet proto i))
    | none =>
      wr [if n = 1 then oTUPLE1 else if n = 2 then oTUPLE2 else oTUPLE3]
      cMemoPut proto o
  else
    wr [oMARK]
    elems
    match ← memoLookup o with
    | some i =>
      cPopMark proto n
      wr (← liftPy (cGet proto i))
    | none =>
      wr [oTUPLE]
      cMemoPut proto o

def cTupleObj (proto : Nat) (o : Oid) (n : Nat) (elems : EncM Unit) : EncM Unit := do
  emit .boundary
  match ← memoLookup o with
  | some i => wr (← liftPy (cGet proto i))
  | none => cTupleWith proto o n elems

/-- `save_reduce` (`Modules/_pickle.c:4270-4621`), general branch: save the
callable and the argument tuple, `REDUCE`, then memoize `obj`. -/
def cReduceWith (proto : Nat) (o : Oid) (g : Glob) (args : EncM Unit) : EncM Unit := do
  cSaveGlobal proto g
  args
  wr [oREDUCE]
  match ← memoLookup o with
  | some i =>
    wr [oPOP]
    wr (← liftPy (cGet proto i))
  | none => cMemoPut proto o

/-- `save_bytes` (`Modules/_pickle.c:2667-2713`). -/
def cSaveBytesObj (proto : Nat) (o : Oid) (b : Bytes) : EncM Unit := do
  emit .boundary
  match ← memoLookup o with
  | some i => wr (← liftPy (cGet proto i))
  | none =>
    if proto < 3 then
      if b.length = 0 then cReduceWith proto o .bytes (cTupleObj proto (.tmp o 0) 0 (pure ()))
      else cReduceWith proto o .codecsEncode <|
        (cTupleObj proto (.tmp o 0) 2 do
          cSaveStrObj proto (latin1StrOid o b) (b.map (·.toNat))
          cSaveStrObj proto .latin1 ((ascii "latin1").map (·.toNat)))
    else
      cSaveBytesData proto b
      cMemoPut proto o

/-- `save_bytearray` (`Modules/_pickle.c:2743-2777`, `_save_bytearray_data`
at :2716-2741). -/
def cSaveBytearrayObj (proto : Nat) (o : Oid) (b : Bytes) : EncM Unit := do
  emit .boundary
  match ← memoLookup o with
  | some i => wr (← liftPy (cGet proto i))
  | none =>
    if proto < 5 then
      if b.length = 0 then cReduceWith proto o .bytearray (cTupleObj proto (.tmp o 0) 0 (pure ()))
      else cReduceWith proto o .bytearray <|
        (cTupleObj proto (.tmp o 0) 1 (cSaveBytesObj proto (bytesCopyOid o b) b))
    else
      cWriteBytes (oBYTEARRAY8 :: leBytes b.length 8) b
      cMemoPut proto o

def cEmptyOp (proto : Nat) (empty op : UInt8) : EncM Unit :=
  if proto ≠ 0 then wr [empty] else wr [oMARK, op]

/-- One item of `batch_list`/`batch_dict` at protocol 0 and of
`batch_list_exact`/`batch_dict_exact_impl`, unrolled: a one-item container
writes the single-item opcode, otherwise a batch of any size is `MARK ...
many`. -/
def cBatchStep (proto n i : Nat) (item : EncM Unit) (one many : UInt8) : EncM Unit :=
  if proto = 0 then do
    item
    wr [one]
  else if n = 1 then do
    item
    wr [one]
  else do
    optWr (i % batchSize = 0) [oMARK]
    item
    optWr ((i + 1) % batchSize = 0 ∨ i + 1 = n) [many]

/-- `save_list` header and memo (`Modules/_pickle.c:3331-3360`); the items
only when the list is non-empty. -/
def cListWith (proto : Nat) (o : Oid) (n : Nat) (items : EncM Unit) : EncM Unit := do
  cEmptyOp proto oEMPTY_LIST oLIST
  cMemoPut proto o
  if n ≠ 0 then items

mutual
/-- C `save()` (`Modules/_pickle.c:4623-4841`) for plain data. -/
def cSave (proto : Nat) : PV → EncM Unit
  | .none => do emit .boundary; wr [oNONE]
  | .bool b => do
    emit .boundary
    -- save_bool, Modules/_pickle.c:2317-2335
    if proto ≥ 2 then wr [if b then oNEWTRUE else oNEWFALSE]
    else wr [oINT, 0x30, if b then 0x31 else 0x30, nl]
  | .int i => do emit .boundary; wr (← liftPy (cSaveLong proto i))
  | .str o s => cSaveStrObj proto o s
  | .bytes o b => cSaveBytesObj proto o b
  | .bytearray o b => cSaveBytearrayObj proto o b
  | .tuple o xs => cTupleObj proto o xs.length (cSaveElems proto xs)
  | .list o xs => do
    emit .boundary
    match ← memoLookup o with
    | some i => wr (← liftPy (cGet proto i))
    | none => cListWith proto o xs.length (cAppends proto xs.length 0 xs)
  | .dict o kvs => do
    emit .boundary
    match ← memoLookup o with
    | some i => wr (← liftPy (cGet proto i))
    | none =>
      -- save_dict, Modules/_pickle.c:3638-3702
      cEmptyOp proto oEMPTY_DICT oDICT
      cMemoPut proto o
      if kvs.length ≠ 0 then cSetitems proto kvs.length 0 kvs
  | .set o xs => do
    emit .boundary
    match ← memoLookup o with
    | some i => wr (← liftPy (cGet proto i))
    | none =>
      -- save_set, Modules/_pickle.c:3705-3781
      if proto < 4 then
        cReduceWith proto o .set
          (cTupleObj proto (.tmp o 0) 1 do
            emit .boundary
            cListWith proto (.tmp o 1) xs.length (cAppends proto xs.length 0 xs))
      else
        wr [oEMPTY_SET]
        cMemoPut proto o
        if xs.length ≠ 0 then cAdditems proto xs.length 0 xs
  | .frozenset o xs => do
    emit .boundary
    match ← memoLookup o with
    | some i => wr (← liftPy (cGet proto i))
    | none =>
      -- save_frozenset_impl, Modules/_pickle.c:3784-3859
      if proto < 4 then
        cReduceWith proto o .frozenset
          (cTupleObj proto (.tmp o 0) 1 do
            emit .boundary
            cListWith proto (.tmp o 1) xs.length (cAppends proto xs.length 0 xs))
      else
        wr [oMARK]
        cSaveElems proto xs
        match ← memoLookup o with
        | some i =>
          wr [oPOP_MARK]
          wr (← liftPy (cGet proto i))
        | none =>
          wr [oFROZENSET]
          cMemoPut proto o

def cSaveElems (proto : Nat) : List PV → EncM Unit
  | [] => pure ()
  | x :: xs => do cSave proto x; cSaveElems proto xs

/-- `batch_list` for protocol 0 (`Modules/_pickle.c:3154-3173`) and
`batch_list_exact` (`:3263-3328`): a one-item list is `item APPEND`;
otherwise `do { MARK, up to 1000 items, APPENDS } while (total < size)`. -/
def cAppends (proto : Nat) (n i : Nat) : List PV → EncM Unit
  | [] => pure ()
  | x :: xs => do
    cBatchStep proto n i (cSave proto x) oAPPEND oAPPENDS
    cAppends proto n (i + 1) xs

/-- `batch_dict` for protocol 0 (`Modules/_pickle.c:3416-3448`) and
`batch_dict_exact_impl` (`:3552-3625`): a one-item dict is `k v SETITEM`;
otherwise `do { MARK, up to 1000 pairs, SETITEMS } while (i == BATCHSIZE)`,
so a size that is a multiple of 1000 ends with an empty `MARK SETITEMS`. -/
def cSetitems (proto : Nat) (n i : Nat) : List (PV × PV) → EncM Unit
  | [] => if proto ≠ 0 ∧ n ≠ 1 ∧ n % batchSize = 0 then wr [oMARK, oSETITEMS] else pure ()
  | (k, v) :: kvs => do
    cBatchStep proto n i (do cSave proto k; cSave proto v) oSETITEM oSETITEMS
    cSetitems proto n (i + 1) kvs

/-- The batch loop of `save_set` (`Modules/_pickle.c@3.14.7:3640-3676`):
`do { MARK, up to 1000 items, ADDITEMS } while (i == BATCHSIZE)`. -/
def cAdditems (proto : Nat) (n i : Nat) : List PV → EncM Unit
  | [] => if n % batchSize = 0 then wr [oMARK, oADDITEMS] else pure ()
  | x :: xs => do
    addStep n i (cSave proto x)
    cAdditems proto n (i + 1) xs
end

/-! ## Framers -/

/-- Python's `_Framer` state: bytes written to the file, and the current frame
(`None` when not framing). -/
structure PyFramer where
  out : Bytes := []
  cur : Option Bytes := none

/-- `commit_frame(force=True)` (`Lib/pickle.py:214-236`). -/
def pyCommit (out f : Bytes) : Bytes :=
  out ++ ((if f.length ≥ frameSizeMin then oFRAME :: leBytes f.length 8 else []) ++ f)

def PyFramer.step (st : PyFramer) : Event → PyFramer
  | .start => { st with cur := some [] }
  | .w d => match st.cur with
    | some f => { st with cur := some (f ++ d) }
    | none => { st with out := st.out ++ d }
  | .boundary => match st.cur with
    | some f => if f.length ≥ frameSizeTarget then { out := pyCommit st.out f, cur := some [] } else st
    | none => st
  | .large hdr payload => match st.cur with
    | some f => { out := pyCommit st.out f ++ (hdr ++ payload), cur := some [] }
    | none => { st with out := st.out ++ (hdr ++ payload) }
  | .finish => match st.cur with
    | some f => if f.length > 0 then { out := pyCommit st.out f, cur := none } else st
    | none => st

def pyFrame (evs : List Event) : Bytes := (evs.foldl PyFramer.step {}).out

/-- C pickler output state (`Modules/_pickle.c:969-1130`): the output buffer,
`frame_start` (`none` for -1) and `framing`. A new frame reserves a 9-byte
header (filled with 0xFE) that `_Pickler_CommitFrame` fills in or removes. -/
structure CFramer where
  buf : Bytes := []
  frameStart : Option Nat := none
  framing : Bool := false

def frameHeaderSize : Nat := 9

/-- `_Pickler_CommitFrame` (`Modules/_pickle.c:996-1015`). -/
def CFramer.commit (st : CFramer) : CFramer :=
  match st.framing, st.frameStart with
  | true, some fs =>
    let frameLen := st.buf.length - fs - frameHeaderSize
    if frameLen ≥ frameSizeMin then
      { st with buf := st.buf.take fs ++ (oFRAME :: leBytes frameLen 8) ++ st.buf.drop (fs + frameHeaderSize),
                frameStart := none }
    else { st with buf := st.buf.take fs ++ st.buf.drop (fs + frameHeaderSize), frameStart := none }
  | _, _ => st

/-- `_Pickler_Write` (`Modules/_pickle.c:1084-1130`). -/
def CFramer.write (st : CFramer) (d : Bytes) : CFramer :=
  if st.framing ∧ st.frameStart = none then
    { st with frameStart := some st.buf.length,
              buf := st.buf ++ List.replicate frameHeaderSize 0xfe ++ d }
  else { st with buf := st.buf ++ d }

def CFramer.step (st : CFramer) : Event → CFramer
  | .start => { st with framing := true }
  | .w d => st.write d
  | .boundary =>
    -- _Pickler_OpcodeBoundary, Modules/_pickle.c:1052-1081
    match st.framing, st.frameStart with
    | true, some fs => if st.buf.length - fs - frameHeaderSize ≥ frameSizeTarget then st.commit else st
    | _, _ => st
  | .large hdr payload =>
    let framing := st.framing
    let st := st.commit
    let st := ({ st with framing := false } : CFramer).write hdr |>.write payload
    { st with framing := framing }
  | .finish => { st.commit with framing := false }

def cFrame (evs : List Event) : Bytes := (evs.foldl CFramer.step {}).buf

/-- `_Pickler_SetProtocol` (`Modules/_pickle.c:1183-1209`): `PyLong_AsLong`
raises `OverflowError` outside the C `long` range. -/
def cProtocol (protocol : Int) : Py Nat :=
  if protocol < longMin ∨ protocol > longMax then
    .error (.overflowError "Python int too large to convert to C long")
  else if protocol < 0 then .ok 5
  else if protocol > 5 then .error (.valueError "pickle protocol must be <= 5")
  else .ok protocol.toNat

/-- The `protocol` argument of `_Pickler.__init__` (`Lib/pickle.py:471-476`). -/
def pyProtocol (protocol : Int) : Py Nat :=
  if protocol < 0 then .ok 5
  else if protocol ≤ 5 then .ok protocol.toNat
  else .error (.valueError "pickle protocol must be <= 5")

/-- `_Pickler.dump` (`Lib/pickle.py:503-516`). -/
def pyBody (proto : Nat) (x : PV) : EncM Unit := do
  if proto ≥ 2 then wr [oPROTO, proto.toUInt8]
  if proto ≥ 4 then emit .start
  pySave proto x
  wr [oSTOP]
  emit .finish

/-- `pickle._dumps(obj, protocol)` (`Lib/pickle.py:1896-1902`). -/
def pyDumps (x : PV) (protocol : Int) : Py Bytes := do
  let proto ← pyProtocol protocol
  let (_, st) ← (pyBody proto x).run {}
  return pyFrame st.ev.reverse

/-- `dump` (`Modules/_pickle.c:4869-4931`). -/
def cBody (proto : Nat) (x : PV) : EncM Unit := do
  if proto ≥ 2 then wr [oPROTO, proto.toUInt8]
  if proto ≥ 4 then emit .start
  cSave proto x
  wr [oSTOP]
  emit .finish

/-- `pickle.dumps(obj, protocol)` (`_pickle_dumps_impl`, `Modules/_pickle.c:8122-8158`). -/
def cDumps (x : PV) (protocol : Int) : Py Bytes := do
  let proto ← cProtocol protocol
  let (_, st) ← (cBody proto x).run {}
  return cFrame st.ev.reverse

end PyLean.Pickle
