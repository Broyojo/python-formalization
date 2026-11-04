import PyLean.Pickle.Enc
import PyLean.Binary64.Model

/-!
The two picklers of `Enc.lean` with their recursion limits and their `protocol` and
`buffer_callback` arguments: these are the mirrors `pickle.dumps` and `pickle._dumps` are
modelled by (`cDumpsA`, `pyDumpsA`). `Enc.lean` is the same code with frames free and an int
protocol; `EncRecProps.lean` proves that each function here either computes what its frames-free
twin computes or raises its `RecursionError`.

**C.** `_Py_EnterRecursiveCall(" while pickling an object")` in `save` before the containers,
`bytearray`, globals and the reduce path (`Modules/_pickle.c:4683`, after the atoms, the memo and
`bytes`/`str` at :4655-4679), and again around the batch loops of a non-empty list (:3364, :3373)
and dict (:3671, :3683). In 3.15 the check is on the machine stack pointer (`_Py_MakeRecCheck`,
Include/internal/pycore_ceval.h:211-241), so `c` is the stack room in levels: every guard on the
current path takes one (a scope limit: real frames differ in size). It fails with
`_Py_CheckRecursiveCall`'s `RecursionError("Stack overflow (used %d kB) while pickling an
object")` (Python/ceval.c).

**Python.** Every call of a Python function pushes a frame; `b` is the number of frames left in
the calling frame, and a call with none left raises `RecursionError` (`_Py_EnterRecursivePy`,
Python/ceval.c). The frames: `_dumps`, `_Pickler.__init__`, `_Framer.__init__`, `dump`, `save`,
`framer.commit_frame`, `persistent_id`, the `save_*` methods, `save_reduce`, `save_type`,
`save_global`, `whichmodule`, `_getattribute`, `_save_toplevel_by_name`, `_save_bytes_no_memo`,
`_save_bytearray_no_memo`, `memoize`, `put`, `get`, `encode_long`, `_batch_appends`,
`_batch_setitems`, `start_framing`, `end_framing`, `write` (`_Framer.write`) and
`write_large_bytes`, which calls `commit_frame` while framing. Everything else they call is C
(`io.BytesIO`, `struct.pack`, `batched`, `str.replace`, `getattr`, `__import__` of an imported
module, `__reduce_ex__` of a builtin). An exception passing a `try` gets a note from
`_T(obj)`, another frame; the result is an exception either way, which is all the model keeps.

**Arguments.** `protocol` is `None`, an int (or bool), a float, or an object of another type
that defines neither `__index__` nor comparisons with int (a scope limit). `buffer_callback` is
`None` or not; it is never called on plain data. `fix_imports` is True (a scope limit:
`fix_imports=False` changes the module name below protocol 3, which `Enc.lean` does not take).
-/

namespace PyLean.Pickle

open PyLean PyLean.Binary64

/-! ## Limits -/

def recPy : PyExc := .named "RecursionError" "maximum recursion depth exceeded"
def recC : PyExc := .named "RecursionError" "~Stack overflow (used N kB) while pickling an object"

/-- A call of a Python function from a frame with `b` frames left: `RecursionError` when there
is none, else the callee runs with `b - 1`. -/
def pyCall {α : Type} (b : Nat) (k : Nat → EncM α) : EncM α :=
  if b = 0 then throw recPy else k (b - 1)

/-- `_Py_EnterRecursiveCall` with room `c`. -/
def cEnter (c : Nat) (k : Nat → EncM Unit) : EncM Unit :=
  if c = 0 then throw recC else k (c - 1)

/-! ## Python `_Pickler`, with frames -/

/-- `self.write(d)`: `_Framer.write` (`Lib/pickle.py:238-242`) writes to the BytesIO frame or
the file in C. -/
def pyW (b : Nat) (d : Bytes) : EncM Unit := pyCall b fun _ => wr d

/-- `self.framer.commit_frame()` (`Lib/pickle.py:214-236`). -/
def pyCommitR (b : Nat) : EncM Unit := pyCall b fun _ => emit .boundary

/-- `self.persistent_id(obj)` (`Lib/pickle.py:636-638`), which returns `None`. -/
def pyPersR (b : Nat) : EncM Unit := pyCall b fun _ => pure ()

/-- `self._write_large_bytes(header, payload)` (`Lib/pickle.py:244-257`): while framing
(protocol 4 and up, where `current_frame` is a BytesIO from `start_framing` to `end_framing`)
it calls `commit_frame(force=True)`. -/
def pyLargeR (b p : Nat) (hdr payload : Bytes) : EncM Unit :=
  pyCall b fun b' => if p ≥ 4 then pyCall b' (fun _ => emit (.large hdr payload)) else emit (.large hdr payload)

/-- `self.put(idx)` (`Lib/pickle.py:541-550`). -/
def pyPutR (b p idx : Nat) : EncM Bytes := pyCall b fun _ => liftPy (pyPut p idx)

/-- `self.get(i)` (`Lib/pickle.py:553-560`). -/
def pyGetR (b p i : Nat) : EncM Bytes := pyCall b fun _ => liftPy (pyGet p i)

/-- `self.memoize(obj)` (`Lib/pickle.py:518-538`; `self.fast` is 0 in `_dumps`). -/
def pyMemoizeR (b p : Nat) (o : Oid) : EncM Unit := pyCall b fun b' => do
  let idx ← memoSize
  pyW b' (← pyPutR b' p idx)
  memoSet o idx

def optWrR (b : Nat) (c : Prop) [Decidable c] (d : Bytes) : EncM Unit := if c then pyW b d else pure ()

def pyEmptyOpR (b p : Nat) (empty op : UInt8) : EncM Unit :=
  if p ≥ 1 then pyW b [empty] else pyW b [oMARK, op]

/-- One item of `_batch_appends`/`_batch_setitems` (`Lib/pickle.py:1031-1113`), in their frame. -/
def pyBatchStepR (b p n i : Nat) (item : EncM Unit) (one many : UInt8) : EncM Unit :=
  if p = 0 then do
    item
    pyW b [one]
  else do
    optWrR b (i % batchSize = 0 ∧ batchLen n i ≠ 1) [oMARK]
    item
    optWrR b ((i + 1) % batchSize = 0 ∨ i + 1 = n) [if batchLen n i ≠ 1 then many else one]

/-- One item of `save_set`'s batches (`Lib/pickle.py:1124-1133`), in its frame. -/
def addStepR (b n i : Nat) (item : EncM Unit) : EncM Unit := do
  optWrR b (i % batchSize = 0) [oMARK]
  item
  optWrR b ((i + 1) % batchSize = 0 ∨ i + 1 = n) [oADDITEMS]

/-- `save_long` (`Lib/pickle.py:822-852`) in its frame: `encode_long` is a Python call at
protocol 2 and up outside the 4-byte range; `repr` and `pack` are C. -/
def pySaveLongR (b p : Nat) (i : Int) : EncM Unit := do
  if p ≥ 2 ∧ ¬ (-0x80000000 ≤ i ∧ i ≤ 0x7fffffff) then pyCall b fun _ => pure ()
  pyW b (← liftPy (pySaveLong p i))

/-- The binary branch of `save_str` (`Lib/pickle.py:938-948`). -/
def pyStrDataR (b p : Nat) (data : Bytes) : EncM Unit :=
  let n := data.length
  if n ≤ 0xff ∧ p ≥ 4 then pyW b (oSHORT_BINUNICODE :: leBytes n 1 ++ data)
  else if n > 0xffffffff ∧ p ≥ 4 then pyLargeR b p (oBINUNICODE8 :: leBytes n 8) data
  else if n ≥ frameSizeTarget then
    (liftPy (packU32 n) >>= fun x => pyLargeR b p (oBINUNICODE :: x) data)
  else (liftPy (packU32 n) >>= fun x => pyW b (oBINUNICODE :: x ++ data))

def pyStrBodyR (b p : Nat) (s : List Nat) : EncM Unit :=
  if p ≥ 1 then pyStrDataR b p (utf8Enc s)
  else pyW b (oUNICODE :: rueEncode (pyStrEscape s) ++ [nl])

/-- `save_str` (`Lib/pickle.py:936-957`) in its frame. -/
def pySaveStrR (b p : Nat) (o : Oid) (s : List Nat) : EncM Unit := do
  pyStrBodyR b p s
  pyMemoizeR b p o

/-- The start of `save(obj)` (`Lib/pickle.py:562-576`) in its frame: `commit_frame`,
`persistent_id`, then the memo; `body` is the dispatch for a memo miss. -/
def pySaveHead (b p : Nat) (o : Oid) (body : EncM Unit) : EncM Unit := do
  pyCommitR b
  pyPersR b
  match ← memoLookup o with
  | some i => pyW b (← pyGetR b p i)
  | none => body

/-- `self.save(s)` for a `str`, from a frame with `b` frames left. -/
def pySaveStrObjR (b p : Nat) (o : Oid) (s : List Nat) : EncM Unit :=
  pyCall b fun b1 => pySaveHead b1 p o (pyCall b1 fun b2 => pySaveStrR b2 p o s)

/-- `save_global` (`Lib/pickle.py:1164-1227`) in its frame: `whichmodule` (which calls
`_getattribute`), then `STACK_GLOBAL` with two `save`s, or `_save_toplevel_by_name`
(:1229-1252), then `memoize`. -/
def pySaveGlobalBodyR (b p : Nat) (g : Glob) : EncM Unit := do
  pyCall b (fun b' => pyCall b' fun _ => pure ())
  if p ≥ 4 then do
    pySaveStrObjR b p (.tmp (.glob g) 0) ((ascii g.module).map (·.toNat))
    pySaveStrObjR b p (.tmp (.glob g) 1) ((ascii g.name).map (·.toNat))
    pyW b [oSTACK_GLOBAL]
  else
    pyCall b fun b' => do
      pyW b' (oGLOBAL :: ascii (globModuleOut p g) ++ [nl])
      pyW b' (ascii g.name ++ [nl])
  pyMemoizeR b p (.glob g)

/-- `self.save(func)` for one of the globals: a type goes through `save_type` (:1254-1261) to
`save_global`; `codecs.encode` through its C `__reduce_ex__`, whose result `'encode'` is passed
to `save_global(obj, rv)` (:606-608). -/
def pySaveGlobalR (b p : Nat) (g : Glob) : EncM Unit :=
  pyCall b fun b1 => pySaveHead b1 p (.glob g) <|
    if g = .codecsEncode then pyCall b1 fun b2 => pySaveGlobalBodyR b2 p g
    else pyCall b1 fun b2 => pyCall b2 fun b3 => pySaveGlobalBodyR b3 p g

/-- `save_tuple` (`Lib/pickle.py:959-1016`) in its frame; `elems` saves the elements from it. -/
def pyTupleWithR (b p : Nat) (o : Oid) (n : Nat) (elems : EncM Unit) : EncM Unit := do
  if n = 0 then
    if p ≥ 1 then pyW b [oEMPTY_TUPLE] else pyW b [oMARK, oTUPLE]
  else if n ≤ 3 ∧ p ≥ 2 then
    elems
    match ← memoLookup o with
    | some i => pyW b (List.replicate n oPOP ++ (← pyGetR b p i))
    | none =>
      pyW b [if n = 1 then oTUPLE1 else if n = 2 then oTUPLE2 else oTUPLE3]
      pyMemoizeR b p o
  else
    pyW b [oMARK]
    elems
    match ← memoLookup o with
    | some i =>
      if p ≥ 1 then pyW b (oPOP_MARK :: (← pyGetR b p i))
      else pyW b (List.replicate (n + 1) oPOP ++ (← pyGetR b p i))
    | none =>
      pyW b [oTUPLE]
      pyMemoizeR b p o

/-- `self.save(t)` for a tuple; `elems b` saves the elements from `save_tuple`'s frame. -/
def pyTupleObjR (b p : Nat) (o : Oid) (n : Nat) (elems : Nat → EncM Unit) : EncM Unit :=
  pyCall b fun b1 => pySaveHead b1 p o (pyCall b1 fun b2 => pyTupleWithR b2 p o n (elems b2))

/-- `self.save_reduce(func, args, obj=obj)` (`Lib/pickle.py:652-797`) for the five globals;
`args b` saves the argument tuple from `save_reduce`'s frame. -/
def pyReduceWithR (b p : Nat) (o : Oid) (g : Glob) (args : Nat → EncM Unit) : EncM Unit :=
  pyCall b fun b1 => do
    pySaveGlobalR b1 p g
    args b1
    pyW b1 [oREDUCE]
    match ← memoLookup o with
    | some i => pyW b1 (oPOP :: (← pyGetR b1 p i))
    | none => pyMemoizeR b1 p o

/-- `_save_bytes_no_memo` (`Lib/pickle.py:860-872`) in its frame. -/
def pySaveBytesDataR (b p : Nat) (bs : Bytes) : EncM Unit := do
  let n := bs.length
  if n ≤ 0xff then pyW b (oSHORT_BINBYTES :: leBytes n 1 ++ bs)
  else if n > 0xffffffff ∧ p ≥ 4 then pyLargeR b p (oBINBYTES8 :: leBytes n 8) bs
  else if n ≥ frameSizeTarget then
    (liftPy (packU32 n) >>= fun x => pyLargeR b p (oBINBYTES :: x) bs)
  else (liftPy (packU32 n) >>= fun x => pyW b (oBINBYTES :: x ++ bs))

/-- `_save_bytearray_no_memo` (`Lib/pickle.py:886-894`) in its frame. -/
def pySaveBytearrayDataR (b p : Nat) (bs : Bytes) : EncM Unit := do
  let n := bs.length
  if n ≥ frameSizeTarget then pyLargeR b p (oBYTEARRAY8 :: leBytes n 8) bs
  else pyW b (oBYTEARRAY8 :: leBytes n 8 ++ bs)

/-- `self.save(b)` for `bytes`: `save_bytes` (`Lib/pickle.py:874-884`). -/
def pySaveBytesObjR (b p : Nat) (o : Oid) (bs : Bytes) : EncM Unit :=
  pyCall b fun b1 => pySaveHead b1 p o <| pyCall b1 fun b2 =>
    if p < 3 then
      if bs = [] then pyReduceWithR b2 p o .bytes (fun b3 => pyTupleObjR b3 p (.tmp o 0) 0 (fun _ => pure ()))
      else pyReduceWithR b2 p o .codecsEncode fun b3 =>
        pyTupleObjR b3 p (.tmp o 0) 2 fun b4 => do
          pySaveStrObjR b4 p (latin1StrOid o bs) (bs.map (·.toNat))
          pySaveStrObjR b4 p .latin1 ((ascii "latin1").map (·.toNat))
    else do
      pyCall b2 fun b3 => pySaveBytesDataR b3 p bs
      pyMemoizeR b2 p o

/-- `self.save(ba)` for `bytearray`: `save_bytearray` (`Lib/pickle.py:896-906`). -/
def pySaveBytearrayObjR (b p : Nat) (o : Oid) (bs : Bytes) : EncM Unit :=
  pyCall b fun b1 => pySaveHead b1 p o <| pyCall b1 fun b2 =>
    if p < 5 then
      if bs = [] then pyReduceWithR b2 p o .bytearray (fun b3 => pyTupleObjR b3 p (.tmp o 0) 0 (fun _ => pure ()))
      else pyReduceWithR b2 p o .bytearray fun b3 =>
        pyTupleObjR b3 p (.tmp o 0) 1 fun b4 => pySaveBytesObjR b4 p (bytesCopyOid o bs) bs
    else do
      pyCall b2 fun b3 => pySaveBytearrayDataR b3 p bs
      pyMemoizeR b2 p o

/-- `save_list` (`Lib/pickle.py:1018-1026`) in its frame; `items b` is `_batch_appends` running
in its own frame with `b` left. -/
def pyListWithR (b p : Nat) (o : Oid) (items : Nat → EncM Unit) : EncM Unit := do
  pyEmptyOpR b p oEMPTY_LIST oLIST
  pyMemoizeR b p o
  pyCall b items

/-- The fresh `list(obj)` that `save_set`/`save_frozenset` pass to `save_reduce` below
protocol 4, saved from the argument tuple's `save_tuple` frame; its memo lookup cannot hit. -/
def pyTmpListR (b p : Nat) (o : Oid) (xs : List PV) (appends : Nat → EncM Unit) : EncM Unit :=
  pyCall b fun b1 => do
    pyCommitR b1
    pyPersR b1
    pyCall b1 fun b2 => pyListWithR b2 p o appends

mutual
/-- `self.save(x)` (`Lib/pickle.py:562-634`) for plain data, from a frame with `b` left. -/
def pySaveR (b p : Nat) : PV → EncM Unit
  | .none => pyCall b fun b1 => do
    pyCommitR b1
    pyPersR b1
    pyCall b1 fun b2 => pyW b2 [oNONE]
  | .bool v => pyCall b fun b1 => do
    pyCommitR b1
    pyPersR b1
    -- save_bool, Lib/pickle.py:815-820
    pyCall b1 fun b2 =>
      if p ≥ 2 then pyW b2 [if v then oNEWTRUE else oNEWFALSE]
      else pyW b2 [oINT, 0x30, if v then 0x31 else 0x30, nl]
  | .int i => pyCall b fun b1 => do
    pyCommitR b1
    pyPersR b1
    pyCall b1 fun b2 => pySaveLongR b2 p i
  | .str o s => pySaveStrObjR b p o s
  | .bytes o bs => pySaveBytesObjR b p o bs
  | .bytearray o bs => pySaveBytearrayObjR b p o bs
  | .tuple o xs => pyTupleObjR b p o xs.length (fun b' => pySaveElemsR b' p xs)
  | .list o xs => pyCall b fun b1 => pySaveHead b1 p o <|
    pyCall b1 fun b2 => pyListWithR b2 p o (fun b3 => pyAppendsR b3 p xs.length 0 xs)
  | .dict o kvs => pyCall b fun b1 => pySaveHead b1 p o <|
    -- save_dict, Lib/pickle.py:1067-1074
    pyCall b1 fun b2 => do
      pyEmptyOpR b2 p oEMPTY_DICT oDICT
      pyMemoizeR b2 p o
      pyCall b2 fun b3 => pySetitemsR b3 p kvs.length 0 kvs
  | .set o xs => pyCall b fun b1 => pySaveHead b1 p o <|
    -- save_set, Lib/pickle.py:1115-1135
    pyCall b1 fun b2 =>
      if p < 4 then
        pyReduceWithR b2 p o .set fun b3 =>
          pyTupleObjR b3 p (.tmp o 0) 1 fun b4 =>
            pyTmpListR b4 p (.tmp o 1) xs (fun b5 => pyAppendsR b5 p xs.length 0 xs)
      else do
        pyW b2 [oEMPTY_SET]
        pyMemoizeR b2 p o
        pyAdditemsR b2 p xs.length 0 xs
  | .frozenset o xs => pyCall b fun b1 => pySaveHead b1 p o <|
    -- save_frozenset, Lib/pickle.py:1137-1162
    pyCall b1 fun b2 =>
      if p < 4 then
        pyReduceWithR b2 p o .frozenset fun b3 =>
          pyTupleObjR b3 p (.tmp o 0) 1 fun b4 =>
            pyTmpListR b4 p (.tmp o 1) xs (fun b5 => pyAppendsR b5 p xs.length 0 xs)
      else do
        pyW b2 [oMARK]
        pySaveElemsR b2 p xs
        match ← memoLookup o with
        | some i => pyW b2 (oPOP_MARK :: (← pyGetR b2 p i))
        | none =>
          pyW b2 [oFROZENSET]
          pyMemoizeR b2 p o

/-- `save(element)` for each element, from the caller's frame. -/
def pySaveElemsR (b p : Nat) : List PV → EncM Unit
  | [] => pure ()
  | x :: xs => do pySaveR b p x; pySaveElemsR b p xs

/-- `_batch_appends` (`Lib/pickle.py:1031-1065`) in its frame, from item `i` of `n`. -/
def pyAppendsR (b p n i : Nat) : List PV → EncM Unit
  | [] => pure ()
  | x :: xs => do
    pyBatchStepR b p n i (pySaveR b p x) oAPPEND oAPPENDS
    pyAppendsR b p n (i + 1) xs

/-- `_batch_setitems` (`Lib/pickle.py:1078-1113`) in its frame, from pair `i` of `n`. -/
def pySetitemsR (b p n i : Nat) : List (PV × PV) → EncM Unit
  | [] => pure ()
  | (k, v) :: kvs => do
    pyBatchStepR b p n i (do pySaveR b p k; pySaveR b p v) oSETITEM oSETITEMS
    pySetitemsR b p n (i + 1) kvs

/-- The `ADDITEMS` batches of `save_set`, in its frame. -/
def pyAdditemsR (b p n i : Nat) : List PV → EncM Unit
  | [] => pure ()
  | x :: xs => do
    addStepR b n i (pySaveR b p x)
    pyAdditemsR b p n (i + 1) xs
end

/-- `dump` (`Lib/pickle.py:503-516`) in its frame: `end_framing` calls `commit_frame` while
framing, since the frame then holds at least `STOP`. -/
def pyBodyR (b p : Nat) (x : PV) : EncM Unit := do
  if p ≥ 2 then pyW b [oPROTO, p.toUInt8]
  if p ≥ 4 then pyCall b fun _ => emit .start
  pySaveR b p x
  pyW b [oSTOP]
  pyCall b fun b' => if p ≥ 4 then pyCall b' (fun _ => emit .finish) else emit .finish

/-! ## Arguments -/

/-- The `protocol` argument. `.int` covers bool. `.other t` is an object of type `t` with
neither `__index__` nor comparisons with int. -/
inductive ProtoArg where
  | none
  | int (i : Int)
  | float (f : F64)
  | other (tp : String)
  deriving Repr, Inhabited

structure DumpsArgs where
  protocol : ProtoArg := .none
  /-- `buffer_callback is not None`. -/
  bufcb : Bool := false
  deriving Repr, Inhabited

def bufErr : PyExc := .valueError "buffer_callback needs protocol >= 5"

/-- `_Pickler_SetProtocol` (`Modules/_pickle.c:1183-1209`): `None` is `DEFAULT_PROTOCOL`,
anything else goes through `PyLong_AsLong`, which takes only ints (and `__index__`). -/
def cProtocolA : ProtoArg → Py Nat
  | .none => .ok 5
  | .int i => cProtocol i
  | .float _ => .error (.typeError "'float' object cannot be interpreted as an integer")
  | .other t => .error (.typeError s!"'{t}' object cannot be interpreted as an integer")

/-- `_Pickler_SetBufferCallback` (`Modules/_pickle.c:1228-1241`). -/
def cBufCheck (bufcb : Bool) (p : Nat) : Py Unit :=
  if bufcb ∧ p < 5 then .error bufErr else .ok ()

/-- The checks of `_Pickler.__init__` (`Lib/pickle.py:471-478`) on `protocol` itself, then
`int(protocol)` (:487). A negative protocol is replaced by the int `HIGHEST_PROTOCOL` before the
`buffer_callback` test. -/
def pyProtocolA (a : DumpsArgs) : Py Nat :=
  match a.protocol with
  | .none => if a.bufcb ∧ 5 < 5 then .error bufErr else .ok 5
  | .int i =>
    if i < 0 then (if a.bufcb ∧ 5 < 5 then .error bufErr else .ok 5)
    else if ¬ (0 ≤ i ∧ i ≤ 5) then .error (.valueError "pickle protocol must be <= 5")
    else if a.bufcb ∧ i < 5 then .error bufErr
    else .ok i.toNat
  | .float f =>
    if f.lt (F64.ofInt 0) then (if a.bufcb ∧ 5 < 5 then .error bufErr else .ok 5)
    else if ¬ ((F64.ofInt 0).le f ∧ f.le (F64.ofInt 5)) then .error (.valueError "pickle protocol must be <= 5")
    else if a.bufcb ∧ f.lt (F64.ofInt 5) then .error bufErr
    else .ok f.truncInt.toNat
  | .other t => .error (.typeError s!"'<' not supported between instances of '{t}' and 'int'")

/-! ## Entry points -/

def liftPyA {α : Type} : Py α → EncM α
  | .ok v => pure v
  | .error e => throw e

/-- Run an encoder from the empty state and frame its calls. -/
def encRun (frame : List Event → Bytes) (m : EncM Unit) : Py Bytes := do
  let (_, st) ← m.run {}
  return frame st.ev.reverse

/-! ## C `Pickler`, with stack room -/

/-- C `save()` on a global (`Modules/_pickle.c:4623-4841`): the memo, then the guard of :4683,
then `save_type`/`save_global` or the reduce to a name (`:3937-4165`). -/
def cSaveGlobalR (c p : Nat) (g : Glob) : EncM Unit := do
  emit .boundary
  match ← memoLookup (.glob g) with
  | some i => wr (← liftPy (cGet p i))
  | none => cEnter c fun _ => do
    cGlobalRef p g
    cMemoPut p (.glob g)

/-- C `save()` on a tuple: the memo, the guard, `save_tuple` (`:3035-3133`), whose elements
`elems c` saves with the room left inside the guard. -/
def cTupleObjR (c p : Nat) (o : Oid) (n : Nat) (elems : Nat → EncM Unit) : EncM Unit := do
  emit .boundary
  match ← memoLookup o with
  | some i => wr (← liftPy (cGet p i))
  | none => cEnter c fun c' => cTupleWith p o n (elems c')

/-- `save_reduce` (`Modules/_pickle.c:4270-4621`), general branch, called without a guard of
its own: `save(callable)`, the argument tuple, `REDUCE`, the memo. -/
def cReduceWithR (c p : Nat) (o : Oid) (g : Glob) (args : EncM Unit) : EncM Unit := do
  cSaveGlobalR c p g
  args
  wr [oREDUCE]
  match ← memoLookup o with
  | some i =>
    wr [oPOP]
    wr (← liftPy (cGet p i))
  | none => cMemoPut p o

/-- `save_bytes` (`Modules/_pickle.c:2667-2713`), reached before the guard. -/
def cSaveBytesObjR (c p : Nat) (o : Oid) (b : Bytes) : EncM Unit := do
  emit .boundary
  match ← memoLookup o with
  | some i => wr (← liftPy (cGet p i))
  | none =>
    if p < 3 then
      if b.length = 0 then cReduceWithR c p o .bytes (cTupleObjR c p (.tmp o 0) 0 (fun _ => pure ()))
      else cReduceWithR c p o .codecsEncode <|
        (cTupleObjR c p (.tmp o 0) 2 fun _ => do
          cSaveStrObj p (latin1StrOid o b) (b.map (·.toNat))
          cSaveStrObj p .latin1 ((ascii "latin1").map (·.toNat)))
    else
      cSaveBytesData p b
      cMemoPut p o

/-- `save_bytearray` (`Modules/_pickle.c:2743-2777`), behind the guard. -/
def cSaveBytearrayObjR (c p : Nat) (o : Oid) (b : Bytes) : EncM Unit := do
  emit .boundary
  match ← memoLookup o with
  | some i => wr (← liftPy (cGet p i))
  | none => cEnter c fun c' =>
    if p < 5 then
      if b.length = 0 then cReduceWithR c' p o .bytearray (cTupleObjR c' p (.tmp o 0) 0 (fun _ => pure ()))
      else cReduceWithR c' p o .bytearray <|
        (cTupleObjR c' p (.tmp o 0) 1 fun c'' => cSaveBytesObjR c'' p (bytesCopyOid o b) b)
    else do
      cWriteBytes (oBYTEARRAY8 :: leBytes b.length 8) b
      cMemoPut p o

/-- The fresh `PySequence_List(obj)` of `save_set`/`save_frozenset_impl` below protocol 4,
saved from the argument tuple: `save()`'s guard, then `save_list` with its second guard. -/
def cTmpListR (c p : Nat) (o : Oid) (n : Nat) (appends : Nat → EncM Unit) : EncM Unit := do
  emit .boundary
  cEnter c fun c' => cListWith p o n (cEnter c' appends)

mutual
/-- C `save()` (`Modules/_pickle.c:4623-4841`) for plain data with room `c`: None, bool, int,
`bytes` and `str` come before the guard of :4683. -/
def cSaveR (c p : Nat) : PV → EncM Unit
  | .none => do emit .boundary; wr [oNONE]
  | .bool b => do
    emit .boundary
    if p ≥ 2 then wr [if b then oNEWTRUE else oNEWFALSE]
    else wr [oINT, 0x30, if b then 0x31 else 0x30, nl]
  | .int i => do emit .boundary; wr (← liftPy (cSaveLong p i))
  | .str o s => cSaveStrObj p o s
  | .bytes o b => cSaveBytesObjR c p o b
  | .bytearray o b => cSaveBytearrayObjR c p o b
  | .tuple o xs => cTupleObjR c p o xs.length (fun c' => cSaveElemsR c' p xs)
  | .list o xs => do
    emit .boundary
    match ← memoLookup o with
    | some i => wr (← liftPy (cGet p i))
    | none => cEnter c fun c' =>
      -- save_list, Modules/_pickle.c:3331-3390: the second guard around the batches
      cListWith p o xs.length (cEnter c' fun c'' => cAppendsR c'' p xs.length 0 xs)
  | .dict o kvs => do
    emit .boundary
    match ← memoLookup o with
    | some i => wr (← liftPy (cGet p i))
    | none => cEnter c fun c' => do
      -- save_dict, Modules/_pickle.c:3638-3702
      cEmptyOp p oEMPTY_DICT oDICT
      cMemoPut p o
      if kvs.length ≠ 0 then cEnter c' fun c'' => cSetitemsR c'' p kvs.length 0 kvs
  | .set o xs => do
    emit .boundary
    match ← memoLookup o with
    | some i => wr (← liftPy (cGet p i))
    | none => cEnter c fun c' =>
      -- save_set, Modules/_pickle.c:3705-3781
      if p < 4 then
        cReduceWithR c' p o .set <| cTupleObjR c' p (.tmp o 0) 1 fun c'' =>
            cTmpListR c'' p (.tmp o 1) xs.length (fun c3 => cAppendsR c3 p xs.length 0 xs)
      else do
        wr [oEMPTY_SET]
        cMemoPut p o
        if xs.length ≠ 0 then cAdditemsR c' p xs.length 0 xs
  | .frozenset o xs => do
    emit .boundary
    match ← memoLookup o with
    | some i => wr (← liftPy (cGet p i))
    | none => cEnter c fun c' =>
      -- save_frozenset_impl, Modules/_pickle.c:3784-3859
      if p < 4 then
        cReduceWithR c' p o .frozenset <| cTupleObjR c' p (.tmp o 0) 1 fun c'' =>
            cTmpListR c'' p (.tmp o 1) xs.length (fun c3 => cAppendsR c3 p xs.length 0 xs)
      else do
        wr [oMARK]
        cSaveElemsR c' p xs
        match ← memoLookup o with
        | some i =>
          wr [oPOP_MARK]
          wr (← liftPy (cGet p i))
        | none =>
          wr [oFROZENSET]
          cMemoPut p o

def cSaveElemsR (c p : Nat) : List PV → EncM Unit
  | [] => pure ()
  | x :: xs => do cSaveR c p x; cSaveElemsR c p xs

def cAppendsR (c p n i : Nat) : List PV → EncM Unit
  | [] => pure ()
  | x :: xs => do
    cBatchStep p n i (cSaveR c p x) oAPPEND oAPPENDS
    cAppendsR c p n (i + 1) xs

def cSetitemsR (c p n i : Nat) : List (PV × PV) → EncM Unit
  | [] => pure ()
  | (k, v) :: kvs => do
    cBatchStep p n i (do cSaveR c p k; cSaveR c p v) oSETITEM oSETITEMS
    cSetitemsR c p n (i + 1) kvs

def cAdditemsR (c p n i : Nat) : List PV → EncM Unit
  | [] => pure ()
  | x :: xs => do
    addStep n i (cSaveR c p x)
    cAdditemsR c p n (i + 1) xs
end

/-- `dump` (`Modules/_pickle.c:4869-4927`) with room `c`. -/
def cBodyR (c p : Nat) (x : PV) : EncM Unit := do
  if p ≥ 2 then wr [oPROTO, p.toUInt8]
  if p ≥ 4 then emit .start
  cSaveR c p x
  wr [oSTOP]
  emit .finish

/-- `pickle.dumps(obj, protocol, buffer_callback=...)`: `_pickle_dumps_impl`
(`Modules/_pickle.c:8122-8149`), `c` levels of stack room. -/
def cDumpsM (c : Nat) (x : PV) (a : DumpsArgs) : EncM Unit := do
  let p ← liftPyA (cProtocolA a.protocol)
  liftPyA (cBufCheck a.bufcb p)
  cBodyR c p x

def cDumpsA (c : Nat) (x : PV) (a : DumpsArgs) : Py Bytes := encRun cFrame (cDumpsM c x a)

/-- `pickle._dumps(obj, protocol, buffer_callback=...)` (`Lib/pickle.py:1896-1902`), called
from a frame with `b` frames left: its own frame, `_Pickler(...)` (`__init__`, which builds a
`_Framer`), then `.dump(obj)`. -/
def pyDumpsM (b : Nat) (x : PV) (a : DumpsArgs) : EncM Unit :=
  pyCall b fun b1 => do
    let p ← pyCall b1 fun b2 => do
      let p ← liftPyA (pyProtocolA a)
      pyCall b2 fun _ => pure ()
      pure p
    pyCall b1 fun b2 => pyBodyR b2 p x

def pyDumpsA (b : Nat) (x : PV) (a : DumpsArgs) : Py Bytes := encRun pyFrame (pyDumpsM b x a)

end PyLean.Pickle
