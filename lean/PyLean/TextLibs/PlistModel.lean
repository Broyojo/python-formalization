import PyLean.TextLibs.StructModel
import PyLean.UnicodeObj.CodecProps
import PyLean.Binary64.Model
import PyLean.Datetime.Delta

/-!
Model of the binary plist reader of `Lib/plistlib.py`, CPython 3.15.2, and of the dispatch of
`load`/`loads` (line numbers below are that file's unless a path is given).

Bytes are lists of byte values (`List Nat`, each below 256: the type invariant of `bytes`).

## Objects and identity

The reader's `self._objects` (:505) is the heap: slot `i` holds `none` (`_undefined`) or the
object read for reference `i`. `_read_object(ref)` always returns the object in slot `ref`
(:553-555, :643-644), so an object is named by its slot and containers hold the slots of their
elements. This keeps object identity exact, cycles included: an array that refers to itself
holds its own slot. Leaves read for different slots are different objects, except where CPython
shares them (small ints, `True`, `None`, `b''`); every such shared leaf is equal to itself, and
identity is only consulted by dict key lookup, which then agrees.

A dict is the list of its (key slot, value slot) pairs in insertion order; `result[k] = v`
(`dict_ass_sub`) hashes the key (`TypeError` for a list or dict), and replaces the value of the
entry whose key is the same object or compares equal (`keyEq`), keeping that entry's key and
position, or appends a new entry. `dict_type` is `dict` (a stated scope limit: other mappings
can run arbitrary code).

## Exceptions

`parse` (:487-510) replaces the exceptions it catches by `InvalidFileException()`. The `except`
clause matches by class: `isInst` walks each class's bases (`excMro`), so
`UnicodeDecodeError` and `InvalidFileException` itself are caught as `ValueError`s, and
`RecursionError` (a `RuntimeError`) is not.

## The recursion limit

As in `TomlModel.lean`: calling a Python function pushes a frame (`_Py_EnterRecursivePy`,
Python/ceval_macros.h:426-429), which raises `RecursionError("maximum recursion depth
exceeded")` when no frame is left. Every model function `foo r ...` is the call of `foo` made
with `r` frames left, its own frame included (`call`). C functions (`struct`, `int.from_bytes`,
`bytes.decode`, `BytesIO`, `datetime`, `dict`) push none. Python frames below the reader's are
`_get_size`, `_read`, `_read_ints` (and its generator expression, :541-542), `_read_refs`,
`UID.__init__` (:81-88), `InvalidFileException.__init__` (:468-469) for every
`raise InvalidFileException`, and `Enum.__hash__` (Lib/enum.py:1328) when `_FORMATS[fmt]`
hashes a format. Storing a `UID` key hashes it with `UID.__hash__` and may compare it with
`UID.__eq__` (one frame each); the key was read by `_read_object` just before with the same
frames left, which needed at least one, so these calls never raise `RecursionError` and are not
counted.
-/

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs PyLean.Binary64

/-! ## Exceptions -/

def recErr : PyExc := .named "RecursionError" "maximum recursion depth exceeded"
/-- `InvalidFileException(message)`, :467-469: a `ValueError` subclass whose `__init__` passes
`message` to `ValueError.__init__`, so `str(e)` is `message`. -/
def invalidFileExc (message : String) : PyExc := .named "InvalidFileException" message
/-- `InvalidFileException()`: the default `message="Invalid file"`. -/
def invalidFile : PyExc := invalidFileExc "Invalid file"
/-- `struct.error`. -/
def structErr (m : String) : PyExc := .named "error" m

/-- The bases of each exception class the module can raise, nearest first (`type.__mro__`
without `BaseException` and `object`). -/
def excMro : PyExc → List String
  | .valueError _ => ["ValueError", "Exception"]
  | .typeError _ => ["TypeError", "Exception"]
  | .indexError _ => ["IndexError", "LookupError", "Exception"]
  | .keyError _ => ["KeyError", "LookupError", "Exception"]
  | .overflowError _ => ["OverflowError", "ArithmeticError", "Exception"]
  | .zeroDivisionError _ => ["ZeroDivisionError", "ArithmeticError", "Exception"]
  | .assertionError _ => ["AssertionError", "Exception"]
  | .stopIteration => ["StopIteration", "Exception"]
  | .named "InvalidFileException" _ => ["InvalidFileException", "ValueError", "Exception"]
  | .named "UnicodeDecodeError" _ => ["UnicodeDecodeError", "UnicodeError", "ValueError", "Exception"]
  | .named "UnicodeEncodeError" _ => ["UnicodeEncodeError", "UnicodeError", "ValueError", "Exception"]
  | .named "Error" _ => ["Error", "ValueError", "Exception"]
  | .named "error" _ => ["error", "Exception"]
  | .named "RecursionError" _ => ["RecursionError", "RuntimeError", "Exception"]
  | .named "AttributeError" _ => ["AttributeError", "Exception"]
  | .named "ExpatError" _ => ["ExpatError", "Exception"]
  | .named c _ => [c, "Exception"]
  | .modelFuel => []

/-- `isinstance(e, cls)`. -/
def isInst (e : PyExc) (cls : String) : Bool := (excMro e).contains cls

/-- The `except (OSError, IndexError, struct.error, OverflowError, ValueError)` of :508-509. -/
def parseCatches (e : PyExc) : Bool :=
  isInst e "OSError" || isInst e "IndexError" || isInst e "error" ||
  isInst e "OverflowError" || isInst e "ValueError"

/-! ## Frames -/

/-- A call of a Python function made with `r` frames left: its body runs with `r - 1`. -/
def call {α : Type} (r : Nat) (body : Nat → Py α) : Py α :=
  match r with
  | 0 => .error recErr
  | r + 1 => body r

/-- `raise InvalidFileException` (or `InvalidFileException()`) with `r` frames left: the
instantiation runs `InvalidFileException.__init__`, :468-469. -/
def raiseInvalid {α : Type} (r : Nat) : Py α := call r fun _ => .error invalidFile

/-! ## Bytes -/

/-- `int.from_bytes(b, 'big')`. -/
def beVal (b : List Nat) : Nat := b.foldl (fun x c => x * 256 + c) 0

/-- `int.from_bytes(b, 'big', signed=s)`. -/
def fromBytes (b : List Nat) (signed : Bool) : Int :=
  let v := beVal b
  if signed && decide (b.length > 0) && decide (2 ^ (8 * b.length - 1) ≤ v) then
    (v : Int) - 2 ^ (8 * b.length)
  else v

/-- `[data[i:i + size] for i in range(0, size * n, size)]`. -/
def chunks (size : Nat) : (n : Nat) → List Nat → List (List Nat)
  | 0, _ => []
  | n + 1, d => d.take size :: chunks size n (d.drop size)

/-! ## The file: `io.BytesIO` (Modules/_io/bytesio.c) -/

structure FP where
  buf : List Nat
  pos : Nat
  deriving Repr, DecidableEq

/-- `BytesIO.read(n)` for `n >= 0`, `_io_BytesIO_read_impl`, bytesio.c:509-525: at most the
bytes left after the position (none when the position is past the end). -/
def FP.read (f : FP) (n : Nat) : List Nat × FP :=
  let k := min n (f.buf.length - f.pos)
  ((f.buf.drop f.pos).take k, { f with pos := f.pos + k })

/-- `BytesIO.seek(pos)` for an int `pos >= 0` (whence 0): the clinic `Py_ssize_t` converter
(clinic/bytesio.c.h:471-482) raises `OverflowError` past `PY_SSIZE_T_MAX`; then
`_io_BytesIO_seek_impl`, bytesio.c:774-815, sets the position. -/
def FP.seek (f : FP) (pos : Nat) : Py FP :=
  if pos > 2 ^ 63 - 1 then .error (.overflowError "Python int too large to convert to C ssize_t")
  else .ok { f with pos := pos }

/-- `BytesIO.seek(-n, os.SEEK_END)`, bytesio.c:796-812: `string_size - n`, raised to 0. -/
def FP.seekEnd (f : FP) (n : Nat) : FP := { f with pos := f.buf.length - n }

/-! ## Objects -/

inductive Obj where
  | none
  | bool (b : Bool)
  | int (i : Int)
  /-- A float, as its 64 bits. -/
  | real (bits : Nat)
  /-- A `datetime`: microseconds since 2001-01-01 00:00, `tzinfo=datetime.UTC` when `aware`. -/
  | date (us : Int) (aware : Bool)
  | data (b : List Nat)
  | str (s : List Nat)
  | uid (n : Nat)
  /-- A list, by the slots of its elements. -/
  | arr (refs : List Nat)
  /-- A dict, by the (key slot, value slot) pairs in insertion order. -/
  | dict (items : List (Nat × Nat))
  deriving Repr, DecidableEq, Inhabited

/-- Exact value of a finite float, as a rational (`F64.toRat`). -/
def realVal (bits : Nat) : Rat := (F64.ofBits bits).toRat

/-- Python `==` between two numbers (bool is an int; `long_richcompare`, `float_richcompare`
compare exactly; a NaN equals nothing). -/
def numEq : Obj → Obj → Option Bool
  | .bool a, .bool b => some (a == b)
  | .bool a, .int b => some ((if a then 1 else 0) == b)
  | .int a, .bool b => some (a == (if b then 1 else 0))
  | .int a, .int b => some (a == b)
  | .real x, .real y => some (F64.eq (F64.ofBits x) (F64.ofBits y))
  | .real x, .int b => some ((F64.ofBits x).isFinite && decide (realVal x = (b : Rat)))
  | .int a, .real y => some ((F64.ofBits y).isFinite && decide ((a : Rat) = realVal y))
  | .real x, .bool b => some ((F64.ofBits x).isFinite && decide (realVal x = (if b then 1 else 0 : Rat)))
  | .bool a, .real y => some ((F64.ofBits y).isFinite && decide ((if a then 1 else 0 : Rat) = realVal y))
  | _, _ => none

/-- `UID.__eq__`, :99-102: `NotImplemented` for a non-`UID`, else the data compared. -/
def uidEq (self : Nat) : Obj → Option Bool
  | .uid d => some (self == d)
  | _ => none

/-- Python `a == b` for two hashable objects the reader makes (C `__eq__`s, and `UID.__eq__`,
whose `NotImplemented` both ways falls back to identity, which differs here). Naive and aware
datetimes never meet in one parse. -/
def keyEq (a b : Obj) : Bool :=
  match numEq a b with
  | some r => r
  | none =>
    match a, b with
    | .none, .none => true
    | .str x, .str y => x == y
    | .data x, .data y => x == y
    | .date x _, .date y _ => x == y
    | .uid d, o => (uidEq d o).getD false
    | o, .uid d => (uidEq d o).getD false
    | _, _ => false

/-- `hash(o)` fails for the two unhashable types the reader makes. -/
def unhashable : Obj → Bool
  | .arr _ | .dict _ => true
  | _ => false

/-- `result[k] = v` on a dict given by its items (keys `k`, `v` are slots of `objs`): the entry
whose key is the same object or equal is updated in place, else one is appended. -/
def dictSet (objs : List (Option Obj)) (k v : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(k, v)]
  | (k', v') :: rest =>
    let same := k' == k || match objs.getD k' none, objs.getD k none with
      | some a, some b => keyEq a b
      | _, _ => false
    if same then (k', v) :: rest else (k', v') :: dictSet objs k v rest

/-! ## Dates: `epoch + datetime.timedelta(seconds=f)`, :587-595 -/

/-- `PyLong_FromDouble` on an integral double, Objects/longobject.c. -/
def longFromDouble (x : F64) : Py Int :=
  if x.isNaN then .error (.valueError "cannot convert float NaN to integer")
  else if x.isInf then .error (.overflowError "cannot convert float infinity to integer")
  else .ok x.truncInt

/-- C `modf(x, &intpart)`: (fractional part, integral part). -/
def modf (x : F64) : F64 × F64 :=
  if x.isNaN then (x, x)
  else if x.isInf then (F64.zero x.sign, x)
  else (F64.sub x (F64.trunc x), F64.trunc x)

/-- `accum("seconds", 0, f, 10**6, &leftover_us)` for a float `f`, Modules/_datetimemodule.c:2733-2811:
the running sum of microseconds and the new `leftover_us`. -/
def accumSeconds (f : F64) : Py (Int × F64) := do
  -- fracpart = modf(dnum, &intpart); x = PyLong_FromDouble(intpart); prod = x * factor
  let (frac1, int1) := modf f
  let x1 ← longFromDouble int1
  let sum := 0 + x1 * 1000000
  if F64.eq frac1 (F64.zero false) then return (sum, F64.zero false)
  -- dnum = PyLong_AsDouble(factor); dnum *= fracpart; fracpart = modf(dnum, &intpart)
  let dnum := F64.mul (F64.ofInt 1000000) frac1
  let (frac2, int2) := modf dnum
  let x2 ← longFromDouble int2
  -- y = sum + x; *leftover += fracpart
  return (sum + x2, F64.add (F64.zero false) frac2)

/-- The rounding of a nonzero `leftover_us` in `delta_new_impl`, :2899-2926: `whole_us =
round(leftover_us)`, or, exactly halfway, `2.0 * round((leftover_us + x_is_odd) * 0.5) -
x_is_odd` with `x_is_odd = x & 1`; then `(long)whole_us`. -/
def wholeUs (x : Int) (leftover : F64) : Int :=
  let whole := F64.roundAway leftover
  let half := F64.ofRat (mkRat 1 2)
  let whole :=
    if F64.eq (F64.abs (F64.sub whole leftover)) half then
      let o := F64.ofInt (x % 2)
      F64.sub (F64.mul (F64.ofInt 2) (F64.roundAway (F64.mul (F64.add leftover o) half))) o
    else whole
  whole.truncInt

/-- `timedelta(seconds=f)` for a float `f`, `delta_new_impl` (:2832-2932) with only `seconds`:
`accum`, the rounding of the leftover, and `microseconds_to_delta_ex` (:2218-2284,
`Datetime.usToDeltaC`). -/
def deltaFromSeconds (f : F64) : Py Datetime.Delta := do
  let (x, leftover) ← accumSeconds f
  if F64.ne leftover (F64.zero false) then Datetime.usToDeltaC (x + wholeUs x leftover)
  else Datetime.usToDeltaC x

/-- `date_from_ordinal` range: `MAXORDINAL`, _datetimemodule.c. -/
def maxOrdinal : Int := 3652059
/-- `date(2001, 1, 1).toordinal()`. -/
def epochOrdinal : Int := 730486

/-- `datetime(2001, 1, 1) + td`, `add_datetime_timedelta` (_datetimemodule.c:6241-6265):
`normalize_datetime` (:847-857) leaves the time fields in range and moves the day count into
`day = 1 + td.days`; `normalize_y_m_d` (:780-835) takes day 0 to 2000-12-31 and day 32 to
2001-02-01 and otherwise goes through the ordinal, raising `OverflowError` outside
`1..MAXORDINAL`. The result, as microseconds since the epoch, is `td` itself. -/
def epochPlus (td : Datetime.Delta) : Py Int :=
  let d := 1 + td.days
  if d < 1 ∨ d > 31 then
    if d = 0 ∨ d = 32 then .ok td.toUs
    else
      let ordinal := epochOrdinal + d - 1
      if ordinal < 1 ∨ ordinal > maxOrdinal then .error (.overflowError "date value out of range")
      else .ok td.toUs
  else .ok td.toUs

/-! ## The parser -/

/-- `_BINARY_FORMAT`, :471: the sizes `struct` reads natively. -/
def binaryFormat (size : Nat) : Bool := size == 1 || size == 2 || size == 4 || size == 8

structure PState where
  fp : FP
  /-- `self._objects`. -/
  objs : List (Option Obj)
  deriving Repr, DecidableEq

structure PCfg where
  /-- `self._object_offsets`. -/
  offsets : List Nat
  /-- `self._ref_size`. -/
  refSize : Nat
  /-- `self._aware_datime`, :485. -/
  aware : Bool

/-- `_read(size)`'s `while True` loop, :525-532. Each round that does not return grows `cursize`
by at least one (it starts at `min(size, 2**20)`, which is 0 only when `size` is), so `size + 1`
rounds of fuel suffice. -/
def readLoop (r : Nat) (size : Nat) : (fuel : Nat) → FP → (cursize : Nat) → List Nat →
    Py (List Nat × FP)
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, fp, cursize, data =>
    if data.length ≠ cursize then raiseInvalid r
    else if cursize = size then .ok (data, fp)
    else
      let delta := min cursize (size - cursize)
      let (d, fp') := fp.read delta
      readLoop r size fuel fp' (cursize + delta) (data ++ d)

/-- `_MIN_READ_BUF_SIZE`, :78. -/
def minReadBuf : Nat := 2 ^ 20

/-- `_read(size)`, :522-532, with `r` frames left. -/
def readR (r : Nat) (fp : FP) (size : Nat) : Py (List Nat × FP) := call r fun r =>
  let cursize := min size minReadBuf
  let (data, fp) := fp.read cursize
  readLoop r size (size + 1) fp cursize data

/-- `_read_ints(n, size)`, :534-542, with `r` frames left. -/
def readIntsR (r : Nat) (fp : FP) (n size : Nat) : Py (List Nat × FP) := call r fun r => do
  let (data, fp) ← readR r fp (size * n)
  if binaryFormat size then
    -- struct.unpack(f'>{n}{_BINARY_FORMAT[size]}', data): data has size * n bytes
    .ok ((chunks size n data).map beVal, fp)
  else if size = 0 then raiseInvalid r
  else
    -- tuple(<generator expression>): one frame while the generator runs
    call r fun _ => .ok ((chunks size n data).map beVal, fp)

/-- `_read_refs(n)`, :544-545. -/
def readRefsR (r : Nat) (cfg : PCfg) (fp : FP) (n : Nat) : Py (List Nat × FP) :=
  call r fun r => readIntsR r fp n cfg.refSize

/-- `_get_size(tokenL)`, :512-520, with `r` frames left. -/
def getSizeR (r : Nat) (fp : FP) (tokenL : Nat) : Py (Nat × FP) := call r fun _ =>
  if tokenL = 0xF then
    let (b, fp) := fp.read 1
    match b with
    | [] => .error (.indexError "index out of range")
    | m0 :: _ =>
      let m := m0 &&& 0x3
      let s := 2 ^ m
      let (d, fp) := fp.read s
      if d.length ≠ s then .error (structErr s!"unpack requires a buffer of {s} bytes")
      else .ok (beVal d, fp)
  else .ok (tokenL, fp)

/-- `UID(data)`, :81-88, for an int `data`, with `r` frames left. -/
def uidR (r : Nat) (data : Int) : Py Nat := call r fun _ =>
  if data ≥ 2 ^ 64 then .error (.valueError "UIDs cannot be >= 2**64")
  else if data < 0 then .error (.valueError "UIDs must be positive")
  else .ok data.toNat

/-- `struct.unpack('>f', b)[0]` / `struct.unpack('>d', b)[0]`: the bits of the float, or
`struct.error` for the wrong length (Modules/_struct.c; `PyFloat_Unpack4`,
Objects/floatobject.c:2146-2201, keeps a signalling NaN signalling). -/
def unpackReal (b : List Nat) (four : Bool) : Py Nat :=
  let n := if four then 4 else 8
  if b.length ≠ n then .error (structErr s!"unpack requires a buffer of {n} bytes")
  else if four then .ok (Struct.pyFloatUnpack4Bits (beVal b)) else .ok (beVal b)

/-- Store `o` in slot `ref`. -/
def PState.put (st : PState) (ref : Nat) (o : Obj) : PState :=
  { st with objs := st.objs.set ref (some o) }

/-- The `for x in obj_refs: result.append(self._read_object(x))` loop, :620-621. `rd` is
`_read_object` with the frames left below the frame that runs the loop. -/
def arrLoop (rd : Nat → PState → Py PState) (ref : Nat) : List Nat → List Nat → PState → Py PState
  | _, [], st => .ok st
  | acc, x :: xs, st => do
    let st ← rd x st
    arrLoop rd ref (acc ++ [x]) xs (st.put ref (.arr (acc ++ [x])))

/-- The body of `for k, o in zip(key_refs, obj_refs): result[self._read_object(k)] =
self._read_object(o)`, :636-637: the value is read first, then the key, then the key is hashed
and stored. -/
def dictLoop (rd : Nat → PState → Py PState) (ref : Nat) :
    List (Nat × Nat) → List (Nat × Nat) → PState → Py PState
  | _, [], st => .ok st
  | items, (k, o) :: ps, st => do
    let st ← rd o st
    let st ← rd k st
    -- `rd k` returned, so slot `k` holds the key; `none` cannot happen
    match st.objs.getD k none with
    | some key =>
      if unhashable key then .error (.typeError "~unhashable type")
      else
        let items := dictSet st.objs k o items
        dictLoop rd ref items ps (st.put ref (.dict items))
    | none => .error .modelFuel

/-- `try: ... except TypeError: raise InvalidFileException()` around the loop of a dict, :635-639. -/
def catchTypeError (r : Nat) (res : Py PState) : Py PState :=
  match res with
  | .ok st => .ok st
  | .error e => if isInst e "TypeError" then raiseInvalid r else .error e

/-- The part of `_read_object(ref)` after the token is read, :560-644, with `r` frames left below
`_read_object`'s frame; `rd` is `_read_object` called with those frames, for the elements. -/
def readToken (cfg : PCfg) (r : Nat) (rd : Nat → PState → Py PState) (ref : Nat) (st : PState)
    (token : Nat) (fp : FP) : Py PState := do
  let tokenH := token &&& 0xF0
  let tokenL := token &&& 0x0F
  let leaf (o : Obj) (fp : FP) : Py PState := .ok ({ st with fp := fp }.put ref o)
  if token = 0x00 then leaf .none fp
  else if token = 0x08 then leaf (.bool false) fp
  else if token = 0x09 then leaf (.bool true) fp
  else if token = 0x0f then leaf (.data []) fp
  else if tokenH = 0x10 then
    let (b, fp) := fp.read (2 ^ tokenL)
    leaf (.int (fromBytes b (decide (tokenL ≥ 3)))) fp
  else if token = 0x22 then
    let (b, fp) := fp.read 4
    leaf (.real (← unpackReal b true)) fp
  else if token = 0x23 then
    let (b, fp) := fp.read 8
    leaf (.real (← unpackReal b false)) fp
  else if token = 0x33 then
    let (b, fp) := fp.read 8
    let f ← unpackReal b false
    let td ← deltaFromSeconds (F64.ofBits f)
    leaf (.date (← epochPlus td) cfg.aware) fp
  else if tokenH = 0x40 then
    let (s, fp) ← getSizeR r fp tokenL
    let (d, fp) ← readR r fp s
    leaf (.data d) fp
  else if tokenH = 0x50 then
    let (s, fp) ← getSizeR r fp tokenL
    let (d, fp) ← readR r fp s
    leaf (.str (← UnicodeObj.asciiDecode d .strict)) fp
  else if tokenH = 0x60 then
    let (s, fp) ← getSizeR r fp tokenL
    let (d, fp) ← readR r fp (s * 2)
    let (u, _) ← UnicodeObj.utf16DecodeFull d 1 .strict true
    leaf (.str u) fp
  else if tokenH = 0x80 then
    let (b, fp) := fp.read (1 + tokenL)
    leaf (.uid (← uidR r (beVal b))) fp
  else if tokenH = 0xA0 then
    let (s, fp) ← getSizeR r fp tokenL
    let (refs, fp) ← readRefsR r cfg fp s
    let st := { st with fp := fp }.put ref (.arr [])
    -- :643 stores the same list again; the loop left it complete in slot `ref`
    arrLoop rd ref [] refs st
  else if tokenH = 0xD0 then
    let (s, fp) ← getSizeR r fp tokenL
    let (keyRefs, fp) ← readRefsR r cfg fp s
    let (objRefs, fp) ← readRefsR r cfg fp s
    let st := { st with fp := fp }.put ref (.dict [])
    -- :643 stores the same dict again
    catchTypeError r (dictLoop rd ref [] (keyRefs.zip objRefs) st)
  else raiseInvalid r

/-- `_read_object(ref)`, :547-644, with `r` frames left. -/
def readObj (cfg : PCfg) : (r : Nat) → (ref : Nat) → PState → Py PState
  | 0, _, _ => .error recErr
  | r + 1, ref, st =>
    -- result = self._objects[ref]
    match st.objs[ref]? with
    | none => .error (.indexError "list index out of range")
    | some (some _) => .ok st
    | some none => do
      let offset := cfg.offsets.getD ref 0
      let fp ← st.fp.seek offset
      -- token = self._fp.read(1)[0]
      let (tb, fp) := fp.read 1
      match tb with
      | [] => .error (.indexError "index out of range")
      | token :: _ => readToken cfg r (fun x st => readObj cfg r x st) ref st token fp

/-- The trailer, `struct.unpack('>6xBBQQQ', trailer)` on its 32 bytes, :499-502. -/
structure Trailer where
  offsetSize : Nat
  refSize : Nat
  numObjects : Nat
  topObject : Nat
  offsetTableOffset : Nat
  deriving Repr, DecidableEq

def Trailer.ofBytes (t : List Nat) : Trailer :=
  ⟨t.getD 6 0, t.getD 7 0, beVal ((t.drop 8).take 8), beVal ((t.drop 16).take 8),
    beVal ((t.drop 24).take 8)⟩

/-- What `parse` returns: the object in slot `root` of `objs`. -/
structure Res where
  objs : List (Option Obj)
  root : Nat
  deriving Repr, DecidableEq

/-- The `try` body of `parse`, :494-506, with `r` frames left below `parse`. -/
def parseBody (r : Nat) (aware : Bool) (buf : List Nat) : Py Res := do
  let fp : FP := ⟨buf, 0⟩
  let fp := fp.seekEnd 32
  let (trailer, fp) := fp.read 32
  if trailer.length ≠ 32 then raiseInvalid r
  else
    let t := Trailer.ofBytes trailer
    let fp ← fp.seek t.offsetTableOffset
    let (offsets, fp) ← readIntsR r fp t.numObjects t.offsetSize
    let cfg : PCfg := ⟨offsets, t.refSize, aware⟩
    let st : PState := ⟨fp, List.replicate t.numObjects none⟩
    let st ← readObj cfg r t.topObject st
    .ok ⟨st.objs, t.topObject⟩

/-- `_BinaryPlistParser.parse(fp)`, :487-510, with `r` frames left. -/
def parseR (r : Nat) (aware : Bool) (buf : List Nat) : Py Res := call r fun r =>
  match parseBody r aware buf with
  | .ok v => .ok v
  | .error e => if parseCatches e then raiseInvalid r else .error e

/-! ## Format detection and `load`/`loads`, :434-460, :872-873, :894-926 -/

def asciiBytes (s : String) : List Nat := s.toList.map Char.toNat

/-- `start.decode('ascii').encode(encoding)` for an ASCII `start`: UTF-8 keeps the bytes,
UTF-16 puts a zero byte before (big-endian) or after (little-endian) each. -/
def encodeAscii (enc : Nat) (s : List Nat) : List Nat :=
  match enc with
  | 0 => s
  | 1 => s.flatMap fun c => [0, c]
  | _ => s.flatMap fun c => [c, 0]

/-- `_is_fmt_xml(header)`, :434-460. -/
def isFmtXml (header : List Nat) : Bool :=
  let prefixes := [asciiBytes "<?xml", asciiBytes "<plist"]
  if prefixes.any (fun p => p.isPrefixOf header) then true
  else
    let boms : List (List Nat × Nat) := [([0xEF, 0xBB, 0xBF], 0), ([0xFE, 0xFF], 1), ([0xFF, 0xFE], 2)]
    boms.any fun (bom, enc) =>
      bom.isPrefixOf header &&
        prefixes.any fun start =>
          let pfx := bom ++ encodeAscii enc start
          header.take pfx.length == pfx

/-- `_is_fmt_binary(header)`, :872-873. -/
def isFmtBinary (header : List Nat) : Bool := header.take 8 == asciiBytes "bplist00"

/-- The `fmt` argument. -/
inductive Fmt where
  | none | xml | binary
  /-- Any other hashable object; `repr` is its `repr()`. -/
  | other (repr : String)
  /-- An object of type `ty` whose `hash()` raises `e` (a C `__hash__`: a Python one would push a
  frame, out of scope). `list`'s raises `TypeError("unhashable type: 'list'")`. -/
  | badHash (ty : String) (e : PyExc)
  deriving Repr, DecidableEq

/-- Looking a key up in a `frozendict` (`_FORMATS[fmt]`, `fmt in _FORMATS`) when its hash raises:
`dict_unhashable_type`, Objects/dictobject.c:2442-2460, rewraps an exact `TypeError` as
`TypeError("cannot use '%T' as a frozendict key (%S)")` and lets any other exception through. -/
def frozendictKeyErr (ty : String) (e : PyExc) : PyExc :=
  if e.className = "TypeError" then .typeError s!"cannot use '{ty}' as a frozendict key ({e.message})"
  else e

/-- The XML parser (`_PlistParser(dict_type, aware_datetime).parse(fp)` on the whole buffer, with
`r` frames left below `load`): a parameter here, modelled in `PlistXml.lean`. -/
abbrev XmlParse := Nat → Bool → List Nat → Py Res

/-- `load(fp, fmt=fmt, aware_datetime=aware)` for a `BytesIO` at position 0, :894-913, with `r`
frames left. -/
def loadR (xml : XmlParse) (r : Nat) (buf : List Nat) (fmt : Fmt) (aware : Bool) : Py Res :=
  call r fun r => do
    -- P is xml (true) or binary (false)
    let P ← match fmt with
      | .none => do
        -- header = fp.read(32); fp.seek(0)
        let header := (FP.read ⟨buf, 0⟩ 32).1
        -- for info in _FORMATS.values(): if info['detect'](header): ... else: raise
        let isXml ← call r fun _ => .ok (isFmtXml header)
        if isXml then .ok true
        else
          let isBin ← call r fun _ => .ok (isFmtBinary header)
          if isBin then .ok false else raiseInvalid r
      -- _FORMATS[fmt]['parser']: hashing a PlistFormat runs Enum.__hash__
      | .xml => call r fun _ => .ok true
      | .binary => call r fun _ => .ok false
      | .other rp => .error (.keyError rp)
      | .badHash ty e => .error (frozendictKeyErr ty e)
    -- p = P(dict_type=dict_type, aware_datetime=aware_datetime): __init__ is one frame
    call r fun _ => .ok ()
    if P then xml r aware buf else parseR r aware buf

/-- The `value` argument of `loads`: a `str` (code points) or a bytes-like object. -/
inductive LoadArg where
  | str (s : List Nat)
  | bytes (b : List Nat)
  deriving Repr, DecidableEq

/-- `loads(value, fmt=fmt, aware_datetime=aware)`, :916-926, with `r` frames left. -/
def loadsR (xml : XmlParse) (r : Nat) (value : LoadArg) (fmt : Fmt) (aware : Bool) : Py Res :=
  call r fun r => do
    let buf ← match value with
      | .str s =>
        if fmt = .binary then
          .error (.typeError "value must be bytes-like object when fmt is FMT_BINARY")
        else UnicodeObj.utf8Encode s .strict
      | .bytes b => .ok b
    loadR xml r buf fmt aware

end PyLean.TextLibs.Plist
