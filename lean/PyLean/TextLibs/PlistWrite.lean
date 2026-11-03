import PyLean.TextLibs.PlistModel

/-!
Model of the binary plist writer of `Lib/plistlib.py`, CPython 3.15.2 (`_dict_items`,
`_count_to_size`, `_BinaryPlistWriter`, `dump`, `dumps`; line numbers are that file's).

## The value written

The value is an object graph: a heap of cells (`WHeap`) and the cell of the root. Containers hold
the cells of their elements, so sharing and cycles are expressible (a list may contain itself).
A cell is one Python object, and `id()` is its cell, except for the two singletons the writer can
meet among the objects it tracks by identity: every `None` cell is the one `None` object and
every empty tuple the one `()` (`objId`). Scalars (`_scalars`, :659) are tracked by value.

A dict cell holds its (key cell, value cell) items in insertion order. Its keys are pairwise
unequal (the type invariant of a dict); a key that is not a `str` may be any hashable object, and
only `isinstance(key, str)` is asked of it.

A `datetime` is its wall-clock time in microseconds since 2001-01-01 00:00 (within
`datetime.min..datetime.max`) and, for an aware one, the `utcoffset()` of its fixed-offset
`timezone`, in microseconds. A naive datetime written with `aware_datetime=True` is converted
from local time (`datetime.astimezone`, `local_timezone_from_local`); that conversion is the
parameter `localToUtc`.

The writer pushes frames as the reader does (`Plist.call`): `_flatten` once per level, and
`_dict_items`, `_getrefnum`, `_write_size`, `_count_to_size`, `UID.__index__` (called by
`struct.pack` on a `UID`, :835-841) and `Enum.__hash__` (when `dump` hashes `fmt`) one each.
`struct.pack`, `str.encode`, `BytesIO`, `sorted` on `str` keys and `datetime` are C.
-/

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs PyLean.Binary64

inductive WObj where
  | none
  | bool (b : Bool)
  | int (i : Int)
  | float (bits : Nat)
  | str (s : List Nat)
  | bytes (b : List Nat)
  | bytearray (b : List Nat)
  /-- Wall time in microseconds since 2001-01-01, and the fixed `utcoffset()` if aware. -/
  | date (us : Int) (off : Option Int)
  /-- A `UID`, by its `data` attribute (an int). -/
  | uid (data : Int)
  | list (xs : List Nat)
  | tuple (xs : List Nat)
  | dict (items : List (Nat × Nat))
  | fdict (items : List (Nat × Nat))
  /-- An object of any other type; `str` is `str(value)`, `ty` is `type(value)`'s `repr`. -/
  | other (str ty : String)
  deriving Repr, DecidableEq, Inhabited

abbrev WHeap := List WObj

/-- `type(value)` for the `_scalars` `(str, int, float, datetime.datetime, bytes)`, :659
(`bool` is an `int` subclass with its own type). `none`: not a scalar. -/
def scalarType : WObj → Option Nat
  | .str _ => some 0
  | .int _ => some 1
  | .bool _ => some 2
  | .float _ => some 3
  | .date _ _ => some 4
  | .bytes _ => some 5
  | _ => none

/-- `id(value)` for the objects tracked by identity. -/
inductive OId where
  | cell (c : Nat)
  | noneObj
  | emptyTuple
  deriving Repr, DecidableEq

def objId (H : WHeap) (c : Nat) : OId :=
  match H.getD c .none with
  | .none => .noneObj
  | .tuple [] => .emptyTuple
  | _ => .cell c

/-- `value == other` for two scalars of the same type (C `__eq__`s: a NaN equals nothing; two
aware datetimes are equal when they are the same instant; naive and aware are unequal). -/
def scalarEq : WObj → WObj → Bool
  | .str a, .str b => a == b
  | .int a, .int b => a == b
  | .bool a, .bool b => a == b
  | .float a, .float b => F64.eq (F64.ofBits a) (F64.ofBits b)
  | .date a none, .date b none => a == b
  | .date a (some oa), .date b (some ob) => a - oa == b - ob
  | .bytes a, .bytes b => a == b
  | _, _ => false

/-- Whether the key `(type(c'), c')` of `self._objtable` matches `(type(c), c)`: same type, and
the same object or equal (`PyObject_RichCompareBool` in the tuple comparison tries identity
first). -/
def scalarMatch (H : WHeap) (c' c : Nat) : Bool :=
  let a := H.getD c' .none
  let b := H.getD c .none
  scalarType a == scalarType b && (c' == c || scalarEq a b)

structure WState where
  /-- `self._objlist`, by cell. -/
  objlist : List Nat
  /-- `self._objtable`: (cell of the scalar first seen, refnum). -/
  objtable : List (Nat × Nat)
  /-- `self._objidtable`. -/
  objidtable : List (OId × Nat)
  deriving Repr, DecidableEq

def WState.init : WState := ⟨[], [], []⟩

structure WCfg where
  sortKeys : Bool
  skipkeys : Bool
  awareDatetime : Bool
  /-- `naive.astimezone(datetime.UTC)` as microseconds since the epoch. -/
  localToUtc : Int → Py Int

def tableLookup (H : WHeap) (st : WState) (c : Nat) : Option Nat :=
  (st.objtable.find? fun (c', _) => scalarMatch H c' c).map (·.2)

def idLookup (H : WHeap) (st : WState) (c : Nat) : Option Nat :=
  (st.objidtable.find? fun (i, _) => i == objId H c).map (·.2)

/-! ## `_dict_items`, :162-178 -/

/-- Python `a < b` on two `str`s: code points, lexicographically. -/
def strLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then strLt as bs else decide (a < b)

def keyStr (H : WHeap) (k : Nat) : Option (List Nat) :=
  match H.getD k .none with
  | .str s => some s
  | _ => none

/-- `sorted(items)` / `items.sort()` for items whose keys are distinct `str`s: tuples compare by
their first element, the keys, so the values are never compared. -/
def sortItems (H : WHeap) (items : List (Nat × Nat)) : List (Nat × Nat) :=
  items.mergeSort fun a b => !strLt ((keyStr H b.1).getD []) ((keyStr H a.1).getD [])

/-- `_dict_items(d, sort_keys, skipkeys)`, :162-178, with `r` frames left. -/
def dictItemsR (r : Nat) (H : WHeap) (cfg : WCfg) (items : List (Nat × Nat)) :
    Py (List (Nat × Nat)) := call r fun _ =>
  if cfg.sortKeys then
    if cfg.skipkeys then .ok (sortItems H (items.filter fun (k, _) => (keyStr H k).isSome))
    else if items.any (fun (k, _) => (keyStr H k).isNone) then .error (.typeError "keys must be strings")
    else .ok (sortItems H items)
  else .ok items

/-- The loop `for k, v in items: if not isinstance(k, str): if skipkeys: continue; raise
TypeError("keys must be strings")` of :737-743 and :855-859, giving the kept items. -/
def keptItems (H : WHeap) (skipkeys : Bool) : List (Nat × Nat) → Py (List (Nat × Nat))
  | [] => .ok []
  | (k, v) :: rest =>
    if (keyStr H k).isNone then
      if skipkeys then keptItems H skipkeys rest else .error (.typeError "keys must be strings")
    else do return (k, v) :: (← keptItems H skipkeys rest)

/-! ## `_flatten`, :713-750 -/

def wloop (f : Nat → WState → Py WState) : List Nat → WState → Py WState
  | [], st => .ok st
  | x :: xs, st => do wloop f xs (← f x st)

/-- `_flatten(value)` with `r` frames left. -/
def flattenR (H : WHeap) (cfg : WCfg) : (r : Nat) → Nat → WState → Py WState
  | 0, _, _ => .error recErr
  | r + 1, c, st =>
    let o := H.getD c .none
    let scalar := (scalarType o).isSome
    let seen := if scalar then (tableLookup H st c).isSome else (idLookup H st c).isSome
    if seen then .ok st
    else
      let refnum := st.objlist.length
      let st := { st with objlist := st.objlist ++ [c] }
      let st := if scalar then { st with objtable := st.objtable ++ [(c, refnum)] }
        else { st with objidtable := st.objidtable ++ [(objId H c, refnum)] }
      match o with
      | .dict items | .fdict items => do
        let items ← dictItemsR r H cfg items
        let kept ← keptItems H cfg.skipkeys items
        -- for o in itertools.chain(keys, values): self._flatten(o)
        wloop (fun x st => flattenR H cfg r x st) (kept.map (·.1) ++ kept.map (·.2)) st
      | .list xs | .tuple xs => wloop (fun x st => flattenR H cfg r x st) xs st
      | _ => .ok st

/-- `_getrefnum(value)`, :752-756, with `r` frames left. Every object was flattened, so the
`KeyError` cannot happen. -/
def getrefnumR (r : Nat) (H : WHeap) (st : WState) (c : Nat) : Py Nat := call r fun _ =>
  let found := if (scalarType (H.getD c .none)).isSome then tableLookup H st c else idLookup H st c
  match found with
  | some n => .ok n
  | none => .error (.keyError "~")

/-! ## Encoding, :646-657, :758-869 -/

/-- `n` as `k` big-endian bytes (`struct.pack('>B'/'>H'/'>L'/'>Q')` of an `n` in range). -/
def beBytes (n : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => beBytes (n / 256) k ++ [n % 256]

/-- `_count_to_size(count)`, :646-657. -/
def countToSize (count : Nat) : Nat :=
  if count < 2 ^ 8 then 1
  else if count < 2 ^ 16 then 2
  else if count < 2 ^ 32 then 4
  else 8

/-- `_count_to_size(count)` with `r` frames left. -/
def countToSizeR (r : Nat) (count : Nat) : Py Nat := call r fun _ => .ok (countToSize count)

/-- The bytes `_write_size(token, size)`, :758-772, writes. -/
def writeSizeB (token size : Nat) : List Nat :=
  if size < 15 then [token ||| size]
  else if size < 2 ^ 8 then [token ||| 0xF, 0x10, size]
  else if size < 2 ^ 16 then [token ||| 0xF, 0x11] ++ beBytes size 2
  else if size < 2 ^ 32 then [token ||| 0xF, 0x12] ++ beBytes size 4
  else [token ||| 0xF, 0x13] ++ beBytes size 8

/-- `_write_size(token, size)` with `r` frames left (the bytes are `writeSizeB`). -/
def writeSizeR (r : Nat) (token size : Nat) : Py (List Nat) := call r fun _ => .ok (writeSizeB token size)

/-- `datetime(2001, 1, 1)`'s range, as microseconds from it. -/
def dtMinUs : Int := -(730485 * 86400 * 1000000)
def dtMaxUs : Int := 2921574 * 86400 * 1000000 - 1

/-- The float `f` of :808-814. -/
def dateSeconds (cfg : WCfg) (us : Int) (off : Option Int) : Py Nat := do
  let utc ← if cfg.awareDatetime then
      -- dt = value.astimezone(datetime.UTC); offset = dt - datetime(2001, 1, 1, tzinfo=UTC)
      match off with
      | none => cfg.localToUtc us
      | some o =>
        if o = 0 then pure us
        else
          let u := us - o
          if u < dtMinUs ∨ u > dtMaxUs then .error (.overflowError "date value out of range")
          else pure u
    else
      -- value - datetime(2001, 1, 1)
      match off with
      | none => pure us
      | some _ => .error (.typeError "can't subtract offset-naive and offset-aware datetimes")
  -- .total_seconds(): the microseconds divided by 10**6, correctly rounded
  return (F64.ofRat (mkRat utc 1000000)).bits

/-- `struct.pack('>' + fmt * len(refs), *refs)`. -/
def packRefs (size : Nat) (refs : List Nat) : List Nat := refs.flatMap fun x => beBytes x size

/-- The `int` branch of `_write_object`, :786-803. -/
def writeInt (v : Int) : Py (List Nat) :=
  if v < 0 then
    -- struct.pack('>Bq', 0x13, value); struct.error becomes OverflowError(value)
    if v ≥ -2 ^ 63 then .ok (0x13 :: beBytes (v + 2 ^ 64).toNat 8)
    else .error (.overflowError (toString v))
  else if v < 2 ^ 8 then .ok [0x10, v.toNat]
  else if v < 2 ^ 16 then .ok (0x11 :: beBytes v.toNat 2)
  else if v < 2 ^ 32 then .ok (0x12 :: beBytes v.toNat 4)
  else if v < 2 ^ 63 then .ok (0x13 :: beBytes v.toNat 8)
  else if v < 2 ^ 64 then .ok (0x14 :: beBytes v.toNat 16)
  else .error (.overflowError (toString v))

/-- `_write_object(value)`, :774-869, with `r` frames left: the refnum and the bytes written. -/
def writeObjectR (r : Nat) (H : WHeap) (cfg : WCfg) (refSize : Nat) (st : WState) (c : Nat) :
    Py (Nat × List Nat) := call r fun r => do
  let ref ← getrefnumR r H st c
  let out : Py (List Nat) := match H.getD c .none with
    | .none => .ok [0x00]
    | .bool false => .ok [0x08]
    | .bool true => .ok [0x09]
    | .int v => writeInt v
    | .float bits => .ok (0x23 :: beBytes bits 8)
    | .date us off => do
      let f ← dateSeconds cfg us off
      .ok (0x33 :: beBytes f 8)
    | .bytes b | .bytearray b => do .ok ((← writeSizeR r 0x40 b.length) ++ b)
    | .str s =>
      match UnicodeObj.ucs1Encode s 128 .strict (fun _ => none) with
      | .ok t => do .ok ((← writeSizeR r 0x50 s.length) ++ t)
      | .error e =>
        if isInst e "UnicodeEncodeError" then do
          let t ← UnicodeObj.utf16EncodeFull s 1 .strict (fun _ => none)
          .ok ((← writeSizeR r 0x60 (t.length / 2)) ++ t)
        else .error e
    | .uid d =>
      -- struct.pack(..., value) calls UID.__index__
      if d < 0 then .error (.valueError "UIDs must be positive")
      else if d < 2 ^ 8 then call r fun _ => .ok [0x80, d.toNat]
      else if d < 2 ^ 16 then call r fun _ => .ok (0x81 :: beBytes d.toNat 2)
      else if d < 2 ^ 32 then call r fun _ => .ok (0x83 :: beBytes d.toNat 4)
      else if d < 2 ^ 64 then call r fun _ => .ok (0x87 :: beBytes d.toNat 8)
      else .error (.overflowError s!"UID({d})")
    | .list xs | .tuple xs => do
      let refs ← xs.mapM (getrefnumR r H st)
      .ok ((← writeSizeR r 0xA0 refs.length) ++ packRefs refSize refs)
    | .dict items | .fdict items => do
      let rootItems ← dictItemsR r H cfg items
      let kept ← keptItems H cfg.skipkeys rootItems
      let keyRefs ← kept.mapM (fun (k, _) => getrefnumR r H st k)
      let valRefs ← kept.mapM (fun (_, v) => getrefnumR r H st v)
      .ok ((← writeSizeR r 0xD0 keyRefs.length) ++ packRefs refSize keyRefs ++ packRefs refSize valRefs)
    | .other s _ => .error (.typeError s)
  return (ref, ← out)

/-- The `for obj in self._objlist: self._write_object(obj)` loop, :695-696: `out` is what was
written so far after the 8-byte header, `offsets` is `self._object_offsets`. -/
def writeAll (r : Nat) (H : WHeap) (cfg : WCfg) (refSize : Nat) (st : WState) :
    List Nat → List Nat → List Nat → Py (List Nat × List Nat)
  | [], offsets, out => .ok (offsets, out)
  | c :: cs, offsets, out => do
    let (ref, b) ← writeObjectR r H cfg refSize st c
    writeAll r H cfg refSize st cs (offsets.set ref (8 + out.length)) (out ++ b)

def bplistHeader : List Nat := asciiBytes "bplist00"

/-- `_BinaryPlistWriter.write(value)`, :668-711, into an empty `BytesIO`, with `r` frames left. -/
def binaryWriteR (r : Nat) (H : WHeap) (cfg : WCfg) (root : Nat) : Py (List Nat) :=
  call r fun r => do
    let st ← flattenR H cfg r root WState.init
    let n := st.objlist.length
    let refSize ← countToSizeR r n
    let (offsets, body) ← writeAll r H cfg refSize st st.objlist (List.replicate n 0) []
    let top ← getrefnumR r H st root
    let tbl := 8 + body.length
    let offsetSize ← countToSizeR r tbl
    let table := packRefs offsetSize offsets
    -- struct.pack('>5xBBBQQQ', sort_version, offset_size, ref_size, num_objects, top, table)
    let trailer := [0, 0, 0, 0, 0, 0, offsetSize, refSize] ++ beBytes n 8 ++ beBytes top 8 ++
      beBytes tbl 8
    return bplistHeader ++ body ++ table ++ trailer

/-- The XML writer (`_PlistWriter(fp, ...)` and `write(value)` into an empty `BytesIO`, with `r`
frames left below `dump`): a parameter here, modelled in `PlistXml.lean`. -/
abbrev XmlWrite := Nat → WHeap → WCfg → Nat → Py (List Nat)

/-- `dump(value, fp, fmt=fmt, ...)` into an empty `BytesIO`, :929-939, with `r` frames left. -/
def dumpR (xml : XmlWrite) (r : Nat) (H : WHeap) (root : Nat) (fmt : Fmt) (cfg : WCfg) :
    Py (List Nat) := call r fun r => do
  -- if fmt not in _FORMATS: hashing a PlistFormat runs Enum.__hash__
  match fmt with
  | .xml | .binary => call r fun _ => .ok ()
  | .none => .error (.valueError "Unsupported format: None")
  | .other rp => .error (.valueError s!"Unsupported format: {rp}")
  -- writer = _FORMATS[fmt]["writer"](fp, ...): Enum.__hash__ again, then the writer's __init__
  call r fun _ => .ok ()
  if fmt = .binary then
    call r fun _ => .ok ()
    binaryWriteR r H cfg root
  else xml r H cfg root

/-- `dumps(value, fmt=fmt, ...)`, :942-949, with `r` frames left. -/
def dumpsR (xml : XmlWrite) (r : Nat) (H : WHeap) (root : Nat) (fmt : Fmt) (cfg : WCfg) :
    Py (List Nat) := call r fun r => dumpR xml r H root fmt cfg

end PyLean.TextLibs.Plist
