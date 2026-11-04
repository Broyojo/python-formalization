import PyLean.BytesObj.Bytes.Ctor

/-!
Slots of `bytes` that the other files reach only through a shared helper: `bytes_repr`,
`bytes_str`, `bytes_richcompare` with the `-b` warnings, `bytes_item` and `PySequence_GetItem`,
`bytes_subscript`'s dispatch on the item, `bytes_buffer_getbuffer`, and `PyBytes_DecodeEscape`'s
warning under `-W error`.

`bw` is `_Py_GetConfig()->bytes_warning`: 0, 1 for `-b`, 2 for `-bb`. Under `-b` a `BytesWarning` is
issued and the call goes on (the result carries the messages); `-bb` installs the `error` filter
for `BytesWarning`, so `PyErr_WarnEx` fails and the call returns NULL with the warning raised.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-- `PyErr_WarnEx(PyExc_BytesWarning, msg, 1)` under `bytes_warning = bw` (`bw ≥ 1`). -/
def bytesWarn (bw : Nat) (msg : String) : Py (List String) :=
  if bw ≥ 2 then .error (.named "BytesWarning" msg) else .ok [msg]

/-- `bytes_repr(op)`, bytesobject.c:1509-1513: `PyBytes_Repr(op, 1)`, with smart quotes. -/
def bytesReprSlot (s : Seq) : Py Seq := bytesRepr s true

/-- `bytes_str(op)`, bytesobject.c:1515-1525: the `-b` warning, then `bytes_repr`. -/
def bytesStrW (bw : Nat) (s : Seq) : Py (Seq × List String) := do
  let ws ← if bw ≠ 0 then bytesWarn bw "str() on a bytes instance" else pure []
  let r ← bytesReprSlot s
  return (r, ws)

/-- `bytes_richcompare(aa, bb, op)`, bytesobject.c:1650-1711, with the `-b` warnings of :1655-1667 for
a non-bytes operand (`none` is `NotImplemented`). Two bytes compare by `bytesRichcompare`; the
identity shortcut of :1672-1687 gives the same answers for one object, whose identity is out of
scope. -/
def bytesRichcompareW (bw : Nat) (a b : Obj) (op : CmpOp) : Py (Option Bool × List String) :=
  match a, b with
  | .bytes x, .bytes y => .ok (some (bytesRichcompare x y op), [])
  | _, _ =>
    if bw ≠ 0 ∧ (op = .eq ∨ op = .ne) then do
      let isStr (o : Obj) : Bool := match o with | .str _ => true | _ => false
      let isInt (o : Obj) : Bool := match o with | .int _ | .bool _ => true | _ => false
      let w1 ← if isStr a || isStr b then bytesWarn bw "Comparison between bytes and string" else pure []
      let w2 ← if isInt a || isInt b then bytesWarn bw "Comparison between bytes and int" else pure []
      return (none, w1 ++ w2)
    else .ok (none, [])

/-- `bytes_item(self, i)`, bytesobject.c:1622-1631, the `sq_item` slot: a negative `i` is out of
range, with no wrap. -/
def bytesItem (s : Seq) (i : Int) : Py Nat :=
  if i < 0 ∨ i ≥ s.length then .error (.indexError "index out of range") else .ok (s.getD i.toNat 0)

/-- `PySequence_GetItem(s, i)`, Objects/abstract.c:1841-1868, on a bytes: a negative `i` gets
`sq_length` added (:1849-1857) before `sq_item`. -/
def pySequenceGetItem (s : Seq) (i : Int) : Py Nat :=
  bytesItem s (if i < 0 then i + s.length else i)

/-- `bytes_subscript(self, item)` for an item that is not a slice, bytesobject.c:1727-1742 and
:1784-1789: `_PyIndex_Check`, then `PyNumber_AsSsize_t(item, PyExc_IndexError)`, whose message names
the type of `item` (Objects/abstract.c:1505-1509); anything else is the `TypeError`. Slices go to
`bytesGetSlice`; a slice object is not in `Obj`. -/
def bytesSubscriptObj (s : Seq) (item : Obj) : Py Nat :=
  match item.index? with
  | some (.ok v) =>
    if v < ssizeMin ∨ v > ssizeMax then
      .error (.indexError s!"cannot fit '{item.typeName}' into an index-sized integer")
    else
      let i := if v < 0 then v + s.length else v
      if i < 0 ∨ i ≥ s.length then .error (.indexError "index out of range") else .ok (s.getD i.toNat 0)
  | some (.error e) => .error e
  | none => .error (.typeError s!"byte indices must be integers or slices, not {item.typeName}")

/-- `bytes_buffer_getbuffer(op, view, flags)`, bytesobject.c:1792-1798:
`PyBuffer_FillInfo(view, self, ob_sval, size, 1, flags)`, Objects/abstract.c:774-815, with
`readonly = 1`: `PyBUF_READ` and `PyBUF_WRITE` are a bad internal call (:784-787) and a
`PyBUF_WRITABLE` request is refused (:788-793). `(contents, readonly)`. -/
def bytesGetBuffer (s : Seq) (flags : Int) : Py (Seq × Bool) :=
  if flags ≠ 0 then
    if flags = 0x100 ∨ flags = 0x200 then
      .error (systemError "Objects/abstract.c:785: bad argument to internal function")
    else if flags % 2 = 1 then .error (bufferError "Object is not writable.")
    else .ok (s, true)
  else .ok (s, true)

/-- `PyBytes_DecodeEscape`, bytesobject.c:1284-1320, under a warnings filter that is `error` for
`DeprecationWarning` when `warnError`: `PyErr_WarnFormat` fails and the call returns NULL with the
warning raised (:1299-1316). -/
def bytesDecodeEscapeW (s : Seq) (errors : Option String) (warnError : Bool) :
    Py (Seq × Option String) := do
  let (r, fb) ← decodeEscape2 s errors
  match escapeWarning fb with
  | some m => if warnError then throw (.named "DeprecationWarning" m) else return (r, some m)
  | none => return (r, none)

/-- `bytes_partition_impl(self, sep)`, bytesobject.c:1899-1908, on `stringlib_partition`
(Objects/stringlib/partition.h:12-66, `STRINGLIB_MUTABLE` 0): the middle item is `sep->obj`, the
argument object itself (a bytearray separator stays a bytearray), and when the separator is not
found the first item is `self` (:32-53). The clinic `Py_buffer` converter refuses a non-buffer. -/
def bytesPartitionObj (s : Seq) (sep : Obj) : Py (Obj × Obj × Obj) :=
  match getBuffer sep with
  | .error e => .error e
  | .ok b =>
    if b.length = 0 then .error (.valueError "empty separator")
    else
      let pos := fastsearch s b (-1) .search
      if pos < 0 then .ok (.bytes s, .bytes [], .bytes [])
      else .ok (.bytes (s.take pos.toNat), sep, .bytes (s.drop (pos.toNat + b.length)))

/-- `bytes_rpartition_impl(self, sep)`, bytesobject.c:1927-1936, on `stringlib_rpartition`
(partition.h:69-125): the middle item is `sep->obj`, and when not found the last item is `self`. -/
def bytesRPartitionObj (s : Seq) (sep : Obj) : Py (Obj × Obj × Obj) :=
  match getBuffer sep with
  | .error e => .error e
  | .ok b =>
    if b.length = 0 then .error (.valueError "empty separator")
    else
      let pos := fastsearch s b (-1) .rsearch
      if pos < 0 then .ok (.bytes [], .bytes [], .bytes s)
      else .ok (.bytes (s.take pos.toNat), sep, .bytes (s.drop (pos.toNat + b.length)))

end PyLean.BytesObj.Bytes
