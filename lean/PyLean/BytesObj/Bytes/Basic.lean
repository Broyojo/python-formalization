import PyLean.BytesObj.Bytes.Format
import PyLean.BytesObj.Bytes.Hex
import PyLean.RangeSlice.Model

/-!
The methods of `bytes` that `PyLean.StrSearch` does not cover,
Objects/bytesobject.c, plus the object-level argument handling of the search
functions of Objects/bytes_methods.c.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch
open PyLean.RangeSlice (Slice sliceUnpack)

/-! ## Search plumbing, bytes_methods.c:403-430, :513-622, :676-720 -/

/-- `parse_args_finds_byte`, bytes_methods.c:403-430, on an object: a buffer is
kept, an index must be in `range(0, 256)`, anything else is a `TypeError`. -/
def parseFindsByteObj (sub : Obj) : Py BSub :=
  match sub.buffer? with
  | some b => .ok (.buf b)
  | none =>
    match sub.index? with
    | some (.ok v) => .ok (.byte v)
    | some (.error e) => .error e
    | none =>
      .error (.typeError s!"argument should be integer or bytes-like object, not '{sub.typeName}'")

/-- `_Py_bytes_find`, `_Py_bytes_rfind`, bytes_methods.c:512-545 with
`find_internal`, :452-510. -/
def bytesFindObj (s : Seq) (sub : Obj) (start «end» : Option Int) (forward : Bool) : Py Int := do
  let b ← parseFindsByteObj sub
  bytesFind s b start «end» forward

/-- `_Py_bytes_index`, `_Py_bytes_rindex`, bytes_methods.c:522-560. -/
def bytesIndexObj (s : Seq) (sub : Obj) (start «end» : Option Int) (forward : Bool) : Py Int := do
  let b ← parseFindsByteObj sub
  bytesIndex s b start «end» forward

/-- `_Py_bytes_count`, bytes_methods.c:562-599. -/
def bytesCountObj (s : Seq) (sub : Obj) (start «end» : Option Int) : Py Int := do
  let b ← parseFindsByteObj sub
  bytesCount s b start «end»

/-- `_Py_bytes_contains`, bytes_methods.c:601-622. Unlike `parse_args_finds_byte`
it tries the index first, and on a `PyNumber_AsSsize_t` failure falls back to the
buffer protocol, losing the original exception. -/
def bytesContains (s : Seq) (arg : Obj) : Py Bool :=
  let viaBuffer : Py Bool :=
    match getBuffer arg with
    | .error e => .error e
    | .ok b => .ok (decide (stringlibFind s b 0 ≥ 0))
  match arg.index? with
  | none | some (.error _) => viaBuffer
  | some (.ok v) =>
    let ival := clampSsize v
    if ival < 0 ∨ ival ≥ 256 then .error (.valueError "byte must be in range(0, 256)")
    else .ok (s.contains ival.toNat)

/-- `tailmatch`'s buffer step, bytes_methods.c:637-646. -/
def tailItem (item : Obj) : Py Seq := getBuffer item

/-- `_Py_bytes_tailmatch`, bytes_methods.c:675-706: a tuple tries each item in turn
(items after a match are not looked at); a failed non-tuple argument gets the
method's own message. -/
def bytesTailmatchObj (s : Seq) (fname : String) (subobj : Obj) (start «end» : Int)
    (direction : Bool) : Py Bool :=
  let rec loop : List Obj → Py Bool
    | [] => .ok false
    | item :: rest =>
      match tailItem item with
      | .error e => .error e
      | .ok p =>
        if bytesTailmatch s p start «end» direction then .ok true else loop rest
  match subobj with
  | .tuple items => loop items
  | _ =>
    match tailItem subobj with
    | .error _ =>
      .error (.typeError s!"{fname} first arg must be bytes or a tuple of bytes, not {subobj.typeName}")
    | .ok p => .ok (bytesTailmatch s p start «end» direction)

/-! ## `_PyBytes_Find`, bytesobject.c:1393-1426 -/

/-- `_PyBytes_Find(haystack, len_haystack, needle, len_needle, offset)`,
bytesobject.c:1393-1417. `stringlib_find` is called with one byte less so that it
never reads `haystack[len_haystack]`; the last alignment is compared by hand. -/
def privateBytesFind (hay needle : Seq) (offset : Int) : Int :=
  if needle.length = 0 then offset
  else if needle.length > hay.length then -1
  else
    let res := stringlibFind (hay.take (hay.length - 1)) needle offset
    if res = -1 then
      let lastAlign := hay.length - needle.length
      if (hay.drop lastAlign).take needle.length = needle then offset + lastAlign else res
    else res

/-- `_PyBytes_ReverseFind`, bytesobject.c:1419-1426. -/
def privateBytesRFind (hay needle : Seq) (offset : Int) : Int :=
  stringlibRFind hay needle offset

/-! ## Concatenation and repetition -/

/-- `bytes_concat`, bytesobject.c@3.14.7:1444-1486. -/
def bytesConcat (a b : Obj) : Py Seq :=
  match a.buffer?, b.buffer? with
  | some va, some vb =>
    if (va.length : Int) > ssizeMax - vb.length then .error memoryError
    else bytesFromStringAndSize (some (va ++ vb)) (va.length + vb.length)
  | _, _ => .error (.typeError s!"can't concat {b.typeName} to {a.typeName}")

/-- `bytes_repeat`, bytesobject.c:1579-1614, after the `sequence_repeat`
conversion of `n`. -/
def bytesRepeat (s : Seq) (n : Int) : Py Seq :=
  let n := if n < 0 then 0 else n
  if n > 0 ∧ (s.length : Int) > Int.tdiv ssizeMax n then
    .error (.overflowError "repeated bytes are too long")
  else
    let size := (s.length : Int) * n
    if size = s.length then .ok s
    else if mallocFails (bytesObjectSize + size) then .error memoryError
    else .ok (bytesRepeatFill size.toNat s)

/-- `b * n`, `sequence_repeat`, Objects/abstract.c:1157-1172: the count goes through
`PyNumber_AsSsize_t(n, PyExc_OverflowError)`. -/
def bytesMul (s : Seq) (n : Int) : Py Seq := do
  bytesRepeat s (← Sequences.repeatCount n)

/-! ## Comparison -/

inductive CmpOp where
  | lt | le | eq | ne | gt | ge
  deriving Repr, DecidableEq, Inhabited

/-- `Py_RETURN_RICHCOMPARE(a, b, op)`. -/
def richResult (op : CmpOp) (a b : Int) : Bool :=
  match op with
  | .lt => decide (a < b)
  | .le => decide (a ≤ b)
  | .eq => decide (a = b)
  | .ne => decide (a ≠ b)
  | .gt => decide (a > b)
  | .ge => decide (a ≥ b)

/-- `memcmp(a, b, n)`: the sign of the first difference, unsigned bytes. -/
def memcmp : Nat → Seq → Seq → Int
  | 0, _, _ => 0
  | n + 1, a :: as, b :: bs =>
    if a < b then -1 else if a > b then 1 else memcmp n as bs
  | _, _, _ => 0

/-- `bytes_compare_eq`, bytesobject.c:1633-1648. The first-byte shortcut reads the
NUL terminator for empty strings. -/
def bytesCompareEq (a b : Seq) : Bool :=
  if b.length ≠ a.length then false
  else if a.headD 0 ≠ b.headD 0 then false
  else decide (memcmp a.length a b = 0)

/-- `bytes_richcompare`, bytesobject.c:1650-1711, for two bytes objects. The
identity shortcut, :1672-1687, gives the same result as this code for equal
contents, so it is not a separate case. -/
def bytesRichcompare (a b : Seq) (op : CmpOp) : Bool :=
  if op = .eq ∨ op = .ne then
    let eq := bytesCompareEq a b
    if op = .ne then !eq else eq
  else
    let lenA : Int := a.length
    let lenB : Int := b.length
    let minLen := min a.length b.length
    let c : Int :=
      if minLen > 0 then
        let d := (a.headD 0 : Int) - (b.headD 0 : Int)
        if d = 0 then memcmp minLen a b else d
      else 0
    if c ≠ 0 then richResult op c 0 else richResult op lenA lenB

/-- `bytes.__lt__` etc., `none` for `NotImplemented`: non-bytes operands. -/
def bytesRichcompareObj (a b : Obj) (op : CmpOp) : Option Bool :=
  match a, b with
  | .bytes x, .bytes y => some (bytesRichcompare x y op)
  | _, _ => none

/-! ## Hash -/

/-- A `bytes` object: its contents and the cached hash, `ob_shash`
(`set_ob_shash`/`get_ob_shash`, bytesobject.c@3.14.7:56-80). `-1` means not computed. -/
structure BytesSt where
  data : Seq
  shash : Int := -1
  deriving Repr, DecidableEq, Inhabited

/-- `bytes_hash`, bytesobject.c:1713-1724: `(hash, object with the cache filled)`.
`hb` is `Py_HashBuffer`. -/
def bytesHash (hb : Seq → Int) (o : BytesSt) : Int × BytesSt :=
  if o.shash = -1 then
    let h := hb o.data
    (h, { o with shash := h })
  else (o.shash, o)

/-- `_PyBytes_Resize` on an object, bytesobject.c:3417-3484: failures are
`bytesResizeCheck`; the kept bytes are the first `newsize`, new ones are left for
the caller (read as zero), and the cached hash is invalidated. `newsize = oldsize`
returns early and keeps the hash. -/
def bytesResize (o : BytesSt) (newsize : Int) : Py BytesSt := do
  bytesResizeCheck o.data.length newsize
  if newsize = o.data.length then return o
  return { data := o.data.take newsize.toNat ++ List.replicate (newsize.toNat - o.data.length) 0 }

/-- `bytes_subtype_new`, bytesobject.c:3182-3199: the copy keeps the cached hash;
`bytes_alloc`, :3171-3180, sets it to -1 before that. -/
def bytesSubtypeNew (tmp : BytesSt) : BytesSt :=
  let pnew : BytesSt := { data := tmp.data, shash := -1 }
  { pnew with shash := tmp.shash }

/-! ## Subscript -/

/-- The positions of an extended slice: `cur = start; cur += step` as a `size_t`
cursor, bytesobject.c:1776-1779. -/
def slicePositions (start step : Int) (n : Nat) : List Int :=
  (List.range n).map (fun (i : Nat) => start + (i : Int) * step)

/-- `bytes_subscript` for a slice, bytesobject.c:1743-1783. -/
def bytesGetSlice (s : Seq) (sl : Slice) : Py Seq := do
  let (start, stop, step) ← sliceUnpack sl
  let (start, _, len) := RangeSlice.adjustIndices s.length start stop step
  if len ≤ 0 then return []
  if start = 0 ∧ step = 1 ∧ len = s.length then return s
  if step = 1 then return (s.drop start.toNat).take len.toNat
  return (slicePositions start step len.toNat).map (fun p => s.getD p.toNat 0)

/-- `bytes_subscript` for an index, bytesobject.c:1730-1742, and `bytes_item`,
:1622-1631. -/
def bytesGetItem (s : Seq) (i : Int) : Py Nat := do
  let i ← Sequences.subIndex i
  let i := if i < 0 then i + s.length else i
  if i < 0 ∨ i ≥ s.length then throw (.indexError "index out of range")
  return s.getD i.toNat 0

/-! ## join, stringlib/join.h -/

/-- `PySequence_Fast(iterable, "can only join an iterable")`: what the model can
iterate. A `bytes` argument yields ints. -/
def iterItems? (o : Obj) : Option (List Obj) :=
  match o with
  | .list xs | .tuple xs | .iter xs | .iterRaises xs _ | .iterHint xs _ => some xs
  | .bytes s | .bytearray s | .memview s _ => some (s.map (fun (c : Nat) => Obj.int (c : Int)))
  | .str cs => some (cs.map (fun c => Obj.str [c]))
  | .dict kv => some (kv.map (fun p => Obj.bytes p.1))
  | _ => none

/-- `PyObject_GetIter(o)`: the items, or the error of `__iter__`, where the callers turn a
`TypeError` into their own message `msg`. -/
def getIterOr (msg : PyExc) (o : Obj) : Py (List Obj) :=
  match o with
  | .iterCallRaises e => .error (if isTypeError e then msg else e)
  | _ =>
    match iterItems? o with
    | some xs => .ok xs
    | none => .error msg

/-- What ends an iteration: `PyIter_Next` failing after the last item. -/
def iterFinish (o : Obj) : Py Unit :=
  match o with
  | .iterRaises _ e => .error e
  | _ => .ok ()

/-- `PyObject_LengthHint(o, d)`, Objects/abstract.c:95-152, with the default `d` for a
sized object too (the difftest only sizes small ones, so the value does not matter). -/
def lengthHint (o : Obj) (d : Int) : Py Int :=
  match o with
  | .iterHint _ (.error e) => if isTypeError e then .ok d else .error e
  | .iterHint _ (.ok v) =>
    if v < ssizeMin ∨ v > ssizeMax then
      .error (.overflowError "Python int too large to convert to C ssize_t")
    else if v < 0 then .error (.valueError "__length_hint__() should return >= 0")
    else .ok v
  | _ => .ok d

/-- `PySequence_Fast(o, msg)`, Objects/abstract.c:2104-2129: an exact list or tuple as it
is, anything else through `PySequence_List`, which runs the iterator to its end first. -/
def sequenceFast (msg : PyExc) (o : Obj) : Py (List Obj) :=
  match o with
  | .list xs | .tuple xs => .ok xs
  | _ => do
    let xs ← getIterOr msg o
    let _ ← lengthHint o 8
    iterFinish o
    return xs

/-- The pre-pass of `stringlib_bytes_join`, join.h:52-103: the buffers in order, or
the error of the first bad item. -/
def joinPass (sep : Seq) : Nat → List Obj → Int → Py (List Seq × Int)
  | _, [], sz => .ok ([], sz)
  | i, item :: rest, sz =>
    match item.buffer? with
    | none =>
      .error (.typeError s!"sequence item {i}: expected a bytes-like object, {item.typeName} found")
    | some b =>
      let itemlen : Int := b.length
      if itemlen > ssizeMax - sz then .error (.overflowError "join() result is too long")
      else
        let sz := sz + itemlen
        if i ≠ 0 ∧ (sep.length : Int) > ssizeMax - sz then
          .error (.overflowError "join() result is too long")
        else
          let sz := if i ≠ 0 then sz + sep.length else sz
          match joinPass sep (i + 1) rest sz with
          | .ok (bs, total) => .ok (b :: bs, total)
          | .error e => .error e

/-- The concatenation of the buffers with `sep` between them, join.h:118-140. -/
def joinWrite (sep : Seq) : List Seq → Seq
  | [] => []
  | [b] => b
  | b :: rest => b ++ sep ++ joinWrite sep rest

/-- `stringlib_bytes_join(sep, iterable)`, join.h:7-154. `exactSingle` is the
`seqlen == 1` shortcut for `bytes` only (`!STRINGLIB_MUTABLE`), which returns the
item itself. -/
def stringlibJoin (sep : Seq) (iterable : Obj) : Py Seq :=
  match sequenceFast (.typeError "can only join an iterable") iterable with
  | .error e => .error e
  | .ok items =>
    match joinPass sep 0 items 0 with
    | .error e => .error e
    | .ok (bs, _) => .ok (joinWrite sep bs)

/-- `PyBytes_Join`, bytesobject.c:1994-2008, and `bytes_join_impl`, :1987-1992. -/
def pyBytesJoin (sep : Obj) (iterable : Obj) : Py Seq :=
  match sep with
  | .bytes s => stringlibJoin s iterable
  | _ => .error (.typeError s!"sep: expected bytes, got {sep.typeName}")

/-! ## translate -/

/-- The table argument: `none` is `None`. Reads shared by both implementations. -/
def tableArg (table : Obj) : Py (Option Seq) :=
  match table with
  | .none => .ok none
  | _ =>
    match getBuffer table with
    | .error e => .error e
    | .ok t => .ok (some t)

/-- The no-delete fast loop, bytesobject.c:2326-2343 and
bytearrayobject.c:1758-1765. -/
def translateFast (s t : Seq) : Seq := s.map (fun c => t.getD c 0)

/-- The general loop, bytesobject.c:2345-2372 and bytearrayobject.c:1767-1788:
`trans_table[c]` is `t[c]` (or `c` for no table), `-1` for a deleted byte. -/
def translateSlow (s : Seq) (t : Option Seq) (del : Seq) : Seq :=
  s.filterMap (fun c =>
    if del.contains c then none else some (match t with | some t => t.getD c 0 | none => c))

/-- `bytes_translate_impl`, bytesobject.c:2258-2373. -/
def bytesTranslate (s : Seq) (table : Obj) (deletechars : Option Obj) : Py Seq := do
  let t ← tableArg table
  if (t.map List.length).getD 256 ≠ 256 then
    throw (.valueError "translation table must be 256 characters long")
  let del ← match deletechars with
    | none => pure []
    | some d => getBuffer d
  match t, del with
  | some t, [] => return translateFast s t
  | _, _ => return translateSlow s t del

/-- `bytearray_translate_impl`, bytearrayobject.c:1709-1796: the same steps, except
that the table goes through `PyObject_GetBuffer` also for a `bytes` table. -/
def bytearrayTranslate (s : Seq) (table : Obj) (deletechars : Option Obj) : Py Seq := do
  let t ← match table with
    | .none => pure none
    | _ => do
      let v ← getBuffer table
      if v.length ≠ 256 then
        throw (.valueError "translation table must be 256 characters long")
      pure (some v)
  let del ← match deletechars with
    | none => pure []
    | some d => getBuffer d
  match t, del with
  | some t, [] => return translateFast s t
  | _, _ => return translateSlow s t del

/-! ## bytes iterator, bytesobject.c:3487-3642 -/

/-- `striterobject`: `seq = none` once exhausted. -/
structure StrIter where
  seq : Option Seq
  index : Int
  deriving Repr, DecidableEq, Inhabited

/-- `bytes_iter`, bytesobject.c:3626-3642. -/
def bytesIter (s : Seq) : StrIter := { seq := some s, index := 0 }

/-- `striter_next`, bytesobject.c:3514-3534. -/
def striterNext (it : StrIter) : Option Nat × StrIter :=
  match it.seq with
  | none => (none, it)
  | some s =>
    if it.index < s.length then (some (s.getD it.index.toNat 0), { it with index := it.index + 1 })
    else (none, { it with seq := none })

/-- `striter_len`, bytesobject.c:3536-3544. -/
def striterLen (it : StrIter) : Int :=
  match it.seq with
  | some s => (s.length : Int) - it.index
  | none => 0

/-- `striter_reduce`, bytesobject.c:3549-3563: `(seq, index)` or the empty tuple. -/
def striterReduce (it : StrIter) : Option (Seq × Int) :=
  it.seq.map (fun s => (s, it.index))

/-- `striter_setstate`, bytesobject.c:3567-3582. -/
def striterSetstate (it : StrIter) (state : Int) : Py StrIter := do
  let index ← Sequences.asSsize state
  match it.seq with
  | none => return it
  | some s =>
    let index : Int := if index < 0 then 0 else if index > s.length then s.length else index
    return { it with index }

/-! ## Object API -/

/-- The error of `PyBytes_Size`, `PyBytes_AsString` and
`PyBytes_AsStringAndSize`, bytesobject.c:1324-1371. -/
def expectedBytes (o : Obj) : PyExc := .typeError s!"expected bytes, {o.typeName} found"

/-- `PyBytes_Size`, bytesobject.c:1324-1333. -/
def pyBytesSize (o : Obj) : Py Nat :=
  match o with
  | .bytes s => .ok s.length
  | _ => .error (expectedBytes o)

/-- `PyBytes_AsString`, bytesobject.c:1335-1344: the buffer as a C string. -/
def pyBytesAsString (o : Obj) : Py Seq :=
  match o with
  | .bytes s => .ok s
  | _ => .error (expectedBytes o)

/-- `PyBytes_AsStringAndSize(obj, &s, len)`, bytesobject.c:1346-1371; `wantLen` is
`len != NULL`. Without a length the C string must equal the bytes. -/
def pyBytesAsStringAndSize (o : Obj) (wantLen : Bool) : Py Seq :=
  match o with
  | .bytes s =>
    if !wantLen ∧ (s.takeWhile (· != 0)).length ≠ s.length then
      .error (.valueError "embedded null byte")
    else .ok s
  | _ => .error (expectedBytes o)

/-- `PyBytes_Concat(pv, w)`, bytesobject.c:3274-3321, on the value of `*pv`; `none`
is NULL, with the exception raised where there is one. `unique` selects the in-place
branch (`_PyObject_IsUniquelyReferenced(*pv) && PyBytes_CheckExact(*pv)`), which
must agree with `bytes_concat`. -/
def pyBytesConcat (pv : Option Seq) (w : Option Obj) (unique : Bool) : Option Seq × Option PyExc :=
  match pv, w with
  | none, _ => (none, none)
  | some _, none => (none, none)
  | some v, some w =>
    if unique then
      match w.buffer? with
      | none =>
        (none, some (.typeError s!"can't concat {w.typeName} to {(Obj.bytes v).typeName}"))
      | some wb =>
        if (v.length : Int) > ssizeMax - wb.length then (none, some memoryError)
        else
          match bytesResize { data := v } (v.length + wb.length) with
          | .error e => (none, some e)
          | .ok o => (some (o.data.take v.length ++ wb), none)
    else
      match bytesConcat (.bytes v) w with
      | .ok r => (some r, none)
      | .error e => (none, some e)

/-- `PyBytes_FromFormatV` arguments. -/
inductive CArg where
  | int (v : Int)
  | str (s : Seq)
  | ptr (v : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- `s[i]` of a NUL-terminated C string. -/
def cAt (f : Seq) (i : Nat) : Nat := f.getD i 0

def skipDigits (f : Seq) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i => if isDigitC (cAt f i) then skipDigits f fuel (i + 1) else i

/-- The precision digits, bytesobject.c:234-236: `prec` in `Py_ssize_t`, which wraps
for absurdly long digit strings (`-fwrapv`). -/
def precDigits (f : Seq) : Nat → Nat → Int → Nat × Int
  | 0, i, p => (i, p)
  | fuel + 1, i, p =>
    if isDigitC (cAt f i) then
      precDigits f fuel (i + 1) (RangeSlice.wrap (RangeSlice.wrap (p * 10) + ((cAt f i : Int) - 48)))
    else (i, p)

def skipToConv (f : Seq) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i =>
    let c := cAt f i
    if c ≠ 0 ∧ c ≠ 37 ∧ !isAlphaC c then skipToConv f fuel (i + 1) else i

/-- `sprintf("%d")` for a value. -/
def cDecimal (v : Int) : Seq := (if v < 0 then [45] else []) ++ digitsOf v.natAbs

/-- `(int)v`. -/
def wrapInt (v : Int) : Int :=
  let m := v % (2 ^ 32)
  if m ≥ 2 ^ 31 then m - 2 ^ 32 else m

/-- The `%s` copy, bytesobject.c:315-326: `strlen`, or at most `prec` bytes. A
precision of 0 (`prec <= 0`) means no limit. -/
def cStringPrec (p : Seq) (prec : Int) : Seq :=
  let z := p.takeWhile (· != 0)
  if prec ≤ 0 then z else z.take prec.toNat

/-- The loop of `PyBytes_FromFormatV`, bytesobject.c:218-352. -/
def fromFormatLoop (f : Seq) : Nat → Nat → List CArg → Seq → Py Seq
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, i, args, out =>
    if cAt f i = 0 then .ok out
    else if cAt f i ≠ 37 then fromFormatLoop f fuel (i + 1) args (out ++ [cAt f i])
    else
      let p := i
      let i := skipDigits f f.length (i + 1)
      let (i, prec) : Nat × Int :=
        if cAt f i = 46 then precDigits f f.length (i + 1) 0 else (i, 0)
      let i := skipToConv f f.length i
      let next := cAt f (i + 1)
      let (i, longflag) : Nat × Bool :=
        if cAt f i = 108 ∧ (next = 100 ∨ next = 117) then (i + 1, true) else (i, false)
      let next := cAt f (i + 1)
      let (i, sizeflag) : Nat × Bool :=
        if cAt f i = 122 ∧ (next = 100 ∨ next = 117) then (i + 1, true) else (i, false)
      let wide := longflag || sizeflag
      let c := cAt f i
      let arg := args.headD (.int 0)
      let rest := args.drop 1
      let argInt : Int := match arg with | .int v => v | _ => 0
      if c = 99 then
        if argInt < 0 ∨ argInt > 255 then
          .error (.overflowError "PyBytes_FromFormatV(): %c format expects an integer in range [0; 255]")
        else fromFormatLoop f fuel (i + 1) rest (out ++ [argInt.toNat])
      else if c = 100 then
        let v := if wide then RangeSlice.wrap argInt else wrapInt argInt
        fromFormatLoop f fuel (i + 1) rest (out ++ cDecimal v)
      else if c = 117 then
        let v := argInt % (if wide then 2 ^ 64 else 2 ^ 32)
        fromFormatLoop f fuel (i + 1) rest (out ++ cDecimal v)
      else if c = 105 then
        fromFormatLoop f fuel (i + 1) rest (out ++ cDecimal (wrapInt argInt))
      else if c = 120 then
        fromFormatLoop f fuel (i + 1) rest (out ++ digitsBase 16 (argInt % (2 ^ 32)).toNat)
      else if c = 115 then
        let s : Seq := match arg with | .str s => s | _ => []
        fromFormatLoop f fuel (i + 1) rest (out ++ cStringPrec s prec)
      else if c = 112 then
        let v : Nat := match arg with | .ptr v => v | _ => 0
        fromFormatLoop f fuel (i + 1) rest (out ++ asc "0x" ++ digitsBase 16 v)
      else if c = 37 then
        fromFormatLoop f fuel (i + 1) args (out ++ [37])
      else
        -- invalid format string: copy unformatted string and exit
        .ok (out ++ (f.drop p).takeWhile (· != 0))

/-- `PyBytes_FromFormatV`, bytesobject.c@3.14.7:199-388, and `PyBytes_FromFormat`, :380-390.
`format` is a C string. -/
def bytesFromFormat (format : Seq) (args : List CArg) : Py Seq :=
  fromFormatLoop format (format.length + 1) 0 args []

end PyLean.BytesObj.Bytes
