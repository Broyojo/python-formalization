import PyLean.PyIO.BytesIO

/-!
`io.BytesIO`'s copy-on-write buffer (`Modules/_io/bytesio.c`, CPython 3.15.2), with
object identity.

`PyIO/BytesIO.lean` models the stream by value and assumes the program keeps no
reference to the objects it passes in or gets back. Here those references are part of
the state, because they decide what C does: `self->buf` is a `bytes` object that
`getvalue()`, `read()` and `readline()` may return without copying (bytesio.c:431-432,
:476-482), and `SHARED_BUF(self)` (`!_PyObject_IsUniquelyReferenced(self->buf)`,
bytesio.c:81) is how a later write or export knows it must copy first
(`unshare_buffer_lock_held`, :159-175). The state has:

* a heap of `bytes` objects with their contents and `ob_shash` (the cached hash, kept
  as the contents it was computed from, `none` for -1),
* `self->buf` as a reference (`none` once closed), `string_size`, `pos`,
* the program's `getbuffer()` memoryviews, each over the object and length it was
  exported with (`PyBuffer_FillInfo`, :1249-1251), `none` once released; `exports` is
  the number of live ones (`bytesiobuf_getbuffer` adds one, `bytesiobuf_releasebuffer`
  removes it, :1252, :1277),
* the program's references to `bytes` objects (`held`): what `getvalue`, `read` and
  `readline` returned and, if the program kept it, the initial value. The only other
  reference to a heap object is `self->buf` itself, so `SHARED_BUF` is "held by the
  program" for a heap object. Empty and one-byte `bytes` are the immortal singletons
  (Objects/bytesobject.c:132-139), never uniquely referenced, so always shared.

The bytes of an allocation beyond `string_size` are uninitialized in C; they are zeros
here. No operation shows them: `getvalue` first sizes the object to `string_size`
(:421-430), the zero-copy read needs `size == PyBytes_GET_SIZE(buf)` (:477), views
cover `string_size` bytes, and a write past the end pads with zeros (:271-282).

`resize_buffer_lock_held`'s `size <= alloc * 1.125` (:205) is a binary64 comparison; it
is `8 * size <= 9 * alloc` exactly while `alloc < 2 ** 49`, and every object here is
below `memLimit = 2 ** 47` bytes, because a larger allocation fails (`allocBytes`).

Scope: the default (GIL) build, where `set_shared_buf`/`clear_shared_buf` are empty; a
memoryview is used whole (no slices of it, which would share its export); `__init__`,
`__setstate__` and `readinto` are in `PyIO/BytesExtra.lean`. `_pyio.BytesIO` copies on
every `getvalue` and `read` (`bytes(self._buffer)`, _pyio.py:912, :948), so it has no
sharing to model.
-/

namespace PyLean.PyIO.Share

open PyLean PyLean.PyIO

/-- A `bytes` object: its contents and `ob_shash` (Objects/bytesobject.c:54-66), kept as
the contents the cached hash was computed from (`none` is -1, not yet computed). -/
structure BObj where
  data : List Nat
  hash : Option (List Nat)

/-- A reference to a `bytes` object: an immortal singleton (`b''` or one byte), or the
heap object with that index. Equal references are the same object (`is`). -/
inductive Ref where
  | single (d : List Nat)
  | heap (i : Nat)
  deriving Repr, DecidableEq

/-- A `getbuffer()` memoryview: the object and length `PyBuffer_FillInfo` gave it. -/
structure View where
  target : Ref
  len : Nat
  deriving Repr, DecidableEq

structure St where
  heap : Nat → BObj
  /-- Index of the next heap object. -/
  next : Nat
  /-- `self->buf`; `none` after `close()` (bytesio.c:890). -/
  buf : Option Ref
  /-- `self->string_size`. -/
  size : Nat
  pos : Nat
  views : List (Option View)
  held : List Ref

/-- Live views. -/
def liveCount (vs : List (Option View)) : Nat := vs.countP Option.isSome

/-- `self->exports`. -/
def St.exports (st : St) : Nat := liveCount st.views

def St.data (st : St) : Ref → List Nat
  | .single d => d
  | .heap i => (st.heap i).data

/-- `PyBytes_GET_SIZE(self->buf)`. -/
def St.alloc (st : St) : Nat :=
  match st.buf with
  | some r => (st.data r).length
  | none => 0

/-- `SHARED_BUF(self)` for `self->buf = r` (bytesio.c:81, the default build): another
reference exists. -/
def St.shared (st : St) : Ref → Bool
  | .single _ => true
  | .heap i => decide (Ref.heap i ∈ st.held)

/-- `get_ob_shash(v) != -1` (Objects/bytesobject.c:3454). -/
def St.hashed (st : St) : Ref → Bool
  | .single _ => false
  | .heap i => (st.heap i).hash.isSome

/-- A new heap object with contents `d` and no cached hash (`set_ob_shash(op, -1)`,
Objects/bytesobject.c:116); it is `.heap st.next`. -/
def St.newObj (st : St) (d : List Nat) : St :=
  { st with heap := fun j => if j = st.next then ⟨d, none⟩ else st.heap j, next := st.next + 1 }

/-- Writing into the memory of object `r` (`memcpy`, `memset`, a view's store, an
in-place `realloc`). The singletons are never written. -/
def St.setData (st : St) (r : Ref) (d : List Nat) : St :=
  match r with
  | .single _ => st
  | .heap i => { st with heap := fun j => if j = i then { st.heap i with data := d } else st.heap j }

/-- `PyBytes_FromStringAndSize(str, n)` with `str` pointing at `d`, Objects/bytesobject.c:124-148:
the singletons for `n <= 1` (:132-139), else a new object. Every `d` here is part of an
existing object, so below `memLimit`, and the allocation succeeds. -/
def St.fromBytes (st : St) (d : List Nat) : St × Ref :=
  if d.length ≤ 1 then (st, .single d) else (st.newObj d, .heap st.next)

/-- `unshare_buffer_lock_held(self, size)`, bytesio.c:159-175: a new object of `size` bytes
(`PyBytes_FromStringAndSize(NULL, size)`, whose `Py_ssize_t` argument is negative for a
`size_t` above `PY_SSIZE_T_MAX`, Objects/bytesobject.c:127-131, and which is the empty
singleton for 0, :137-139), the first `string_size` bytes copied, replacing `self->buf`. -/
def unshare (st : St) (size : Nat) : Py St :=
  match st.buf with
  | none => .ok st
  | some r =>
    if (size : Int) > ssizeMax then
      .error (.named "SystemError" "Negative size passed to PyBytes_FromStringAndSize") else
    if size = 0 then .ok { st with buf := some (.single []) } else
    match allocBytes size with
    | .error e => .error e
    | .ok () =>
      .ok { st.newObj ((st.data r).take st.size ++ List.replicate (size - st.size) 0) with
            buf := some (.heap st.next) }

/-- `resize_unshared_buffer_lock_held(self, size)`, bytesio.c:101-116, which is
`_PyBytes_ResizeKeepOnError(&self->buf, size)` (Objects/bytesobject.c:3418-3472): a bad
internal call for a negative size (:3423-3426), nothing for the same size (:3428-3434), a
new object when the old one is empty (:3436-3444), the empty singleton for 0
(:3446-3450), a copy when the object is shared or its hash is cached (:3452-3468), else
`bytes_resize_inplace` (:3359-3401, its checks at :3371-3374 and :3382-3383), which keeps the object. Every failure leaves it. -/
def resizeUnshared (st : St) (size : Int) : Py St :=
  match st.buf with
  | none => .ok st
  | some r =>
    let d := st.data r
    if size < 0 then
      .error (.named "SystemError" "Objects/bytesobject.c:3424: bad argument to internal function") else
    let n := size.toNat
    if d.length = n then .ok st else
    if d.length = 0 then
      match allocBytes n with
      | .error e => .error e
      | .ok () => .ok { st.newObj (List.replicate n 0) with buf := some (.heap st.next) }
    else if n = 0 then .ok { st with buf := some (.single []) }
    else if st.shared r || st.hashed r then
      match allocBytes n with
      | .error e => .error e
      | .ok () => .ok { st.newObj (d.take n ++ List.replicate (n - d.length) 0) with buf := some (.heap st.next) }
    else
      match allocBytes n with
      | .error e => .error e
      | .ok () => .ok (st.setData r (d.take n ++ List.replicate (n - d.length) 0))

/-- `alloc` of `resize_buffer_lock_held`, bytesio.c:197-212, for `size <= PY_SSIZE_T_MAX`:
`none` is the quick exit (:201-204). -/
def newAlloc (alloc size : Nat) : Option Nat :=
  if size < alloc / 2 then some (size + 1)
  else if size < alloc then none
  else if 8 * size ≤ 9 * alloc then some (size + size / 8 + (if size < 9 then 3 else 6))
  else some (size + 1)

/-- `resize_buffer_lock_held(self, size)`, bytesio.c:181-229: `OverflowError` above
`PY_SSIZE_T_MAX` (:194-195, :225-228), the new allocation size (:197-212), then
`unshare_buffer_lock_held` when shared (:214-217) or `resize_unshared_buffer_lock_held`
(:218-221), whose `Py_ssize_t` parameter is negative for `alloc = 2 ** 63`. -/
def resizeBuffer (st : St) (size : Nat) : Py St :=
  if (size : Int) > ssizeMax then .error (.overflowError "new buffer size too large") else
  match newAlloc st.alloc size with
  | none => .ok st
  | some a =>
    match st.buf with
    | none => .ok st
    | some r =>
      if st.shared r then unshare st a
      else resizeUnshared st (if (a : Int) > ssizeMax then (a : Int) - 2 ^ 64 else a)

/-- What `write_bytes_lock_held` does to `self->buf` before copying, bytesio.c:257-269: a
resize when the end passes the allocation, else an unshare when shared. -/
def writePrep (st : St) (r : Ref) (endpos : Nat) : Py St :=
  if endpos > (st.data r).length then resizeBuffer st endpos
  else if st.shared r then unshare st (max endpos st.size)
  else .ok st

/-- The copy of `write_bytes_lock_held`, bytesio.c:271-292, into the memory of `self->buf`:
the zero padding of an overseek, then the bytes; `st` is the state before the prep. -/
def writeInto (st st1 : St) (b : List Nat) : St × Py Val :=
  match st1.buf with
  | none => (st, .error C.closedErr)
  | some r1 =>
    let endpos := st1.pos + b.length
    let d := st1.data r1
    let d := if st1.pos > st1.size
      then d.take st1.size ++ List.replicate (st1.pos - st1.size) 0 ++ d.drop st1.pos else d
    let d := d.take st1.pos ++ b ++ d.drop endpos
    ({ st1.setData r1 d with pos := endpos, size := max st1.size endpos }, .ok (.int b.length))

/-- `write_bytes_lock_held`, bytesio.c:236-297, for a `bytes` argument the program does not
keep (its buffer export cannot fail or run code): closed and exports checks (:246), an
empty write (:251-254), a resize when the end passes the allocation (:257-263), else an
unshare when shared (:264-269), then the zero padding of an overseek (:271-282) and the
copy (:286-292), both into the memory of `self->buf`. -/
def write (st : St) (b : List Nat) : St × Py Val :=
  match st.buf with
  | none => (st, .error C.closedErr)
  | some r =>
    if st.exports > 0 then (st, .error bufferError) else
    if b.length = 0 then (st, .ok (.int 0)) else
    match writePrep st r (st.pos + b.length) with
    | .error e => (st, .error e)
    | .ok st1 => writeInto st st1 b

/-- `self->buf` sized to `string_size` before `getvalue` returns it, bytesio.c:421-430. -/
def sizePrep (st : St) (r : Ref) : Py St :=
  if st.size ≠ (st.data r).length then
    (if st.shared r then unshare st st.size else resizeUnshared st st.size)
  else .ok st

/-- `_io_BytesIO_getvalue_impl`, bytesio.c:413-433: a copy when `string_size <= 1` or a view
exists (:417-419); otherwise `self->buf`, first sized to `string_size` by an unshare or a
resize (:421-430), is returned itself (:431-432). The program keeps the result. -/
def getvalue (st : St) : St × Py Val :=
  match st.buf with
  | none => (st, .error C.closedErr)
  | some r =>
    let c := (st.data r).take st.size
    if st.size ≤ 1 ∨ st.exports > 0 then
      ({ (st.fromBytes c).1 with held := st.held ++ [(st.fromBytes c).2] }, .ok (.bytes c))
    else
      match sizePrep st r with
      | .error e => (st, .error e)
      | .ok st1 =>
        match st1.buf with
        | none => (st, .error C.closedErr)
        | some r1 => ({ st1 with held := st1.held ++ [r1] }, .ok (.bytes (st1.data r1)))

/-- `read_bytes_lock_held(self, size)`, bytesio.c:468-494, `size <= string_size - pos`:
`self->buf` itself when it is exactly the `size` bytes from 0 and no view exists
(:476-482), the empty singleton for 0 (:487-489), else a copy (:491-493). -/
def readBytes (st : St) (size : Nat) : St × Ref :=
  match st.buf with
  | none => (st, .single [])
  | some r =>
    if size > 1 ∧ st.pos = 0 ∧ size = (st.data r).length ∧ st.exports = 0 then
      ({ st with pos := st.pos + size }, r)
    else if size = 0 then (st, .single [])
    else ({ (st.fromBytes (slice (st.data r) st.pos size)).1 with pos := st.pos + size },
          (st.fromBytes (slice (st.data r) st.pos size)).2)

/-- The by-value view of the state, on which `PyIO/BytesIO.lean`'s `C.scanEol` and `C.seek`
run (they read only the contents, `pos` and the closed flag). -/
def St.proj (st : St) : BState :=
  ⟨match st.buf with | some r => (st.data r).take st.size | none => [],
   st.pos, st.buf.isNone, st.exports, match st.buf with | some r => st.shared r | none => false⟩

/-- Keep the reference `r` that an operation returned. -/
def keepRes (st : St) (r : Ref) : St × Py Val :=
  ({ st with held := st.held ++ [r] }, .ok (.bytes (st.data r)))

/-- `_io_BytesIO_read_impl`, bytesio.c:509-525, after the clinic `Py_ssize_t` conversion. -/
def read (st : St) (size : Option Int) : St × Py Val :=
  match optSsize (-1) size with
  | .error e => (st, .error e)
  | .ok size =>
    if st.buf.isNone then (st, .error C.closedErr) else
    let n : Int := (st.size : Int) - st.pos
    let size : Int := if size < 0 ∨ size > n then (if n < 0 then 0 else n) else size
    let (st', r) := readBytes st size.toNat
    keepRes st' r

/-- `_io_BytesIO_readline_impl`, bytesio.c:561-571. -/
def readline (st : St) (size : Option Int) : St × Py Val :=
  match optSsize (-1) size with
  | .error e => (st, .error e)
  | .ok size =>
    if st.buf.isNone then (st, .error C.closedErr) else
    let (st', r) := readBytes st (C.scanEol st.proj size)
    keepRes st' r

/-- The new size of `truncate`: `pos` for `None` (:700-701), else `PyLong_AsLong` (:703-707). -/
def truncArg (st : St) : Option Int → Py Int
  | none => .ok st.pos
  | some v => asLong v

/-- `_io_BytesIO_truncate_impl`, bytesio.c:692-727, for `None` or an int: `string_size` is
set before `resize_buffer_lock_held` (:716-722), which may shrink or replace the object,
and restored if it fails. -/
def truncate (st : St) (size : Option Int) : St × Py Val :=
  if st.buf.isNone then (st, .error C.closedErr) else
  if st.exports > 0 then (st, .error bufferError) else
  match truncArg st size with
  | .error e => (st, .error e)
  | .ok n =>
    if n < 0 then (st, .error (.valueError s!"negative size value {n}")) else
    if n < st.size then
      match resizeBuffer { st with size := n.toNat } n.toNat with
      | .error e => (st, .error e)
      | .ok st1 => (st1, .ok (.int n))
    else (st, .ok (.int n))

/-- The unshare before the first export of a shared buffer, bytesio.c:1243-1246. -/
def exportPrep (st : St) (r : Ref) : Py St :=
  if st.exports = 0 ∧ st.shared r = true then unshare st st.size else .ok st

/-- `_io_BytesIO_getbuffer_impl` (bytesio.c:386-403) and `bytesiobuf_getbuffer_lock_held`
(:1236-1254): `CHECK_CLOSED`, then the first export of a shared buffer unshares it
(:1243-1246), and the view is `string_size` writable bytes of `self->buf` (:1249-1251). -/
def getbuffer (st : St) : St × Py Val :=
  match st.buf with
  | none => (st, .error C.closedErr)
  | some r =>
    match exportPrep st r with
    | .error e => (st, .error e)
    | .ok st1 =>
      match st1.buf with
      | none => (st, .error C.closedErr)
      | some r1 => ({ st1 with views := st1.views ++ [some ⟨r1, st1.size⟩] }, .ok .none)

def releasedErr : PyExc := .valueError "operation forbidden on released memoryview object"

/-- `views[v][i] = x` (Objects/memoryobject.c `memory_ass_sub`): released views refuse,
then the index, then the value; the byte is stored into the exported object's memory. -/
def viewSet (st : St) (v i x : Nat) : St × Py Val :=
  match st.views[v]? with
  | some (some w) =>
    if i < w.len then
      if x < 256 then (st.setData w.target ((st.data w.target).set i x), .ok .none)
      else (st, .error (.valueError "memoryview: invalid value for format 'B'"))
    else (st, .error (.indexError "index out of bounds on dimension 1"))
  | _ => (st, .error releasedErr)

/-- `bytes(views[v])`: the view's bytes now. -/
def viewBytes (st : St) (v : Nat) : St × Py Val :=
  match st.views[v]? with
  | some (some w) => (st, .ok (.bytes ((st.data w.target).take w.len)))
  | _ => (st, .error releasedErr)

/-- `views[v].release()`: `bytesiobuf_releasebuffer` (:1273-1278) drops the export; a
released view does nothing. -/
def release (st : St) (v : Nat) : St × Py Val :=
  match st.views[v]? with
  | some (some _) => ({ st with views := st.views.set v none }, .ok .none)
  | _ => (st, .ok .none)

/-- `hash(x) == hash(bytes(bytearray(x)))` for the `h`-th kept object `x`: `bytes_hash`
(Objects/bytesobject.c:1714-1724) returns the cached hash or computes and caches it; the
fresh copy hashes its contents. The singletons are never written, so their hash is right. -/
def hashOp (st : St) (h : Nat) : St × Py Val :=
  match st.held[h]? with
  | some (.heap i) =>
    let o := st.heap i
    let hv := o.hash.getD o.data
    ({ st with heap := fun j => if j = i then { o with hash := some hv } else st.heap j },
     .ok (.bool (decide (hv = o.data))))
  | _ => (st, .ok (.bool true))

inductive SOp where
  | write (b : List Nat)
  | getvalue
  | read (n : Option Int)
  | readline (n : Option Int)
  | seek (p w : Int)
  | tell
  | truncate (n : Option Int)
  | getbuffer
  | viewSet (v i x : Nat)
  | viewBytes (v : Nat)
  | release (v : Nat)
  | close
  | closed
  /-- `del held[h]`. -/
  | drop (h : Nat)
  | hash (h : Nat)
  /-- `held[h] is held[k]`. -/
  | same (h k : Nat)
  deriving Repr, DecidableEq

def step (st : St) : SOp → St × Py Val
  | .write b => write st b
  | .getvalue => getvalue st
  | .read n => read st n
  | .readline n => readline st n
  | .seek p w =>
    let (s', r) := C.seek st.proj p w
    ({ st with pos := s'.pos }, r)
  | .tell => if st.buf.isNone then (st, .error C.closedErr) else (st, .ok (.int st.pos))
  | .truncate n => truncate st n
  | .getbuffer => getbuffer st
  | .viewSet v i x => viewSet st v i x
  | .viewBytes v => viewBytes st v
  | .release v => release st v
  | .close => if st.exports > 0 then (st, .error bufferError) else ({ st with buf := none }, .ok .none)
  | .closed => (st, .ok (.bool st.buf.isNone))
  | .drop h => ({ st with held := st.held.eraseIdx h }, .ok .none)
  | .hash h => hashOp st h
  | .same h k => (st, .ok (.bool (decide (st.held[h]? = st.held[k]?))))

/-- `io.BytesIO(x)` for `x = bytes(init)`: `bytesio_new` then `__init__`, which stores `x`
itself (bytesio.c:1097-1101); the program keeps `x` or deletes it. -/
def start (init : List Nat) (keep : Bool) : St :=
  let r : Ref := if init.length ≤ 1 then .single init else .heap 0
  { heap := fun _ => ⟨init, none⟩, next := 1, buf := some r, size := init.length, pos := 0,
    views := [], held := if keep then [r] else [] }

def runS (init : List Nat) (keep : Bool) (ops : List SOp) : St × List (Py Val) :=
  runOps step (start init keep) ops

end PyLean.PyIO.Share
