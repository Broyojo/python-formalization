import PyLean.BytesObj.Mem.State

/-!
The `memoryview` object, `Objects/memoryobject.c` (CPython 3.15.2), function by function
in source order. Line numbers refer to that file unless stated otherwise.

`Obj` is the Python object an operation receives. The constructors `index`, `floatLike`,
`boolLike` and `exporter` run Python code (`__index__`, `__float__`, `__bool__`,
`__buffer__`), which is what makes the `CHECK_RELEASED_AGAIN` macros necessary (gh-92888).
Such a callback first does `m.release()` on view `i` when `rel = some i`, ignoring
`BufferError`, and then ends as `Ret` says: it returns a value, raises, or returns an
object of the wrong type, which the C caller reports.
-/

namespace PyLean.BytesObj.Mem

open PyLean
open PyLean.RangeSlice (Slice sliceUnpack adjustIndices wrap)

/-- How a Python-level callback ends. -/
inductive Ret (α : Type) where
  | val (a : α)
  | raises (e : PyExc)
  /-- It returned an object of this type, not the one the C caller needs. -/
  | wrong (typeName : String)
  deriving Repr, DecidableEq, Inhabited

/-- A Python object as an argument. -/
inductive Obj where
  | int (n : Int)
  | bool (b : Bool)
  | float (bits : Nat)
  | bytes (b : List Nat)
  | str (s : List Char)
  | none
  /-- A list with `n` items; only `len()` is used. -/
  | list (n : Nat)
  /-- A memoryview. -/
  | view (i : Nat)
  /-- A buffer exporter already laid out in the store. -/
  | exporter (b : Ret Buf) (rel : Option Nat)
  /-- A `complex`, as two 64-bit IEEE patterns. -/
  | complex (re im : Nat)
  /-- An object with `__index__`. -/
  | index (n : Ret Int) (rel : Option Nat)
  /-- An object with `__float__`. -/
  | floatLike (bits : Ret Nat) (rel : Option Nat)
  /-- An object with `__bool__`. -/
  | boolLike (b : Ret Bool) (rel : Option Nat)
  /-- An object with `__len__`, as the `sep` of `hex`. -/
  | lenLike (n : Ret Int) (rel : Option Nat)
  /-- An object with `__eq__`, as the value of `count` and `index`. -/
  | eqLike (b : Ret Bool) (rel : Option Nat)
  deriving Repr, DecidableEq, Inhabited

def Obj.typeName : Obj → String
  | .int _ => "int"
  | .bool _ => "bool"
  | .float _ => "float"
  | .complex _ _ => "complex"
  | .bytes _ => "bytes"
  | .str _ => "str"
  | .none => "NoneType"
  | .list _ => "list"
  | .view _ => "memoryview"
  | .exporter _ _ => "Exporter"
  | .index _ _ => "Idx"
  | .floatLike _ _ => "Flt"
  | .boolLike _ _ => "Bln"
  | .lenLike _ _ => "Len"
  | .eqLike _ _ => "Eql"

/-- A part of a slice object. -/
inductive SlicePart where
  | start | stop | step
  deriving Repr, DecidableEq, Inhabited

/-- A part of a slice whose `__index__` fails, or that has none. -/
structure SliceFail where
  part : SlicePart
  how : Ret Unit
  deriving Repr, DecidableEq, Inhabited

/-- One element of a subscript. -/
inductive KeyElem where
  | obj (o : Obj)
  /-- A slice object. `rel` is the callback of an `__index__` among its parts, on `fail`'s
  part if there is one and otherwise on the first part that is not `None`. -/
  | slice (s : Slice) (rel : Option Nat) (fail : Option SliceFail := none)
  deriving Repr, DecidableEq, Inhabited

/-- A subscript: `m[x]`, `m[x, y, ...]` or `m[...]`. -/
inductive Key where
  | one (e : KeyElem)
  | tuple (es : List KeyElem)
  | ellipsis
  deriving Repr, DecidableEq, Inhabited

/-! ## ManagedBuffer object -/

/-- `mbuf_alloc`, :71-86: a fresh managed buffer, returned by number. -/
def mbufAlloc : M Nat := fun st =>
  (.ok st.mbufs.length, { st with mbufs := st.mbufs ++ [{}] })

/-- `PyBuffer_Release(view)` when `obj` is a memoryview: `memory_releasebuf`, :1637-1644. -/
def pyBufferRelease0 (b : Buf) : M Unit := fun st =>
  match b.obj with
  | some (.mv i) =>
    let x := st.mv i
    (.ok (), st.setMv i { x with exports := x.exports - 1 })
  | _ => (.ok (), st)

/-- `PyBuffer_Release(view)`, Objects/abstract.c: `bf_releasebuffer`, which for a Python
exporter is `__release_buffer__` (typeobject.c:11515-11565), whose exceptions are not
raised (`PyErr_FormatUnraisable`), then the drop of `view->obj`. The callback here does
`m.release()`, ignoring `BufferError`; `rel` is that release. -/
def hookRelease (rel : Nat → M Unit) (b : Buf) : M Unit := fun st =>
  match b.hook with
  | some t =>
    let st := if (st.mv t).exports = 0 then (rel t st).2 else st
    pyBufferRelease0 b st
  | none => pyBufferRelease0 b st

/-- `mbuf_release` with the callback's release `rel`. -/
def mbufReleaseWith (rel : Nat → M Unit) (k : Nat) : M Unit := fun st =>
  let x := st.mb k
  if x.released then (.ok (), st)
  else hookRelease rel x.master (st.setMb k { x with released := true })

/-- `_memory_release` as a callback sees it, to any depth: a callback's release can release a
buffer whose own callback runs, and so on. Each level has marked a view released before it goes
deeper, and a view marked already stops at once, so a chain is no longer than the number of views. -/
def memoryReleaseAt : Nat → Nat → M Unit
  | 0, _ => fun st => (.ok (), st)
  | f + 1, i => fun st =>
    let x := st.mv i
    if x.flags.released then (.ok (), st)
    else
      let st := st.setMv i { x with flags := { x.flags with released := true } }
      let b := st.mb x.mbuf
      let e := b.exports - 1
      let st := st.setMb x.mbuf { b with exports := e }
      if e = 0 then mbufReleaseWith (memoryReleaseAt f) x.mbuf st else (.ok (), st)

/-- `_memory_release` as a `__release_buffer__` callback sees it. -/
def memoryRelease0 (i : Nat) : M Unit := fun st => memoryReleaseAt st.mvs.length i st

/-- `PyBuffer_Release(view)`, with the callback's release to any depth. -/
def pyBufferRelease (b : Buf) : M Unit := fun st =>
  match b.hook with
  | some t =>
    let st := if (st.mv t).exports = 0 then (memoryRelease0 t st).2 else st
    pyBufferRelease0 b st
  | none => pyBufferRelease0 b st

/-- `mbuf_release`, :174-180. -/
def mbufRelease (k : Nat) : M Unit := fun st =>
  let x := st.mb k
  if x.released then (.ok (), st)
  else pyBufferRelease x.master (st.setMb k { x with released := true })

/-- `mbuf_clear`, :138-145. -/
def mbufClear (k : Nat) : M Unit := mbufRelease k

/-! ## Release (:1176-1272) -/

/-- `_memory_release`, :1180-1192. -/
def memoryRelease (i : Nat) : M Unit := fun st =>
  let x := st.mv i
  if x.flags.released then (.ok (), st)
  else
    let st := st.setMv i { x with flags := { x.flags with released := true } }
    let b := st.mb x.mbuf
    let e := b.exports - 1
    let st := st.setMb x.mbuf { b with exports := e }
    if e = 0 then mbufRelease x.mbuf st else (.ok (), st)

/-- `get_exports`, :1162-1170. -/
def getExports (st : St) (i : Nat) : Int := (st.mv i).exports

/-- `memoryview_release_impl`, :1200-1225. -/
def memoryviewRelease (i : Nat) : M Unit := fun st =>
  let e := getExports st i
  if e = 0 then memoryRelease i st
  else if e > 0 then
    (.error (bufferError s!"memoryview has {e} exported buffer{if e = 1 then "" else "s"}"), st)
  else (.error (systemError "memoryview: negative export count"), st)

/-- `memory_dealloc`, :1227-1238: the last reference to a view goes away. After the
release, `PyObject_ClearWeakRefs` (:1235-1236) runs the callback of a weakref to it. -/
def memoryDealloc (i : Nat) : M Unit := fun st =>
  let cb := (st.mv i).weakcb
  match memoryRelease i st with
  | (r, s) =>
    match cb with
    | some t => if getExports s t = 0 then (memoryRelease t s) else (r, s)
    | none => (r, s)

/-- `mbuf_dealloc`, :119-128: `mbuf_release` and the frees. A released managed buffer is
left alone, so this is the release of a buffer no view ever kept: :889-890, :918-919. -/
def mbufDealloc (k : Nat) : M Unit := mbufRelease k

/-- `memory_clear`, :1248-1259: a view in a reference cycle. -/
def memoryClear (i : Nat) : M Unit := fun st =>
  if getExports st i = 0 then memoryRelease i st else (.ok (), st)

/-- `memory_enter`, :1261-1266. -/
def memoryEnter (i : Nat) : M Nat := do
  checkReleased i
  return i

/-- `memory_exit`, :1268-1272. -/
def memoryExit (i : Nat) : M Unit := memoryviewRelease i

/-- Python callback of an argument object: `m.release()`, `BufferError` swallowed. -/
def fire : Option Nat → M Unit
  | none => pure ()
  | some i => fun st => if getExports st i = 0 then memoryRelease i st else (.ok (), st)

/-- The end of a callback. `wrong` is the error text the C caller gives for a result of
the wrong type. -/
def Ret.get {α : Type} (wrong : String → PyExc) : Ret α → M α
  | .val a => pure a
  | .raises e => throw e
  | .wrong t => throw (wrong t)

theorem Ret.get_state {α : Type} (w : String → PyExc) (r : Ret α) (st : St) : (r.get w st).2 = st := by
  cases r <;> rfl

theorem Ret.get_val {α : Type} (w : String → PyExc) (a : α) (st : St) :
    (Ret.val a).get w st = (.ok a, st) := rfl

/-- `__buffer__` returned something other than a memoryview, typeobject.c:11432-11433. -/
def bufferWrong (t : String) : PyExc := .typeError s!"Exporter.__buffer__() must return a memoryview, not {t}"

/-! ## Registering views -/

/-- `memory_alloc`, :681-704, with the view filled in by the caller. Returns its number. -/
def memoryAlloc (x : MV) : M Nat := fun st =>
  (.ok st.mvs.length, { st with mvs := st.mvs ++ [x] })

def bumpMbuf (k : Nat) : M Unit := fun st =>
  let b := st.mb k
  (.ok (), st.setMb k { b with exports := b.exports + 1 })

/-- `mbuf_add_view`, :714-744. -/
def mbufAddView (k : Nat) (src : Option Buf) : M Nat := do
  let st ← M.get
  let src := src.getD (st.mb k).master
  if src.ndim > 64 then
    throw (.valueError "memoryview: number of dimensions must not exceed 64")
  let (sh, stridesOut) := initShapeStrides src
  let dest : Buf := { initSharedValues { ndim := src.ndim } src with
    shape := sh, strides := stridesOut, suboffsets := initSuboffsets src }
  let i ← memoryAlloc { mbuf := k, view := dest, flags := initFlags dest }
  bumpMbuf k
  return i

/-- `mbuf_add_incomplete_view`, :751-790. -/
def mbufAddIncompleteView (k : Nat) (src : Option Buf) (ndim : Nat) : M Nat := do
  let st ← M.get
  let src := src.getD (st.mb k).master
  let i ← memoryAlloc { mbuf := k, view := initSharedValues { ndim := ndim } src }
  bumpMbuf k
  return i

/-! ## Buffer requests -/

def bufWritable : Nat := 0x0001
def bufFormat : Nat := 0x0004
def bufND : Nat := 0x0008
def bufStrides : Nat := 0x0010 ||| bufND
def bufCContiguous : Nat := 0x0020 ||| bufStrides
def bufFContiguous : Nat := 0x0040 ||| bufStrides
def bufAnyContiguous : Nat := 0x0080 ||| bufStrides
def bufIndirect : Nat := 0x0100 ||| bufStrides
def bufFullRO : Nat := bufIndirect ||| bufFormat

def req (flags x : Nat) : Bool := (flags &&& x) == x

/-- `view->format = NULL` without `PyBUF_FORMAT`, :1652-1659. -/
def viewFormat (flags : Nat) (v : Buf) : Buf :=
  if (flags &&& bufFormat) == 0 then { v with format := none } else v

/-- `view->strides = NULL` without `PyBUF_STRIDES`, :1681-1688. -/
def viewStrides (flags : Nat) (v : Buf) : Buf :=
  if !req flags bufStrides then { v with strides := none } else v

/-- `view->ndim = 1; view->shape = NULL` without `PyBUF_ND`, :1689-1704. -/
def viewShape (flags : Nat) (v : Buf) : Buf :=
  if !req flags bufND then { v with ndim := 1, shape := none } else v

/-- The checks of `memory_getbuf`, :1643-1704, on `*view = *base`, in order. -/
def getbufView (base : Buf) (baseflags : Flags) (flags : Nat) : Py Buf :=
  if (flags &&& bufWritable) != 0 && base.readonly then
    .error (bufferError "memoryview: underlying buffer is not writable")
  else
  let view := viewFormat flags { base with obj := none }
  if req flags bufCContiguous && !baseflags.isC then
    .error (bufferError "memoryview: underlying buffer is not C-contiguous")
  else if req flags bufFContiguous && !baseflags.isF then
    .error (bufferError "memoryview: underlying buffer is not Fortran contiguous")
  else if req flags bufAnyContiguous && !baseflags.isAny then
    .error (bufferError "memoryview: underlying buffer is not contiguous")
  else if !req flags bufIndirect && baseflags.pil then
    .error (bufferError "memoryview: underlying buffer requires suboffsets")
  else if !req flags bufStrides && !baseflags.isC then
    .error (bufferError "memoryview: underlying buffer is not C-contiguous")
  else
  let view := viewStrides flags view
  if !req flags bufND && view.format.isSome then
    .error (bufferError "memoryview: cannot cast to unsigned bytes if the format flag is present")
  else
  .ok (viewShape flags view)

/-- `memory_getbuf`, :1628-1711. `*view = *base` is a copy; the export is counted only
on success. The memoryview itself becomes `view->obj`. -/
def memoryGetbuf (self : Nat) (flags : Nat) : M Buf := do
  checkReleased self
  checkRestricted self
  let st ← M.get
  let x := st.mv self
  let view ← M.lift (getbufView x.view x.flags flags)
  M.modify fun st =>
    let y := st.mv self
    st.setMv self { y with exports := y.exports + 1 }
  -- the release of this export runs `memory_releasebuf`, not the exporter's hook
  return { view with obj := some (.mv self), hook := Option.none }

/-- `memory_releasebuf`, :1713-1720. -/
def memoryReleasebuf (self : Nat) : M Unit := pyBufferRelease { obj := some (.mv self) }

/-- `PyBuffer_FillInfo`, abstract.c, and the same logic in `array_buffer_getbuf`, for an
exporter whose full description is `b`. -/
def simpleGetbuffer (b : Buf) (flags : Nat) : Py Buf :=
  if req flags bufWritable && b.readonly then .error (bufferError "Object is not writable.")
  else .ok { b with
    format := if req flags bufFormat then b.format else none,
    shape := if req flags bufND then b.shape else none,
    strides := if req flags bufStrides then b.strides else none,
    suboffsets := if req flags bufIndirect then b.suboffsets else none }

/-- The bytes object `b` placed at the end of the store, as `PyBuffer_FillInfo` with
`PyBUF_FULL_RO` describes it. -/
def bytesBuf (b : List Nat) : M Buf := fun st =>
  let a : Int := st.mem.length
  (.ok { obj := some (.exp 1000000), buf := a, len := b.length, itemsize := 1, readonly := true,
         ndim := 1, format := some ['B'], shape := some [b.length], strides := some [1] },
   { st with mem := st.mem ++ b })

/-- `PyObject_GetBuffer(o, &buf, PyBUF_FULL_RO)`: a TypeError for a non-exporter. -/
def getBufferFull (o : Obj) : M Buf :=
  match o with
  | .view i => memoryGetbuf i bufFullRO
  | .bytes b => bytesBuf b
  | .exporter r rel => do
    fire rel
    -- `__buffer__` of the wrapper class returns `memoryview(exporter)`
    let b ← r.get bufferWrong
    if b.ndim > 64 then
      throw (.valueError "memoryview: number of dimensions must not exceed 64")
    return b
  | o => throw (.typeError s!"a bytes-like object is required, not '{o.typeName}'")

/-! ## Constructors -/

/-- `_PyManagedBuffer_FromObject`, :88-104, for an exporter described by `b`. -/
def managedBufferFromObject (b : Buf) (flags : Nat) : M Nat := do
  let k ← mbufAlloc
  let master ← M.lift (simpleGetbuffer b flags)
  M.modify fun st => st.setMb k { st.mb k with master := master }
  return k

/-- The exporter path of `PyMemoryView_FromObjectAndFlags`, :884-892: on failure of
`mbuf_add_view` the `Py_DECREF(mbuf)` releases the master. -/
def viewOfExporter (b : Buf) (flags : Nat) : M Nat := do
  let k ← managedBufferFromObject b flags
  M.onError (mbufAddView k none) (mbufDealloc k)

/-- `PyMemoryView_FromObjectAndFlags`, :873-898. -/
def memoryViewFromObjectAndFlags (v : Obj) (flags : Nat) : M Nat :=
  match v with
  | .view i => do
    checkReleased i
    checkRestricted i
    let st ← M.get
    mbufAddView (st.mv i).mbuf (some (st.mv i).view)
  | .bytes b => do
    let e ← bytesBuf b
    viewOfExporter e flags
  | .exporter r rel => do
    fire rel
    viewOfExporter (← r.get bufferWrong) flags
  | o => throw (.typeError s!"memoryview: a bytes-like object is required, not '{o.typeName}'")

/-- `PyMemoryView_FromObject`, :926-930. -/
def memoryViewFromObject (v : Obj) : M Nat := memoryViewFromObjectAndFlags v bufFullRO

/-- `memoryview_impl`, :1086-1091 (`memoryview(object)`). -/
def memoryviewNew (v : Obj) : M Nat := memoryViewFromObject v

/-- `memoryview__from_flags_impl`, :1104-1109. -/
def memoryviewFromFlags (v : Obj) (flags : Nat) : M Nat := memoryViewFromObjectAndFlags v flags

/-- `_PyMemoryView_FromBufferProc`, :904-921, for any `bufferproc`. If it fails, `master.obj`
is cleared and the `Py_DECREF(mbuf)` releases nothing. -/
def bufferProc (proc : M Buf) : M Nat := do
  let k ← mbufAlloc
  let master ← proc
  M.modify fun st => st.setMb k { st.mb k with master := master }
  M.onError (mbufAddView k none) (mbufDealloc k)

/-- `m.__buffer__(flags)`: `wrap_buffer`, Objects/typeobject.c:10446-10465, with `memory_getbuf`
as the buffer proc. -/
def memoryBufferProc (self : Nat) (flags : Nat) : M Nat := bufferProc (memoryGetbuf self flags)

/-- `PyMemoryView_FromMemory`, :740-762, on `size` bytes at `mem`. `writable` is
`flags == PyBUF_WRITE`. -/
def memoryViewFromMemory (mem : Int) (size : Int) (writable : Bool) : M Nat := do
  let k ← mbufAlloc
  let master : Buf :=
    { buf := mem, len := size, itemsize := 1, readonly := !writable, ndim := 1,
      format := some ['B'], shape := some [size], strides := some [1] }
  M.modify fun st => st.setMb k { st.mb k with master := master }
  mbufAddView k none

/-- `PyMemoryView_FromBuffer`, :842-867. `isNull` is `info->buf == NULL`. -/
def memoryViewFromBuffer (info : Buf) (isNull : Bool) : M Nat := do
  if isNull then throw (.valueError "PyMemoryView_FromBuffer(): info->buf must not be NULL")
  let k ← mbufAlloc
  M.modify fun st => st.setMb k { st.mb k with master := { info with obj := none } }
  mbufAddView k none

/-- `releasebuffer_call_python`, Objects/typeobject.c:11535-11548, for an exporter with no Python
`__buffer__`: `__release_buffer__` receives a new view of the buffer, restricted. -/
def restrictedView (b : Buf) : M Nat := do
  let i ← memoryViewFromBuffer b false
  M.modify fun st =>
    let x := st.mv i
    st.setMv i { x with flags := { x.flags with restricted := true } }
  return i

/-- The first part of `memory_from_contiguous_copy`, :973-985: a new bytes object at the
end of the store, its managed buffer, and `mbuf_copy_format` (:933-947). -/
def contigBytes (src : Buf) : M Nat := do
  let e ← bytesBuf (List.replicate src.len.toNat 0)
  let k ← managedBufferFromObject e bufFullRO
  M.modify fun st =>
    let b := st.mb k
    st.setMb k { b with master := { b.master with format := src.format } }
  return k

/-- The second part of `memory_from_contiguous_copy`, :987-1018: the view, its strides in
the requested order, and the copy. -/
def contigFill (k : Nat) (src : Buf) (order : Char) : M Nat := do
  let i ← mbufAddIncompleteView k none src.ndim
  let shape := src.shape.getD []
  let strides :=
    if order = 'C' ∨ order = 'A' then cStrides src.itemsize shape
    else fStrides src.itemsize shape
  let st ← M.get
  let x := st.mv i
  let dest : Buf := { x.view with
    itemsize := src.itemsize, shape := some shape, strides := some strides, suboffsets := none }
  M.modify fun st => st.setMv i { x with view := dest, flags := initFlags dest }
  let st ← M.get
  let dm ← M.lift (copyBuffer st.mem st.mem dest src)
  M.modify fun st => { st with mem := dm }
  return i

/-- `memory_from_contiguous_copy`, :961-1019. -/
def memoryFromContiguousCopy (src : Buf) (order : Char) : M Nat := do
  let k ← contigBytes src
  contigFill k src order

/-- `PyMemoryView_GetContiguous`, :1038-1074. `writable` is `buffertype == PyBUF_WRITE`. -/
def memoryViewGetContiguous (obj : Obj) (writable : Bool) (order : Char) : M Nat := do
  let mv ← memoryViewFromObject obj
  let st ← M.get
  let view := (st.mv mv).view
  if writable && view.readonly then
    memoryDealloc mv
    throw (bufferError "underlying buffer is not writable")
  if pyBufferIsContiguous view order then return mv
  if writable then
    memoryDealloc mv
    throw (bufferError "writable contiguous buffer requested for a non-contiguous object.")
  let ret ← memoryFromContiguousCopy view order
  memoryDealloc mv
  return ret

/-! ## Casting -/

/-- The test `get_native_fmtchar(&srcchar, view->format) >= 0 && IS_BYTE_FORMAT(srcchar)`
of :1381-1382. -/
def srcIsByte (view : Buf) : Bool :=
  match getNativeFmtchar (view.format.getD ['B']) with
  | some (c, _) => isByteFormat c
  | none => false

/-- `cast_to_1D`, :1354-1435, on the fresh view `i`. -/
def castTo1D (i : Nat) (format : List Char) : M Unit := do
  let st ← M.get
  let x := st.mv i
  let view := x.view
  if format.any (fun c => c.toNat ≥ 128) then throw unicodeEncodeError
  let some (destchar, itemsize) := getNativeFmtchar format
    | throw (.valueError "memoryview: destination format must be a native format prefixed with an optional '@'")
  if !srcIsByte view && !isByteFormat destchar then
    throw (.typeError "memoryview: cannot cast between two non-byte formats")
  if view.len.tmod itemsize ≠ 0 then
    throw (.typeError "memoryview: length is not a multiple of itemsize")
  let some fstr := getNativeFmtstr format
    | throw (runtimeError "memoryview: internal error")
  let v : Buf := { view with
    format := some fstr, itemsize := itemsize, ndim := 1,
    shape := some [Int.tdiv view.len itemsize], strides := some [itemsize], suboffsets := none }
  M.set (st.setMv i { x with view := v, flags := initFlags v })

/-- `PyLong_AsSsize_t`, Objects/longobject.c:748-749. -/
def longAsSsize (x : Int) : Py Int :=
  if ssizeMin ≤ x ∧ x ≤ ssizeMax then .ok x
  else .error (.overflowError "Python int too large to convert to C ssize_t")

/-- `PyLong_Check(tmp)` and the value of an `int` (or `bool`). -/
def Obj.asLong? : Obj → Option Int
  | .int n => some n
  | .bool b => some (if b then 1 else 0)
  | _ => Option.none

/-- `copy_shape`, :1416-1450: `(len, shape)`, `len` the running product. -/
def copyShape : List Obj → Int → Py (Int × List Int)
  | [], len => .ok (len, [])
  | tmp :: rest, len =>
    match tmp.asLong? with
    | Option.none => .error (.typeError "memoryview.cast(): elements of shape must be integers")
    | some v => do
      let x ← longAsSsize v
      if x ≤ 0 then .error (.valueError "memoryview.cast(): elements of shape must be integers > 0")
      else if x > Int.tdiv ssizeMax len then
        .error (.valueError "memoryview.cast(): product(shape) > SSIZE_MAX")
      else do
        let (l, s) ← copyShape rest (len * x)
        return (l, x :: s)

/-- `cast_to_ND`, :1455-1489. -/
def castToND (i : Nat) (shape : List Obj) (ndim : Nat) : M Unit := do
  let st ← M.get
  let x := st.mv i
  let view := x.view
  let (len, v) ←
    if ndim = 0 then
      pure (view.itemsize, { view with ndim := 0, shape := none, strides := none })
    else do
      let (len, sh) ← M.lift (copyShape shape view.itemsize)
      pure (len, { view with
        ndim := ndim, shape := some sh, strides := some (cStrides view.itemsize sh) })
  if view.len ≠ len then
    throw (.typeError "memoryview: product(shape) * itemsize != buffer size")
  M.set (st.setMv i { x with view := v, flags := initFlags v })

/-- `zero_in_shape`, :1491-1502. -/
def zeroInShape (v : Buf) : Bool := ((v.shape.getD []).take v.ndim).any (· == 0)

/-- The argument `shape` of `memoryview.cast`. -/
inductive ShapeArg where
  /-- A list or tuple. -/
  | seq (items : List Obj)
  /-- Anything else. -/
  | other
  deriving Repr, DecidableEq, Inhabited

/-- `memoryview_cast_impl`, :1525-1577. -/
def memoryviewCast (self : Nat) (format : List Char) (shape : Option ShapeArg) : M Nat := do
  checkReleased self
  checkRestricted self
  let st ← M.get
  let x := st.mv self
  if !x.flags.isC then
    throw (.typeError "memoryview: casts are restricted to C-contiguous views")
  if (shape.isSome || x.view.ndim != 1) && zeroInShape x.view then
    throw (.typeError "memoryview: cannot cast view with zeros in shape or strides")
  let mut ndim : Nat := 1
  let mut items : List Obj := []
  match shape with
  | Option.none => pure ()
  | some .other => throw (.typeError "shape must be a list or a tuple")
  | some (.seq l) =>
    items := l
    ndim := l.length
    if ndim > 64 then
      throw (.valueError "memoryview: number of dimensions must not exceed 64")
    if x.view.ndim != 1 && ndim != 1 then
      throw (.typeError "memoryview: cast must be 1D -> ND or ND -> 1D")
  let mv ← mbufAddIncompleteView x.mbuf (some x.view) (if ndim = 0 then 1 else ndim)
  M.onError (do
    castTo1D mv format
    if shape.isSome then castToND mv items ndim
    return mv) (memoryDealloc mv)

/-- `memoryview_toreadonly_impl`, :1585-1599. -/
def memoryviewToreadonly (self : Nat) : M Nat := do
  checkReleased self
  checkRestricted self
  let st ← M.get
  let i ← mbufAddView (st.mv self).mbuf (some (st.mv self).view)
  M.modify fun st =>
    let y := st.mv i
    st.setMv i { y with view := { y.view with readonly := true } }
  return i

/-! ## Pack and unpack (:1705-2102) -/

/-- `type_error_int`, :1711-1717. -/
def typeErrorInt (fmt : List Char) : PyExc :=
  .typeError s!"memoryview: invalid type for format '{fmtText fmt}'"

/-- `value_error_int`, :1719-1725. -/
def valueErrorInt (fmt : List Char) : PyExc :=
  .valueError s!"memoryview: invalid value for format '{fmtText fmt}'"

/-- `fix_error_int`, :1727-1741: `PyErr_ExceptionMatches`, so a subclass counts. -/
def fixErrorInt (fmt : List Char) (e : PyExc) : PyExc :=
  if excMatches e "TypeError" then typeErrorInt fmt
  else if excMatches e "OverflowError" || excMatches e "ValueError" then valueErrorInt fmt
  else e

@[simp] theorem fixErrorInt_type (fmt : List Char) (m : String) :
    fixErrorInt fmt (.typeError m) = typeErrorInt fmt := by
  simp [fixErrorInt, excMatches, PyExc.className]

@[simp] theorem fixErrorInt_value (fmt : List Char) (m : String) :
    fixErrorInt fmt (.valueError m) = valueErrorInt fmt := by
  simp [fixErrorInt, excMatches, PyExc.className, excBases]

@[simp] theorem fixErrorInt_overflow (fmt : List Char) (m : String) :
    fixErrorInt fmt (.overflowError m) = valueErrorInt fmt := by
  simp [fixErrorInt, excMatches, PyExc.className, excBases]

/-- `__index__` returned a non-int, Objects/abstract.c:1433-1435. -/
def indexWrong (t : String) : PyExc := .typeError s!"Idx.__index__() must return an int, not {t}"

/-- `_PyNumber_Index(item)`, Objects/abstract.c:1409-1449, running `__index__`. -/
def numberIndex : Obj → M Int
  | .int n => pure n
  | .bool b => pure (if b then 1 else 0)
  | .index r rel => do fire rel; r.get indexWrong
  | o => throw (.typeError s!"'{o.typeName}' object cannot be interpreted as an integer")

/-- `PyLong_AsLong`. -/
def asLong (x : Int) : Py Int :=
  if -(2 ^ 63) ≤ x ∧ x < 2 ^ 63 then .ok x
  else .error (.overflowError "Python int too large to convert to C long")

/-- `PyLong_AsUnsignedLong`. -/
def asUnsignedLong (x : Int) : Py Int :=
  if x < 0 then .error (.overflowError "can't convert negative int to unsigned")
  else if x < 2 ^ 64 then .ok x
  else .error (.overflowError "Python int too large to convert to C unsigned long")

/-- `pylong_as_ld`, :1681-1694. -/
def pylongAsLd (item : Obj) : M Int := do M.lift (asLong (← numberIndex item))
/-- `pylong_as_lu`, :1696-1709. -/
def pylongAsLu (item : Obj) : M Int := do M.lift (asUnsignedLong (← numberIndex item))
/-- `pylong_as_lld`, :1711-1724. -/
def pylongAsLld (item : Obj) : M Int := do M.lift (asLong (← numberIndex item))
/-- `pylong_as_llu`, :1726-1739. -/
def pylongAsLlu (item : Obj) : M Int := do M.lift (asUnsignedLong (← numberIndex item))
/-- `pylong_as_zd`, :1741-1754. -/
def pylongAsZd (item : Obj) : M Int := do M.lift (longAsSsize (← numberIndex item))
/-- `pylong_as_zu`, :1756-1769. -/
def pylongAsZu (item : Obj) : M Int := do M.lift (asUnsignedLong (← numberIndex item))

/-- `__float__` returned a non-float, Objects/floatobject.c:284-286. -/
def floatWrong (t : String) : PyExc := .typeError s!"Flt.__float__() must return a float, not {t}"

/-- `PyFloat_AsDouble`, Objects/floatobject.c: `__float__`, then `__index__`. -/
def floatAsDouble : Obj → M Nat
  | .float b => pure b
  | .floatLike r rel => do fire rel; r.get floatWrong
  | .int n => M.lift (longAsDouble n)
  | .bool b => M.lift (longAsDouble (if b then 1 else 0))
  | .index r rel => do fire rel; M.lift (longAsDouble (← r.get indexWrong))
  | o => throw (.typeError s!"must be real number, not {o.typeName}")

/-- `__bool__` returned a non-bool, Objects/typeobject.c:10937-10940. -/
def boolWrong (t : String) : PyExc := .typeError s!"Bln.__bool__() must return a bool, not {t}"

/-- `__len__` returned a non-int: `PyNumber_AsSsize_t` of its result in `slot_sq_length`. -/
def lenWrong (t : String) : PyExc := .typeError s!"'{t}' object cannot be interpreted as an integer"

/-- `PyObject_IsTrue`, Objects/object.c: `True`, `False`, `None`, then `nb_bool`, `mp_length`,
`sq_length`, then true. An `Idx`, `Flt`, `Eql` or `Exporter` has none of the three. -/
def isTrue : Obj → M Bool
  | .int n => pure (n != 0)
  | .bool b => pure b
  | .float d => pure (d % two63 != 0)
  | .bytes b => pure (!b.isEmpty)
  | .str s => pure (!s.isEmpty)
  | .none => pure false
  | .list n => pure (n != 0)
  | .boolLike r rel => do fire rel; r.get boolWrong
  | .complex a b => pure (a % two63 != 0 || b % two63 != 0)
  | .lenLike r rel => do
    -- no `__bool__`: `slot_sq_length`, Objects/typeobject.c
    fire rel
    let n ← r.get lenWrong
    if n < 0 then throw (.valueError "__len__() should return >= 0")
    return n != 0
  | .view i => do
    -- `memory_length` via `sq_length`/`mp_length`
    let st ← M.get
    checkReleased i
    if (st.mv i).view.ndim = 0 then
      throw (.typeError "0-dim memory has no length")
    return ((st.mv i).view.shape.getD []).getD 0 0 != 0
  | _ => pure true

/-- `PyComplex_AsCComplex`, Objects/complexobject.c: a `complex`, or a real from `PyFloat_AsDouble`. -/
def complexAsC : Obj → M (Nat × Nat)
  | .complex a b => pure (a, b)
  | o => do return (← floatAsDouble o, 0)

/-- `PyLong_AsVoidPtr`, Objects/longobject.c: only a real `int`. -/
def asVoidPtr (item : Obj) : Py Int :=
  match item.asLong? with
  | Option.none => .error (.typeError "an integer is required")
  | some n => if n < 0 then asLong n else asUnsignedLong n

/-- `memcpy(ptr, bytes)` into the store. -/
def memWrite (ptr : Int) (bs : List Nat) : M Unit := fun st =>
  (.ok (), { st with mem := wrBytes st.mem ptr bs })

/-- `pack_single`, :1949-2102. `fmt` is the format after `adjust_fmt`. Note the arm for
`c` (:2071-2077): unlike every other arm and unlike `unpack_single`, it has no
`CHECK_RELEASED_INT_AGAIN`. -/
def packSingle (self : Nat) (ptr : Int) (item : Obj) (fmt : List Char) : M Unit :=
  let fixed {α : Type} (x : M α) : M α := M.mapErr (fixErrorInt fmt) x
  match cc fmt 0 with
  | 'b' | 'h' | 'i' | 'l' => do
    let ld ← fixed (pylongAsLd item)
    checkReleased self
    match cc fmt 0 with
    | 'b' =>
      if ld < -128 ∨ ld > 127 then throw (valueErrorInt fmt)
      memWrite ptr (encInt ld 1)
    | 'h' =>
      if ld < -32768 ∨ ld > 32767 then throw (valueErrorInt fmt)
      memWrite ptr (encInt ld 2)
    | 'i' =>
      if ld < -2147483648 ∨ ld > 2147483647 then throw (valueErrorInt fmt)
      memWrite ptr (encInt ld 4)
    | _ => memWrite ptr (encInt ld 8)
  | 'B' | 'H' | 'I' | 'L' => do
    let lu ← fixed (pylongAsLu item)
    checkReleased self
    match cc fmt 0 with
    | 'B' =>
      if lu > 255 then throw (valueErrorInt fmt)
      memWrite ptr (encInt lu 1)
    | 'H' =>
      if lu > 65535 then throw (valueErrorInt fmt)
      memWrite ptr (encInt lu 2)
    | 'I' =>
      if lu > 4294967295 then throw (valueErrorInt fmt)
      memWrite ptr (encInt lu 4)
    | _ => memWrite ptr (encInt lu 8)
  | 'q' => do
    let lld ← fixed (pylongAsLld item)
    checkReleased self
    memWrite ptr (encInt lld 8)
  | 'Q' => do
    let llu ← fixed (pylongAsLlu item)
    checkReleased self
    memWrite ptr (encInt llu 8)
  | 'n' => do
    let zd ← fixed (pylongAsZd item)
    checkReleased self
    memWrite ptr (encInt zd 8)
  | 'N' => do
    let zu ← fixed (pylongAsZu item)
    checkReleased self
    memWrite ptr (encInt zu 8)
  | 'f' | 'd' | 'e' => do
    let d ← fixed (floatAsDouble item)
    checkReleased self
    match cc fmt 0 with
    | 'f' => memWrite ptr (encLE (narrow32 d) 4)
    | 'd' => memWrite ptr (encLE d 8)
    | _ => do
      let h ← fixed (M.lift (pack2 d))
      memWrite ptr (encLE h 2)
  | '?' => do
    let ld ← isTrue item
    checkReleased self
    memWrite ptr (encInt (if ld then 1 else 0) 1)
  | 'c' =>
    match item with
    | .bytes [b] => memWrite ptr [b]
    | .bytes _ => throw (valueErrorInt fmt)
    | _ => throw (typeErrorInt fmt)
  | 'P' => do
    let p ← fixed (M.lift (asVoidPtr item))
    checkReleased self
    memWrite ptr (encInt p 8)
  | 'Z' =>
    match cc fmt 1 with
    | 'd' => do
      let (a, b) ← fixed (complexAsC item)
      checkReleased self
      memWrite ptr (encLE a 8 ++ encLE b 8)
    | 'f' => do
      let (a, b) ← fixed (complexAsC item)
      checkReleased self
      memWrite ptr (encLE (narrow32 a) 4 ++ encLE (narrow32 b) 4)
    | _ => throw (notImplError s!"memoryview: format {fmtText fmt} not supported")
  | _ => throw (notImplError s!"memoryview: format {fmtText fmt} not supported")

/-- `unpack_single`, :1850-1938. -/
def unpackSingle (self : Nat) (ptr : Int) (fmt : List Char) : M Item := do
  checkReleased self
  let st ← M.get
  M.lift (unpackRaw st.mem ptr fmt)

/-- `adjust_fmt`, :2230-2242: `view->format` with an optional `@` removed, or an error
unless a single character is left. -/
def adjustFmt (v : Buf) : Py (List Char) :=
  let vf := v.format.getD []
  let fmt := if cc vf 0 = '@' then vf.drop 1 else vf
  if cc fmt 0 = 'Z' ∧ cc fmt 1 ≠ '\x00' ∧ cc fmt 2 = '\x00' then .ok fmt
  else if cc fmt 0 ≠ '\x00' ∧ cc fmt 1 = '\x00' then .ok fmt
  else .error (notImplError s!"memoryview: unsupported format {fmtText vf}")

/-! ## Representations -/

/-- `memoryview_tolist_impl`, :2314-2339. `Tree.leaf` for a 0-dim view. -/
def memoryviewTolist (self : Nat) : M Tree := do
  checkReleased self
  let st ← M.get
  let view := (st.mv self).view
  let fmt ← M.lift (adjustFmt view)
  let f (p : Int) : Py Item := (unpackSingle self p fmt st).1
  if view.ndim = 0 then
    return .leaf (← M.lift (f view.buf))
  else if view.ndim = 1 then
    let l ← M.lift (tolistBase st.mem f ((view.strides.getD []).getD 0 0) view.suboffsets
      ((view.shape.getD []).getD 0 0).toNat view.buf)
    return .node (l.map Tree.leaf)
  else
    M.lift (tolistRec st.mem f (view.shape.getD []) (view.strides.getD []) view.suboffsets view.buf)

/-- The `order` argument of `memoryview_tobytes_impl`, :2366-2378. -/
def parseOrder : Option (List Char) → Py Char
  | Option.none => .ok 'C'
  | some ['F'] => .ok 'F'
  | some ['A'] => .ok 'A'
  | some ['C'] => .ok 'C'
  | some _ => .error (.valueError "order must be 'C', 'F' or 'A'")

/-- `memoryview_tobytes_impl`, :2356-2390. `order`: `none` is `order=None`, or the
argument's text. -/
def memoryviewTobytes (self : Nat) (order : Option (List Char)) : M (List Nat) := do
  checkReleased self
  let ord ← M.lift (parseOrder order)
  let st ← M.get
  let src := (st.mv self).view
  M.lift (pyBufferToContiguous st.mem src src.len ord)

/-- The separator checks of `_Py_strhex_impl`, pystrhex.c:122-153: `(sep_char, group)`. -/
def strhexSep (sep : Option Obj) (group : Int) : Py (Char × Int) :=
  match sep with
  | Option.none => .ok ('\x00', 0)
  | some o =>
    let check (c : Nat) : Py (Char × Int) :=
      if c > 127 then .error (.valueError "sep must be ASCII.")
      else .ok (Char.ofNat c, group)
    match o with
    | .str s =>
      if s.length ≠ 1 then .error (.valueError "sep must be length 1.")
      else
        let c := (cc s 0).toNat
        if c > 255 then .error (.valueError "sep must be ASCII.") else check c
    | .bytes b =>
      if b.length ≠ 1 then .error (.valueError "sep must be length 1.")
      else check (b.getD 0 0)
    | .list n =>
      if n ≠ 1 then .error (.valueError "sep must be length 1.")
      else .error (.typeError "sep must be str or bytes.")
    | o => .error (.typeError s!"object of type '{o.typeName}' has no len()")

/-- `_Py_strhex_with_sep`, Python/pystrhex.c:115-253 and :268-274. -/
def strhexWithSep (arg : List Nat) (sep : Option Obj) (bps : Int) : Py (List Char) := do
  let (c, group) ← strhexSep sep bps
  strhexBody arg c group

/-- `_Py_strhex_with_sep`'s handling of `sep`, Python/pystrhex.c:122-140, for a `sep` whose
`__len__` is Python code, then the formatting. -/
def strhexWithSepM (arg : M (List Nat)) (sep : Option Obj) (bps : Int) : M (List Char) := do
  match sep with
  | some (.lenLike r rel) =>
    fire rel
    let n ← r.get lenWrong
    if n < 0 then throw (.valueError "__len__() should return >= 0")
    if n ≠ 1 then throw (.valueError "sep must be length 1.")
    throw (.typeError "sep must be str or bytes.")
  | _ =>
    let (c, group) ← M.lift (strhexSep sep bps)
    M.lift (strhexBody (← arg) c group)

/-- The export count held around a call that runs Python code, so that the view cannot
be released under it: :2463-2465, :3342-3344. -/
def withExport {α : Type} (i : Nat) (x : M α) : M α := fun st =>
  let bump (d : Int) (s : St) : St := s.setMv i { s.mv i with exports := (s.mv i).exports + d }
  match x (bump 1 st) with
  | (r, s) => (r, bump (-1) s)

/-- `memoryview_hex_impl`, :2448-2484. Only the contiguous branch hexes the view's own
memory, so only that branch holds an export (:2463-2465, gh-143195). -/
def memoryviewHex (self : Nat) (sep : Option Obj) (bps : Int) : M (List Char) := do
  checkReleased self
  let st ← M.get
  let x := st.mv self
  let src := x.view
  if x.flags.isC then
    return ← withExport self
      (strhexWithSepM (fun s => (.ok (rdBytes s.mem src.buf src.len.toNat), s)) sep bps)
  let bytes ← M.lift (pyBufferToContiguous st.mem src src.len 'C')
  strhexWithSepM (pure bytes) sep bps

/-- `memoryview.hex(sep, bytes_per_sep)`: the clinic `Py_ssize_t`, then `memoryview_hex_impl`. -/
def memoryviewHexArgs (self : Nat) (sep : Option Obj) (bps : Int) : M (List Char) :=
  if bps < ssizeMin ∨ bps > ssizeMax then
    throw (.overflowError "Python int too large to convert to C ssize_t")
  else memoryviewHex self sep bps

/-- `memory_repr`, :2486-2494: the text before ` at 0x...`. -/
def memoryRepr (self : Nat) : M String := fun st =>
  (.ok (if (st.mv self).flags.released then "<released memory" else "<memory"), st)

/-! ## Indexing and slicing (:2497-2854) -/

/-- `lookup_dimension`, :2501-2524. -/
def lookupDimension (m : Mem) (v : Buf) (ptr : Int) (dim : Nat) (index : Int) : Py Int :=
  let nitems := (v.shape.getD []).getD dim 0
  let index := if index < 0 then index + nitems else index
  if index < 0 ∨ index ≥ nitems then
    .error (.indexError s!"index out of bounds on dimension {dim + 1}")
  else
    .ok (adjustPtr m (ptr + (v.strides.getD []).getD dim 0 * index) v.suboffsets dim)

/-- `ptr_from_index`, :2526-2532. -/
def ptrFromIndex (m : Mem) (v : Buf) (index : Int) : Py Int := lookupDimension m v v.buf 0 index

/-- `PyNumber_AsSsize_t(key, PyExc_IndexError)`, Objects/abstract.c:1468-1510, after
`__index__` gave `x`. The message names the key's type. -/
def keyAsSsize (o : Obj) (x : Int) : Py Int :=
  if ssizeMin ≤ x ∧ x ≤ ssizeMax then .ok x
  else .error (.indexError s!"cannot fit '{o.typeName}' into an index-sized integer")

/-- The tuple elements as index objects, for `ptr_from_tuple`. -/
def elemIndex : KeyElem → M Int
  | .obj o => do
    let n ← numberIndex o
    M.lift (keyAsSsize o n)
  | .slice .. => throw (.typeError "slice indices must be integers")

/-- The loop of `ptr_from_tuple`, :2446-2453. -/
def tupleLoop (v : Buf) : Nat → List KeyElem → Int → M Int
  | _, [], ptr => pure ptr
  | dim, e :: es, ptr => do
    let index ← elemIndex e
    let st ← M.get
    let ptr ← M.lift (lookupDimension st.mem v ptr dim index)
    tupleLoop v (dim + 1) es ptr

/-- `ptr_from_tuple`, :2432-2455. -/
def ptrFromTuple (v : Buf) (tup : List KeyElem) : M Int := do
  if tup.length > v.ndim then
    throw (.typeError s!"cannot index {v.ndim}-dimension view with {tup.length}-element tuple")
  tupleLoop v 0 tup v.buf

/-- `memory_item`, :2460-2487. -/
def memoryItem (self : Nat) (index : Int) : M Item := do
  checkReleased self
  let st ← M.get
  let view := (st.mv self).view
  let fmt ← M.lift (adjustFmt view)
  if view.ndim = 0 then throw (.typeError "invalid indexing of 0-dim memory")
  if view.ndim = 1 then
    let ptr ← M.lift (ptrFromIndex st.mem view index)
    return ← unpackSingle self ptr fmt
  throw (notImplError "multi-dimensional sub-views are not implemented")

/-- `memory_item_multi`, :2490-2513. -/
def memoryItemMulti (self : Nat) (tup : List KeyElem) : M Item := do
  checkReleased self
  let st ← M.get
  let view := (st.mv self).view
  let fmt ← M.lift (adjustFmt view)
  if tup.length < view.ndim then throw (notImplError "sub-views are not implemented")
  let ptr ← ptrFromTuple view tup
  unpackSingle self ptr fmt

/-- The loop of :2532-2533: the last earlier dimension with a suboffset. -/
def lastSub (subs : List Int) : Nat → Option Nat
  | 0 => Option.none
  | n + 1 => if subs.getD n (-1) ≥ 0 then some n else lastSub subs n

/-- `init_slice`, :2515-2542. `PySlice_Unpack` saturates and rejects a zero step;
every `Py_ssize_t` product is a wrapping one. -/
def initSlice (base : Buf) (s : Slice) (dim : Nat) : Py Buf := do
  let (start, stop, step) ← sliceUnpack s
  let shape := base.shape.getD []
  let strides := base.strides.getD []
  let (start, _, slicelength) := adjustIndices (shape.getD dim 0) start stop step
  let sd := strides.getD dim 0
  let adjustBuf : Buf := { base with buf := base.buf + wrap (sd * start) }
  let b : Buf :=
    match base.suboffsets with
    | Option.none => adjustBuf
    | some subs =>
      if dim = 0 then adjustBuf
      else
        match lastSub subs dim with
        | Option.none => adjustBuf
        | some n => { base with suboffsets := some (subs.set n (subs.getD n 0 + wrap (sd * start))) }
  return { b with shape := some (shape.set dim slicelength),
                  strides := some (strides.set dim (wrap (sd * step))) }

/-- `is_multislice`, :2544-2561, on the tuple elements. -/
def isMultislice (es : List KeyElem) : Bool :=
  !es.isEmpty && es.all fun e => match e with | .slice .. => true | _ => false

/-- `_PyIndex_Check`. -/
def Obj.isIndex : Obj → Bool
  | .int _ | .bool _ | .index _ _ => true
  | _ => false

/-- `is_multiindex`, :2563-2578. -/
def isMultiindex (es : List KeyElem) : Bool :=
  es.all fun e => match e with | .obj o => o.isIndex | _ => false

/-- The part whose `__index__` the case's callback is on. -/
def slicePartOf (s : Slice) (fail : Option SliceFail) : SlicePart :=
  match fail with
  | some f => f.part
  | Option.none => if s.start.isSome then .start else if s.stop.isSome then .stop else .step

/-- `_PyEval_SliceIndex` of one part: Python code only on the part `at_`. -/
def sliceStage (at_ p : SlicePart) (rel : Option Nat) (fail : Option SliceFail) : M Unit :=
  if p = at_ then do
    fire rel
    match fail with
    | some f => f.how.get indexWrong
    | Option.none => pure ()
  else pure ()

/-- The Python code inside `PySlice_Unpack`, Objects/sliceobject.c:219-259: step, then
start, then stop, with the zero test right after the step. `initSlice` does the
arithmetic. -/
def sliceEvents (s : Slice) (rel : Option Nat) (fail : Option SliceFail) : M Unit := do
  let at_ := slicePartOf s fail
  sliceStage at_ .step rel fail
  if s.step = some 0 then throw (.valueError "slice step cannot be zero")
  sliceStage at_ .start rel fail
  sliceStage at_ .stop rel fail

/-- What a subscript returns. -/
inductive Sub where
  | item (x : Item)
  /-- A memoryview by number. -/
  | view (i : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- `memory_subscript`, :2582-2643. -/
def memorySubscript (self : Nat) (key : Key) : M Sub := do
  checkReleased self
  let st ← M.get
  let view := (st.mv self).view
  if view.ndim = 0 then
    match key with
    | .tuple [] =>
      let fmt ← M.lift (adjustFmt view)
      return .item (← unpackSingle self view.buf fmt)
    | .ellipsis => return .view self
    | _ => throw (.typeError "invalid indexing of 0-dim memory")
  match key with
  | .one (.obj o) =>
    if o.isIndex then
      let n ← numberIndex o
      let index ← M.lift (keyAsSsize o n)
      return .item (← memoryItem self index)
    throw (.typeError "memoryview: invalid slice key")
  | .one (.slice s rel fail) =>
    checkRestricted self
    let sliced ← mbufAddView (st.mv self).mbuf (some view)
    M.onError (do
      sliceEvents s rel fail
      let st' ← M.get
      let x := st'.mv sliced
      let v ← M.lift (initSlice x.view s 0)
      let v := { v with len := initLen (v.shape.getD []) v.itemsize }
      M.modify fun st => st.setMv sliced { x with view := v, flags := initFlags v }
      return .view sliced) (memoryDealloc sliced)
  | .tuple es =>
    if isMultiindex es then
      return .item (← memoryItemMulti self es)
    if isMultislice es then
      throw (notImplError "multi-dimensional slicing is not implemented")
    throw (.typeError "memoryview: invalid slice key")
  | .ellipsis => throw (.typeError "memoryview: invalid slice key")

/-- `copy_single`, :405-433. -/
def copySingle (self : Nat) (dest src : Buf) : M Unit := do
  checkReleased self
  M.lift (equivStructure dest src)
  let useMem := !lastDimIsContiguous dest src
  let st ← M.get
  let dm := copyBase ((dest.shape.getD []).getD 0 0) dest.itemsize dest.buf
    ((dest.strides.getD []).getD 0 0) dest.suboffsets src.buf ((src.strides.getD []).getD 0 0)
    src.suboffsets useMem st.mem st.mem
  M.modify fun st => { st with mem := dm }

/-- `memory_ass_sub`, :2645-2746. `value = none` is `del m[key]`. -/
def memoryAssSub (self : Nat) (key : Key) (value : Option Obj) : M Unit := do
  checkReleased self
  let st ← M.get
  let view := (st.mv self).view
  let fmt ← M.lift (adjustFmt view)
  if view.readonly then throw (.typeError "cannot modify read-only memory")
  let some value := value | throw (.typeError "cannot delete memory")
  if view.ndim = 0 then
    match key with
    | .ellipsis | .tuple [] => return ← packSingle self view.buf value fmt
    | _ => throw (.typeError "invalid indexing of 0-dim memory")
  match key with
  | .one (.obj o) =>
    if o.isIndex then
      if 1 < view.ndim then throw (notImplError "sub-views are not implemented")
      let n ← numberIndex o
      let index ← M.lift (keyAsSsize o n)
      let st ← M.get
      let ptr ← M.lift (ptrFromIndex st.mem view index)
      return ← packSingle self ptr value fmt
    throw (.typeError "memoryview: invalid slice key")
  | .one (.slice s rel fail) =>
    if view.ndim = 1 then
      let src ← getBufferFull value
      let body : M Unit := do
        sliceEvents s rel fail
        let dest ← M.lift (initSlice view s 0)
        let dest := { dest with
          len := (dest.shape.getD []).getD 0 0 * dest.itemsize }
        copySingle self dest src
      let r ← M.onError body (pyBufferRelease src)
      pyBufferRelease src
      return r
    throw (notImplError "memoryview slice assignments are currently restricted to ndim = 1")
  | .tuple es =>
    if isMultiindex es then
      if (es.length : Int) < view.ndim then throw (notImplError "sub-views are not implemented")
      let ptr ← ptrFromTuple view es
      return ← packSingle self ptr value fmt
    if isMultislice es then
      throw (notImplError "memoryview slice assignments are currently restricted to ndim = 1")
    throw (.typeError "memoryview: invalid slice key")
  | .ellipsis => throw (.typeError "memoryview: invalid slice key")

/-- `memory_length`, :2748-2758. -/
def memoryLength (self : Nat) : M Int := do
  checkReleased self
  let st ← M.get
  let view := (st.mv self).view
  if view.ndim = 0 then throw (.typeError "0-dim memory has no length")
  return (view.shape.getD []).getD 0 0

/-! ## Iteration (:3463-3558) -/

/-- `PyObject_GC_New(memoryiterobject, ...)`: a new iterator, by number. -/
def iterAlloc (x : MIter) : M Nat := fun st =>
  (.ok st.iters.length, { st with iters := st.iters ++ [x] })

/-- `memory_iter`, :3522-3558: the iterator's number. -/
def memoryIter (self : Nat) : M Nat := do
  checkReleased self
  let st ← M.get
  let view := (st.mv self).view
  if view.ndim = 0 then throw (.typeError "invalid indexing of 0-dim memory")
  if view.ndim ≠ 1 then throw (notImplError "multi-dimensional sub-views are not implemented")
  let fmt ← M.lift (adjustFmt view)
  let len ← memoryLength self
  iterAlloc { fmt := fmt, length := len, index := 0, seq := some self }

/-- A NULL pointer out of `ADJUST_PTR`: a stored pointer of 0 with a suboffset of 0, which
`adjust_ptr` reads as any other address. The store is laid out so that nothing lives at 0. -/
def nullPtr : Int := 0

/-- `memoryiter_next`, :3494-3520: `none` is exhaustion (a NULL return with no error). -/
def memoryiterNext (it : Nat) : M (Option Item) := do
  let st ← M.get
  let x := st.iters.getD it default
  let some seq := x.seq | return Option.none
  if x.index < x.length then
    checkReleased seq
    let view := (st.mv seq).view
    let ptr := view.buf + (view.strides.getD []).getD 0 0 * x.index
    let ptr := adjustPtr st.mem ptr view.suboffsets 0
    M.modify fun st => { st with iters := st.iters.set it { x with index := x.index + 1 } }
    -- `if (ptr == NULL) return NULL;` with no exception set: the iterator just stops
    if ptr = nullPtr then return Option.none
    return some (← unpackSingle seq ptr x.fmt)
  M.modify fun st => { st with iters := st.iters.set it { x with seq := Option.none } }
  return Option.none

/-! ## Comparison (:2911-3202) -/

/-- `fix_struct_error_int`, :2919-2931: `struct.error` means "not equal". -/
def fixStructError (e : PyExc) : Py Bool :=
  if excMatches e "ImportError" || excMatches e "MemoryError" then .error e else .ok false

/-- What `import struct` raises with `sys.modules['struct'] = None`. -/
def importStruct : PyExc := .named "ModuleNotFoundError" "import of struct halted; None in sys.modules"

/-- `struct_get_unpacker`, :2078-2127: the import of `struct.Struct` comes first (:2087-2089). -/
def unpackerOf (noStruct : Bool) (fmt : List Char) (itemsize : Int) : Py Unpacker :=
  if noStruct then .error importStruct else structGetUnpacker fmt itemsize

/-- `Py_EQ`, `Py_NE`, or an ordering operator. -/
inductive CmpOp where
  | eq | ne | other
  deriving Repr, DecidableEq, Inhabited

/-- The comparison proper, :3137-3181, once both buffers are at hand. -/
def compareBufs (m : Mem) (noStruct : Bool) (vv ww : Buf) : Py Bool :=
  if !equivShape vv ww then .ok false
  else
    let vf := vv.format.getD []
    let wf := ww.format.getD []
    let vfmt := match getNativeFmtchar vf with | some (c, _) => c | Option.none => '_'
    let wfmt := match getNativeFmtchar wf with | some (c, _) => c | Option.none => '_'
    let run (fmt : Char) (unp : Option (Unpacker × Unpacker)) : Py Bool :=
      if vv.ndim = 0 then unpackCmp m vv.buf ww.buf fmt unp
      else if vv.ndim = 1 then
        cmpBase m fmt unp ((vv.strides.getD []).getD 0 0) ((ww.strides.getD []).getD 0 0)
          vv.suboffsets ww.suboffsets ((vv.shape.getD []).getD 0 0).toNat vv.buf ww.buf
      else
        cmpRec m fmt unp (vv.shape.getD []) (vv.strides.getD []) vv.suboffsets
          (ww.strides.getD []) ww.suboffsets vv.buf ww.buf
    if vfmt = '_' ∨ wfmt = '_' ∨ vfmt ≠ wfmt then
      match unpackerOf noStruct vf vv.itemsize with
      | .error e => fixStructError e
      | .ok up =>
        match unpackerOf noStruct wf ww.itemsize with
        | .error e => fixStructError e
        | .ok uq => run '_' (some (up, uq))
    else run vfmt Option.none

/-- The test of :3232-3241: a format of one of these characters, after an optional `@`. -/
def selfEqualFormat : Option (List Char) → Bool
  | none => false
  | some f =>
    let g := if cc f 0 = '@' then f.drop 1 else f
    cc g 0 != '\x00' && "bBchHiIlLnNqQ?".toList.contains (cc g 0) && cc g 1 == '\x00'

/-- The part of `memory_richcompare` before the label `result:`, :3110-3181: `equal`,
with `none` for `MV_COMPARE_NOT_IMPL`. The check of `v` at :3116 comes before
`PyObject_GetBuffer(w)` at :3130, which runs Python code; nothing looks at `v` again. -/
def memoryRichEqual (v : Nat) (w : Obj) : M (Option Bool) := do
  let st ← M.get
  if baseInaccessible st v then
    return some (w == .view v)
  let vv := (st.mv v).view
  -- `v == w`: the same object, of a format with no NaN, :3222-3244
  if w == .view v && selfEqualFormat vv.format then
    return some true
  match w with
  | .view i =>
    if baseInaccessible st i then
      return some (i == v)
    let ww := (st.mv i).view
    return some (← M.lift (compareBufs st.mem st.noStruct vv ww))
  | .bytes _ | .exporter _ _ =>
    match ← tryCatch (some <$> getBufferFull w) (fun _ => pure Option.none) with
    | Option.none => return Option.none
    | some ww =>
      let st ← M.get
      let r := compareBufs st.mem st.noStruct vv ww
      -- `PyBuffer_Release(ww)`, :3195-3196, after the result is known
      pyBufferRelease ww
      return some (← M.lift r)
  | _ => return Option.none

/-- `memory_richcompare`, :3101-3202. `none` is `NotImplemented`. -/
def memoryRichcompare (v : Nat) (w : Obj) (op : CmpOp) : M (Option Bool) := do
  if op = .other then return Option.none
  let e ← memoryRichEqual v w
  return e.map fun equal => if op = .eq then equal else !equal

/-- `PyObject_RichCompareBool(item, value, Py_EQ)` where neither side runs Python code or looks
at a buffer: an item never equals an object of a type other than `int`, `bool`, `float`, `bytes`,
except that a `bytes` item compares with a memoryview through `memory_richcompare`, in `itemEqM`. -/
def itemEqObj (x : Item) : Obj → Bool
  | .complex a b => itemEq x (.complex a b)
  | .int n => itemEq x (.int n)
  | .bool b => itemEq x (.bool b)
  | .float d => itemEq x (.float d)
  | .bytes b => itemEq x (.bytes b)
  | _ => false

/-- The truth of what `__eq__` returned in place of a bool, for the objects the difftest returns:
`"x"`, `None` and `[]`. -/
def wrongTruth : String → Bool
  | "str" => true
  | _ => false

/-- `PyObject_RichCompareBool(item, value, Py_EQ)`. A Python `__eq__` of `value` runs through the
reflected operation, may raise or release views, and can return any object, whose truth is the
result. `bytes_richcompare` gives `NotImplemented` for a memoryview, so for a `bytes` item (format
`c`) the reflected `memory_richcompare(value, item)` decides, and it can raise; an `int` or `float`
item has nothing to compare with it, and neither has the memoryview. -/
def itemEqM (x : Item) : Obj → M Bool
  | .eqLike r rel => do
    fire rel
    match r with
    | .val b => pure b
    | .raises e => throw e
    | .wrong t => pure (wrongTruth t)
  | .view j =>
    match x with
    | .bytes b => do return (← memoryRichEqual j (.bytes b)).getD false
    | _ => pure false
  | o => pure (itemEqObj x o)

/-- The loop of `memoryview_count_impl`, :2800-2819. -/
def countLoop (it : Nat) (value : Obj) : Nat → Int → M Int
  | 0, _ => throw .modelFuel
  | fuel + 1, count => do
    match ← memoryiterNext it with
    | Option.none => return count
    | some item =>
      let contained ← itemEqM item value
      countLoop it value fuel (if contained then count + 1 else count)

/-- `memoryview_count_impl`, :2789-2822. -/
def memoryviewCount (self : Nat) (value : Obj) : M Int := do
  let it ← memoryIter self
  let st ← M.get
  countLoop it value ((st.iters.getD it default).length.toNat + 2) 0

/-- The search loop of `memoryview_index_impl`, :2875-2898. -/
def indexLoop (self : Nat) (value : Obj) : Nat → Int → Int → M Int
  | 0, _, _ => throw .modelFuel
  | fuel + 1, index, stop =>
    if index < stop then do
      let item ← memoryItem self index
      if ← itemEqM item value then return index
      indexLoop self value fuel (index + 1) stop
    else throw (.valueError "memoryview.index(x): x not found")

/-- `memoryview_index_impl`, :2842-2908. `start` and `stop` are `slice_index` arguments,
already saturated to `Py_ssize_t`. -/
def memoryviewIndex (self : Nat) (value : Obj) (start stop : Int) : M Int := do
  checkReleased self
  let st ← M.get
  let view := (st.mv self).view
  if view.ndim = 0 then throw (.typeError "invalid lookup on 0-dim memory")
  if view.ndim = 1 then
    let n := (view.shape.getD []).getD 0 0
    let start := if start < 0 then max (start + n) 0 else start
    let stop := if stop < 0 then max (stop + n) 0 else stop
    let stop := min stop n
    let start := min start stop
    return ← indexLoop self value (stop - start + 1).toNat start stop
  throw (notImplError "multi-dimensional lookup is not implemented")

/-! ## Hash (:3208-3263) -/

/-- `memory_hash`, :3208-3263, as the bytes given to `Py_HashBuffer`. The result is
cached in `self->hash`, consulted before anything else. `PyObject_Hash(view->obj)` is
this function again when the exporter is a memoryview (`fuel` bounds that chain), and
may be Python code otherwise, so `self` holds an export around it (:3234-3236, gh-142664):
a `__hash__` that calls `self.release()` gets `BufferError`. -/
def memoryHashF : Nat → Nat → M (List Nat)
  | 0, _ => throw .modelFuel
  | fuel + 1, self => do
    let st ← M.get
    let x := st.mv self
    match x.hash with
    | some h => return h
    | Option.none =>
      checkReleased self
      let view := x.view
      if !view.readonly then throw (.valueError "cannot hash writable memoryview object")
      match getNativeFmtchar (view.format.getD []) with
      | some (c, _) =>
        if !isByteFormat c then
          throw (.valueError "memoryview: hashing is restricted to formats 'B', 'b' or 'c'")
      | Option.none =>
        throw (.valueError "memoryview: hashing is restricted to formats 'B', 'b' or 'c'")
      match view.obj with
      | some (.exp e) =>
        withExport self do
          fire (st.hashHook.getD e Option.none)
          match st.unhashable.getD e Option.none with
          | some err => throw err
          | Option.none => pure ()
      | some (.mv i) =>
        let _ ← withExport self (memoryHashF fuel i)
      | Option.none => pure ()
      let mem ←
        if !x.flags.isC then M.lift (bufferToContiguous st.mem view 'C')
        else pure (rdBytes st.mem view.buf view.len.toNat)
      M.modify fun st => st.setMv self { st.mv self with hash := some mem }
      return mem

def memoryHash (self : Nat) : M (List Nat) := fun st => memoryHashF (st.mvs.length + 1) self st

/-! ## Getters (:3270-3393) -/

/-- `_IntTupleFromSsizet`, :3270-3292: NULL gives the empty tuple. -/
def intTupleFromSsizet (len : Nat) (vals : Option (List Int)) : List Int :=
  match vals with
  | Option.none => []
  | some v => v.take len

/-- The getters, by attribute name. -/
inductive Attr where
  | obj | nbytes | readonly | itemsize | format | ndim | shape | strides | suboffsets
  | cContiguous | fContiguous | contiguous
  deriving Repr, DecidableEq, Inhabited

/-- What a getter returns. -/
inductive AttrVal where
  | obj (r : Option ORef)
  | int (n : Int)
  | bool (b : Bool)
  | fmt (s : List Char)
  | tuple (l : List Int)
  deriving Repr, DecidableEq, Inhabited

/-- `memory_obj_get` to `memory_contiguous`, :3294-3393: each is `CHECK_RELEASED`, then
a read. -/
def memoryGet (self : Nat) (a : Attr) : M AttrVal := do
  checkReleased self
  let st ← M.get
  let x := st.mv self
  let v := x.view
  match a with
  | .obj => return .obj v.obj
  | .nbytes => return .int v.len
  | .readonly => return .bool v.readonly
  | .itemsize => return .int v.itemsize
  | .format => return .fmt (v.format.getD [])
  | .ndim => return .int v.ndim
  | .shape => return .tuple (intTupleFromSsizet v.ndim v.shape)
  | .strides => return .tuple (intTupleFromSsizet v.ndim v.strides)
  | .suboffsets => return .tuple (intTupleFromSsizet v.ndim v.suboffsets)
  | .cContiguous => return .bool x.flags.isC
  | .fContiguous => return .bool x.flags.isF
  | .contiguous => return .bool x.flags.isAny

end PyLean.BytesObj.Mem
