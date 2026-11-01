import PyLean.BytesObj.Mem.State

/-!
The `memoryview` object, `Objects/memoryobject.c` (CPython 3.14.7), function by function
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
  /-- An object with `__index__`. -/
  | index (n : Ret Int) (rel : Option Nat)
  /-- An object with `__float__`. -/
  | floatLike (bits : Ret Nat) (rel : Option Nat)
  /-- An object with `__bool__`. -/
  | boolLike (b : Ret Bool) (rel : Option Nat)
  deriving Repr, DecidableEq, Inhabited

def Obj.typeName : Obj → String
  | .int _ => "int"
  | .bool _ => "bool"
  | .float _ => "float"
  | .bytes _ => "bytes"
  | .str _ => "str"
  | .none => "NoneType"
  | .list _ => "list"
  | .view _ => "memoryview"
  | .exporter _ _ => "Exporter"
  | .index _ _ => "Idx"
  | .floatLike _ _ => "Flt"
  | .boolLike _ _ => "Bln"

/-- One element of a subscript. -/
inductive KeyElem where
  | obj (o : Obj)
  /-- A slice object; `rel` is the callback of an `__index__` among its parts. -/
  | slice (s : Slice) (rel : Option Nat)
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

/-- `PyBuffer_Release(&self->master)` when `obj` is a memoryview: `memory_releasebuf`,
:1608-1615, runs. Other exporters' `bf_releasebuffer` is out of scope. -/
def pyBufferRelease (b : Buf) : M Unit := fun st =>
  match b.obj with
  | some (.mv i) =>
    let x := st.mv i
    (.ok (), st.setMv i { x with exports := x.exports - 1 })
  | _ => (.ok (), st)

/-- `mbuf_release`, :106-117. -/
def mbufRelease (k : Nat) : M Unit := fun st =>
  let x := st.mb k
  if x.released then (.ok (), st)
  else pyBufferRelease x.master (st.setMb k { x with released := true })

/-- `mbuf_clear`, :138-145. -/
def mbufClear (k : Nat) : M Unit := mbufRelease k

/-! ## Release (:1104-1193) -/

/-- `_memory_release`, :1108-1120. -/
def memoryRelease (i : Nat) : M Unit := fun st =>
  let x := st.mv i
  if x.flags.released then (.ok (), st)
  else
    let st := st.setMv i { x with flags := { x.flags with released := true } }
    let b := st.mb x.mbuf
    let e := b.exports - 1
    let st := st.setMb x.mbuf { b with exports := e }
    if e = 0 then mbufRelease x.mbuf st else (.ok (), st)

/-- `get_exports`, :1089-1097. -/
def getExports (st : St) (i : Nat) : Int := (st.mv i).exports

/-- `memoryview_release_impl`, :1128-1148. -/
def memoryviewRelease (i : Nat) : M Unit := fun st =>
  let e := getExports st i
  if e = 0 then memoryRelease i st
  else if e > 0 then
    (.error (bufferError s!"memoryview has {e} exported buffer{if e = 1 then "" else "s"}"), st)
  else (.error (systemError "memoryview: negative export count"), st)

/-- `memory_dealloc`, :1150-1161: the last reference to a view goes away. -/
def memoryDealloc (i : Nat) : M Unit := memoryRelease i

/-- `memory_clear`, :1171-1180: a view in a reference cycle. -/
def memoryClear (i : Nat) : M Unit := fun st =>
  if getExports st i = 0 then memoryRelease i st else (.ok (), st)

/-- `memory_enter`, :1182-1187. -/
def memoryEnter (i : Nat) : M Unit := checkReleased i

/-- `memory_exit`, :1189-1193. -/
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

/-- `__buffer__` returned something other than a memoryview, typeobject.c:10718-10719. -/
def bufferWrong (_ : String) : PyExc := .typeError "__buffer__ returned non-memoryview object"

/-! ## Registering views -/

/-- `memory_alloc`, :643-665, with the view filled in by the caller. Returns its number. -/
def memoryAlloc (x : MV) : M Nat := fun st =>
  (.ok st.mvs.length, { st with mvs := st.mvs ++ [x] })

def bumpMbuf (k : Nat) : M Unit := fun st =>
  let b := st.mb k
  (.ok (), st.setMb k { b with exports := b.exports + 1 })

/-- `mbuf_add_view`, :675-705. -/
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

/-- `mbuf_add_incomplete_view`, :712-735. -/
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

/-- `view->format = NULL` without `PyBUF_FORMAT`, :1547-1554. -/
def viewFormat (flags : Nat) (v : Buf) : Buf :=
  if (flags &&& bufFormat) == 0 then { v with format := none } else v

/-- `view->strides = NULL` without `PyBUF_STRIDES`, :1576-1583. -/
def viewStrides (flags : Nat) (v : Buf) : Buf :=
  if !req flags bufStrides then { v with strides := none } else v

/-- `view->ndim = 1; view->shape = NULL` without `PyBUF_ND`, :1584-1599. -/
def viewShape (flags : Nat) (v : Buf) : Buf :=
  if !req flags bufND then { v with ndim := 1, shape := none } else v

/-- The checks of `memory_getbuf`, :1538-1599, on `*view = *base`, in order. -/
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

/-- `memory_getbuf`, :1528-1606. `*view = *base` is a copy; the export is counted only
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
  return { view with obj := some (.mv self) }

/-- `memory_releasebuf`, :1608-1615. -/
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

/-- The exporter path of `PyMemoryView_FromObjectAndFlags`, :811-819: on failure of
`mbuf_add_view` the `Py_DECREF(mbuf)` releases the master. -/
def viewOfExporter (b : Buf) (flags : Nat) : M Nat := do
  let k ← managedBufferFromObject b flags
  M.onError (mbufAddView k none) (mbufRelease k)

/-- `PyMemoryView_FromObjectAndFlags`, :800-825. -/
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

/-- `PyMemoryView_FromObject`, :853-857. -/
def memoryViewFromObject (v : Obj) : M Nat := memoryViewFromObjectAndFlags v bufFullRO

/-- `memoryview_impl`, :1013-1018 (`memoryview(object)`). -/
def memoryviewNew (v : Obj) : M Nat := memoryViewFromObject v

/-- `memoryview__from_flags_impl`, :1031-1036. -/
def memoryviewFromFlags (v : Obj) (flags : Nat) : M Nat := memoryViewFromObjectAndFlags v flags

/-- `_PyMemoryView_FromBufferProc`, :831-848, with `memory_getbuf` as the buffer proc
(`m.__buffer__(flags)`, `wrap_buffer`, Objects/typeobject.c:9754-9773). -/
def memoryBufferProc (self : Nat) (flags : Nat) : M Nat := do
  let k ← mbufAlloc
  let master ← memoryGetbuf self flags
  M.modify fun st => st.setMb k { st.mb k with master := master }
  M.onError (mbufAddView k none) (mbufRelease k)

/-- `PyMemoryView_FromMemory`, :740-762, on `size` bytes at `mem`. `writable` is
`flags == PyBUF_WRITE`. -/
def memoryViewFromMemory (mem : Int) (size : Int) (writable : Bool) : M Nat := do
  let k ← mbufAlloc
  let master : Buf :=
    { buf := mem, len := size, itemsize := 1, readonly := !writable, ndim := 1,
      format := some ['B'], shape := some [size], strides := some [1] }
  M.modify fun st => st.setMb k { st.mb k with master := master }
  mbufAddView k none

/-- `PyMemoryView_FromBuffer`, :769-794. `isNull` is `info->buf == NULL`. -/
def memoryViewFromBuffer (info : Buf) (isNull : Bool) : M Nat := do
  if isNull then throw (.valueError "PyMemoryView_FromBuffer(): info->buf must not be NULL")
  let k ← mbufAlloc
  M.modify fun st => st.setMb k { st.mb k with master := { info with obj := none } }
  mbufAddView k none

/-- The first part of `memory_from_contiguous_copy`, :900-912: a new bytes object at the
end of the store, its managed buffer, and `mbuf_copy_format` (:860-874). -/
def contigBytes (src : Buf) : M Nat := do
  let e ← bytesBuf (List.replicate src.len.toNat 0)
  let k ← managedBufferFromObject e bufFullRO
  M.modify fun st =>
    let b := st.mb k
    st.setMb k { b with master := { b.master with format := src.format } }
  return k

/-- The second part of `memory_from_contiguous_copy`, :914-945: the view, its strides in
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

/-- `memory_from_contiguous_copy`, :888-946. -/
def memoryFromContiguousCopy (src : Buf) (order : Char) : M Nat := do
  let k ← contigBytes src
  contigFill k src order

/-- `PyMemoryView_GetContiguous`, :965-1001. `writable` is `buffertype == PyBUF_WRITE`. -/
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
of :1302-1303. -/
def srcIsByte (view : Buf) : Bool :=
  match getNativeFmtchar (view.format.getD ['B']) with
  | some (c, _) => isByteFormat c
  | none => false

/-- `cast_to_1D`, :1275-1335, on the fresh view `i`. -/
def castTo1D (i : Nat) (format : List Char) : M Unit := do
  let st ← M.get
  let x := st.mv i
  let view := x.view
  if format.any (fun c => c.toNat ≥ 128) then throw unicodeEncodeError
  let some (destchar, itemsize) := getNativeFmtchar format
    | throw (.valueError "memoryview: destination format must be a native single character format prefixed with an optional '@'")
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

/-- `PyLong_AsSsize_t`, Objects/longobject.c:668-669. -/
def longAsSsize (x : Int) : Py Int :=
  if ssizeMin ≤ x ∧ x ≤ ssizeMax then .ok x
  else .error (.overflowError "Python int too large to convert to C ssize_t")

/-- `PyLong_Check(tmp)` and the value of an `int` (or `bool`). -/
def Obj.asLong? : Obj → Option Int
  | .int n => some n
  | .bool b => some (if b then 1 else 0)
  | _ => Option.none

/-- `copy_shape`, :1338-1372: `(len, shape)`, `len` the running product. -/
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

/-- `cast_to_ND`, :1377-1411. -/
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

/-- `zero_in_shape`, :1413-1424. -/
def zeroInShape (v : Buf) : Bool := ((v.shape.getD []).take v.ndim).any (· == 0)

/-- The argument `shape` of `memoryview.cast`. -/
inductive ShapeArg where
  /-- A list or tuple. -/
  | seq (items : List Obj)
  /-- Anything else. -/
  | other
  deriving Repr, DecidableEq, Inhabited

/-- `memoryview_cast_impl`, :1447-1499. -/
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

/-- `memoryview_toreadonly_impl`, :1507-1521. -/
def memoryviewToreadonly (self : Nat) : M Nat := do
  checkReleased self
  checkRestricted self
  let st ← M.get
  let i ← mbufAddView (st.mv self).mbuf (some (st.mv self).view)
  M.modify fun st =>
    let y := st.mv i
    st.setMv i { y with view := { y.view with readonly := true } }
  return i

/-! ## Pack and unpack (:1628-2026) -/

/-- `type_error_int`, :1634-1640. -/
def typeErrorInt (fmt : List Char) : PyExc :=
  .typeError s!"memoryview: invalid type for format '{fmtText fmt}'"

/-- `value_error_int`, :1642-1648. -/
def valueErrorInt (fmt : List Char) : PyExc :=
  .valueError s!"memoryview: invalid value for format '{fmtText fmt}'"

/-- `fix_error_int`, :1650-1665. -/
def fixErrorInt (fmt : List Char) : PyExc → PyExc
  | .typeError _ => typeErrorInt fmt
  | .overflowError _ | .valueError _ => valueErrorInt fmt
  | e => e

/-- `__index__` returned a non-int, Objects/abstract.c:1423-1425. -/
def indexWrong (t : String) : PyExc := .typeError s!"__index__ returned non-int (type {t})"

/-- `_PyNumber_Index(item)`, Objects/abstract.c:1402-1440, running `__index__`. -/
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

/-- `pylong_as_ld`, :1672-1685. -/
def pylongAsLd (item : Obj) : M Int := do M.lift (asLong (← numberIndex item))
/-- `pylong_as_lu`, :1687-1700. -/
def pylongAsLu (item : Obj) : M Int := do M.lift (asUnsignedLong (← numberIndex item))
/-- `pylong_as_lld`, :1702-1715. -/
def pylongAsLld (item : Obj) : M Int := do M.lift (asLong (← numberIndex item))
/-- `pylong_as_llu`, :1717-1730. -/
def pylongAsLlu (item : Obj) : M Int := do M.lift (asUnsignedLong (← numberIndex item))
/-- `pylong_as_zd`, :1732-1745. -/
def pylongAsZd (item : Obj) : M Int := do M.lift (longAsSsize (← numberIndex item))
/-- `pylong_as_zu`, :1747-1760. -/
def pylongAsZu (item : Obj) : M Int := do M.lift (asUnsignedLong (← numberIndex item))

/-- `__float__` returned a non-float, Objects/floatobject.c:294-296. -/
def floatWrong (t : String) : PyExc := .typeError s!"Flt.__float__ returned non-float (type {t})"

/-- `PyFloat_AsDouble`, Objects/floatobject.c: `__float__`, then `__index__`. -/
def floatAsDouble : Obj → M Nat
  | .float b => pure b
  | .floatLike r rel => do fire rel; r.get floatWrong
  | .int n => M.lift (longAsDouble n)
  | .bool b => M.lift (longAsDouble (if b then 1 else 0))
  | .index r rel => do fire rel; M.lift (longAsDouble (← r.get indexWrong))
  | o => throw (.typeError s!"must be real number, not {o.typeName}")

/-- `__bool__` returned a non-bool, Objects/typeobject.c:10235-10238. -/
def boolWrong (t : String) : PyExc := .typeError s!"__bool__ should return bool, returned {t}"

/-- `PyObject_IsTrue`. -/
def isTrue : Obj → M Bool
  | .int n => pure (n != 0)
  | .bool b => pure b
  | .float d => pure (d % two63 != 0)
  | .bytes b => pure (!b.isEmpty)
  | .str s => pure (!s.isEmpty)
  | .none => pure false
  | .list n => pure (n != 0)
  | .boolLike r rel => do fire rel; r.get boolWrong
  | .view i => do
    -- `memory_length` via `sq_length`/`mp_length`
    let st ← M.get
    checkReleased i
    if (st.mv i).view.ndim = 0 then
      throw (.typeError "0-dim memory has no length")
    return ((st.mv i).view.shape.getD []).getD 0 0 != 0
  | _ => pure true

/-- `PyLong_AsVoidPtr`, Objects/longobject.c: only a real `int`. -/
def asVoidPtr (item : Obj) : Py Int :=
  match item.asLong? with
  | Option.none => .error (.typeError "an integer is required")
  | some n => if n < 0 then asLong n else asUnsignedLong n

/-- `memcpy(ptr, bytes)` into the store. -/
def memWrite (ptr : Int) (bs : List Nat) : M Unit := fun st =>
  (.ok (), { st with mem := wrBytes st.mem ptr bs })

/-- `pack_single`, :1874-2026. `fmt` is the format after `adjust_fmt`. Note the arm for
`c` (:1995-2001): unlike every other arm and unlike `unpack_single`, it has no
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
  | _ => throw (notImplError s!"memoryview: format {fmtText fmt} not supported")

/-- `unpack_single`, :1775-1863. -/
def unpackSingle (self : Nat) (ptr : Int) (fmt : List Char) : M Item := do
  checkReleased self
  let st ← M.get
  M.lift (unpackRaw st.mem ptr fmt)

/-- `adjust_fmt`, :2152-2164: `view->format` with an optional `@` removed, or an error
unless a single character is left. -/
def adjustFmt (v : Buf) : Py (List Char) :=
  let vf := v.format.getD []
  let fmt := if cc vf 0 = '@' then vf.drop 1 else vf
  if cc fmt 0 ≠ '\x00' ∧ cc fmt 1 = '\x00' then .ok fmt
  else .error (notImplError s!"memoryview: unsupported format {fmtText vf}")

/-! ## Representations -/

/-- `memoryview_tolist_impl`, :2236-2261. `Tree.leaf` for a 0-dim view. -/
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

/-- The `order` argument of `memoryview_tobytes_impl`, :2288-2300. -/
def parseOrder : Option (List Char) → Py Char
  | Option.none => .ok 'C'
  | some ['F'] => .ok 'F'
  | some ['A'] => .ok 'A'
  | some ['C'] => .ok 'C'
  | some _ => .error (.valueError "order must be 'C', 'F' or 'A'")

/-- `memoryview_tobytes_impl`, :2278-2312. `order`: `none` is `order=None`, or the
argument's text. -/
def memoryviewTobytes (self : Nat) (order : Option (List Char)) : M (List Nat) := do
  checkReleased self
  let ord ← M.lift (parseOrder order)
  let st ← M.get
  let src := (st.mv self).view
  M.lift (pyBufferToContiguous st.mem src src.len ord)

/-- The separator checks of `_Py_strhex_impl`, pystrhex.c:13-44: `(sep_char, group)`. -/
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

/-- `_Py_strhex_with_sep`, Python/pystrhex.c:7-143 and :159-163. -/
def strhexWithSep (arg : List Nat) (sep : Option Obj) (bps : Int) : Py (List Char) := do
  let (c, group) ← strhexSep sep bps
  strhexBody arg c group

/-- `memoryview_hex_impl`, :2337-2373. The export count held around the call in the
contiguous branch (:2352-2354) only matters to a `__len__` of `sep`, which the model
does not run. -/
def memoryviewHex (self : Nat) (sep : Option Obj) (bps : Int) : M (List Char) := do
  checkReleased self
  let st ← M.get
  let x := st.mv self
  let src := x.view
  if x.flags.isC then
    return ← M.lift (strhexWithSep (rdBytes st.mem src.buf src.len.toNat) sep bps)
  let bytes ← M.lift (pyBufferToContiguous st.mem src src.len 'C')
  M.lift (strhexWithSep bytes sep bps)

/-- `memory_repr`, :2375-2383: the text before ` at 0x...`. -/
def memoryRepr (self : Nat) : M String := fun st =>
  (.ok (if (st.mv self).flags.released then "<released memory" else "<memory"), st)

/-! ## Indexing and slicing (:2386-2743) -/

/-- `lookup_dimension`, :2390-2413. -/
def lookupDimension (m : Mem) (v : Buf) (ptr : Int) (dim : Nat) (index : Int) : Py Int :=
  let nitems := (v.shape.getD []).getD dim 0
  let index := if index < 0 then index + nitems else index
  if index < 0 ∨ index ≥ nitems then
    .error (.indexError s!"index out of bounds on dimension {dim + 1}")
  else
    .ok (adjustPtr m (ptr + (v.strides.getD []).getD dim 0 * index) v.suboffsets dim)

/-- `ptr_from_index`, :2415-2421. -/
def ptrFromIndex (m : Mem) (v : Buf) (index : Int) : Py Int := lookupDimension m v v.buf 0 index

/-- `PyNumber_AsSsize_t(key, PyExc_IndexError)`, Objects/abstract.c:1458-1500, after
`__index__` gave `x`. The message names the key's type. -/
def keyAsSsize (o : Obj) (x : Int) : Py Int :=
  if ssizeMin ≤ x ∧ x ≤ ssizeMax then .ok x
  else .error (.indexError s!"cannot fit '{o.typeName}' into an index-sized integer")

/-- The tuple elements as index objects, for `ptr_from_tuple`. -/
def elemIndex : KeyElem → M Int
  | .obj o => do
    let n ← numberIndex o
    M.lift (keyAsSsize o n)
  | .slice _ _ => throw (.typeError "slice indices must be integers")

/-- The loop of `ptr_from_tuple`, :2437-2446. -/
def tupleLoop (v : Buf) : Nat → List KeyElem → Int → M Int
  | _, [], ptr => pure ptr
  | dim, e :: es, ptr => do
    let index ← elemIndex e
    let st ← M.get
    let ptr ← M.lift (lookupDimension st.mem v ptr dim index)
    tupleLoop v (dim + 1) es ptr

/-- `ptr_from_tuple`, :2423-2448. -/
def ptrFromTuple (v : Buf) (tup : List KeyElem) : M Int := do
  if tup.length > v.ndim then
    throw (.typeError s!"cannot index {v.ndim}-dimension view with {tup.length}-element tuple")
  tupleLoop v 0 tup v.buf

/-- `memory_item`, :2453-2480. -/
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

/-- `memory_item_multi`, :2483-2506. -/
def memoryItemMulti (self : Nat) (tup : List KeyElem) : M Item := do
  checkReleased self
  let st ← M.get
  let view := (st.mv self).view
  let fmt ← M.lift (adjustFmt view)
  if tup.length < view.ndim then throw (notImplError "sub-views are not implemented")
  let ptr ← ptrFromTuple view tup
  unpackSingle self ptr fmt

/-- The loop of :2525-2526: the last earlier dimension with a suboffset. -/
def lastSub (subs : List Int) : Nat → Option Nat
  | 0 => Option.none
  | n + 1 => if subs.getD n (-1) ≥ 0 then some n else lastSub subs n

/-- `init_slice`, :2508-2535. `PySlice_Unpack` saturates and rejects a zero step;
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

/-- `is_multislice`, :2537-2554, on the tuple elements. -/
def isMultislice (es : List KeyElem) : Bool :=
  !es.isEmpty && es.all fun e => match e with | .slice _ _ => true | _ => false

/-- `_PyIndex_Check`. -/
def Obj.isIndex : Obj → Bool
  | .int _ | .bool _ | .index _ _ => true
  | _ => false

/-- `is_multiindex`, :2556-2571. -/
def isMultiindex (es : List KeyElem) : Bool :=
  es.all fun e => match e with | .obj o => o.isIndex | _ => false

/-- What a subscript returns. -/
inductive Sub where
  | item (x : Item)
  /-- A memoryview by number. -/
  | view (i : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- `memory_subscript`, :2579-2640. -/
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
  | .one (.slice s rel) =>
    checkRestricted self
    let sliced ← mbufAddView (st.mv self).mbuf (some view)
    M.onError (do
      fire rel
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

/-- `copy_single`, :404-432. -/
def copySingle (self : Nat) (dest src : Buf) : M Unit := do
  checkReleased self
  M.lift (equivStructure dest src)
  let useMem := !lastDimIsContiguous dest src
  let st ← M.get
  let dm := copyBase ((dest.shape.getD []).getD 0 0) dest.itemsize dest.buf
    ((dest.strides.getD []).getD 0 0) dest.suboffsets src.buf ((src.strides.getD []).getD 0 0)
    src.suboffsets useMem st.mem st.mem
  M.modify fun st => { st with mem := dm }

/-- `memory_ass_sub`, :2642-2743. `value = none` is `del m[key]`. -/
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
  | .one (.slice s rel) =>
    if view.ndim = 1 then
      let src ← getBufferFull value
      let body : M Unit := do
        fire rel
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

/-- `memory_length`, :2745-2755. -/
def memoryLength (self : Nat) : M Int := do
  checkReleased self
  let st ← M.get
  let view := (st.mv self).view
  if view.ndim = 0 then throw (.typeError "0-dim memory has no length")
  return (view.shape.getD []).getD 0 0

/-! ## Iteration (:3460-3555) -/

/-- `PyObject_GC_New(memoryiterobject, ...)`: a new iterator, by number. -/
def iterAlloc (x : MIter) : M Nat := fun st =>
  (.ok st.iters.length, { st with iters := st.iters ++ [x] })

/-- `memory_iter`, :3519-3555: the iterator's number. -/
def memoryIter (self : Nat) : M Nat := do
  checkReleased self
  let st ← M.get
  let view := (st.mv self).view
  if view.ndim = 0 then throw (.typeError "invalid indexing of 0-dim memory")
  if view.ndim ≠ 1 then throw (notImplError "multi-dimensional sub-views are not implemented")
  let fmt ← M.lift (adjustFmt view)
  let len ← memoryLength self
  iterAlloc { fmt := fmt, length := len, index := 0, seq := some self }

/-- `memoryiter_next`, :3491-3517: `none` is exhaustion (a NULL return with no error). -/
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
    return some (← unpackSingle seq ptr x.fmt)
  M.modify fun st => { st with iters := st.iters.set it { x with seq := Option.none } }
  return Option.none

/-- `PyObject_RichCompareBool(item, value, Py_EQ)` for a built-in `value`: an item never
equals an object of a type other than `int`, `bool`, `float`, `bytes`. -/
def itemEqObj (x : Item) : Obj → Bool
  | .int n => itemEq x (.int n)
  | .bool b => itemEq x (.bool b)
  | .float d => itemEq x (.float d)
  | .bytes b => itemEq x (.bytes b)
  | _ => false

/-- The loop of `memoryview_count_impl`, :2797-2816. -/
def countLoop (it : Nat) (value : Obj) : Nat → Int → M Int
  | 0, _ => throw .modelFuel
  | fuel + 1, count => do
    match ← memoryiterNext it with
    | Option.none => return count
    | some item =>
      countLoop it value fuel (if itemEqObj item value then count + 1 else count)

/-- `memoryview_count_impl`, :2786-2819. -/
def memoryviewCount (self : Nat) (value : Obj) : M Int := do
  let it ← memoryIter self
  let st ← M.get
  countLoop it value ((st.iters.getD it default).length.toNat + 2) 0

/-- The search loop of `memoryview_index_impl`, :2872-2895. -/
def indexLoop (self : Nat) (value : Obj) : Nat → Int → Int → M Int
  | 0, _, _ => throw .modelFuel
  | fuel + 1, index, stop =>
    if index < stop then do
      let item ← memoryItem self index
      if itemEqObj item value then return index
      indexLoop self value fuel (index + 1) stop
    else throw (.valueError "memoryview.index(x): x not found")

/-- `memoryview_index_impl`, :2839-2905. `start` and `stop` are `slice_index` arguments,
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

/-! ## Comparison (:2908-3199) -/

/-- `fix_struct_error_int`, :2916-2928: `struct.error` means "not equal". -/
def fixStructError : PyExc → Py Bool
  | .named "ImportError" m => .error (.named "ImportError" m)
  | .named "MemoryError" m => .error (.named "MemoryError" m)
  | _ => .ok false

/-- `Py_EQ`, `Py_NE`, or an ordering operator. -/
inductive CmpOp where
  | eq | ne | other
  deriving Repr, DecidableEq, Inhabited

/-- The comparison proper, :3134-3178, once both buffers are at hand. -/
def compareBufs (m : Mem) (vv ww : Buf) : Py Bool :=
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
      match structGetUnpacker vf vv.itemsize with
      | .error e => fixStructError e
      | .ok up =>
        match structGetUnpacker wf ww.itemsize with
        | .error e => fixStructError e
        | .ok uq => run '_' (some (up, uq))
    else run vfmt Option.none

/-- The part of `memory_richcompare` before the label `result:`, :3107-3178: `equal`,
with `none` for `MV_COMPARE_NOT_IMPL`. The check of `v` at :3113 comes before
`PyObject_GetBuffer(w)` at :3127, which runs Python code; nothing looks at `v` again. -/
def memoryRichEqual (v : Nat) (w : Obj) : M (Option Bool) := do
  let st ← M.get
  if baseInaccessible st v then
    return some (w == .view v)
  let vv := (st.mv v).view
  match w with
  | .view i =>
    if baseInaccessible st i then
      return some (i == v)
    let ww := (st.mv i).view
    return some (← M.lift (compareBufs st.mem vv ww))
  | .bytes _ | .exporter _ _ =>
    match ← tryCatch (some <$> getBufferFull w) (fun _ => pure Option.none) with
    | Option.none => return Option.none
    | some ww =>
      let st ← M.get
      return some (← M.lift (compareBufs st.mem vv ww))
  | _ => return Option.none

/-- `memory_richcompare`, :3098-3199. `none` is `NotImplemented`. -/
def memoryRichcompare (v : Nat) (w : Obj) (op : CmpOp) : M (Option Bool) := do
  if op = .other then return Option.none
  let e ← memoryRichEqual v w
  return e.map fun equal => if op = .eq then equal else !equal

/-! ## Hash (:3205-3260) -/

/-- `memory_hash`, :3205-3260, as the bytes given to `Py_HashBuffer`. The result is
cached in `self->hash`, consulted before anything else. `PyObject_Hash(view->obj)` is
this function again when the exporter is a memoryview (`fuel` bounds that chain). The
exports held around that call (:3231-3233) only matter to a Python `__hash__`. -/
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
        match st.unhashable.getD e Option.none with
        | some err => throw err
        | Option.none => pure ()
      | some (.mv i) =>
        let _ ← memoryHashF fuel i
      | Option.none => pure ()
      let mem ←
        if !x.flags.isC then M.lift (bufferToContiguous st.mem view 'C')
        else pure (rdBytes st.mem view.buf view.len.toNat)
      M.modify fun st => st.setMv self { st.mv self with hash := some mem }
      return mem

def memoryHash (self : Nat) : M (List Nat) := fun st => memoryHashF (st.mvs.length + 1) self st

/-! ## Getters (:3267-3390) -/

/-- `_IntTupleFromSsizet`, :3267-3289: NULL gives the empty tuple. -/
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

/-- `memory_obj_get` to `memory_contiguous`, :3291-3390: each is `CHECK_RELEASED`, then
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
