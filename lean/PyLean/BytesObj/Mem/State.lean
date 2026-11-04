import PyLean.BytesObj.Mem.Struct

/-!
Object state of the `memoryview` model: `Py_buffer`, `_PyManagedBufferObject`,
`PyMemoryViewObject`, the iterator, and the state monad that threads them, plus the
functions of memoryobject.c that only compute on buffers (contiguity, stride
initialisation, the copy routines). Line numbers refer to `Objects/memoryobject.c`,
CPython 3.15.2, unless stated otherwise.
-/

namespace PyLean.BytesObj.Mem

open PyLean
open PyLean.RangeSlice (wrap)

/-- What `Py_buffer.obj` refers to. -/
inductive ORef where
  /-- A non-memoryview exporter, numbered by the script. -/
  | exp (i : Nat)
  /-- A memoryview exporting through `memory_getbuf`. -/
  | mv (i : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- `Py_buffer`. `none` is a NULL pointer. -/
structure Buf where
  obj : Option ORef := none
  buf : Int := 0
  len : Int := 0
  itemsize : Int := 1
  readonly : Bool := false
  ndim : Nat := 1
  format : Option (List Char) := none
  shape : Option (List Int) := none
  strides : Option (List Int) := none
  suboffsets : Option (List Int) := none
  /-- The view a Python `__release_buffer__` releases, for an exporter that has one. -/
  hook : Option Nat := none
  deriving Repr, DecidableEq, Inhabited

/-- `mv->flags`, Include/cpython/memoryobject.h:19-25. -/
structure Flags where
  released : Bool := false
  c : Bool := false
  fortran : Bool := false
  scalar : Bool := false
  pil : Bool := false
  restricted : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- `_PyManagedBufferObject`, plus whether the master's `obj` has been released. -/
structure MBuf where
  master : Buf := {}
  exports : Int := 0
  released : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- `PyMemoryViewObject`. A cached hash is kept as the bytes it hashed: `Py_HashBuffer`
is a function of those bytes, and only that fact is used. -/
structure MV where
  mbuf : Nat := 0
  view : Buf := {}
  hash : Option (List Nat) := none
  flags : Flags := {}
  exports : Int := 0
  /-- The view a weakref callback releases when this view is deallocated. -/
  weakcb : Option Nat := none
  deriving Repr, DecidableEq, Inhabited

/-- `memoryiterobject`, :3593-3599. -/
structure MIter where
  index : Int := 0
  seq : Option Nat := none
  length : Int := 0
  fmt : List Char := []
  deriving Repr, DecidableEq, Inhabited

/-- All objects a script can reach. Objects are never removed: a deallocated
memoryview simply stays released. -/
structure St where
  mem : Mem := []
  mbufs : List MBuf := []
  mvs : List MV := []
  iters : List MIter := []
  /-- `PyObject_Hash(obj)` failure of exporter `i`, if it has one. -/
  unhashable : List (Option PyExc) := []
  /-- The view that `__hash__` of exporter `i` releases, if it does. -/
  hashHook : List (Option Nat) := []
  /-- `sys.modules['struct'] = None`: `PyImport_ImportModuleAttrString("struct", "Struct")` fails. -/
  noStruct : Bool := false
  deriving Repr, Inhabited

def St.mv (st : St) (i : Nat) : MV := st.mvs.getD i default
def St.mb (st : St) (i : Nat) : MBuf := st.mbufs.getD i default
def St.setMv (st : St) (i : Nat) (x : MV) : St := { st with mvs := st.mvs.set i x }
def St.setMb (st : St) (i : Nat) (x : MBuf) : St := { st with mbufs := st.mbufs.set i x }

/-- `BASE_INACCESSIBLE`, :180-182. -/
def baseInaccessible (st : St) (i : Nat) : Bool :=
  (st.mv i).flags.released || (st.mb (st.mv i).mbuf).released

/-! ## The state monad -/

/-- A computation on the object state that may raise. An exception keeps the state
reached so far, as in C. -/
def M (α : Type) := St → Py α × St

instance : Monad M where
  pure a := fun s => (.ok a, s)
  bind x f := fun s =>
    match x s with
    | (.ok a, s') => f a s'
    | (.error e, s') => (.error e, s')

instance : MonadExcept PyExc M where
  throw e := fun s => (.error e, s)
  tryCatch x h := fun s =>
    match x s with
    | (.ok a, s') => (.ok a, s')
    | (.error e, s') => h e s'

namespace M

theorem pure_app {α : Type} (a : α) (s : St) : (pure a : M α) s = (.ok a, s) := rfl
theorem bind_app {α β : Type} (x : M α) (f : α → M β) (s : St) :
    (x >>= f) s = match x s with
      | (.ok a, s') => f a s'
      | (.error e, s') => (.error e, s') := rfl
theorem throw_app {α : Type} (e : PyExc) (s : St) : (throw e : M α) s = (.error e, s) := rfl

/-- The whole state. -/
def get : M St := fun s => (.ok s, s)
def set (s' : St) : M Unit := fun _ => (.ok (), s')
def modify (f : St → St) : M Unit := fun s => (.ok (), f s)

/-- A pure computation. -/
def lift {α : Type} (r : Py α) : M α := fun s => (r, s)

/-- Rewrite the exception of `x`. -/
def mapErr {α : Type} (f : PyExc → PyExc) (x : M α) : M α := fun s =>
  match x s with
  | (.ok a, s') => (.ok a, s')
  | (.error e, s') => (.error (f e), s')

/-- Run `cleanup` if `x` raised, then raise again (a `goto error` with `Py_DECREF`). -/
def onError {α : Type} (x : M α) (cleanup : M Unit) : M α := fun s =>
  match x s with
  | (.ok a, s') => (.ok a, s')
  | (.error e, s') => (.error e, (cleanup s').2)

end M

/-- `CHECK_RELEASED`/`CHECK_RELEASED_INT` and their `_AGAIN` forms, :184-196, :214-215. -/
def checkReleased (i : Nat) : M Unit := fun st =>
  if baseInaccessible st i then (.error releasedError, st) else (.ok (), st)

/-- `CHECK_RESTRICTED`/`CHECK_RESTRICTED_INT`, :198-210. -/
def checkRestricted (i : Nat) : M Unit := fun st =>
  if (st.mv i).flags.restricted then (.error restrictedError, st) else (.ok (), st)

/-! ## Pointers -/

/-- `ADJUST_PTR(ptr, suboffsets, dim)`, :229-230: follow the pointer stored at `ptr`
when dimension `dim` has a non-negative suboffset. -/
def adjustPtr (m : Mem) (ptr : Int) (subs : Option (List Int)) (dim : Nat) : Int :=
  match subs with
  | some s =>
    if s.getD dim (-1) ≥ 0 then (rdU m ptr 8 : Int) + s.getD dim 0 else ptr
  | none => ptr

/-! ## Contiguity (Objects/abstract.c:460-540) -/

/-- The loop of `_IsCContiguous`, abstract.c:505-512, from dimension `i - 1` down. -/
def cLoop (shape strides : List Int) : Nat → Int → Bool
  | 0, _ => true
  | i + 1, sd =>
    let dim := shape.getD i 0
    if dim > 1 ∧ strides.getD i 0 ≠ sd then false else cLoop shape strides i (sd * dim)

/-- `_IsCContiguous`, abstract.c:500-525. -/
def isCContiguous (v : Buf) : Bool :=
  if v.len = 0 then true
  else
    match v.strides with
    | none => true
    | some st => cLoop (v.shape.getD []) st v.ndim v.itemsize

/-- The loop of `_IsFortranContiguous`, abstract.c:477-484: dimensions in `dims`. -/
def fLoop : List Int → List Int → Int → Bool
  | [], _, _ => true
  | dim :: shape, s :: strides, sd =>
    if dim > 1 ∧ s ≠ sd then false else fLoop shape strides (sd * dim)
  | dim :: shape, [], sd => if dim > 1 ∧ 0 ≠ sd then false else fLoop shape [] (sd * dim)

/-- `_IsFortranContiguous`, abstract.c:460-498. -/
def isFortranContiguous (v : Buf) : Bool :=
  if v.len = 0 then true
  else
    match v.strides with
    | none =>
      if v.ndim ≤ 1 then true
      else ((v.shape.getD []).filter (· > 1)).length ≤ 1
    | some st => fLoop (v.shape.getD []) st v.itemsize

/-- `PyBuffer_IsContiguous`, abstract.c:527-540. -/
def pyBufferIsContiguous (v : Buf) (order : Char) : Bool :=
  if v.suboffsets.isSome then false
  else if order = 'C' then isCContiguous v
  else if order = 'F' then isFortranContiguous v
  else if order = 'A' then isCContiguous v || isFortranContiguous v
  else false

/-- `MV_CONTIGUOUS_NDIM1`, :240-241. -/
def mvContiguousNdim1 (v : Buf) : Bool :=
  (v.shape.getD []).getD 0 0 == 1 || (v.strides.getD []).getD 0 0 == v.itemsize

/-- `MV_C_CONTIGUOUS`, `MV_F_CONTIGUOUS`, `MV_ANY_CONTIGUOUS`, :233-237. -/
def Flags.isC (f : Flags) : Bool := f.scalar || f.c
def Flags.isF (f : Flags) : Bool := f.scalar || f.fortran
def Flags.isAny (f : Flags) : Bool := f.scalar || f.c || f.fortran

/-- `init_flags`, :610-639. The assignment `mv->flags = flags` replaces every bit. -/
def initFlags (v : Buf) : Flags :=
  let f : Flags :=
    match v.ndim with
    | 0 => { scalar := true, c := true, fortran := true }
    | 1 => if mvContiguousNdim1 v then { c := true, fortran := true } else {}
    | _ => { c := pyBufferIsContiguous v 'C', fortran := pyBufferIsContiguous v 'F' }
  if v.suboffsets.isSome then { f with pil := true, c := false, fortran := false } else f

/-! ## Strides -/

/-- The loop of `init_fortran_strides_from_shape`, :487-489. -/
def fStrides (sd : Int) : List Int → List Int
  | [] => []
  | d :: ds => sd :: fStrides (sd * d) ds

/-- `init_strides_from_shape`, :467-477: `strides[ndim-1] = itemsize`, then downwards.
The loop of :475-476 is the Fortran loop on the reversed shape. -/
def cStrides (itemsize : Int) (shape : List Int) : List Int :=
  (fStrides itemsize shape.reverse).reverse

/-- `init_len`, :596-607. -/
def initLen (shape : List Int) (itemsize : Int) : Int := shape.foldl (· * ·) 1 * itemsize

/-- `init_shared_values`, :542-552. -/
def initSharedValues (dest src : Buf) : Buf :=
  { dest with
    obj := src.obj, buf := src.buf, len := src.len, itemsize := src.itemsize,
    readonly := src.readonly, format := some (src.format.getD ['B']), hook := src.hook }

/-- `init_shape_strides`, :555-580: `(shape, strides)` of `dest`, reconstructing what
`src` lacks. -/
def initShapeStrides (src : Buf) : Option (List Int) × Option (List Int) :=
  if src.ndim = 0 then (none, none)
  else if src.ndim = 1 then
    (some [match src.shape with | some s => s.getD 0 0 | none => Int.tdiv src.len src.itemsize],
     some [match src.strides with | some s => s.getD 0 0 | none => src.itemsize])
  else
    let shape := (src.shape.getD []).take src.ndim
    match src.strides with
    | some st => (some shape, some (st.take src.ndim))
    | none => (some shape, some (cStrides src.itemsize shape))

/-- `init_suboffsets`, :582-593. -/
def initSuboffsets (src : Buf) : Option (List Int) := src.suboffsets.map (·.take src.ndim)

/-! ## Format and shape equivalence -/

/-- `equiv_format`, :287-302 (`dest`, `src` have formats, assertion at :292). -/
def stripAt (f : List Char) : List Char := if cc f 0 = '@' then f.drop 1 else f

def equivFormat (dest src : Buf) : Bool :=
  stripAt (dest.format.getD []) == stripAt (src.format.getD []) && dest.itemsize == src.itemsize

/-- The loop of `equiv_shape`, :315-320: stop at the first equal zero. -/
def shapeLoop : List Int → List Int → Bool
  | [], _ => true
  | a :: as, bs =>
    match bs with
    | [] => a == 0
    | b :: bs => if a ≠ b then false else if a = 0 then true else shapeLoop as bs

/-- `equiv_shape`, :307-323. -/
def equivShape (dest src : Buf) : Bool :=
  dest.ndim == src.ndim && shapeLoop ((dest.shape.getD []).take dest.ndim) (src.shape.getD [])

/-- `equiv_structure`, :327-339. -/
def equivStructure (dest src : Buf) : Py Unit :=
  if !equivFormat dest src || !equivShape dest src then
    .error (.valueError "memoryview assignment: lvalue and rvalue have different structures")
  else .ok ()

/-- `HAVE_SUBOFFSETS_IN_LAST_DIM`, :268-269. -/
def haveSubInLast (v : Buf) : Bool :=
  match v.suboffsets with
  | some s => s.getD (v.ndim - 1) (-1) ≥ 0
  | none => false

/-- `last_dim_is_contiguous`, :271-279. -/
def lastDimIsContiguous (dest src : Buf) : Bool :=
  !haveSubInLast dest && !haveSubInLast src &&
    (dest.strides.getD []).getD (dest.ndim - 1) 0 == dest.itemsize &&
    (src.strides.getD []).getD (src.ndim - 1) 0 == src.itemsize

/-! ## The copy routines

The destination of `copy_rec` and `copy_buffer` is always a fresh buffer
(`buffer_to_contiguous`, `memory_from_contiguous_copy`), so they take the source store
`sm` and the destination store `dm` separately. `copy_single` passes one store as both;
`copy_base` reads everything before writing anything, in either branch. -/

/-- The first loop of `copy_base`, :360-363: the `n` items into the scratch buffer. -/
def readItems (sm : Mem) (itemsize : Nat) (stride : Int) (subs : Option (List Int)) :
    Nat → Int → List (List Nat)
  | 0, _ => []
  | n + 1, sptr =>
    rdBytes sm (adjustPtr sm sptr subs 0) itemsize :: readItems sm itemsize stride subs n (sptr + stride)

/-- The second loop of `copy_base`, :364-367. Pointers of `dest` come from `dm`. -/
def writeItems (itemsize : Nat) (stride : Int) (subs : Option (List Int)) :
    List (List Nat) → Int → Mem → Mem
  | [], _, dm => dm
  | it :: its, dptr, dm =>
    writeItems itemsize stride subs its (dptr + stride) (wrBytes dm (adjustPtr dm dptr subs 0) it)

/-- `copy_base`, :344-370. `useMem` is `mem != NULL`. The contiguous branch's `memcpy`
and `memmove` agree here since the bytes are read first. -/
def copyBase (shape0 itemsize : Int) (dptr : Int) (dstr : Int) (dsub : Option (List Int))
    (sptr : Int) (sstr : Int) (ssub : Option (List Int)) (useMem : Bool) (sm dm : Mem) : Mem :=
  if !useMem then
    wrBytes dm dptr (rdBytes sm sptr (shape0 * itemsize).toNat)
  else
    writeItems itemsize.toNat dstr dsub (readItems sm itemsize.toNat sstr ssub shape0.toNat sptr) dptr dm

/-- Tail of a suboffset array: `dsuboffsets ? dsuboffsets+1 : NULL`. -/
def subTail (s : Option (List Int)) : Option (List Int) := s.map (·.drop 1)

/-- The loop of `copy_rec`, :392-400: `k` sub-arrays, both pointers advancing. -/
def copyLoop (dstep sstep : Int) (body : Int → Int → Mem → Mem) : Nat → Int → Int → Mem → Mem
  | 0, _, _, dm => dm
  | k + 1, dptr, sptr, dm => copyLoop dstep sstep body k (dptr + dstep) (sptr + sstep) (body dptr sptr dm)

/-- `copy_rec`, :374-401, on the shape, stride and suboffset arrays from the current
dimension on. `ndim` is `shape.length`. -/
def copyRec (itemsize : Int) (useMem : Bool) (sm : Mem) :
    List Int → Int → List Int → Option (List Int) → Int → List Int → Option (List Int) → Mem → Mem
  | [], _, _, _, _, _, _, dm => dm
  | [n], dptr, dst, dsub, sptr, sst, ssub, dm =>
    copyBase n itemsize dptr (dst.getD 0 0) dsub sptr (sst.getD 0 0) ssub useMem sm dm
  | n :: shape@(_ :: _), dptr, dst, dsub, sptr, sst, ssub, dm =>
    copyLoop (dst.getD 0 0) (sst.getD 0 0)
      (fun dptr' sptr' dm =>
        copyRec itemsize useMem sm shape (adjustPtr dm dptr' dsub 0) (dst.drop 1) (subTail dsub)
          (adjustPtr sm sptr' ssub 0) (sst.drop 1) (subTail ssub) dm)
      n.toNat dptr sptr dm

/-- `copy_buffer`, :437-464, into `dm`. -/
def copyBuffer (sm dm : Mem) (dest src : Buf) : Py Mem := do
  equivStructure dest src
  let useMem := !lastDimIsContiguous dest src
  return copyRec dest.itemsize useMem sm (dest.shape.getD []) dest.buf (dest.strides.getD [])
    dest.suboffsets src.buf (src.strides.getD []) src.suboffsets dm

/-- `buffer_to_contiguous`, :495-534: `len(mem) == src->len`, `src->ndim >= 1`. -/
def bufferToContiguous (sm : Mem) (src : Buf) (order : Char) : Py (List Nat) :=
  let shape := src.shape.getD []
  let strides :=
    if order = 'C' ∨ order = 'A' then cStrides src.itemsize shape
    else fStrides src.itemsize shape
  let dest : Buf := { src with buf := 0, strides := some strides, suboffsets := none }
  copyBuffer sm (List.replicate src.len.toNat 0) dest src

/-- `PyBuffer_ToContiguous`, :1048-1087, into a fresh `len`-byte buffer. -/
def pyBufferToContiguous (sm : Mem) (src : Buf) (len : Int) (order : Char) : Py (List Nat) :=
  if len ≠ src.len then .error (.valueError "PyBuffer_ToContiguous: len != view->len")
  else if pyBufferIsContiguous src order then .ok (rdBytes sm src.buf len.toNat)
  else
    let (sh, st) := initShapeStrides src
    let fb : Buf := { initSharedValues src src with
      shape := sh, strides := st, suboffsets := initSuboffsets src }
    bufferToContiguous sm fb order

/-! ## `struct` unpackers -/

/-- `struct unpacker`, :2113-2118. -/
structure Unpacker where
  fmt : SFmt
  itemsize : Int
  deriving Repr, DecidableEq, Inhabited

/-- `MemoryError()`. -/
def noMemory : PyExc := .named "MemoryError" ""

/-- `struct_get_unpacker`, :2150-2200. The `Struct` call raises `struct.error` on a bad format, and
`PyMem_Malloc(itemsize)` fails for a size no allocation can have, taken as at least `2^47`, past the
address space of an LP64 system. The import is `unpackerOf`. -/
def structGetUnpacker (fmt : List Char) (itemsize : Int) : Py Unpacker := do
  let sf ← structParse fmt
  if itemsize ≥ 2 ^ 47 then throw noMemory
  return ⟨sf, itemsize⟩

/-- `struct_unpack_single`, :2203-2220: copy `itemsize` bytes, then `unpack_from`. -/
def structUnpackSingle (m : Mem) (ptr : Int) (x : Unpacker) : Py (List Item) :=
  structUnpackFrom x.fmt (rdBytes m ptr x.itemsize.toNat)

/-- `struct_unpack_cmp`, :3011-3036. -/
def structUnpackCmp (m : Mem) (p q : Int) (up uq : Unpacker) : Py Bool := do
  let v ← structUnpackSingle m p up
  let w ← structUnpackSingle m q uq
  return structResultEq v w

/-- `UNPACK_TO_BOOL`, :1697-1698. -/
def unpackToBool (m : Mem) (p : Int) : Bool := rdByte m p != 0

/-- The native item at `ptr` as the `switch` of `unpack_single` reads it, :1825-1881.
`fmt` is the format after `adjust_fmt`. -/
def unpackRaw (m : Mem) (ptr : Int) (fmt : List Char) : Py Item :=
  match cc fmt 0 with
  | 'B' => .ok (.int (rdByte m ptr))
  | 'b' => .ok (.int (rdS m ptr 1))
  | 'h' => .ok (.int (rdS m ptr 2))
  | 'i' => .ok (.int (rdS m ptr 4))
  | 'l' => .ok (.int (rdS m ptr 8))
  | '?' => .ok (.bool (unpackToBool m ptr))
  | 'H' => .ok (.int (rdU m ptr 2))
  | 'I' => .ok (.int (rdU m ptr 4))
  | 'L' => .ok (.int (rdU m ptr 8))
  | 'q' => .ok (.int (rdS m ptr 8))
  | 'Q' => .ok (.int (rdU m ptr 8))
  | 'n' => .ok (.int (rdS m ptr 8))
  | 'N' => .ok (.int (rdU m ptr 8))
  | 'f' => .ok (.float (widen32 (rdU m ptr 4)))
  | 'd' => .ok (.float (rdU m ptr 8))
  | 'e' => .ok (.float (unpack2 (rdU m ptr 2)))
  | 'c' => .ok (.bytes [rdByte m ptr])
  | 'P' => .ok (.int (rdU m ptr 8))
  | 'Z' =>
    match cc fmt 1 with
    | 'f' => .ok (.complex (unpack4 (rdU m ptr 4)) (unpack4 (rdU m (ptr + 4) 4)))
    | 'd' => .ok (.complex (rdU m ptr 8) (rdU m (ptr + 8) 8))
    | _ => .error (notImplError s!"memoryview: format {fmtText fmt} not supported")
  | _ => .error (notImplError s!"memoryview: format {fmtText fmt} not supported")

/-- `unpack_cmp`, :3053-3140, for `fmt != '_'`. `CMP_SINGLE` compares C values, which
for integer types is equality of the decoded numbers; `f` compares as `float`, and
widening is exact, so comparing doubles is the same. -/
def unpackCmpNative (m : Mem) (p q : Int) (fmt : Char) : Py Bool :=
  match fmt with
  | 'B' => .ok (rdByte m p == rdByte m q)
  | 'b' => .ok (rdS m p 1 == rdS m q 1)
  | 'h' => .ok (rdS m p 2 == rdS m q 2)
  | 'i' => .ok (rdS m p 4 == rdS m q 4)
  | 'l' => .ok (rdS m p 8 == rdS m q 8)
  | '?' => .ok (unpackToBool m p == unpackToBool m q)
  | 'H' => .ok (rdU m p 2 == rdU m q 2)
  | 'I' => .ok (rdU m p 4 == rdU m q 4)
  | 'L' => .ok (rdU m p 8 == rdU m q 8)
  | 'q' => .ok (rdS m p 8 == rdS m q 8)
  | 'Q' => .ok (rdU m p 8 == rdU m q 8)
  | 'n' => .ok (rdS m p 8 == rdS m q 8)
  | 'N' => .ok (rdU m p 8 == rdU m q 8)
  | 'f' => .ok (dEq (widen32 (rdU m p 4)) (widen32 (rdU m q 4)))
  | 'd' => .ok (dEq (rdU m p 8) (rdU m q 8))
  | 'e' => .ok (dEq (unpack2 (rdU m p 2)) (unpack2 (rdU m q 2)))
  | 'c' => .ok (rdByte m p == rdByte m q)
  | 'P' => .ok (rdU m p 8 == rdU m q 8)
  | c =>
    if c = zfCode then
      .ok (dEq (widen32 (rdU m p 4)) (widen32 (rdU m q 4)) &&
        dEq (widen32 (rdU m (p + 4) 4)) (widen32 (rdU m (q + 4) 4)))
    else if c = zdCode then
      .ok (dEq (rdU m p 8) (rdU m q 8) && dEq (rdU m (p + 8) 8) (rdU m (q + 8) 8))
    else .error (runtimeError "memoryview: internal error in richcompare")

/-- `unpack_cmp`, with `unp = some (unpack_p, unpack_q)` for `fmt == '_'`. -/
def unpackCmp (m : Mem) (p q : Int) (fmt : Char) (unp : Option (Unpacker × Unpacker)) : Py Bool :=
  match fmt, unp with
  | '_', some (up, uq) => structUnpackCmp m p q up uq
  | _, _ => unpackCmpNative m p q fmt

/-- `cmp_base`, :3143-3161: `equal <= 0` stops the walk. -/
def cmpBase (m : Mem) (fmt : Char) (unp : Option (Unpacker × Unpacker))
    (ps qs : Int) (psub qsub : Option (List Int)) : Nat → Int → Int → Py Bool
  | 0, _, _ => .ok true
  | n + 1, p, q => do
    let equal ← unpackCmp m (adjustPtr m p psub 0) (adjustPtr m q qsub 0) fmt unp
    if !equal then return false
    cmpBase m fmt unp ps qs psub qsub n (p + ps) (q + qs)

/-- The loop of `cmp_rec`, :3187-3196: `equal <= 0` stops the walk. -/
def cmpLoop (pstep qstep : Int) (body : Int → Int → Py Bool) : Nat → Int → Int → Py Bool
  | 0, _, _ => .ok true
  | k + 1, p, q => do
    let equal ← body p q
    if !equal then return false
    cmpLoop pstep qstep body k (p + pstep) (q + qstep)

/-- `cmp_rec`, :3165-3199, on the arrays from the current dimension on. -/
def cmpRec (m : Mem) (fmt : Char) (unp : Option (Unpacker × Unpacker)) :
    List Int → List Int → Option (List Int) → List Int → Option (List Int) → Int → Int → Py Bool
  | [], _, _, _, _, _, _ => .ok true
  | [n], pst, psub, qst, qsub, p, q =>
    cmpBase m fmt unp (pst.getD 0 0) (qst.getD 0 0) psub qsub n.toNat p q
  | n :: shape@(_ :: _), pst, psub, qst, qsub, p, q =>
    cmpLoop (pst.getD 0 0) (qst.getD 0 0)
      (fun p' q' =>
        cmpRec m fmt unp shape (pst.drop 1) (subTail psub) (qst.drop 1) (subTail qsub)
          (adjustPtr m p' psub 0) (adjustPtr m q' qsub 0))
      n.toNat p q

/-! ## `tolist` -/

/-- A nested list of items. -/
inductive Tree where
  | leaf (i : Item)
  | node (l : List Tree)
  deriving Repr, Inhabited

/-- The loop of `tolist_base`, :2257-2265, with `unpack_single` as `f`. -/
def tolistBase {α : Type} (m : Mem) (f : Int → Py α) (stride : Int) (subs : Option (List Int)) :
    Nat → Int → Py (List α)
  | 0, _ => .ok []
  | n + 1, ptr => do
    let x ← f (adjustPtr m ptr subs 0)
    let r ← tolistBase m f stride subs n (ptr + stride)
    return x :: r

/-- `tolist_rec`, :2272-2304, on the arrays from the current dimension on. The loop at
:2291-2301 is the loop of `tolist_base` with a recursive call as the item. -/
def tolistRec (m : Mem) (f : Int → Py Item) :
    List Int → List Int → Option (List Int) → Int → Py Tree
  | [], _, _, _ => .ok (.node [])
  | [n], st, subs, ptr =>
    .node <$> ((·.map Tree.leaf) <$> tolistBase m f (st.getD 0 0) subs n.toNat ptr)
  | n :: shape@(_ :: _), st, subs, ptr =>
    .node <$> tolistBase m
      (fun p => tolistRec m f shape (st.drop 1) (subTail subs) p) (st.getD 0 0) subs n.toNat ptr

/-! ## `_Py_strhex_with_sep` (Python/pystrhex.c) -/

def hexDigit (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

/-- `retbuf[j++] = Py_hexdigits[c >> 4]; retbuf[j++] = Py_hexdigits[c & 0x0f]`. -/
def hexPair (c : Nat) : List Char := [hexDigit (c / 16), hexDigit (c % 16)]

/-- The loops of pystrhex.c:210-226: chunks counted from the left. -/
def hexLeft (sep : Char) (k : Nat) : Nat → List Nat → List Char
  | 0, l => l.flatMap hexPair
  | c + 1, l => (l.take k).flatMap hexPair ++ sep :: hexLeft sep k c (l.drop k)

/-- The loops of pystrhex.c:227-244: chunks counted from the right, on the reversed
input, since `retbuf` is filled backwards. -/
def hexRight (sep : Char) (k : Nat) : Nat → List Nat → List Char
  | 0, rl => rl.reverse.flatMap hexPair
  | c + 1, rl => hexRight sep k c (rl.drop k) ++ sep :: (rl.take k).reverse.flatMap hexPair

/-- `_Py_strhex_impl` after the separator checks, pystrhex.c:154-245. `group` is
`bytes_per_sep_group`, `0` when there is no separator. -/
def strhexBody (arg : List Nat) (sep : Char) (group : Int) : Py (List Char) :=
  let arglen : Int := arg.length
  let abs := group.natAbs
  let resultlen : Int := if group ≠ 0 ∧ arglen > 0 then Int.tdiv (arglen - 1) abs else 0
  if arglen ≥ Int.tdiv ssizeMax 2 - resultlen then .error memoryError
  else
    let (group, abs) := if (abs : Int) ≥ arglen then ((0 : Int), 0) else (group, abs)
    if group = 0 then .ok (arg.flatMap hexPair)
    else
      let chunks := (arg.length - 1) / abs
      if group < 0 then .ok (hexLeft sep abs chunks arg)
      else .ok (hexRight sep abs chunks arg.reverse)

end PyLean.BytesObj.Mem
